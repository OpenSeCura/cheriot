(*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics HelperLemmas.
From Cheriot Require Import SpecDefines SpecDevice.
From Cheriot.Proof Require Import RefCoreRel RefSpecRead.

Import ListNotations.
Local Open Scope Z_scope.

(* The revocation table: the rev byte of a revokable base lies in
 * `[revTableStartAddr, revTableStartAddr + revTableSizeInBytes)` (`revByteAddrOf_inTable`), so a
 * capability that needs a revocation check has its rev byte in the table
 * (`revByte_needsCheck_inTable`).
 *
 * 1. `castBits` leaves values unchanged;
 * 2. the values of the bit operations `computeRevBitAddr` uses;
 * 3. the rev byte address of a base, and why a revokable base's is in the table;
 * 4. with disjoint regions, `revTableInExternalMem` makes every line of the table ExternalMem
 *    (`revTab_line`). *)

(* --- 1. Casts Are the Identity on Values --- *)

Lemma positive_cast_refl : forall (P : positive -> Type) p (v : P p), @positive_cast P p p (eq_refl p) v = v.
Proof.
  intros P p; revert P; induction p as [p IH | p IH |]; intros P v; cbn.
  - apply (IH (fun q => P (xI q))).
  - apply (IH (fun q => P (xO q))).
  - reflexivity.
Qed.

Lemma Z_cast_refl : forall (P : Z -> Type) n (v : P n), @Z_cast P n n (eq_refl n) v = v.
Proof.
  intros P [| p | p] v; cbn.
  - reflexivity.
  - apply (positive_cast_refl (fun q => P (Zpos q))).
  - apply (positive_cast_refl (fun q => P (Zneg q))).
Qed.

Lemma to_Z_castBits : forall ni no (pf : ni = no) (e : Expr type (Bit ni)),
  Zmod.to_Z (evalExpr (castBits pf e)) = Zmod.to_Z (evalExpr e).
Proof. intros ni no pf e; subst no; unfold castBits; rewrite Z_cast_refl; reflexivity. Qed.

(* --- 2. Values of the Bit Operations --- *)

Lemma to_Z_lastn : forall n w (a : bits w), 0 <= n -> 0 <= w - n ->
  Zmod.to_Z (Zmod_lastn n a) = Zmod.to_Z a / 2 ^ (w - n).
Proof.
  intros n w a Hn Hwn; unfold Zmod_lastn.
  rewrite bits.unsigned_of_Z, Z.shiftr_div_pow2 by lia.
  pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
  apply Z.mod_small; split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; [lia |].
  rewrite <- Z.pow_add_r by lia; replace (w - n + n) with w by lia; lia.
Qed.

(* The same, with the input width written `l + n`, as `TruncMsb n l` types it *)
Lemma to_Z_lastn' : forall n l (a : bits (l + n)), 0 <= n -> 0 <= l ->
  Zmod.to_Z (Zmod_lastn n a) = Zmod.to_Z a / 2 ^ l.
Proof. intros n l a Hn Hl; rewrite to_Z_lastn by lia; do 2 f_equal; lia. Qed.

Lemma to_Z_ZeroExtend : forall msb lsb (e : Expr type (Bit lsb)), 0 <= lsb -> 0 <= msb ->
  Zmod.to_Z (evalExpr (ZeroExtend msb e)) = Zmod.to_Z (evalExpr e).
Proof.
  intros msb lsb e Hl Hm; unfold ZeroExtend; cbn [evalExpr].
  rewrite bits.unsigned_app by lia.
  rewrite Zmod.unsigned_0, Z.shiftl_0_l, Z.lor_0_r; reflexivity.
Qed.

Lemma to_Z_Sub : forall n (a b : Expr type (Bit n)), 0 <= n ->
  Zmod.to_Z (evalExpr (Sub a b)) = (Zmod.to_Z (evalExpr a) - Zmod.to_Z (evalExpr b)) mod 2 ^ n.
Proof.
  intros n a b Hn; unfold Sub; cbn [evalExpr map fold_left].
  change (evalNot (k:=Bit n) (evalExpr b)) with (Zmod.not (evalExpr b)).
  assert (HM : 2 ^ n <> 0) by (apply Z.pow_nonzero; lia).
  rewrite !Zmod.unsigned_add, bits.unsigned_not', Zmod.unsigned_0, Zmod.unsigned_1, Z.ones_equiv.
  rewrite Z.add_mod_idemp_r, Z.add_mod_idemp_l by exact HM.
  rewrite <- Z.add_assoc, Z.add_mod_idemp_l by exact HM.
  rewrite <- (Z.mod_add (Zmod.unsigned (evalExpr a) - Zmod.unsigned (evalExpr b)) 1 (2 ^ n) HM).
  f_equal; lia.
Qed.

(* --- 3. The Rev Byte of a Revokable Base Is in the Table --- *)

Section RevTab.
  Variable config : RevConfig.

  Hypothesis Hg0 : 0 <= lgRevGranularity config.
  Hypothesis Hg1 : lgRevGranularity config + 3 <= AddrSz + 1.

  Lemma revByteAddrOf_val : forall base,
    Zmod.to_Z (revByteAddrOf config base) =
      (revTableStartAddr config +
       ((Zmod.to_Z base - heapStartAddr config) mod 2 ^ (AddrSz + 1)) / 2 ^ (lgRevGranularity config + 3))
      mod 2 ^ AddrSz.
  Proof.
    intros base; unfold revByteAddrOf, computeRevBitAddr.
    cbn [evalLetExpr evalExpr readDiffTuple mapDiffTuple fst snd map fold_left finNum Fst Snd].
    assert (HM : 2 ^ AddrSz <> 0) by (apply Z.pow_nonzero; cbv; congruence).
    rewrite !Zmod.unsigned_add, Zmod.unsigned_0, Zmod.unsigned_of_Z.
    rewrite to_Z_castBits; unfold ZeroExtendTo; rewrite to_Z_ZeroExtend by lia; cbn [evalExpr].
    rewrite to_Z_lastn' by lia; rewrite to_Z_castBits; cbn [evalExpr].
    rewrite to_Z_lastn' by lia; rewrite to_Z_castBits; cbn [evalExpr].
    rewrite to_Z_Sub by (cbv; congruence); cbn [evalExpr].
    rewrite Zmod.unsigned_of_Z, Zminus_mod_idemp_r.
    rewrite Z.div_div, <- Z.pow_add_r by (try apply Z.pow_pos_nonneg; lia).
    rewrite Z.add_0_l, Z.mod_mod, Z.add_mod_idemp_l by exact HM.
    reflexivity.
  Qed.
  Hypothesis Hsz : 0 <= revTableSizeInBytes config.

  Lemma revByteAddrOf_inTable : forall base,
    evalExpr (isRevokableAddr config (Var type (Bit (AddrSz + 1)) base)) = true ->
    exists a, revTableStartAddr config <= a < revTableStartAddr config + revTableSizeInBytes config /\
              revByteAddrOf config base = Zmod.of_Z _ a.
  Proof.
    intros base Hrev.
    unfold isRevokableAddr, Uge in Hrev; cbn [evalExpr map fold_left] in Hrev.
    change (evalAndBinary (k:=Bool)) with andb in Hrev.
    change (evalNot (k:=Bool)) with negb in Hrev.
    change (InvDefault Bool) with true in Hrev.
    unfold heapEndAddr, heapSize in Hrev; rewrite !Zmod.unsigned_of_Z in Hrev; cbn [andb] in Hrev.
    apply andb_prop in Hrev as [H1 H2]; apply negb_true_iff, Z.ltb_ge in H1; apply Z.ltb_lt in H2.
    assert (HMpos : 0 < 2 ^ (AddrSz + 1)) by (apply Z.pow_pos_nonneg; cbv; congruence).
    pose proof (Zmod.unsigned_pos_bound base HMpos) as HB.
    pose proof (Z.mod_pos_bound (heapStartAddr config) _ HMpos) as HHm.
    assert (HP : 0 < 2 ^ (lgRevGranularity config + 3)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hhs : revTableSizeInBytes config * 8 * 2 ^ lgRevGranularity config =
                  2 ^ (lgRevGranularity config + 3) * revTableSizeInBytes config)
      by (rewrite Z.pow_add_r by lia; ring).
    rewrite Hhs in H2.
    assert (Hoff : (Zmod.unsigned base - heapStartAddr config) mod 2 ^ (AddrSz + 1) =
                   Zmod.unsigned base - heapStartAddr config mod 2 ^ (AddrSz + 1)).
    { rewrite <- Zminus_mod_idemp_r; apply Z.mod_small; lia. }
    assert (Hend : (heapStartAddr config + 2 ^ (lgRevGranularity config + 3) * revTableSizeInBytes config)
                     mod 2 ^ (AddrSz + 1) <=
                   heapStartAddr config mod 2 ^ (AddrSz + 1) +
                   2 ^ (lgRevGranularity config + 3) * revTableSizeInBytes config).
    { rewrite <- Zplus_mod_idemp_l; apply Z.mod_le; [nia | lia]. }
    exists (revTableStartAddr config +
            ((Zmod.unsigned base - heapStartAddr config) mod 2 ^ (AddrSz + 1)) / 2 ^ (lgRevGranularity config + 3)).
    split.
    - rewrite Hoff; split.
      + pose proof (Z.div_pos (Zmod.unsigned base - heapStartAddr config mod 2 ^ (AddrSz + 1))
                              (2 ^ (lgRevGranularity config + 3)) ltac:(lia) HP); lia.
      + pose proof (Z.div_lt_upper_bound (Zmod.unsigned base - heapStartAddr config mod 2 ^ (AddrSz + 1))
                                         (2 ^ (lgRevGranularity config + 3)) (revTableSizeInBytes config)
                                         HP ltac:(lia)); lia.
    - apply Zmod.unsigned_inj; rewrite revByteAddrOf_val, Zmod.unsigned_of_Z; reflexivity.
  Qed.

  Lemma capNeedsCheck_revokable : forall c, capNeedsCheck config c = true ->
    evalExpr (isRevokableAddr config (Var type (Bit (AddrSz + 1)) (capBase c))) = true.
  Proof.
    intros c H; unfold capNeedsCheck, needsRevocationCheck in H; cbn [evalExpr map fold_left] in H.
    change (evalAndBinary (k:=Bool)) with andb in H.
    apply andb_prop in H as [_ H]; exact H.
  Qed.
End RevTab.

(* The bounds come from the configuration's own checks *)
Lemma revTableSize_nonneg : forall config, 0 <= revTableSizeInBytes config.
Proof. intros config; apply Z.leb_le, Is_true_eq_true, revTableSizeNonNeg. Qed.

Lemma lgRevGranularity_bounds :
  forall config, 0 <= lgRevGranularity config /\ lgRevGranularity config + 3 <= AddrSz + 1.
Proof.
  intros config; pose proof (Is_true_eq_true _ (lgRevGranularityOK config)) as H.
  apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
Qed.

Lemma revByte_needsCheck_inTable :
  forall config c, capNeedsCheck config c = true ->
    exists a, revTableStartAddr config <= a < revTableStartAddr config + revTableSizeInBytes config /\
              revByteAddrOf config (capBase c) = Zmod.of_Z _ a.
Proof.
  intros config c Hc; destruct (lgRevGranularity_bounds config) as [Hg0 Hg1].
  exact (revByteAddrOf_inTable config Hg0 Hg1 (revTableSize_nonneg config) (capBase c)
           (capNeedsCheck_revokable config c Hc)).
Qed.

(* --- 4. The Table's Lines Are ExternalMem --- *)

(* The value of a line address: the address with its offset in the line cleared *)
Lemma to_Z_lineOf : forall x : type Addr,
  Zmod.to_Z (lineOf false x) = Zmod.to_Z x / 2 ^ LgLineBytes * 2 ^ LgLineBytes.
Proof.
  intros x; unfold lineOf, memLineAddr; cbn [evalExpr].
  assert (HL : 0 <= LgLineBytes <= AddrSz) by (unfold LgLineBytes, AddrSz; lia).
  etransitivity; [apply bits.unsigned_app; lia |].
  rewrite bits.unsigned_app by lia.
  rewrite !Zmod.unsigned_0, !Z.shiftl_0_l, !Z.lor_0_l.
  rewrite to_Z_lastn' by lia; rewrite Z.add_0_l, Z.shiftl_mul_pow2 by lia; reflexivity.
Qed.

(* An address of a region that ends below 2^AddrSz has its line in the region *)
Lemma isRegionAddrB_lineOf : forall r a,
  regionBase r <= a < regionBase r + regionSize r ->
  regionBase r + regionSize r < Z.shiftl 1 AddrSz ->
  isRegionAddrB r (lineOf false (Zmod.of_Z _ a)) = true.
Proof.
  intros r a Ha Hend.
  pose proof (Is_true_eq_true _ (regionInMemory r)) as Hin; apply andb_prop in Hin as [Hb _]; apply Z.leb_le in Hb.
  pose proof (Is_true_eq_true _ (regionBaseAligned r)) as Hal; apply Z.eqb_eq in Hal.
  rewrite Z.shiftl_1_l in Hend.
  assert (HLp : 0 < 2 ^ LgLineBytes) by (apply Z.pow_pos_nonneg; unfold LgLineBytes; lia).
  rewrite isRegionAddrB_eq, to_Z_lineOf, !Zmod.unsigned_of_Z; unfold AddrSz in *.
  rewrite (Z.mod_small a), (Z.mod_small (regionBase r)), (Z.mod_small (regionBase r + regionSize r)) by lia.
  assert (Hlo : regionBase r <= a / 2 ^ LgLineBytes * 2 ^ LgLineBytes).
  { rewrite (Z.div_mod (regionBase r) (2 ^ LgLineBytes)) at 1 by lia; rewrite Hal, Z.add_0_r.
    rewrite (Z.mul_comm (2 ^ LgLineBytes)); apply Z.mul_le_mono_nonneg_r; [lia |].
    apply Z.div_le_mono; lia. }
  assert (Hhi : a / 2 ^ LgLineBytes * 2 ^ LgLineBytes <= a).
  { rewrite Z.mul_comm; apply Z.mul_div_le; lia. }
  apply andb_true_intro; split; [apply negb_true_iff, Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.

(* With disjoint regions, a line's kind is that of any region containing it *)
Lemma lineKind_in_disjoint : forall l r L,
  pairwiseDisjoint l = true -> In r l -> isRegionAddrB r L = true ->
  lineKind l L = Some (match regionKind r with ExternalMem => true | CustomMem _ _ _ _ => false end).
Proof.
  induction l as [| r0 rs IH]; intros r L Hd Hin Hm; [destruct Hin |].
  cbn [pairwiseDisjoint] in Hd; apply andb_prop in Hd as [Hd1 Hd2].
  cbn [lineKind]; destruct Hin as [-> | Hin].
  - rewrite Hm; reflexivity.
  - destruct (isRegionAddrB r0 L) eqn:Hm0.
    + exfalso; pose proof (proj1 (forallb_forall _ _) Hd1 r Hin) as Hdr.
      rewrite (isRegionAddrB_disjoint r0 r L Hdr Hm0) in Hm; discriminate.
    + apply IH; assumption.
Qed.

(* Every line of the table is ExternalMem *)
Lemma revTab_line : forall config l,
  pairwiseDisjoint l = true -> revTableInExternalMem config l = true ->
  forall a, revTableStartAddr config <= a < revTableStartAddr config + revTableSizeInBytes config ->
    lineKind l (lineOf false (Zmod.of_Z _ a)) = Some true.
Proof.
  intros config l Hd Ht a Ha.
  unfold revTableInExternalMem in Ht; apply existsb_exists in Ht as [r [Hin Hr]].
  rewrite (lineKind_in_disjoint l r _ Hd Hin).
  - destruct (regionKind r); [reflexivity | discriminate].
  - destruct (regionKind r); [| discriminate].
    apply andb_prop in Hr as [Hr Hend]; apply andb_prop in Hr as [Hlo Hhi].
    apply Z.leb_le in Hlo; apply Z.leb_le in Hhi; apply Z.ltb_lt in Hend.
    pose proof (revTableSize_nonneg config).
    apply isRegionAddrB_lineOf; lia.
Qed.
