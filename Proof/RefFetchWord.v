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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits SpecDevice.
From Cheriot Require Import ImplCommon ImplDevice ImplFetch.
From Cheriot.Proof Require Import SimDevices RefCoreRel RefFetch RefBits RefConsts RefRevTable RefSnoopMiss RefFetchBits
  RefPcEven DecodeFacts RefFetchRqImpl.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* Milestone 6, the fetched word. The impl assembles an instruction from two 16-bit parcels of a
 * fetch packet (`FromBit FetchPacket (ToBit rp.data)`); the spec reads it as the low word of a
 * capability packet (`memExtractCapPacket`, `memAssembleCapRead`). Both are views of the line's
 * bytes: `digits 8 (bytes of the line)`, element 0 lowest. *)

(* --- 1. Digit strings: a list of w-bit digits as a number, element 0 lowest --- *)

Fixpoint digits (w : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | d :: l' => d + 2 ^ w * digits w l'
  end.

Definition inRange (w : Z) (l : list Z) : Prop := Forall (fun d => 0 <= d < 2 ^ w) l.

Lemma inRange_firstn : forall w l n, inRange w l -> inRange w (firstn n l).
Proof.
  intros w l n H; unfold inRange in *; rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H; exact (proj1 H).
Qed.

Lemma inRange_skipn : forall w l n, inRange w l -> inRange w (skipn n l).
Proof.
  intros w l n H; unfold inRange in *; rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H; exact (proj2 H).
Qed.

Lemma inRange_bits : forall w (l : list (bits w)), 0 <= w -> inRange w (map Zmod.unsigned l).
Proof.
  intros w l Hw; unfold inRange; apply Forall_map; apply Forall_forall; intros x _.
  exact (bits.unsigned_range x Hw).
Qed.

Lemma digits_app :
  forall w l1 l2, 0 <= w ->
    digits w (l1 ++ l2) = digits w l1 + 2 ^ (w * Z.of_nat (length l1)) * digits w l2.
Proof.
  intros w l1 l2 Hw; induction l1 as [| d l1 IH]; cbn [digits app length].
  - rewrite Z.mul_0_r, Z.pow_0_r; lia.
  - rewrite IH, Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by nia; ring.
Qed.

Lemma digits_bound :
  forall w l, 0 <= w -> inRange w l -> 0 <= digits w l < 2 ^ (w * Z.of_nat (length l)).
Proof.
  intros w l Hw; induction l as [| d l IH]; intros Hr; cbn [digits length].
  - rewrite Z.mul_0_r, Z.pow_0_r; lia.
  - inversion Hr as [| ? ? Hd Hl]; subst; specialize (IH Hl).
    rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by nia.
    pose proof (pow2_pos w Hw); nia.
Qed.

Lemma digits_firstn :
  forall w l n, 0 <= w -> inRange w l -> digits w l mod 2 ^ (w * Z.of_nat n) = digits w (firstn n l).
Proof.
  intros w l n Hw Hr.
  pose proof (digits_bound w _ Hw (inRange_firstn w l n Hr)) as Hb.
  pose proof (pow2_pos (w * Z.of_nat n) ltac:(nia)) as Hp.
  rewrite <- (firstn_skipn n l) at 1; rewrite digits_app by exact Hw.
  destruct (Nat.le_gt_cases n (length l)) as [Hle | Hgt].
  - rewrite firstn_length_le in Hb |- * by exact Hle.
    rewrite (Z.mul_comm (2 ^ (w * Z.of_nat n))), Z.mod_add by lia.
    apply Z.mod_small; exact Hb.
  - rewrite skipn_all2 by lia; cbn [digits]; rewrite Z.mul_0_r, Z.add_0_r.
    rewrite firstn_all2 in Hb |- * by lia.
    apply Z.mod_small; split; [lia |].
    eapply Z.lt_le_trans; [exact (proj2 Hb) |].
    apply Z.pow_le_mono_r; [lia | nia].
Qed.

Lemma digits_skipn :
  forall w l n, 0 <= w -> inRange w l -> digits w l / 2 ^ (w * Z.of_nat n) = digits w (skipn n l).
Proof.
  intros w l n Hw Hr.
  pose proof (digits_bound w _ Hw (inRange_firstn w l n Hr)) as Hb.
  pose proof (pow2_pos (w * Z.of_nat n) ltac:(nia)) as Hp.
  rewrite <- (firstn_skipn n l) at 1; rewrite digits_app by exact Hw.
  destruct (Nat.le_gt_cases n (length l)) as [Hle | Hgt].
  - rewrite firstn_length_le in Hb |- * by exact Hle.
    rewrite (Z.mul_comm (2 ^ (w * Z.of_nat n))), Z.div_add by lia.
    rewrite Z.div_small by exact Hb; lia.
  - rewrite skipn_all2 by lia; cbn [digits]; rewrite Z.mul_0_r, Z.add_0_r.
    rewrite firstn_all2 in Hb |- * by lia.
    apply Z.div_small; split; [lia |].
    eapply Z.lt_le_trans; [exact (proj2 Hb) |]; apply Z.pow_le_mono_r; [lia | nia].
Qed.

(* --- 2. Guru's bit arrays: `ToBit` of an array of words is its digit string, `FromBit` reads
 * the digits back --- *)

Lemma unsigned_app_add :
  forall n m (a : bits n) (b : bits m), 0 <= n -> 0 <= m ->
    Zmod.unsigned (Zmod.app a b) = Zmod.unsigned a + 2 ^ n * Zmod.unsigned b.
Proof.
  intros n m a b Hn Hm.
  pose proof (f_equal Zmod.unsigned (Zmod_firstn_app n m a b Hn Hm)) as Hf.
  pose proof (f_equal Zmod.unsigned (Zmod_lastn_app n m a b Hn Hm)) as Hl.
  rewrite bits.unsigned_firstn in Hf.
  rewrite to_Z_lastn in Hl by lia.
  replace (n + m - m) with n in Hl by lia.
  pose proof (pow2_pos n Hn).
  pose proof (Z.div_mod (Zmod.unsigned (Zmod.app a b)) (2 ^ n) ltac:(lia)) as E.
  rewrite Hf, Hl in E; lia.
Qed.

Lemma evalToBitArray_digits :
  forall w n (l : list (bits w)) pf, 0 <= w ->
    Zmod.unsigned (@evalToBitArray n (Bit w) (fun x => x) (@Build_SameTuple _ n l pf)) =
    digits w (map Zmod.unsigned l).
Proof.
  intros w n l; revert n; induction l as [| x xs IH]; intros n pf Hw; destruct n as [| m].
  - cbn [evalToBitArray]; apply Zmod.unsigned_0.
  - destruct pf.
  - destruct pf.
  - rewrite evalToBitArray_S.
    etransitivity;
      [exact (unsigned_app_add w (NatZ_mul m w) x (@evalToBitArray m (Bit w) (fun x => x) (@Build_SameTuple _ m xs pf))
                Hw (NatZ_mul_nonneg m w Hw)) |].
    cbn [map digits]; f_equal; f_equal; exact (IH m pf Hw).
Qed.

Lemma evalFromBitArray_nth_bits :
  forall w n (v : bits (NatZ_mul n w)) i d, 0 <= w -> (i < n)%nat ->
    nth i (tupleElems (@evalFromBitArray n (Bit w) (fun x => x) v)) d =
    Zmod.of_Z _ (Zmod.unsigned v / 2 ^ (w * Z.of_nat i)).
Proof.
  intros w n; induction n as [| m IH]; intros v i d Hw Hi; [lia |].
  rewrite evalFromBitArray_S; cbn [tupleElems].
  destruct i as [| i'].
  - cbn [nth]; rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r; reflexivity.
  - cbn [nth]; rewrite (IH _ i' d Hw ltac:(lia)).
    pose proof (NatZ_mul_nonneg m w Hw) as Hm.
    rewrite to_Z_lastn by (cbn [kindSize]; lia).
    match goal with |- context [Zmod.unsigned v / 2 ^ ?e] => replace e with w by (cbn [kindSize]; lia) end.
    pose proof (pow2_pos w Hw); pose proof (pow2_pos (w * Z.of_nat i') ltac:(nia)).
    rewrite Z.div_div by lia.
    rewrite <- Z.pow_add_r by nia.
    rewrite Nat2Z.inj_succ, Z.mul_succ_r; do 3 f_equal; lia.
Qed.

(* --- 3. The parcels of a line response --- *)

Definition rpBytes (rp : type LineReadRp) : list Z := map Zmod.unsigned rp.(Fst).(tupleElems).

Lemma length_rpBytes : forall rp, length (rpBytes rp) = LineBytes.
Proof.
  intros rp; unfold rpBytes; rewrite length_map.
  apply Nat.eqb_eq, Is_true_eq_true; exact rp.(Fst).(tupleSize).
Qed.

Lemma inRange_rpBytes : forall rp, inRange 8 (rpBytes rp).
Proof. intros rp; apply inRange_bits; lia. Qed.

Lemma parcelIdx_lt : forall k : bits LgFetchParcels, (Z.to_nat (Zmod.unsigned k) < NumFetchParcels)%nat.
Proof.
  intros k; destruct invariant_fetch as [HN [_ [_ [_ [_ [_ [_ [HF _]]]]]]]].
  pose proof (bits.unsigned_range k HF) as Hr.
  apply Nat2Z.inj_lt; rewrite Z2Nat.id, HN by lia; lia.
Qed.

(* The fetch packet, as the array encoders see it *)
Lemma fetchPktOf_arrays :
  forall rp : type LineReadRp,
    fetchPktOf rp =
    @evalFromBitArray NumFetchParcels (Bit CompInstSz) (fun x => x)
      (@evalToBitArray LineBytes (Bit 8) (fun x => x) rp.(Fst)).
Proof. reflexivity. Qed.

(* Parcel `k` of the fetch packet of `rp`: bytes `2k` and `2k+1` of the line (`rpParcel`) *)
Lemma pktParcel_fetchPkt :
  forall (rp : type LineReadRp) (k : bits LgFetchParcels),
    Zmod.unsigned (pktParcel (fetchPktOf rp) k) =
    digits 8 (map Zmod.unsigned (rpParcel rp (Z.to_nat (Zmod.unsigned k)))).
Proof.
  intros rp k.
  destruct invariant_fetch as [HN [HL [HC _]]].
  pose proof (parcelIdx_lt k) as Hi.
  set (i := Z.to_nat (Zmod.unsigned k)) in *.
  assert (EA : Zmod.unsigned (pktParcel (fetchPktOf rp) k) =
               (digits 8 (rpBytes rp) / 2 ^ (CompInstSz * Z.of_nat i)) mod 2 ^ CompInstSz).
  { unfold pktParcel; cbn [evalExpr]; rewrite fetchPktOf_arrays.
    rewrite readNatToFinType_nth by exact Hi.
    rewrite (evalFromBitArray_nth_bits CompInstSz NumFetchParcels) by (first [lia | exact Hi]).
    rewrite Zmod.unsigned_of_Z.
    do 2 f_equal.
    exact (evalToBitArray_digits 8 LineBytes _ (tupleSize rp.(Fst)) ltac:(lia)). }
  rewrite EA.
  replace (CompInstSz * Z.of_nat i) with (8 * Z.of_nat (2 * i)) by lia.
  rewrite (digits_skipn 8 (rpBytes rp) (2 * i) ltac:(lia) (inRange_rpBytes rp)).
  replace (2 ^ CompInstSz) with (2 ^ (8 * Z.of_nat 2)) by (rewrite HC; reflexivity).
  rewrite (digits_firstn 8 _ 2 ltac:(lia) (inRange_skipn _ _ _ (inRange_rpBytes rp))).
  unfold rpParcel, rpBytes; rewrite skipn_map, firstn_map; reflexivity.
Qed.

(* --- 4. The spec's capability packet and word --- *)

(* The elements of a `genFinType` are 0 .. n-1 *)
Lemma nth_map_genFinType :
  forall {A : Type} n (g : FinType n -> A) i d, (i < n)%nat ->
    exists pf, nth i (map g (genFinType n)) d = g (Build_FinType i pf).
Proof.
  intros A n; induction n as [| m IH]; intros g i d Hi; [lia |].
  cbn [genFinType map].
  destruct i as [| i'].
  - exists I; reflexivity.
  - cbn [nth]; rewrite map_map.
    destruct (IH (fun x => g (@Build_FinType (S m) (S x.(finNum)) x.(finLt))) i' d ltac:(lia)) as [pf E].
    exists pf; exact E.
Qed.

(* The spec's word is the low `InstSz` bits of the packet's bytes *)
Lemma specWord_firstn :
  forall (a : type Addr) (pkt : type CapPacket),
    specWord a pkt = Zmod.firstn InstSz (@evalToBitArray (Z.to_nat NumBytesFullCapSz) (Bit 8) (fun x => x) pkt.(Fst)).
Proof. reflexivity. Qed.

Lemma specWord_digits :
  forall (a : type Addr) (pkt : type CapPacket),
    Zmod.unsigned (specWord a pkt) =
    digits 8 (map Zmod.unsigned (firstn (Z.to_nat (InstSz / 8)) pkt.(Fst).(tupleElems))).
Proof.
  intros a pkt.
  destruct invariant_fetch as [_ [_ [HC [HI _]]]].
  rewrite specWord_firstn, bits.unsigned_firstn.
  etransitivity.
  { apply f_equal2; [| reflexivity].
    exact (evalToBitArray_digits 8 (Z.to_nat NumBytesFullCapSz) _ (tupleSize pkt.(Fst)) ltac:(lia)). }
  replace InstSz with (8 * Z.of_nat (Z.to_nat (InstSz / 8))) at 1
    by (rewrite Z2Nat.id by (apply Z.div_pos; lia); rewrite HI, HC; reflexivity).
  rewrite (digits_firstn 8 _ _ ltac:(lia) (inRange_bits 8 _ ltac:(lia))).
  rewrite firstn_map; reflexivity.
Qed.

Lemma evalExpr_ReadArray :
  forall n k m (v : Expr type (Array n k)) (ix : Expr type (Bit m)),
    evalExpr (ReadArray v ix) =
    readNatToFinType (getDefault k) (readSameTuple (evalExpr v)) (Z.to_nat (Zmod.unsigned (evalExpr ix))).
Proof. reflexivity. Qed.

(* Byte `i` of the spec's packet at `a`: byte `(a mod lineBytes + i) mod lineBytes` of the line *)
Lemma specPkt_nth :
  forall (a : type Addr) (rp : type LineReadRp) i d, (i < Z.to_nat NumBytesFullCapSz)%nat ->
    nth i (specPkt a rp).(Fst).(tupleElems) d =
    nth (Z.to_nat ((Zmod.unsigned a mod 2 ^ LgLineBytes + Z.of_nat i) mod 2 ^ LgLineBytes))
        rp.(Fst).(tupleElems) Zmod.zero.
Proof.
  intros a rp i d Hi.
  pose proof lineBytes_pos as HL; pose proof capBytes_le_lineBytes as Hcl.
  pose proof invariant_NumBytesFullCapSz as HN.
  assert (HiZ : Z.of_nat i < 2 ^ LgLineBytes) by (rewrite <- HN in Hcl; lia).
  unfold specPkt, memExtractCapPacket, slice, ArrayBuilder.
  cbn [evalLetExpr evalExpr mapDiffTuple fst snd].
  cbn [evalExpr Fst Snd].
  cbn [mapSameTuple tupleElems]; rewrite map_map.
  match goal with |- nth _ (map ?g _) _ = _ => destruct (nth_map_genFinType _ g i d Hi) as [pf E] end.
  etransitivity; [exact E |]; cbv beta; cbn [finNum].
  rewrite evalExpr_ReadArray.
  match goal with |- readNatToFinType _ _ (Z.to_nat (Zmod.unsigned ?e)) = _ =>
    assert (He : Zmod.unsigned e = (Zmod.unsigned a mod 2 ^ LgLineBytes + Z.of_nat i) mod 2 ^ LgLineBytes) end.
  { unfold memLineOffset; rewrite to_Z_Add2, to_Z_TruncLsb, to_Z_Var, to_Z_const.
    rewrite (Z.mod_small (Z.of_nat i)) by lia; reflexivity. }
  rewrite He.
  pose proof (Z.mod_pos_bound (Zmod.unsigned a mod 2 ^ LgLineBytes + Z.of_nat i) (2 ^ LgLineBytes) HL) as Hb.
  rewrite readNatToFinType_nth by (rewrite lineBytes_nat; apply Z2Nat.inj_lt; lia).
  reflexivity.
Qed.

Lemma evalExpr_ReadArrayConst :
  forall n k (v : Expr type (Array n k)) (i : FinType n) d,
    evalExpr (ReadArrayConst v i) = nth i.(finNum) (evalExpr v).(tupleElems) d.
Proof. intros n k v i d; cbn [evalExpr]; unfold readSameTuple; apply nth_pf_nth. Qed.

Lemma evalExpr_ITE :
  forall k (c : Expr type Bool) (t f : Expr type k),
    evalExpr (ITE c t f) = if evalExpr c then evalExpr t else evalExpr f.
Proof. reflexivity. Qed.

Lemma evalExpr_Not_bits : forall n (x : Expr type (Bit n)), evalExpr (Not x) = Zmod.not (evalExpr x).
Proof. reflexivity. Qed.

Lemma evalExpr_Const : forall k (v : type k), evalExpr (Const type k v) = v.
Proof. reflexivity. Qed.

Lemma evalExpr_Srl :
  forall n m (x : Expr type (Bit n)) (c : Expr type (Bit m)),
    evalExpr (Srl x c) = Zmod.sru (evalExpr x) (Zmod.unsigned (evalExpr c)).
Proof. reflexivity. Qed.

Lemma fromBit_boolArray :
  forall n (e : Expr type (Bit (kindSize (Array n Bool)))),
    evalExpr (FromBit (Array n Bool) e) = @evalFromBitArray n Bool (fun v => Zmod.eqb v Zmod.one) (evalExpr e).
Proof. reflexivity. Qed.

Lemma unsigned_invDefault : forall w, 0 <= w -> Zmod.unsigned (InvDefault (Bit w)) = Z.ones w.
Proof.
  intros w Hw; change (InvDefault (Bit w)) with (Zmod.of_Z (2 ^ w) (-1)).
  rewrite Zmod.unsigned_of_Z, Z.ones_equiv.
  pose proof (pow2_pos w Hw).
  symmetry; apply Z.mod_unique_pos with (q := -1); lia.
Qed.

Lemma nth_indep_tuple :
  forall {A : Type} {n : nat} (t : SameTuple A n) i d d', (i < n)%nat -> nth i t.(tupleElems) d = nth i t.(tupleElems) d'.
Proof.
  intros A n t i d d' Hi; apply nth_indep.
  rewrite (proj1 (Nat.eqb_eq _ _) (Is_true_eq_true _ t.(tupleSize))); exact Hi.
Qed.

(* Byte `i` of the merged packet: from `p1` at and above `capBytes - (a mod capBytes)`, else `p0` *)
Lemma merge_nth :
  forall (a : type Addr) (p0 p1 : type CapPacket) i d, (i < Z.to_nat NumBytesFullCapSz)%nat ->
    nth i (evalExpr (memMergeCapPacket (Var type Addr a) (Var type CapPacket p0) (Var type CapPacket p1))).(Fst).(tupleElems) d =
    if (Z.to_nat NumBytesFullCapSz - Z.to_nat (Zmod.unsigned a mod 2 ^ LgNumBytesFullCapSz) <=? i)%nat
    then nth i p1.(Fst).(tupleElems) Zmod.zero else nth i p0.(Fst).(tupleElems) Zmod.zero.
Proof.
  intros a p0 p1 i d Hi.
  pose proof invariant_NumBytesFullCapSz as HN.
  pose proof LgNumBytesFullCapSz_nonneg as Hc0.
  pose proof capBytes_pos as Hcp.
  unfold memMergeCapPacket, ArrayBuilder.
  cbn [evalExpr mapDiffTuple fst snd Fst Snd].
  cbn [mapSameTuple tupleElems]; rewrite map_map.
  match goal with |- nth _ (map ?g _) _ = _ => destruct (nth_map_genFinType _ g i d Hi) as [pf E] end.
  etransitivity; [exact E |]; cbv beta.
  rewrite evalExpr_ITE.
  rewrite (evalExpr_ReadArrayConst _ Bool _ _ false), !(evalExpr_ReadArrayConst _ (Bit 8) _ _ Zmod.zero); cbn [finNum].
  match goal with |- (if nth _ (tupleElems (evalExpr (FromBit _ ?e))) _ then _ else _) = _ =>
    assert (Hc : nth i (tupleElems (evalExpr (FromBit (Array (Z.to_nat NumBytesFullCapSz) Bool) e))) false =
                 (Z.to_nat NumBytesFullCapSz - Z.to_nat (Zmod.unsigned a mod 2 ^ LgNumBytesFullCapSz) <=? i)%nat) end.
  { rewrite fromBit_boolArray, evalFromBitArray_nth by exact Hi.
    rewrite evalExpr_Not_bits, bits.unsigned_not, evalExpr_Srl.
    rewrite Zmod.unsigned_sru by apply Zmod.unsigned_pos_bound, pow2_pos, Hc0.
    rewrite evalExpr_Const, to_Z_TruncLsb, to_Z_Var.
    match goal with |- context [Z.shiftr _ ?cc] =>
      replace cc with (Zmod.unsigned a mod 2 ^ LgNumBytesFullCapSz) by reflexivity end.
    pose proof (Z.mod_pos_bound (Zmod.unsigned a) (2 ^ LgNumBytesFullCapSz) Hcp) as Hcb.
    set (c := Zmod.unsigned a mod 2 ^ LgNumBytesFullCapSz) in *.
    assert (Hw : kindSize (Array (Z.to_nat NumBytesFullCapSz) Bool) = 2 ^ LgNumBytesFullCapSz)
      by (cbn [kindSize]; rewrite NatZ_mul_n_1, Z2Nat.id by lia; exact HN).
    rewrite unsigned_invDefault by (rewrite Hw; lia).
    rewrite Hw.
    rewrite Z.ldiff_spec, Z.shiftr_spec by lia.
    rewrite !Z.testbit_ones_nonneg by lia.
    assert (HiZ : Z.of_nat i < 2 ^ LgNumBytesFullCapSz) by (rewrite <- HN; lia).
    assert (Hn' : Z.of_nat (Z.to_nat NumBytesFullCapSz) = NumBytesFullCapSz) by (apply Z2Nat.id; lia).
    assert (Hc' : Z.of_nat (Z.to_nat c) = c) by (apply Z2Nat.id; lia).
    destruct (Z.ltb_spec (Z.of_nat i) (2 ^ LgNumBytesFullCapSz)); [| lia].
    destruct (Z.ltb_spec (Z.of_nat i + c) (2 ^ LgNumBytesFullCapSz));
      destruct (Nat.leb_spec (Z.to_nat NumBytesFullCapSz - Z.to_nat c) i); cbn [andb negb];
      first [reflexivity | exfalso; lia]. }
  rewrite Hc.
  destruct (Z.to_nat NumBytesFullCapSz - Z.to_nat (Zmod.unsigned a mod 2 ^ LgNumBytesFullCapSz) <=? i)%nat;
    apply nth_indep_tuple; exact Hi.
Qed.

(* --- 5. Addresses of parcels --- *)

(* `{< high, low >}`, the word the impl assembles from two parcels *)
Definition implWord (high low : type (Bit CompInstSz)) : type Inst :=
  evalExpr ({< Var type (Bit CompInstSz) high, Var type (Bit CompInstSz) low >}).

Lemma implWord_unsigned :
  forall high low, Zmod.unsigned (implWord high low) = Zmod.unsigned low + 2 ^ CompInstSz * Zmod.unsigned high.
Proof.
  intros high low; destruct invariant_fetch as [_ [_ [HC _]]].
  unfold implWord; cbn [evalExpr].
  etransitivity; [exact (unsigned_app_add _ _ (Zmod.app (Zmod.zero : bits 0) low) high ltac:(lia) ltac:(lia)) |].
  rewrite (unsigned_app_add 0 CompInstSz (Zmod.zero : bits 0) low ltac:(lia) ltac:(lia)).
  rewrite Zmod.unsigned_0, !Z.add_0_l, Z.pow_0_r; lia.
Qed.

(* The line offset of parcel `k` of line `A` is `2k` *)
Lemma parcelAddr_off :
  forall (A : type Addr) (k : bits LgFetchParcels),
    Zmod.unsigned A mod 2 ^ LgLineBytes = 0 ->
    Zmod.unsigned (parcelAddrOf A k) mod 2 ^ LgLineBytes = 2 * Zmod.unsigned k.
Proof.
  intros A k HA.
  destruct invariant_fetch as [HN [HL [_ [_ [_ [_ [_ [HF _]]]]]]]].
  pose proof LgLineBytes_lt_AddrSz as HLA.
  pose proof (bits.unsigned_range k HF) as Hk.
  unfold parcelAddrOf, getParcelAddr; cbn [evalExpr].
  etransitivity.
  { apply f_equal2; [| reflexivity].
    exact (unsigned_app_add _ _ (Zmod.app (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits (LgLineBytes - LgFetchParcels))) k)
             (Zmod_lastn (AddrSz - LgLineBytes) A) ltac:(lia) ltac:(lia)). }
  rewrite (unsigned_app_add (0 + (LgLineBytes - LgFetchParcels)) LgFetchParcels
             (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits (LgLineBytes - LgFetchParcels))) k ltac:(lia) ltac:(lia)).
  rewrite (unsigned_app_add 0 (LgLineBytes - LgFetchParcels) (Zmod.zero : bits 0) Zmod.zero ltac:(lia) ltac:(lia)).
  rewrite !Zmod.unsigned_0.
  replace (0 + (LgLineBytes - LgFetchParcels) + LgFetchParcels) with LgLineBytes by lia.
  replace (0 + (LgLineBytes - LgFetchParcels)) with 1 by lia.
  pose proof lineBytes_pos as Hlb.
  rewrite (Z.mul_comm (2 ^ LgLineBytes)), Z.mod_add by lia.
  change (2 ^ 1) with 2; change (2 ^ 0) with 1.
  assert (HL2 : 2 ^ LgLineBytes = 2 * 2 ^ LgFetchParcels)
    by (rewrite <- HL, Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
  rewrite Z.mod_small by lia; lia.
Qed.

(* Parcel `k` of line `A` lies in parcel `k` *)
Lemma packetParcel_parcelAddr :
  forall (A : type Addr) (k : bits LgFetchParcels),
    Zmod.unsigned A mod 2 ^ LgLineBytes = 0 ->
    evalExpr (@getPacketParcel type (parcelAddrOf A k)) = k.
Proof.
  intros A k HA.
  destruct invariant_fetch as [HN [HL [_ [_ [_ [_ [_ [HF _]]]]]]]].
  pose proof (bits.unsigned_range k HF) as Hk.
  pose proof (parcelAddr_off A k HA) as Hoff.
  apply Zmod.unsigned_inj.
  unfold getPacketParcel; cbn [evalExpr].
  rewrite to_Z_lastn by lia.
  replace (LgLineBytes - LgFetchParcels + LgFetchParcels - LgFetchParcels) with 1 by lia.
  match goal with |- @Zmod.unsigned ?m (@Zmod.firstn ?n ?w ?x) / _ = _ =>
    replace (@Zmod.unsigned m (@Zmod.firstn n w x)) with (Zmod.unsigned x mod 2 ^ n)
      by (first [exact (eq_sym (bits.unsigned_firstn x)) | exact (bits.unsigned_firstn x)]) end.
  rewrite Hoff; change (2 ^ 1) with 2; rewrite Z.mul_comm, Z.div_mul; lia.
Qed.

(* An access that runs past the end of its line crosses *)
Lemma crossesB_true : forall (a : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)),
  2 ^ LgLineBytes < Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz ->
  crossesB a sz = true.
Proof.
  intros a sz H.
  pose proof (size_pow_bound (Zmod.to_Z sz) (Zmod.unsigned_pos_bound sz ltac:(reflexivity))) as Hp.
  pose proof capBytes_le_lineBytes as Hcl.
  pose proof lineBytes_pos as Hlb.
  pose proof (Z.mod_pos_bound (Zmod.to_Z a) (2 ^ LgLineBytes) Hlb) as Hlo.
  unfold crossesB, memCrossesLine, memLineOffset.
  match goal with |- evalExpr (FromBit Bool ?e) = true =>
    change (Zmod.eqb (evalExpr e) Zmod.one = true) end.
  unfold Zmod.eqb.
  match goal with |- context [evalExpr (TruncMsb 1 LgLineBytes ?x)] =>
    change (evalExpr (TruncMsb 1 LgLineBytes x)) with (Zmod_lastn 1 (evalExpr x)) end.
  rewrite to_Z_lastn' by (cbv; congruence).
  rewrite to_Z_Sub by (cbv; congruence).
  rewrite to_Z_Add2, to_Z_Sll.
  rewrite !to_Z_ZeroExtend by (cbv; congruence).
  rewrite to_Z_TruncLsb, !to_Z_Var, !to_Z_const.
  change (Zmod.to_Z (@Zmod.one (2 ^ 1))) with 1.
  rewrite lineBytes_succ.
  rewrite (Z.mod_small 1) by lia.
  rewrite Z.shiftl_1_l.
  rewrite (Z.mod_small (2 ^ Zmod.to_Z sz)) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz)) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz - 1)) by lia.
  replace ((Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz - 1) / 2 ^ LgLineBytes) with 1
    by (apply Z.div_unique_pos with (r := Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz - 1 - 2 ^ LgLineBytes); lia).
  reflexivity.
Qed.

(* --- 6. The words --- *)

Lemma firstn_plus : forall {A : Type} n m (l : list A), firstn (n + m) l = (firstn n l ++ firstn m (skipn n l))%list.
Proof.
  intros A n; induction n as [| n IH]; intros m l; [reflexivity |].
  destruct l as [| x l]; [cbn; rewrite firstn_nil; reflexivity |].
  cbn [firstn skipn app Nat.add]; rewrite IH; reflexivity.
Qed.

Lemma pktParcel_default : forall k : bits LgFetchParcels, pktParcel (getDefault FetchPacket) k = Zmod.zero.
Proof.
  intros k; unfold pktParcel; rewrite evalExpr_ReadArray; cbn [evalExpr].
  rewrite readNatToFinType_nth by exact (parcelIdx_lt k).
  unfold FetchPacket; cbn [getDefault SameTupleDefault tupleElems].
  apply nth_repeat.
Qed.

Lemma implWord_zero : implWord Zmod.zero Zmod.zero = Zmod.zero.
Proof.
  apply Zmod.unsigned_inj; rewrite implWord_unsigned, !Zmod.unsigned_0; lia.
Qed.

Lemma defaultPkt_nth :
  forall i, nth i (evalExpr (Const type CapPacket (getDefault CapPacket))).(Fst).(tupleElems) Zmod.zero = Zmod.zero.
Proof.
  intros i; cbn [evalExpr]; unfold CapPacket.
  cbn [getDefault DiffTupleDefault SameTupleDefault Fst tupleElems].
  apply nth_repeat.
Qed.

(* The bytes `o`, .., `o+n-1` of the line *)
Definition lineBytesAt (rp : type LineReadRp) (o n : nat) : list Z := firstn n (skipn o (rpBytes rp)).

Lemma rpParcel_bytesAt : forall rp p, map Zmod.unsigned (rpParcel rp p) = lineBytesAt rp (2 * p) 2.
Proof. intros rp p; unfold rpParcel, lineBytesAt, rpBytes; rewrite skipn_map, firstn_map; reflexivity. Qed.

Lemma lineBytesAt_split :
  forall rp o n m, lineBytesAt rp o (n + m) = (lineBytesAt rp o n ++ lineBytesAt rp (o + n) m)%list.
Proof.
  intros rp o n m; unfold lineBytesAt; rewrite firstn_plus, skipn_skipn, (Nat.add_comm n o); reflexivity.
Qed.

Lemma length_lineBytesAt : forall rp o n, (o + n <= LineBytes)%nat -> length (lineBytesAt rp o n) = n.
Proof.
  intros rp o n H; unfold lineBytesAt; rewrite firstn_length_le; [reflexivity |].
  rewrite length_skipn, length_rpBytes; lia.
Qed.

(* --- 7. Parcel and instruction sizes in bytes --- *)

Definition parcelBytes : nat := Z.to_nat (CompInstSz / 8).
Definition instBytes : nat := Z.to_nat (InstSz / 8).

Lemma parcelBytes_eq : parcelBytes = 2%nat.
Proof. destruct invariant_fetch as [_ [_ [HC _]]]; unfold parcelBytes; rewrite HC; reflexivity. Qed.

Lemma instBytes_eq : instBytes = 4%nat.
Proof. destruct invariant_fetch as [_ [_ [HC [HI _]]]]; unfold instBytes; rewrite HI, HC; reflexivity. Qed.

Lemma instBytes_le_cap : (instBytes <= Z.to_nat NumBytesFullCapSz)%nat.
Proof.
  destruct invariant_fetch as [_ [_ [_ [_ [H5 [H6 [H7 _]]]]]]].
  pose proof invariant_NumBytesFullCapSz as HN.
  unfold instBytes; rewrite <- H5, HN.
  apply Z2Nat.inj_le; [apply Z.pow_nonneg; lia | apply Z.pow_nonneg; lia | apply Z.pow_le_mono_r; lia].
Qed.

Lemma lineBytes_parcels : 2 ^ LgLineBytes = 2 * 2 ^ LgFetchParcels.
Proof.
  destruct invariant_fetch as [_ [HL [_ [_ [_ [_ [_ [HF _]]]]]]]].
  rewrite <- HL, Z.pow_add_r by lia; change (2 ^ 1) with 2; lia.
Qed.

(* A line holds at least two parcels (an instruction's worth). *)
Lemma parcels_ge2 : 2 <= 2 ^ LgFetchParcels.
Proof.
  destruct invariant_fetch as [_ [HL [_ [_ [_ [H6 [H7 [HF H9]]]]]]]].
  pose proof lineBytes_parcels as HL2.
  pose proof capBytes_le_lineBytes as Hcl.
  assert (Hic : 2 ^ LgNumBytesInstSz <= 2 ^ LgNumBytesFullCapSz) by (apply Z.pow_le_mono_r; lia).
  replace (LgLineBytes - LgFetchParcels) with 1 in H9 by lia.
  rewrite Z.pow_1_r in H9; lia.
Qed.

Lemma lastParcel_unsigned : Zmod.unsigned lastParcel = 2 ^ LgFetchParcels - 1.
Proof.
  destruct invariant_fetch as [_ [_ [_ [_ [_ [_ [_ [HF _]]]]]]]].
  unfold lastParcel; rewrite evalExpr_Const, unsigned_invDefault, Z.ones_equiv by exact HF; lia.
Qed.

(* The impl's word from parcels `k` and `k+1` is the bytes `2k` .. `2k+3` *)
Lemma implWord_bytes :
  forall rp (k k1 : bits LgFetchParcels),
    Zmod.unsigned k1 = Zmod.unsigned k + 1 -> Zmod.unsigned k + 1 < 2 ^ LgFetchParcels ->
    Zmod.unsigned (implWord (pktParcel (fetchPktOf rp) k1) (pktParcel (fetchPktOf rp) k)) =
    digits 8 (lineBytesAt rp (parcelBytes * Z.to_nat (Zmod.unsigned k)) instBytes).
Proof.
  intros rp k k1 Hk1 Hlt.
  destruct invariant_fetch as [HN [HL [HC [_ [_ [_ [_ [HF _]]]]]]]].
  pose proof (bits.unsigned_range k HF) as Hk.
  rewrite parcelBytes_eq, instBytes_eq.
  rewrite implWord_unsigned, !pktParcel_fetchPkt, !rpParcel_bytesAt.
  rewrite Hk1, Z2Nat.inj_add by lia; change (Z.to_nat 1) with 1%nat.
  change 4%nat with (2 + 2)%nat; rewrite lineBytesAt_split.
  rewrite (digits_app 8 _ _ ltac:(lia)).
  rewrite length_lineBytesAt.
  - rewrite HC; replace (2 * (Z.to_nat (Zmod.unsigned k) + 1))%nat with (2 * Z.to_nat (Zmod.unsigned k) + 2)%nat by lia.
    reflexivity.
  - assert (HLB : Z.of_nat LineBytes = 2 * 2 ^ LgFetchParcels)
      by (rewrite invariant_LineBytes, <- HL, Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
    pose proof (Z2Nat.id (Zmod.unsigned k) ltac:(lia)) as Hid.
    apply Nat2Z.inj_le; rewrite HLB; lia.
Qed.

(* --- 8. The spec's word at a parcel address --- *)

Lemma map_unsigned_nth :
  forall w (l : list (bits w)) j, nth j (map Zmod.unsigned l) 0 = Zmod.unsigned (nth j l Zmod.zero).
Proof.
  intros w l; induction l as [| x l IH]; intros j; destruct j as [| j]; cbn [map nth];
    first [reflexivity | symmetry; apply Zmod.unsigned_0 | apply IH].
Qed.

Lemma lineBytesAt_nth :
  forall rp o n j, (j < n)%nat ->
    nth j (lineBytesAt rp o n) 0 = Zmod.unsigned (nth (o + j) rp.(Fst).(tupleElems) Zmod.zero).
Proof.
  intros rp o n j Hj; unfold lineBytesAt, rpBytes.
  rewrite nth_firstn; destruct (Nat.ltb_spec j n); [| lia].
  rewrite nth_skipn; apply map_unsigned_nth.
Qed.

(* The first `n` bytes of the spec's packet at `fp` (line offset `o`): the line's bytes from `o` *)
Lemma specPkt_bytesAt :
  forall (fp : type Addr) (rp : type LineReadRp) (o : Z) n,
    Zmod.unsigned fp mod 2 ^ LgLineBytes = o -> (n <= Z.to_nat NumBytesFullCapSz)%nat ->
    o + Z.of_nat n <= 2 ^ LgLineBytes ->
    map Zmod.unsigned (firstn n (specPkt fp rp).(Fst).(tupleElems)) = lineBytesAt rp (Z.to_nat o) n.
Proof.
  intros fp rp o n Ho Hn Hb.
  pose proof lineBytes_pos as HL.
  assert (Ho0 : 0 <= o) by (rewrite <- Ho; apply Z.mod_pos_bound; exact HL).
  assert (Hlen : length (specPkt fp rp).(Fst).(tupleElems) = Z.to_nat NumBytesFullCapSz)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_map, firstn_length_le by lia.
    rewrite length_lineBytesAt; [reflexivity |].
    rewrite lineBytes_nat; apply Nat2Z.inj_le; rewrite Nat2Z.inj_add, !Z2Nat.id by lia; exact Hb.
  - intros j Hj; rewrite length_map, firstn_length_le in Hj by lia.
    rewrite map_unsigned_nth, nth_firstn; destruct (Nat.ltb_spec j n); [| lia].
    rewrite specPkt_nth by lia; rewrite Ho.
    rewrite lineBytesAt_nth by exact Hj.
    rewrite Z.mod_small by lia.
    rewrite Z2Nat.inj_add, Nat2Z.id by lia; reflexivity.
Qed.

(* A word inside its line: the spec's word at parcel `k` is the impl's word of parcels `k`, `k+1` *)
Lemma specWord_inline :
  forall (fp : type Addr) (k k1 : bits LgFetchParcels) (rp : type LineReadRp),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 * Zmod.unsigned k ->
    Zmod.unsigned k1 = Zmod.unsigned k + 1 -> Zmod.unsigned k + 1 < 2 ^ LgFetchParcels ->
    specWord fp (specPkt fp rp) = implWord (pktParcel (fetchPktOf rp) k1) (pktParcel (fetchPktOf rp) k).
Proof.
  intros fp k k1 rp Ho Hk1 Hlt.
  destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
  pose proof (bits.unsigned_range k HF) as Hk.
  pose proof lineBytes_parcels as HL2.
  apply Zmod.unsigned_inj.
  rewrite implWord_bytes by assumption.
  rewrite specWord_digits; change (Z.to_nat (InstSz / 8)) with instBytes.
  rewrite (specPkt_bytesAt fp rp (2 * Zmod.unsigned k) instBytes Ho instBytes_le_cap).
  - rewrite Z2Nat.inj_mul, parcelBytes_eq by lia; reflexivity.
  - rewrite instBytes_eq; lia.
Qed.

(* The low parcel of the spec's word at parcel `k` is parcel `k` (also in the last parcel) *)
Lemma specWord_low :
  forall (fp : type Addr) (k : bits LgFetchParcels) (rp : type LineReadRp),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 * Zmod.unsigned k ->
    Zmod.unsigned (specWord fp (specPkt fp rp)) mod 2 ^ CompInstSz = Zmod.unsigned (pktParcel (fetchPktOf rp) k).
Proof.
  intros fp k rp Ho.
  destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
  pose proof (bits.unsigned_range k HF) as Hk.
  pose proof lineBytes_parcels as HL2.
  pose proof instBytes_le_cap as Hc4; rewrite instBytes_eq in Hc4.
  rewrite specWord_digits, pktParcel_fetchPkt, rpParcel_bytesAt.
  replace (2 ^ CompInstSz) with (2 ^ (8 * Z.of_nat 2)) by (rewrite HC; reflexivity).
  rewrite digits_firstn by (first [lia | apply inRange_bits; lia]).
  rewrite firstn_map, firstn_firstn.
  change (Z.to_nat (InstSz / 8)) with instBytes; rewrite instBytes_eq; change (Nat.min 2 4) with 2%nat.
  rewrite (specPkt_bytesAt fp rp (2 * Zmod.unsigned k) 2 Ho ltac:(lia) ltac:(lia)).
  rewrite Z2Nat.inj_mul by lia; reflexivity.
Qed.

(* The merged packet at the last parcel: bytes 0, 1 from the first packet, the rest from the second *)
Lemma merge_bytes_last :
  forall (fp : type Addr) (p0 p1 : type CapPacket) j,
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 -> (j < Z.to_nat NumBytesFullCapSz)%nat ->
    nth j (evalExpr (memMergeCapPacket (Var type Addr fp) (Var type CapPacket p0) (Var type CapPacket p1))).(Fst).(tupleElems)
        Zmod.zero =
    if (2 <=? j)%nat then nth j p1.(Fst).(tupleElems) Zmod.zero else nth j p0.(Fst).(tupleElems) Zmod.zero.
Proof.
  intros fp p0 p1 j Ho Hj.
  destruct invariant_fetch as [_ [_ [_ [_ [H5 [H6 [H7 _]]]]]]].
  pose proof invariant_NumBytesFullCapSz as HN.
  pose proof invariant_geometry as [[Hc0 Hcl] _].
  pose proof (pow2_pos LgNumBytesFullCapSz Hc0) as Hcp.
  pose proof lineBytes_pos as Hlp.
  assert (H4 : 4 <= 2 ^ LgNumBytesFullCapSz).
  { pose proof instBytes_le_cap as Hc4; rewrite instBytes_eq, HN in Hc4.
    apply Nat2Z.inj_le in Hc4; rewrite Z2Nat.id in Hc4 by lia; exact Hc4. }
  rewrite merge_nth by exact Hj.
  assert (HLc : 2 ^ LgLineBytes = 2 ^ LgNumBytesFullCapSz * 2 ^ (LgLineBytes - LgNumBytesFullCapSz))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hoff : Zmod.unsigned fp mod 2 ^ LgNumBytesFullCapSz = 2 ^ LgNumBytesFullCapSz - 2).
  { rewrite <- (Z.mod_mod_divide (Zmod.unsigned fp) (2 ^ LgLineBytes) (2 ^ LgNumBytesFullCapSz))
      by (exists (2 ^ (LgLineBytes - LgNumBytesFullCapSz)); lia).
    rewrite Ho.
    symmetry; apply Z.mod_unique_pos with (q := 2 ^ (LgLineBytes - LgNumBytesFullCapSz) - 1); nia. }
  rewrite Hoff, HN.
  replace (Z.to_nat (2 ^ LgNumBytesFullCapSz) - Z.to_nat (2 ^ LgNumBytesFullCapSz - 2))%nat with 2%nat; [reflexivity |].
  rewrite Z2Nat.inj_sub by lia; change (Z.to_nat 2) with 2%nat.
  pose proof (Z2Nat.id (2 ^ LgNumBytesFullCapSz) ltac:(lia)); lia.
Qed.

(* The spec's word at the last parcel of the line, merged with a second packet whose bytes 2, 3
 * make the parcel `high`: the impl's word `{< high, last parcel >}` *)
Lemma specWord_merged :
  forall (fp : type Addr) (rp0 : type LineReadRp) (p1 : type CapPacket) (high : type (Bit CompInstSz)),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 ->
    Zmod.unsigned high = digits 8 (map Zmod.unsigned (firstn 2 (skipn 2 p1.(Fst).(tupleElems)))) ->
    specWord fp (evalExpr (memMergeCapPacket (Var type Addr fp) (Var type CapPacket (specPkt fp rp0)) (Var type CapPacket p1))) =
    implWord high (pktParcel (fetchPktOf rp0) lastParcel).
Proof.
  intros fp rp0 p1 high Ho Hhigh.
  destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
  pose proof lineBytes_parcels as HL2.
  pose proof lineBytes_pos as Hlp.
  pose proof (pow2_pos LgFetchParcels HF) as Hfp.
  pose proof instBytes_le_cap as Hc4; rewrite instBytes_eq in Hc4.
  assert (Hlen1 : length p1.(Fst).(tupleElems) = Z.to_nat NumBytesFullCapSz)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  assert (Hlenm : length (evalExpr (memMergeCapPacket (Var type Addr fp) (Var type CapPacket (specPkt fp rp0))
                                      (Var type CapPacket p1))).(Fst).(tupleElems) = Z.to_nat NumBytesFullCapSz)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  apply Zmod.unsigned_inj.
  rewrite implWord_unsigned, Hhigh, pktParcel_fetchPkt, rpParcel_bytesAt, lastParcel_unsigned.
  rewrite specWord_digits; change (Z.to_nat (InstSz / 8)) with instBytes; rewrite instBytes_eq.
  set (L1 := lineBytesAt rp0 (2 * Z.to_nat (2 ^ LgFetchParcels - 1)) 2).
  set (L2 := map Zmod.unsigned (firstn 2 (skipn 2 p1.(Fst).(tupleElems)))).
  assert (HlenL1 : length L1 = 2%nat).
  { unfold L1; apply length_lineBytesAt.
    rewrite lineBytes_nat; apply Nat2Z.inj_le.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id by lia; lia. }
  assert (EL : map Zmod.unsigned
                 (firstn 4 (evalExpr (memMergeCapPacket (Var type Addr fp) (Var type CapPacket (specPkt fp rp0))
                                        (Var type CapPacket p1))).(Fst).(tupleElems)) = (L1 ++ L2)%list).
  { apply nth_ext with (d := 0) (d' := 0).
    - rewrite length_map, firstn_length_le by lia.
      rewrite length_app, HlenL1; unfold L2; rewrite length_map, firstn_length_le; [reflexivity |].
      rewrite length_skipn; lia.
    - intros j Hj; rewrite length_map, firstn_length_le in Hj by lia.
      rewrite map_unsigned_nth, nth_firstn; destruct (Nat.ltb_spec j 4); [| lia].
      rewrite merge_bytes_last by (first [exact Ho | lia]).
      destruct (Nat.leb_spec 2 j).
      + rewrite app_nth2 by lia; rewrite HlenL1; unfold L2.
        rewrite map_unsigned_nth, nth_firstn; destruct (Nat.ltb_spec (j - 2) 2); [| lia].
        rewrite nth_skipn; replace (2 + (j - 2))%nat with j by lia; reflexivity.
      + rewrite app_nth1 by lia; unfold L1.
        rewrite lineBytesAt_nth by lia.
        rewrite specPkt_nth by lia; rewrite Ho.
        rewrite Z.mod_small by lia.
        f_equal; f_equal.
        apply Nat2Z.inj; rewrite Z2Nat.id, Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id by lia; lia. }
  rewrite EL, (digits_app 8 L1 L2 ltac:(lia)), HlenL1.
  replace (2 ^ CompInstSz) with (2 ^ (8 * Z.of_nat 2)) by (rewrite HC; reflexivity).
  reflexivity.
Qed.

(* A 4-byte instruction in the last parcel that fails the top check: its upper parcel reads 0 *)
Lemma specWord_lastTop :
  forall (fp : type Addr) (rp : type LineReadRp),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 ->
    specWord fp (evalExpr (memMergeCapPacket (Var type Addr fp) (Var type CapPacket (specPkt fp rp))
                             (Var type CapPacket (evalExpr (Const type CapPacket (getDefault CapPacket)))))) =
    implWord Zmod.zero (pktParcel (fetchPktOf rp) lastParcel).
Proof.
  intros fp rp Ho; apply specWord_merged; [exact Ho |].
  pose proof instBytes_le_cap as Hc4; rewrite instBytes_eq in Hc4.
  assert (Hlen : length (evalExpr (Const type CapPacket (getDefault CapPacket))).(Fst).(tupleElems) = Z.to_nat NumBytesFullCapSz)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  rewrite Zmod.unsigned_0.
  assert (E : firstn 2 (skipn 2 (evalExpr (Const type CapPacket (getDefault CapPacket))).(Fst).(tupleElems)) =
              [Zmod.zero; Zmod.zero]).
  { apply nth_ext with (d := Zmod.zero) (d' := Zmod.zero).
    - rewrite firstn_length_le; [reflexivity |]; rewrite length_skipn, Hlen; lia.
    - intros j Hj; rewrite firstn_length_le in Hj by (rewrite length_skipn, Hlen; lia).
      rewrite nth_firstn; destruct (Nat.ltb_spec j 2); [| lia].
      rewrite nth_skipn, defaultPkt_nth.
      destruct j as [| [| j]]; [reflexivity | reflexivity | lia]. }
  rewrite E; cbn [map digits]; rewrite Zmod.unsigned_0; lia.
Qed.

(* A straddling instruction: low parcel from the first line, upper parcel from the second *)
Lemma specWord_straddle :
  forall (fp : type Addr) (rp0 rp1 : type LineReadRp),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 ->
    specWord fp (evalExpr (memMergeCapPacket (Var type Addr fp) (Var type CapPacket (specPkt fp rp0))
                             (Var type CapPacket (specPkt fp rp1)))) =
    implWord (pktParcel (fetchPktOf rp1) Zmod.zero) (pktParcel (fetchPktOf rp0) lastParcel).
Proof.
  intros fp rp0 rp1 Ho; apply specWord_merged; [exact Ho |].
  destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
  pose proof lineBytes_parcels as HL2.
  pose proof (pow2_pos LgFetchParcels HF) as Hfp.
  pose proof instBytes_le_cap as Hc4; rewrite instBytes_eq in Hc4.
  assert (Hlen : length (specPkt fp rp1).(Fst).(tupleElems) = Z.to_nat NumBytesFullCapSz)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  rewrite pktParcel_fetchPkt, rpParcel_bytesAt, Zmod.unsigned_0; change (2 * Z.to_nat 0)%nat with 0%nat.
  assert (HLB : (0 + 2 <= LineBytes)%nat)
    by (rewrite lineBytes_nat; apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  f_equal.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_lineBytesAt by exact HLB.
    rewrite length_map, firstn_length_le; [reflexivity |]; rewrite length_skipn, Hlen; lia.
  - intros j Hj; rewrite length_lineBytesAt in Hj by exact HLB.
    rewrite lineBytesAt_nth by exact Hj.
    rewrite map_unsigned_nth, nth_firstn; destruct (Nat.ltb_spec j 2); [| lia].
    rewrite nth_skipn, specPkt_nth by lia; rewrite Ho.
    replace ((2 ^ LgLineBytes - 2 + Z.of_nat (2 + j)) mod 2 ^ LgLineBytes) with (Z.of_nat j)
      by (apply Z.mod_unique_pos with (q := 1); lia).
    rewrite Nat2Z.id; cbn [Nat.add]; reflexivity.
Qed.

(* --- 9. Boolean evaluation helpers (the action's small boolean expressions) --- *)

Lemma and2not_eval : forall a b : bool,
  evalExpr (And [Not (Var type Bool a); Not (Var type Bool b)]) = andb (negb a) (negb b).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma and2_eval : forall a b : bool, evalExpr (And [Var type Bool a; Not (Var type Bool b)]) = andb a (negb b).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma and2nv_eval : forall a b : bool, evalExpr (And [Not (Var type Bool a); Var type Bool b]) = andb (negb a) b.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma and3n_eval : forall a b c : bool,
  evalExpr (And [Not (Var type Bool a); Not (Var type Bool b); Var type Bool c]) = andb (andb (negb a) (negb b)) c.
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma or2_eval : forall (a b : Expr type Bool), evalExpr (Or [a; b]) = orb (evalExpr a) (evalExpr b).
Proof. intros a b; cbn [evalExpr map fold_left]; destruct (evalExpr a), (evalExpr b); reflexivity. Qed.

Lemma isAllOnes_eval : forall n (e : Expr type (Bit n)),
  evalExpr (isAllOnes e) = Zmod.eqb (evalExpr e) (InvDefault (Bit n)).
Proof. reflexivity. Qed.

Lemma ITE0_eval : forall k (c : Expr type Bool) (e : Expr type k),
  evalExpr (ITE0 c e) = if evalExpr c then evalExpr e else getDefault k.
Proof. reflexivity. Qed.

Lemma eqBits_eval : forall n (a b : Expr type (Bit n)), evalExpr (Eq a b) = Zmod.eqb (evalExpr a) (evalExpr b).
Proof. reflexivity. Qed.

Lemma ugt_eval : forall n (a b : type (Bit n)),
  evalExpr (Ugt (Var type (Bit n) a) (Var type (Bit n) b)) = Z.ltb (Zmod.unsigned b) (Zmod.unsigned a).
Proof. reflexivity. Qed.

(* --- 10. Parcel addresses --- *)

Lemma parcelAddr_unsigned :
  forall (A : type Addr) (k : bits LgFetchParcels),
    Zmod.unsigned A mod 2 ^ LgLineBytes = 0 ->
    Zmod.unsigned (parcelAddrOf A k) = Zmod.unsigned A + 2 * Zmod.unsigned k.
Proof.
  intros A k HA.
  destruct invariant_fetch as [HN [HL [_ [_ [_ [_ [_ [HF _]]]]]]]].
  pose proof LgLineBytes_lt_AddrSz as HLA.
  pose proof (bits.unsigned_range k HF) as Hk.
  pose proof lineBytes_pos as Hlb.
  unfold parcelAddrOf, getParcelAddr; cbn [evalExpr].
  etransitivity.
  { exact (unsigned_app_add _ _ (Zmod.app (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits (LgLineBytes - LgFetchParcels))) k)
             (Zmod_lastn (AddrSz - LgLineBytes) A) ltac:(lia) ltac:(lia)). }
  rewrite (unsigned_app_add (0 + (LgLineBytes - LgFetchParcels)) LgFetchParcels
             (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits (LgLineBytes - LgFetchParcels))) k ltac:(lia) ltac:(lia)).
  rewrite (unsigned_app_add 0 (LgLineBytes - LgFetchParcels) (Zmod.zero : bits 0) Zmod.zero ltac:(lia) ltac:(lia)).
  rewrite !Zmod.unsigned_0.
  replace (0 + (LgLineBytes - LgFetchParcels) + LgFetchParcels) with LgLineBytes by lia.
  replace (0 + (LgLineBytes - LgFetchParcels)) with 1 by lia.
  change (2 ^ 1) with 2; change (2 ^ 0) with 1.
  rewrite to_Z_lastn by (first [lia | cbv; congruence]).
  pose proof (Z.div_mod (Zmod.unsigned A) (2 ^ LgLineBytes) ltac:(lia)) as E; rewrite HA in E.
  match goal with |- context [Zmod.unsigned A / 2 ^ ?e] =>
    replace e with LgLineBytes by (first [lia | cbv; congruence]) end.
  lia.
Qed.

Lemma lineAddr_parcelAddr :
  forall (A : type Addr) (k : bits LgFetchParcels),
    Zmod.unsigned A mod 2 ^ LgLineBytes = 0 -> lineAddrOf (parcelAddrOf A k) = A.
Proof.
  intros A k HA.
  destruct invariant_fetch as [HN [HL [_ [_ [_ [_ [_ [HF _]]]]]]]].
  pose proof (bits.unsigned_range k HF) as Hk.
  pose proof lineBytes_parcels as HL2.
  pose proof lineBytes_pos as Hlb.
  apply Zmod.unsigned_inj; rewrite lineAddr_div, parcelAddr_unsigned by exact HA.
  pose proof (Z.div_mod (Zmod.unsigned A) (2 ^ LgLineBytes) ltac:(lia)) as E; rewrite HA, Z.add_0_r in E.
  rewrite E at 1.
  rewrite (Z.mul_comm (2 ^ LgLineBytes)), Z.div_add_l by lia.
  rewrite (Z.div_small (2 * Zmod.unsigned k)) by lia; lia.
Qed.

Lemma lineAddr_aligned : forall (x : type Addr), Zmod.unsigned (lineAddrOf x) mod 2 ^ LgLineBytes = 0.
Proof.
  intros x; rewrite lineAddr_div; pose proof lineBytes_pos; apply Z.mod_mul; lia.
Qed.

Lemma parcelAddr_even :
  forall (A : type Addr) (k : bits LgFetchParcels), Zmod.unsigned A mod 2 ^ LgLineBytes = 0 -> pcAligned (parcelAddrOf A k).
Proof.
  intros A k HA.
  destruct invariant_fetch as [HN [HL [_ [_ [_ [_ [_ [HF _]]]]]]]].
  apply pcAligned_iff; change (Zmod.to_Z (parcelAddrOf A k)) with (Zmod.unsigned (parcelAddrOf A k)).
  rewrite parcelAddr_unsigned by exact HA.
  pose proof lineBytes_parcels as HL2.
  rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia.
  rewrite <- (Z.mod_mod_divide (Zmod.unsigned A) (2 ^ LgLineBytes) 2) by (exists (2 ^ LgFetchParcels); lia).
  rewrite HA; reflexivity.
Qed.

(* --- 11. The top check --- *)

Lemma AdderAccessEnd_unsigned :
  forall (pc : type Addr) (lg : type (Bit LgLgNumBytesFullCapSz)),
    Zmod.unsigned (evalLetExpr (AdderAccessEnd (ty := type) pc lg)) = Zmod.unsigned pc + 2 ^ Zmod.unsigned lg.
Proof.
  intros pc lg.
  pose proof (size_pow_bound (Zmod.unsigned lg) (Zmod.unsigned_pos_bound lg ltac:(reflexivity))) as Hp.
  pose proof capBytes_le_lineBytes as Hcl; pose proof lineBytes_lt_addrBytes as Hla.
  assert (Hpc : 0 <= Zmod.unsigned pc < 2 ^ AddrSz) by exact (bits.unsigned_range pc ltac:(cbv; congruence)).
  pose proof addrBytes_pos as Hab.
  assert (H2 : 2 ^ (AddrSz + 2) = 4 * 2 ^ AddrSz) by (rewrite Z.pow_add_r by (cbv; congruence); lia).
  unfold AdderAccessEnd; cbn [evalLetExpr].
  rewrite to_Z_Var, to_Z_Add2; unfold ZeroExtendTo; rewrite to_Z_ZeroExtend by (cbv; congruence).
  rewrite !to_Z_Var, to_Z_Sll, to_Z_const, to_Z_Var.
  rewrite !H2.
  rewrite (Z.mod_small 1) by lia.
  rewrite Z.shiftl_1_l, (Z.mod_small (2 ^ Zmod.unsigned lg)) by lia.
  apply Z.mod_small; lia.
Qed.

Lemma memFetchTopExc_eval :
  forall (e t : type (Bit (AddrSz + 2))),
    evalExpr (memFetchTopExc (Var type (Bit (AddrSz + 2)) e) (Var type (Bit (AddrSz + 2)) t)) =
    orb (Z.ltb (Zmod.unsigned t) (Zmod.unsigned e)) (Z.ltb (2 ^ AddrSz) (Zmod.unsigned e)).
Proof.
  intros e t; unfold memFetchTopExc; rewrite or2_eval; unfold Ugt; cbn [evalExpr].
  pose proof addrBytes_pos as Hab.
  assert (H2 : 2 ^ (AddrSz + 2) = 4 * 2 ^ AddrSz) by (rewrite Z.pow_add_r by (cbv; congruence); lia).
  rewrite Zmod.unsigned_of_Z, (Z.mod_small (2 ^ AddrSz)) by lia; reflexivity.
Qed.

Lemma pccWithAddr_addr :
  forall (pcc : type FullECapWithTag) (pc : type Addr),
    evalExpr ((Var type FullECapWithTag (pccWithAddr pcc pc))`"addr") = pc.
Proof. intros [t [e [a []]]] pc; reflexivity. Qed.

Lemma pccWithAddr_ecap :
  forall (pcc : type FullECapWithTag) (pc : type Addr),
    evalExpr ((Var type FullECapWithTag (pccWithAddr pcc pc))`"ecap") = evalExpr ((Var type FullECapWithTag pcc)`"ecap").
Proof. intros [t [e [a []]]] pc; reflexivity. Qed.

(* The top check of a compressed instruction, as `specFetch` does it for a pre-faulted one *)
Lemma specPreFaultTopExc_eq :
  forall (pcc : type FullECapWithTag) (pc : type Addr),
    Zmod.unsigned pc + 2 ^ Z.log2 (CompInstSz / 8) <= 2 ^ AddrSz ->
    specPreFaultTopExc (pccWithAddr pcc pc) = topExcAt pcc pc true.
Proof.
  intros pcc pc Hb; unfold specPreFaultTopExc, topExcAt, pccTopOf; cbv zeta.
  rewrite pccWithAddr_addr, pccWithAddr_ecap.
  change (evalExpr (ITE (Var type Bool true) ?a ?b)) with (evalExpr a).
  rewrite memFetchTopExc_eval, ugt_eval, !AdderAccessEnd_unsigned.
  rewrite to_Z_const.
  destruct invariant_fetch as [_ [_ [HC _]]].
  rewrite (Z.mod_small (Z.log2 (CompInstSz / 8))) by (rewrite HC; cbv; split; congruence).
  destruct (Z.ltb_spec (2 ^ AddrSz) (Zmod.unsigned pc + 2 ^ Z.log2 (CompInstSz / 8))); [lia | rewrite orb_false_r; reflexivity].
Qed.

Lemma topExcAt_false_bound :
  forall (pcc : type FullECapWithTag) (pc : type Addr) c,
    topExcAt pcc pc c = false ->
    Zmod.unsigned pc + 2 ^ Z.log2 (if c then CompInstSz / 8 else InstSz / 8) <= 2 ^ AddrSz /\
    Zmod.unsigned pc + 2 ^ Z.log2 (if c then CompInstSz / 8 else InstSz / 8) <= Zmod.unsigned (pccTopOf pcc).
Proof.
  intros pcc pc c H; unfold topExcAt in H; cbv zeta in H.
  rewrite memFetchTopExc_eval, AdderAccessEnd_unsigned in H.
  destruct invariant_fetch as [_ [_ [HC [HI _]]]].
  assert (Hlg : Zmod.unsigned (evalExpr (ITE (Var type Bool c)
                  ($(Z.log2 (CompInstSz / 8)) : Expr type (Bit LgLgNumBytesFullCapSz)) $(Z.log2 (InstSz / 8)))) =
                Z.log2 (if c then CompInstSz / 8 else InstSz / 8)).
  { destruct c; cbn [evalExpr]; rewrite Zmod.unsigned_of_Z; apply Z.mod_small; rewrite ?HI, HC; cbv; split; congruence. }
  rewrite Hlg in H; apply orb_false_iff in H; destruct H as [H1 H2].
  apply Z.ltb_ge in H1, H2; lia.
Qed.

(* The next line of an address in the last parcel of its line, when it does not wrap *)
Lemma nextLine_last :
  forall fp : type Addr,
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 -> Zmod.unsigned fp + 2 < 2 ^ AddrSz ->
    Zmod.unsigned (evalExpr (memNextLineAddr (Var type Addr fp))) = Zmod.unsigned fp + 2.
Proof.
  intros fp Ho Hb; rewrite nextLine_unsigned, lineAddr_div.
  pose proof lineBytes_pos as Hlb; pose proof addrBytes_pos as Hab.
  assert (Hfp : 0 <= Zmod.unsigned fp < 2 ^ AddrSz) by exact (bits.unsigned_range fp ltac:(cbv; congruence)).
  pose proof (Z.div_mod (Zmod.unsigned fp) (2 ^ LgLineBytes) ltac:(lia)) as E; rewrite Ho in E.
  rewrite Z.mod_small by lia; lia.
Qed.

(* --- 12. The pre-fault flags above the frontier --- *)

Definition pccBase (pcc : type FullECapWithTag) : type (Bit (AddrSz + 1)) :=
  evalExpr ((Var type ECap (evalExpr ((Var type FullECapWithTag pcc)`"ecap")))`"base").

Lemma preExcAt_bounds :
  forall (pcc : type FullECapWithTag) (pc : type Addr),
    (preExcAt pcc pc).(Snd).(Snd).(Snd).(Fst) = Z.ltb (Zmod.unsigned pc) (Zmod.unsigned (pccBase pcc)).
Proof.
  intros pcc pc; unfold preExcAt, pccBase; cbn [Fst Snd]; cbv zeta.
  match goal with |- evalExpr (Ult ?a ?b) = _ => change (evalExpr (Ult a b)) with (Z.ltb (Zmod.to_Z (evalExpr a)) (Zmod.to_Z (evalExpr b))) end.
  unfold ZeroExtendTo; rewrite to_Z_ZeroExtend by (cbv; congruence); reflexivity.
Qed.

Lemma preExcAt_above :
  forall (pcc : type FullECapWithTag) (fp a : type Addr),
    excAny (preExcAt pcc fp) = false -> Zmod.unsigned fp <= Zmod.unsigned a ->
    preExcAt pcc a = preExcAt pcc fp.
Proof.
  intros pcc fp a Hx Hle.
  pose proof (preExcAt_bounds pcc fp) as Bf; pose proof (preExcAt_bounds pcc a) as Ba.
  unfold excAny in Hx; rewrite Bf in Hx.
  apply orb_false_iff in Hx as [_ Hx]; apply orb_false_iff in Hx as [_ Hx]; apply orb_false_iff in Hx as [_ Hx].
  apply Z.ltb_ge in Hx.
  unfold preExcAt in Ba, Bf |- *; cbn [Fst Snd] in Ba, Bf; cbv zeta in Ba, Bf |- *.
  rewrite Ba, Bf.
  destruct (Z.ltb_spec (Zmod.unsigned a) (Zmod.unsigned (pccBase pcc))); [lia |].
  destruct (Z.ltb_spec (Zmod.unsigned fp) (Zmod.unsigned (pccBase pcc))); [lia | reflexivity].
Qed.

(* --- 13. Crossing and the wrapped last word --- *)

Lemma and2nvE_eval : forall (a : bool) (e : Expr type Bool),
  evalExpr (And [Not (Var type Bool a); e]) = andb (negb a) (evalExpr e).
Proof. intros a e; cbn [evalExpr map fold_left]; destruct a, (evalExpr e); reflexivity. Qed.

(* The size of an instruction, as `specMemFetchRead` writes it *)
Definition instSzE : Expr type (Bit LgLgNumBytesFullCapSz) := $LgNumBytesInstSz.

Lemma instSzE_unsigned : Zmod.unsigned (evalExpr instSzE) = LgNumBytesInstSz.
Proof.
  destruct invariant_fetch as [_ [_ [_ [_ [_ [H6 [H7 _]]]]]]].
  pose proof LgNumBytesFullCapSz_lt_sizes as Hs.
  unfold instSzE; rewrite to_Z_const; apply Z.mod_small; lia.
Qed.

Lemma specCrosses_eval :
  forall (pc : type Addr) (raw0 : type Inst),
    specCrosses pc raw0 =
    andb (negb (evalExpr (@isCompressed type raw0))) (evalExpr (memCrossesLine (Var type Addr pc) instSzE)).
Proof. intros pc raw0; unfold specCrosses; apply and2nvE_eval. Qed.

(* `crossesB_false`/`crossesB_true` for a size given as an expression *)
Lemma memCrossesLine_false_e : forall (a : type Addr) (se : Expr type (Bit LgLgNumBytesFullCapSz)),
  Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se) <= 2 ^ LgLineBytes ->
  evalExpr (memCrossesLine (Var type Addr a) se) = false.
Proof.
  intros a se H.
  pose proof (size_pow_bound (Zmod.to_Z (evalExpr se)) (Zmod.unsigned_pos_bound (evalExpr se) ltac:(reflexivity))) as Hp.
  pose proof capBytes_le_lineBytes as Hcl.
  pose proof lineBytes_pos as Hlb.
  pose proof (Z.mod_pos_bound (Zmod.to_Z a) (2 ^ LgLineBytes) Hlb) as Hlo.
  unfold memCrossesLine, memLineOffset.
  match goal with |- evalExpr (FromBit Bool ?e) = false =>
    change (Zmod.eqb (evalExpr e) Zmod.one = false) end.
  unfold Zmod.eqb.
  match goal with |- context [evalExpr (TruncMsb 1 LgLineBytes ?x)] =>
    change (evalExpr (TruncMsb 1 LgLineBytes x)) with (Zmod_lastn 1 (evalExpr x)) end.
  rewrite to_Z_lastn' by (cbv; congruence).
  rewrite to_Z_Sub by (cbv; congruence).
  rewrite to_Z_Add2, to_Z_Sll.
  rewrite !to_Z_ZeroExtend by (cbv; congruence).
  rewrite to_Z_TruncLsb, !to_Z_Var, !to_Z_const.
  change (Zmod.to_Z (@Zmod.one (2 ^ 1))) with 1.
  rewrite lineBytes_succ.
  rewrite (Z.mod_small 1) by lia.
  rewrite Z.shiftl_1_l.
  rewrite (Z.mod_small (2 ^ Zmod.to_Z (evalExpr se))) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se))) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se) - 1)) by lia.
  rewrite Z.div_small by lia.
  reflexivity.
Qed.

Lemma memCrossesLine_true_e : forall (a : type Addr) (se : Expr type (Bit LgLgNumBytesFullCapSz)),
  2 ^ LgLineBytes < Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se) ->
  evalExpr (memCrossesLine (Var type Addr a) se) = true.
Proof.
  intros a se H.
  pose proof (size_pow_bound (Zmod.to_Z (evalExpr se)) (Zmod.unsigned_pos_bound (evalExpr se) ltac:(reflexivity))) as Hp.
  pose proof capBytes_le_lineBytes as Hcl.
  pose proof lineBytes_pos as Hlb.
  pose proof (Z.mod_pos_bound (Zmod.to_Z a) (2 ^ LgLineBytes) Hlb) as Hlo.
  unfold memCrossesLine, memLineOffset.
  match goal with |- evalExpr (FromBit Bool ?e) = true =>
    change (Zmod.eqb (evalExpr e) Zmod.one = true) end.
  unfold Zmod.eqb.
  match goal with |- context [evalExpr (TruncMsb 1 LgLineBytes ?x)] =>
    change (evalExpr (TruncMsb 1 LgLineBytes x)) with (Zmod_lastn 1 (evalExpr x)) end.
  rewrite to_Z_lastn' by (cbv; congruence).
  rewrite to_Z_Sub by (cbv; congruence).
  rewrite to_Z_Add2, to_Z_Sll.
  rewrite !to_Z_ZeroExtend by (cbv; congruence).
  rewrite to_Z_TruncLsb, !to_Z_Var, !to_Z_const.
  change (Zmod.to_Z (@Zmod.one (2 ^ 1))) with 1.
  rewrite lineBytes_succ.
  rewrite (Z.mod_small 1) by lia.
  rewrite Z.shiftl_1_l.
  rewrite (Z.mod_small (2 ^ Zmod.to_Z (evalExpr se))) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se))) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se) - 1)) by lia.
  replace ((Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se) - 1) / 2 ^ LgLineBytes) with 1
    by (apply Z.div_unique_pos with (r := Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z (evalExpr se) - 1 - 2 ^ LgLineBytes); lia).
  reflexivity.
Qed.

Lemma specCross_last :
  forall fp : type Addr, Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 ->
    evalExpr (memCrossesLine (Var type Addr fp) instSzE) = true.
Proof.
  intros fp Ho; apply memCrossesLine_true_e; rewrite instSzE_unsigned.
  destruct invariant_fetch as [_ [_ [HC [HI [H5 _]]]]].
  change (Zmod.to_Z fp) with (Zmod.unsigned fp); rewrite Ho, H5, HI, HC; cbv; congruence.
Qed.

Lemma specCross_inline :
  forall (fp : type Addr) (k : bits LgFetchParcels),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 * Zmod.unsigned k -> Zmod.unsigned k + 1 < 2 ^ LgFetchParcels ->
    evalExpr (memCrossesLine (Var type Addr fp) instSzE) = false.
Proof.
  intros fp k Ho Hk; apply memCrossesLine_false_e; rewrite instSzE_unsigned.
  destruct invariant_fetch as [_ [_ [HC [HI [H5 _]]]]].
  pose proof lineBytes_parcels as HL2.
  change (Zmod.to_Z fp) with (Zmod.unsigned fp); rewrite Ho, H5, HI, HC.
  change ((2 * 8 + 2 * 8) / 8) with 4; lia.
Qed.

(* The word at the last parcel of the line, read within that line: its upper parcel wraps to parcel 0 *)
Lemma specWord_lastWrap :
  forall (fp : type Addr) (rp : type LineReadRp),
    Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 ->
    specWord fp (specPkt fp rp) = implWord (pktParcel (fetchPktOf rp) Zmod.zero) (pktParcel (fetchPktOf rp) lastParcel).
Proof.
  intros fp rp Ho.
  destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
  pose proof lineBytes_parcels as HL2.
  pose proof lineBytes_pos as Hlp.
  pose proof (pow2_pos LgFetchParcels HF) as Hfp.
  pose proof instBytes_le_cap as Hc4; rewrite instBytes_eq in Hc4.
  assert (Hlen : length (specPkt fp rp).(Fst).(tupleElems) = Z.to_nat NumBytesFullCapSz)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  apply Zmod.unsigned_inj.
  rewrite implWord_unsigned, !pktParcel_fetchPkt, !rpParcel_bytesAt, lastParcel_unsigned, Zmod.unsigned_0.
  change (2 * Z.to_nat 0)%nat with 0%nat.
  rewrite specWord_digits; change (Z.to_nat (InstSz / 8)) with instBytes; rewrite instBytes_eq.
  set (L1 := lineBytesAt rp (2 * Z.to_nat (2 ^ LgFetchParcels - 1)) 2).
  set (L2 := lineBytesAt rp 0 2).
  assert (HLB : (0 + 2 <= LineBytes)%nat)
    by (rewrite lineBytes_nat; apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  assert (HlenL1 : length L1 = 2%nat).
  { unfold L1; apply length_lineBytesAt.
    rewrite lineBytes_nat; apply Nat2Z.inj_le.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id by lia; lia. }
  assert (EL : map Zmod.unsigned (firstn 4 (specPkt fp rp).(Fst).(tupleElems)) = (L1 ++ L2)%list).
  { apply nth_ext with (d := 0) (d' := 0).
    - rewrite length_map, firstn_length_le by lia.
      rewrite length_app, HlenL1; unfold L2; rewrite length_lineBytesAt by exact HLB; reflexivity.
    - intros j Hj; rewrite length_map, firstn_length_le in Hj by lia.
      rewrite map_unsigned_nth, nth_firstn; destruct (Nat.ltb_spec j 4); [| lia].
      rewrite specPkt_nth by lia; rewrite Ho.
      destruct (Nat.leb_spec 2 j).
      + rewrite app_nth2 by lia; rewrite HlenL1; unfold L2.
        rewrite lineBytesAt_nth by lia.
        replace ((2 ^ LgLineBytes - 2 + Z.of_nat j) mod 2 ^ LgLineBytes) with (Z.of_nat (j - 2))
          by (apply Z.mod_unique_pos with (q := 1); lia).
        rewrite Nat2Z.id; reflexivity.
      + rewrite app_nth1 by lia; unfold L1.
        rewrite lineBytesAt_nth by lia.
        rewrite Z.mod_small by lia.
        f_equal; f_equal.
        apply Nat2Z.inj; rewrite Z2Nat.id, Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id by lia; lia. }
  rewrite EL, (digits_app 8 L1 L2 ltac:(lia)), HlenL1.
  replace (2 ^ CompInstSz) with (2 ^ (8 * Z.of_nat 2)) by (rewrite HC; reflexivity).
  reflexivity.
Qed.

(* `isCompressed` reads the low two bits: those of the low parcel *)
Lemma isCompressed_lowParcel :
  forall (raw : type Inst) (low : type (Bit CompInstSz)),
    Zmod.unsigned raw mod 2 ^ CompInstSz = Zmod.unsigned low ->
    evalExpr (@isCompressed type raw) = evalExpr (@isParcelCompressed type low).
Proof.
  intros raw low H.
  rewrite df_isCompressed_eval, df_isParcelCompressed_eval.
  destruct invariant_fetch as [_ [_ [HC _]]].
  assert (E : @Zmod.firstn 2 32 raw = @Zmod.firstn 2 CompInstSz low).
  { apply Zmod.unsigned_inj; rewrite !bits.unsigned_firstn.
    rewrite <- H, (Z.mod_mod_divide (Zmod.unsigned raw) (2 ^ CompInstSz) (2 ^ 2)) by (exists (2 ^ (CompInstSz - 2)); rewrite HC; reflexivity).
    reflexivity. }
  rewrite E; reflexivity.
Qed.

(* --- 14. Small facts for the live-head branches of fetchAssemble --- *)

Lemma notE_eval : forall e : Expr type Bool, evalExpr (Not e) = negb (evalExpr e).
Proof. reflexivity. Qed.

Lemma and3E_eval : forall a b c : Expr type Bool,
  evalExpr (And [a; b; c]) = andb (andb (evalExpr a) (evalExpr b)) (evalExpr c).
Proof. intros a b c; cbn [evalExpr map fold_left]; destruct (evalExpr a), (evalExpr b), (evalExpr c); reflexivity. Qed.

Lemma eqb_invDefault_true : forall x : bits LgFetchParcels,
  Zmod.eqb x (InvDefault (Bit LgFetchParcels)) = true -> Zmod.unsigned x = 2 ^ LgFetchParcels - 1.
Proof.
  intros x H; destruct invariant_fetch as [_ [_ [_ [_ [_ [_ [_ [HF _]]]]]]]].
  apply Zmod.eqb_eq in H; rewrite H, unsigned_invDefault by exact HF; rewrite Z.ones_equiv; lia.
Qed.

Lemma eqb_invDefault_false : forall x : bits LgFetchParcels,
  Zmod.eqb x (InvDefault (Bit LgFetchParcels)) = false -> Zmod.unsigned x <> 2 ^ LgFetchParcels - 1.
Proof.
  intros x H E; destruct invariant_fetch as [_ [_ [_ [_ [_ [_ [_ [HF _]]]]]]]].
  assert (E' : Zmod.unsigned x = Zmod.unsigned (InvDefault (Bit LgFetchParcels)))
    by (rewrite unsigned_invDefault by exact HF; rewrite Z.ones_equiv; lia).
  apply Zmod.unsigned_inj in E'; rewrite E', Zmod.eqb_refl in H; discriminate H.
Qed.

(* An aligned line start leaves room for its whole line *)
Lemma aligned_line_bound : forall A : type Addr,
  Zmod.unsigned A mod 2 ^ LgLineBytes = 0 -> Zmod.unsigned A + 2 ^ LgLineBytes <= 2 ^ AddrSz.
Proof.
  intros A HA.
  pose proof lineBytes_pos as Hlb; pose proof lineCount_pos as Hlc; pose proof addrBytes_lines as HAL.
  assert (Hr : 0 <= Zmod.unsigned A < 2 ^ AddrSz) by exact (bits.unsigned_range A ltac:(cbv; congruence)).
  pose proof (Z.div_mod (Zmod.unsigned A) (2 ^ LgLineBytes) ltac:(lia)) as E; rewrite HA, Z.add_0_r in E.
  assert (Hq : Zmod.unsigned A / 2 ^ LgLineBytes < 2 ^ (AddrSz - LgLineBytes))
    by (apply Z.div_lt_upper_bound; [lia | nia]).
  rewrite E, HAL; nia.
Qed.

(* The sequential PC after a 4-byte instruction in the last parcel of a line does not wrap *)
Lemma seq_no_wrap : forall fp : type Addr,
  Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 -> Zmod.unsigned fp + 4 <= 2 ^ AddrSz ->
  Zmod.unsigned fp + 4 < 2 ^ AddrSz.
Proof.
  intros fp Ho Hb.
  pose proof lineBytes_pos as Hlb; pose proof addrBytes_lines as HAL.
  pose proof lineBytes_parcels as HL2; pose proof parcels_ge2 as HF2.
  pose proof (Z.div_mod (Zmod.unsigned fp) (2 ^ LgLineBytes) ltac:(lia)) as E; rewrite Ho in E.
  destruct (Z.lt_trichotomy (Zmod.unsigned fp + 4) (2 ^ AddrSz)) as [Hlt | [Heq | Hgt]]; [exact Hlt | exfalso | lia].
  rewrite HAL in Heq.
  assert (Ht : 2 ^ LgLineBytes * (2 ^ (AddrSz - LgLineBytes) - Zmod.unsigned fp / 2 ^ LgLineBytes - 1) = 2) by nia.
  destruct (Z.le_gt_cases (2 ^ (AddrSz - LgLineBytes) - Zmod.unsigned fp / 2 ^ LgLineBytes - 1) 0) as [Ht0 | Ht1]; nia.
Qed.
