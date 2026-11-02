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

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Cheriot Require Import SpecDefines ImplCommon.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* The memory geometry: address, line, capability-slot and access sizes.
 *
 * As in BoundsMonotonic.v, only the `invariant_*` theorems unfold the constants of SpecDefines.
 * Every other fact about these constants, here and in the files that import this one, is derived
 * from them, so a configuration change only has to re-establish these theorems, and the two mask
 * checks at the end of this file (`checkD_ok`, `checkT_ok`, through `dmBits_spec` and `tmBits_spec`),
 * which say that the spec's line-write masks leave untouched capability slots alone. They are stated
 * over the named constants and rerun by `vm_compute`; they do not follow from the invariants (they
 * depend on the mask expressions), so they are the other part of what a new configuration must
 * re-establish. *)

(* ========================================================================= *)
(* PRIMARY INVARIANTS                                                        *)
(* ========================================================================= *)

(* An address is a capability-slot index followed by a byte offset in the slot *)
Theorem invariant_TagAddrWidth : TagAddrWidth = AddrSz - LgNumBytesFullCapSz.
Proof. reflexivity. Qed.

(* A line holds 2^LgNumLineTags capability slots *)
Theorem invariant_LgNumLineTags : LgNumLineTags = LgLineBytes - LgNumBytesFullCapSz.
Proof. reflexivity. Qed.

Theorem invariant_LineBytes : Z.of_nat LineBytes = 2 ^ LgLineBytes.
Proof. reflexivity. Qed.

Theorem invariant_NumLineTags : Z.of_nat NumLineTags = 2 ^ LgNumLineTags.
Proof. reflexivity. Qed.

Theorem invariant_NumBytesFullCapSz : NumBytesFullCapSz = 2 ^ LgNumBytesFullCapSz.
Proof. reflexivity. Qed.

(* A capability slot fits in a line, a line in the address space *)
Theorem invariant_geometry : 0 <= LgNumBytesFullCapSz <= LgLineBytes /\ LgLineBytes < AddrSz.
Proof. unfold LgNumBytesFullCapSz, LgLineBytes, AddrSz; lia. Qed.

(* The size field of an access codes 2^0 .. 2^LgNumBytesFullCapSz bytes: no access is bigger than a
 * capability slot *)
Theorem invariant_sizes : 0 <= LgLgNumBytesFullCapSz /\ 2 ^ LgLgNumBytesFullCapSz = LgNumBytesFullCapSz + 1.
Proof. unfold LgLgNumBytesFullCapSz, LgNumBytesFullCapSz; split; [lia | reflexivity]. Qed.

(* Instruction fetch: a parcel is a compressed instruction (two bytes); a line holds
 * 2^LgFetchParcels parcels; an instruction is two parcels and fits in a capability packet. (The
 * instruction sizes are fixed by the ISA; the address size is not constrained here.) *)
Theorem invariant_fetch :
  Z.of_nat NumFetchParcels = 2 ^ LgFetchParcels /\ LgFetchParcels + 1 = LgLineBytes /\
  CompInstSz = 2 * 8 /\ InstSz = CompInstSz + CompInstSz /\
  2 ^ LgNumBytesInstSz = InstSz / 8 /\ LgNumBytesInstSz <= LgNumBytesFullCapSz /\ 0 <= LgNumBytesInstSz /\
  0 <= LgFetchParcels /\
  2 ^ LgNumBytesInstSz = 2 ^ (LgLineBytes - LgFetchParcels) + 2 ^ (LgLineBytes - LgFetchParcels).
Proof. vm_compute; repeat split; first [reflexivity | congruence]. Qed.

(* ========================================================================= *)
(* DERIVED FACTS (from the invariants only)                                  *)
(* ========================================================================= *)

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn; apply Z.pow_pos_nonneg; lia. Qed.

Lemma LgNumBytesFullCapSz_nonneg : 0 <= LgNumBytesFullCapSz.
Proof. pose proof invariant_geometry; lia. Qed.

Lemma LgLineBytes_nonneg : 0 <= LgLineBytes.
Proof. pose proof invariant_geometry; lia. Qed.

Lemma LgLineBytes_lt_AddrSz : LgLineBytes < AddrSz.
Proof. pose proof invariant_geometry; lia. Qed.

Lemma LgNumLineTags_nonneg : 0 <= LgNumLineTags.
Proof. rewrite invariant_LgNumLineTags; pose proof invariant_geometry; lia. Qed.

Lemma TagAddrWidth_pos : 0 < TagAddrWidth.
Proof. rewrite invariant_TagAddrWidth; pose proof invariant_geometry; lia. Qed.

Lemma LgLgNumBytesFullCapSz_nonneg : 0 <= LgLgNumBytesFullCapSz.
Proof. exact (proj1 invariant_sizes). Qed.

(* The size field is narrower than the slot offset *)
Lemma LgLgNumBytesFullCapSz_le : LgLgNumBytesFullCapSz <= LgNumBytesFullCapSz.
Proof.
  destruct invariant_sizes as [H0 H1].
  pose proof (Z.pow_gt_lin_r 2 LgLgNumBytesFullCapSz ltac:(lia) H0); lia.
Qed.

(* The code of a full capability fits in the size field *)
Lemma LgNumBytesFullCapSz_lt_sizes : LgNumBytesFullCapSz < 2 ^ LgLgNumBytesFullCapSz.
Proof. rewrite (proj2 invariant_sizes); lia. Qed.

Lemma capBytes_pos : 0 < 2 ^ LgNumBytesFullCapSz.
Proof. apply pow2_pos, LgNumBytesFullCapSz_nonneg. Qed.

Lemma lineBytes_pos : 0 < 2 ^ LgLineBytes.
Proof. apply pow2_pos, LgLineBytes_nonneg. Qed.

Lemma lineTags_pos : 0 < 2 ^ LgNumLineTags.
Proof. apply pow2_pos, LgNumLineTags_nonneg. Qed.

Lemma lineCount_pos : 0 < 2 ^ (AddrSz - LgLineBytes).
Proof. apply pow2_pos; pose proof LgLineBytes_lt_AddrSz; lia. Qed.

Lemma addrBytes_pos : 0 < 2 ^ AddrSz.
Proof. apply pow2_pos; pose proof LgLineBytes_lt_AddrSz; pose proof LgLineBytes_nonneg; lia. Qed.

Lemma slotCount_gt1 : 1 < 2 ^ TagAddrWidth.
Proof. apply Z.pow_gt_1; [lia | exact TagAddrWidth_pos]. Qed.

(* A line is 2^LgNumLineTags capability slots *)
Lemma lineBytes_split : 2 ^ LgLineBytes = 2 ^ LgNumLineTags * 2 ^ LgNumBytesFullCapSz.
Proof.
  pose proof LgNumLineTags_nonneg; pose proof LgNumBytesFullCapSz_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)); pose proof invariant_LgNumLineTags; lia.
Qed.

(* The address space is 2^TagAddrWidth capability slots *)
Lemma addrBytes_split : 2 ^ AddrSz = 2 ^ TagAddrWidth * 2 ^ LgNumBytesFullCapSz.
Proof.
  pose proof TagAddrWidth_pos; pose proof LgNumBytesFullCapSz_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)); pose proof invariant_TagAddrWidth; lia.
Qed.

(* The address space is 2^(AddrSz - LgLineBytes) lines *)
Lemma addrBytes_lines : 2 ^ AddrSz = 2 ^ (AddrSz - LgLineBytes) * 2 ^ LgLineBytes.
Proof.
  pose proof LgLineBytes_lt_AddrSz; pose proof LgLineBytes_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)); lia.
Qed.

(* ... of 2^LgNumLineTags capability slots each *)
Lemma slotCount_lines : 2 ^ TagAddrWidth = 2 ^ (AddrSz - LgLineBytes) * 2 ^ LgNumLineTags.
Proof.
  pose proof LgLineBytes_lt_AddrSz; pose proof LgNumLineTags_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)).
  pose proof invariant_TagAddrWidth; pose proof invariant_LgNumLineTags; lia.
Qed.

Lemma capBytes_le_lineBytes : 2 ^ LgNumBytesFullCapSz <= 2 ^ LgLineBytes.
Proof. pose proof invariant_geometry; apply Z.pow_le_mono_r; lia. Qed.

Lemma lineBytes_lt_addrBytes : 2 ^ LgLineBytes < 2 ^ AddrSz.
Proof. pose proof invariant_geometry; apply Z.pow_lt_mono_r; lia. Qed.

Lemma lineBytes_succ : 2 ^ (LgLineBytes + 1) = 2 * 2 ^ LgLineBytes.
Proof. rewrite Z.pow_add_r by (pose proof LgLineBytes_nonneg; lia); lia. Qed.

Lemma capBytes_succ : 2 ^ (LgNumBytesFullCapSz + 1) = 2 * 2 ^ LgNumBytesFullCapSz.
Proof. rewrite Z.pow_add_r by (pose proof LgNumBytesFullCapSz_nonneg; lia); lia. Qed.

(* An access of size code `sz` covers 1 .. 2^LgNumBytesFullCapSz bytes *)
Lemma size_pow_bound : forall sz, 0 <= sz < 2 ^ LgLgNumBytesFullCapSz -> 1 <= 2 ^ sz <= 2 ^ LgNumBytesFullCapSz.
Proof.
  intros sz Hs; rewrite (proj2 invariant_sizes) in Hs; split.
  - apply (Z.pow_le_mono_r 2 0 sz); lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

(* The line and slot counts as naturals *)
Lemma lineBytes_nat : LineBytes = Z.to_nat (2 ^ LgLineBytes).
Proof. rewrite <- invariant_LineBytes, Nat2Z.id; reflexivity. Qed.

Lemma numLineTags_nat : NumLineTags = Z.to_nat (2 ^ LgNumLineTags).
Proof. rewrite <- invariant_NumLineTags, Nat2Z.id; reflexivity. Qed.

(* ========================================================================= *)
(* LINE-WRITE MASK CHECKS (configuration dependent, by computation)          *)
(* ========================================================================= *)

(* The line-write masks with the line offset (data) and slot offset and slot (tags) as inputs; equal
 * to the spec's `memDataMask`/`memTagMask` by `reflexivity` (RefSnoopMiss.v `dataMask_offset`,
 * `tagMask_parts`) *)
Section MaskO.
  Variable ty : Kind -> Type.

  (* `memDataMask` with the line offset of the address as input *)
  Definition dataMaskO (isSecond : Expr ty Bool) (off : Expr ty (Bit LgLineBytes))
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : LetExpr ty (Array LineBytes Bool) :=
    LetE numBytesActive : Bit (LgLineBytes + 1)%Z <-
      Sll $1 (ZeroExtend (LgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
    LetE fullMask : Bit (kindSize (Array LineBytes Bool)) <-
      rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) off ;
    LetE add1Bits : Bit (kindSize (Array LineBytes Bool)) <-
      ToBit (FromBit (Array LineBytes Bool) (Not (Sll (ConstBit (InvDefault _)) off))) ;
    LetE lineSelMask : Bit (kindSize (Array LineBytes Bool)) <-
      ITE isSecond #add1Bits (Not #add1Bits) ;
    RetE (FromBit (Array LineBytes Bool) (And [ #fullMask ; #lineSelMask ])).

  (* `memTagMask` with the address's offset in its capability slot and its tag slot as inputs *)
  Definition tagMaskO (isSecond : Expr ty Bool) (capOff : Expr ty (Bit LgNumBytesFullCapSz))
    (slot : Expr ty (Bit LgNumLineTags)) (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : LetExpr ty (Array NumLineTags Bool) :=
    let wTagCnt := (LgNumLineTags + 2)%Z in
    let w := kindSize (Array NumLineTags Bool) in
    LetE capOffset : Bit LgNumBytesFullCapSz <- capOff ;
    LetE numBytesActiveTag : Bit (LgNumBytesFullCapSz + wTagCnt)%Z <-
      Sll $1 (ZeroExtend (LgNumBytesFullCapSz + wTagCnt - LgLgNumBytesFullCapSz)%Z memSize) ;
    LetE endByteOffset : Bit (LgNumBytesFullCapSz + wTagCnt)%Z <-
      Sub (Add [ ZeroExtend wTagCnt #capOffset ; #numBytesActiveTag ]) $1 ;
    LetE numTagsActive : Bit wTagCnt <-
      Add [ TruncMsb wTagCnt LgNumBytesFullCapSz #endByteOffset ; $1 ] ;
    LetE baseMask : Bit (w + w)%Z <-
      Not (Sll (ConstBit (InvDefault (Bit (w + w)%Z))) #numTagsActive) ;
    LetE shiftedMask : Bit (w + w)%Z <- Sll #baseMask slot ;
    LetE maskBits : Bit w <-
      ITE isSecond (TruncMsb w w #shiftedMask) (TruncLsb w w #shiftedMask) ;
    RetE (FromBit (Array NumLineTags Bool) #maskBits).
End MaskO.

Definition dmBits (b : bool) (o : bits LgLineBytes) (sz : bits LgLgNumBytesFullCapSz) : list bool :=
  (evalLetExpr (dataMaskO type (Const type Bool b) (Var type (Bit LgLineBytes) o)
                  (Var type (Bit LgLgNumBytesFullCapSz) sz))).(tupleElems).

(* When slot `k` of the line is untouched: first line (`b = false`): the store's slot
 * `o / 2^LgNumBytesFullCapSz` is not `k`, nor is the next slot when the store spills into it; second
 * line: `k` is not slot 0, or the store does not cross the line *)
Definition dCond (b : bool) (o sz k : Z) : bool :=
  if b then orb (negb (k =? 0)) (negb (2 ^ LgLineBytes <? o + 2 ^ sz))
  else andb (negb (o / 2 ^ LgNumBytesFullCapSz =? k))
            (negb (andb (2 ^ LgNumBytesFullCapSz <=? o mod 2 ^ LgNumBytesFullCapSz + 2 ^ sz - 1)
                        (o / 2 ^ LgNumBytesFullCapSz + 1 =? k))).

(* The checker, one named constant per level (so that each instantiation matches syntactically) *)
Definition checkK (b : bool) (oz szz : nat) (bits : list bool) (k : nat) : bool :=
  implb (dCond b (Z.of_nat oz) (Z.of_nat szz) (Z.of_nat k))
        (forallb (fun j => negb (nth (Z.to_nat (2 ^ LgNumBytesFullCapSz) * k + j) bits false))
           (seq 0 (Z.to_nat (2 ^ LgNumBytesFullCapSz)))).
Definition checkSz (b : bool) (oz szz : nat) : bool :=
  forallb (checkK b oz szz (dmBits b (Zmod.of_Z _ (Z.of_nat oz)) (Zmod.of_Z _ (Z.of_nat szz)))) (seq 0 NumLineTags).
Definition checkO (b : bool) (oz : nat) : bool :=
  forallb (checkSz b oz) (seq 0 (Z.to_nat (2 ^ LgLgNumBytesFullCapSz))).
Definition checkB (b : bool) : bool := forallb (checkO b) (seq 0 LineBytes).
(* Stated without a constant for the whole check: converting one with the concrete `forallb`
 * would make the kernel evaluate the check without the VM (8 s) *)
Lemma checkD_ok : forallb checkB [true; false] = true.
Proof. vm_compute; reflexivity. Qed.

Lemma in_seq_lt : forall n k, (k < n)%nat -> In k (seq 0 n).
Proof. intros n k H; apply in_seq; lia. Qed.

Lemma bits_of_to_nat : forall n (x : bits n), 0 <= n ->
  x = Zmod.of_Z _ (Z.of_nat (Z.to_nat (Zmod.to_Z x))) /\ (Z.to_nat (Zmod.to_Z x) < Z.to_nat (2 ^ n))%nat.
Proof.
  intros n x Hn.
  pose proof (Zmod.to_Z_range x) as Hr.
  split.
  - rewrite Z2Nat.id by lia; symmetry; apply Zmod.of_Z_to_Z.
  - apply Z2Nat.inj_lt; lia.
Qed.

Lemma forallb_in : forall {A : Type} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof. intros A f l x H Hx; exact (proj1 (forallb_forall f l) H x Hx). Qed.

Lemma dmBits_spec :
  forall b (o : bits LgLineBytes) (sz : bits LgLgNumBytesFullCapSz) k j,
    (k < NumLineTags)%nat -> (j < Z.to_nat (2 ^ LgNumBytesFullCapSz))%nat ->
    dCond b (Zmod.to_Z o) (Zmod.to_Z sz) (Z.of_nat k) = true ->
    nth (Z.to_nat (2 ^ LgNumBytesFullCapSz) * k + j) (dmBits b o sz) false = false.
Proof.
  intros b o sz k j Hk Hj Hc.
  destruct (bits_of_to_nat _ o ltac:(cbv; congruence)) as [Eo Ho]; rewrite <- lineBytes_nat in Ho.
  destruct (bits_of_to_nat _ sz ltac:(cbv; congruence)) as [Es Hs].
  pose proof (forallb_in checkB _ b checkD_ok ltac:(destruct b; cbn; auto)) as H1; unfold checkB in H1.
  pose proof (forallb_in (checkO b) _ _ H1 (in_seq_lt LineBytes _ Ho)) as H2; unfold checkO in H2; clear H1.
  pose proof (forallb_in (checkSz b _) _ _ H2 (in_seq_lt _ _ Hs)) as H3; unfold checkSz in H3; clear H2.
  pose proof (forallb_in (checkK b _ _ _) _ _ H3 (in_seq_lt NumLineTags k Hk)) as H4; unfold checkK in H4; clear H3.
  rewrite <- Eo, <- Es in H4.
  rewrite !Z2Nat.id in H4 by (match goal with |- 0 <= @Zmod.unsigned _ ?x => exact (proj1 (Zmod.unsigned_pos_bound x ltac:(apply pow2_pos; cbv; congruence))) end).
  rewrite Hc in H4; cbn [implb] in H4.
  pose proof (forallb_in _ _ _ H4 (in_seq_lt _ j Hj)) as H5; cbv beta in H5.
  apply negb_true_iff in H5; exact H5.
Qed.

(* --- The tag mask, checked on all offsets (the same slot condition `dCond`) --- *)

Definition tmBits (b : bool) (c : bits LgNumBytesFullCapSz) (t : bits LgNumLineTags) (sz : bits LgLgNumBytesFullCapSz)
  : list bool :=
  (evalLetExpr (tagMaskO type (Const type Bool b) (Var type (Bit LgNumBytesFullCapSz) c)
                  (Var type (Bit LgNumLineTags) t) (Var type (Bit LgLgNumBytesFullCapSz) sz))).(tupleElems).

Definition checkTK (b : bool) (oz szz : nat) (bits : list bool) (k : nat) : bool :=
  implb (dCond b (Z.of_nat oz) (Z.of_nat szz) (Z.of_nat k)) (negb (nth k bits false)).
Definition checkTSz (b : bool) (oz szz : nat) : bool :=
  forallb (checkTK b oz szz (tmBits b (Zmod.of_Z _ (Z.of_nat oz mod 2 ^ LgNumBytesFullCapSz))
                                     (Zmod.of_Z _ (Z.of_nat oz / 2 ^ LgNumBytesFullCapSz))
                                     (Zmod.of_Z _ (Z.of_nat szz)))) (seq 0 NumLineTags).
Definition checkTO (b : bool) (oz : nat) : bool :=
  forallb (checkTSz b oz) (seq 0 (Z.to_nat (2 ^ LgLgNumBytesFullCapSz))).
Definition checkTB (b : bool) : bool := forallb (checkTO b) (seq 0 LineBytes).

Lemma checkT_ok : forallb checkTB [true; false] = true.
Proof. vm_compute; reflexivity. Qed.

Lemma tmBits_spec :
  forall b (o : bits LgLineBytes) (sz : bits LgLgNumBytesFullCapSz) k,
    (k < NumLineTags)%nat ->
    dCond b (Zmod.to_Z o) (Zmod.to_Z sz) (Z.of_nat k) = true ->
    nth k (tmBits b (Zmod.of_Z _ (Zmod.to_Z o mod 2 ^ LgNumBytesFullCapSz))
                 (Zmod.of_Z _ (Zmod.to_Z o / 2 ^ LgNumBytesFullCapSz)) sz) false = false.
Proof.
  intros b o sz k Hk Hc.
  destruct (bits_of_to_nat _ o ltac:(cbv; congruence)) as [_ Ho]; rewrite <- lineBytes_nat in Ho.
  destruct (bits_of_to_nat _ sz ltac:(cbv; congruence)) as [Es Hs].
  pose proof (forallb_in checkTB _ b checkT_ok ltac:(destruct b; cbn; auto)) as H1; unfold checkTB in H1.
  pose proof (forallb_in (checkTO b) _ _ H1 (in_seq_lt LineBytes _ Ho)) as H2; unfold checkTO in H2; clear H1.
  pose proof (forallb_in (checkTSz b _) _ _ H2 (in_seq_lt _ _ Hs)) as H3; unfold checkTSz in H3; clear H2.
  pose proof (forallb_in (checkTK b _ _ _) _ _ H3 (in_seq_lt NumLineTags k Hk)) as H4; unfold checkTK in H4; clear H3.
  rewrite <- Es in H4.
  rewrite !Z2Nat.id in H4 by (match goal with |- 0 <= @Zmod.unsigned _ ?x => exact (proj1 (Zmod.unsigned_pos_bound x ltac:(apply pow2_pos; cbv; congruence))) end).
  rewrite Hc in H4; cbn [implb] in H4.
  apply negb_true_iff in H4; exact H4.
Qed.
