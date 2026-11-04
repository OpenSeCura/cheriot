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
From Cheriot Require Import SpecDefines SpecDevice.
From Cheriot.Proof Require Import RefConsts StateRel SimDevices RefRel RefFetch RefCoreRel RefRevTable RefBits RefSpecRead RefWriteRqPorts.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* Milestone 4, the snoop-miss lemma (byte level): a store line write that misses the revoker's
 * snoop leaves the capability slot at `scanFull sa` untouched. The write masks depend on the
 * address only through its line offset; they are written here as functions of the offset
 * (`dataMaskO`), equal to the spec's by `reflexivity`, and checked on all offsets by `vm_compute`.
 * All sizes are the named constants; arithmetic facts about them come from RefConsts.v. *)


Lemma tagMask_parts :
  forall isSecond (addr : Expr type Addr) memSize,
    evalLetExpr (memTagMask isSecond addr memSize) =
    evalLetExpr (tagMaskO type isSecond (TruncLsb TagAddrWidth LgNumBytesFullCapSz addr) (memTagSlot addr) memSize).
Proof. reflexivity. Qed.

Lemma tagMaskO_cong :
  forall isSecond (c1 c2 : Expr type (Bit LgNumBytesFullCapSz)) (t1 t2 : Expr type (Bit LgNumLineTags)) memSize,
    evalExpr c1 = evalExpr c2 -> evalExpr t1 = evalExpr t2 ->
    evalLetExpr (tagMaskO type isSecond c1 t1 memSize) = evalLetExpr (tagMaskO type isSecond c2 t2 memSize).
Proof.
  intros isSecond c1 c2 t1 t2 memSize Hc Ht.
  unfold tagMaskO, Sub; cbn [evalLetExpr].
  cbn [evalExpr map].
  rewrite Hc, Ht; reflexivity.
Qed.

Lemma dataMask_offset :
  forall isSecond (addr : Expr type Addr) memSize,
    evalLetExpr (memDataMask isSecond addr memSize) = evalLetExpr (dataMaskO type isSecond (memLineOffset addr) memSize).
Proof. reflexivity. Qed.

Lemma dataMaskO_cong :
  forall isSecond (off1 off2 : Expr type (Bit LgLineBytes)) memSize,
    evalExpr off1 = evalExpr off2 ->
    evalLetExpr (dataMaskO type isSecond off1 memSize) = evalLetExpr (dataMaskO type isSecond off2 memSize).
Proof.
  intros isSecond off1 off2 memSize H.
  unfold dataMaskO, rotateLeft, Sub; cbn [evalLetExpr].
  cbn [evalExpr map].
  rewrite H; reflexivity.
Qed.

(* --- Elements of a masked update --- *)

Lemma nth_updList_other :
  forall {A : Type} (v : A) (ls : list A) i j d, i <> j -> nth j (updList v ls i) d = nth j ls d.
Proof.
  intros A v ls; induction ls as [| x xs IH]; intros i j d Hne; [reflexivity |].
  destruct i as [| i'], j as [| j']; cbn [updList nth]; [contradiction | reflexivity | reflexivity |].
  apply IH; intros E; apply Hne; rewrite E; reflexivity.
Qed.

(* A masked update leaves index `j` alone when the mask bit for `j` is off *)
Lemma maskUpdateList_other :
  forall {A : Type} {n : nat} (masks : list bool) (upds : list A) idx (acc : SameTuple A n) j d,
    (forall i, (idx + i)%nat = j -> nth i masks false = false) ->
    nth j (maskUpdateList idx upds masks acc).(tupleElems) d = nth j acc.(tupleElems) d.
Proof.
  intros A n masks; induction masks as [| m ms IH]; intros upds idx acc j d H; [destruct upds; reflexivity |].
  destruct upds as [| u us]; [destruct m; reflexivity |].
  destruct m; cbn [maskUpdateList].
  - rewrite IH.
    + unfold updSameTupleNat; cbn [tupleElems].
      apply nth_updList_other; intros E.
      specialize (H 0%nat ltac:(rewrite Nat.add_0_r; exact E)); cbn [nth] in H; discriminate H.
    + intros i Ei; apply (H (S i)); rewrite <- Ei; lia.
  - apply IH; intros i Ei; apply (H (S i)); rewrite <- Ei; lia.
Qed.

(* --- The capability packet reads an 8-byte window and one tag --- *)

Section Window.
  Local Open Scope string_scope.

  Definition winByte (pc : type Addr) (rp : type LineReadRp) (j : nat) : type (Bit 8) :=
    evalExpr (ReadArray ((Var type LineReadRp rp)`"data")
                (Add [memLineOffset (Var type Addr pc); Const type (Bit LgLineBytes) (Zmod.of_Z _ (Z.of_nat j))])).
  Definition winTag (pc : type Addr) (rp : type LineReadRp) : bool :=
    evalExpr (ReadArray ((Var type LineReadRp rp)`"tag") (memTagSlot (Var type Addr pc))).

  Lemma specPkt_window :
    forall pc rp1 rp2,
      (forall j, (j < Z.to_nat (2 ^ LgNumBytesFullCapSz))%nat -> winByte pc rp1 j = winByte pc rp2 j) ->
      winTag pc rp1 = winTag pc rp2 ->
      specPkt pc rp1 = specPkt pc rp2.
  Proof.
    intros pc rp1 rp2 Hd Ht.
    unfold specPkt, memExtractCapPacket, slice, ArrayBuilder.
    cbn [evalLetExpr evalExpr mapDiffTuple fst snd].
    cbn [evalExpr Fst Snd].
    f_equal; [| f_equal; exact Ht].
    apply SameTuple_ext; cbn [mapSameTuple tupleElems].
    rewrite !map_map; apply map_ext_in; intros i _.
    pose proof (finLt i) as Hl; apply Is_true_eq_true, Nat.ltb_lt in Hl.
    exact (Hd _ Hl).
  Qed.

  Lemma nth_pf_nth :
    forall {A : Type} (ls : list A) i (pf : Is_true (i <? length ls)%nat) d, nth_pf pf = nth i ls d.
  Proof.
    intros A ls; induction ls as [| x xs IH]; intros i pf d.
    - exfalso; cbn in pf; exact pf.
    - destruct i as [| i']; cbn [nth_pf nth]; [reflexivity | apply IH].
  Qed.

  Lemma readNatToFinType_nth :
    forall {A : Type} {n : nat} (t : SameTuple A n) i d, (i < n)%nat ->
      readNatToFinType d (readSameTuple t) i = nth i t.(tupleElems) d.
  Proof.
    intros A n t i d Hi; unfold readNatToFinType.
    generalize (@eq_refl bool (i <? n)%nat).
    generalize (i <? n)%nat at 2 3 as b; intros b Eb.
    destruct b.
    - unfold readSameTuple; cbn [finNum]; apply nth_pf_nth.
    - exfalso; apply Nat.ltb_ge in Eb; lia.
  Qed.

  (* The line index of window byte `j` *)
  Definition winIdx (pc : type Addr) (j : nat) : nat :=
    Z.to_nat (Zmod.to_Z (evalExpr (Add [memLineOffset (Var type Addr pc);
                                         Const type (Bit LgLineBytes) (Zmod.of_Z _ (Z.of_nat j))]))).

  Lemma winByte_eq :
    forall pc (rp : type LineReadRp) j,
      winByte pc rp j = readNatToFinType (getDefault (Bit 8)) (readSameTuple rp.(Fst)) (winIdx pc j).
  Proof. reflexivity. Qed.

  Lemma winIdx_lt : forall pc j, (winIdx pc j < LineBytes)%nat.
  Proof.
    intros pc j; unfold winIdx.
    match goal with |- (Z.to_nat (@Zmod.to_Z ?m ?x) < _)%nat =>
      assert (Hr : 0 <= @Zmod.to_Z m x < 2 ^ LgLineBytes) by exact (Zmod.unsigned_pos_bound x lineBytes_pos) end.
    rewrite lineBytes_nat; apply Z2Nat.inj_lt; lia.
  Qed.

  (* A line write whose data mask is off at the window byte's index leaves the byte *)
  Lemma winByte_write :
    forall pc L (w : type LineWriteRq) rp j,
      nth (winIdx pc j) w.(Snd).(Snd).(Fst).(tupleElems) false = false ->
      winByte pc (applyLineWriteRq L w rp) j = winByte pc rp j.
  Proof.
    intros pc L w rp j Hm.
    rewrite !winByte_eq.
    unfold applyLineWriteRq; cbv zeta.
    destruct (Zmod.eqb w.(Fst) L); [| reflexivity].
    cbn [Fst Snd].
    rewrite !readNatToFinType_nth by apply winIdx_lt.
    unfold maskUpdateSameTuple.
    apply maskUpdateList_other; intros i Ei; cbn in Ei; subst i; exact Hm.
  Qed.

  Definition winTagIdx (pc : type Addr) : nat := Z.to_nat (Zmod.to_Z (evalExpr (memTagSlot (Var type Addr pc)))).

  Lemma winTag_eq :
    forall pc (rp : type LineReadRp),
      winTag pc rp = readNatToFinType (getDefault Bool) (readSameTuple rp.(Snd).(Fst)) (winTagIdx pc).
  Proof. reflexivity. Qed.

  Lemma winTagIdx_lt : forall pc, (winTagIdx pc < NumLineTags)%nat.
  Proof.
    intros pc; unfold winTagIdx.
    match goal with |- (Z.to_nat (@Zmod.to_Z ?m ?x) < _)%nat =>
      assert (Hr : 0 <= @Zmod.to_Z m x < 2 ^ LgNumLineTags) by exact (Zmod.unsigned_pos_bound x lineTags_pos) end.
    rewrite numLineTags_nat; apply Z2Nat.inj_lt; lia.
  Qed.

  Lemma winTag_write :
    forall pc L (w : type LineWriteRq) rp,
      nth (winTagIdx pc) w.(Snd).(Snd).(Snd).(Snd).(Fst).(tupleElems) false = false ->
      winTag pc (applyLineWriteRq L w rp) = winTag pc rp.
  Proof.
    intros pc L w rp Hm.
    rewrite !winTag_eq.
    unfold applyLineWriteRq; cbv zeta.
    destruct (Zmod.eqb w.(Fst) L); [| reflexivity].
    cbn [Fst Snd].
    rewrite !readNatToFinType_nth by apply winTagIdx_lt.
    unfold maskUpdateSameTuple.
    apply maskUpdateList_other; intros i Ei; cbn in Ei; subst i; exact Hm.
  Qed.
End Window.

(* --- The data mask of a line write (the checks are in RefConsts.v) --- *)

Lemma buildW_dataMask :
  forall b addr pkt size,
    (buildW b addr pkt size).(Snd).(Snd).(Fst) =
    evalLetExpr (dataMaskO type (Const type Bool b)
                   (Var type (Bit LgLineBytes) (evalExpr (memLineOffset (Var type Addr addr))))
                   (Var type (Bit LgLgNumBytesFullCapSz) size)).
Proof.
  intros b addr pkt size.
  transitivity (evalLetExpr (memDataMask (Const type Bool b) (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)));
    [reflexivity |].
  rewrite dataMask_offset; apply dataMaskO_cong; reflexivity.
Qed.

(* --- Indices of the slot at `scanFull sa` --- *)

(* Generic arithmetic (over variables: the constants are instantiated below) *)
Lemma slot_idx_gen : forall s j cb nt, 0 < cb -> 0 < nt -> 0 <= j < cb ->
  ((s * cb) mod (nt * cb) + j mod (nt * cb)) mod (nt * cb) = s mod nt * cb + j.
Proof.
  intros s j cb nt Hc Hn Hj.
  pose proof (Z.mod_pos_bound s nt Hn).
  rewrite Z.mul_mod_distr_r by lia.
  rewrite (Z.mod_small j) by nia.
  apply Z.mod_small; nia.
Qed.

Lemma winIdx_scanFull :
  forall sa j, (j < Z.to_nat (2 ^ LgNumBytesFullCapSz))%nat ->
    winIdx (scanFull sa) j = (Z.to_nat (2 ^ LgNumBytesFullCapSz) * Z.to_nat (Zmod.to_Z sa mod 2 ^ LgNumLineTags) + j)%nat.
Proof.
  intros sa j Hj; unfold winIdx.
  pose proof capBytes_pos as Hcb; pose proof lineTags_pos as Hnt.
  assert (Hj' : 0 <= Z.of_nat j < 2 ^ LgNumBytesFullCapSz)
    by (split; [lia | apply Nat2Z.inj_lt in Hj; rewrite Z2Nat.id in Hj by lia; exact Hj]).
  rewrite to_Z_Add2; unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var, to_Z_scanFull.
  cbn [evalExpr]; rewrite Zmod.unsigned_of_Z.
  assert (E : (Zmod.to_Z sa * 2 ^ LgNumBytesFullCapSz mod 2 ^ LgLineBytes + Z.of_nat j mod 2 ^ LgLineBytes) mod 2 ^ LgLineBytes
              = Zmod.to_Z sa mod 2 ^ LgNumLineTags * 2 ^ LgNumBytesFullCapSz + Z.of_nat j)
    by (rewrite lineBytes_split; apply slot_idx_gen; lia).
  rewrite E.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) (2 ^ LgNumLineTags) Hnt).
  apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id by nia; ring.
Qed.

Lemma winTagIdx_scanFull : forall sa, winTagIdx (scanFull sa) = Z.to_nat (Zmod.to_Z sa mod 2 ^ LgNumLineTags).
Proof.
  intros sa; unfold winTagIdx, memTagSlot.
  match goal with |- context [evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz ?x)] =>
    change (evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz x)) with (Zmod_lastn LgNumLineTags (evalExpr x)) end.
  rewrite to_Z_lastn by (cbv; congruence).
  unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var, to_Z_scanFull.
  f_equal.
  match goal with |- ?u / 2 ^ ?d = _ => change (u / 2 ^ d) with (u / 2 ^ LgNumBytesFullCapSz) end.
  pose proof capBytes_pos; pose proof lineTags_pos.
  rewrite lineBytes_split, Z.mul_mod_distr_r by lia.
  rewrite Z.div_mul by lia; reflexivity.
Qed.

(* The tag mask of a line write as `tmBits` at the address's offset *)
Lemma buildW_tagMask :
  forall b addr pkt size,
    let o := evalExpr (memLineOffset (Var type Addr addr)) in
    (buildW b addr pkt size).(Snd).(Snd).(Snd).(Snd).(Fst).(tupleElems) =
    tmBits b (Zmod.of_Z _ (Zmod.to_Z o mod 2 ^ LgNumBytesFullCapSz)) (Zmod.of_Z _ (Zmod.to_Z o / 2 ^ LgNumBytesFullCapSz)) size.
Proof.
  intros b addr pkt size o.
  unfold tmBits; apply (f_equal (fun t : SameTuple bool NumLineTags => t.(tupleElems))).
  transitivity (evalLetExpr (memTagMask (Const type Bool b) (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)));
    [reflexivity |].
  rewrite tagMask_parts; apply tagMaskO_cong.
  - apply Zmod.unsigned_inj.
    rewrite to_Z_TruncLsb, to_Z_Var; cbn [evalExpr]; rewrite Zmod.unsigned_of_Z.
    subst o; unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var.
    pose proof capBytes_pos.
    rewrite Z.mod_mod by lia.
    symmetry; apply Z.mod_mod_divide; exists (2 ^ LgNumLineTags); exact lineBytes_split.
  - apply Zmod.unsigned_inj.
    unfold memTagSlot.
    match goal with |- context [evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz ?x)] =>
      change (evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz x)) with (Zmod_lastn LgNumLineTags (evalExpr x)) end.
    rewrite to_Z_lastn by (cbv; congruence).
    cbn [evalExpr]; rewrite Zmod.unsigned_of_Z.
    subst o; unfold memLineOffset; rewrite !to_Z_TruncLsb, !to_Z_Var.
    match goal with |- ?u / 2 ^ ?d = _ => change (u / 2 ^ d) with (u / 2 ^ LgNumBytesFullCapSz) end.
    pose proof lineBytes_pos; pose proof capBytes_pos; pose proof lineTags_pos; pose proof lineBytes_split.
    match goal with |- ?u mod 2 ^ LgLineBytes / _ = _ => pose proof (Z.mod_pos_bound u (2 ^ LgLineBytes) ltac:(lia)) end.
    symmetry; apply Z.mod_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia].
Qed.

(* --- The conditions in Z --- *)

Lemma to_Z_lineOf_false : forall x, Zmod.to_Z (lineOf false x) = Zmod.to_Z x / 2 ^ LgLineBytes * 2 ^ LgLineBytes.
Proof.
  intros x; unfold lineOf, memLineAddr; cbn [evalExpr].
  etransitivity; [apply bits.unsigned_app; cbv; congruence |].
  rewrite bits.unsigned_app by (cbv; congruence).
  rewrite !Zmod.unsigned_0, !Z.shiftl_0_l, !Z.lor_0_l.
  rewrite Z.shiftl_mul_pow2 by (cbv; congruence).
  unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by (cbv; congruence).
  match goal with |- (?u / 2 ^ ?d) mod 2 ^ ?e * 2 ^ ?f = _ =>
    change ((u / 2 ^ d) mod 2 ^ e * 2 ^ f)
      with ((u / 2 ^ LgLineBytes) mod 2 ^ (AddrSz - LgLineBytes) * 2 ^ LgLineBytes) end.
  rewrite Z.mod_small; [reflexivity |].
  match goal with |- context [@Zmod.unsigned ?m x] =>
    assert (Hx : 0 <= @Zmod.unsigned m x < 2 ^ AddrSz) by exact (Zmod.unsigned_pos_bound x addrBytes_pos) end.
  pose proof lineBytes_pos; pose proof addrBytes_lines as E.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | rewrite Z.mul_comm, <- E; lia]].
Qed.

(* A crossing access runs past its line's end *)
Lemma crossesB_true : forall (a : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)),
  crossesB a sz = true -> 2 ^ LgLineBytes < Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz.
Proof.
  intros a sz H; apply Z.nle_gt; intros Hle.
  rewrite crossesB_false in H; [discriminate H | exact Hle].
Qed.

(* The store's slot, in Z *)
Lemma to_Z_slotOf : forall addr : type Addr,
  Zmod.to_Z (Zmod_lastn TagAddrWidth addr) = Zmod.to_Z addr / 2 ^ LgNumBytesFullCapSz.
Proof.
  intros addr; rewrite to_Z_lastn by (cbv; congruence).
  match goal with |- ?u / 2 ^ ?d = _ => change (u / 2 ^ d) with (u / 2 ^ LgNumBytesFullCapSz) end.
  reflexivity.
Qed.

Lemma isEq_bits_false : forall n (a b : bits n), isEq (k:=Bit n) a b = false -> Zmod.to_Z a <> Zmod.to_Z b.
Proof.
  intros n a b H E; apply Zmod.unsigned_inj in E; subst b.
  change (Zmod.eqb a a = false) in H; rewrite Zmod.eqb_refl in H; discriminate H.
Qed.

(* Facts over abstract expressions, applied to the expressions of `snoopHitsB` by unification (a
 * conversion of the evaluated expression would be slow in the kernel) *)
Lemma evalExpr_Or2_false : forall a b : Expr type Bool,
  evalExpr (Or [a; b]) = false -> evalExpr a = false /\ evalExpr b = false.
Proof.
  intros a b H; cbn [evalExpr map fold_left] in H.
  revert H; destruct (evalExpr a), (evalExpr b); cbn; intros H; first [split; reflexivity | discriminate H].
Qed.

Lemma evalExpr_And2_false : forall a b : Expr type Bool,
  evalExpr (And [a; b]) = false -> evalExpr a = true -> evalExpr b = false.
Proof.
  intros a b H Ha; cbn [evalExpr map fold_left] in H; rewrite Ha in H.
  revert H; destruct (evalExpr b); cbn; intros H; [discriminate H | reflexivity].
Qed.

Lemma evalExpr_Eq_false : forall n (a b : Expr type (Bit n)),
  evalExpr (Eq a b) = false -> Zmod.to_Z (evalExpr a) <> Zmod.to_Z (evalExpr b).
Proof.
  intros n a b H E; apply Zmod.unsigned_inj in E.
  cbn [evalExpr] in H; rewrite E in H; change (Zmod.eqb (evalExpr b) (evalExpr b) = false) in H.
  rewrite Zmod.eqb_refl in H; discriminate H.
Qed.

Lemma snoopMiss_Z :
  forall (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) sa,
    snoopHitsB addr size sa = false ->
    Zmod.to_Z addr / 2 ^ LgNumBytesFullCapSz <> Zmod.to_Z sa /\
    (2 ^ LgNumBytesFullCapSz <= Zmod.to_Z addr mod 2 ^ LgNumBytesFullCapSz + 2 ^ Zmod.to_Z size - 1 ->
     (Zmod.to_Z addr / 2 ^ LgNumBytesFullCapSz + 1) mod 2 ^ TagAddrWidth <> Zmod.to_Z sa).
Proof.
  intros addr size sa H.
  unfold snoopHitsB in H; cbv zeta in H.
  apply evalExpr_Or2_false in H as [H1 H2].
  apply evalExpr_Eq_false in H1; rewrite !to_Z_Var in H1.
  assert (Hsz : 0 <= Zmod.to_Z size < 2 ^ LgLgNumBytesFullCapSz)
    by exact (Zmod.unsigned_pos_bound size (pow2_pos _ LgLgNumBytesFullCapSz_nonneg)).
  pose proof (size_pow_bound _ Hsz) as Hp.
  pose proof capBytes_pos as Hcb.
  split.
  - change (evalExpr (TruncMsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr addr)))
      with (Zmod_lastn TagAddrWidth addr) in H1.
    rewrite to_Z_slotOf in H1; exact H1.
  - intros Hc.
    refine (_ (evalExpr_And2_false _ _ H2 _)).
    + intros H3; apply evalExpr_Eq_false in H3; rewrite !to_Z_Var, to_Z_Add2, to_Z_Var in H3.
      change (evalExpr (TruncMsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr addr)))
        with (Zmod_lastn TagAddrWidth addr) in H3.
      rewrite to_Z_slotOf in H3.
      cbn [evalExpr] in H3; rewrite Zmod.unsigned_of_Z in H3.
      rewrite (Z.mod_small 1 (2 ^ TagAddrWidth)) in H3 by (pose proof slotCount_gt1; lia).
      exact H3.
    + match goal with |- evalExpr (Var _ _ (evalExpr (FromBit Bool ?e))) = true =>
        change (Zmod.eqb (evalExpr e) Zmod.one = true) end.
      apply Zmod.eqb_eq, Zmod.unsigned_inj.
      match goal with |- context [evalExpr (TruncMsb 1 LgNumBytesFullCapSz ?x)] =>
        change (evalExpr (TruncMsb 1 LgNumBytesFullCapSz x)) with (Zmod_lastn 1 (evalExpr x)) end.
      rewrite to_Z_lastn by (cbv; congruence).
      rewrite to_Z_Sub by (cbv; congruence).
      rewrite to_Z_Var, to_Z_Add2.
      rewrite to_Z_ZeroExtend by (cbv; congruence).
      rewrite !to_Z_Var, to_Z_TruncLsb, to_Z_Var, to_Z_Sll.
      rewrite to_Z_ZeroExtend by (cbv; congruence).
      rewrite to_Z_Var.
      repeat match goal with |- context [Zmod.unsigned (evalExpr ?e)] => change (Zmod.unsigned (evalExpr e)) with 1 end.
      match goal with |- _ = Zmod.unsigned ?o => change (Zmod.unsigned o) with 1 end.
      match goal with |- context [@Zmod.unsigned ?m addr] => change (@Zmod.unsigned m addr) with (Zmod.to_Z addr) end.
      match goal with |- context [@Zmod.unsigned ?m size] => change (@Zmod.unsigned m size) with (Zmod.to_Z size) end.
      match goal with |- ?u / 2 ^ ?d = _ => change (u / 2 ^ d) with (u / 2 ^ LgNumBytesFullCapSz) end.
      rewrite Z.shiftl_1_l, capBytes_succ.
      pose proof (Z.mod_pos_bound (Zmod.to_Z addr) (2 ^ LgNumBytesFullCapSz) Hcb) as Hr.
      rewrite (Z.mod_small (2 ^ Zmod.to_Z size)) by lia.
      rewrite (Z.mod_small (Zmod.to_Z addr mod 2 ^ LgNumBytesFullCapSz + 2 ^ Zmod.to_Z size)) by lia.
      rewrite (Z.mod_small (Zmod.to_Z addr mod 2 ^ LgNumBytesFullCapSz + 2 ^ Zmod.to_Z size - 1)) by lia.
      symmetry; apply (Z.div_unique _ _ _ (Zmod.to_Z addr mod 2 ^ LgNumBytesFullCapSz + 2 ^ Zmod.to_Z size - 1 -
                                 2 ^ LgNumBytesFullCapSz)); [left; lia | lia].
Qed.

Lemma to_Z_lineOf_true : forall x,
  Zmod.to_Z (lineOf true x) = (Zmod.to_Z x / 2 ^ LgLineBytes * 2 ^ LgLineBytes + 2 ^ LgLineBytes) mod 2 ^ AddrSz.
Proof.
  intros x; unfold lineOf, memNextLineAddr.
  rewrite to_Z_Add2.
  change (evalExpr (memLineAddr (Var type Addr x))) with (lineOf false x).
  rewrite to_Z_lineOf_false.
  reflexivity.
Qed.

Lemma to_Z_offset : forall addr : type Addr,
  Zmod.to_Z (evalExpr (memLineOffset (Var type Addr addr))) = Zmod.to_Z addr mod 2 ^ LgLineBytes.
Proof. intros addr; unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var; reflexivity. Qed.

(* The second line of a crossing store holds slot 0 of the next line, the store's slot + 1. Over
 * variables: `lb` bytes per line, `cb` per capability slot, `nt` slots per line, `lc` lines, `M`
 * bytes and `N` slots in the address space *)
Lemma arith_second_gen : forall A S lb cb nt lc M N,
  0 < cb -> 0 < nt -> 0 < lc -> lb = nt * cb -> M = lc * lb -> N = lc * nt ->
  0 <= A < M -> 0 <= S < N -> S mod nt = 0 -> lb < A mod lb + cb ->
  (A / lb * lb + lb) mod M = S * cb / lb * lb -> (A / cb + 1) mod N = S.
Proof.
  intros A S lb cb nt lc M N Hcb Hnt Hlc Elb EM EN HA HS Hk Ho Hl.
  subst lb M N.
  assert (Hncb : 0 < nt * cb) by nia.
  assert (Hq : 0 <= A / (nt * cb) < lc)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]).
  pose proof (Z.div_mod A (nt * cb) ltac:(lia)) as HAd.
  pose proof (Z.mod_pos_bound A (nt * cb) Hncb) as HAm.
  pose proof (Z.div_mod S nt ltac:(lia)) as HSd; rewrite Hk, Z.add_0_r in HSd.
  assert (HA8 : A / cb = nt * (A / (nt * cb)) + (nt - 1)).
  { rewrite HAd at 1.
    replace (nt * cb * (A / (nt * cb)) + A mod (nt * cb)) with (nt * (A / (nt * cb)) * cb + A mod (nt * cb)) by ring.
    rewrite Z.div_add_l by lia; f_equal.
    symmetry; apply (Z.div_unique _ _ _ (A mod (nt * cb) - (nt - 1) * cb)); [left; nia | ring]. }
  assert (HS8 : S * cb / (nt * cb) * (nt * cb) = S * cb).
  { rewrite HSd; replace (nt * (S / nt) * cb) with (S / nt * (nt * cb)) by ring.
    rewrite Z.div_mul by lia; reflexivity. }
  rewrite HS8 in Hl; rewrite HA8.
  destruct (Z.lt_ge_cases (A / (nt * cb) + 1) lc) as [Hlt | Hge].
  - rewrite Z.mod_small in Hl by nia.
    assert (Es : S / nt = A / (nt * cb) + 1).
    { apply (Z.mul_reg_r _ _ (nt * cb)); [lia |]. rewrite HSd in Hl; nia. }
    rewrite Z.mod_small by nia.
    rewrite HSd, Es; ring.
  - assert (Eq : A / (nt * cb) = lc - 1) by lia.
    rewrite Eq in Hl; rewrite Eq.
    replace ((lc - 1) * (nt * cb) + nt * cb) with (lc * (nt * cb)) in Hl by ring.
    rewrite Z.mod_same in Hl by lia.
    assert (ES : S = 0) by nia.
    replace (nt * (lc - 1) + (nt - 1) + 1) with (lc * nt) by ring.
    rewrite Z.mod_same by nia; lia.
Qed.

Lemma arith_second :
  forall A S, 0 <= A < 2 ^ AddrSz -> 0 <= S < 2 ^ TagAddrWidth -> S mod 2 ^ LgNumLineTags = 0 ->
    2 ^ LgLineBytes < A mod 2 ^ LgLineBytes + 2 ^ LgNumBytesFullCapSz ->
    (A / 2 ^ LgLineBytes * 2 ^ LgLineBytes + 2 ^ LgLineBytes) mod 2 ^ AddrSz =
      S * 2 ^ LgNumBytesFullCapSz / 2 ^ LgLineBytes * 2 ^ LgLineBytes ->
    (A / 2 ^ LgNumBytesFullCapSz + 1) mod 2 ^ TagAddrWidth = S.
Proof.
  intros A S.
  exact (arith_second_gen A S _ _ _ _ _ _ capBytes_pos lineTags_pos lineCount_pos
           lineBytes_split addrBytes_lines slotCount_lines).
Qed.

Lemma div_split_gen : forall A lb cb nt, 0 < cb -> 0 < nt -> lb = nt * cb -> 0 <= A ->
  A / cb = nt * (A / lb) + A mod lb / cb /\ A mod cb = A mod lb mod cb.
Proof.
  intros A lb cb nt Hc Hn E HA; subst lb.
  split.
  - rewrite (Z.div_mod A (nt * cb)) at 1 by nia.
    replace (nt * cb * (A / (nt * cb)) + A mod (nt * cb)) with (nt * (A / (nt * cb)) * cb + A mod (nt * cb)) by ring.
    rewrite Z.div_add_l by lia; reflexivity.
  - symmetry; apply Z.mod_mod_divide; exists nt; reflexivity.
Qed.

Lemma div8_split : forall A, 0 <= A ->
  A / 2 ^ LgNumBytesFullCapSz = 2 ^ LgNumLineTags * (A / 2 ^ LgLineBytes) + A mod 2 ^ LgLineBytes / 2 ^ LgNumBytesFullCapSz /\
  A mod 2 ^ LgNumBytesFullCapSz = A mod 2 ^ LgLineBytes mod 2 ^ LgNumBytesFullCapSz /\
  0 <= A mod 2 ^ LgLineBytes < 2 ^ LgLineBytes /\ 0 <= A mod 2 ^ LgNumBytesFullCapSz < 2 ^ LgNumBytesFullCapSz.
Proof.
  intros A HA.
  destruct (div_split_gen A _ _ _ capBytes_pos lineTags_pos lineBytes_split HA) as [E1 E2].
  pose proof (Z.mod_pos_bound A _ lineBytes_pos); pose proof (Z.mod_pos_bound A _ capBytes_pos).
  repeat split; first [exact E1 | exact E2 | lia].
Qed.

(* The slot condition from the line equality, the snoop miss and (second line) the crossing *)
Lemma dCond_of :
  forall b (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) sa,
    lineOf b addr = lineOf false (scanFull sa) ->
    snoopHitsB addr size sa = false ->
    (b = true -> crossesB addr size = true) ->
    dCond b (Zmod.to_Z (evalExpr (memLineOffset (Var type Addr addr)))) (Zmod.to_Z size)
      (Zmod.to_Z sa mod 2 ^ LgNumLineTags) = true.
Proof.
  intros b addr size sa Hl Hm Hcr.
  destruct (snoopMiss_Z addr size sa Hm) as [M1 M2].
  apply (f_equal (@Zmod.to_Z _)) in Hl.
  rewrite to_Z_lineOf_false, to_Z_scanFull in Hl.
  rewrite to_Z_offset.
  assert (HA : 0 <= Zmod.to_Z addr < 2 ^ AddrSz) by exact (Zmod.unsigned_pos_bound addr addrBytes_pos).
  assert (HS : 0 <= Zmod.to_Z sa < 2 ^ TagAddrWidth)
    by exact (Zmod.unsigned_pos_bound sa (pow2_pos _ (Z.lt_le_incl _ _ TagAddrWidth_pos))).
  assert (Hsz : 0 <= Zmod.to_Z size < 2 ^ LgLgNumBytesFullCapSz)
    by exact (Zmod.unsigned_pos_bound size (pow2_pos _ LgLgNumBytesFullCapSz_nonneg)).
  pose proof (size_pow_bound _ Hsz) as Hp.
  destruct (div8_split (Zmod.to_Z addr) ltac:(lia)) as [D1 [D2 [D3 D4]]].
  pose proof lineBytes_pos as Hlb; pose proof capBytes_pos as Hcb; pose proof lineTags_pos as Hnt.
  pose proof lineBytes_split as Esp.
  pose proof (Z.div_mod (Zmod.to_Z sa) (2 ^ LgNumLineTags) ltac:(lia)) as DS1.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) (2 ^ LgNumLineTags) Hnt) as DS2.
  assert (DS3 : Zmod.to_Z sa * 2 ^ LgNumBytesFullCapSz / 2 ^ LgLineBytes = Zmod.to_Z sa / 2 ^ LgNumLineTags)
    by (rewrite Esp; apply Z.div_mul_cancel_r; lia).
  destruct b.
  - pose proof (crossesB_true addr size (Hcr eq_refl)) as Hx.
    rewrite to_Z_lineOf_true in Hl.
    unfold dCond; apply orb_true_intro.
    destruct (Z.eqb_spec (Zmod.to_Z sa mod 2 ^ LgNumLineTags) 0) as [Hk | Hk]; [right | left; reflexivity].
    apply negb_true_iff, Z.ltb_ge; exfalso; apply M2.
    + assert (Hoc : Zmod.to_Z addr mod 2 ^ LgLineBytes mod 2 ^ LgNumBytesFullCapSz =
                    Zmod.to_Z addr mod 2 ^ LgLineBytes - (2 ^ LgNumLineTags - 1) * 2 ^ LgNumBytesFullCapSz)
        by (symmetry; apply (Z.mod_unique _ _ (2 ^ LgNumLineTags - 1));
            [left; rewrite Z.mul_sub_distr_r, <- Esp, Z.mul_1_l; lia | ring]).
      rewrite D2, Hoc, Z.mul_sub_distr_r, <- Esp, Z.mul_1_l; lia.
    + apply arith_second; [lia | lia | exact Hk | lia | exact Hl].
  - rewrite (to_Z_lineOf_false addr), DS3 in Hl.
    assert (HlS : Zmod.to_Z addr / 2 ^ LgLineBytes = Zmod.to_Z sa / 2 ^ LgNumLineTags)
      by (apply (Z.mul_reg_r _ _ (2 ^ LgLineBytes)); lia).
    clear Hl; unfold dCond.
    apply andb_true_intro; split; apply negb_true_iff.
    + apply Z.eqb_neq; intros Ek; apply M1; rewrite D1, HlS, Ek; lia.
    + apply not_true_is_false; intros Hb; apply andb_true_iff in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1; apply Z.eqb_eq in Hb2.
      apply (M2 ltac:(rewrite D2; lia)).
      assert (Ex : Zmod.to_Z addr / 2 ^ LgNumBytesFullCapSz + 1 = Zmod.to_Z sa) by (rewrite D1, HlS; lia).
      rewrite Ex; apply Z.mod_small; lia.
Qed.

(* --- The slot at `scanFull sa` after a line write that misses the snoop --- *)

Lemma specPkt_write_miss :
  forall b (addr : type Addr) pkt (size : type (Bit LgLgNumBytesFullCapSz)) sa rp,
    lineOf b addr = lineOf false (scanFull sa) ->
    snoopHitsB addr size sa = false ->
    (b = true -> crossesB addr size = true) ->
    specPkt (scanFull sa) (applyLineWriteRq (lineOf false (scanFull sa)) (buildW b addr pkt size) rp) =
    specPkt (scanFull sa) rp.
Proof.
  intros b addr pkt size sa rp Hl Hm Hc.
  pose proof (dCond_of b addr size sa Hl Hm Hc) as Hd.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) _ lineTags_pos) as Hk.
  assert (Hk4 : (Z.to_nat (Zmod.to_Z sa mod 2 ^ LgNumLineTags) < NumLineTags)%nat)
    by (rewrite numLineTags_nat; apply Z2Nat.inj_lt; lia).
  rewrite <- (Z2Nat.id (Zmod.to_Z sa mod 2 ^ LgNumLineTags)) in Hd by lia.
  apply specPkt_window.
  - intros j Hj; apply winByte_write.
    rewrite winIdx_scanFull by exact Hj.
    rewrite buildW_dataMask.
    exact (dmBits_spec b _ size _ j Hk4 Hj Hd).
  - apply winTag_write.
    rewrite winTagIdx_scanFull.
    rewrite buildW_tagMask.
    exact (tmBits_spec b _ size _ Hk4 Hd).
Qed.

(* The snoop-miss lemma: a store line write that misses the revoker's snoop leaves the capability at
 * `scanFull sa` *)
Section MemVal.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).

  Lemma memValAt_write_miss :
    forall m b (addr : type Addr) pkt (size : type (Bit LgLgNumBytesFullCapSz)) sa,
      lineKind specRegions (lineOf b addr) = Some true -> lineUnique specRegions (lineOf b addr) ->
      snoopHitsB addr size sa = false -> (b = true -> crossesB addr size = true) ->
      memValAt pre post revBase revPfB revPfA initLine
        (specWriteLine specRegions (lineOf b addr) (buildW b addr pkt size) m) (scanFull sa) capSz =
      memValAt pre post revBase revPfB revPfA initLine m (scanFull sa) capSz.
  Proof.
    intros m b addr pkt size sa Hk Hu Hm Hc.
    unfold memValAt.
    rewrite (lineContent_specWrite initLine specRegions (lineOf b addr) (buildW b addr pkt size) m
               (lineOf false (scanFull sa)) (buildW_addr b addr pkt size) Hk Hu).
    destruct (Zmod.eqb (lineOf b addr) (lineOf false (scanFull sa))) eqn:E.
    - apply Zmod.eqb_eq in E.
      rewrite (specPkt_write_miss b addr pkt size sa _ E Hm Hc); reflexivity.
    - rewrite applyLineWriteRq_other; [reflexivity | rewrite buildW_addr; exact E].
  Qed.
End MemVal.
