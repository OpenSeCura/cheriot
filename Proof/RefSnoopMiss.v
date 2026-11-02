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
From Cheriot.Proof Require Import StateRel SimDevices RefRel RefFetch RefCoreRel RefRevTable RefBits RefSpecRead RefWriteRqPorts.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* Milestone 4, the snoop-miss lemma (byte level): a store line write that misses the revoker's
 * snoop leaves the capability slot at `scanFull sa` untouched. The write masks depend on the
 * address only through its line offset; they are written here as functions of the offset
 * (`dataMaskO`), equal to the spec's by `reflexivity`, and checked on all offsets by `vm_compute`. *)

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

  (* `memTagMask` with the address's low 3 bits and its tag slot as inputs *)
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
      (forall j, (j < 8)%nat -> winByte pc rp1 j = winByte pc rp2 j) ->
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
      pose proof (Zmod.to_Z_range x) as Hr; assert (Em : m = 32) by reflexivity end.
    change LineBytes with (Z.to_nat 32); apply Z2Nat.inj_lt; lia.
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
      pose proof (Zmod.to_Z_range x) as Hr; assert (Em : m = 4) by reflexivity end.
    change NumLineTags with (Z.to_nat 4); apply Z2Nat.inj_lt; lia.
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

(* --- The data mask of a line write, checked on all offsets --- *)

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

Definition dmBits (b : bool) (o : bits LgLineBytes) (sz : bits LgLgNumBytesFullCapSz) : list bool :=
  (evalLetExpr (dataMaskO type (Const type Bool b) (Var type (Bit LgLineBytes) o)
                  (Var type (Bit LgLgNumBytesFullCapSz) sz))).(tupleElems).

(* When slot `k` of the line is untouched: first line (`b = false`): the store's slot `o / 8` is not
 * `k`, nor is the next slot when the store spills into it; second line: `k` is not slot 0, or the
 * store does not cross the line *)
Definition dCond (b : bool) (o sz k : Z) : bool :=
  if b then orb (negb (k =? 0)) (negb (32 <? o + 2 ^ sz))
  else andb (negb (o / 8 =? k)) (negb (andb (8 <=? o mod 8 + 2 ^ sz - 1) (o / 8 + 1 =? k))).

(* The checker, one named constant per level (so that each instantiation matches syntactically) *)
Definition checkK (b : bool) (oz szz : nat) (bits : list bool) (k : nat) : bool :=
  implb (dCond b (Z.of_nat oz) (Z.of_nat szz) (Z.of_nat k))
        (forallb (fun j => negb (nth (8 * k + j) bits false)) (seq 0 8)).
Definition checkSz (b : bool) (oz szz : nat) : bool :=
  forallb (checkK b oz szz (dmBits b (Zmod.of_Z _ (Z.of_nat oz)) (Zmod.of_Z _ (Z.of_nat szz)))) (seq 0 4).
Definition checkO (b : bool) (oz : nat) : bool := forallb (checkSz b oz) (seq 0 4).
Definition checkB (b : bool) : bool := forallb (checkO b) (seq 0 32).
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
    (k < 4)%nat -> (j < 8)%nat ->
    dCond b (Zmod.to_Z o) (Zmod.to_Z sz) (Z.of_nat k) = true ->
    nth (8 * k + j) (dmBits b o sz) false = false.
Proof.
  intros b o sz k j Hk Hj Hc.
  destruct (bits_of_to_nat _ o ltac:(cbv; congruence)) as [Eo Ho].
  destruct (bits_of_to_nat _ sz ltac:(cbv; congruence)) as [Es Hs].
  pose proof (forallb_in checkB _ b checkD_ok ltac:(destruct b; cbn; auto)) as H1; unfold checkB in H1.
  pose proof (forallb_in (checkO b) _ _ H1 (in_seq_lt 32 _ Ho)) as H2; unfold checkO in H2; clear H1.
  pose proof (forallb_in (checkSz b _) _ _ H2 (in_seq_lt 4 _ Hs)) as H3; unfold checkSz in H3; clear H2.
  pose proof (forallb_in (checkK b _ _ _) _ _ H3 (in_seq_lt 4 k Hk)) as H4; unfold checkK in H4; clear H3.
  rewrite <- Eo, <- Es in H4.
  rewrite !Z2Nat.id in H4 by (match goal with |- (0 <= ?u)%Z => match u with context [?x] => is_var x; pose proof (Zmod.to_Z_range x) end end; lia).
  rewrite Hc in H4; cbn [implb] in H4.
  pose proof (forallb_in _ _ _ H4 (in_seq_lt 8 j Hj)) as H5; cbv beta in H5.
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
  forallb (checkTK b oz szz (tmBits b (Zmod.of_Z _ (Z.of_nat oz mod 8)) (Zmod.of_Z _ (Z.of_nat oz / 8))
                                     (Zmod.of_Z _ (Z.of_nat szz)))) (seq 0 4).
Definition checkTO (b : bool) (oz : nat) : bool := forallb (checkTSz b oz) (seq 0 4).
Definition checkTB (b : bool) : bool := forallb (checkTO b) (seq 0 32).

Lemma checkT_ok : forallb checkTB [true; false] = true.
Proof. vm_compute; reflexivity. Qed.

Lemma tmBits_spec :
  forall b (o : bits LgLineBytes) (sz : bits LgLgNumBytesFullCapSz) k,
    (k < 4)%nat ->
    dCond b (Zmod.to_Z o) (Zmod.to_Z sz) (Z.of_nat k) = true ->
    nth k (tmBits b (Zmod.of_Z _ (Zmod.to_Z o mod 8)) (Zmod.of_Z _ (Zmod.to_Z o / 8)) sz) false = false.
Proof.
  intros b o sz k Hk Hc.
  destruct (bits_of_to_nat _ o ltac:(cbv; congruence)) as [_ Ho].
  destruct (bits_of_to_nat _ sz ltac:(cbv; congruence)) as [Es Hs].
  pose proof (forallb_in checkTB _ b checkT_ok ltac:(destruct b; cbn; auto)) as H1; unfold checkTB in H1.
  pose proof (forallb_in (checkTO b) _ _ H1 (in_seq_lt 32 _ Ho)) as H2; unfold checkTO in H2; clear H1.
  pose proof (forallb_in (checkTSz b _) _ _ H2 (in_seq_lt 4 _ Hs)) as H3; unfold checkTSz in H3; clear H2.
  pose proof (forallb_in (checkTK b _ _ _) _ _ H3 (in_seq_lt 4 k Hk)) as H4; unfold checkTK in H4; clear H3.
  rewrite <- Es in H4.
  rewrite !Z2Nat.id in H4 by (match goal with |- (0 <= ?u)%Z => match u with context [?x] => is_var x; pose proof (Zmod.to_Z_range x) end end; lia).
  rewrite Hc in H4; cbn [implb] in H4.
  apply negb_true_iff in H4; exact H4.
Qed.

(* --- Indices of the slot at `scanFull sa` --- *)

Lemma winIdx_scanFull :
  forall sa j, (j < 8)%nat -> winIdx (scanFull sa) j = (8 * Z.to_nat (Zmod.to_Z sa mod 4) + j)%nat.
Proof.
  intros sa j Hj; unfold winIdx.
  rewrite to_Z_Add2; unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var, to_Z_scanFull.
  cbn [evalExpr]; rewrite Zmod.unsigned_of_Z.
  pose proof (Zmod.to_Z_range sa) as Hs.
  change (2 ^ LgNumBytesFullCapSz) with 8; rewrite LgLineBytes_val.
  assert (E : (Zmod.to_Z sa * 8 mod 32 + Z.of_nat j mod 32) mod 32 = 8 * (Zmod.to_Z sa mod 4) + Z.of_nat j)
    by (rewrite (Z.mod_small (Z.of_nat j) 32) by lia;
        replace 32 with (4 * 8) by reflexivity; rewrite Z.mul_mod_distr_r by lia;
        rewrite Z.mod_small; [lia |]; pose proof (Z.mod_pos_bound (Zmod.to_Z sa) 4 ltac:(lia)); lia).
  rewrite E.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) 4 ltac:(lia)).
  apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id by lia; lia.
Qed.

Lemma winTagIdx_scanFull : forall sa, winTagIdx (scanFull sa) = Z.to_nat (Zmod.to_Z sa mod 4).
Proof.
  intros sa; unfold winTagIdx, memTagSlot.
  match goal with |- context [evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz ?x)] =>
    change (evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz x)) with (Zmod_lastn LgNumLineTags (evalExpr x)) end.
  unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z.
  rewrite Z.shiftr_div_pow2 by (cbv; congruence).
  unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var, to_Z_scanFull.
  pose proof (Zmod.to_Z_range sa) as Hs.
  change (2 ^ LgNumBytesFullCapSz) with 8; rewrite LgLineBytes_val.
  f_equal.
  match goal with |- (?u / 2 ^ ?d) mod 2 ^ ?e = _ =>
    change (2 ^ d) with 8; change (2 ^ e) with 4 end.
  replace 32 with (4 * 8) by reflexivity; rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.div_mul by lia.
  apply Z.mod_small; apply Z.mod_pos_bound; lia.
Qed.

(* The tag mask of a line write as `tmBits` at the address's offset *)
Lemma buildW_tagMask :
  forall b addr pkt size,
    let o := evalExpr (memLineOffset (Var type Addr addr)) in
    (buildW b addr pkt size).(Snd).(Snd).(Snd).(Snd).(Fst).(tupleElems) =
    tmBits b (Zmod.of_Z _ (Zmod.to_Z o mod 8)) (Zmod.of_Z _ (Zmod.to_Z o / 8)) size.
Proof.
  intros b addr pkt size o.
  unfold tmBits; apply (f_equal (fun t : SameTuple bool NumLineTags => t.(tupleElems))).
  transitivity (evalLetExpr (memTagMask (Const type Bool b) (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)));
    [reflexivity |].
  rewrite tagMask_parts; apply tagMaskO_cong.
  - apply Zmod.unsigned_inj.
    rewrite to_Z_TruncLsb, to_Z_Var; cbn [evalExpr]; rewrite Zmod.unsigned_of_Z.
    subst o; unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var.
    change (2 ^ LgNumBytesFullCapSz) with 8; rewrite LgLineBytes_val.
    rewrite Z.mod_mod by lia.
    symmetry; apply Z.mod_mod_divide; exists 4; reflexivity.
  - apply Zmod.unsigned_inj.
    unfold memTagSlot.
    match goal with |- context [evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz ?x)] =>
      change (evalExpr (TruncMsb LgNumLineTags LgNumBytesFullCapSz x)) with (Zmod_lastn LgNumLineTags (evalExpr x)) end.
    unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by (cbv; congruence).
    cbn [evalExpr]; rewrite Zmod.unsigned_of_Z.
    subst o; unfold memLineOffset; rewrite !to_Z_TruncLsb, !to_Z_Var.
    rewrite LgLineBytes_val.
    match goal with |- (?u / 2 ^ ?d) mod 2 ^ ?e = _ =>
      change (2 ^ d) with 8; change (2 ^ e) with 4 end.
    change (2 ^ LgNumLineTags) with 4.
    pose proof (Zmod.to_Z_range addr); lia.
Qed.

(* --- The conditions in Z --- *)

Lemma to_Z_lineOf_false : forall x, Zmod.to_Z (lineOf false x) = Zmod.to_Z x / 32 * 32.
Proof.
  intros x; unfold lineOf, memLineAddr; cbn [evalExpr].
  etransitivity; [apply bits.unsigned_app; cbv; congruence |].
  rewrite bits.unsigned_app by (cbv; congruence).
  rewrite !Zmod.unsigned_0, !Z.shiftl_0_l, !Z.lor_0_l.
  rewrite Z.shiftl_mul_pow2 by (cbv; congruence).
  unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by (cbv; congruence).

  match goal with |- (?u / 2 ^ ?d) mod 2 ^ ?e * 2 ^ ?f = _ =>
    change (2 ^ d) with 32; change (2 ^ e) with 134217728; change (2 ^ f) with 32 end.
  rewrite Z.mod_small; [reflexivity |].
  match goal with |- context [@Zmod.unsigned ?m x] =>
    assert (Hx : 0 <= @Zmod.unsigned m x < 4294967296) by exact (Zmod.unsigned_pos_bound x ltac:(cbv; reflexivity)) end.
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

(* A crossing access runs past its line's end *)
Lemma crossesB_true : forall (a : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)),
  crossesB a sz = true -> 32 < Zmod.to_Z a mod 32 + 2 ^ Zmod.to_Z sz.
Proof.
  intros a sz H; apply Z.nle_gt; intros Hle.
  rewrite crossesB_false in H; [discriminate H |].
  rewrite LgLineBytes_val; exact Hle.
Qed.

(* The store's slot and the next one, in Z *)
Lemma to_Z_slotOf : forall addr : type Addr,
  Zmod.to_Z (Zmod_lastn TagAddrWidth addr) = Zmod.to_Z addr / 8.
Proof.
  intros addr; unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by (cbv; congruence).
  match goal with |- context [@Zmod.unsigned ?m addr] =>
    assert (Hx : 0 <= @Zmod.unsigned m addr < 4294967296) by exact (Zmod.unsigned_pos_bound addr ltac:(cbv; reflexivity)) end.
  match goal with |- (?u / 2 ^ ?d) mod 2 ^ ?e = _ => change (2 ^ d) with 8; change (2 ^ e) with 536870912 end.
  apply Z.mod_small; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
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
    Zmod.to_Z addr / 8 <> Zmod.to_Z sa /\
    (8 <= Zmod.to_Z addr mod 8 + 2 ^ Zmod.to_Z size - 1 -> (Zmod.to_Z addr / 8 + 1) mod 2 ^ 29 <> Zmod.to_Z sa).
Proof.
  intros addr size sa H.
  unfold snoopHitsB in H; cbv zeta in H.
  apply evalExpr_Or2_false in H as [H1 H2].
  apply evalExpr_Eq_false in H1; rewrite !to_Z_Var in H1.
  assert (HA : 0 <= Zmod.to_Z addr < 4294967296) by exact (Zmod.unsigned_pos_bound addr ltac:(cbv; reflexivity)).
  assert (Hsz : 0 <= Zmod.to_Z size < 4) by exact (Zmod.unsigned_pos_bound size ltac:(cbv; reflexivity)).
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
      change (2 ^ TagAddrWidth) with 536870912 in H3; change (2 ^ 29) with 536870912.
      rewrite (Z.mod_small 1 536870912) in H3 by lia.
      exact H3.
    + match goal with |- evalExpr (Var _ _ (evalExpr (FromBit Bool ?e))) = true =>
        change (Zmod.eqb (evalExpr e) Zmod.one = true) end.
      apply Zmod.eqb_eq, Zmod.unsigned_inj.
      match goal with |- context [evalExpr (TruncMsb 1 LgNumBytesFullCapSz ?x)] =>
        change (evalExpr (TruncMsb 1 LgNumBytesFullCapSz x)) with (Zmod_lastn 1 (evalExpr x)) end.
      unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by (cbv; congruence).
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
      change (2 ^ LgNumBytesFullCapSz) with 8; change (2 ^ (LgNumBytesFullCapSz + 1)) with 16.
      change (2 ^ (LgNumBytesFullCapSz + 1 - 1)) with 8; change (2 ^ 1) with 2.
      rewrite Z.shiftl_1_l.
      assert (Ecs : Zmod.to_Z size = 0 \/ Zmod.to_Z size = 1 \/ Zmod.to_Z size = 2 \/ Zmod.to_Z size = 3) by lia.
      pose proof (Z.mod_pos_bound (Zmod.to_Z addr) 8 ltac:(lia)) as Hr.
      generalize dependent (Zmod.to_Z addr mod 8); intros r Hc Hr.
      assert (Er : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia.
      destruct Ecs as [E | [E | [E | E]]]; rewrite E in Hc |- *; cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in Hc |- *;
        destruct Er as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; first [reflexivity | lia].
Qed.

Lemma to_Z_lineOf_true : forall x, Zmod.to_Z (lineOf true x) = (Zmod.to_Z x / 32 * 32 + 32) mod 2 ^ 32.
Proof.
  intros x; unfold lineOf, memNextLineAddr.
  rewrite to_Z_Add2.
  change (evalExpr (memLineAddr (Var type Addr x))) with (lineOf false x).
  rewrite to_Z_lineOf_false.
  reflexivity.
Qed.

Lemma to_Z_offset : forall addr : type Addr,
  Zmod.to_Z (evalExpr (memLineOffset (Var type Addr addr))) = Zmod.to_Z addr mod 32.
Proof. intros addr; unfold memLineOffset; rewrite to_Z_TruncLsb, to_Z_Var; reflexivity. Qed.

(* The second line of a crossing store holds slot 0 of the next line, the store's slot + 1 *)
Lemma arith_second :
  forall A S, 0 <= A < 4294967296 -> 0 <= S < 536870912 -> S mod 4 = 0 -> 25 <= A mod 32 ->
    (A / 32 * 32 + 32) mod 4294967296 = S * 8 / 32 * 32 -> (A / 8 + 1) mod 536870912 = S.
Proof.
  intros A S HA HS Hk Ho Hl.
  pose proof (Z.mod_pos_bound A 32 ltac:(lia)) as HAm.
  pose proof (Z.div_mod A 32 ltac:(lia)) as HAd.
  pose proof (Z.mod_pos_bound S 4 ltac:(lia)) as HSm.
  pose proof (Z.div_mod S 4 ltac:(lia)) as HSd.
  assert (H8 : A / 8 = 4 * (A / 32) + 3).
  { assert (EA : A = 4 * (A / 32) * 8 + A mod 32) by (pose proof (Z.div_mod A 32 ltac:(lia)); lia).
    rewrite EA at 1; rewrite Z.div_add_l by lia.
    assert (Eo : A mod 32 / 8 = 3) by (symmetry; apply Z.div_unique with (r := A mod 32 - 24); [left |]; lia).
    rewrite Eo; reflexivity. }
  assert (HS8 : S * 8 / 32 * 32 = 8 * S).
  { assert (ES : S = S / 4 * 4) by (pose proof (Z.div_mod S 4 ltac:(lia)); lia).
    rewrite ES at 1.
    replace (S / 4 * 4 * 8) with (S / 4 * 32) by ring.
    rewrite Z.div_mul by lia; lia. }
  rewrite HS8 in Hl; rewrite H8.
  assert (Hq : 0 <= A / 32 < 134217728) by lia.
  destruct (Z.lt_ge_cases (A / 32 + 1) 134217728) as [Hlt | Hge].
  - rewrite Z.mod_small in Hl by lia; rewrite Z.mod_small by lia; lia.
  - assert (Eq : A / 32 = 134217727) by lia.
    rewrite Eq in Hl |- *.
    change ((134217727 * 32 + 32) mod 4294967296) with 0 in Hl.
    change ((4 * 134217727 + 3 + 1) mod 536870912) with 0; lia.
Qed.

Lemma pow2_0 : 2 ^ 0 = 1. Proof. reflexivity. Qed.
Lemma pow2_1 : 2 ^ 1 = 2. Proof. reflexivity. Qed.
Lemma pow2_2 : 2 ^ 2 = 4. Proof. reflexivity. Qed.
Lemma pow2_3 : 2 ^ 3 = 8. Proof. reflexivity. Qed.

Lemma div8_split : forall A, 0 <= A ->
  A / 8 = 4 * (A / 32) + A mod 32 / 8 /\ A mod 8 = A mod 32 mod 8 /\ 0 <= A mod 32 < 32 /\ 0 <= A mod 8 < 8.
Proof.
  intros A HA.
  pose proof (Z.mod_pos_bound A 32 ltac:(lia)); pose proof (Z.mod_pos_bound A 8 ltac:(lia)).
  split; [| split; [| split; lia]].
  - assert (EA : A = 4 * (A / 32) * 8 + A mod 32) by (pose proof (Z.div_mod A 32 ltac:(lia)); lia).
    rewrite EA at 1; rewrite Z.div_add_l by lia; reflexivity.
  - symmetry; apply Z.mod_mod_divide; exists 4; reflexivity.
Qed.

(* The slot condition from the line equality, the snoop miss and (second line) the crossing *)
Lemma dCond_of :
  forall b (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) sa,
    lineOf b addr = lineOf false (scanFull sa) ->
    snoopHitsB addr size sa = false ->
    (b = true -> crossesB addr size = true) ->
    dCond b (Zmod.to_Z (evalExpr (memLineOffset (Var type Addr addr)))) (Zmod.to_Z size) (Zmod.to_Z sa mod 4) = true.
Proof.
  intros b addr size sa Hl Hm Hcr.
  destruct (snoopMiss_Z addr size sa Hm) as [M1 M2].
  apply (f_equal (@Zmod.to_Z _)) in Hl.
  rewrite to_Z_lineOf_false, to_Z_scanFull in Hl.
  rewrite to_Z_offset.
  assert (HA : 0 <= Zmod.to_Z addr < 4294967296) by exact (Zmod.unsigned_pos_bound addr ltac:(cbv; reflexivity)).
  assert (HS : 0 <= Zmod.to_Z sa < 536870912) by exact (Zmod.unsigned_pos_bound sa ltac:(cbv; reflexivity)).
  assert (Hsz : 0 <= Zmod.to_Z size < 4) by exact (Zmod.unsigned_pos_bound size ltac:(cbv; reflexivity)).
  change (2 ^ LgNumBytesFullCapSz) with 8 in Hl.
  change (2 ^ 29) with 536870912 in M2.
  destruct (div8_split (Zmod.to_Z addr) ltac:(lia)) as [D1 [D2 [D3 D4]]].
  pose proof (Z.div_mod (Zmod.to_Z sa) 4 ltac:(lia)) as DS1.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) 4 ltac:(lia)) as DS2.
  pose proof (Z.mod_pos_bound (Zmod.to_Z addr mod 32) 8 ltac:(lia)) as D5.
  pose proof (Z.div_mod (Zmod.to_Z addr mod 32) 8 ltac:(lia)) as D6.
  assert (DS3 : Zmod.to_Z sa * 8 / 32 = Zmod.to_Z sa / 4)
    by (change 32 with (4 * 8); apply Z.div_mul_cancel_r; lia).
  assert (D7 : 24 <= Zmod.to_Z addr mod 32 -> Zmod.to_Z addr mod 8 = Zmod.to_Z addr mod 32 - 24)
    by (intros H24; rewrite D2; symmetry; apply Z.mod_unique with (q := 3); [left |]; lia).
  assert (Ecs : Zmod.to_Z size = 0 \/ Zmod.to_Z size = 1 \/ Zmod.to_Z size = 2 \/ Zmod.to_Z size = 3) by lia.
  destruct b.
  - pose proof (crossesB_true addr size (Hcr eq_refl)) as Hx.
    rewrite to_Z_lineOf_true in Hl; change (2 ^ 32) with 4294967296 in Hl.
    unfold dCond.
    destruct Ecs as [E | [E | [E | E]]]; rewrite E in *; rewrite ?pow2_0, ?pow2_1, ?pow2_2, ?pow2_3 in *.
    all: apply orb_true_intro.
    all: destruct (Z.eqb_spec (Zmod.to_Z sa mod 4) 0) as [Hk | Hk]; [right | left; reflexivity].
    all: apply negb_true_iff, Z.ltb_ge; exfalso; apply M2.
    all: first [apply arith_second; [lia | lia | exact Hk | lia | exact Hl] | lia].
  - rewrite (to_Z_lineOf_false addr) in Hl.
    assert (HlS : Zmod.to_Z addr / 32 = Zmod.to_Z sa / 4) by (rewrite DS3 in Hl; lia).
    clear Hl.
    unfold dCond.
    destruct Ecs as [E | [E | [E | E]]]; rewrite E in *; rewrite ?pow2_0, ?pow2_1, ?pow2_2, ?pow2_3 in *.
    all: apply andb_true_intro; split; apply negb_true_iff.
    all: first [ apply Z.eqb_neq; intros Ek; apply M1; lia
               | apply not_true_is_false; intros Hb; apply andb_true_iff in Hb as [Hb1 Hb2];
                 apply Z.leb_le in Hb1; apply Z.eqb_eq in Hb2; apply (M2 ltac:(lia));
                 assert (Ex : Zmod.to_Z addr / 8 + 1 = Zmod.to_Z sa) by lia;
                 rewrite Ex; apply Z.mod_small; lia ].
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
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) 4 ltac:(lia)) as Hk.
  assert (Hk4 : (Z.to_nat (Zmod.to_Z sa mod 4) < 4)%nat) by lia.
  rewrite <- (Z2Nat.id (Zmod.to_Z sa mod 4)) in Hd by lia.
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
