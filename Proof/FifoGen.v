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

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot.Proof Require Import StateRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * GENERIC SHIFT-FIFO LEMMAS (ANY CAPACITY)
 * ===========================================================================
 * List-level effect of `enq`, `deq`, `first`, `isFull`, `isEmpty`, `clear` of
 * `ShiftFifo.v` for any capacity, in terms of `fifo_to_list` (StateRel.v).
 *
 * Usage: after a stage wrapper such as
 * `SimFetchDecode.evalActionPropGen_fetchInstDeq`, run `fifo_eval` (goal) or
 * `fifo_eval in H` (section 5), or rewrite with `evalActionPropGen_enq_iff` /
 * `_deq_iff` / `_first_iff` / `_isFull_iff` / `_isEmpty_iff` / `_clear_iff`
 * giving `dom cap k` explicitly (plain `rewrite` without them fails there).
 * Then describe the new state with `fifo_to_list_enq` / `fifo_to_list_deq` /
 * `fifo_to_list_clear`, and keep the invariant `fifo_wf` with `fifo_wf_enq` /
 * `fifo_wf_deq` / `fifo_wf_clear` (initially: `InitStateConsistent_fifo_wf`). *)

(* NOTE: in this file `length` refers to `String.length` (String is imported
 * after the prelude), so list lengths are written `Datatypes.length`, and list
 * append is written with an explicit `%list` scope. *)

(* ---------------------------------------------------------------------------
 * 1. Generic list helpers
 * --------------------------------------------------------------------------- *)

(* Replace the `i`-th element of `l` by `v` (no-op if out of range). *)
Fixpoint fifo_upd {A : Type} (l : list A) (i : nat) (v : A) : list A :=
  match l with
  | [] => []
  | x :: xs =>
      match i with
      | O => v :: xs
      | S i' => x :: fifo_upd xs i' v
      end
  end.

(* Effect of `shiftElems` on the register contents: every element takes the
 * value of its successor, the last element keeps its value. *)
Fixpoint fifo_shiftList {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | _ :: ((y :: _) as rest) => y :: fifo_shiftList rest
  end.

Lemma firstn_S_fifo_upd : forall {A : Type} (l : list A) (n : nat) (v : A),
  (n < Datatypes.length l)%nat ->
  firstn (S n) (fifo_upd l n v) = (firstn n l ++ [v])%list.
Proof.
  intros A l. induction l as [| x l IH]; intros n v Hn.
  - cbn in Hn. lia.
  - destruct n as [| n].
    + reflexivity.
    + cbn [fifo_upd firstn app]. f_equal. apply IH. cbn in Hn. lia.
Qed.

Lemma firstn_fifo_shiftList : forall {A : Type} (l : list A) (m : nat),
  (m < Datatypes.length l)%nat -> firstn m (fifo_shiftList l) = firstn m (tl l).
Proof.
  intros A l. induction l as [| x l IH]; intros m Hm.
  - reflexivity.
  - destruct l as [| y l'].
    + cbn in Hm. assert (m = 0%nat) as -> by lia. reflexivity.
    + destruct m as [| m']; [reflexivity |].
      change (fifo_shiftList (x :: y :: l')) with (y :: fifo_shiftList (y :: l')).
      cbn [tl firstn]. f_equal.
      rewrite IH by (cbn in Hm |- *; lia). reflexivity.
Qed.

Lemma tl_firstn_S : forall {A : Type} (l : list A) (n : nat),
  tl (firstn (S n) l) = firstn n (tl l).
Proof. intros A [| x l] [| n]; reflexivity. Qed.

(* ---------------------------------------------------------------------------
 * 2. Generic register-list helpers (any tree)
 * --------------------------------------------------------------------------- *)

Definition readRegsAll {t : Tree DomainElem} {kk : Kind}
  (ps : list (RegOfKind (t := t) kk)) (s : TreeState DomainElemState t) : list (type kk) :=
  map (fun rk => readRegOfKind rk s) ps.

Lemma readRegsAll_cons : forall {t : Tree DomainElem} {kk : Kind}
  (r : RegOfKind (t := t) kk) (ps : list (RegOfKind (t := t) kk)) (s : TreeState DomainElemState t),
  readRegsAll (r :: ps) s = readRegOfKind r s :: readRegsAll ps s.
Proof. reflexivity. Qed.

Lemma readRegsAll_writeRegOfKind_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind} (r : RegOfKind (t := t) k2) (v : type k2)
         (ps : list (RegOfKind (t := t) k1)) (s : TreeState DomainElemState t),
    Forall (fun rk' : RegOfKind (t := t) k1 => rk'.(rk_path).(regPath) <> r.(rk_path).(regPath)) ps ->
    readRegsAll ps (writeRegOfKind r v s) = readRegsAll ps s.
Proof.
  intros t k1 k2 r v ps s Hall.
  induction Hall as [| r' ps' Hne Hall' IH]; [reflexivity |].
  rewrite !readRegsAll_cons, IH, (readRegOfKind_writeRegOfKind_other r' r v s Hne).
  reflexivity.
Qed.

Lemma readRegsAll_child0_ext :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {kk : Kind}
         (ps : list (RegOfKind (t := Node name (c0 :: cs)) kk))
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg ps = true -> s1.(Fst) = s2.(Fst) ->
    readRegsAll ps s1 = readRegsAll ps s2.
Proof.
  intros name c0 cs kk ps s1 s2 Hall Heq. revert Hall.
  induction ps as [| r ps IH]; intros Hall; [reflexivity |].
  cbn [forallb] in Hall. apply andb_prop in Hall as [Hr Hrest].
  rewrite !readRegsAll_cons, (IH Hrest).
  f_equal. exact (proj2 (proj2 (writeRegOfKind_child0 r (getDefault kk) s1 s2 Hr) Heq)).
Qed.

(* Reading all registers after `writeRegsList` (evaluated). *)
Lemma readRegsAll_evalWriteRegsListHelper :
  forall {t : Tree DomainElem} {kk : Kind} {sz : Z}
         (ps : list (RegOfKind (t := t) kk)) (curr : nat) (idx : bits sz) (v : type kk)
         (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind (t := t) kk => r.(rk_path).(regPath)) ps) ->
    Z.of_nat curr <= Zmod.unsigned idx ->
    Z.of_nat (curr + Datatypes.length ps) <= 2 ^ sz ->
    readRegsAll ps (evalWriteRegsListHelper curr ps idx v s) =
    fifo_upd (readRegsAll ps s) (Z.to_nat (Zmod.unsigned idx) - curr)%nat v.
Proof.
  intros t kk sz ps. induction ps as [| r ps IH]; intros curr idx v s Hnd Hlo Hhi.
  - reflexivity.
  - cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hnin Hnd'].
    destruct (not_In_map_regPath_Forall r ps Hnin) as [HF1 HF2].
    cbn [Datatypes.length] in Hhi.
    change (evalWriteRegsListHelper curr (r :: ps) idx v s) with
      (evalWriteRegsListHelper (S curr) ps idx v
         (if @isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)) then writeRegOfKind r v s else s)).
    rewrite !readRegsAll_cons.
    destruct (Z.eq_dec (Zmod.unsigned idx) (Z.of_nat curr)) as [Heq | Hneq].
    + rewrite (isEq_Bit_of_Z_eq idx curr Heq).
      change (if true then writeRegOfKind r v s else s) with (writeRegOfKind r v s).
      rewrite (evalWriteRegsListHelper_above ps (S curr) idx v (writeRegOfKind r v s)) by lia.
      rewrite readRegOfKind_writeRegOfKind_same.
      rewrite (readRegsAll_writeRegOfKind_other r v ps s HF2).
      replace (Z.to_nat (Zmod.unsigned idx) - curr)%nat with 0%nat by lia.
      reflexivity.
    + rewrite (isEq_Bit_of_Z_neq idx curr) by lia.
      change (if false then writeRegOfKind r v s else s) with s.
      rewrite (readRegOfKind_evalWriteRegsListHelper_other r ps (S curr) idx v s HF1).
      rewrite (IH (S curr) idx v s Hnd') by lia.
      replace (Z.to_nat (Zmod.unsigned idx) - curr)%nat
        with (S (Z.to_nat (Zmod.unsigned idx) - S curr)) by lia.
      reflexivity.
Qed.

(* Evaluated effect of `shiftElems`. *)
Fixpoint evalShiftRegs {t : Tree DomainElem} {kk : Kind}
  (ps : list (RegOfKind (t := t) kk)) (s : TreeState DomainElemState t)
  : TreeState DomainElemState t :=
  match ps with
  | [] => s
  | [_] => s
  | rkCurr :: ((rkNext :: _) as rest) =>
      evalShiftRegs rest (writeRegOfKind rkCurr (readRegOfKind rkNext s) s)
  end.

Lemma evalShiftRegs_cons2 : forall {t : Tree DomainElem} {kk : Kind}
  (r1 r2 : RegOfKind (t := t) kk) (ps : list (RegOfKind (t := t) kk))
  (s : TreeState DomainElemState t),
  evalShiftRegs (r1 :: r2 :: ps) s =
  evalShiftRegs (r2 :: ps) (writeRegOfKind r1 (readRegOfKind r2 s) s).
Proof. reflexivity. Qed.

Lemma readRegOfKind_evalShiftRegs_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind} (rk : RegOfKind (t := t) k1)
         (ps : list (RegOfKind (t := t) k2)) (s : TreeState DomainElemState t),
    Forall (fun rk' : RegOfKind (t := t) k2 => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) ps ->
    readRegOfKind rk (evalShiftRegs ps s) = readRegOfKind rk s.
Proof.
  intros t k1 k2 rk ps. induction ps as [| r1 ps IH]; intros s Hall; [reflexivity |].
  destruct ps as [| r2 ps']; [reflexivity |].
  pose proof (Forall_inv Hall) as Hne. pose proof (Forall_inv_tail Hall) as Hall'.
  rewrite evalShiftRegs_cons2, (IH _ Hall').
  apply readRegOfKind_writeRegOfKind_other. exact Hne.
Qed.

Lemma evalShiftRegs_child0_Snd :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {kk : Kind}
         (ps : list (RegOfKind (t := Node name (c0 :: cs)) kk))
         (s : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg ps = true ->
    (evalShiftRegs ps s).(Snd) = s.(Snd).
Proof.
  intros name c0 cs kk ps. induction ps as [| r1 ps IH]; intros s Hall; [reflexivity |].
  destruct ps as [| r2 ps']; [reflexivity |].
  cbn [forallb] in Hall. apply andb_prop in Hall as [Hr1 Hrest].
  rewrite evalShiftRegs_cons2, (IH _ Hrest).
  exact (proj1 (writeRegOfKind_child0 r1 (readRegOfKind r2 s) s s Hr1)).
Qed.

Lemma readRegsAll_evalShiftRegs :
  forall {t : Tree DomainElem} {kk : Kind} (ps : list (RegOfKind (t := t) kk))
         (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind (t := t) kk => r.(rk_path).(regPath)) ps) ->
    readRegsAll ps (evalShiftRegs ps s) = fifo_shiftList (readRegsAll ps s).
Proof.
  intros t kk ps. induction ps as [| r1 ps IH]; intros s Hnd; [reflexivity |].
  destruct ps as [| r2 ps']; [reflexivity |].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hnin Hnd'].
  destruct (not_In_map_regPath_Forall r1 (r2 :: ps') Hnin) as [HF1 HF2].
  rewrite evalShiftRegs_cons2.
  rewrite (readRegsAll_cons r1 (r2 :: ps')
             (evalShiftRegs (r2 :: ps') (writeRegOfKind r1 (readRegOfKind r2 s) s))).
  rewrite (IH _ Hnd').
  rewrite (readRegOfKind_evalShiftRegs_other r1 (r2 :: ps') _ HF1).
  rewrite readRegOfKind_writeRegOfKind_same.
  rewrite (readRegsAll_writeRegOfKind_other r1 (readRegOfKind r2 s) (r2 :: ps') s HF2).
  reflexivity.
Qed.

(* Copy of `ImplStagedProof.unsigned_sub_ge` with a constant subtrahend
 * (matches the shape of `Sub #size $1` in `ShiftFifo.deq`). *)
Lemma fifo_unsigned_sub_const : forall (w : Z) (a b : bits w),
  0 < w ->
  Zmod.unsigned b <= Zmod.unsigned a ->
  Zmod.unsigned (evalExpr (Sub (Var type (Bit w) a) (Const type (Bit w) b))) =
  Zmod.unsigned a - Zmod.unsigned b.
Proof.
  intros w a b Hw Hle.
  cbn [evalExpr Sub fold_left map evalNot KindCustomInd].
  rewrite Zmod.add_0_l.
  rewrite !Zmod.unsigned_add.
  rewrite bits.unsigned_not' by lia.
  rewrite Z.ones_equiv; unfold Z.pred.
  unfold Zmod.one; rewrite Zmod.unsigned_of_Z.
  assert (H2w : 2 <= 2 ^ w).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  rewrite (Z.mod_small 1 (2 ^ w)) by lia.
  pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
  pose proof (bits.unsigned_range b ltac:(lia)) as Hb.
  rewrite Z.add_mod_idemp_l by lia.
  transitivity (((Zmod.unsigned a - Zmod.unsigned b) + 1 * 2 ^ w) mod 2 ^ w).
  { f_equal; lia. }
  rewrite Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

(* ---------------------------------------------------------------------------
 * 3. `getTreeRegsOfKind` length helpers
 * --------------------------------------------------------------------------- *)

Lemma length_getTreeRegsOfKind_cons : forall (kk : Kind) (name : string)
  (x : Tree DomainElem) (xs : list (Tree DomainElem)),
  Datatypes.length (getTreeRegsOfKind kk (Node name (x :: xs))) =
  (Datatypes.length (getTreeRegsOfKind kk x) +
   Datatypes.length (getTreeRegsOfKind kk (Node name xs)))%nat.
Proof.
  intros kk name x xs. cbn [getTreeRegsOfKind]. rewrite length_app, !length_map. reflexivity.
Qed.

Lemma length_dep_if_true : forall {A : Type} (b : bool)
  (f1 : b = true -> list A) (f2 : b = false -> list A),
  b = true -> (forall pf, Datatypes.length (f1 pf) = 1%nat) ->
  Datatypes.length ((if b as b0 return (b = b0 -> list A) then f1 else f2) eq_refl) = 1%nat.
Proof. intros A [|] f1 f2 Hb H1; [apply H1 | discriminate Hb]. Qed.

Lemma length_getTreeRegsOfKind_leaf : forall (kk : Kind) (name d : string) (r : Reg),
  regKind r = kk -> Datatypes.length (getTreeRegsOfKind kk (Leaf name (d, EReg r))) = 1%nat.
Proof.
  intros kk name d r Hr. cbn [getTreeRegsOfKind].
  apply length_dep_if_true.
  - subst kk. apply Kind_eqb_refl.
  - intros pf. reflexivity.
Qed.

Lemma length_getTreeRegsOfKind_seq : forall (d : string) (kk : Kind) (name : string)
  (g : nat -> string) (n start : nat),
  Datatypes.length
    (getTreeRegsOfKind kk
       (Node name (map (fun idx => Leaf (g idx) (d, EReg (Build_Reg kk None false))) (seq start n)))) = n.
Proof.
  intros d kk name g n. induction n as [| n IH]; intros start.
  - reflexivity.
  - cbn [seq map].
    rewrite length_getTreeRegsOfKind_cons,
      (length_getTreeRegsOfKind_leaf kk (g start) d (Build_Reg kk None false) eq_refl), IH.
    reflexivity.
Qed.

(* ---------------------------------------------------------------------------
 * 4. Shift-FIFO lemmas for an arbitrary capacity
 * --------------------------------------------------------------------------- *)

Section FifoGen.
  Variable dom : string.
  Variable cap : nat.
  Variable k : Kind.

  Local Abbreviation FT := (ShiftFifo.fifoTree dom cap k).
  Local Abbreviation FState := (TreeState DomainElemState (ShiftFifo.fifoTree dom cap k)).
  Local Abbreviation W := (Z.log2_up (Z.of_nat (cap + 1))).
  Local Abbreviation EPaths := (ShiftFifo.elemPathsWithKind dom cap k).

  (* Well-formedness: size <= capacity. *)
  Definition fifo_wf (f : FState) : Prop :=
    (Z.to_nat (Zmod.unsigned (fifo_size f)) <= cap)%nat.

  (* ----- width facts ----- *)

  Lemma fifo_W_nonneg : 0 <= W.
  Proof. apply Z.log2_up_nonneg. Qed.

  Lemma fifo_cap_lt_pow : Z.of_nat cap < 2 ^ W.
  Proof.
    pose proof (proj2 (Z.log2_up_le_pow2 (Z.of_nat (cap + 1)) W ltac:(lia)) (Z.le_refl _)) as H.
    lia.
  Qed.

  Lemma fifo_pow_pos : 0 < 2 ^ W.
  Proof. pose proof fifo_cap_lt_pow. lia. Qed.

  Lemma fifo_size_bound : forall f : FState, 0 <= Zmod.unsigned (fifo_size f) < 2 ^ W.
  Proof. intros f. exact (Zmod.unsigned_pos_bound (fifo_size f) fifo_pow_pos). Qed.

  (* ----- element-register paths ----- *)

  Lemma length_elemPaths : Datatypes.length EPaths = cap.
  Proof.
    unfold ShiftFifo.elemPathsWithKind. rewrite length_map.
    exact (length_getTreeRegsOfKind_seq dom k "elems"
             (fun idx => ("elem_" ++ hex_string_of_Z (Z.of_nat idx))%string) cap 0).
  Qed.

  Lemma elemPaths_all_child0 : forallb is_child0_reg EPaths = true.
  Proof.
    unfold ShiftFifo.elemPathsWithKind.
    generalize (getTreeRegsOfKind k (getNode (ShiftFifo.np_elems dom cap k))).
    intros l. induction l as [| x l IH]; [reflexivity |].
    cbn [map forallb]. rewrite IH. reflexivity.
  Qed.

  Lemma NoDup_elemPaths :
    NoDup (map (fun r : RegOfKind (t := FT) k => r.(rk_path).(regPath)) EPaths).
  Proof.
    unfold ShiftFifo.elemPathsWithKind. rewrite map_map.
    pose proof (NoDup_getTreeRegsOfKind k (getNode (ShiftFifo.np_elems dom cap k))) as Hnd.
    revert Hnd. generalize (getTreeRegsOfKind k (getNode (ShiftFifo.np_elems dom cap k))).
    intros l. induction l as [| x l IH]; intros Hnd; [constructor |].
    cbn [map] in Hnd |- *. apply NoDup_cons_iff in Hnd as [Hnin Hnd'].
    constructor; [| exact (IH Hnd')].
    intros Hin. apply Hnin.
    apply in_map_iff in Hin as [y [Hy Hiny]].
    apply in_map_iff. exists y. split; [| exact Hiny].
    cbn in Hy. injection Hy as Hy. exact Hy.
  Qed.

  Lemma length_fifo_elems_all : forall f : FState, Datatypes.length (fifo_elems_all f) = cap.
  Proof. intros f. unfold fifo_elems_all. rewrite length_map. exact length_elemPaths. Qed.

  Lemma length_fifo_to_list : forall f : FState, fifo_wf f ->
    Datatypes.length (fifo_to_list f) = Z.to_nat (Zmod.unsigned (fifo_size f)).
  Proof.
    intros f Hwf. unfold fifo_to_list.
    apply firstn_length_le. rewrite length_fifo_elems_all. exact Hwf.
  Qed.

  (* ----- state helpers ----- *)

  Definition fifoSetSize (f : FState) (sz : bits W) : FState :=
    (f.(Fst) ,, (sz ,, f.(Snd).(Snd))).

  Lemma fifo_size_setSize : forall (f : FState) (sz : bits W), fifo_size (fifoSetSize f sz) = sz.
  Proof. reflexivity. Qed.

  Lemma fifo_elems_all_setSize : forall (f : FState) (sz : bits W),
    fifo_elems_all (fifoSetSize f sz) = fifo_elems_all f.
  Proof.
    intros f sz.
    exact (readRegsAll_child0_ext EPaths (fifoSetSize f sz) f elemPaths_all_child0 eq_refl).
  Qed.

  Lemma fifo_size_evalWriteRegsList : forall (idx : bits W) (v : type k) (s : FState),
    fifo_size (evalWriteRegsList EPaths idx v s) = fifo_size s.
  Proof.
    intros idx v s. unfold fifo_size.
    assert (H : (evalWriteRegsList EPaths idx v s).(Snd) = s.(Snd))
      by exact (proj1 (evalWriteRegsListHelper_child0 EPaths 0 idx v s s elemPaths_all_child0)).
    rewrite H. reflexivity.
  Qed.

  Lemma fifo_elems_all_evalWriteRegsList : forall (idx : bits W) (v : type k) (s : FState),
    fifo_elems_all (evalWriteRegsList EPaths idx v s) =
    fifo_upd (fifo_elems_all s) (Z.to_nat (Zmod.unsigned idx)) v.
  Proof.
    intros idx v s.
    pose proof (Zmod.unsigned_pos_bound idx fifo_pow_pos) as Hb.
    pose proof fifo_cap_lt_pow as Hc.
    pose proof (readRegsAll_evalWriteRegsListHelper EPaths 0 idx v s NoDup_elemPaths) as H.
    rewrite length_elemPaths, Nat.sub_0_r in H.
    exact (H ltac:(lia) ltac:(lia)).
  Qed.

  Lemma fifo_size_evalShift : forall s : FState, fifo_size (evalShiftRegs EPaths s) = fifo_size s.
  Proof.
    intros s. unfold fifo_size.
    assert (H : (evalShiftRegs EPaths s).(Snd) = s.(Snd))
      by exact (evalShiftRegs_child0_Snd EPaths s elemPaths_all_child0).
    rewrite H. reflexivity.
  Qed.

  Lemma fifo_elems_all_evalShift : forall s : FState,
    fifo_elems_all (evalShiftRegs EPaths s) = fifo_shiftList (fifo_elems_all s).
  Proof. intros s. exact (readRegsAll_evalShiftRegs EPaths s NoDup_elemPaths). Qed.

  (* ----- size arithmetic ----- *)

  Lemma fifo_size_eqb_cap : forall f : FState,
    Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) =
    Nat.eqb (Z.to_nat (Zmod.unsigned (fifo_size f))) cap.
  Proof.
    intros f.
    pose proof (fifo_size_bound f) as Hb. pose proof fifo_cap_lt_pow as Hc.
    assert (Hu : Zmod.unsigned (Zmod.of_Z (2 ^ W) (Z.of_nat cap)) = Z.of_nat cap).
    { rewrite Zmod.unsigned_of_Z. apply Z.mod_small. lia. }
    destruct (Zmod.eqb_spec (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap))) as [Hz | Hnz].
    - rewrite Hz, Hu, Nat2Z.id, Nat.eqb_refl. reflexivity.
    - symmetry. apply Nat.eqb_neq. intros Heq. apply Hnz.
      apply Zmod.unsigned_inj. rewrite Hu. lia.
  Qed.

  Lemma fifo_size_eqb_zero : forall f : FState, fifo_wf f ->
    Zmod.eqb (fifo_size f) Zmod.zero = match fifo_to_list f with [] => true | _ => false end.
  Proof.
    intros f Hwf.
    pose proof (length_fifo_to_list f Hwf) as Hlen.
    pose proof (fifo_size_bound f) as Hb.
    revert Hlen.
    destruct (fifo_to_list f) as [| x l]; intros Hlen; cbn [Datatypes.length] in Hlen;
      destruct (Zmod.eqb_spec (fifo_size f) Zmod.zero) as [Hz | Hnz]; try reflexivity.
    - exfalso. apply Hnz. apply Zmod.unsigned_inj. rewrite Zmod.unsigned_0. lia.
    - exfalso. rewrite Hz, Zmod.unsigned_0 in Hlen. lia.
  Qed.

  Lemma fifo_size_nonzero : forall f : FState,
    Zmod.eqb (fifo_size f) Zmod.zero = false -> 1 <= Zmod.unsigned (fifo_size f).
  Proof.
    intros f Hemp. pose proof (fifo_size_bound f) as Hb.
    destruct (Z.eq_dec (Zmod.unsigned (fifo_size f)) 0) as [H0 | H0]; [| lia].
    exfalso.
    assert (Hz : fifo_size f = Zmod.zero)
      by (apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; exact H0).
    rewrite Hz, Zmod.eqb_refl in Hemp. discriminate Hemp.
  Qed.

  Lemma unsigned_fifoIncSize : forall (sz : bits W),
    Zmod.unsigned sz < Z.of_nat cap ->
    Zmod.unsigned (Zmod.add sz (Zmod.of_Z _ 1)) = Zmod.unsigned sz + 1.
  Proof.
    intros sz Hlt.
    pose proof (Zmod.unsigned_pos_bound sz fifo_pow_pos) as Hb.
    pose proof fifo_cap_lt_pow as Hc.
    rewrite Zmod.unsigned_add, Zmod.unsigned_of_Z.
    rewrite (Z.mod_small 1 (2 ^ W)) by lia.
    apply Z.mod_small. lia.
  Qed.

  (* `size - 1`, exactly as computed by `Sub #size $1` in `ShiftFifo.deq`. *)
  Definition fifoDecSize (sz : bits W) : bits W :=
    evalExpr (Sub (Var type (Bit W) sz) (Const type (Bit W) (Zmod.of_Z _ 1))).

  Lemma unsigned_fifoDecSize : forall (sz : bits W),
    1 <= Zmod.unsigned sz ->
    Zmod.unsigned (fifoDecSize sz) = Zmod.unsigned sz - 1.
  Proof.
    intros sz H1.
    pose proof (Zmod.unsigned_pos_bound sz fifo_pow_pos) as Hb.
    pose proof fifo_W_nonneg as HW0.
    assert (Hp : 1 < 2 ^ W) by lia.
    assert (HW : 0 < W).
    { destruct (Z.eq_dec W 0) as [H0 | H0]; [| lia].
      rewrite H0, Z.pow_0_r in Hp. lia. }
    assert (Hu1 : Zmod.unsigned (Zmod.of_Z (2 ^ W) 1) = 1).
    { rewrite Zmod.unsigned_of_Z. apply Z.mod_small. lia. }
    unfold fifoDecSize.
    rewrite fifo_unsigned_sub_const;
      [rewrite Hu1; reflexivity | exact HW | rewrite Hu1; exact H1].
  Qed.

  (* ----- abstract effects of the actions ----- *)

  Definition fifoEnqState (f : FState) (v : type k) : FState :=
    if Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) then f
    else evalWriteRegsList EPaths (fifo_size f) v
           (fifoSetSize f (Zmod.add (fifo_size f) (Zmod.of_Z _ 1))).

  Definition fifoDeqState (f : FState) : FState :=
    if Zmod.eqb (fifo_size f) Zmod.zero then f
    else evalShiftRegs EPaths (fifoSetSize f (fifoDecSize (fifo_size f))).

  Definition fifoFirstVal (f : FState) : type (Option k) :=
    (hd (getDefault k) (fifo_elems_all f) ,, (negb (Zmod.eqb (fifo_size f) Zmod.zero) ,, tt)).

  Lemma fifoEnqState_full_eq : forall (f : FState) (v : type k),
    Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) = true -> fifoEnqState f v = f.
  Proof. intros f v H. unfold fifoEnqState. rewrite H. reflexivity. Qed.

  Lemma fifoEnqState_nonfull_eq : forall (f : FState) (v : type k),
    Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) = false ->
    fifoEnqState f v =
    evalWriteRegsList EPaths (fifo_size f) v (fifoSetSize f (Zmod.add (fifo_size f) (Zmod.of_Z _ 1))).
  Proof. intros f v H. unfold fifoEnqState. rewrite H. reflexivity. Qed.

  Lemma fifoDeqState_empty_eq : forall f : FState,
    Zmod.eqb (fifo_size f) Zmod.zero = true -> fifoDeqState f = f.
  Proof. intros f H. unfold fifoDeqState. rewrite H. reflexivity. Qed.

  Lemma fifoDeqState_nonempty_eq : forall f : FState,
    Zmod.eqb (fifo_size f) Zmod.zero = false ->
    fifoDeqState f = evalShiftRegs EPaths (fifoSetSize f (fifoDecSize (fifo_size f))).
  Proof. intros f H. unfold fifoDeqState. rewrite H. reflexivity. Qed.

  (* ----- raw evaluation of the actions ----- *)

  Lemma evalActionPropGen_isFull_raw : forall env (f : FState) P,
    evalActionPropGen env (@ShiftFifo.isFull dom cap k type) f P <->
    P f (Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap))).
  Proof. intros env f P. reflexivity. Qed.

  Lemma evalActionPropGen_isEmpty_raw : forall env (f : FState) P,
    evalActionPropGen env (@ShiftFifo.isEmpty dom cap k type) f P <->
    P f (Zmod.eqb (fifo_size f) Zmod.zero).
  Proof. intros env f P. reflexivity. Qed.

  Lemma evalActionPropGen_enq_raw : forall env (v : type k) (f : FState) P,
    evalActionPropGen env (@ShiftFifo.enq dom cap k type v) f P <->
    (if negb (Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)))
     then evalActionPropGen env
            (writeRegsList EPaths (Var type (Bit W) (fifo_size f)) (Var type k v))
            (fifoSetSize f (Zmod.add (Zmod.add Zmod.zero (fifo_size f)) (Zmod.of_Z _ 1)))
            (fun s _ => P s Zmod.zero)
     else P f Zmod.zero).
  Proof. intros env v f P. reflexivity. Qed.

  Lemma evalActionPropGen_deq_raw : forall env (f : FState) P,
    evalActionPropGen env (@ShiftFifo.deq dom cap k type) f P <->
    (if negb (Zmod.eqb (fifo_size f) Zmod.zero)
     then evalActionPropGen env (@ShiftFifo.shiftElems dom cap k type EPaths)
            (fifoSetSize f (fifoDecSize (fifo_size f)))
            (fun s _ => P s Zmod.zero)
     else P f Zmod.zero).
  Proof. intros env f P. reflexivity. Qed.

  Lemma evalActionPropGen_shiftElems_step : forall env (rk1 rk2 : RegOfKind (t := FT) k)
    (ps : list (RegOfKind (t := FT) k)) (s : FState) P,
    evalActionPropGen env (@ShiftFifo.shiftElems dom cap k type (rk1 :: rk2 :: ps)) s P <->
    evalActionPropGen env (@ShiftFifo.shiftElems dom cap k type (rk2 :: ps))
      (writeTreeState FT s rk1.(rk_path).(regPath)
         (castStateRegInv rk1.(rk_path)
            (evalExpr (eq_rect k (Expr type) (Var type k (readRegOfKind rk2 s)) _
                         (eq_sym (Kind_eqb_eq _ _ rk1.(rk_pf))))))) P.
  Proof. intros env rk1 rk2 ps s P. reflexivity. Qed.

  Lemma evalActionPropGen_shiftElems : forall env (ps : list (RegOfKind (t := FT) k)) (s : FState) P,
    evalActionPropGen env (@ShiftFifo.shiftElems dom cap k type ps) s P <->
    P (evalShiftRegs ps s) Zmod.zero.
  Proof.
    intros env ps. induction ps as [| rk1 ps IH]; intros s P; [reflexivity |].
    destruct ps as [| rk2 ps']; [reflexivity |].
    rewrite evalActionPropGen_shiftElems_step, IH, evalExpr_eq_rect_Kind.
    reflexivity.
  Qed.

  (* ----- main evalActionPropGen lemmas ----- *)

  Lemma evalActionPropGen_enq_iff : forall env (v : type k) (f : FState) P,
    evalActionPropGen env (@ShiftFifo.enq dom cap k type v) f P <->
    P (fifoEnqState f v) Zmod.zero.
  Proof.
    intros env v f P. rewrite evalActionPropGen_enq_raw.
    destruct (Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap))) eqn:Hfull; cbn [negb].
    - rewrite (fifoEnqState_full_eq f v Hfull). reflexivity.
    - rewrite (fifoEnqState_nonfull_eq f v Hfull).
      rewrite evalActionPropGen_writeRegsList. cbn [evalExpr].
      rewrite Zmod.add_0_l. reflexivity.
  Qed.

  Lemma evalActionPropGen_deq_iff : forall env (f : FState) P,
    evalActionPropGen env (@ShiftFifo.deq dom cap k type) f P <->
    P (fifoDeqState f) Zmod.zero.
  Proof.
    intros env f P. rewrite evalActionPropGen_deq_raw.
    destruct (Zmod.eqb (fifo_size f) Zmod.zero) eqn:Hemp; cbn [negb].
    - rewrite (fifoDeqState_empty_eq f Hemp). reflexivity.
    - rewrite (fifoDeqState_nonempty_eq f Hemp).
      exact (evalActionPropGen_shiftElems env EPaths
               (fifoSetSize f (fifoDecSize (fifo_size f))) (fun s _ => P s Zmod.zero)).
  Qed.

  Lemma evalActionPropGen_first_iff : forall env (f : FState) P,
    evalActionPropGen env (@ShiftFifo.first dom cap k type) f P <-> P f (fifoFirstVal f).
  Proof.
    intros env f P.
    unfold fifoFirstVal, fifo_elems_all, ShiftFifo.first.
    destruct (ShiftFifo.elemPathsWithKind dom cap k) as [| rk0 rest]; reflexivity.
  Qed.

  Lemma evalActionPropGen_isFull_iff : forall env (f : FState) P, fifo_wf f ->
    (evalActionPropGen env (@ShiftFifo.isFull dom cap k type) f P <->
     P f (Nat.eqb (Datatypes.length (fifo_to_list f)) cap)).
  Proof.
    intros env f P Hwf.
    rewrite evalActionPropGen_isFull_raw, (length_fifo_to_list f Hwf), fifo_size_eqb_cap.
    reflexivity.
  Qed.

  Lemma evalActionPropGen_isEmpty_iff : forall env (f : FState) P, fifo_wf f ->
    (evalActionPropGen env (@ShiftFifo.isEmpty dom cap k type) f P <->
     P f (match fifo_to_list f with [] => true | _ => false end)).
  Proof.
    intros env f P Hwf.
    rewrite evalActionPropGen_isEmpty_raw, (fifo_size_eqb_zero f Hwf).
    reflexivity.
  Qed.

  (* ----- list-level lemmas ----- *)

  Lemma fifo_to_list_enq : forall (f : FState) (v : type k), fifo_wf f ->
    (Datatypes.length (fifo_to_list f) < cap)%nat ->
    fifo_to_list (fifoEnqState f v) = (fifo_to_list f ++ [v])%list.
  Proof.
    intros f v Hwf Hlt.
    rewrite (length_fifo_to_list f Hwf) in Hlt.
    pose proof (fifo_size_bound f) as Hb.
    assert (Hnf : Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) = false).
    { rewrite fifo_size_eqb_cap. apply Nat.eqb_neq. lia. }
    rewrite (fifoEnqState_nonfull_eq f v Hnf).
    unfold fifo_to_list at 1.
    rewrite fifo_size_evalWriteRegsList, fifo_elems_all_evalWriteRegsList,
      fifo_size_setSize, fifo_elems_all_setSize.
    rewrite unsigned_fifoIncSize by lia.
    replace (Z.to_nat (Zmod.unsigned (fifo_size f) + 1))
      with (S (Z.to_nat (Zmod.unsigned (fifo_size f)))) by lia.
    rewrite firstn_S_fifo_upd by (rewrite length_fifo_elems_all; lia).
    reflexivity.
  Qed.

  Lemma fifoEnqState_full : forall (f : FState) (v : type k), fifo_wf f ->
    Datatypes.length (fifo_to_list f) = cap -> fifoEnqState f v = f.
  Proof.
    intros f v Hwf Hlen. rewrite (length_fifo_to_list f Hwf) in Hlen.
    apply fifoEnqState_full_eq. rewrite fifo_size_eqb_cap, Hlen. apply Nat.eqb_refl.
  Qed.

  Lemma fifo_wf_enq : forall (f : FState) (v : type k), fifo_wf f -> fifo_wf (fifoEnqState f v).
  Proof.
    intros f v Hwf.
    destruct (Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap))) eqn:Hfull.
    - rewrite (fifoEnqState_full_eq f v Hfull). exact Hwf.
    - pose proof Hfull as Hfull'.
      rewrite fifo_size_eqb_cap in Hfull'. apply Nat.eqb_neq in Hfull'.
      pose proof (fifo_size_bound f) as Hb.
      unfold fifo_wf in *.
      rewrite (fifoEnqState_nonfull_eq f v Hfull), fifo_size_evalWriteRegsList, fifo_size_setSize.
      rewrite unsigned_fifoIncSize by lia.
      lia.
  Qed.

  Lemma fifo_to_list_deq : forall f : FState, fifo_wf f ->
    fifo_to_list (fifoDeqState f) = tl (fifo_to_list f).
  Proof.
    intros f Hwf.
    destruct (Zmod.eqb (fifo_size f) Zmod.zero) eqn:Hemp.
    - rewrite (fifoDeqState_empty_eq f Hemp).
      apply Zmod.eqb_eq in Hemp.
      unfold fifo_to_list. rewrite Hemp, Zmod.unsigned_0. reflexivity.
    - pose proof (fifo_size_nonzero f Hemp) as H1.
      rewrite (fifoDeqState_nonempty_eq f Hemp).
      unfold fifo_to_list.
      rewrite fifo_size_evalShift, fifo_elems_all_evalShift, fifo_size_setSize,
        fifo_elems_all_setSize.
      rewrite (unsigned_fifoDecSize (fifo_size f) H1).
      unfold fifo_wf in Hwf.
      destruct (Z.to_nat (Zmod.unsigned (fifo_size f))) as [| m] eqn:Hn; [lia |].
      replace (Z.to_nat (Zmod.unsigned (fifo_size f) - 1)) with m by lia.
      rewrite firstn_fifo_shiftList by (rewrite length_fifo_elems_all; lia).
      rewrite tl_firstn_S. reflexivity.
  Qed.

  Lemma fifo_wf_deq : forall f : FState, fifo_wf f -> fifo_wf (fifoDeqState f).
  Proof.
    intros f Hwf.
    destruct (Zmod.eqb (fifo_size f) Zmod.zero) eqn:Hemp.
    - rewrite (fifoDeqState_empty_eq f Hemp). exact Hwf.
    - pose proof (fifo_size_nonzero f Hemp) as H1.
      unfold fifo_wf in *.
      rewrite (fifoDeqState_nonempty_eq f Hemp), fifo_size_evalShift, fifo_size_setSize.
      rewrite (unsigned_fifoDecSize (fifo_size f) H1).
      lia.
  Qed.

  Lemma fifoFirstVal_valid : forall f : FState, fifo_wf f ->
    (fifoFirstVal f).(Snd).(Fst) = negb (match fifo_to_list f with [] => true | _ => false end).
  Proof. intros f Hwf. rewrite <- (fifo_size_eqb_zero f Hwf). reflexivity. Qed.

  Lemma fifoFirstVal_data : forall (f : FState) (x : type k) (l : list (type k)),
    fifo_to_list f = x :: l -> (fifoFirstVal f).(Fst) = x.
  Proof.
    intros f x l H. unfold fifo_to_list in H.
    change ((fifoFirstVal f).(Fst)) with (hd (getDefault k) (fifo_elems_all f)).
    revert H.
    destruct (fifo_elems_all f) as [| y ys]; intros H.
    - rewrite firstn_nil in H. discriminate H.
    - revert H. destruct (Z.to_nat (Zmod.unsigned (fifo_size f))) as [| n]; intros H.
      + discriminate H.
      + cbn [firstn] in H. injection H as Hy _. cbn [hd]. exact Hy.
  Qed.

  Lemma InitStateConsistent_fifo_wf : forall f : FState, InitStateConsistent FT f -> fifo_wf f.
  Proof.
    intros f Hinit. unfold fifo_wf.
    rewrite (InitStateConsistent_fifo_size dom cap k f Hinit), Zmod.unsigned_0. lia.
  Qed.

  Lemma length_fifo_to_list_le : forall f : FState, fifo_wf f ->
    (Datatypes.length (fifo_to_list f) <= cap)%nat.
  Proof. intros f Hwf. rewrite (length_fifo_to_list f Hwf). exact Hwf. Qed.

  (* ----- `clear` ----- *)

  Definition fifoClearState (f : FState) : FState := fifoSetSize f (Zmod.of_Z _ 0).

  Lemma evalActionPropGen_clear_iff : forall env (f : FState) P,
    evalActionPropGen env (@ShiftFifo.clear dom cap k type) f P <-> P (fifoClearState f) Zmod.zero.
  Proof. intros env f P. reflexivity. Qed.

  Lemma fifo_to_list_clear : forall f : FState, fifo_to_list (fifoClearState f) = [].
  Proof.
    intros f. pose proof fifo_pow_pos as Hp. unfold fifo_to_list, fifoClearState.
    rewrite fifo_size_setSize, Zmod.unsigned_of_Z, Z.mod_0_l by lia. reflexivity.
  Qed.

  Lemma fifo_wf_clear : forall f : FState, fifo_wf (fifoClearState f).
  Proof.
    intros f. pose proof fifo_pow_pos as Hp. unfold fifo_wf, fifoClearState.
    rewrite fifo_size_setSize, Zmod.unsigned_of_Z, Z.mod_0_l by lia. lia.
  Qed.
End FifoGen.

Arguments fifo_wf {dom cap k} f.
Arguments fifoSetSize {dom cap k} f sz.
Arguments fifoDecSize {cap} sz.
Arguments fifoEnqState {dom cap k} f v.
Arguments fifoDeqState {dom cap k} f.
Arguments fifoFirstVal {dom cap k} f.
Arguments fifoClearState {dom cap k} f.

(* ---------------------------------------------------------------------------
 * 5. `fifo_eval`: rewrite ShiftFifo action evaluations with the lemmas above
 * ---------------------------------------------------------------------------
 * Stage wrappers built with `evalActionPropGen_liftAction` (for example
 * `SimFetchDecode.evalActionPropGen_fetchInstDeq`) leave goals whose implicit
 * tree argument of `evalActionPropGen` is `getNode np`.  A plain
 * `rewrite evalActionPropGen_deq_iff` cannot unify that with
 * `ShiftFifo.fifoTree ?dom ?cap ?k` ("Found no subterm matching"), so give
 * `dom cap k` explicitly, e.g. `rewrite (evalActionPropGen_deq_iff dom cap k)`.
 * `fifo_eval` (goal) and `fifo_eval in H` do this automatically for every
 * enq/deq/first/clear they find.  isFull/isEmpty are rewritten only when a
 * hypothesis `fifo_wf f` for the FIFO state `f` is in context (no side goals
 * are created); otherwise use e.g. `rewrite (evalActionPropGen_isFull_iff
 * dom cap k)` and prove the `fifo_wf` side goal. *)

Ltac fifo_eval_goal_step :=
  match goal with
  | |- context [@evalActionPropGen _ _ _ (@ShiftFifo.enq ?d ?c ?kk _ _) _ _] =>
      rewrite (evalActionPropGen_enq_iff d c kk)
  | |- context [@evalActionPropGen _ _ _ (@ShiftFifo.deq ?d ?c ?kk _) _ _] =>
      rewrite (evalActionPropGen_deq_iff d c kk)
  | |- context [@evalActionPropGen _ _ _ (@ShiftFifo.first ?d ?c ?kk _) _ _] =>
      rewrite (evalActionPropGen_first_iff d c kk)
  | |- context [@evalActionPropGen _ _ _ (@ShiftFifo.clear ?d ?c ?kk _) _ _] =>
      rewrite (evalActionPropGen_clear_iff d c kk)
  | |- context [@evalActionPropGen _ _ _ (@ShiftFifo.isFull ?d ?c ?kk _) ?f _] =>
      let Hwf := fresh "Hwf" in
      assert (Hwf : @fifo_wf d c kk f) by assumption;
      rewrite (evalActionPropGen_isFull_iff d c kk _ f _ Hwf); clear Hwf
  | |- context [@evalActionPropGen _ _ _ (@ShiftFifo.isEmpty ?d ?c ?kk _) ?f _] =>
      let Hwf := fresh "Hwf" in
      assert (Hwf : @fifo_wf d c kk f) by assumption;
      rewrite (evalActionPropGen_isEmpty_iff d c kk _ f _ Hwf); clear Hwf
  end.

Ltac fifo_eval_hyp_step H :=
  match type of H with
  | context [@evalActionPropGen _ _ _ (@ShiftFifo.enq ?d ?c ?kk _ _) _ _] =>
      rewrite (evalActionPropGen_enq_iff d c kk) in H
  | context [@evalActionPropGen _ _ _ (@ShiftFifo.deq ?d ?c ?kk _) _ _] =>
      rewrite (evalActionPropGen_deq_iff d c kk) in H
  | context [@evalActionPropGen _ _ _ (@ShiftFifo.first ?d ?c ?kk _) _ _] =>
      rewrite (evalActionPropGen_first_iff d c kk) in H
  | context [@evalActionPropGen _ _ _ (@ShiftFifo.clear ?d ?c ?kk _) _ _] =>
      rewrite (evalActionPropGen_clear_iff d c kk) in H
  | context [@evalActionPropGen _ _ _ (@ShiftFifo.isFull ?d ?c ?kk _) ?f _] =>
      let Hwf := fresh "Hwf" in
      assert (Hwf : @fifo_wf d c kk f) by assumption;
      rewrite (evalActionPropGen_isFull_iff d c kk _ f _ Hwf) in H; clear Hwf
  | context [@evalActionPropGen _ _ _ (@ShiftFifo.isEmpty ?d ?c ?kk _) ?f _] =>
      let Hwf := fresh "Hwf" in
      assert (Hwf : @fifo_wf d c kk f) by assumption;
      rewrite (evalActionPropGen_isEmpty_iff d c kk _ f _ Hwf) in H; clear Hwf
  end.

Tactic Notation "fifo_eval" := repeat fifo_eval_goal_step.
Tactic Notation "fifo_eval" "in" hyp(H) := repeat (fifo_eval_hyp_step H).
