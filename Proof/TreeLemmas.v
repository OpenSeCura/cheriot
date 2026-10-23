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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Export SpecDefines ShiftFifo ShiftFifoLemmas ImplStaged ImplCommon.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. REGISTER-BANK HELPER DEFINITIONS & LEMMAS FOR `rfTree`
 * =========================================================================== *)

Definition updGpr (dom : string) (pcAddrInit : Z)
  (idx : bits RegIdxSzReal) (val : type FullECapWithTag)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : TreeState DomainElemState (rfTree dom pcAddrInit) :=
  evalWriteRegsList (gprPathsWithKind dom pcAddrInit) idx val rf.

Definition readGpr (dom : string) (pcAddrInit : Z)
  (idx : bits RegIdxSzReal)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : type FullECapWithTag :=
  evalReadRegsList (gprPathsWithKind dom pcAddrInit) idx rf.

Definition updScr (dom : string) (pcAddrInit : Z)
  (idx : bits ScrIdxSz) (val : type FullECapWithTag)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : TreeState DomainElemState (rfTree dom pcAddrInit) :=
  evalWriteRegsList (scrPathsWithKind dom pcAddrInit) idx val rf.

Definition readScr (dom : string) (pcAddrInit : Z)
  (idx : bits ScrIdxSz)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : type FullECapWithTag :=
  evalReadRegsList (scrPathsWithKind dom pcAddrInit) idx rf.

Definition updCsr (dom : string) (pcAddrInit : Z)
  (idx : bits CsrIdxSz) (val : type (Bit Xlen))
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : TreeState DomainElemState (rfTree dom pcAddrInit) :=
  evalWriteRegsList (csrPathsWithKind dom pcAddrInit) idx val rf.

Definition readCsr (dom : string) (pcAddrInit : Z)
  (idx : bits CsrIdxSz)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : type (Bit Xlen) :=
  evalReadRegsList (csrPathsWithKind dom pcAddrInit) idx rf.

Definition is_child0_reg {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inl _ => true
  | inr _ => false
  end.

Definition is_child1_reg {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: c1 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inr (inl _) => true
  | _ => false
  end.

Definition is_child2_reg {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inr (inr (inl _)) => true
  | _ => false
  end.

Lemma writeRegOfKind_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    is_child0_reg r = true ->
    (writeRegOfKind r val s1).(Snd) = s1.(Snd) /\
    (s1.(Fst) = s2.(Fst) ->
     (writeRegOfKind r val s1).(Fst) = (writeRegOfKind r val s2).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 cs k r val s1 s2 Hc0.
  unfold is_child0_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) w).(Snd) = s1.(Snd) /\
          (s1.(Fst) = s2.(Fst) ->
           (writeTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) =
           (writeTreeState (Node name (c0 :: cs)) s2 r.(rk_path).(regPath) w).(Fst) /\
           readTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: cs)) s2 r.(rk_path).(regPath))) as [H1 H2].
  { split; [exact H1 | intros Hfst; destruct (H2 Hfst) as [H3 H4]; split; [exact H3 | rewrite H4; reflexivity]]. }
  clearbody w; revert Hc0 w; generalize (r.(rk_path).(regPath)); intros [p0 | p_rest] Hc0 w; [| discriminate Hc0].
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | intros Hfst; rewrite Hfst; split; reflexivity].
Qed.

Lemma writeRegOfKind_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: c1 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    is_child1_reg r = true ->
    (writeRegOfKind r val s1).(Fst) = s1.(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Snd) = s1.(Snd).(Snd) /\
    (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
     (writeRegOfKind r val s1).(Snd).(Fst) = (writeRegOfKind r val s2).(Snd).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 c1 cs k r val s1 s2 Hc1.
  unfold is_child1_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) = s1.(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd) = s1.(Snd).(Snd) /\
          (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
           (writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Fst) =
           (writeTreeState (Node name (c0 :: c1 :: cs)) s2 r.(rk_path).(regPath) w).(Snd).(Fst) /\
           readTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: c1 :: cs)) s2 r.(rk_path).(regPath))) as [H1 [H2 H3]].
  { split; [exact H1 | split; [exact H2 | intros Hsf; destruct (H3 Hsf) as [H4 H5]; split; [exact H4 | rewrite H5; reflexivity]]]. }
  clearbody w; revert Hc1 w; generalize (r.(rk_path).(regPath)); intros [p0 | [p1 | p_rest]] Hc1 w; try discriminate Hc1.
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | split; [reflexivity | intros Hsf; rewrite Hsf; split; reflexivity]].
Qed.

Lemma writeRegOfKind_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    is_child2_reg r = true ->
    (writeRegOfKind r val s1).(Fst) = s1.(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Fst) = s1.(Snd).(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
    (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
     (writeRegOfKind r val s1).(Snd).(Snd).(Fst) = (writeRegOfKind r val s2).(Snd).(Snd).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 c1 c2 cs k r val s1 s2 Hc2.
  unfold is_child2_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) = s1.(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Fst) = s1.(Snd).(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
          (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
           (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd).(Fst) =
           (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s2 r.(rk_path).(regPath) w).(Snd).(Snd).(Fst) /\
           readTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: c1 :: c2 :: cs)) s2 r.(rk_path).(regPath))) as [H1 [H2 [H3 H4]]].
  { split; [exact H1 | split; [exact H2 | split; [exact H3 | intros Hssf; destruct (H4 Hssf) as [H5 H6]; split; [exact H5 | rewrite H6; reflexivity]]]]. }
  clearbody w; revert Hc2 w; generalize (r.(rk_path).(regPath)); intros [p0 | [p1 | [p2 | p_rest]]] Hc2 w; try discriminate Hc2.
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | split; [reflexivity | split; [reflexivity | intros Hssf; rewrite Hssf; split; reflexivity]]].
Qed.

Lemma evalWriteRegsListHelper_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Snd) = s1.(Snd) /\
    (s1.(Fst) = s2.(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Fst)).
Proof.
  intros name c0 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | exact id].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child0 r val s1 s2 Hr) as [Hsnd Hfst].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest) as [IHsnd IHfst].
      split; [rewrite IHsnd; exact Hsnd | intros Heq; apply IHfst, Hfst, Heq].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg paths = true ->
    s1.(Fst) = s2.(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child0 r (getDefault k) s1 s2 Hr) as [_ Hfst].
    destruct (Hfst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma evalWriteRegsListHelper_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    forallb is_child1_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Fst) = s1.(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd) = s1.(Snd).(Snd) /\
    (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Snd).(Fst)).
Proof.
  intros name c0 c1 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | split; [reflexivity | exact id]].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child1 r val s1 s2 Hr) as [Hfst [Hsndsnd Hsndfst]].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest)
        as [IHfst [IHsndsnd IHsndfst]].
      split; [rewrite IHfst; exact Hfst | split; [rewrite IHsndsnd; exact Hsndsnd | intros Heq; apply IHsndfst, Hsndfst, Heq]].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    forallb is_child1_reg paths = true ->
    s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 c1 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child1 r (getDefault k) s1 s2 Hr) as [_ [_ Hsndfst]].
    destruct (Hsndfst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma evalWriteRegsListHelper_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    forallb is_child2_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Fst) = s1.(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Fst) = s1.(Snd).(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
    (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Snd).(Snd).(Fst)).
Proof.
  intros name c0 c1 c2 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | split; [reflexivity | split; [reflexivity | exact id]]].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child2 r val s1 s2 Hr) as [Hfst [Hsndfst [Hsnd3 Hsnd2fst]]].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest)
        as [IHfst [IHsndfst [IHsnd3 IHsnd2fst]]].
      split; [rewrite IHfst; exact Hfst |
        split; [rewrite IHsndfst; exact Hsndfst |
          split; [rewrite IHsnd3; exact Hsnd3 |
            intros Heq; apply IHsnd2fst, Hsnd2fst, Heq]]].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    forallb is_child2_reg paths = true ->
    s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 c1 c2 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child2 r (getDefault k) s1 s2 Hr) as [_ [_ [_ Hsnd2fst]]].
    destruct (Hsnd2fst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma gprPaths_all_child0 :
  forall dom pcAddrInit,
    forallb is_child0_reg (gprPathsWithKind dom pcAddrInit) = true.
Proof.
  reflexivity.
Qed.

Lemma scrPaths_all_child1 :
  forall dom pcAddrInit,
    forallb is_child1_reg (scrPathsWithKind dom pcAddrInit) = true.
Proof.
  reflexivity.
Qed.

Lemma csrPaths_all_child2 :
  forall dom pcAddrInit,
    forallb is_child2_reg (csrPathsWithKind dom pcAddrInit) = true.
Proof.
  reflexivity.
Qed.

(* --- Cross-bank projections & frame lemmas --- *)

Lemma updGpr_Snd :
  forall dom pcAddrInit idx val rf,
    (updGpr dom pcAddrInit idx val rf).(Snd) = rf.(Snd).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (evalWriteRegsListHelper_child0 (gprPathsWithKind dom pcAddrInit) 0 idx val rf rf
                  (gprPaths_all_child0 dom pcAddrInit))).
Qed.

Lemma updGpr_Fst_ext :
  forall dom pcAddrInit idx val rf1 rf2,
    rf1.(Fst) = rf2.(Fst) ->
    (updGpr dom pcAddrInit idx val rf1).(Fst) = (updGpr dom pcAddrInit idx val rf2).(Fst).
Proof.
  intros dom pcAddrInit idx val rf1 rf2 Heq.
  exact (proj2 (evalWriteRegsListHelper_child0 (gprPathsWithKind dom pcAddrInit) 0 idx val rf1 rf2
                  (gprPaths_all_child0 dom pcAddrInit)) Heq).
Qed.

Lemma readGpr_Fst_ext :
  forall dom pcAddrInit idx rf1 rf2,
    rf1.(Fst) = rf2.(Fst) ->
    readGpr dom pcAddrInit idx rf1 = readGpr dom pcAddrInit idx rf2.
Proof.
  intros dom pcAddrInit idx rf1 rf2 Heq.
  exact (evalReadRegsListHelper_child0 (gprPathsWithKind dom pcAddrInit) 0 nil idx rf1 rf2
           (gprPaths_all_child0 dom pcAddrInit) Heq).
Qed.

Lemma updScr_Fst :
  forall dom pcAddrInit idx val rf,
    (updScr dom pcAddrInit idx val rf).(Fst) = rf.(Fst).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (evalWriteRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                  (scrPaths_all_child1 dom pcAddrInit))).
Qed.

Lemma updScr_Snd_Snd :
  forall dom pcAddrInit idx val rf,
    (updScr dom pcAddrInit idx val rf).(Snd).(Snd) = rf.(Snd).(Snd).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (proj2 (evalWriteRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                         (scrPaths_all_child1 dom pcAddrInit)))).
Qed.

Lemma updScr_Snd_Fst_ext :
  forall dom pcAddrInit idx val rf1 rf2,
    rf1.(Snd).(Fst) = rf2.(Snd).(Fst) ->
    (updScr dom pcAddrInit idx val rf1).(Snd).(Fst) = (updScr dom pcAddrInit idx val rf2).(Snd).(Fst).
Proof.
  intros dom pcAddrInit idx val rf1 rf2 Heq.
  exact (proj2 (proj2 (evalWriteRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 idx val rf1 rf2
                         (scrPaths_all_child1 dom pcAddrInit))) Heq).
Qed.

Lemma readScr_Snd_Fst_ext :
  forall dom pcAddrInit idx rf1 rf2,
    rf1.(Snd).(Fst) = rf2.(Snd).(Fst) ->
    readScr dom pcAddrInit idx rf1 = readScr dom pcAddrInit idx rf2.
Proof.
  intros dom pcAddrInit idx rf1 rf2 Heq.
  exact (evalReadRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 nil idx rf1 rf2
           (scrPaths_all_child1 dom pcAddrInit) Heq).
Qed.

Lemma updCsr_Fst :
  forall dom pcAddrInit idx val rf,
    (updCsr dom pcAddrInit idx val rf).(Fst) = rf.(Fst).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                  (csrPaths_all_child2 dom pcAddrInit))).
Qed.

Lemma updCsr_Snd_Fst :
  forall dom pcAddrInit idx val rf,
    (updCsr dom pcAddrInit idx val rf).(Snd).(Fst) = rf.(Snd).(Fst).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (proj2 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                         (csrPaths_all_child2 dom pcAddrInit)))).
Qed.

Lemma updCsr_Snd_Snd_Snd :
  forall dom pcAddrInit idx val rf,
    (updCsr dom pcAddrInit idx val rf).(Snd).(Snd).(Snd) = rf.(Snd).(Snd).(Snd).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (proj2 (proj2 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                                (csrPaths_all_child2 dom pcAddrInit))))).
Qed.

Lemma updCsr_Snd_Snd_Fst_ext :
  forall dom pcAddrInit idx val rf1 rf2,
    rf1.(Snd).(Snd).(Fst) = rf2.(Snd).(Snd).(Fst) ->
    (updCsr dom pcAddrInit idx val rf1).(Snd).(Snd).(Fst) = (updCsr dom pcAddrInit idx val rf2).(Snd).(Snd).(Fst).
Proof.
  intros dom pcAddrInit idx val rf1 rf2 Heq.
  exact (proj2 (proj2 (proj2 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf1 rf2
                                (csrPaths_all_child2 dom pcAddrInit)))) Heq).
Qed.

Lemma readCsr_Snd_Snd_Fst_ext :
  forall dom pcAddrInit idx rf1 rf2,
    rf1.(Snd).(Snd).(Fst) = rf2.(Snd).(Snd).(Fst) ->
    readCsr dom pcAddrInit idx rf1 = readCsr dom pcAddrInit idx rf2.
Proof.
  intros dom pcAddrInit idx rf1 rf2 Heq.
  exact (evalReadRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 nil idx rf1 rf2
           (csrPaths_all_child2 dom pcAddrInit) Heq).
Qed.

Lemma rfTree_state_eq :
  forall {dom pcAddrInit} (rf1 rf2 : TreeState DomainElemState (rfTree dom pcAddrInit)),
    rf1.(Fst) = rf2.(Fst) ->
    rf1.(Snd).(Fst) = rf2.(Snd).(Fst) ->
    rf1.(Snd).(Snd).(Fst) = rf2.(Snd).(Snd).(Fst) ->
    rf1 = rf2.
Proof.
  intros dom pcAddrInit [g1 [s1 [c1 []]]] [g2 [s2 [c2 []]]] Hg Hs Hc.
  cbn [Fst Snd] in *; subst; reflexivity.
Qed.

(* --- Cross-bank commutativity --- *)

Theorem updGpr_updScr_comm :
  forall dom pcAddrInit gprIdx gprVal scrIdx scrVal rf,
    updGpr dom pcAddrInit gprIdx gprVal (updScr dom pcAddrInit scrIdx scrVal rf) =
    updScr dom pcAddrInit scrIdx scrVal (updGpr dom pcAddrInit gprIdx gprVal rf).
Proof.
  intros dom pcAddrInit gprIdx gprVal scrIdx scrVal rf.
  apply rfTree_state_eq.
  - rewrite updScr_Fst; apply updGpr_Fst_ext, updScr_Fst.
  - rewrite !updGpr_Snd; symmetry; apply updScr_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
  - rewrite !updGpr_Snd, !updScr_Snd_Snd, !updGpr_Snd; reflexivity.
Qed.

Theorem updGpr_updCsr_comm :
  forall dom pcAddrInit gprIdx gprVal csrIdx csrVal rf,
    updGpr dom pcAddrInit gprIdx gprVal (updCsr dom pcAddrInit csrIdx csrVal rf) =
    updCsr dom pcAddrInit csrIdx csrVal (updGpr dom pcAddrInit gprIdx gprVal rf).
Proof.
  intros dom pcAddrInit gprIdx gprVal csrIdx csrVal rf.
  apply rfTree_state_eq.
  - rewrite updCsr_Fst; apply updGpr_Fst_ext, updCsr_Fst.
  - rewrite !updGpr_Snd, !updCsr_Snd_Fst, !updGpr_Snd; reflexivity.
  - rewrite !updGpr_Snd; symmetry; apply updCsr_Snd_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
Qed.

Theorem updScr_updCsr_comm :
  forall dom pcAddrInit scrIdx scrVal csrIdx csrVal rf,
    updScr dom pcAddrInit scrIdx scrVal (updCsr dom pcAddrInit csrIdx csrVal rf) =
    updCsr dom pcAddrInit csrIdx csrVal (updScr dom pcAddrInit scrIdx scrVal rf).
Proof.
  intros dom pcAddrInit scrIdx scrVal csrIdx csrVal rf.
  apply rfTree_state_eq.
  - rewrite !updScr_Fst, !updCsr_Fst, !updScr_Fst; reflexivity.
  - rewrite updCsr_Snd_Fst; apply updScr_Snd_Fst_ext, updCsr_Snd_Fst.
  - rewrite !updScr_Snd_Snd; symmetry; apply updCsr_Snd_Snd_Fst_ext; rewrite updScr_Snd_Snd; reflexivity.
Qed.

(* --- Cross-bank read-over-write invariance --- *)

Theorem readScr_updGpr :
  forall dom pcAddrInit scrIdx gprIdx gprVal rf,
    readScr dom pcAddrInit scrIdx (updGpr dom pcAddrInit gprIdx gprVal rf) =
    readScr dom pcAddrInit scrIdx rf.
Proof.
  intros; apply readScr_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
Qed.

Theorem readCsr_updGpr :
  forall dom pcAddrInit csrIdx gprIdx gprVal rf,
    readCsr dom pcAddrInit csrIdx (updGpr dom pcAddrInit gprIdx gprVal rf) =
    readCsr dom pcAddrInit csrIdx rf.
Proof.
  intros; apply readCsr_Snd_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
Qed.

Theorem readGpr_updScr :
  forall dom pcAddrInit gprIdx scrIdx scrVal rf,
    readGpr dom pcAddrInit gprIdx (updScr dom pcAddrInit scrIdx scrVal rf) =
    readGpr dom pcAddrInit gprIdx rf.
Proof.
  intros; apply readGpr_Fst_ext, updScr_Fst.
Qed.

Theorem readGpr_updCsr :
  forall dom pcAddrInit gprIdx csrIdx csrVal rf,
    readGpr dom pcAddrInit gprIdx (updCsr dom pcAddrInit csrIdx csrVal rf) =
    readGpr dom pcAddrInit gprIdx rf.
Proof.
  intros; apply readGpr_Fst_ext, updCsr_Fst.
Qed.

Theorem readScr_updCsr :
  forall dom pcAddrInit scrIdx csrIdx csrVal rf,
    readScr dom pcAddrInit scrIdx (updCsr dom pcAddrInit csrIdx csrVal rf) =
    readScr dom pcAddrInit scrIdx rf.
Proof.
  intros; apply readScr_Snd_Fst_ext, updCsr_Snd_Fst.
Qed.

Theorem readCsr_updScr :
  forall dom pcAddrInit csrIdx scrIdx scrVal rf,
    readCsr dom pcAddrInit csrIdx (updScr dom pcAddrInit scrIdx scrVal rf) =
    readCsr dom pcAddrInit csrIdx rf.
Proof.
  intros; apply readCsr_Snd_Snd_Fst_ext; rewrite updScr_Snd_Snd; reflexivity.
Qed.

(* --- Same-bank GPR, SCR, and CSR read-over-write and write-over-write lemmas --- *)

Lemma NoDup_gprPathsWithKind :
  forall dom pcAddrInit,
    NoDup (map (fun r : RegOfKind FullECapWithTag => r.(rk_path).(regPath))
               (gprPathsWithKind dom pcAddrInit)).
Proof.
  intros dom pcAddrInit.
  apply NoDup_regPath_of_leafPath_id.
  cbn [gprPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

Lemma NoDup_scrPathsWithKind :
  forall dom pcAddrInit,
    NoDup (map (fun r : RegOfKind FullECapWithTag => r.(rk_path).(regPath))
               (scrPathsWithKind dom pcAddrInit)).
Proof.
  intros dom pcAddrInit.
  apply NoDup_regPath_of_leafPath_id.
  cbn [scrPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

Lemma NoDup_csrPathsWithKind :
  forall dom pcAddrInit,
    NoDup (map (fun r : RegOfKind (Bit Xlen) => r.(rk_path).(regPath))
               (csrPathsWithKind dom pcAddrInit)).
Proof.
  intros dom pcAddrInit.
  apply NoDup_regPath_of_leafPath_id.
  cbn [csrPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

Theorem updGpr_same :
  forall dom pcAddrInit idx v1 v2 rf,
    updGpr dom pcAddrInit idx v2 (updGpr dom pcAddrInit idx v1 rf) =
    updGpr dom pcAddrInit idx v2 rf.
Proof.
  intros dom pcAddrInit idx v1 v2 rf; unfold updGpr.
  apply evalWriteRegsList_same, NoDup_gprPathsWithKind.
Qed.

Theorem updGpr_comm :
  forall dom pcAddrInit idx1 idx2 v1 v2 rf,
    idx1 <> idx2 ->
    updGpr dom pcAddrInit idx2 v2 (updGpr dom pcAddrInit idx1 v1 rf) =
    updGpr dom pcAddrInit idx1 v1 (updGpr dom pcAddrInit idx2 v2 rf).
Proof.
  intros dom pcAddrInit idx1 idx2 v1 v2 rf Hneq; unfold updGpr.
  apply evalWriteRegsList_comm; [apply NoDup_gprPathsWithKind | exact Hneq].
Qed.

Theorem readGpr_updGpr_other :
  forall dom pcAddrInit idx1 idx2 v rf,
    idx1 <> idx2 ->
    readGpr dom pcAddrInit idx1 (updGpr dom pcAddrInit idx2 v rf) =
    readGpr dom pcAddrInit idx1 rf.
Proof.
  intros dom pcAddrInit idx1 idx2 v rf Hneq; unfold readGpr, updGpr.
  apply evalReadRegsList_evalWriteRegsList_other; [apply NoDup_gprPathsWithKind | exact Hneq].
Qed.

Theorem readGpr_updGpr_same :
  forall dom pcAddrInit idx v rf,
    readGpr dom pcAddrInit idx (updGpr dom pcAddrInit idx v rf) = v.
Proof.
  intros dom pcAddrInit idx v rf; unfold readGpr, updGpr.
  apply evalReadRegsList_evalWriteRegsList_same; reflexivity.
Qed.

Theorem updScr_same :
  forall dom pcAddrInit idx v1 v2 rf,
    updScr dom pcAddrInit idx v2 (updScr dom pcAddrInit idx v1 rf) =
    updScr dom pcAddrInit idx v2 rf.
Proof.
  intros dom pcAddrInit idx v1 v2 rf; unfold updScr.
  apply evalWriteRegsList_same, NoDup_scrPathsWithKind.
Qed.

Theorem updScr_comm :
  forall dom pcAddrInit idx1 idx2 v1 v2 rf,
    idx1 <> idx2 ->
    updScr dom pcAddrInit idx2 v2 (updScr dom pcAddrInit idx1 v1 rf) =
    updScr dom pcAddrInit idx1 v1 (updScr dom pcAddrInit idx2 v2 rf).
Proof.
  intros dom pcAddrInit idx1 idx2 v1 v2 rf Hneq; unfold updScr.
  apply evalWriteRegsList_comm; [apply NoDup_scrPathsWithKind | exact Hneq].
Qed.

Theorem readScr_updScr_other :
  forall dom pcAddrInit idx1 idx2 v rf,
    idx1 <> idx2 ->
    readScr dom pcAddrInit idx1 (updScr dom pcAddrInit idx2 v rf) =
    readScr dom pcAddrInit idx1 rf.
Proof.
  intros dom pcAddrInit idx1 idx2 v rf Hneq; unfold readScr, updScr.
  apply evalReadRegsList_evalWriteRegsList_other; [apply NoDup_scrPathsWithKind | exact Hneq].
Qed.

Theorem updCsr_same :
  forall dom pcAddrInit idx v1 v2 rf,
    updCsr dom pcAddrInit idx v2 (updCsr dom pcAddrInit idx v1 rf) =
    updCsr dom pcAddrInit idx v2 rf.
Proof.
  intros dom pcAddrInit idx v1 v2 rf; unfold updCsr.
  apply evalWriteRegsList_same, NoDup_csrPathsWithKind.
Qed.

Theorem updCsr_comm :
  forall dom pcAddrInit idx1 idx2 v1 v2 rf,
    idx1 <> idx2 ->
    updCsr dom pcAddrInit idx2 v2 (updCsr dom pcAddrInit idx1 v1 rf) =
    updCsr dom pcAddrInit idx1 v1 (updCsr dom pcAddrInit idx2 v2 rf).
Proof.
  intros dom pcAddrInit idx1 idx2 v1 v2 rf Hneq; unfold updCsr.
  apply evalWriteRegsList_comm; [apply NoDup_csrPathsWithKind | exact Hneq].
Qed.

Theorem readCsr_updCsr_other :
  forall dom pcAddrInit idx1 idx2 v rf,
    idx1 <> idx2 ->
    readCsr dom pcAddrInit idx1 (updCsr dom pcAddrInit idx2 v rf) =
    readCsr dom pcAddrInit idx1 rf.
Proof.
  intros dom pcAddrInit idx1 idx2 v rf Hneq; unfold readCsr, updCsr.
  apply evalReadRegsList_evalWriteRegsList_other; [apply NoDup_csrPathsWithKind | exact Hneq].
Qed.

Theorem readScr_updScr_same :
  forall dom pcAddrInit idx v rf,
    Zmod.to_Z idx < 5 ->
    readScr dom pcAddrInit idx (updScr dom pcAddrInit idx v rf) = v.
Proof.
  intros dom pcAddrInit idx v rf Hlt; unfold readScr, updScr, evalReadRegsList, evalWriteRegsList.
  pose proof (Zmod.unsigned_pos_bound idx eq_refl) as Hb.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_same;
    [change (length (scrPathsWithKind dom pcAddrInit)) with 5%nat; lia
    | change (length (scrPathsWithKind dom pcAddrInit)) with 5%nat; change (2 ^ ScrIdxSz) with 8; lia
    | constructor].
Qed.

Theorem readCsr_updCsr_same :
  forall dom pcAddrInit idx v rf,
    Zmod.to_Z idx < 10 ->
    readCsr dom pcAddrInit idx (updCsr dom pcAddrInit idx v rf) = v.
Proof.
  intros dom pcAddrInit idx v rf Hlt; unfold readCsr, updCsr, evalReadRegsList, evalWriteRegsList.
  pose proof (Zmod.unsigned_pos_bound idx eq_refl) as Hb.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_same;
    [change (length (csrPathsWithKind dom pcAddrInit)) with 10%nat; lia
    | change (length (csrPathsWithKind dom pcAddrInit)) with 10%nat; change (2 ^ CsrIdxSz) with 16; lia
    | constructor].
Qed.

(* ===========================================================================
 * 5. `ShiftFifo` EVALUATION LEMMAS FOR `fifoTree dom depth elemK`
 * =========================================================================== *)

Definition fifo_elems {dom : string} {depth : nat} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom depth elemK))
  : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)) :=
  f.(Fst).

Definition fifo_size {dom : string} {depth : nat} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom depth elemK))
  : bits (Z.log2_up (Z.of_nat (depth + 1))) :=
  f.(Snd).(Fst).

Definition mkFifo {dom : string} {depth : nat} {elemK : Kind}
  (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
  (sz : bits (Z.log2_up (Z.of_nat (depth + 1))))
  : TreeState DomainElemState (fifoTree dom depth elemK) :=
  (elems ,, (sz ,, tt)).

Lemma mkFifo_eta :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)),
    mkFifo (fifo_elems f) (fifo_size f) = f.
Proof.
  intros dom depth elemK [elems [sz []]]; reflexivity.
Qed.

Lemma fifo_elems_mkFifo :
  forall {dom depth elemK}
         (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
         (sz : bits (Z.log2_up (Z.of_nat (depth + 1)))),
    fifo_elems (mkFifo elems sz) = elems.
Proof.
  reflexivity.
Qed.

Lemma fifo_size_mkFifo :
  forall {dom depth elemK}
         (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
         (sz : bits (Z.log2_up (Z.of_nat (depth + 1)))),
    fifo_size (mkFifo elems sz) = sz.
Proof.
  reflexivity.
Qed.

Fixpoint evalShiftElems {t : Tree DomainElem} {k : Kind}
  (ps : list (RegOfKind (t:=t) k)) (s : TreeState DomainElemState t)
  : TreeState DomainElemState t :=
  match ps with
  | [] => s
  | [_] => s
  | rkCurr :: ((rkNext :: _) as rest) =>
      let nextVal := readRegOfKind rkNext s in
      evalShiftElems rest (writeRegOfKind rkCurr nextVal s)
  end.

Lemma evalShiftElems_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (ps : list (RegOfKind (t := getNode p) k))
         (s : TreeState DomainElemState t),
    evalShiftElems (map (embedRegOfKind p) ps) s =
    writeSubTreeState p s (evalShiftElems ps (readSubTreeState p s)).
Proof.
  intros t p k ps.
  induction ps as [| rkCurr rest IH]; intros s.
  - cbn [map evalShiftElems]; symmetry; apply writeSubTreeState_readSubTreeState.
  - destruct rest as [| rkNext rest'].
    + cbn [map evalShiftElems]; symmetry; apply writeSubTreeState_readSubTreeState.
    + change (evalShiftElems (map (embedRegOfKind p) (rkCurr :: rkNext :: rest')) s)
        with (evalShiftElems (map (embedRegOfKind p) (rkNext :: rest'))
                (writeRegOfKind (embedRegOfKind p rkCurr)
                  (readRegOfKind (embedRegOfKind p rkNext) s) s)).
      change (evalShiftElems (rkCurr :: rkNext :: rest') (readSubTreeState p s))
        with (evalShiftElems (rkNext :: rest')
                (writeRegOfKind rkCurr
                  (readRegOfKind rkNext (readSubTreeState p s))
                  (readSubTreeState p s))).
      rewrite readRegOfKind_embed, writeRegOfKind_embed, IH,
              readSubTreeState_writeSubTreeState_same, writeSubTreeState_writeSubTreeState_same.
      reflexivity.
Qed.

Definition fifo_head_elem {dom : string} {depth : nat} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom depth elemK)) : type elemK :=
  match elemPathsWithKind dom depth elemK with
  | [] => getDefault elemK
  | rk0 :: _ => readRegOfKind rk0 f
  end.

Definition fifo_enq_elems {dom : string} {depth : nat} {elemK : Kind}
  (idx : bits (Z.log2_up (Z.of_nat (depth + 1)))) (val : type elemK)
  (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
  : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)) :=
  evalWriteRegsList (getTreeRegsOfKind elemK (Node "elems" (elemLeaves dom depth elemK))) idx val elems.

Definition fifo_shift_elems {dom : string} {depth : nat} {elemK : Kind}
  (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
  : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)) :=
  evalShiftElems (getTreeRegsOfKind elemK (Node "elems" (elemLeaves dom depth elemK))) elems.

Lemma evalWriteRegsList_elemPathsWithKind :
  forall {dom depth elemK}
         (idx : bits (Z.log2_up (Z.of_nat (depth + 1)))) (val : type elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)),
    evalWriteRegsList (elemPathsWithKind dom depth elemK) idx val f =
    mkFifo (fifo_enq_elems idx val (fifo_elems f)) (fifo_size f).
Proof.
  intros dom depth elemK idx val [elems [sz []]].
  unfold elemPathsWithKind, fifo_enq_elems, fifo_elems, fifo_size, mkFifo.
  rewrite evalWriteRegsList_map_embedRegOfKind.
  reflexivity.
Qed.

Lemma evalShiftElems_elemPathsWithKind :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)),
    evalShiftElems (elemPathsWithKind dom depth elemK) f =
    mkFifo (fifo_shift_elems (fifo_elems f)) (fifo_size f).
Proof.
  intros dom depth elemK [elems [sz []]].
  unfold elemPathsWithKind, fifo_shift_elems, fifo_elems, fifo_size, mkFifo.
  rewrite evalShiftElems_map_embedRegOfKind.
  reflexivity.
Qed.

Lemma evalActionPropGen_readElemReg :
  forall {dom depth elemK} (rk : RegOfKind (t := fifoTree dom depth elemK) elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@readElemReg dom depth elemK type rk) f P <->
    P f (readRegOfKind rk f).
Proof.
  reflexivity.
Qed.

Lemma evalActionPropGen_writeElemReg :
  forall {dom depth elemK} (rk : RegOfKind (t := fifoTree dom depth elemK) elemK)
         (newVal : Expr type elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@writeElemReg dom depth elemK type rk newVal) f P <->
    P (writeRegOfKind rk (evalExpr newVal) f) Zmod.zero.
Proof.
  intros dom depth elemK rk newVal f P.
  unfold writeElemReg, writeRegOfKind; cbn [evalActionPropGen evalExpr].
  rewrite evalExpr_eq_rect_Kind; reflexivity.
Qed.

Lemma evalActionPropGen_shiftElems :
  forall {dom depth elemK} (ps : list (RegOfKind (t := fifoTree dom depth elemK) elemK))
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@shiftElems dom depth elemK type ps) f P <->
    P (evalShiftElems ps f) Zmod.zero.
Proof.
  intros dom depth elemK ps.
  induction ps as [| rkCurr rest IH]; intros f P.
  - reflexivity.
  - destruct rest as [| rkNext rest'].
    + reflexivity.
    + change (@shiftElems dom depth elemK type (rkCurr :: rkNext :: rest'))
        with (LetAction "nextVal" (@readElemReg dom depth elemK type rkNext)
                (fun nextVal =>
                   LetAction "" (@writeElemReg dom depth elemK type rkCurr (Var type elemK nextVal))
                     (fun _ => @shiftElems dom depth elemK type (rkNext :: rest')))).
      cbn [evalActionPropGen].
      rewrite evalActionPropGen_readElemReg, evalActionPropGen_writeElemReg.
      apply IH.
Qed.

Theorem evalActionPropGen_ShiftFifo_isFull :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@isFull dom depth elemK type) f P <->
    P f (Zmod.eqb (fifo_size f)
                  (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) (Z.of_nat depth))).
Proof.
  reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_isEmpty :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@isEmpty dom depth elemK type) f P <->
    P f (Zmod.eqb (fifo_size f) Zmod.zero).
Proof.
  reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_first :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@first dom depth elemK type) f P <->
    P f (fifo_head_elem f ,, (negb (Zmod.eqb (fifo_size f) Zmod.zero) ,, tt)).
Proof.
  intros dom depth elemK f P.
  unfold first, fifo_head_elem, fifo_size.
  cbn [evalActionPropGen evalExpr].
  destruct (elemPathsWithKind dom depth elemK) as [| rk0 rest]; reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_enq :
  forall {dom depth elemK} (val : type elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@enq dom depth elemK type val) f P <->
    P (if negb (Zmod.eqb (fifo_size f)
                         (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) (Z.of_nat depth)))
       then mkFifo (fifo_enq_elems (fifo_size f) val (fifo_elems f))
                   (evalExpr (Add [Const type (Bit (Z.log2_up (Z.of_nat (depth + 1)))) (fifo_size f); $1]))
       else f) Zmod.zero.
Proof.
  intros dom depth elemK val [elems [sz []]] P.
  unfold enq, isFull, fifo_size, fifo_elems.
  cbn -[writeRegsList elemPathsWithKind].
  destruct (Zmod.eqb sz (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) (Z.of_nat depth))); cbn [negb].
  - reflexivity.
  - rewrite evalActionPropGen_writeRegsList; cbn [evalExpr].
    rewrite evalWriteRegsList_elemPathsWithKind; reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_deq :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@deq dom depth elemK type) f P <->
    P (if negb (Zmod.eqb (fifo_size f) Zmod.zero)
       then mkFifo (fifo_shift_elems (fifo_elems f))
                   (evalExpr (Sub (Const type (Bit (Z.log2_up (Z.of_nat (depth + 1)))) (fifo_size f)) $1))
       else f) Zmod.zero.
Proof.
  intros dom depth elemK [elems [sz []]] P.
  unfold deq, fifo_size, fifo_elems.
  cbn -[shiftElems elemPathsWithKind Sub].
  destruct (Zmod.eqb sz Zmod.zero); cbn [negb].
  - reflexivity.
  - rewrite evalActionPropGen_shiftElems.
    rewrite evalShiftElems_elemPathsWithKind; reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_clear :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@clear dom depth elemK type) f P <->
    P (mkFifo (fifo_elems f) (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) 0)) Zmod.zero.
Proof.
  intros dom depth elemK [elems [sz []]] P.
  reflexivity.
Qed.

(* --- Depth-1 specializations complementing `ShiftFifoLemmas.v` --- *)

Theorem evalActionPropGen_fifo_isEmpty :
  forall {dom elemK}
         (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
    evalActionPropGen (@isEmpty dom 1 elemK type) f P <->
    P f (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)).
Proof.
  reflexivity.
Qed.

Theorem evalActionPropGen_fifo_clear :
  forall {dom elemK}
         (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
    evalActionPropGen (@clear dom 1 elemK type) f P <->
    P (mkFifo1 (fifo1_elem f) (Zmod.of_Z 2 0)) Zmod.zero.
Proof.
  intros dom elemK [[e []] [sz []]] P.
  reflexivity.
Qed.


