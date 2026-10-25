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
From Cheriot Require Export SpecDefines ShiftFifo ShiftFifoLemmas ImplStaged ImplStagedProof ImplCommon.

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

(* --- Environment invariance for trees without `ERecv` leaves (`rfTree`, etc.) --- *)

Definition defaultEnv {t : Tree DomainElem} : Env t :=
  fun _ _ _ => True.

Fixpoint noRecvTree (t : Tree DomainElem) : bool :=
  match t with
  | Leaf _ de => negb (isRecvElem (snd de))
  | Node _ children =>
      (fix loop (ls : list (Tree DomainElem)) : bool :=
         match ls with
         | nil => true
         | x :: xs => andb (noRecvTree x) (loop xs)
         end) children
  end.

Lemma noRecvTree_no_isRecvElem :
  forall (t : Tree DomainElem) (lp : LeafPath t),
    noRecvTree t = true ->
    Is_true (isRecvElem (getLeafElem lp)) ->
    False.
Proof.
  fix F 1.
  intros [name de | name children] lp Hno Hpf.
  - cbn in Hno, Hpf.
    destruct (isRecvElem (snd de)); [discriminate Hno | exact Hpf].
  - cbn in Hno, lp, Hpf.
    induction children as [| x xs IH].
    + destruct lp.
    + apply andb_prop in Hno as [Hx Hxs].
      destruct lp as [lp_x | lp_xs].
      * exact (F x lp_x Hx Hpf).
      * exact (IH lp_xs Hxs Hpf).
Qed.

Lemma noRecvTree_no_RecvPath :
  forall (t : Tree DomainElem),
    noRecvTree t = true ->
    forall (x : RecvPath t), False.
Proof.
  intros t Hno [lp pf].
  exact (noRecvTree_no_isRecvElem t lp Hno pf).
Qed.

Lemma evalActionPropGen_noRecvTree_env :
  forall {t : Tree DomainElem} (env1 env2 : Env t) {k : Kind}
         (a : Action type t k) (s : TreeState DomainElemState t) P,
    noRecvTree t = true ->
    evalActionPropGen env1 a s P <-> evalActionPropGen env2 a s P.
Proof.
  intros t env1 env2 k a s P Hno.
  apply evalActionPropGen_env_ext.
  intros sub x v.
  exfalso; exact (noRecvTree_no_RecvPath t Hno x).
Qed.

Lemma SemAction_noRecvTree_env :
  forall {t : Tree DomainElem} (env1 env2 : Env t) {k : Kind}
         (a : Action type t k) (s s' : TreeState DomainElemState t) (v : type k),
    noRecvTree t = true ->
    SemAction env1 a s s' v <-> SemAction env2 a s s' v.
Proof.
  intros t env1 env2 k a s s' v Hno.
  split; apply SemAction_env_mono; intros sub x rv;
    exfalso; exact (noRecvTree_no_RecvPath t Hno x).
Qed.

Lemma evalActionPropGen_rfTree_env :
  forall {dom : string} {pcAddrInit : Z}
         (env1 env2 : Env (rfTree dom pcAddrInit)) {k : Kind}
         (a : Action type (rfTree dom pcAddrInit) k)
         (s : TreeState DomainElemState (rfTree dom pcAddrInit)) P,
    evalActionPropGen env1 a s P <-> evalActionPropGen env2 a s P.
Proof.
  intros dom pcAddrInit env1 env2 k a s P.
  exact (evalActionPropGen_noRecvTree_env env1 env2 a s P eq_refl).
Qed.

Lemma SemAction_rfTree_env :
  forall {dom : string} {pcAddrInit : Z}
         (env1 env2 : Env (rfTree dom pcAddrInit)) {k : Kind}
         (a : Action type (rfTree dom pcAddrInit) k)
         (s s' : TreeState DomainElemState (rfTree dom pcAddrInit)) (v : type k),
    SemAction env1 a s s' v <-> SemAction env2 a s s' v.
Proof.
  intros dom pcAddrInit env1 env2 k a s s' v.
  exact (SemAction_noRecvTree_env env1 env2 a s s' v eq_refl).
Qed.
