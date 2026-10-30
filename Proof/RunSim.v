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

From Stdlib Require Import List Zmod.
From Guru Require Import Primitives Library Syntax Semantics Theorems.

Import ListNotations.

(* ===========================================================================
 * RUN-LEVEL SIMULATION WITH A PER-RUN SPEC ENV AND ASSUMED IMPL STEPS
 * ===========================================================================
 * `ModSimulation env1 env2` fixes `env2` before the run. Here the spec env is
 * taken from a family `env2 : O -> Env t2` indexed by an oracle that is only
 * chosen once the impl run is known:
 * - the relation carries a prefix `p : P` of the oracle;
 * - every spec step taken so far is valid for every oracle that agrees with the
 *   current prefix, and prefixes only grow (`Ext`);
 * - at the end, any oracle that agrees with the final prefix works.
 * Impl runs may also be restricted to steps satisfying `Step` (e.g. a software
 * rule), assumed for every step taken from a state reachable from the start. *)

Section RunSim.
  Variables t1 t2 : Tree DomainElem.
  Variable env1 : Env t1.
  Variables O P : Type.
  Variable env2 : O -> Env t2.
  Variable Agrees : P -> O -> Prop.
  Variable Ext : P -> P -> Prop.

  Hypothesis Ext_refl : forall p, Ext p p.
  Hypothesis Ext_trans : forall p1 p2 p3, Ext p1 p2 -> Ext p2 p3 -> Ext p1 p3.
  Hypothesis Agrees_Ext : forall p p' o, Ext p p' -> Agrees p' o -> Agrees p o.

  Variable ls1 : list (Action type t1 (Bit 0)).
  Variable ls2 : list (Action type t2 (Bit 0)).
  Variable R : P -> TreeState DomainElemState t1 -> TreeState DomainElemState t2 -> Prop.
  Variable Step : TreeState DomainElemState t1 -> TreeState DomainElemState t1 -> Prop.

  (* Per-action obligation: one impl step is matched by spec steps that are valid
   * for every oracle agreeing with the (possibly extended) prefix. *)
  Definition StepSim : Prop :=
    forall p s1 s1' s2 a,
      In a ls1 ->
      SemAction env1 a s1 s1' Zmod.zero ->
      Step s1 s1' ->
      R p s1 s2 ->
      exists p' s2',
        Ext p p' /\
        (forall o, Agrees p' o -> SemActions (env2 o) ls2 s2 s2') /\
        R p' s1' s2'.

  Lemma SemActions_snoc :
    forall (env : Env t1) (ls : list (Action type t1 (Bit 0))) old s s' a,
      SemActions env ls old s ->
      In a ls ->
      SemAction env a s s' Zmod.zero ->
      SemActions env ls old s'.
  Proof.
    intros env ls old s s' a Hrun Hin Ha.
    eapply SemActions_trans; [exact Hrun |].
    econstructor 2; [exact Hin | exact Ha | constructor 1; reflexivity].
  Qed.

  Lemma SemActions_refl :
    forall (env : Env t2) (ls : list (Action type t2 (Bit 0))) s,
      SemActions env ls s s.
  Proof.
    intros env ls s; constructor 1; reflexivity.
  Qed.

  Theorem run_sim :
    StepSim ->
    forall old1 new1,
      SemActions env1 ls1 old1 new1 ->
      (forall s s' a,
         SemActions env1 ls1 old1 s ->
         In a ls1 ->
         SemAction env1 a s s' Zmod.zero ->
         Step s s') ->
      forall p old2,
        R p old1 old2 ->
        exists p' new2,
          Ext p p' /\
          (forall o, Agrees p' o -> SemActions (env2 o) ls2 old2 new2) /\
          R p' new1 new2.
  Proof.
    intros Hsim old1 new1 Hrun Hstep p old2 Hrel.
    (* Generalize over the reachable prefix `old1 ->* s` and the rest `s ->* new1`. *)
    assert (Hgen :
      forall s s_end,
        SemActions env1 ls1 s s_end ->
        SemActions env1 ls1 old1 s ->
        forall q s2,
          Ext p q ->
          (forall o, Agrees q o -> SemActions (env2 o) ls2 old2 s2) ->
          R q s s2 ->
          exists p' new2,
            Ext p p' /\
            (forall o, Agrees p' o -> SemActions (env2 o) ls2 old2 new2) /\
            R p' s_end new2).
    { intros s s_end Hrest.
      induction Hrest as [s s_end Heq | s s_end mid a Hin Ha Hrest IH];
        intros Hpre q s2 Hpq Hval Hr.
      - subst s_end; exists q, s2; split; [exact Hpq | split; [exact Hval | exact Hr]].
      - destruct (Hsim q s mid s2 a Hin Ha (Hstep s mid a Hpre Hin Ha) Hr)
          as [q' [s2' [Hqq' [Hval' Hr']]]].
        apply (IH (SemActions_snoc env1 ls1 old1 s mid a Hpre Hin Ha) q' s2').
        + exact (Ext_trans p q q' Hpq Hqq').
        + intros o Hag.
          eapply SemActions_trans.
          * exact (Hval o (Agrees_Ext q q' o Hqq' Hag)).
          * exact (Hval' o Hag).
        + exact Hr'. }
    assert (Hnil : SemActions env1 ls1 old1 old1) by (constructor 1; reflexivity).
    apply (Hgen old1 new1 Hrun Hnil p old2 (Ext_refl p)).
    - intros o _; apply SemActions_refl.
    - exact Hrel.
  Qed.
End RunSim.
