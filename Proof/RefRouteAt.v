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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot Require Import SpecDefines SpecDevice.
From Cheriot.Proof Require Import RefRegion RefCoreRel RefSpecRead.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the router (`genRouteRegionActionAux`) on any region tree: a line held by no
 * region leaves every region alone (`route_none_or`, `route_none_unit`); a line held by the region
 * at position `j` (unique by `lineUnique`) runs the region's action there and nowhere else
 * (`route_at_or`, `route_at_unit`). *)

Section RouteAt.
  Variable rt : MemRegion -> Tree Elem.

  Lemma lineKind_some_nth :
    forall L l j r, nth_error l j = Some r -> isRegionAddrB r L = true -> lineKind l L <> None.
  Proof.
    intros L l; induction l as [| r0 rs IH]; intros [| j'] r pf Hm; try discriminate pf; cbn [lineKind].
    - cbn [nth_error] in pf; injection pf as ->; rewrite Hm; discriminate.
    - destruct (isRegionAddrB r0 L); [discriminate | exact (IH j' r pf Hm)].
  Qed.

  Lemma evalActionPropGen_post_iff :
    forall t k (env : Env t) (a : Action type t k) s (Q1 Q2 : TS t -> type k -> Prop),
      (forall s' v, Q1 s' v <-> Q2 s' v) ->
      evalActionPropGen env a s Q1 <-> evalActionPropGen env a s Q2.
  Proof.
    intros t k env a s Q1 Q2 H; split; apply evalActionPropGen_mono; intros s' v; apply H.
  Qed.

  Lemma route_none_or :
    forall k (getAction : forall r, Action type (rt r) k) L l acc (env : Env (regionsTree rt l)) ms P,
      lineKind l L = None ->
      evalActionPropGen env (genRouteRegionActionAux rt getAction (@Or type k) L acc l) ms P <->
      P ms (fold_left (@evalOrBinary k) (map (@evalExpr _) (rev acc)) (getDefault k)).
  Proof.
    intros k getAction L l; induction l as [| r rs IH]; intros acc env ms P Hk.
    - cbn [genRouteRegionActionAux evalActionPropGen].
      rewrite rev_tail_rev, app_nil_r; reflexivity.
    - cbn [lineKind] in Hk.
      destruct (isRegionAddrB r L) eqn:Em; [discriminate Hk |].
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      rewrite Em.
      rewrite evalActionPropGen_liftAction.
      etransitivity; [apply IH; exact Hk |].
      destruct ms as [m0 [m1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
      cbn [rev map]; rewrite map_app; cbn [map].
      rewrite fold_left_app; cbn [fold_left].
      change (evalExpr (Var type k (evalExpr (Const type k (getDefault k))))) with (getDefault k).
      rewrite evalOrBinary_getDefault_r; reflexivity.
  Qed.

  Lemma route_at_or :
    forall k (getAction : forall r, Action type (rt r) k) L l j r (pf : nth_error l j = Some r) acc
           (env : Env (regionsTree rt l)) ms P,
      isRegionAddrB r L = true -> lineUnique l L ->
      Forall (fun e => evalExpr e = getDefault k) acc ->
      evalActionPropGen env (genRouteRegionActionAux rt getAction (@Or type k) L acc l) ms P <->
      evalActionPropGen (envRegionAt rt j l r pf env ms) (getAction r) (regionStateAt rt j l r pf ms)
        (fun x v => P (updRegionStateAt rt j l r pf ms x) v).
  Proof.
    intros k getAction L l; induction l as [| r1 rs IH]; intros [| j'] r pf acc env ms P Hm Hu Hacc;
      try discriminate pf.
    - cbn [regionStateAt updRegionStateAt envRegionAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r1 | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      cbn [lineUnique] in Hu; rewrite Hm in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      rewrite Hm; cbv beta iota.
      destruct ms as [m0 [m1 []]].
      rewrite evalActionPropGen_liftAction.
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd].
      apply evalActionPropGen_post_iff.
      intros x v; cbv beta.
      cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
      rewrite evalActionPropGen_liftAction.
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
      etransitivity; [apply route_none_or; exact Hu |].
      cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd].
      cbn [rev map]; rewrite map_app; cbn [map].
      rewrite fold_left_app; cbn [fold_left].
      rewrite (fold_left_evalOrBinary_default (map (@evalExpr _) (rev acc)) _)
        by (apply Forall_map; apply Forall_rev; exact Hacc).
      change (evalExpr (Var type k v)) with v.
      rewrite evalOrBinary_getDefault_l; reflexivity.
    - cbn [regionStateAt updRegionStateAt envRegionAt].
      cbn [lineUnique] in Hu.
      assert (Hm1 : isRegionAddrB r1 L = false).
      { destruct (isRegionAddrB r1 L) eqn:E; [| reflexivity].
        exfalso; exact (lineKind_some_nth L rs j' r pf Hm Hu). }
      rewrite Hm1 in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r1 (Var type Addr L))))) with (isRegionAddrB r1 L).
      rewrite Hm1.
      rewrite evalActionPropGen_liftAction.
      destruct ms as [m0 [m1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
      rewrite (IH j' r pf) by first [exact Hm | exact Hu | constructor; [reflexivity | exact Hacc]].
      reflexivity.
  Qed.

  Lemma route_none_unit :
    forall (getAction : forall r, Action type (rt r) (Bit 0)) c L l acc (env : Env (regionsTree rt l)) ms P,
      lineKind l L = None -> (forall w, P ms w) ->
      evalActionPropGen env (genRouteRegionActionAux rt getAction c L acc l) ms P.
  Proof.
    intros getAction c L l; induction l as [| r rs IH]; intros acc env ms P Hk HP.
    - cbn [genRouteRegionActionAux evalActionPropGen]; apply HP.
    - cbn [lineKind] in Hk.
      destruct (isRegionAddrB r L) eqn:Em; [discriminate Hk |].
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      rewrite Em.
      rewrite evalActionPropGen_liftAction.
      apply IH; [exact Hk |].
      intros w; destruct ms as [m0 [m1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
      apply HP.
  Qed.

  Lemma route_at_unit :
    forall (getAction : forall r, Action type (rt r) (Bit 0)) c L l j r (pf : nth_error l j = Some r) acc
           (env : Env (regionsTree rt l)) ms P,
      isRegionAddrB r L = true -> lineUnique l L ->
      evalActionPropGen (envRegionAt rt j l r pf env ms) (getAction r) (regionStateAt rt j l r pf ms)
        (fun x _ => forall w, P (updRegionStateAt rt j l r pf ms x) w) ->
      evalActionPropGen env (genRouteRegionActionAux rt getAction c L acc l) ms P.
  Proof.
    intros getAction c L l; induction l as [| r1 rs IH]; intros [| j'] r pf acc env ms P Hm Hu H;
      try discriminate pf.
    - cbn [regionStateAt updRegionStateAt envRegionAt] in H.
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r1 | None => False end
                  with eq_refl => eq_refl end) in H.
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota in H.
      cbn [lineUnique] in Hu; rewrite Hm in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      rewrite Hm; cbv beta iota.
      destruct ms as [m0 [m1 []]].
      rewrite evalActionPropGen_liftAction.
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H |- *.
      eapply evalActionPropGen_mono; [| exact H].
      intros x v Hx; cbv beta in Hx |- *.
      cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
      rewrite evalActionPropGen_liftAction.
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
      apply route_none_unit; [exact Hu |].
      intros w; cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd].
      apply Hx.
    - cbn [regionStateAt updRegionStateAt envRegionAt] in H.
      cbn [lineUnique] in Hu.
      assert (Hm1 : isRegionAddrB r1 L = false).
      { destruct (isRegionAddrB r1 L) eqn:E; [| reflexivity].
        exfalso; exact (lineKind_some_nth L rs j' r pf Hm Hu). }
      rewrite Hm1 in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r1 (Var type Addr L))))) with (isRegionAddrB r1 L).
      rewrite Hm1.
      rewrite evalActionPropGen_liftAction.
      destruct ms as [m0 [m1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H |- *.
      apply (IH j' r pf); [exact Hm | exact Hu |].
      eapply evalActionPropGen_mono; [| exact H].
      intros x v Hx; exact Hx.
  Qed.
End RouteAt.
