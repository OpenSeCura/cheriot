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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic Spec.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute.
From Cheriot.Proof Require Import RefRel RefRegion RefMemRel RefCoreRel RefFrame RefPeriph FifoGen.
From Cheriot.Proof Require Import RefSpecRead RefRouteAt RefRqStepChar RefSpecFetch RefExecImpl.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 6, the regions' side of a fetch request (`implRegionsFetchLineReadRq`): the ExternalMem
 * region holding the line logs the line and the ready it received (`fetchRqUpd`); a CustomMem
 * region or no region answers ready at once and changes nothing (`FetchRqAtL`). *)

Section FetchRqRegions.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  Definition fetchRqUpd r (y : ExtI r) (L : type Addr) (rdy : bool) : ExtI r :=
    ((((L :: y.(Fst).(Fst).(Fst)) ,, y.(Fst).(Fst).(Snd)) ,, y.(Fst).(Snd)) ,,
     (((rdy :: y.(Snd).(Fst).(Fst)) ,, y.(Snd).(Fst).(Snd)) ,, y.(Snd).(Snd))).

  Definition RegionFetchRqI (r : MemRegion) (A : type Addr) (rdy : bool)
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y y' => y' = fetchRqUpd r y (lineAddrOf A) rdy
    | CustomMem _ _ _ _ => fun y y' => y' = y /\ rdy = true
    end.

  (* The region holding the line at `A` took the request; the others are unchanged *)
  Fixpoint FetchRqAtL (A : type Addr) (rdy : bool) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> Prop with
    | [] => fun mi mi' => mi' = mi
    | r :: rs => fun mi mi' =>
        if isRegionAddrB r A then RegionFetchRqI r A rdy mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)
        else mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\ FetchRqAtL A rdy rs mi.(Snd).(Fst) mi'.(Snd).(Fst)
    end.

  Lemma region_fetchRq :
    forall A r env (y : TS (implMemRegionTree r)) Q,
      evalActionPropGen env (@implMemRegionFetchLineReadRq r type A) y Q ->
      exists y' rdy, RegionFetchRqI r A rdy y y' /\ Q y' rdy.
  Proof.
    intros A r; unfold RegionFetchRqI, implMemRegionFetchLineReadRq, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q H.
    - unfold implExternalFetchLineReadRq, externalFetchLineReadRq in H.
      cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      cbn [evalActionPropGen] in H.
      destruct H as [rdy [_ H]].
      eexists _, rdy; split; [| exact H].
      reflexivity.
    - cbn [evalActionPropGen] in H.
      exists y, true; split; [split; reflexivity | exact H].
  Qed.

  Lemma route_fetchRq :
    forall A l acc (env : Env (implRegionsTree l)) mi Q,
      lineUnique l A -> Forall (fun e => evalExpr e = getDefault Bool) acc ->
      evalActionPropGen env (genRouteRegionActionAux implMemRegionTree
                               (fun r => @implMemRegionFetchLineReadRq r type A) (@Or type Bool) A acc l) mi Q ->
      exists mi' v, FetchRqAtL A v l mi mi' /\ Q mi' (match lineKind l A with Some _ => v | None => false end).
  Proof.
    intros A l; induction l as [| r rs IH]; intros acc env mi Q Hu Hacc H.
    - cbn [genRouteRegionActionAux evalActionPropGen] in H.
      exists mi, false; split; [reflexivity |]; cbn [lineKind].
      rewrite rev_tail_rev, app_nil_r in H; cbn [evalExpr] in H.
      rewrite (fold_left_evalOrBinary_default (map (@evalExpr _) (rev acc)) _) in H
        by (apply Forall_map; apply Forall_rev; exact Hacc).
      exact H.
    - cbn [lineUnique] in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen] in H.
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr A))))) with (isRegionAddrB r A) in H.
      destruct mi as [m0 [m1 []]].
      cbn [FetchRqAtL lineKind].
      destruct (isRegionAddrB r A) eqn:Em.
      + rewrite evalActionPropGen_liftAction in H.
        cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        destruct (region_fetchRq A r _ m0 _ H) as [y' [v [Hs H']]].
        cbv beta in H'.
        cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd] in H'.
        rewrite evalActionPropGen_liftAction in H'.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H'.
        apply (proj1 (route_none_or implMemRegionTree _ _ _ _ _ _ _ _ Hu)) in H'.
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H'.
        exists (y' ,, (m1 ,, tt)), v; split; [split; [exact Hs | reflexivity] |].
        cbn [rev map] in H'; rewrite map_app in H'; cbn [map] in H'.
        rewrite fold_left_app in H'; cbn [fold_left] in H'.
        rewrite (fold_left_evalOrBinary_default (map (@evalExpr _) (rev acc)) _) in H'
          by (apply Forall_map; apply Forall_rev; exact Hacc).
        change (evalExpr (Var type Bool v)) with v in H'.
        rewrite evalOrBinary_getDefault_l in H'; exact H'.
      + rewrite evalActionPropGen_liftAction in H.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        destruct (IH _ _ _ _ Hu (Forall_cons (Var type Bool (evalExpr ConstDef)) eq_refl Hacc) H) as [m1' [v [Hs H']]].
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H'.
        exists (m0 ,, (m1' ,, tt)), v; split; [| exact H'].
        cbn [Fst Snd]; split; [reflexivity | split; [reflexivity | exact Hs]].
  Qed.

  Lemma FetchRqAtL_none_irrel :
    forall A v v' l mi mi', lineKind l A = None -> FetchRqAtL A v l mi mi' -> FetchRqAtL A v' l mi mi'.
  Proof.
    intros A v v'; induction l as [| r rs IH]; intros mi mi' Hk H; cbn [FetchRqAtL lineKind] in *; [exact H |].
    destruct (isRegionAddrB r A); [discriminate Hk |].
    destruct H as [H0 [H1 H2]]; exact (conj H0 (conj H1 (IH _ _ Hk H2))).
  Qed.

  Lemma FetchRqAtL_custom :
    forall A v l mi mi', lineKind l A = Some false -> FetchRqAtL A v l mi mi' -> v = true.
  Proof.
    intros A v; induction l as [| r rs IH]; intros mi mi' Hk H; cbn [FetchRqAtL lineKind] in *; [discriminate Hk |].
    destruct (isRegionAddrB r A).
    - destruct H as [H _]; revert Hk H; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionFetchRqI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hk H;
        [discriminate Hk | exact (proj2 H)].
    - destruct H as [_ [_ H]]; exact (IH _ _ Hk H).
  Qed.

  (* The routed fetch request: the region holding the line at `A` took it; the ready is true unless
   * that region is an ExternalMem one *)
  Lemma regionsFetchRq_char :
    forall l env (mi mi' : TS (implRegionsTree l)) rdy (A : type Addr),
      lineUnique l A ->
      SemAction env (@implRegionsFetchLineReadRq type l A) mi mi' rdy ->
      FetchRqAtL A rdy l mi mi' /\ (lineKind l A <> Some true -> rdy = true).
  Proof.
    intros l env mi mi' rdy A Hu H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsFetchLineReadRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    destruct (route_fetchRq A l [] _ mi _ Hu (Forall_nil _) H) as [mi'' [v [Hs [E1 E2]]]].
    subst mi'' rdy.
    cbn [evalExpr map fold_left].
    rewrite isMapped_eval.
    destruct (lineKind l A) as [[|]|] eqn:Ek.
    - split; [| intros C; exfalso; exact (C eq_refl)].
      change (evalExpr (Var type Bool v)) with v; destruct v; exact Hs.
    - pose proof (FetchRqAtL_custom A v l mi mi' Ek Hs) as ->.
      split; [exact Hs | intros _; reflexivity].
    - split; [| intros _; reflexivity].
      exact (FetchRqAtL_none_irrel A v _ l mi mi' Ek Hs).
  Qed.
End FetchRqRegions.

Section FetchRqFrames.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  Lemma FetchRqAtL_none :
    forall A v l mi mi', lineKind l A = None -> FetchRqAtL A v l mi mi' -> mi' = mi.
  Proof.
    intros A v; induction l as [| r rs IH]; intros mi mi' Hk H; cbn [FetchRqAtL lineKind] in *; [exact H |].
    destruct (isRegionAddrB r A); [discriminate Hk |].
    destruct H as [H0 [H1 H2]].
    apply prod_ext; [exact H0 |]; apply prod_ext; [exact (IH _ _ Hk H2) | exact H1].
  Qed.

  (* Port predicates that ignore the fetch requests and their readies are kept *)
  Lemma AllPorts_fetchRqAt :
    forall (P : forall r, ExtI r -> Prop), (forall r y L rdy, P r (fetchRqUpd r y L rdy) = P r y) ->
      forall A v l mi mi', FetchRqAtL A v l mi mi' -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP A v; induction l as [| r rs IH]; intros mi mi' Hw; cbn [FetchRqAtL] in Hw; [rewrite Hw; reflexivity |].
    cbn [AllPorts].
    destruct (isRegionAddrB r A).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; f_equal.
      revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionFetchRqI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hw0;
        [subst y'; apply HP | reflexivity].
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf, (IH _ _ Hrest); reflexivity.
  Qed.

  Lemma AllPorts_none_impl :
    forall (P P' : forall r, ExtI r -> Prop) A,
      (forall r y, isRegionAddrB r A = false -> P r y -> P' r y) ->
      forall l mi, lineKind l A = None -> AllPorts P l mi -> AllPorts P' l mi.
  Proof.
    intros P P' A Hn; induction l as [| r rs IH]; intros mi Hk H; [exact I |].
    cbn [lineKind] in Hk; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct (isRegionAddrB r A) eqn:Em; [discriminate Hk |].
    split; [| exact (IH _ Hk H1)].
    revert H0; generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
    exact (Hn _ y Em H0).
  Qed.

  (* A port predicate moved across the request: the holding region against its update, the others
   * as they are *)
  Lemma AllPorts_fetchRqAt_impl :
    forall (P P' : forall r, ExtI r -> Prop) A v,
      (forall r y, isRegionAddrB r A = true -> P r y -> P' r (fetchRqUpd r y (lineAddrOf A) v)) ->
      (forall r y, isRegionAddrB r A = false -> P r y -> P' r y) ->
      forall l mi mi', lineUnique l A -> FetchRqAtL A v l mi mi' -> AllPorts P l mi -> AllPorts P' l mi'.
  Proof.
    intros P P' A v Ht Hn; induction l as [| r rs IH]; intros mi mi' Hu Hw H; [exact I |].
    cbn [lineUnique] in Hu; cbn [FetchRqAtL] in Hw; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct (isRegionAddrB r A) eqn:Em.
    - destruct Hw as [Hw0 Hs]; rewrite Hs; split; [| exact (AllPorts_none_impl P P' A Hn rs _ Hu H1)].
      revert H0 Hw0; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, RegionFetchRqI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hw0; [| exact I].
      subst y'; exact (Ht _ y Em H0).
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf; split; [| exact (IH _ _ Hu Hrest H1)].
      revert H0; generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
      exact (Hn _ y Em H0).
  Qed.

  (* Device (CustomMem) positions are untouched *)
  Lemma regionStateAt_fetchRqAt :
    forall A v l j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree l)),
      FetchRqAtL A v l mi mi' -> isCustomR r0 ->
      regionStateAt implMemRegionTree j l r0 pf mi' = regionStateAt implMemRegionTree j l r0 pf mi.
  Proof.
    intros A v; induction l as [| r rs IH]; intros [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [FetchRqAtL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct (isRegionAddrB r0 A); [| destruct H as [Hf _]; rewrite Hf; reflexivity].
      destruct H as [Hw0 _]; revert Hw0; generalize (mi'.(Fst)) (mi.(Fst));
        unfold RegionFetchRqI, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact (proj1 Hy)].
    - cbn [regionStateAt].
      destruct (isRegionAddrB r A).
      + destruct H as [_ Hs]; rewrite Hs; reflexivity.
      + destruct H as [_ [_ Hrest]]; exact (IH j' r0 pf _ _ Hrest Hc).
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_fetchRqAt :
    forall i r x (y y' : TS (implMemRegionTree r)) A v,
      RegionFetchRqI r A v y y' -> RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r x y'.
  Proof.
    intros i r x y y' A v; unfold RegionRelAt, RegionFetchRqI, implMemRegionTree, memRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros Hs Hr.
    - subst y'; exact Hr.
    - destruct Hs as [-> _]; exact Hr.
  Qed.

  Lemma MemRelPost_fetchRqAt :
    forall A v l i ms mi mi', FetchRqAtL A v l mi mi' -> MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l ms mi'.
  Proof.
    intros A v; induction l as [| r rs IH]; intros i ms mi mi' Hw H; [exact I |].
    cbn [FetchRqAtL] in Hw; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct (isRegionAddrB r A).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; exact (conj (RegionRelAt_fetchRqAt _ _ _ _ _ _ _ Hw0 Hr) Hl).
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf; exact (conj Hr (IH _ _ _ _ Hrest Hl)).
  Qed.

  Lemma MemRelPre_fetchRqAt :
    forall A v sRev iRev post l i ms mi mi',
      FetchRqAtL A v (l ++ iRev :: post) mi mi' -> MemRelPre cp pp i l sRev iRev post ms mi ->
      MemRelPre cp pp i l sRev iRev post ms mi'.
  Proof.
    intros A v sRev iRev post; induction l as [| r rs IH]; intros i ms mi mi' Hw H.
    - cbn [app FetchRqAtL] in Hw; cbn [MemRelPre] in H |- *.
      destruct (isRegionAddrB iRev A).
      + destruct Hw as [_ Ht]; rewrite Ht; exact H.
      + destruct Hw as [_ [_ Hrest]]; exact (MemRelPost_fetchRqAt _ _ _ _ _ _ _ Hrest H).
    - cbn [app FetchRqAtL] in Hw; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct (isRegionAddrB r A).
      + destruct Hw as [Hw0 Ht]; rewrite Ht; exact (conj (RegionRelAt_fetchRqAt _ _ _ _ _ _ _ Hw0 Hr) Hl).
      + destruct Hw as [Hf [_ Hrest]]; rewrite Hf; exact (conj Hr (IH _ _ _ _ Hrest Hl)).
  Qed.
End FetchRqFrames.

(* --- The fence.i Wait Flags the Stage Reads --- *)

Definition regionWait (r : MemRegion) : TS (implMemRegionTree r) -> bool :=
  match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> bool with
  | ExternalMem => fun y => y.(Fst).(Fst).(Snd).(Snd).(Fst)
  | CustomMem _ _ _ _ => fun _ => false
  end.

Fixpoint anyWait (l : list MemRegion) : TS (implRegionsTree l) -> bool :=
  match l as l0 return TS (implRegionsTree l0) -> bool with
  | [] => fun _ => false
  | r :: rs => fun mi => orb (regionWait r mi.(Fst)) (anyWait rs mi.(Snd).(Fst))
  end.

Lemma region_readFenceIWait :
  forall r env (y : TS (implMemRegionTree r)) Q,
    evalActionPropGen env (@liftToImplRegion type r Bool (memRegionReadFenceIWait r)) y Q -> Q y (regionWait r y).
Proof.
  intros r; unfold liftToImplRegion, regionWait, memRegionReadFenceIWait, implMemRegionTree, memRegionTree.
  destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q H.
  - unfold externalReadFenceIWait in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    cbn [evalActionPropGen] in H.
    rewrite !writeSubTreeState_readSubTreeState in H; exact H.
  - apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H; cbn [evalActionPropGen] in H.
    rewrite writeSubTreeState_readSubTreeState in H; exact H.
Qed.

Lemma fold_readFenceIWait :
  forall l acc (env : Env (implRegionsTree l)) mi P,
    evalActionPropGen env (genFoldRegionActionsAux implMemRegionTree
                             (fun r => @liftToImplRegion type r Bool (memRegionReadFenceIWait r)) (@Or type Bool) acc l) mi P ->
    P mi (orb (fold_left (@evalOrBinary Bool) (map (@evalExpr _) (rev acc)) (getDefault Bool)) (anyWait l mi)).
Proof.
  intros l; induction l as [| r rs IH]; intros acc env mi P H.
  - cbn [genFoldRegionActionsAux evalActionPropGen] in H.
    rewrite rev_tail_rev, app_nil_r in H; cbn [evalExpr] in H.
    cbn [anyWait]; rewrite orb_false_r; exact H.
  - cbn [genFoldRegionActionsAux evalActionPropGen] in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    destruct mi as [m0 [m1 []]].
    cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H.
    apply region_readFenceIWait in H; cbv beta in H.
    cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd] in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
    apply IH in H.
    cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H.
    cbn [anyWait Fst Snd].
    cbn [rev map] in H; rewrite map_app, fold_left_app in H; cbn [map fold_left] in H.
    assert (Eo : forall x w a : bool, (@evalOrBinary Bool x w || a)%bool = (x || (w || a))%bool)
      by (intros [|] [|] [|]; reflexivity).
    rewrite Eo in H; exact H.
Qed.

Lemma memReadFenceIWait_read :
  forall l env' (sub : TS (implMemTree l)) Q,
    evalActionPropGen env' (liftAction child0Path (@implRegionsReadFenceIWait type l)) sub Q ->
    Q sub (anyWait l sub.(Fst)).
Proof.
  intros l env' sub Q H.
  apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
  unfold implRegionsReadFenceIWait, genFoldRegionActions in H.
  apply fold_readFenceIWait in H.
  exact H.
Qed.

Lemma anyWait_false :
  forall l mi, anyWait l mi = false -> AllPorts (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) l mi.
Proof.
  intros l; induction l as [| r rs IH]; intros mi H; [exact I |].
  cbn [anyWait] in H; cbn [AllPorts]; apply orb_false_iff in H as [H0 H1].
  split; [| exact (IH _ H1)].
  revert H0; generalize (mi.(Fst)); unfold RegionPort, regionWait, implMemRegionTree.
  destruct (regionKind r); intros y H0; [exact H0 | exact I].
Qed.

(* --- Boolean Tests of the Stage --- *)

Lemma notVar_eval : forall b, evalExpr (Not (Var type Bool b)) = negb b.
Proof. reflexivity. Qed.

Lemma and3_eval :
  forall a b c : bool,
    evalExpr (And [Not (Var type Bool a); Not (Var type Bool b); Not (Var type Bool c)]) =
    andb (negb a) (andb (negb b) (negb c)).
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma or4_excAny :
  forall a b c d : bool,
    evalExpr (Or [Var type Bool a; Var type Bool b; Var type Bool c; Var type Bool d]) =
    excAny ((a ,, (b ,, (c ,, (d ,, tt)))) : type FetchException).
Proof. intros [|] [|] [|] [|]; reflexivity. Qed.

Lemma and3_true :
  forall a b c : bool, a = false -> b = false -> c = false ->
    evalExpr (And [Not (Var type Bool a); Not (Var type Bool b); Not (Var type Bool c)]) = true.
Proof. intros a b c -> -> ->; reflexivity. Qed.

Lemma var_bool : forall b c : bool, b = c -> evalExpr (Var type Bool b) = c.
Proof. intros b c ->; reflexivity. Qed.

(* Bit 0 cleared *)
Definition clearBit0 (a : type Addr) : type Addr :=
  evalExpr ({< TruncMsb (AddrSz - 1) 1 (Var type Addr a), Const type (Bit 1) Zmod.zero >}).

(* --- The Stage's Step --- *)

Section FetchRqImpl.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable envI : Env (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STAGE :=
    (@fetchRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

  Local Abbreviation ACC f := (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA := (ACC iRf).
  Local Abbreviation iWbA := (ACC iWb).
  Local Abbreviation iMemA := (ACC iMem).
  Local Abbreviation iFetchA := (ACC iFetch).
  Local Abbreviation iDecodeA := (ACC iDecode).
  Local Abbreviation iExecA := (ACC iExec).
  Local Abbreviation iDmA := (ACC iDm).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iRegionsA := (ACC iRegions).
  Local Abbreviation iFetchPcA := (ACC iFetchPc).
  Local Abbreviation iPredEpochA := (ACC iPredEpoch).
  Local Abbreviation iExecEpochA := (ACC iExecEpoch).
  Local Abbreviation iFenceIPendingA := (ACC iFenceIPending).
  Local Abbreviation iPccA := (ACC iPcc).
  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* What the stage reads and computes *)
  Definition frFull (s1 : IState) : bool := Zmod.eqb (fifo_size (FBF s1)) (Zmod.of_Z _ (Z.of_nat fetchCapacity)).
  (* fetch's PCC copy and fence.i copy (item 3.4) *)
  Definition frPcc (s1 : IState) : type FullECapWithTag := fetch_pccCopy pcAddrInit fetchCapacity instCapacity (iFetchA s1).
  Definition frFip (s1 : IState) : bool := fetch_fipCopy pcAddrInit fetchCapacity instCapacity (iFetchA s1).
  Definition frExc (s1 : IState) : type FetchException := preExcAt (frPcc s1) (iFetchPcA s1).
  Definition frEntry (s1 : IState) (nio : type NoInstPredOut) : type FetchBufEntry :=
    (iFetchPcA s1 ,, (clearBit0 nio.(Snd).(Fst) ,, (nio.(Fst) ,, (iExecEpochA s1 ,, (iPredEpochA s1 ,, (frExc s1 ,, tt)))))).
  Definition frNoPred (s1 : IState) : type NoInstPredOut :=
    (evalExpr (Const type (Bit LgFetchParcels) (InvDefault _)) ,, (iFetchPcA s1 ,, tt)).
  Definition frEnqF (s1 : IState) (e : type FetchBufEntry) :=
    fetch_withPc pcAddrInit fetchCapacity instCapacity
      (fetch_withFetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) (fifoEnqState (FBF s1) e))
      (fbPredPc e).

  (* The step changed memory to `m` and fetch to `f` (and possibly the branch predictor) *)
  Definition FrqStep (s1 s1' : IState) m f : Prop :=
    iRfA s1' = iRfA s1 /\ iWbA s1' = iWbA s1 /\ iMemA s1' = m /\ iFetchA s1' = f /\
    iDecodeA s1' = iDecodeA s1 /\ iExecA s1' = iExecA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1.

  Ltac frq_open H :=
    rewrite SemAction_iff_evalActionPropGen in H;
    unfold fetchRqStage in H;
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H;
    unfold fetchRq in H;
    cbn [execute_readFenceIPend execute_readExecEpoch implExecuteIfc mem_readFenceIWait mem_readInstRq implMemIfc] in H.
  Ltac frq_full H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_isFull_raw fetchCapacity FetchBufEntry _ _ _) HQ_)];
    cbv beta in H.
  Ltac frq_fip H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readFetchFenceIPending pcAddrInit fetchCapacity instCapacity _ _) HQ_)];
    cbv beta in H.
  Ltac frq_wait H :=
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (memReadFenceIWait_read _ _ _ _ HQ_)]; cbv beta in H.
  Ltac frq_pc H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readFetchPc pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; cbv beta in H.
  Ltac frq_epoch H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecEpoch _ _) HQ_)]; cbv beta in H.
  Ltac frq_pe H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readPredEpoch pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; cbv beta in H.
  Ltac frq_pcc H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readFetchPcc pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; cbv beta in H.
  Ltac frq_lets H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (LetExp _ _ _) _ _ => apply fw_letExp in H
            end; cbv beta in H).
  Ltac frq_ret H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (Return _) _ _ => apply fw_return in H
            | evalActionPropGen _ (LetAction _ _ _) _ _ => apply fw_letAction in H
            end; cbv beta in H).
  Ltac frq_prefix H :=
    frq_open H; frq_full H; frq_fip H; frq_wait H; frq_pc H; frq_epoch H; frq_pe H; frq_pcc H; frq_lets H.
  Ltac frq_enq H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_enq_iff fetchCapacity FetchBufEntry _ _ _ _) HQ_)];
    cbv beta in H.
  Ltac frq_wrPc H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_writeFetchPc pcAddrInit fetchCapacity instCapacity _ _ _) HQ_)]; cbv beta in H.

  Lemma fetchRq_idle :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      andb (negb (frFull s1)) (andb (negb (frFip s1)) (negb (anyWait implRegions (iRegionsA s1)))) = false ->
      s1' = s1.
  Proof.
    intros s1 s1' H Hc.
    frq_prefix H.
    apply fw_ifFalse in H; [| rewrite and3_eval; exact Hc].
    frq_ret H.
    destruct H as [<- _]; reflexivity.
  Qed.

  Lemma fetchRq_pre :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      frFull s1 = false -> frFip s1 = false -> anyWait implRegions (iRegionsA s1) = false ->
      excAny (frExc s1) = true ->
      FrqStep s1 s1' (iMemA s1) (frEnqF s1 (frEntry s1 (frNoPred s1))).
  Proof.
    intros s1 s1' H Hf Hfip Hw Hpre.
    frq_prefix H.
    apply fw_ifTrue in H; [| apply and3_true; [exact Hf | exact Hfip | exact Hw]].
    apply fw_ifTrue in H; [| apply var_bool; rewrite or4_excAny; exact Hpre].
    apply fw_return in H; cbv beta in H.
    apply fw_ifTrue in H; [| reflexivity].
    frq_lets H.
    apply fw_ifFalse in H; [| rewrite notVar_eval, or4_excAny; apply negb_false_iff; exact Hpre].
    apply fw_return in H; cbv beta in H.
    frq_lets H. frq_enq H. frq_wrPc H. frq_ret H.
    destruct H as [<- _]; unfold FrqStep; repeat split; reflexivity.
  Qed.

  Lemma fetchRq_noPre :
    forall (s1 s1' : IState),
      (forall A, lineUnique implRegions A) ->
      SemAction envI STAGE s1 s1' Zmod.zero ->
      frFull s1 = false -> frFip s1 = false -> anyWait implRegions (iRegionsA s1) = false ->
      excAny (frExc s1) = false ->
      exists mr' rdy,
        FetchRqAtL (lineAddrOf (iFetchPcA s1)) rdy implRegions (iRegionsA s1) mr' /\
        (lineKind implRegions (lineAddrOf (iFetchPcA s1)) <> Some true -> rdy = true) /\
        (if rdy then exists nio, FrqStep s1 s1' (mr' ,, (iMemA s1).(Snd)) (frEnqF s1 (frEntry s1 nio))
         else FrqStep s1 s1' (mr' ,, (iMemA s1).(Snd)) (iFetchA s1)).
  Proof.
    intros s1 s1' Hu H Hf Hfip Hw Hpre.
    frq_prefix H.
    apply fw_ifTrue in H; [| apply and3_true; [exact Hf | exact Hfip | exact Hw]].
    apply fw_ifFalse in H; [| apply var_bool; rewrite or4_excAny; exact Hpre].
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [m' [rdy [Hm H']]]; clear H; rename H' into H.
    apply SemAction_liftAction_iff in Hm as [mr' [Hm ->]].
    apply regionsFetchRq_char in Hm; [| apply Hu].
    destruct Hm as [Hat Hk].
    exists mr', rdy; split; [exact Hat | split; [exact Hk |]].
    cbv beta in H.
    destruct rdy.
    - apply fw_ifTrue in H; [| reflexivity].
      frq_lets H.
      apply fw_ifTrue in H; [| rewrite notVar_eval, or4_excAny; apply negb_true_iff; exact Hpre].
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      destruct (evalActionPropGen_to_SemAction _ _ _ H) as [bp' [nio [_ H']]]; clear H; rename H' into H.
      cbv beta in H.
      frq_lets H. frq_enq H. frq_wrPc H. frq_ret H.
      destruct H as [<- _]; exists nio; unfold FrqStep; repeat split; reflexivity.
    - apply fw_ifFalse in H; [| reflexivity].
      frq_ret H.
      destruct H as [<- _]; unfold FrqStep; repeat split; reflexivity.
  Qed.
End FetchRqImpl.
