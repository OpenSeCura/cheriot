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
From Cheriot.Proof Require Import RefSpecRead RefRouteAt RefRqStepChar RefSpecFetch RefExecImpl RefFetchRqImpl.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 6, the regions' side of `fetchAssemble`: the fetch response it reads
 * (`implRegionsFetchLineReadRp`, read-only: `fetchRpAt`) and the dequeue of that response
 * (`implRegionsFetchLineDeqRp`: the ExternalMem region holding the line empties its `readRp`,
 * `FetchDeqAtL`). *)

Lemma if_post : forall {A} (Q : A -> Prop) (b : bool) x y, (if b then Q x else Q y) -> Q (if b then x else y).
Proof. intros A Q [|] x y H; exact H. Qed.

Section FetchRpRegions.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  Definition someDefPkt : type (Option FetchPacket) := evalExpr (mkSome (ConstDef : Expr type FetchPacket)).

  (* The response a region offers *)
  Definition regionFetchRp (r : MemRegion) : TS (implMemRegionTree r) -> type (Option FetchPacket) :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> type (Option FetchPacket) with
    | ExternalMem => fun y =>
        let rpOpt : type (Option LineReadRp) := y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst) in
        if rpOpt.(Snd).(Fst) then (fetchPktOf rpOpt.(Fst) ,, (true ,, tt)) else getDefault (Option FetchPacket)
    | CustomMem _ _ _ _ => fun _ => someDefPkt
    end.

  (* The response for the line at `A` *)
  Fixpoint fetchRpAt (l : list MemRegion) : TS (implRegionsTree l) -> type Addr -> type (Option FetchPacket) :=
    match l as l0 return TS (implRegionsTree l0) -> type Addr -> type (Option FetchPacket) with
    | [] => fun _ _ => someDefPkt
    | r :: rs => fun mi A => if isRegionAddrB r A then regionFetchRp r mi.(Fst) else fetchRpAt rs mi.(Snd).(Fst) A
    end.

  Lemma region_fetchRp :
    forall r env (y : TS (implMemRegionTree r)) Q,
      evalActionPropGen env (@implMemRegionFetchLineReadRp r type) y Q -> Q y (regionFetchRp r y).
  Proof.
    intros r; unfold regionFetchRp, implMemRegionFetchLineReadRp, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q H.
    - unfold implExternalFetchLineReadRp in H.
      cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      cbn [evalActionPropGen] in H.
      rewrite !writeSubTreeState_readSubTreeState in H.
      exact (if_post (Q y) _ _ _ H).
    - cbn [evalActionPropGen] in H; exact H.
  Qed.

  Lemma route_fetchRp :
    forall A l acc (env : Env (implRegionsTree l)) mi Q,
      lineUnique l A -> Forall (fun e => evalExpr e = getDefault (Option FetchPacket)) acc ->
      evalActionPropGen env (genRouteRegionActionAux implMemRegionTree
                               (fun r => @implMemRegionFetchLineReadRp r type) (@Or type (Option FetchPacket)) A acc l) mi Q ->
      Q mi (match lineKind l A with Some _ => fetchRpAt l mi A | None => getDefault (Option FetchPacket) end).
  Proof.
    intros A l; induction l as [| r rs IH]; intros acc env mi Q Hu Hacc H.
    - cbn [genRouteRegionActionAux evalActionPropGen] in H.
      rewrite rev_tail_rev, app_nil_r in H; cbn [evalExpr] in H.
      rewrite (fold_left_evalOrBinary_default (map (@evalExpr _) (rev acc)) _) in H
        by (apply Forall_map; apply Forall_rev; exact Hacc).
      exact H.
    - cbn [lineUnique] in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen] in H.
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr A))))) with (isRegionAddrB r A) in H.
      destruct mi as [m0 [m1 []]].
      cbn [fetchRpAt lineKind].
      destruct (isRegionAddrB r A) eqn:Em.
      + rewrite evalActionPropGen_liftAction in H.
        cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        apply region_fetchRp in H; cbv beta in H.
        cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd] in H.
        rewrite evalActionPropGen_liftAction in H.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        apply (proj1 (route_none_or implMemRegionTree _ _ _ _ _ _ _ _ Hu)) in H.
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H.
        cbn [rev map] in H; rewrite map_app in H; cbn [map] in H.
        rewrite fold_left_app in H; cbn [fold_left] in H.
        rewrite (fold_left_evalOrBinary_default (map (@evalExpr _) (rev acc)) _) in H
          by (apply Forall_map; apply Forall_rev; exact Hacc).
        rewrite evalOrBinary_getDefault_l in H; exact H.
      + rewrite evalActionPropGen_liftAction in H.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        apply (IH _ _ _ _ Hu (Forall_cons (Var type (Option FetchPacket) (evalExpr ConstDef)) eq_refl Hacc)) in H.
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H.
        exact H.
  Qed.

  Lemma fetchRpAt_none : forall l mi A, lineKind l A = None -> fetchRpAt l mi A = someDefPkt.
  Proof.
    intros l; induction l as [| r rs IH]; intros mi A Hk; cbn [fetchRpAt lineKind] in *; [reflexivity |].
    destruct (isRegionAddrB r A); [discriminate Hk | exact (IH _ _ Hk)].
  Qed.

  Lemma regionsFetchRp_read :
    forall l env (mi : TS (implRegionsTree l)) (A : type Addr) P,
      lineUnique l A ->
      evalActionPropGen env (@implRegionsFetchLineReadRp type l A) mi P -> P mi (fetchRpAt l mi A).
  Proof.
    intros l env mi A P Hu H.
    unfold implRegionsFetchLineReadRp, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    apply (route_fetchRp A l [] _ mi _ Hu (Forall_nil _)) in H; cbv beta in H.
    cbn [evalActionPropGen evalExpr] in H.
    rewrite isMapped_eval in H.
    destruct (lineKind l A) eqn:Ek; [exact H |].
    rewrite (fetchRpAt_none l mi A Ek); exact H.
  Qed.

  (* --- The dequeue --- *)

  Definition clearReadRp r (y : ExtI r) : ExtI r :=
    (y.(Fst) ,, ((y.(Snd).(Fst).(Fst) ,, (y.(Snd).(Fst).(Snd).(Fst) ,, (y.(Snd).(Fst).(Snd).(Snd).(Fst) ,,
      (getDefault (Option LineReadRp) ,, y.(Snd).(Fst).(Snd).(Snd).(Snd).(Snd))))) ,, y.(Snd).(Snd))).

  Definition RegionFetchDeqI (r : MemRegion)
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y y' => y' = clearReadRp r y
    | CustomMem _ _ _ _ => fun y y' => y' = y
    end.

  Fixpoint FetchDeqAtL (A : type Addr) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> Prop with
    | [] => fun mi mi' => mi' = mi
    | r :: rs => fun mi mi' =>
        if isRegionAddrB r A then RegionFetchDeqI r mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)
        else mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\ FetchDeqAtL A rs mi.(Snd).(Fst) mi'.(Snd).(Fst)
    end.

  Lemma region_fetchDeq :
    forall r env (y : TS (implMemRegionTree r)) Q,
      evalActionPropGen env (@implMemRegionFetchLineDeqRp r type) y Q -> exists y', RegionFetchDeqI r y y' /\ Q y' Zmod.zero.
  Proof.
    intros r; unfold RegionFetchDeqI, implMemRegionFetchLineDeqRp, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q H.
    - unfold implExternalFetchLineDeqRp in H.
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      cbn [evalActionPropGen] in H.
      eexists; split; [| exact H]; reflexivity.
    - cbn [evalActionPropGen] in H; exists y; split; [reflexivity | exact H].
  Qed.

  Lemma route_none_deq :
    forall A l acc (env : Env (implRegionsTree l)) mi Q,
      lineKind l A = None ->
      evalActionPropGen env (genRouteRegionActionAux implMemRegionTree
                               (fun r => @implMemRegionFetchLineDeqRp r type) (fun _ => $0) A acc l) mi Q ->
      Q mi Zmod.zero.
  Proof.
    intros A l; induction l as [| r rs IH]; intros acc env mi Q Hk H.
    - cbn [genRouteRegionActionAux evalActionPropGen] in H; exact H.
    - cbn [lineKind] in Hk.
      cbn [genRouteRegionActionAux evalActionPropGen] in H.
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr A))))) with (isRegionAddrB r A) in H.
      destruct (isRegionAddrB r A); [discriminate Hk |].
      destruct mi as [m0 [m1 []]].
      rewrite evalActionPropGen_liftAction in H.
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
      apply (IH _ _ _ _ Hk) in H.
      cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H; exact H.
  Qed.

  Lemma route_fetchDeq :
    forall A l acc (env : Env (implRegionsTree l)) mi Q,
      lineUnique l A ->
      evalActionPropGen env (genRouteRegionActionAux implMemRegionTree
                               (fun r => @implMemRegionFetchLineDeqRp r type) (fun _ => $0) A acc l) mi Q ->
      exists mi' v, FetchDeqAtL A l mi mi' /\ Q mi' v.
  Proof.
    intros A l; induction l as [| r rs IH]; intros acc env mi Q Hu H.
    - cbn [genRouteRegionActionAux evalActionPropGen] in H.
      exists mi, (evalExpr ($0 : Expr type (Bit 0))); split; [reflexivity | exact H].
    - cbn [lineUnique] in Hu.
      cbn [genRouteRegionActionAux evalActionPropGen] in H.
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr A))))) with (isRegionAddrB r A) in H.
      destruct mi as [m0 [m1 []]].
      cbn [FetchDeqAtL].
      destruct (isRegionAddrB r A) eqn:Em.
      + rewrite evalActionPropGen_liftAction in H.
        cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        destruct (region_fetchDeq r _ m0 _ H) as [y' [Hs H']]; cbv beta in H'.
        cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd] in H'.
        rewrite evalActionPropGen_liftAction in H'.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H'.
        apply (route_none_deq A rs _ _ _ _ Hu) in H'.
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H'.
        exists (y' ,, (m1 ,, tt)), Zmod.zero; split; [split; [exact Hs | reflexivity] | exact H'].
      + rewrite evalActionPropGen_liftAction in H.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
        destruct (IH _ _ _ _ Hu H) as [m1' [v [Hs H']]].
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H'.
        exists (m0 ,, (m1' ,, tt)), v; split; [| exact H'].
        cbn [Fst Snd]; split; [reflexivity | split; [reflexivity | exact Hs]].
  Qed.
End FetchRpRegions.

Section FetchDeqFrames.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  Lemma AllPorts_none_impl' :
    forall (P P' : forall r, ExtI r -> Prop) A,
      (forall r y, isRegionAddrB r A = false -> P r y -> P' r y) ->
      forall l mi, lineKind l A = None -> AllPorts P l mi -> AllPorts P' l mi.
  Proof. exact AllPorts_none_impl. Qed.

  Lemma AllPorts_fetchDeqAt_impl :
    forall (P P' : forall r, ExtI r -> Prop) A,
      (forall r y, isRegionAddrB r A = true -> P r y -> P' r (clearReadRp r y)) ->
      (forall r y, isRegionAddrB r A = false -> P r y -> P' r y) ->
      forall l mi mi', lineUnique l A -> FetchDeqAtL A l mi mi' -> AllPorts P l mi -> AllPorts P' l mi'.
  Proof.
    intros P P' A Ht Hn; induction l as [| r rs IH]; intros mi mi' Hu Hw H; [exact I |].
    cbn [lineUnique] in Hu; cbn [FetchDeqAtL] in Hw; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct (isRegionAddrB r A) eqn:Em.
    - destruct Hw as [Hw0 Hs]; rewrite Hs; split; [| exact (AllPorts_none_impl P P' A Hn rs _ Hu H1)].
      revert H0 Hw0; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, RegionFetchDeqI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hw0; [| exact I].
      subst y'; exact (Ht _ y Em H0).
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf; split; [| exact (IH _ _ Hu Hrest H1)].
      revert H0; generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
      exact (Hn _ y Em H0).
  Qed.

  Lemma AllPorts_fetchDeqAt :
    forall (P : forall r, ExtI r -> Prop), (forall r y, P r (clearReadRp r y) = P r y) ->
      forall A l mi mi', FetchDeqAtL A l mi mi' -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP A; induction l as [| r rs IH]; intros mi mi' Hw; cbn [FetchDeqAtL] in Hw; [rewrite Hw; reflexivity |].
    cbn [AllPorts].
    destruct (isRegionAddrB r A).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; f_equal.
      revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionFetchDeqI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hw0;
        [subst y'; apply HP | reflexivity].
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf, (IH _ _ Hrest); reflexivity.
  Qed.

  Lemma regionStateAt_fetchDeqAt :
    forall A l j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree l)),
      FetchDeqAtL A l mi mi' -> isCustomR r0 ->
      regionStateAt implMemRegionTree j l r0 pf mi' = regionStateAt implMemRegionTree j l r0 pf mi.
  Proof.
    intros A; induction l as [| r rs IH]; intros [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [FetchDeqAtL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct (isRegionAddrB r0 A); [| destruct H as [Hf _]; rewrite Hf; reflexivity].
      destruct H as [Hw0 _]; revert Hw0; generalize (mi'.(Fst)) (mi.(Fst));
        unfold RegionFetchDeqI, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt].
      destruct (isRegionAddrB r A).
      + destruct H as [_ Hs]; rewrite Hs; reflexivity.
      + destruct H as [_ [_ Hrest]]; exact (IH j' r0 pf _ _ Hrest Hc).
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_fetchDeqAt :
    forall i r x (y y' : TS (implMemRegionTree r)),
      RegionFetchDeqI r y y' -> RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r x y'.
  Proof.
    intros i r x y y'; unfold RegionRelAt, RegionFetchDeqI, implMemRegionTree, memRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros Hs Hr; subst y'; exact Hr.
  Qed.

  Lemma MemRelPost_fetchDeqAt :
    forall A l i ms mi mi', FetchDeqAtL A l mi mi' -> MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l ms mi'.
  Proof.
    intros A; induction l as [| r rs IH]; intros i ms mi mi' Hw H; [exact I |].
    cbn [FetchDeqAtL] in Hw; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct (isRegionAddrB r A).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; exact (conj (RegionRelAt_fetchDeqAt _ _ _ _ _ Hw0 Hr) Hl).
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf; exact (conj Hr (IH _ _ _ _ Hrest Hl)).
  Qed.

  Lemma MemRelPre_fetchDeqAt :
    forall A sRev iRev post l i ms mi mi',
      FetchDeqAtL A (l ++ iRev :: post) mi mi' -> MemRelPre cp pp i l sRev iRev post ms mi ->
      MemRelPre cp pp i l sRev iRev post ms mi'.
  Proof.
    intros A sRev iRev post; induction l as [| r rs IH]; intros i ms mi mi' Hw H.
    - cbn [app FetchDeqAtL] in Hw; cbn [MemRelPre] in H |- *.
      destruct (isRegionAddrB iRev A).
      + destruct Hw as [_ Ht]; rewrite Ht; exact H.
      + destruct Hw as [_ [_ Hrest]]; exact (MemRelPost_fetchDeqAt _ _ _ _ _ _ Hrest H).
    - cbn [app FetchDeqAtL] in Hw; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct (isRegionAddrB r A).
      + destruct Hw as [Hw0 Ht]; rewrite Ht; exact (conj (RegionRelAt_fetchDeqAt _ _ _ _ _ Hw0 Hr) Hl).
      + destruct Hw as [Hf [_ Hrest]]; rewrite Hf; exact (conj Hr (IH _ _ _ _ Hrest Hl)).
  Qed.
End FetchDeqFrames.

(* --- The Stage's Step --- *)

Lemma fw_ifRead :
  forall {t : Tree Elem} (env : Env t) {k k'} s (c : bool) (tb fb : Action type t k') (cont : type k' -> Action type t k)
         old P (v : type k'),
    (c = true -> forall Q, evalActionPropGen env tb old Q -> Q old v) ->
    (c = false -> forall Q, evalActionPropGen env fb old Q -> Q old v) ->
    evalActionPropGen env (IfElse s (Var type Bool c) tb fb cont) old P ->
    evalActionPropGen env (cont v) old P.
Proof.
  intros t env k k' s c tb fb cont old P v Ht Hf H; cbn [evalActionPropGen] in H.
  change (evalExpr (Var type Bool c)) with c in H.
  destruct c; [exact (Ht eq_refl _ H) | exact (Hf eq_refl _ H)].
Qed.

Lemma fw_liftReadGen :
  forall {t : Tree Elem} (env : Env t) {k k'} s (p : NodePath t) (a : Action type (getNode p) k')
         (cont : type k' -> Action type t k) old (g : TS (getNode p) -> type k') P,
    (forall env' sub Q, evalActionPropGen env' a sub Q -> Q sub (g sub)) ->
    evalActionPropGen env (LetAction s (liftAction p a) cont) old P ->
    exists v, v = g (readSubTreeState p old) /\ evalActionPropGen env (cont v) old P.
Proof.
  intros t env k k' s p a cont old g P Hr H.
  exists (g (readSubTreeState p old)); split; [reflexivity |].
  exact (fw_liftRead env s p a cont old g P Hr H).
Qed.

Lemma fw_letExpGen :
  forall {t : Tree Elem} (env : Env t) {k k'} s (e : Expr type k') (cont : type k' -> Action type t k) old P,
    evalActionPropGen env (LetExp s e cont) old P ->
    exists v, v = evalExpr e /\ evalActionPropGen env (cont v) old P.
Proof. intros t env k k' s e cont old P H; exists (evalExpr e); split; [reflexivity | exact H]. Qed.

Section FetchAsmImpl.
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
  Hypothesis Hu : forall A, lineUnique implRegions A.

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STAGE :=
    (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation IBF s1 := (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind
               preDecode preDecodeBranch AdderAccessEnd.

  (* What the stage reads *)
  Definition aHead (s1 : IState) : type (Option FetchBufEntry) := fifoFirstVal (FBF s1).
  Definition aE (s1 : IState) : type FetchBufEntry := (aHead s1).(Fst).
  Definition aPre (s1 : IState) : bool :=
    evalExpr (Or [ (Var type FetchException (fbFetchExc (aE s1)))`"tag" ;
                   (Var type FetchException (fbFetchExc (aE s1)))`"seal" ;
                   (Var type FetchException (fbFetchExc (aE s1)))`"perm" ;
                   (Var type FetchException (fbFetchExc (aE s1)))`"bounds" ]).
  Definition aPkt (s1 : IState) : type (Option FetchPacket) :=
    if aPre s1 then someDefPkt else fetchRpAt implRegions (iRegionsA s1) (lineAddrOf (fbPcAddr (aE s1))).
  Definition aCp (s1 : IState) : bool := fetch_canProceed pcAddrInit fetchCapacity instCapacity (iFetchA s1).

  Lemma aPre_excAny : forall s1, aPre s1 = excAny (fbFetchExc (aE s1)).
  Proof.
    intros s1; unfold aPre; generalize (fbFetchExc (aE s1)) as x.
    intros [t [s [p [b []]]]]; destruct t, s, p, b; reflexivity.
  Qed.

  (* The step changed memory to `m` and fetch to `f` (and possibly the branch predictor) *)
  Definition FasmStep (s1 s1' : IState) m f : Prop :=
    iRfA s1' = iRfA s1 /\ iWbA s1' = iWbA s1 /\ iMemA s1' = m /\ iFetchA s1' = f /\
    iDecodeA s1' = iDecodeA s1 /\ iExecA s1' = iExecA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1.

  Definition aF0 (s1 : IState) := fetch_withCanProceed pcAddrInit fetchCapacity instCapacity (iFetchA s1) false.

  Lemma fetch_withFetchBufFifo_eta' :
    forall sf, fetch_withFetchBufFifo pcAddrInit fetchCapacity instCapacity sf
                 (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity sf) = sf.
  Proof. reflexivity. Qed.
  Lemma fetch_withInstFifo_eta' :
    forall sf, fetch_withInstFifo pcAddrInit fetchCapacity instCapacity sf
                 (fetch_instFifo pcAddrInit fetchCapacity instCapacity sf) = sf.
  Proof. reflexivity. Qed.

  Ltac asm_open H :=
    rewrite SemAction_iff_evalActionPropGen in H;
    unfold fetchAssembleStage in H;
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H;
    unfold fetchAssemble in H;
    cbn [execute_readExecEpoch implExecuteIfc mem_getInstRp mem_deqInstRp implMemIfc] in H.
  Ltac asm_read H lem :=
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (proj1 (lem _ _) HQ_)]; cbv beta in H.
  Ltac asm_cp H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readFetchCanProceed pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; cbv beta in H.
  Ltac asm_clear H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_clearFetchCanProceed pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; cbv beta in H.
  Ltac asm_gen H :=
    let v := fresh "rv" in let Ev := fresh "Erv" in destruct H as [v [Ev H]]; cbv beta in H.
  Ltac asm_head H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_first_iff fetchCapacity FetchBufEntry _ _ _) HQ_)];
    asm_gen H.
  Ltac asm_ibFull H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_isFull_raw instCapacity AssembledInst _ _ _) HQ_)];
    asm_gen H.
  Ltac asm_epoch H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecEpoch _ _) HQ_)]; asm_gen H.
  Ltac asm_pe H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readPredEpoch pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; asm_gen H.
  Ltac asm_curp H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readCurParcelOpt pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; asm_gen H.
  Ltac asm_str H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_readStraddleOpt pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; asm_gen H.
  Ltac asm_pcc H :=
    eapply fw_liftReadGen in H;
    [| intros env_ sub_ Q_ HQ_; apply (proj1 (evalActionPropGen_readRegsList _ _ _ _)) in HQ_;
       rewrite (readPcc_idx0 pcAddrInit) in HQ_; exact HQ_]; asm_gen H.
  (* the `Let`s; a `LetL` becomes a fresh variable *)
  Ltac asm_lets H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (LetExp _ _ _) _ _ =>
                let a := fresh "lv" in let Ea := fresh "Elv" in
                apply fw_letExpGen in H; destruct H as [a [Ea H]]; cbv beta in H
            | evalActionPropGen _ (LetAction _ (toAction _ _) _) _ _ =>
                let a := fresh "lv" in let Ea := fresh "Elv" in
                apply fw_letLGen in H; destruct H as [a [Ea H]]; cbv beta in H
            end).
  Ltac asm_ret H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (Return _) _ _ => apply fw_return in H
            | evalActionPropGen _ (LetAction _ _ _) _ _ => apply fw_letAction in H
            end; cbv beta in H).

  (* the response: read-only, `aPkt` *)
  Ltac asm_pkt H :=
    lazymatch type of H with
    | evalActionPropGen _ (IfElse _ (Var type Bool ?c) _
                             (liftAction ?pm (liftAction _ (@implRegionsFetchLineReadRp _ ?l ?A))) _) ?old _ =>
        eapply (fw_ifRead _ _ _ _ _ _ _ _
                  (if c then someDefPkt
                   else fetchRpAt l (readSubTreeState child0Path (readSubTreeState pm old)) A)) in H;
        [| let Hc := fresh in let Q := fresh in let HQ := fresh in
           intros Hc Q HQ; cbn [evalActionPropGen] in HQ; rewrite Hc; exact HQ
         | let Hc := fresh in let Q := fresh in let HQ := fresh in
           intros Hc Q HQ;
           apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in HQ;
           apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in HQ;
           apply regionsFetchRp_read in HQ; [| apply Hu];
           rewrite !writeSubTreeState_readSubTreeState in HQ;
           rewrite Hc; exact HQ ];
        cbv beta in H
    end.
  Ltac asm_headEq := match goal with E : ?v = fifoFirstVal _ |- _ => rewrite E end.

  Ltac asm_prefix H Hcp s1 :=
    asm_open H; asm_cp H; apply fw_ifTrue in H; [| exact Hcp];
    asm_clear H; asm_head H; asm_ibFull H; asm_epoch H; asm_pe H; asm_curp H; asm_str H; asm_pcc H;
    asm_lets H; asm_pkt H; asm_lets H.

  Lemma asm_idle :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = false -> s1' = s1.
  Proof.
    intros s1 s1' H Hcp.
    asm_open H; asm_cp H; apply fw_ifFalse in H; [| exact Hcp]; asm_ret H.
    destruct H as [<- _]; reflexivity.
  Qed.

  Axiom cheat : forall P : Prop, P.
  Lemma t1 : forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true -> False.
  Proof.
    intros s1 s1' H Hcp.
    asm_open H. asm_cp H. apply fw_ifTrue in H; [| exact Hcp].
    asm_clear H. asm_head H. asm_ibFull H. asm_epoch H. asm_pe H. asm_curp H. asm_str H. asm_pcc H.
    apply cheat.
  Qed.
  Lemma t2 : forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true -> False.
  Proof.
    intros s1 s1' H Hcp.
    asm_open H. asm_cp H. apply fw_ifTrue in H; [| exact Hcp].
    asm_clear H. asm_head H. asm_ibFull H. asm_epoch H. asm_pe H. asm_curp H. asm_str H. asm_pcc H.
    asm_lets H. asm_pkt H.
    apply cheat.
  Qed.
  Lemma t3 : forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true -> False.
  Proof.
    intros s1 s1' H Hcp.
    asm_open H. asm_cp H. apply fw_ifTrue in H; [| exact Hcp].
    asm_clear H. asm_head H. asm_ibFull H. asm_epoch H. asm_pe H. asm_curp H. asm_str H. asm_pcc H.
    asm_lets H. asm_pkt H. asm_lets H.
    apply cheat.
  Qed.
  Lemma asm_noHead :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true ->
      (aHead s1).(Snd).(Fst) = false -> FasmStep s1 s1' (iMemA s1) (aF0 s1).
  Proof.
    intros s1 s1' H Hcp Hv.
    asm_open H. asm_cp H. apply fw_ifTrue in H; [| exact Hcp].
    asm_clear H. asm_head H. asm_ibFull H. asm_epoch H. asm_pe H. asm_curp H. asm_str H. asm_pcc H.
    asm_lets H. asm_pkt H. asm_lets H.
    apply fw_ifFalse in H; [| asm_headEq; exact Hv]. asm_ret H.
    destruct H as [<- _]; unfold FasmStep; repeat split; reflexivity.
  Qed.
End FetchAsmImpl.
