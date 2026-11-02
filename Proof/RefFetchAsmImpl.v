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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefMemRel RefCoreRel RefFrame RefPeriph FifoGen.
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

Lemma fw_ifReadGen :
  forall {t : Tree Elem} (env : Env t) {k k'} s (c : bool) (tb fb : Action type t k') (cont : type k' -> Action type t k)
         old P (v : type k'),
    (c = true -> forall Q, evalActionPropGen env tb old Q -> Q old v) ->
    (c = false -> forall Q, evalActionPropGen env fb old Q -> Q old v) ->
    evalActionPropGen env (IfElse s (Var type Bool c) tb fb cont) old P ->
    exists v', v' = v /\ evalActionPropGen env (cont v') old P.
Proof.
  intros t env k k' s c tb fb cont old P v Ht Hf H.
  exists v; split; [reflexivity | exact (fw_ifRead env s c tb fb cont old P v Ht Hf H)].
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

  (* --- Transcriptions of `fetchAssemble` (Impl/ImplFetch.v), in the action's own syntax. Each
   * part ends in a call to the next one, so a step through a part's `Let`s has a small
   * continuation (compile speed). `asmRest` is the `canProceed` branch. --- *)
  Local Abbreviation MIF := (fun ty : Kind -> Type => @implMemIfc config implRegions ty revI).
  Local Abbreviation EIF := (fun ty : Kind -> Type => @implExecuteIfc ty).
  Local Abbreviation DECT := (implDecodeTree decodeCapacity).
  Local Abbreviation DMT := (implDataMemTree dataMemCapacity).
  Local Abbreviation MDT := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation CT := (coreTree (rfTree pcAddrInit) (withInst_BpTree bp) (implMemTree implRegions)
                              (implFetchTree pcAddrInit fetchCapacity instCapacity) DECT implExecuteTree DMT MDT).

  Section AsmTy.
  Variable ty : Kind -> Type.
  Local Abbreviation NP f := (f pcAddrInit fetchCapacity instCapacity bp MIF EIF DECT DMT MDT ty).
  Local Abbreviation FA f := (f pcAddrInit fetchCapacity instCapacity ty).
  Definition asmD (fetchHead : ty (Option FetchBufEntry)) (pktOpt : ty (Option FetchPacket))
    (isEpochMatch hasPreFault instBuf_isFull isSeqParcel initStraddle hasCombFault needsPred : ty Bool)
    (alignedPc entryPc instPc seqPc : ty Addr) (noneParcel someNextK : ty (Option (Bit LgFetchParcels)))
    (fetchOut : ty FetchOut) (execEpoch predEpoch : ty Epoch)
    (currInstLastParcel exitParcel : ty (Bit LgFetchParcels)) (entry : ty FetchBufEntry)
    (expInst : ty Inst) (pb : ty PreBranchInfo) (parcelK : ty (Bit CompInstSz)) (preExc : ty FetchException)
    : Action ty CT (Bit 0) :=
      If (##fetchHead`"valid") Then (
        If (##pktOpt`"valid") Then (
          If (Not #isEpochMatch) Then (
            Act (liftAction (NP np_fetchFifo) (@deq fetchCapacity FetchBufEntry ty)) ;
            If (Not #hasPreFault) Then (
              liftAction (NP ImplFetch.np_mem) (liftAction child0Path (@implRegionsFetchLineDeqRp ty implRegions alignedPc))
            ) ;
            liftAction (NP ImplFetch.np_fetch) (FA writeCurParcelOpt noneParcel)
          ) Else (
            If (Not #instBuf_isFull) Then (
              If #isSeqParcel Then (
                Act (liftAction (NP ImplFetch.np_fetch) (FA setFetchCanProceed)) ;
                Act (liftAction (NP ImplFetch.np_fetch) (FA writeCurParcelOpt someNextK)) ;
                Act (liftAction (NP ImplFetch.np_fetch) (FA clearStraddle)) ;
                Let asmInst : AssembledInst <- STRUCT {
                  "fetchOut"  ::= #fetchOut ;
                  "predPc"    ::= #seqPc ;
                  "execEpoch" ::= #execEpoch
                } ;
                liftAction (NP np_instFifo) (@enq instCapacity AssembledInst ty asmInst)
              ) Else (
                Let  instPred       : Addr <- ITE (Eq #currInstLastParcel #exitParcel) (##entry`"predPc") #seqPc ;
                Let  seqNextPktAddr : Addr <- Add [ #alignedPc ; $(Z.of_nat LineBytes) ] ;
                Let  defaultPredPc  : Addr <- ITE #initStraddle #seqNextPktAddr #instPred ;
                LetIf l2PredPc : Addr <-
                  If (And [ Not #initStraddle ; Not #hasCombFault ]) Then (
                    LetIf predPc <- If #needsPred Then
                                      liftAction (NP ImplFetch.np_bp) (bp.(withInst_getPred) instPc instPred expInst pb)
                                    Else Return #seqPc ;
                    Return {< TruncMsb (AddrSz - 1) 1 #predPc, Const ty (Bit 1) Zmod.zero >}
                  ) Else (
                    Return #defaultPredPc
                  ) ;
                Let  isEndOfLine    : Bool <- Or [ Not (Eq #l2PredPc #seqPc) ; isAllOnes #currInstLastParcel ] ;
                If #isEndOfLine Then (
                  Let exitMismatch   : Bool <- Not (Eq #exitParcel #currInstLastParcel) ;
                  Let predPcMismatch : Bool <- Not (Eq (##entry`"predPc") #l2PredPc) ;
                  Act (liftAction (NP np_fetchFifo) (@deq fetchCapacity FetchBufEntry ty)) ;
                  If (Not #hasPreFault) Then (
                    liftAction (NP ImplFetch.np_mem) (liftAction child0Path (@implRegionsFetchLineDeqRp ty implRegions alignedPc))
                  ) ;
                  Act (liftAction (NP ImplFetch.np_fetch) (FA writeCurParcelOpt noneParcel)) ;
                  Act (liftAction (NP ImplFetch.np_bp) (bp.(withInst_noInst_updByFetch)
                         entryPc currInstLastParcel exitMismatch l2PredPc predPcMismatch pb initStraddle)) ;
                  If #predPcMismatch Then (
                    Let nextPredEpoch : Epoch <- Add [ #predEpoch ; $1 ] ;
                    Act (liftAction (NP ImplFetch.np_fetch) (FA writePredEpoch nextPredEpoch)) ;
                    liftAction (NP ImplFetch.np_fetch) (FA writeFetchPc l2PredPc)
                  ) ;
                  Retv
                ) Else (
                  liftAction (NP ImplFetch.np_fetch) (FA writeCurParcelOpt someNextK)
                ) ;
                If #initStraddle Then (
                  Let newStraddle : StraddleHalf <- STRUCT {
                    "lowParcel" ::= #parcelK ;
                    "fetchExc"  ::= #preExc
                  } ;
                  Let someStraddle : Option StraddleHalf <- mkSome #newStraddle ;
                  liftAction (NP ImplFetch.np_fetch) (FA writeStraddleOpt someStraddle)
                ) Else (
                  Let asmInst : AssembledInst <- STRUCT {
                    "fetchOut"  ::= #fetchOut ;
                    "predPc"    ::= #l2PredPc ;
                    "execEpoch" ::= #execEpoch
                  } ;
                  Act (liftAction (NP ImplFetch.np_fetch) (FA clearStraddle)) ;
                  liftAction (NP np_instFifo) (@enq instCapacity AssembledInst ty asmInst)
                ) ;
                Retv
              ) ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

  Definition asmLets (fetchHead : ty (Option FetchBufEntry)) (instBuf_isFull : ty Bool) (execEpoch predEpoch : ty Epoch)
    (curParcelOpt : ty (Option (Bit LgFetchParcels))) (straddleOpt : ty (Option StraddleHalf))
    (pcc : ty FullECapWithTag) : Action ty CT (Bit 0) :=
      Let  entry              : FetchBufEntry              <- ##fetchHead`"data" ;
      Let  entryPc            : Addr                       <- ##entry`"pcAddr" ;
      Let  alignedPc          : Addr                       <- alignPacketAddr entryPc ;
      Let  startParcel        : Bit LgFetchParcels         <- getPacketParcel entryPc ;
      Let  exitParcel         : Bit LgFetchParcels         <- ##entry`"exitParcel" ;
      Let  preExc             : FetchException             <- ##entry`"fetchExc" ;
      Let  hasPreFault        : Bool                       <- Or [ ##preExc`"tag" ;
                                                                   ##preExc`"seal" ;
                                                                   ##preExc`"perm" ;
                                                                   ##preExc`"bounds" ] ;
      LetIf pktOpt : Option FetchPacket <-
        If #hasPreFault Then (
          Return (mkSome ConstDef)
        ) Else (
          liftAction (NP ImplFetch.np_mem) (liftAction child0Path (@implRegionsFetchLineReadRp ty implRegions alignedPc))
        ) ;
      Let  pkt                : FetchPacket                <- ##pktOpt`"data" ;
      Let  noneParcel         : Option (Bit LgFetchParcels) <- ConstDef ;
      Let  isEpochMatch       : Bool                       <- And [ Eq (##entry`"execEpoch") #execEpoch ;
                                                                    Eq (##entry`"predEpoch") #predEpoch ] ;
      Let  straddle           : StraddleHalf               <- ##straddleOpt`"data" ;
      Let  hasStraddle        : Bool                       <- ##straddleOpt`"valid" ;
      Let  k                  : Bit LgFetchParcels         <- ITE (##curParcelOpt`"valid") (##curParcelOpt`"data") #startParcel ;
      Let  instPcK            : Addr                       <- getParcelAddr alignedPc k ;
      Let  parcelK            : Bit CompInstSz             <- ReadArray #pkt #k ;
      Let  isCompParcel       : Bool                       <- isParcelCompressed parcelK ;
      Let  isLastK            : Bool                       <- isAllOnes #k ;
      Let  instPc             : Addr                       <- ITE #hasStraddle (Sub #alignedPc $2) #instPcK ;
      Let  isCompInst         : Bool                       <- And [ Not #hasStraddle ; #isCompParcel ] ;
      Let  stepBytes          : Addr                       <- ITE #isCompInst $(CompInstSz / 8) $(InstSz / 8) ;
      Let  seqPc              : Addr                       <- Add [ #instPc ; #stepBytes ] ;
      Let  instLgBytes        : Bit LgLgNumBytesFullCapSz  <-
        ITE #isCompInst $(Z.log2 (CompInstSz / 8)) $(Z.log2 (InstSz / 8)) ;
      LetL instEnd            : Bit (AddrSz + 2)           <- AdderAccessEnd instPc instLgBytes ;
      Let  pccECap            : ECap                       <- ##pcc`"ecap" ;
      Let  topExc             : Bool                       <- memFetchTopExc #instEnd (##pccECap`"top") ;
      Let  crossesLine        : Bool                       <- And [ Not #hasStraddle ; Not #isCompParcel ; #isLastK ] ;
      Let  initStraddle       : Bool                       <- And [ #crossesLine ; Not #topExc ] ;
      Let  kPlus1             : Bit LgFetchParcels         <- Add [ #k ; $1 ] ;
      Let  currInstLastParcel : Bit LgFetchParcels         <-
        ITE0 (Not #hasStraddle) (ITE (Or [ #isCompParcel ; #isLastK ]) #k #kPlus1) ;
      Let  highParcelIdx      : Bit LgFetchParcels         <- ITE0 (Not #hasStraddle) #kPlus1 ;
      Let  highParcel         : Bit CompInstSz             <- ITE0 (Not #crossesLine) (ReadArray #pkt #highParcelIdx) ;
      Let  lowParcel          : Bit CompInstSz             <- ITE #hasStraddle (##straddle`"lowParcel") #parcelK ;
      Let  rawInst            : Inst                       <- {< #highParcel, #lowParcel >} ;
      LetL expInst            : Inst                       <- preDecode rawInst ;
      Let  stradExc           : FetchException             <- ##straddle`"fetchExc" ;
      Let  pktExc             : FetchException             <- ITE #hasStraddle #stradExc #preExc ;
      Let  combExc            : FetchException             <- #pktExc `{ "bounds" <- Or [ ##pktExc`"bounds" ; #topExc ] } ;
      Let  hasCombFault       : Bool                       <- Or [ ##combExc`"tag" ;
                                                                   ##combExc`"seal" ;
                                                                   ##combExc`"perm" ;
                                                                   ##combExc`"bounds" ] ;
      LetL pb                 : PreBranchInfo              <- preDecodeBranch expInst ;
      Let  needsPred          : Bool                       <- Or [ ##pb`"isCjal" ; ##pb`"isBranch" ; ##pb`"isCjalr" ; ##pb`"isCall" ; ##pb`"isReturn" ] ;
      Let  isSeqParcel        : Bool                       <- And [ Not (isAllOnes #currInstLastParcel) ;
                                                                    Not (Eq #currInstLastParcel #exitParcel) ;
                                                                    Not #needsPred ] ;
      Let  nextK              : Bit LgFetchParcels         <- Add [ #currInstLastParcel ; $1 ] ;
      Let  someNextK          : Option (Bit LgFetchParcels) <- mkSome #nextK ;
      Let  fetchOut           : FetchOut                   <- STRUCT {
        "hasAsr"   ::= ##pccECap`"perms"`"SR" ;
        "inst"     ::= #expInst ;
        "fetchExc" ::= #combExc
      } ;
      asmD fetchHead pktOpt isEpochMatch hasPreFault instBuf_isFull isSeqParcel initStraddle hasCombFault needsPred
        alignedPc entryPc instPc seqPc noneParcel someNextK fetchOut execEpoch predEpoch
        currInstLastParcel exitParcel entry expInst pb parcelK preExc.

  Definition asmRest : Action ty CT (Bit 0) :=
      Act (liftAction (NP ImplFetch.np_fetch) (FA clearFetchCanProceed)) ;
      LetA fetchHead          : Option FetchBufEntry       <- liftAction (NP np_fetchFifo) (@first fetchCapacity FetchBufEntry ty) ;
      LetA instBuf_isFull     : Bool                       <- liftAction (NP np_instFifo) (@isFull instCapacity AssembledInst ty) ;
      LetA execEpoch          : Epoch                      <- liftAction (NP ImplFetch.np_execute) (@readExecEpoch ty) ;
      LetA predEpoch          : Epoch                      <- liftAction (NP ImplFetch.np_fetch) (FA readPredEpoch) ;
      LetA curParcelOpt       : Option (Bit LgFetchParcels) <- liftAction (NP ImplFetch.np_fetch) (FA readCurParcelOpt) ;
      LetA straddleOpt        : Option StraddleHalf        <- liftAction (NP ImplFetch.np_fetch) (FA readStraddleOpt) ;
      LetA pcc                : FullECapWithTag            <- liftAction (NP ImplFetch.np_rf) (readRegsList (gprPathsWithKind pcAddrInit) ($0 : Expr ty (Bit RegIdxSzReal))) ;
      asmLets fetchHead instBuf_isFull execEpoch predEpoch curParcelOpt straddleOpt pcc.

  End AsmTy.

  (* What the stage reads *)
  Definition aHead (s1 : IState) : type (Option FetchBufEntry) := fifoFirstVal (FBF s1).
  Definition aE (s1 : IState) : type FetchBufEntry := (aHead s1).(Fst).
  (* the same values in the action's syntax: conversions with the action's values then never
   * evaluate a field lookup by name *)
  Definition aEntry (s1 : IState) : type FetchBufEntry :=
    evalExpr ((Var type (Option FetchBufEntry) (aHead s1))`"data").
  Definition aPreExc (s1 : IState) : type FetchException :=
    evalExpr ((Var type FetchBufEntry (aEntry s1))`"fetchExc").
  Definition aEntryPc (s1 : IState) : type Addr :=
    evalExpr ((Var type FetchBufEntry (aEntry s1))`"pcAddr").
  Definition aAligned (s1 : IState) : type Addr := evalExpr (alignPacketAddr (ty := type) (aEntryPc s1)).
  Definition aPre (s1 : IState) : bool :=
    evalExpr (Or [ (Var type FetchException (aPreExc s1))`"tag" ;
                   (Var type FetchException (aPreExc s1))`"seal" ;
                   (Var type FetchException (aPreExc s1))`"perm" ;
                   (Var type FetchException (aPreExc s1))`"bounds" ]).
  Definition aPkt (s1 : IState) : type (Option FetchPacket) :=
    if aPre s1 then someDefPkt else fetchRpAt implRegions (iRegionsA s1) (aAligned s1).
  Definition aMatch (s1 : IState) : bool :=
    evalExpr (And [ Eq ((Var type FetchBufEntry (aEntry s1))`"execEpoch") (Var type Epoch (ACC iExecEpoch s1)) ;
                    Eq ((Var type FetchBufEntry (aEntry s1))`"predEpoch") (Var type Epoch (ACC iPredEpoch s1)) ]).

  Lemma aEntry_eq : forall s1, aEntry s1 = aE s1.
  Proof. reflexivity. Qed.
  Lemma aPreExc_eq : forall s1, aPreExc s1 = fbFetchExc (aE s1).
  Proof. reflexivity. Qed.
  Lemma aAligned_eq : forall s1, aAligned s1 = lineAddrOf (fbPcAddr (aE s1)).
  Proof. reflexivity. Qed.
  Lemma aMatch_eq : forall s1, aMatch s1 = ACC fbLive s1 (aE s1).
  Proof. reflexivity. Qed.
  Definition aCp (s1 : IState) : bool := fetch_canProceed pcAddrInit fetchCapacity instCapacity (iFetchA s1).

  Lemma aPre_excAny : forall s1, aPre s1 = excAny (fbFetchExc (aE s1)).
  Proof.
    intros s1; unfold aPre; rewrite aPreExc_eq; generalize (fbFetchExc (aE s1)) as x.
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
  Ltac asm_letsS H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (LetExp _ _ _) _ _ => apply fw_letExp in H; cbv beta in H
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
        eapply (fw_ifReadGen _ _ _ _ _ _ _ _
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
        let v := fresh "pk" in let Ev := fresh "Epkr" in destruct H as [v [Ev H]]; cbv beta in H
    end.
  Ltac asm_headEq := match goal with E : ?v = fifoFirstVal _ |- _ => rewrite E end.

  Ltac asm_rh := match goal with Eh : _ = aHead _ |- _ => rewrite Eh end.
  Ltac asm_none := match goal with En : ?v = evalExpr (Const _ _ _) |- _ => rewrite En end.
  Ltac asm_vars := repeat match goal with E : ?v = _ |- context [?v] => is_var v; rewrite E end.
  Ltac asm_fifoDeq H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_deq_iff fetchCapacity FetchBufEntry _ _ _) HQ_)];
    cbv beta in H.
  Ltac asm_wrCp H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_writeCurParcelOpt pcAddrInit fetchCapacity instCapacity _ _ _) HQ_)]; cbv beta in H.

  Ltac asm_start H Hcp :=
    asm_open H; asm_cp H; apply fw_ifTrue in H; [| exact Hcp];
    lazymatch type of H with
    | evalActionPropGen ?e _ ?o ?Q => change (evalActionPropGen e (asmRest type) o Q) in H
    end;
    unfold asmRest in H;
    asm_clear H; asm_head H; asm_ibFull H; asm_epoch H; asm_pe H; asm_curp H; asm_str H; asm_pcc H;
    unfold asmLets in H; asm_letsS H; asm_pkt H; asm_lets H;
    unfold asmD in H.
  Ltac asm_prefix H Hcp s1 :=
    asm_open H; asm_cp H; apply fw_ifTrue in H; [| exact Hcp];
    asm_clear H; asm_head H; asm_ibFull H; asm_epoch H; asm_pe H; asm_curp H; asm_str H; asm_pcc H;
    asm_lets H; asm_pkt H; asm_lets H.

  Lemma asm_noHead :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true ->
      (aHead s1).(Snd).(Fst) = false -> FasmStep s1 s1' (iMemA s1) (aF0 s1).
  Proof.
    intros s1 s1' H Hcp Hv.
    asm_start H Hcp.
    apply fw_ifFalse in H; [| asm_headEq; exact Hv]. asm_ret H.
    destruct H as [<- _]; unfold FasmStep; repeat split; reflexivity.
  Qed.

  Definition aNone : type (Option (Bit LgFetchParcels)) := evalExpr (ConstDef : Expr type (Option (Bit LgFetchParcels))).
  Definition aFDrop (s1 : IState) :=
    fetch_withCurParcelOpt pcAddrInit fetchCapacity instCapacity
      (fetch_withFetchBufFifo pcAddrInit fetchCapacity instCapacity (aF0 s1) (fifoDeqState (FBF s1))) aNone.

  Definition aIbFull (s1 : IState) : bool :=
    Zmod.eqb (fifo_size (IBF s1)) (Zmod.of_Z _ (Z.of_nat instCapacity)).

  Ltac asm_norm s1 :=
    repeat match goal with
    | E : ?v = fifoFirstVal _ |- _ => change (v = aHead s1) in E
    | E : ?v = Zmod.eqb (fifo_size _) _ |- _ => change (v = aIbFull s1) in E
    | E : ?v = ex_execEpoch _ |- _ => change (v = ACC iExecEpoch s1) in E
    | E : ?v = fetch_predEpoch _ _ _ _ |- _ => change (v = ACC iPredEpoch s1) in E
    | E : ?v = fetch_curParcelOpt _ _ _ _ |- _ => change (v = ACC iCurParcel s1) in E
    | E : ?v = fetch_straddleOpt _ _ _ _ |- _ => change (v = ACC iStraddle s1) in E
    | E : ?v = readPcc _ _ |- _ => change (v = ACC iPcc s1) in E
    end.

  (* the response read is `aPkt` *)
  Ltac asm_pkEq s1 :=
    match goal with E : ?v = (if _ then someDefPkt else fetchRpAt _ ?R _) |- _ =>
      let ER := fresh in assert (ER : R = iRegionsA s1) by reflexivity;
      let E' := fresh "Epk" in
      assert (E' : v = aPkt s1)
        by (rewrite E, ER; match goal with Eh : _ = aHead s1 |- _ => rewrite Eh end; reflexivity);
      clear E ER
    end.
  (* the epoch test is `aMatch` *)
  Ltac asm_matchEq s1 :=
    match goal with E : ?v = evalExpr (And [Eq _ _ ; Eq _ _]) |- _ =>
      let E' := fresh "Ematch" in
      assert (E' : v = aMatch s1)
        by (rewrite E;
            repeat match goal with
                   | Eh : _ = aHead s1 |- _ => rewrite Eh
                   | Ee : _ = ACC iExecEpoch s1 |- _ => rewrite Ee
                   | Ep : _ = ACC iPredEpoch s1 |- _ => rewrite Ep
                   end; reflexivity);
      clear E
    end.

  (* A head whose epochs are stale is dropped, with its response *)
  Lemma asm_stale :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true ->
      (aHead s1).(Snd).(Fst) = true -> (aPkt s1).(Snd).(Fst) = true ->
      aMatch s1 = false ->
      exists mr', (aPre s1 = true -> mr' = iRegionsA s1) /\
                  (aPre s1 = false -> FetchDeqAtL (aAligned s1) implRegions (iRegionsA s1) mr') /\
                  FasmStep s1 s1' (mr' ,, (iMemA s1).(Snd)) (aFDrop s1).
  Proof.
    intros s1 s1' H Hcp Hv Hpv Hst.
    asm_start H Hcp. asm_norm s1. asm_pkEq s1. asm_matchEq s1.
    apply fw_ifTrue in H; [| match goal with Eh : _ = aHead s1 |- _ => rewrite Eh end; exact Hv].

    apply fw_ifTrue in H; [| rewrite Epk; exact Hpv].
    apply fw_ifTrue in H; [| rewrite notVar_eval, Ematch; exact (f_equal negb Hst)].
    asm_fifoDeq H.
    destruct (aPre s1) eqn:Hpre.
    - apply fw_ifFalse in H; [| rewrite notVar_eval; asm_rh; exact (f_equal negb Hpre)].
      apply fw_return in H; cbv beta in H.
      asm_wrCp H. asm_ret H.
      destruct H as [<- _]; exists (iRegionsA s1); split; [reflexivity | split; [discriminate |]].
      unfold FasmStep; asm_none; repeat split; reflexivity.
    - apply fw_ifTrue in H; [| rewrite notVar_eval; asm_rh; exact (f_equal negb Hpre)].
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
      unfold implRegionsFetchLineDeqRp, genRouteRegionUnitAction, genRouteRegionAction in H.
      destruct (route_fetchDeq _ _ _ _ _ _ (Hu _) H) as [mr' [v [Hdq H']]]; clear H; rename H' into H.
      cbv beta in H.
      asm_wrCp H. asm_ret H.
      destruct H as [<- _]; exists mr'; split; [discriminate | split].
      + intros _; match goal with Eh : _ = aHead s1 |- _ => rewrite Eh in Hdq end; exact Hdq.
      + unfold FasmStep; asm_none; repeat split; reflexivity.
  Qed.

  Lemma asm_noPkt :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true ->
      (aHead s1).(Snd).(Fst) = true -> (aPkt s1).(Snd).(Fst) = false -> FasmStep s1 s1' (iMemA s1) (aF0 s1).
  Proof.
    intros s1 s1' H Hcp Hv Hpv.
    asm_start H Hcp. asm_norm s1. asm_pkEq s1.
    apply fw_ifTrue in H; [| asm_rh; exact Hv].
    apply fw_ifFalse in H; [| rewrite Epk; exact Hpv].
    asm_ret H.
    destruct H as [<- _]; unfold FasmStep; repeat split; reflexivity.
  Qed.

  Lemma asm_ibFullStall :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = true ->
      (aHead s1).(Snd).(Fst) = true -> (aPkt s1).(Snd).(Fst) = true -> aMatch s1 = true ->
      aIbFull s1 = true -> FasmStep s1 s1' (iMemA s1) (aF0 s1).
  Proof.
    intros s1 s1' H Hcp Hv Hpv Hm Hf.
    asm_start H Hcp. asm_norm s1. asm_pkEq s1. asm_matchEq s1.
    apply fw_ifTrue in H; [| asm_rh; exact Hv].
    apply fw_ifTrue in H; [| rewrite Epk; exact Hpv].
    apply fw_ifFalse in H; [| rewrite notVar_eval, Ematch; exact (f_equal negb Hm)].
    apply fw_ifFalse in H;
      [| rewrite notVar_eval; match goal with Ef : _ = aIbFull _ |- _ => rewrite Ef end; exact (f_equal negb Hf)].
    asm_ret H.
    destruct H as [<- _]; unfold FasmStep; repeat split; reflexivity.
  Qed.

  Lemma asm_idle :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> aCp s1 = false -> s1' = s1.
  Proof.
    intros s1 s1' H Hcp.
    asm_open H; asm_cp H; apply fw_ifFalse in H; [| exact Hcp]; asm_ret H.
    destruct H as [<- _]; reflexivity.
  Qed.

End FetchAsmImpl.
