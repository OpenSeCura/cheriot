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
From Cheriot Require Import SpecDefines SpecDevice Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefSpecRead RefRevoker RefMemStep RefWriteRqPorts RefRouteAt RefRqStepChar.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the request steps of the memory `state` register on an ExternalMem line: the
 * request is staged in the `portRq` of the region holding the line (`StageAtL`); nothing else
 * changes. *)

Section Stage.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  Definition setPortRq r (y : ExtI r) (v : type (Option PortRq)) : ExtI r :=
    (y.(Fst) ,, (y.(Snd).(Fst) ,, (y.(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Fst) ,,
     (y.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
     (v ,, y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))))).

  Definition RegionStageI (r : MemRegion) (v : type (Option PortRq))
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y y' => y' = setPortRq r y v
    | CustomMem _ _ _ _ => fun _ _ => False
    end.

  (* The region holding line `L` staged `v`; the others are unchanged *)
  Fixpoint StageAtL (L : type Addr) (v : type (Option PortRq)) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> Prop with
    | [] => fun mi mi' => mi' = mi
    | r :: rs => fun mi mi' =>
        if isRegionAddrB r L then RegionStageI r v mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)
        else mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\ StageAtL L v rs mi.(Snd).(Fst) mi'.(Snd).(Fst)
    end.

  Definition isExtR (r : MemRegion) : bool :=
    match r.(regionKind) with ExternalMem => true | CustomMem _ _ _ _ => false end.

  (* The router stages the request when the region's action does *)
  Lemma route_stage :
    forall k (act : forall r, Action type (implMemRegionTree r) k) (res0 : type k) v L,
      (forall r env (y : TS (implMemRegionTree r)) Q, isExtR r = true -> RegionPort quietP r y ->
         evalActionPropGen env (act r) y Q -> exists y', RegionStageI r v y y' /\ Q y' res0) ->
      forall l acc (env : Env (implRegionsTree l)) mi Q,
        lineKind l L = Some true -> lineUnique l L -> AllPorts quietP l mi ->
        Forall (fun e => evalExpr e = getDefault k) acc ->
        evalActionPropGen env (genRouteRegionActionAux implMemRegionTree act (@Or type k) L acc l) mi Q ->
        exists mi', StageAtL L v l mi mi' /\ Q mi' res0.
  Proof.
    intros k act res0 v L Hreg l; induction l as [| r rs IH]; intros acc env mi Q Hk Hu Hq Hacc H;
      [discriminate Hk |].
    cbn [lineKind lineUnique] in Hk, Hu; cbn [AllPorts] in Hq; destruct Hq as [Hq0 Hq1].
    cbn [genRouteRegionActionAux evalActionPropGen] in H.
    change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L) in H.
    destruct mi as [m0 [m1 []]].
    cbn [StageAtL].
    destruct (isRegionAddrB r L) eqn:Em.
    - injection Hk as Hk.
      rewrite evalActionPropGen_liftAction in H.
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H, Hq0.
      destruct (Hreg r _ m0 _ Hk Hq0 H) as [y' [Hs H']].
      cbv beta in H'.
      cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd] in H'.
      rewrite evalActionPropGen_liftAction in H'.
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H'.
      apply (proj1 (route_none_or implMemRegionTree _ _ _ _ _ _ _ _ Hu)) in H'.
      cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H'.
      exists (y' ,, (m1 ,, tt)); split; [split; [exact Hs | reflexivity] |].
      cbn [rev map] in H'; rewrite map_app in H'; cbn [map] in H'.
      rewrite fold_left_app in H'; cbn [fold_left] in H'.
      rewrite (fold_left_evalOrBinary_default (map (@evalExpr _) (rev acc)) _) in H'
        by (apply Forall_map; apply Forall_rev; exact Hacc).
      change (evalExpr (Var type k res0)) with res0 in H'.
      rewrite evalOrBinary_getDefault_l in H'; exact H'.
    - rewrite evalActionPropGen_liftAction in H.
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
      destruct (IH _ _ _ _ Hk Hu Hq1 (Forall_cons (Var type k (evalExpr ConstDef)) eq_refl Hacc) H) as [m1' [Hs H']].
      cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H'.
      exists (m0 ,, (m1' ,, tt)); split; [| exact H'].
      cbn [Fst Snd]; split; [reflexivity | split; [reflexivity | exact Hs]].
  Qed.
End Stage.

Section StageRegion.
  Lemma region_write_stage :
    forall (w : type LineWriteRq) r env (y : TS (implMemRegionTree r)) Q, isExtR r = true -> RegionPort quietP r y ->
      evalActionPropGen env (@implMemRegionLineWriteRq r type w) y Q ->
      exists y', RegionStageI r (someWrite w) y y' /\ Q y' true.
  Proof.
    intros w r; unfold isExtR, RegionPort, RegionStageI, implMemRegionLineWriteRq, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q Hk Hq H; [| discriminate Hk].
    destruct Hq as [Hv _].
    unfold implExternalLineWriteRq in H.
    destruct y as [y0 [y1 [y2 [y3 [y4 [y5 [y6 []]]]]]]].
    unfold extPortRq in Hv; cbn [Fst Snd] in Hv.
    cbn [evalActionPropGen] in H.
    match type of H with (if ?c then _ else _) =>
      assert (Ec : c = true) by (change c with (negb (optValid y6)); rewrite Hv; reflexivity); rewrite Ec in H end.
    cbn [evalActionPropGen] in H.
    eexists; split; [| exact H]; reflexivity.
  Qed.

  (* The result of a staged read: ready, no response yet *)
  Definition rdStagedRes : type LineReadRqRes := (true ,, (getDefault (Option LineReadRp) ,, tt)).

  Lemma region_read_stage :
    forall (L : type Addr) mask r env (y : TS (implMemRegionTree r)) Q, isExtR r = true -> RegionPort quietP r y ->
      evalActionPropGen env (@implMemRegionLineReadRq r type L mask) y Q ->
      exists y', RegionStageI r (someRead L) y y' /\ Q y' rdStagedRes.
  Proof.
    intros L mask r; unfold isExtR, RegionPort, RegionStageI, implMemRegionLineReadRq, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q Hk Hq H; [| discriminate Hk].
    destruct Hq as [Hv _].
    unfold implExternalLineReadRq in H.
    destruct y as [y0 [y1 [y2 [y3 [y4 [y5 [y6 []]]]]]]].
    unfold extPortRq in Hv; cbn [Fst Snd] in Hv.
    cbn [evalActionPropGen] in H.
    match type of H with (if ?c then _ else _) =>
      assert (Ec : c = true) by (change c with (negb (optValid y6)); rewrite Hv; reflexivity); rewrite Ec in H end.
    cbn [evalActionPropGen] in H.
    eexists; split; [| exact H]; reflexivity.
  Qed.

  Lemma regionsWrite_stage :
    forall l env (mi mi' : TS (implRegionsTree l)) rdy (w : type LineWriteRq),
      lineKind l w.(Fst) = Some true -> lineUnique l w.(Fst) -> AllPorts quietP l mi ->
      SemAction env (@implRegionsLineWriteRq type l w) mi mi' rdy ->
      rdy = true /\ StageAtL w.(Fst) (someWrite w) l mi mi'.
  Proof.
    intros l env mi mi' rdy w Hk Hu Hq H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsLineWriteRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    destruct (route_stage Bool (fun r => @implMemRegionLineWriteRq r type w) true (someWrite w) (w.(Fst))
                (fun r env0 y Q => region_write_stage w r env0 y Q) l [] _ mi _ Hk Hu Hq (Forall_nil _) H)
      as [mi'' [Hs [E1 E2]]].
    rewrite <- E2; cbn [evalExpr map fold_left].
    rewrite isMapped_eval.
    match goal with |- context [lineKind l ?a] => change (lineKind l a) with (lineKind l (w.(Fst))) end.
    rewrite Hk; split; [reflexivity | rewrite <- E1; exact Hs].
  Qed.

  Lemma regionsRead_stage :
    forall l env (mi mi' : TS (implRegionsTree l)) res (L : type Addr) mask,
      lineKind l L = Some true -> lineUnique l L -> AllPorts quietP l mi ->
      SemAction env (@implRegionsLineReadRq type l L mask) mi mi' res ->
      res = rdStagedRes /\ StageAtL L (someRead L) l mi mi'.
  Proof.
    intros l env mi mi' res L mask Hk Hu Hq H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsLineReadRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    destruct (route_stage LineReadRqRes (fun r => @implMemRegionLineReadRq r type L mask) rdStagedRes (someRead L) L
                (fun r env0 y Q => region_read_stage L mask r env0 y Q) l [] _ mi _ Hk Hu Hq (Forall_nil _) H)
      as [mi'' [Hs [E1 E2]]].
    rewrite <- E2; cbn [evalExpr].
    rewrite isMapped_eval, Hk; split; [reflexivity | rewrite <- E1; exact Hs].
  Qed.
End StageRegion.

Section StageFrames.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  Lemma StageAtL_none :
    forall L v l mi mi', lineKind l L = None -> StageAtL L v l mi mi' -> mi' = mi.
  Proof.
    intros L v; induction l as [| r rs IH]; intros mi mi' Hk H; cbn [StageAtL lineKind] in *; [exact H |].
    destruct (isRegionAddrB r L); [discriminate Hk |].
    destruct H as [H0 [H1 H2]].
    apply prod_ext; [exact H0 |]; apply prod_ext; [exact (IH _ _ Hk H2) | exact H1].
  Qed.

  (* Port predicates that ignore `portRq` are kept *)
  Lemma AllPorts_stage :
    forall (P : forall r, ExtI r -> Prop), (forall r y v, P r (setPortRq r y v) = P r y) ->
      forall L v l mi mi', StageAtL L v l mi mi' -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP L v; induction l as [| r rs IH]; intros mi mi' Hw; cbn [StageAtL] in Hw; [rewrite Hw; reflexivity |].
    cbn [AllPorts].
    destruct (isRegionAddrB r L).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; f_equal.
      revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionStageI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hw0; [| contradiction].
      subst y'; apply HP.
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf, (IH _ _ Hrest); reflexivity.
  Qed.

  Lemma RqInsensitive_setPortRq :
    forall P, RqInsensitive P -> forall r (y : ExtI r) v, P r (setPortRq r y v) = P r y.
  Proof. intros P HP r y v; apply HP; reflexivity. Qed.

  Definition stagedP (L : type Addr) (v : type (Option PortRq)) : forall r, ExtI r -> Prop :=
    fun r y => extDataQuiet r y /\ (if isRegionAddrB r L then extPortRq r y = v else optValid (extPortRq r y) = false).

  Lemma quiet_stagedP_none :
    forall L v l (mi : TS (implRegionsTree l)), lineKind l L = None -> AllPorts quietP l mi -> AllPorts (stagedP L v) l mi.
  Proof.
    intros L v; induction l as [| r rs IH]; intros mi Hk H; [exact I |].
    cbn [lineKind] in Hk; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct (isRegionAddrB r L) eqn:Em; [discriminate Hk |].
    split; [| exact (IH _ Hk H1)].
    revert H0; generalize (mi.(Fst)); unfold RegionPort, stagedP, quietP, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
    destruct H0 as [Hp Hq]; rewrite Em; exact (conj Hq Hp).
  Qed.

  (* After the staging, the region holding `L` holds `v`; every other port is quiet *)
  Lemma stagedP_stage :
    forall L v l mi mi', lineUnique l L -> AllPorts quietP l mi -> StageAtL L v l mi mi' ->
      AllPorts (stagedP L v) l mi'.
  Proof.
    intros L v; induction l as [| r rs IH]; intros mi mi' Hu H Hw; [exact I |].
    cbn [lineUnique] in Hu; cbn [AllPorts] in H |- *; cbn [StageAtL] in Hw; destruct H as [H0 H1].
    destruct (isRegionAddrB r L) eqn:Em.
    - destruct Hw as [Hw0 Ht]; rewrite Ht; split; [| exact (quiet_stagedP_none L v rs _ Hu H1)].
      revert H0 Hw0; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, stagedP, quietP, RegionStageI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hw0; [| contradiction].
      subst y'; destruct H0 as [_ Hq]; rewrite Em; split; [exact Hq | reflexivity].
    - destruct Hw as [Hf [Ht Hrest]]; rewrite Hf; split.
      + revert H0; generalize (mi.(Fst)); unfold RegionPort, stagedP, quietP, implMemRegionTree.
        destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
        destruct H0 as [Hp Hq]; rewrite Em; exact (conj Hq Hp).
      + exact (IH _ _ Hu H1 Hrest).
  Qed.

  (* Device (CustomMem) positions are untouched *)
  Lemma regionStateAt_stage :
    forall L v l j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree l)),
      StageAtL L v l mi mi' -> isCustomR r0 ->
      regionStateAt implMemRegionTree j l r0 pf mi' = regionStateAt implMemRegionTree j l r0 pf mi.
  Proof.
    intros L v; induction l as [| r rs IH]; intros [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [StageAtL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct (isRegionAddrB r0 L); [| destruct H as [Hf _]; rewrite Hf; reflexivity].
      exfalso; destruct H as [Hw0 _]; revert Hw0; generalize (mi'.(Fst)) (mi.(Fst));
        unfold RegionStageI, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt].
      destruct (isRegionAddrB r L).
      + destruct H as [_ Hs]; rewrite Hs; reflexivity.
      + destruct H as [_ [_ Hrest]]; exact (IH j' r0 pf _ _ Hrest Hc).
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_stage :
    forall i r x (y y' : TS (implMemRegionTree r)) v,
      RegionStageI r v y y' -> RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r x y'.
  Proof.
    intros i r x y y' v; unfold RegionRelAt, RegionStageI, implMemRegionTree, memRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros Hs Hr; [| contradiction].
    subst y'; exact Hr.
  Qed.

  Lemma MemRelPost_stage :
    forall L v l i ms mi mi', StageAtL L v l mi mi' -> MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l ms mi'.
  Proof.
    intros L v; induction l as [| r rs IH]; intros i ms mi mi' Hw H; [exact I |].
    cbn [StageAtL] in Hw; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct (isRegionAddrB r L).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; exact (conj (RegionRelAt_stage _ _ _ _ _ _ Hw0 Hr) Hl).
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf; exact (conj Hr (IH _ _ _ _ Hrest Hl)).
  Qed.

  Lemma MemRelPre_stage :
    forall L v sRev iRev post l i ms mi mi', isCustomR iRev ->
      StageAtL L v (l ++ iRev :: post) mi mi' -> MemRelPre cp pp i l sRev iRev post ms mi ->
      MemRelPre cp pp i l sRev iRev post ms mi'.
  Proof.
    intros L v sRev iRev post; induction l as [| r rs IH]; intros i ms mi mi' Hc Hw H.
    - cbn [app StageAtL] in Hw; cbn [MemRelPre] in H |- *.
      destruct (isRegionAddrB iRev L) eqn:Em.
      + exfalso; destruct Hw as [Hw0 _]; revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
        unfold RegionStageI, isCustomR, implMemRegionTree in *; destruct (regionKind iRev); [contradiction | intros _ _ F; exact F].
      + destruct Hw as [_ [_ Hrest]]; exact (MemRelPost_stage _ _ _ _ _ _ _ Hrest H).
    - cbn [app StageAtL] in Hw; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct (isRegionAddrB r L).
      + destruct Hw as [Hw0 Ht]; rewrite Ht; exact (conj (RegionRelAt_stage _ _ _ _ _ _ Hw0 Hr) Hl).
      + destruct Hw as [Hf [_ Hrest]]; rewrite Hf; exact (conj Hr (IH _ _ _ _ Hc Hrest Hl)).
  Qed.
End StageFrames.
