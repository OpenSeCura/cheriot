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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead.
From Cheriot.Proof Require Import RefRevoker ImplSpec RefFetch RefMemStep RefSpecFetch.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4: the data write-request ports (`writeRqPorts`).
 * 1. One port step of an ExternalMem region (`implExternalLineWriteRqPort`): nothing when no write
 *    is staged, otherwise the staged write is sent and, when accepted (`lineWriteRqReady`), joins
 *    the region's accepted writes and leaves `portRq` (`wrRqPort_cases`, `wrRqSent`); over a
 *    region list, one ExternalMem position steps (`wrRqPorts_step`). *)

(* --- 1. One Data Write-Request Port Step --- *)

Section WrRqPortRegion.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* The staged request of the region's data port: valid and a Write, and the write itself *)
  Definition portRqIsWrite r (y : ExtI r) : bool :=
    let p := extPortRq r y in evalExpr (And [ ##p`"valid" ; (##p`"data") `? "Write" ]).
  Definition portRqWrite r (y : ExtI r) : type LineWriteRq :=
    let p := extPortRq r y in evalExpr ((##p`"data") `! "Write").

  (* The region after its port sent write `w`, accepted (`rdy`) or not *)
  Definition wrRqSent r (y : ExtI r) (w : type LineWriteRq) (rdy : bool) : ExtI r :=
    ((y.(Fst).(Fst) ,, (y.(Fst).(Snd).(Fst) ,, (y.(Fst).(Snd).(Snd).(Fst) ,,
       ((w :: y.(Fst).(Snd).(Snd).(Snd).(Fst)) ,, y.(Fst).(Snd).(Snd).(Snd).(Snd))))) ,,
     (y.(Snd).(Fst) ,, (y.(Snd).(Snd).(Fst) ,, ((rdy :: y.(Snd).(Snd).(Snd).(Fst)) ,,
       (if rdy
        then (y.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
               (getDefault (Option PortRq) ,, y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))
        else y.(Snd).(Snd).(Snd).(Snd)))))).

  Lemma wrRqPort_cases :
    forall r (env : Env (implExternalMemRegionTree r)) (y y' : ExtI r) v,
      SemAction env (@implExternalLineWriteRqPort r type) y y' v ->
      (portRqIsWrite r y = false /\ y' = y) \/
      (portRqIsWrite r y = true /\ exists rdy, y' = wrRqSent r y (portRqWrite r y) rdy).
  Proof.
    intros r env y y' v Hsem.
    unfold implExternalLineWriteRqPort in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn -[evalExpr] in Hsem.
    match type of Hsem with (if ?c then _ else _) =>
      assert (Ec : c = portRqIsWrite r y) by reflexivity; rewrite Ec in Hsem end.
    destruct (portRqIsWrite r y).
    - right; split; [reflexivity |].
      destruct Hsem as [rdy [_ Hrest]]; exists rdy.
      unfold cast_send_expr in Hrest.
      match type of Hrest with context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
        rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) in Hrest end.
      destruct rdy; destruct Hrest as [<- _]; reflexivity.
    - left; split; [reflexivity |]; destruct Hsem as [<- _]; reflexivity.
  Qed.

  (* What the relation reads from a region after its port sent a write *)
  Lemma implAccWrites_wrRqSent : forall r (y : ExtI r) w rdy,
    implAccWrites r (wrRqSent r y w rdy) = if rdy then w :: implAccWrites r y else implAccWrites r y.
  Proof. intros r y w [|]; reflexivity. Qed.

  Lemma extPortRq_wrRqSent : forall r (y : ExtI r) w rdy,
    extPortRq r (wrRqSent r y w rdy) = if rdy then getDefault (Option PortRq) else extPortRq r y.
  Proof. intros r y w [|]; reflexivity. Qed.

  Lemma implDataAccRqs_wrRqSent : forall r (y : ExtI r) w rdy,
    implDataAccRqs r (wrRqSent r y w rdy) = implDataAccRqs r y.
  Proof. intros r y w [|]; reflexivity. Qed.

  Lemma wrRqSent_rps : forall r (y : ExtI r) w rdy,
    (wrRqSent r y w rdy).(Fst).(Snd).(Snd).(Fst) = y.(Fst).(Snd).(Snd).(Fst).
  Proof. reflexivity. Qed.

  Lemma wrRqSent_fetch : forall r (y : ExtI r) w rdy,
    (wrRqSent r y w rdy).(Fst).(Fst) = y.(Fst).(Fst) /\ (wrRqSent r y w rdy).(Snd).(Fst) = y.(Snd).(Fst).
  Proof. split; reflexivity. Qed.

  (* The staged write of `PortsWriteStaged` *)
  Lemma portRq_someWrite :
    forall r (y : ExtI r) w, extPortRq r y = someWrite w -> portRqIsWrite r y = true /\ portRqWrite r y = w.
  Proof.
    intros r y w H; unfold portRqIsWrite, portRqWrite; cbv zeta; rewrite H; split; [reflexivity |].
    exact (evalExpr_ReadUnionData_BuildUnion PortRqList (@Build_FinType 2 1 I) (Var type LineWriteRq w) eq_refl).
  Qed.

  Lemma portRqIsWrite_invalid :
    forall r (y : ExtI r), optValid (extPortRq r y) = false -> portRqIsWrite r y = false.
  Proof.
    intros r y H; unfold portRqIsWrite; cbv zeta.
    destruct (extPortRq r y) as [d [vld []]]; unfold optValid in H; cbn in H; subst vld; reflexivity.
  Qed.

  Lemma portRqIsWrite_read :
    forall r (y : ExtI r) L, extPortRq r y = someRead L -> portRqIsWrite r y = false.
  Proof. intros r y L H; unfold portRqIsWrite; cbv zeta; rewrite H; reflexivity. Qed.

  (* One region's write-request port step *)
  Definition RegionWrRqStep (r : MemRegion) : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y y' => (portRqIsWrite r y = false /\ y' = y) \/
                                 (portRqIsWrite r y = true /\ exists rdy, y' = wrRqSent r y (portRqWrite r y) rdy)
    | CustomMem _ _ _ _ => fun _ _ => False
    end.

  Fixpoint WrRqPortStepL (l : list MemRegion) : TS (implRegionsTree l) -> TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> Prop with
    | [] => fun _ _ => False
    | r :: rs => fun mi mi' =>
        (RegionWrRqStep r mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)) \/
        (mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\ WrRqPortStepL rs mi.(Snd).(Fst) mi'.(Snd).(Fst))
    end.

  Lemma wrRqPorts_step :
    forall l (aI : forall ty, Action ty (implRegionsTree l) (Bit 0)) env mi mi' v,
      In aI (implCollectLineWriteRqPorts l) ->
      SemAction env (aI type) mi mi' v -> WrRqPortStepL l mi mi'.
  Proof.
    induction l as [| r rs IH]; intros aI env mi mi' v Hin Hsem; [destruct Hin |].
    unfold implCollectLineWriteRqPorts, implCollectRegionActions in Hin; cbn [genCollectRegionActions] in Hin.
    apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as [f [<- Hf]].
    - left; apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
      split; [| reflexivity]; cbn [writeSubTreeState readSubTreeState] in Hy' |- *.
      revert f Hf Hy'; destruct r as [nm bs sz kd sn im ba sa]; destruct kd;
        cbn [implMemRegionLineWriteRqPorts regionKind In RegionWrRqStep]; intros f Hf Hy'; try contradiction.
      destruct Hf as [<- | []]; exact (wrRqPort_cases _ _ _ _ _ Hy').
    - right; apply SemAction_liftAction_iff in Hsem as [z' [Hz' ->]].
      split; [reflexivity | split; [reflexivity |]].
      exact (IH f _ _ _ _ Hf Hz').
  Qed.

  (* No port holds a Write: nothing changes *)
  Lemma wrRqStep_noWrite :
    forall l mi mi', AllPorts (fun r y => portRqIsWrite r y = false) l mi -> WrRqPortStepL l mi mi' -> mi' = mi.
  Proof.
    induction l as [| r rs IH]; intros mi mi' Hn Hst; [destruct Hst |].
    cbn [AllPorts] in Hn; destruct Hn as [Hn0 Hn1]; cbn [WrRqPortStepL] in Hst.
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - apply prod_ext; [| exact Ht].
      revert Hn0 Hs; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, RegionWrRqStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hn Hs; [| contradiction].
      destruct Hs as [[_ ->] | [Hb _]]; [reflexivity | rewrite Hn in Hb; discriminate].
    - apply prod_ext; [exact Hf |]; apply prod_ext; [exact (IH _ _ Hn1 Hrest) | exact Ht].
  Qed.
End WrRqPortRegion.

(* --- 2. A Line Write of the Spec through the Router --- *)

Section SpecWrite.
  (* An ExternalMem region after it was sent write `w` *)
  Definition RegionWriteS (r : MemRegion) : TS (memRegionTree r) -> type LineWriteRq -> TS (memRegionTree r) :=
    match r.(regionKind) as k return TS (memRegionKindTree r k) -> type LineWriteRq -> TS (memRegionKindTree r k) with
    | ExternalMem => fun x w => (x.(Fst) ,, (x.(Snd).(Fst) ,, (x.(Snd).(Snd).(Fst) ,, ((w :: x.(Snd).(Snd).(Snd).(Fst)) ,, tt))))
    | CustomMem _ _ _ _ => fun x _ => x
    end.

  (* The spec memory after write `w` reached the first region holding line `L` *)
  Fixpoint specWriteLine (l : list MemRegion) (L : type Addr) (w : type LineWriteRq) : TS (specMemTree l) -> TS (specMemTree l) :=
    match l as l0 return TS (specMemTree l0) -> TS (specMemTree l0) with
    | [] => fun ms => ms
    | r :: rs => fun ms =>
        if isRegionAddrB r L then (RegionWriteS r ms.(Fst) w ,, ms.(Snd))
        else (ms.(Fst) ,, (specWriteLine rs L w ms.(Snd).(Fst) ,, ms.(Snd).(Snd)))
    end.

  Lemma region_line_write_wp :
    forall r (env : Env (memRegionTree r)) (x : TS (memRegionTree r)) (w : type LineWriteRq) P,
      match r.(regionKind) with ExternalMem => true | CustomMem _ _ _ _ => false end = true ->
      (forall v, P (RegionWriteS r x w) v) ->
      evalActionPropGen env (@memRegionLineWrite r type w) x P.
  Proof.
    intros r; unfold RegionWriteS, memRegionLineWrite, memRegionTree.
    destruct (regionKind r) as [| ch rd wr irq]; intros env x w P Hk HP; [| discriminate Hk].
    unfold externalLineWrite.
    destruct x as [xf [xrq [xrp [xwr []]]]].
    cbn; apply HP.
  Qed.

  Lemma route_write_none_wp :
    forall (getAction : forall r, Action type (memRegionTree r) (Bit 0)) L l combine acc
           (env : Env (specMemTree l)) ms P,
      lineKind l L = None -> (forall v, P ms v) ->
      evalActionPropGen env (genRouteRegionActionAux memRegionTree getAction combine L acc l) ms P.
  Proof.
    intros getAction L l; induction l as [| r rs IH]; intros combine acc env ms P Hk HP.
    - cbn [genRouteRegionActionAux evalActionPropGen]; apply HP.
    - cbn [lineKind] in Hk.
      destruct (isRegionAddrB r L) eqn:Em; [discriminate Hk |].
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      rewrite Em.
      rewrite evalActionPropGen_liftAction.
      apply IH; [exact Hk |].
      intros v; destruct ms as [m0 [m1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
      apply HP.
  Qed.

  Lemma route_write_wp :
    forall (w : type LineWriteRq) L l combine acc (env : Env (specMemTree l)) ms P,
      lineKind l L = Some true -> lineUnique l L ->
      (forall v, P (specWriteLine l L w ms) v) ->
      evalActionPropGen env
        (genRouteRegionActionAux memRegionTree (fun r => @memRegionLineWrite r type w) combine L acc l) ms P.
  Proof.
    intros w L l; induction l as [| r rs IH]; intros combine acc env ms P Hk Hu HP; [discriminate Hk |].
    cbn [lineKind lineUnique specWriteLine] in Hk, Hu, HP.
    cbn [genRouteRegionActionAux evalActionPropGen].
    change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
    destruct ms as [m0 [m1 []]].
    revert Hk Hu HP; destruct (isRegionAddrB r L) eqn:Em; intros Hk Hu HP; rewrite evalActionPropGen_liftAction.
    - cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd].
      apply region_line_write_wp; [injection Hk as Hk; exact Hk |].
      intros v0; cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
      rewrite evalActionPropGen_liftAction.
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
      apply route_write_none_wp; [exact Hu |].
      intros v; cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd]; apply HP.
    - cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
      apply IH; [exact Hk | exact Hu |].
      intros v; cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd]; apply HP.
  Qed.

  Lemma specMemLineWrite_wp :
    forall l (w : type LineWriteRq) (env : Env (specMemTree l)) ms P,
      lineKind l w.(Fst) = Some true -> lineUnique l w.(Fst) ->
      (forall v, P (specWriteLine l w.(Fst) w ms) v) ->
      evalActionPropGen env (@specMemLineWrite type l w) ms P.
  Proof.
    intros l w env ms P Hk Hu HP.
    unfold specMemLineWrite, genRouteRegionUnitAction, genRouteRegionAction.
    apply ev_letExp; cbv beta.
    apply route_write_wp; [exact Hk | exact Hu | exact HP].
  Qed.

  (* The line a write request is for *)
  Lemma buildW_addr :
    forall b addr pkt size, (buildW b addr pkt size).(Fst) = lineOf b addr.
  Proof. intros [|] addr pkt size; reflexivity. Qed.

  Lemma specMemWrite_wp :
    forall l (addr : type Addr) (stVal : type FullCapWithTag) (size : type (Bit LgLgNumBytesFullCapSz))
           (env : Env (specMemTree l)) ms P,
      lineKind l (lineOf false addr) = Some true -> lineUnique l (lineOf false addr) ->
      (forall v, P (specWriteLine l (lineOf false addr) (buildW false addr (disassembleW addr stVal size) size) ms) v) ->
      evalActionPropGen env (@specMemWrite type l addr stVal size) ms P.
  Proof.
    intros l addr stVal size env ms P Hk Hu HP.
    unfold specMemWrite.
    apply ev_letL; cbv beta.
    apply ev_letL; cbv beta.
    change (evalActionPropGen env (@specMemLineWrite type l (buildW false addr (disassembleW addr stVal size) size)) ms P).
    apply specMemLineWrite_wp; rewrite buildW_addr; [exact Hk | exact Hu | exact HP].
  Qed.

  (* What a write keeps: the fetch view grows, the snapshot counts stay, devices are unchanged *)
  Lemma RegionFetchViewExt_write : forall r x w, RegionFetchViewExt r x (RegionWriteS r x w).
  Proof.
    intros r; unfold RegionFetchViewExt, RegionWriteS, memRegionTree; destruct (regionKind r); intros x w;
      [| exact I].
    split; [reflexivity | exists [w]; reflexivity].
  Qed.

  Lemma FetchViewExt_specWrite : forall l L w ms, FetchViewExt l ms (specWriteLine l L w ms).
  Proof.
    induction l as [| r rs IH]; intros L w ms; cbn [specWriteLine FetchViewExt]; [exact I |].
    destruct (isRegionAddrB r L); cbn [Fst Snd]; split.
    - apply RegionFetchViewExt_write.
    - apply FetchViewExt_refl.
    - apply RegionFetchViewExt_refl.
    - apply IH.
  Qed.

  Lemma RegionSnapshotOK_write :
    forall r fwc x w, RegionSnapshotOK r fwc x -> RegionSnapshotOK r fwc (RegionWriteS r x w).
  Proof.
    intros r fwc; unfold RegionSnapshotOK, RegionWriteS, memRegionTree; destruct (regionKind r); intros x w H;
      [| exact I].
    cbn [Fst Snd length]; lia.
  Qed.

  Lemma SnapshotOK_specWrite :
    forall l fwcs L w ms, SnapshotOK fwcs l ms -> SnapshotOK fwcs l (specWriteLine l L w ms).
  Proof.
    induction l as [| r rs IH]; intros fwcs L w ms H; cbn [specWriteLine SnapshotOK] in *; [exact I |].
    destruct H as [H0 H1]; destruct (isRegionAddrB r L); cbn [Fst Snd].
    - split; [exact (RegionSnapshotOK_write _ _ _ _ H0) | exact H1].
    - split; [exact H0 | exact (IH _ _ _ _ H1)].
  Qed.

  Lemma RegionWriteS_custom : forall r, isCustomR r -> forall x w, RegionWriteS r x w = x.
  Proof.
    intros r; unfold RegionWriteS, isCustomR, memRegionTree; destruct (regionKind r); intros Hc x w;
      [contradiction | reflexivity].
  Qed.

  Lemma regionStateAt_specWrite :
    forall l idx r0 (pf : nth_error l idx = Some r0) L w ms, isCustomR r0 ->
      regionStateAt memRegionTree idx l r0 pf (specWriteLine l L w ms) = regionStateAt memRegionTree idx l r0 pf ms.
  Proof.
    induction l as [| r rs IH]; intros [| i'] r0 pf L w ms Hc; try discriminate pf; cbn [specWriteLine].
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct (isRegionAddrB r0 L); cbn [Fst]; [rewrite (RegionWriteS_custom r0 Hc); reflexivity | reflexivity].
    - cbn [regionStateAt].
      destruct (isRegionAddrB r L); cbn [Fst Snd]; [reflexivity | apply IH; exact Hc].
  Qed.
End SpecWrite.

(* --- 3. The Same Write on Both Sides --- *)

Section WriteBoth.
  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* The region holding line `L` sent write `w` (accepted iff `rdy`); the others are unchanged *)
  Definition RegionWriteI (r : MemRegion) (w : type LineWriteRq) (rdy : bool)
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y y' => y' = wrRqSent r y w rdy
    | CustomMem _ _ _ _ => fun _ _ => False
    end.

  Fixpoint WriteAtL (L : type Addr) (w : type LineWriteRq) (rdy : bool) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> Prop with
    | [] => fun mi mi' => mi' = mi
    | r :: rs => fun mi mi' =>
        if isRegionAddrB r L then RegionWriteI r w rdy mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)
        else mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\ WriteAtL L w rdy rs mi.(Snd).(Fst) mi'.(Snd).(Fst)
    end.

  Lemma WriteAtL_none :
    forall L w rdy l mi mi', lineKind l L = None -> WriteAtL L w rdy l mi mi' -> mi' = mi.
  Proof.
    intros L w rdy; induction l as [| r rs IH]; intros mi mi' Hk H; cbn [WriteAtL lineKind] in *; [exact H |].
    destruct (isRegionAddrB r L); [discriminate Hk |].
    destruct H as [H0 [H1 H2]].
    apply prod_ext; [exact H0 |]; apply prod_ext; [exact (IH _ _ Hk H2) | exact H1].
  Qed.

  (* The port predicate of `PortsWriteStaged L w` *)
  Definition wStagedP (L : type Addr) (w : type LineWriteRq) : forall r, ExtI r -> Prop :=
    fun r y => extDataQuiet r y /\
               (if isRegionAddrB r L then extPortRq r y = someWrite w else optValid (extPortRq r y) = false).

  Lemma wrRqStep_staged :
    forall L w l mi mi', lineUnique l L -> AllPorts (wStagedP L w) l mi -> WrRqPortStepL l mi mi' ->
      mi' = mi \/ exists rdy, WriteAtL L w rdy l mi mi'.
  Proof.
    intros L w; induction l as [| r rs IH]; intros mi mi' Hu H Hst; [destruct Hst |].
    cbn [lineUnique] in Hu; cbn [AllPorts] in H; cbn [WrRqPortStepL] in Hst; cbn [WriteAtL].
    destruct H as [H0 H1].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - unfold RegionPort, wStagedP in H0; cbv beta in H0.
      destruct (isRegionAddrB r L) eqn:Em.
      + assert (Hex : exists rdy, RegionWriteI r w rdy mi.(Fst) mi'.(Fst)).
        { revert H0 Hs; generalize (mi.(Fst)) (mi'.(Fst)).
          unfold RegionWrRqStep, RegionWriteI, implMemRegionTree.
          destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs; [| contradiction].
          destruct H0 as [_ Hp]; destruct (portRq_someWrite _ _ _ Hp) as [Hw Ew].
          destruct Hs as [[Hf _] | [_ [rdy Ey]]]; [rewrite Hw in Hf; discriminate Hf |].
          exists rdy; rewrite Ey, Ew; reflexivity. }
        destruct Hex as [rdy Hr]; right; exists rdy; split; [exact Hr | exact Ht].
      + left; apply prod_ext; [| exact Ht].
        revert H0 Hs; generalize (mi.(Fst)) (mi'.(Fst)).
        unfold RegionWrRqStep, implMemRegionTree.
        destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs; [| contradiction].
        destruct H0 as [_ Hp]; pose proof (portRqIsWrite_invalid _ _ Hp) as Hw.
        destruct Hs as [[_ Ey] | [Hb _]]; [exact Ey | rewrite Hw in Hb; discriminate Hb].
    - destruct (isRegionAddrB r L) eqn:Em.
      + left; apply prod_ext; [exact Hf |]; apply prod_ext; [| exact Ht].
        destruct (IH _ _ (lineKind_none_unique rs L Hu) H1 Hrest) as [E | [rdy Hw]]; [exact E |].
        exact (WriteAtL_none _ _ _ _ _ _ Hu Hw).
      + destruct (IH _ _ Hu H1 Hrest) as [E | [rdy Hw]].
        * left; apply prod_ext; [exact Hf |]; apply prod_ext; [exact E | exact Ht].
        * right; exists rdy; split; [exact Hf | split; [exact Ht | exact Hw]].
  Qed.

  (* Port predicates that ignore the write traces and `portRq` are kept *)
  Lemma AllPorts_writeAt :
    forall (P : forall r, ExtI r -> Prop), (forall r y w rdy, P r (wrRqSent r y w rdy) = P r y) ->
      forall L w rdy l mi mi', WriteAtL L w rdy l mi mi' -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP L w rdy; induction l as [| r rs IH]; intros mi mi' Hw; cbn [WriteAtL] in Hw; [rewrite Hw; reflexivity |].
    cbn [AllPorts].
    destruct (isRegionAddrB r L).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; f_equal.
      revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionWriteI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hw0; [| contradiction].
      subst y'; apply HP.
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf, (IH _ _ Hrest); reflexivity.
  Qed.

  (* The same for a write that was not accepted, for predicates that ignore only that *)
  Lemma AllPorts_writeAt_false :
    forall (P : forall r, ExtI r -> Prop), (forall r y w, P r (wrRqSent r y w false) = P r y) ->
      forall L w l mi mi', WriteAtL L w false l mi mi' -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP L w; induction l as [| r rs IH]; intros mi mi' Hw; cbn [WriteAtL] in Hw; [rewrite Hw; reflexivity |].
    cbn [AllPorts].
    destruct (isRegionAddrB r L).
    - destruct Hw as [Hw0 Ht]; rewrite Ht; f_equal.
      revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionWriteI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hw0; [| contradiction].
      subst y'; apply HP.
    - destruct Hw as [Hf [_ Hrest]]; rewrite Hf, (IH _ _ Hrest); reflexivity.
  Qed.

  (* Device (CustomMem) positions are untouched by a write-port step *)
  Lemma regionStateAt_writeAt :
    forall L w rdy l j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree l)),
      WriteAtL L w rdy l mi mi' -> isCustomR r0 ->
      regionStateAt implMemRegionTree j l r0 pf mi' = regionStateAt implMemRegionTree j l r0 pf mi.
  Proof.
    intros L w rdy; induction l as [| r rs IH]; intros [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [WriteAtL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct (isRegionAddrB r0 L); [| destruct H as [Hf _]; rewrite Hf; reflexivity].
      exfalso; destruct H as [Hw0 _]; revert Hw0; generalize (mi'.(Fst)) (mi.(Fst));
        unfold RegionWriteI, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt].
      destruct (isRegionAddrB r L).
      + destruct H as [_ Hs]; rewrite Hs; reflexivity.
      + destruct H as [_ [_ Hrest]]; exact (IH j' r0 pf _ _ Hrest Hc).
  Qed.

  Definition quietP : forall r, ExtI r -> Prop :=
    fun r y => optValid (extPortRq r y) = false /\ extDataQuiet r y.

  Lemma quiet_none :
    forall L w l (mi : TS (implRegionsTree l)), lineKind l L = None -> AllPorts (wStagedP L w) l mi -> AllPorts quietP l mi.
  Proof.
    intros L w; induction l as [| r rs IH]; intros mi Hk H; [exact I |].
    cbn [lineKind] in Hk; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct (isRegionAddrB r L) eqn:Em; [discriminate Hk |].
    split; [| exact (IH _ Hk H1)].
    revert H0; generalize (mi.(Fst)); unfold RegionPort, wStagedP, quietP, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
    destruct H0 as [Hq Hp]; rewrite Em in Hp; exact (conj Hp Hq).
  Qed.

  (* After the staged write was accepted, every port is quiet *)
  Lemma quiet_writeAt :
    forall L w l mi mi', lineUnique l L -> AllPorts (wStagedP L w) l mi -> WriteAtL L w true l mi mi' ->
      AllPorts quietP l mi'.
  Proof.
    intros L w; induction l as [| r rs IH]; intros mi mi' Hu H Hw; [exact I |].
    cbn [lineUnique] in Hu; cbn [AllPorts] in H |- *; cbn [WriteAtL] in Hw; destruct H as [H0 H1].
    destruct (isRegionAddrB r L) eqn:Em.
    - destruct Hw as [Hw0 Ht]; rewrite Ht; split; [| exact (quiet_none L w rs _ Hu H1)].
      revert H0 Hw0; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, wStagedP, quietP, RegionWriteI, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hw0; [| contradiction].
      subst y'; destruct H0 as [Hq _]; split; [reflexivity | exact Hq].
    - destruct Hw as [Hf [Ht Hrest]]; rewrite Hf; split.
      + revert H0; generalize (mi.(Fst)); unfold RegionPort, wStagedP, quietP, implMemRegionTree.
        destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y H0; [| exact I].
        destruct H0 as [Hq Hp]; rewrite Em in Hp; exact (conj Hp Hq).
      + exact (IH _ _ Hu H1 Hrest).
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_write :
    forall i r x (y y' : TS (implMemRegionTree r)) w rdy,
      RegionWriteI r w rdy y y' -> RegionRelAt cp pp i r x y ->
      RegionRelAt cp pp i r (if rdy then RegionWriteS r x w else x) y'.
  Proof.
    intros i r x y y' w rdy; unfold RegionRelAt, RegionWriteI, RegionWriteS, implMemRegionTree, memRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros Hs Hr; [| contradiction].
    subst y'; destruct Hr as [E1 [E2 [E3 E4]]].
    destruct rdy; unfold ExtRel; rewrite implAccWrites_wrRqSent; cbn [Fst Snd].
    - split; [rewrite E1; reflexivity | exact (conj E2 (conj E3 E4))].
    - exact (conj E1 (conj E2 (conj E3 E4))).
  Qed.

  Lemma MemRelPost_write :
    forall L w rdy l i ms mi mi', WriteAtL L w rdy l mi mi' -> MemRelPost cp pp i l ms mi ->
      MemRelPost cp pp i l (if rdy then specWriteLine l L w ms else ms) mi'.
  Proof.
    intros L w rdy; induction l as [| r rs IH]; intros i ms mi mi' Hw H; [exact I |].
    cbn [WriteAtL] in Hw; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct (isRegionAddrB r L) eqn:Em.
    - destruct Hw as [Hw0 Ht]; rewrite Ht.
      destruct rdy; cbn [specWriteLine]; rewrite ?Em; cbn [Fst Snd].
      + split; [exact (RegionRelAt_write _ _ _ _ _ _ true Hw0 Hr) | exact Hl].
      + split; [exact (RegionRelAt_write _ _ _ _ _ _ false Hw0 Hr) | exact Hl].
    - destruct Hw as [Hf [Ht Hrest]]; rewrite Hf.
      pose proof (IH _ _ _ _ Hrest Hl) as Hl'.
      destruct rdy; cbn [specWriteLine]; [rewrite Em |]; cbn [Fst Snd]; exact (conj Hr Hl').
  Qed.

  Lemma MemRelPre_write :
    forall L w rdy sRev iRev post l i ms mi mi', isCustomR iRev ->
      isRegionAddrB sRev L = isRegionAddrB iRev L ->
      WriteAtL L w rdy (l ++ iRev :: post) mi mi' -> MemRelPre cp pp i l sRev iRev post ms mi ->
      MemRelPre cp pp i l sRev iRev post (if rdy then specWriteLine (l ++ sRev :: post) L w ms else ms) mi'.
  Proof.
    intros L w rdy sRev iRev post; induction l as [| r rs IH]; intros i ms mi mi' Hc Ea Hw H.
    - cbn [app WriteAtL] in Hw; cbn [MemRelPre] in H |- *.
      destruct (isRegionAddrB iRev L) eqn:Em.
      + exfalso; destruct Hw as [Hw0 _]; revert Hw0; generalize (mi.(Fst)) (mi'.(Fst)).
        unfold RegionWriteI, isCustomR, implMemRegionTree in *; destruct (regionKind iRev); [contradiction | intros _ _ F; exact F].
      + destruct Hw as [_ [_ Hrest]].
        pose proof (MemRelPost_write _ _ _ _ _ _ _ _ Hrest H) as H'.
        destruct rdy; cbn [app specWriteLine]; [rewrite Ea |]; cbn [Fst Snd]; exact H'.
    - cbn [app WriteAtL] in Hw; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct (isRegionAddrB r L) eqn:Em.
      + destruct Hw as [Hw0 Ht]; rewrite Ht.
        destruct rdy; cbn [app specWriteLine]; rewrite ?Em; cbn [Fst Snd].
        * split; [exact (RegionRelAt_write _ _ _ _ _ _ true Hw0 Hr) | exact Hl].
        * split; [exact (RegionRelAt_write _ _ _ _ _ _ false Hw0 Hr) | exact Hl].
      + destruct Hw as [Hf [Ht Hrest]]; rewrite Hf.
        pose proof (IH _ _ _ _ Hc Ea Hrest Hl) as Hl'.
        destruct rdy; cbn [app specWriteLine]; [rewrite Em |]; cbn [Fst Snd]; exact (conj Hr Hl').
  Qed.
End WriteBoth.

(* --- 4. Line Contents after a Write --- *)

Section WriteContent.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma applyLineWriteRq_other :
    forall L' (w : type LineWriteRq) rp, Zmod.eqb w.(Fst) L' = false -> applyLineWriteRq L' w rp = rp.
  Proof. intros L' w rp H; unfold applyLineWriteRq; cbv zeta; rewrite H; reflexivity. Qed.

  Lemma isRegionAddrB_diff :
    forall r L L', isRegionAddrB r L = true -> isRegionAddrB r L' = false -> Zmod.eqb L L' = false.
  Proof.
    intros r L L' H1 H2; destruct (Zmod.eqb L L') eqn:E; [| reflexivity].
    apply Zmod.eqb_eq in E; subst L'; rewrite H1 in H2; discriminate H2.
  Qed.

  Lemma RegionLineContent_write :
    forall r x (w : type LineWriteRq) L',
      match r.(regionKind) with ExternalMem => true | CustomMem _ _ _ _ => false end = true ->
      RegionLineContent initLine r (RegionWriteS r x w) L' = applyLineWriteRq L' w (RegionLineContent initLine r x L').
  Proof.
    intros r; unfold RegionLineContent, RegionWriteS, memRegionTree.
    destruct (regionKind r); intros x w L' Hk; [reflexivity | discriminate Hk].
  Qed.

  (* After write `w` of line `L` (an ExternalMem line), every line reads as `w` applied *)
  Lemma lineContent_specWrite :
    forall l L (w : type LineWriteRq) ms L',
      w.(Fst) = L -> lineKind l L = Some true -> lineUnique l L ->
      lineContent initLine l (specWriteLine l L w ms) L' = applyLineWriteRq L' w (lineContent initLine l ms L').
  Proof.
    induction l as [| r rs IH]; intros L w ms L' Ew Hk Hu; [discriminate Hk |].
    cbn [lineKind lineUnique] in Hk, Hu; cbn [specWriteLine lineContent].
    destruct (isRegionAddrB r L) eqn:Em.
    - injection Hk as Hk; cbn [Fst Snd].
      destruct (isRegionAddrB r L') eqn:Em'.
      + apply RegionLineContent_write; exact Hk.
      + rewrite applyLineWriteRq_other; [reflexivity |].
        rewrite Ew; exact (isRegionAddrB_diff r L L' Em Em').
    - cbn [Fst Snd].
      destruct (isRegionAddrB r L') eqn:Em'.
      + rewrite applyLineWriteRq_other; [reflexivity |].
        rewrite Ew; destruct (Zmod.eqb L L') eqn:E; [| reflexivity].
        apply Zmod.eqb_eq in E; subst L'; rewrite Em in Em'; discriminate Em'.
      + exact (IH L w _ L' Ew Hk Hu).
  Qed.
End WriteContent.
