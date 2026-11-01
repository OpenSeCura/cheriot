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
From Cheriot.Proof Require Import ImplSpec RefFetch RefMemStep.

Import ListNotations.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4: the fetch response ports (`implExternalFetchLineRpPort`, one per ExternalMem
 * region).
 * 1. One port step (`fetchRpPort_cases`): nothing (the region's fetch buffer is full), a `false`
 *    valid (no response), or a response taken into the fetch buffer. The env makes a response
 *    one the region's memory may give for the oldest unanswered accepted fetch
 *    (`implFetchLineAddr`). Over the region list one ExternalMem position steps
 *    (`fetchRpPorts_step`).
 * 2. A response the impl memory may give is one the spec may fetch (`ImplLineAllowed`,
 *    `lineAllowed_pre`): the spec's writes are the impl's accepted writes (`ExtRel`).
 * 3. The spec stutters. The step changes only the fetch side of one region, so the port
 *    predicates that ignore it are unchanged (`FetchRpInsensitive`), and only `FetchRespRel` and
 *    the handshake invariant need work (`RefRelG_fetchRp_frame`, `stepOK_fetchLineRpPorts`). *)

(* --- 1. One Fetch Response Port Step --- *)

Section FetchRpPortRegion.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* The region's fetch buffer, the fetch responses it received, and its fence.i acks *)
  Definition fetchRdRp r (y : ExtI r) : type (Option LineReadRp) := y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst).
  Definition fetchRcv r (y : ExtI r) : list (type LineReadRp) := y.(Fst).(Fst).(Snd).(Fst).
  Definition fetchAcks r (y : ExtI r) : list bool := y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst).

  (* The region after its fetch port saw no response *)
  Definition fetchRpNone r (y : ExtI r) : ExtI r :=
    (y.(Fst) ,, ((y.(Snd).(Fst).(Fst) ,, ((false :: y.(Snd).(Fst).(Snd).(Fst)) ,, y.(Snd).(Fst).(Snd).(Snd))) ,,
                 y.(Snd).(Snd))).

  (* The region after its fetch port took the response `rp` into the fetch buffer (`z`: the value
   * sent on lineReadRpReady) *)
  Definition fetchRpTaken r (y : ExtI r) (rp : type LineReadRp) (z : type (Bit 0)) : ExtI r :=
    (((y.(Fst).(Fst).(Fst) ,, ((rp :: y.(Fst).(Fst).(Snd).(Fst)) ,, y.(Fst).(Fst).(Snd).(Snd))) ,, y.(Fst).(Snd)) ,,
     ((y.(Snd).(Fst).(Fst) ,, ((true :: y.(Snd).(Fst).(Snd).(Fst)) ,, ((z :: y.(Snd).(Fst).(Snd).(Snd).(Fst)) ,,
        ((rp ,, (true ,, tt)) ,, y.(Snd).(Fst).(Snd).(Snd).(Snd).(Snd))))) ,, y.(Snd).(Snd))).

  Local Opaque liftAction.

  Lemma fetchRpPort_cases :
    forall r fwc (eR : Env (implExternalMemRegionTree r)) (y y' : ExtI r) v,
      (forall s x w, eR s x w -> implExtRegionEnv initLine r fwc s x w) ->
      SemAction eR (@implExternalFetchLineRpPort r type) y y' v ->
      y' = y \/
      (optValid (fetchRdRp r y) = false /\ y' = fetchRpNone r y) \/
      (optValid (fetchRdRp r y) = false /\ (length (fetchRcv r y) < length (implFetchAccRqs r y))%nat /\
       exists rp z, EnvFetchLineReadRpAt (initLine r) fwc (fetchAcks r y) (implAccWrites r y) (implFetchLineAddr r y) rp /\
                    y' = fetchRpTaken r y rp z).
  Proof.
    intros r fwc eR
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [[if_rdRpData [if_rdRpVal []]] []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           y' v HE Hsem.
    unfold implExternalFetchLineRpPort, implExternalFetchLineReadRp, externalFetchLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem; cbn in Hsem.
    destruct if_rdRpVal; cbn in Hsem.
    - left; destruct Hsem as [<- _]; reflexivity.
    - rewrite evalActionPropGen_liftAction in Hsem; cbn in Hsem.
      destruct Hsem as [valid [Hvenv HvalidBranch]].
      destruct valid; cbn in HvalidBranch.
      + rewrite !evalActionPropGen_liftAction in HvalidBranch; cbn in HvalidBranch.
        destruct HvalidBranch as [rp [Hrpenv HrpBranch]].
        rewrite evalActionPropGen_liftAction in HrpBranch; cbn in HrpBranch.
        destruct HrpBranch as [<- _].
        right; right; split; [reflexivity |]; split.
        * unfold subEnv, cast_recv_inv in Hvenv; apply HE in Hvenv.
          unfold implExtRegionEnv, implExtFetchEnv, extRegionEnvCtx, extFetchEnvCtx in Hvenv.
          cbn -[eq_rect EnvFetchLineReadRpValidConstraint] in Hvenv.
          rewrite ?eq_rect_Kind_refl in Hvenv.
          exact (Hvenv eq_refl).
        * eexists rp, _; split; [| reflexivity].
          unfold subEnv, cast_recv_inv in Hrpenv; apply HE in Hrpenv.
          unfold implExtRegionEnv, implExtFetchEnv, extRegionEnvCtx, extFetchEnvCtx in Hrpenv.
          cbn -[eq_rect EnvFetchLineReadRpAt implAccWrites implFetchLineAddr] in Hrpenv.
          rewrite ?eq_rect_Kind_refl in Hrpenv.
          exact Hrpenv.
      + destruct HvalidBranch as [<- _].
        right; left; split; reflexivity.
  Qed.

  (* One region's fetch response port step *)
  Definition RegionFetchRpStep (fwc : nat -> nat) (r : MemRegion)
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y y' =>
        y' = y \/
        (optValid (fetchRdRp r y) = false /\ y' = fetchRpNone r y) \/
        (optValid (fetchRdRp r y) = false /\ (length (fetchRcv r y) < length (implFetchAccRqs r y))%nat /\
         exists rp z, EnvFetchLineReadRpAt (initLine r) fwc (fetchAcks r y) (implAccWrites r y) (implFetchLineAddr r y) rp /\
                      y' = fetchRpTaken r y rp z)
    | CustomMem _ _ _ _ => fun _ _ => False
    end.

  (* One position of the list takes a fetch response port step, the others are unchanged *)
  Fixpoint FetchRpPortStepL (fwcs : nat -> nat -> nat) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> Prop with
    | [] => fun _ _ => False
    | r :: rs => fun mi mi' =>
        (RegionFetchRpStep (fwcs 0%nat) r mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)) \/
        (mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\
         FetchRpPortStepL (fun i => fwcs (S i)) rs mi.(Snd).(Fst) mi'.(Snd).(Fst))
    end.

  Lemma fetchRpPorts_step :
    forall l fwcs (aI : forall ty, Action ty (implRegionsTree l) (Bit 0)) env mi mi' v,
      ImplEnvOK initLine l fwcs env ->
      In aI (implCollectFetchLineRpPorts l) ->
      SemAction env (aI type) mi mi' v -> FetchRpPortStepL fwcs l mi mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs aI env mi mi' v HE Hin Hsem; [destruct Hin |].
    unfold implCollectFetchLineRpPorts, implCollectRegionActions in Hin; cbn [genCollectRegionActions] in Hin.
    apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as [f [<- Hf]].
    - left; apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
      split; [| reflexivity]; cbn [writeSubTreeState readSubTreeState] in Hy' |- *.
      pose proof (ImplEnvOK_head initLine r rs fwcs env mi HE) as HE0.
      revert f Hf Hy' HE0; destruct r as [nm bs sz kd sn im ba sa]; destruct kd;
        cbn [implMemRegionFetchLineRpPorts regionKind In RegionFetchRpStep implRegionEnv];
        intros f Hf Hy' HE0; try contradiction.
      destruct Hf as [<- | []].
      exact (fetchRpPort_cases _ _ _ _ _ _ HE0 Hy').
    - right; apply SemAction_liftAction_iff in Hsem as [z' [Hz' ->]].
      split; [reflexivity | split; [reflexivity |]].
      exact (IH _ f _ _ _ _ (ImplEnvOK_tail initLine r rs fwcs env mi HE) Hf Hz').
  Qed.

  (* --- Frame Facts of a Step --- *)

  (* A port predicate that reads neither the fetch responses received nor the impl's fetch side *)
  Definition FetchRpInsensitive (P : forall r, ExtI r -> Prop) : Prop :=
    forall r (y y' : ExtI r),
      y'.(Fst).(Fst).(Fst) = y.(Fst).(Fst).(Fst) -> y'.(Fst).(Fst).(Snd).(Snd) = y.(Fst).(Fst).(Snd).(Snd) ->
      y'.(Fst).(Snd) = y.(Fst).(Snd) -> y'.(Snd).(Snd) = y.(Snd).(Snd) ->
      P r y' = P r y.

  Lemma AllPorts_fetchRpStep :
    forall P, FetchRpInsensitive P ->
      forall l fwcs mi mi', FetchRpPortStepL fwcs l mi mi' -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP; induction l as [| r rs IH]; intros fwcs mi mi' Hst; [destruct Hst |].
    cbn [FetchRpPortStepL] in Hst; cbn [AllPorts].
    destruct Hst as [[Hr Hs] | [Hf [Hs Hl]]].
    - rewrite Hs; f_equal.
      revert Hr; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionFetchRpStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hr; [| contradiction].
      destruct Hr as [-> | [[_ ->] | [_ [_ [rp [z [_ ->]]]]]]]; [reflexivity | apply HP; reflexivity ..].
    - rewrite Hf, (IH _ _ _ Hl); reflexivity.
  Qed.

  (* Device (CustomMem) positions are untouched *)
  Lemma regionStateAt_fetchRpStep :
    forall l fwcs j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree l)),
      FetchRpPortStepL fwcs l mi mi' -> isCustomR r0 ->
      regionStateAt implMemRegionTree j l r0 pf mi' = regionStateAt implMemRegionTree j l r0 pf mi.
  Proof.
    induction l as [| r rs IH]; intros fwcs [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [FetchRpPortStepL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct H as [[Hs _] | [Hf _]]; [| rewrite Hf; reflexivity].
      exfalso; revert Hs; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionFetchRpStep, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt].
      destruct H as [[_ Hs] | [_ [_ Hrest]]].
      + rewrite Hs; reflexivity.
      + exact (IH _ j' r0 pf _ _ Hrest Hc).
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_fetchRpStep :
    forall fwc i r x (y y' : TS (implMemRegionTree r)),
      RegionFetchRpStep fwc r y y' -> RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r x y'.
  Proof.
    intros fwc i r x y y'; unfold RegionRelAt, RegionFetchRpStep, implMemRegionTree, memRegionTree in *.
    revert x y y'; destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind];
      intros x y y' Hs Hr; [| contradiction].
    destruct Hs as [-> | [[_ ->] | [_ [_ [rp [z [_ ->]]]]]]]; exact Hr.
  Qed.

  Lemma MemRelPost_fetchRpStep :
    forall l fwcs i ms mi mi', FetchRpPortStepL fwcs l mi mi' ->
      MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l ms mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs i ms mi mi' Hst H; [destruct Hst |].
    cbn [FetchRpPortStepL] in Hst; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - rewrite Ht; split; [exact (RegionRelAt_fetchRpStep _ _ _ _ _ _ Hs Hr) | exact Hl].
    - rewrite Hf; split; [exact Hr | exact (IH _ _ _ _ _ Hrest Hl)].
  Qed.

  Lemma MemRelPre_fetchRpStep :
    forall sRev iRev post l fwcs i ms mi mi', isCustomR iRev ->
      FetchRpPortStepL fwcs (l ++ iRev :: post) mi mi' ->
      MemRelPre cp pp i l sRev iRev post ms mi -> MemRelPre cp pp i l sRev iRev post ms mi'.
  Proof.
    intros sRev iRev post; induction l as [| r rs IH]; intros fwcs i ms mi mi' Hc Hst H.
    - cbn [app FetchRpPortStepL] in Hst; cbn [MemRelPre] in H |- *.
      destruct Hst as [[Hs _] | [_ [_ Hrest]]]; [| exact (MemRelPost_fetchRpStep _ _ _ _ _ _ Hrest H)].
      exfalso; revert Hs; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionFetchRpStep, isCustomR, implMemRegionTree in *.
      destruct (regionKind iRev); [contradiction | intros y' y Hy; exact Hy].
    - cbn [app FetchRpPortStepL] in Hst; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
      + rewrite Ht; split; [exact (RegionRelAt_fetchRpStep _ _ _ _ _ _ Hs Hr) | exact Hl].
      + rewrite Hf; split; [exact Hr | exact (IH _ _ _ _ _ Hc Hrest Hl)].
  Qed.

  (* The handshake invariant and the fence.i count invariant are kept *)
  Lemma handshake_fetchRpStep :
    forall l fwcs mi mi', FetchRpPortStepL fwcs l mi mi' ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) l mi ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) l mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs mi mi' Hst H; [destruct Hst |].
    cbn [FetchRpPortStepL] in Hst; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - rewrite Ht; split; [| exact H1].
      revert H0 Hs; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionFetchRpStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs; [| exact I].
      destruct H0 as [Hh Hf].
      destruct Hs as [-> | [[Hv ->] | [Hv [_ [rp [z [_ ->]]]]]]].
      + exact (conj Hh Hf).
      + split; [| exact Hf].
        unfold ImplExternalRegionHandshakeInv in Hh |- *; cbn [fetchRpNone Fst Snd count_true] in Hh |- *.
        exact Hh.
      + split; [| exact Hf].
        unfold ImplExternalRegionHandshakeInv in Hh |- *; cbn [fetchRpTaken Fst Snd length count_true hd] in Hh |- *.
        destruct Hh as [H1' [H2 [_ [H4 H5]]]].
        refine (conj (f_equal S H1') (conj (f_equal S H2) (conj _ (conj H4 H5)))).
        intros _; split; [reflexivity | intro Hnil; discriminate Hnil].
    - rewrite Hf; split; [exact H0 | exact (IH _ _ _ Hrest H1)].
  Qed.
End FetchRpPortRegion.

(* --- 2. Responses the Impl Memory May Give Are Responses the Spec May Fetch --- *)

Section LineAllowedImpl.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  (* What the impl env allows as a fetch response for line `L` of a region (by the region's
   * accepted writes and acks); the router decides by the first region holding `L` *)
  Definition ImplRegionLineAllowed (r : MemRegion) (fwc : nat -> nat)
    : TS (implMemRegionTree r) -> type Addr -> type LineReadRp -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> type Addr -> type LineReadRp -> Prop with
    | ExternalMem => fun y L rp => EnvFetchLineReadRpAt (initLine r) fwc (fetchAcks r y) (implAccWrites r y) L rp
    | CustomMem _ _ _ _ => fun _ _ _ => True
    end.

  Fixpoint ImplLineAllowed (fwcs : nat -> nat -> nat) (l : list MemRegion)
    : TS (implRegionsTree l) -> type Addr -> type LineReadRp -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> type Addr -> type LineReadRp -> Prop with
    | [] => fun _ _ rp => rp = getDefault LineReadRp
    | r :: rs => fun mi L rp =>
        if isRegionAddrB r L then ImplRegionLineAllowed r (fwcs 0%nat) mi.(Fst) L rp
        else ImplLineAllowed (fun i => fwcs (S i)) rs mi.(Snd).(Fst) L rp
    end.

  (* The env only reads the acks through their count *)
  Lemma EnvFetchLineReadRpAt_acks :
    forall il fwc acks1 acks2 ws L rp,
      count_true acks1 = count_true acks2 ->
      EnvFetchLineReadRpAt il fwc acks2 ws L rp -> EnvFetchLineReadRpAt il fwc acks1 ws L rp.
  Proof.
    intros il fwc acks1 acks2 ws L rp E H.
    unfold EnvFetchLineReadRpAt, fenceISnapshotCount in *; rewrite E; exact H.
  Qed.

  Variables cp pp : nat.

  Lemma lineAllowed_region :
    forall i r fwc x (y : TS (implMemRegionTree r)) L rp,
      RegionRelAt cp pp i r x y -> ImplRegionLineAllowed r fwc y L rp -> RegionLineAllowed initLine r fwc x L rp.
  Proof.
    intros i r fwc; unfold RegionRelAt, ImplRegionLineAllowed, RegionLineAllowed, memRegionTree, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros x y L rp Hr H; [| exact I].
    destruct Hr as [Ew [_ [_ Ea]]].
    unfold fetchAcks in H; rewrite <- Ew in H.
    exact (EnvFetchLineReadRpAt_acks _ _ _ _ _ _ _ Ea H).
  Qed.

  Lemma lineAllowed_post :
    forall l i fwcs ms mi L rp,
      MemRelPost cp pp i l ms mi -> ImplLineAllowed fwcs l mi L rp -> LineAllowed initLine fwcs l ms L rp.
  Proof.
    induction l as [| r rs IH]; intros i fwcs ms mi L rp Hm H; cbn [ImplLineAllowed LineAllowed MemRelPost] in *.
    - exact H.
    - destruct Hm as [Hr Hl]; unfold isRegionAddrB in H.
      destruct (evalExpr (isRegionAddr r (Var type Addr L))).
      + exact (lineAllowed_region _ _ _ _ _ _ _ Hr H).
      + exact (IH _ _ _ _ L rp Hl H).
  Qed.

  (* The spec and impl revoker regions sit at the same addresses and are CustomMem *)
  Lemma lineAllowed_pre :
    forall sRev iRev post l i fwcs ms mi L rp,
      isCustomR sRev -> isRegionAddrB sRev L = isRegionAddrB iRev L ->
      MemRelPre cp pp i l sRev iRev post ms mi ->
      ImplLineAllowed fwcs (l ++ iRev :: post) mi L rp -> LineAllowed initLine fwcs (l ++ sRev :: post) ms L rp.
  Proof.
    intros sRev iRev post; induction l as [| r rs IH]; intros i fwcs ms mi L rp Hc Ea Hm H.
    - cbn [app ImplLineAllowed LineAllowed MemRelPre] in *.
      change (evalExpr (isRegionAddr sRev (Var type Addr L))) with (isRegionAddrB sRev L).
      rewrite Ea in *; destruct (isRegionAddrB iRev L).
      + revert Hc; generalize (ms.(Fst)); unfold isCustomR, RegionLineAllowed, memRegionTree.
        destruct (regionKind sRev); [intros _ [] | intros _ _; exact I].
      + exact (lineAllowed_post _ _ _ _ _ L rp Hm H).
    - cbn [app ImplLineAllowed LineAllowed MemRelPre] in *.
      destruct Hm as [Hr Hl]; unfold isRegionAddrB in H.
      destruct (evalExpr (isRegionAddr r (Var type Addr L))).
      + exact (lineAllowed_region _ _ _ _ _ _ _ Hr H).
      + exact (IH _ _ _ _ L rp Hc Ea Hl H).
  Qed.
End LineAllowedImpl.

(* --- 3. FetchRespRel after a Step --- *)

Section FetchResp.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* What `FetchRespRel` asks of one ExternalMem region, with the fetchBuf entries `E r` of its
   * lines, the liveness test `live` and the spec's line check `Q` as parameters *)
  Definition FRP (E : MemRegion -> list (type FetchBufEntry)) (live : type FetchBufEntry -> bool)
    (Q : type Addr -> type LineReadRp -> Prop) : forall r, ExtI r -> Prop :=
    fun r y =>
      let rcv := y.(Fst).(Fst).(Snd).(Fst) in
      let rdRp := y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst) in
      exists C, implFetchAccRqs r y = (rev (map (fun f => lineAddrOf (fbPcAddr f)) (E r)) ++ C)%list /\
                (length C + (if optValid rdRp then 1 else 0))%nat = length rcv /\
                (optValid rdRp = true ->
                   exists f E', E r = f :: E' /\ (live f = true -> Q (lineAddrOf (fbPcAddr f)) (optData rdRp))).

  (* The next fetch response of a region is for its oldest fetchBuf entry *)
  Lemma fifoRq_head :
    forall (g : type FetchBufEntry -> type Addr) f E' C,
      fifoRq Zmod.zero ((rev (map g (f :: E')) ++ C)%list) (length C) = g f.
  Proof.
    intros g f E' C; unfold fifoRq.
    rewrite length_app, length_rev, length_map; cbn [length map rev].
    replace (S (length E') + length C - S (length C))%nat with (length E') by lia.
    rewrite <- app_assoc, app_nth2 by (rewrite length_rev, length_map; lia).
    rewrite length_rev, length_map, Nat.sub_diag; reflexivity.
  Qed.

  Lemma fifoRq_head' :
    forall (g : type FetchBufEntry -> type Addr) f E' C n,
      n = length C -> fifoRq Zmod.zero ((rev (map g (f :: E')) ++ C)%list) n = g f.
  Proof. intros g f E' C n ->; apply fifoRq_head. Qed.

  Lemma FRP_region :
    forall E live Q fwc r (y y' : TS (implMemRegionTree r)),
      (forall f, In f (E r) -> isRegionAddrB r (lineAddrOf (fbPcAddr f)) = true) ->
      (forall L rp, isRegionAddrB r L = true -> ImplRegionLineAllowed initLine r fwc y L rp -> Q L rp) ->
      RegionFetchRpStep initLine fwc r y y' ->
      RegionPort (FRP E live Q) r y -> RegionPort (FRP E live Q) r y'.
  Proof.
    intros E live Q fwc r; unfold RegionPort, RegionFetchRpStep, ImplRegionLineAllowed, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' HE HQ Hs H; [| exact I].
    destruct Hs as [-> | [[Hv ->] | [Hv [Hlt [rp [z [Henv ->]]]]]]].
    - exact H.
    - exact H.
    - unfold FRP in H |- *; cbv zeta in H |- *.
      destruct H as [C [HC1 [HC2 _]]].
      unfold fetchRdRp in Hv; rewrite Hv in HC2; cbv iota in HC2.
      assert (HCn : length (fetchRcv _ y) = length C)
        by (change (length C + 0 = length (fetchRcv _ y))%nat in HC2; lia).
      exists C; split; [exact HC1 | split].
      + change (length C + 1 = S (length (fetchRcv _ y)))%nat; rewrite HCn, Nat.add_1_r; reflexivity.
      + intros _.
        destruct (E _) as [| f E'] eqn:EE.
        * exfalso; rewrite HC1 in Hlt; cbn [map rev app] in Hlt; rewrite HCn in Hlt; exact (Nat.lt_irrefl _ Hlt).
        * exists f, E'; split; [first [reflexivity | exact EE] | intros _].
          change (Q (lineAddrOf (fbPcAddr f)) rp).
          apply HQ; [apply HE; first [left; reflexivity | rewrite EE; left; reflexivity] |].
          unfold implFetchLineAddr in Henv; rewrite HC1 in Henv.
          erewrite fifoRq_head' in Henv by (change (length (fetchRcv _ y) = length C); exact HCn).
          exact Henv.
  Qed.

  Lemma FRP_fetchRpStep :
    forall l fwcs E live Q (mi mi' : TS (implRegionsTree l)),
      (forall L, lineUnique l L) ->
      (forall r f, In f (E r) -> isRegionAddrB r (lineAddrOf (fbPcAddr f)) = true) ->
      (forall L rp, lineKind l L = Some true -> ImplLineAllowed initLine fwcs l mi L rp -> Q L rp) ->
      FetchRpPortStepL initLine fwcs l mi mi' ->
      AllPorts (FRP E live Q) l mi -> AllPorts (FRP E live Q) l mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs E live Q mi mi' Hu HE HQ Hst H; [destruct Hst |].
    cbn [FetchRpPortStepL] in Hst; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - rewrite Ht; split; [| exact H1].
      refine (FRP_region E live Q (fwcs 0%nat) r _ _ (HE r) _ Hs H0).
      intros L rp Hm Hal; apply HQ.
      + cbn [lineKind]; rewrite Hm.
        revert Hs; generalize (mi.(Fst)) (mi'.(Fst)); clear; unfold RegionFetchRpStep, implMemRegionTree.
        destruct (regionKind r); [intros; reflexivity | intros _ _ []].
      + cbn [ImplLineAllowed]; rewrite Hm; exact Hal.
    - rewrite Hf; split; [exact H0 |].
      refine (IH (fun i => fwcs (S i)) E live Q _ _ _ HE _ Hrest H1).
      + intros L; specialize (Hu L); cbn [lineUnique] in Hu.
        destruct (isRegionAddrB r L); [exact (lineKind_none_unique _ _ Hu) | exact Hu].
      + intros L rp Hk Hal; specialize (Hu L); cbn [lineUnique] in Hu.
        destruct (isRegionAddrB r L) eqn:Hm; [rewrite Hu in Hk; discriminate Hk |].
        apply HQ; cbn [lineKind ImplLineAllowed]; rewrite Hm; [exact Hk | exact Hal].
  Qed.
End FetchResp.

(* --- 4. The Fetch Response Ports Refine the Spec (it stutters) --- *)

Section FetchRpPorts.
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

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation NPMI := (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPMS := (Spec.np_mem pcAddrInit specRegions).

  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).

  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation FRESP := (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 initLine fwcs).
  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).

  Local Abbreviation UPD s1 mi' := (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd))).

  Local Ltac fetchins_tac :=
    let r0 := fresh "r" in let y0 := fresh "y" in let y1 := fresh "y" in
    intros r0 y0 y1 Q1 Q2 Q3 Q4; cbv beta zeta;
    unfold extPortRq, extDataQuiet, extDataOut, implDataAccRqs; rewrite ?Q1, ?Q2, ?Q3, ?Q4; reflexivity.

  (* A step that changes only the fetch side of the regions: the spec stutters *)
  Lemma RefRelG_fetchRp_frame :
    forall g (s1 s1' : IState) (s2 : SState) mi',
      s1' = UPD s1 mi' ->
      (forall P, FetchRpInsensitive P -> AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      iRevA s1' = iRevA s1 ->
      MEMC g s1' s2 -> FRESP s1' s2 ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1') ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 mi' E1 HP HR Hmem Hfr' Hhs H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    assert (Edm : iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                  iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
      by (rewrite E1; reflexivity).
    constructor.
    - rewrite E1; exact Hrf.
    - exact Hmem.
    - exact Hl.
    - exact Hrp.
    - exact He.
    - refine (AccessRel_frame_ports pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine
                g s1 s1' s2 s2 _ _ _ _ HR _ _ _ Edm eq_refl (fun L => eq_refl) Ha).
      + unfold PortsQuiet; apply HP; fetchins_tac.
      + intros L; unfold PortsReadStaged; apply HP; fetchins_tac.
      + intros L; unfold PortsReadOut; apply HP; fetchins_tac.
      + intros L rq; unfold PortsWriteStaged; apply HP; fetchins_tac.
      + rewrite E1; reflexivity.
      + rewrite E1; reflexivity.
      + rewrite E1; reflexivity.
    - unfold CnwbRel in *; rewrite Edm; exact Hc.
    - rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite HP by fetchins_tac; rewrite E1; exact Hf.
    - rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 _]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split; [rewrite E1; exact F6 | exact Hfr'].
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd _]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 | split; [rewrite E1; exact Wmd | exact Hhs]].
    - exact (RevokerRel_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine
               g g s1 s1' s2 s2 eq_refl eq_refl HR (fun L => eq_refl) Hrk).
  Qed.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Lemma iRegions_write' : forall (s1 : IState) mi', iRegionsA (UPD s1 mi') = mi'.
  Proof. reflexivity. Qed.

  (* The fetch response ports: the spec stutters; a response taken is one the spec may fetch *)
  Theorem stepOK_fetchLineRpPorts :
    forall act,
      In act (@fetchLineRpPorts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
      STEPOK act.
  Proof.
    intros act Hin s1 s1' s2 Hsem [g Hg].
    unfold fetchLineRpPorts, implMemCollectFetchLineRpPorts in Hin.
    rewrite map_map in Hin; apply in_map_iff in Hin as [f [<- Hf]]; cbv beta in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    apply SemAction_liftAction_iff in Hm' as [mi' [Hmi' Em]].
    pose proof (fetchRpPorts_step initLine implRegions fwcs f _ _ _ _
                  (implEnvOK_regions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                     initLine fwcs s1 _) Hf Hmi') as Hst.
    change (FetchRpPortStepL initLine fwcs implRegions (iRegionsA s1) mi') in Hst.
    assert (Es1 : s1' = UPD s1 mi') by (rewrite E1, Em; reflexivity).
    exists s2; split; [apply NilAction; reflexivity |].
    exists g.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hfe Hs Hfr Hw Hrk].
    assert (HR : iRevA s1' = iRevA s1).
    { rewrite Es1; change (implRevState pre post revBase revPfB revPfA mi' =
                           implRevState pre post revBase revPfB revPfA (iRegionsA s1)).
      unfold implRevState; rewrite (regionStateAt_fetchRpStep initLine _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    apply (RefRelG_fetchRp_frame g s1 s1' s2 mi' Es1); [| exact HR | | | | exact Hg].
    - intros P HPi; rewrite Es1, iRegions_write'; exact (AllPorts_fetchRpStep initLine P HPi _ _ _ _ Hst).
    - (* the memory relation *)
      rewrite Es1; unfold MemRelC, MemRel, DevInv in *; rewrite iRegions_write'.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
      assert (Ec : implClintState pre post revBase revPfB revPfA clint mi' =
                   implClintState pre post revBase revPfB revPfA clint (iRegionsA s1)).
      { unfold implClintState; rewrite (regionStateAt_fetchRpStep initLine _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
      assert (Ep : implPlicState pre post revBase revPfB revPfA plic mi' =
                   implPlicState pre post revBase revPfB revPfA plic (iRegionsA s1)).
      { unfold implPlicState; rewrite (regionStateAt_fetchRpStep initLine _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
      assert (Er : implRevState pre post revBase revPfB revPfA mi' =
                   implRevState pre post revBase revPfB revPfA (iRegionsA s1)).
      { unfold implRevState; rewrite (regionStateAt_fetchRpStep initLine _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
      rewrite Ec, Ep, Er.
      refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
      eapply MemRelPre_fetchRpStep; [exact I | exact Hst | exact Hpre].
    - (* the fetch responses *)
      unfold FetchRespRel in Hfr |- *.
      destruct Hfr as [_ [_ [_ [_ [_ [_ F7]]]]]].
      rewrite Es1, iRegions_write'.
      change (AllPorts (FRP (fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
                          (fbLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
                          (LineAllowed initLine fwcs specRegions (sMemA s2))) implRegions mi').
      change (AllPorts (FRP (fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
                          (fbLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
                          (LineAllowed initLine fwcs specRegions (sMemA s2))) implRegions (iRegionsA s1)) in F7.
      refine (FRP_fetchRpStep initLine implRegions fwcs _ _ _ _ _ _ _ _ Hst F7).
      + intros L; apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj.
      + intros r f0 Hin; unfold fbInRegion in Hin; apply filter_In in Hin as [_ Hin].
        apply andb_prop in Hin as [_ Hin]; exact Hin.
      + intros L rp _ Hal.
        destruct Hm as [[Hpre _] _].
        refine (lineAllowed_pre initLine (clintIdx clintS) (plicIdx plicS) (specRevRegion revBase revPfB revPfA)
                  (implRevRegion revBase revPfB revPfA) post pre 0 fwcs _ _ L rp I _ Hpre Hal).
        reflexivity.
    - (* the handshake invariant *)
      rewrite Es1, iRegions_write'.
      unfold WfRel in Hw; destruct Hw as [_ [_ [_ [_ [_ W5]]]]].
      exact (handshake_fetchRpStep initLine _ _ _ _ Hst W5).
  Qed.
End FetchRpPorts.
