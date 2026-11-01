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
From Cheriot.Proof Require Import ImplSpec RefFetch RefMemStep RefFetchRp RefReadRp.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4: the data response ports (`readRpPorts`: `implMemLineRpPort` around
 * `implExternalLineRpPort`, one per ExternalMem region).
 * 1. One port step (`dataRpPort_cases`): a `false` valid (no response), or a response taken (the
 *    env makes it the line content of the oldest unanswered accepted read, `implDataLineAddr`, as
 *    the accepted writes left it). Over the region list one ExternalMem position steps
 *    (`dataRpPorts_step`). *)

(* --- 1. One Data Response Port Step --- *)

Section DataRpPortRegion.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* The data responses the region received *)
  Definition dataRcv r (y : ExtI r) : list (type LineReadRp) := y.(Fst).(Snd).(Snd).(Fst).

  (* The region after its data port saw no response *)
  Definition dataRpNone r (y : ExtI r) : ExtI r :=
    (y.(Fst) ,, (y.(Snd).(Fst) ,, (y.(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Fst) ,,
      ((false :: y.(Snd).(Snd).(Snd).(Snd).(Fst)) ,, y.(Snd).(Snd).(Snd).(Snd).(Snd)))))).

  (* The region after its data port took the response `rp` (`z`: the value sent on
   * lineReadRpReady) *)
  Definition dataRpTaken r (y : ExtI r) (rp : type LineReadRp) (z : type (Bit 0)) : ExtI r :=
    ((y.(Fst).(Fst) ,, (y.(Fst).(Snd).(Fst) ,, ((rp :: y.(Fst).(Snd).(Snd).(Fst)) ,, y.(Fst).(Snd).(Snd).(Snd)))) ,,
     (y.(Snd).(Fst) ,, (y.(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Fst) ,,
       ((true :: y.(Snd).(Snd).(Snd).(Snd).(Fst)) ,,
        ((z :: y.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)) ,, y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))).

  Local Opaque liftAction.

  Lemma dataRpPort_cases :
    forall r fwc (eR : Env (implExternalMemRegionTree r)) (y y' : ExtI r) o,
      (forall s x w, eR s x w -> implExtRegionEnv initLine r fwc s x w) ->
      SemAction eR (@implExternalLineRpPort r type) y y' o ->
      (optValid o = false /\ y' = dataRpNone r y) \/
      ((length (dataRcv r y) < length (implDataAccRqs r y))%nat /\
       exists rp z, rp = evalLineWriteRqTrace (initLine r) (implAccWrites r y) (implDataLineAddr r y) /\
                    o = (rp ,, (true ,, tt)) /\ y' = dataRpTaken r y rp z).
  Proof.
    intros r fwc eR
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [[if_rdRpData [if_rdRpVal []]] []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           y' o HE Hsem.
    unfold implExternalLineRpPort, externalLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn in Hsem.
    destruct Hsem as [valid [Hvenv Hbr]].
    destruct valid; cbn in Hbr.
    - rewrite !evalActionPropGen_liftAction in Hbr; cbn in Hbr.
      destruct Hbr as [rp [Hrpenv Hrest]].
      cbn in Hrest; destruct Hrest as [<- <-].
      right; split.
      + unfold subEnv, cast_recv_inv in Hvenv; apply HE in Hvenv.
        unfold implExtRegionEnv, extRegionEnvCtx in Hvenv.
        cbn -[eq_rect EnvDataLineReadRpValidConstraint] in Hvenv.
        rewrite ?eq_rect_Kind_refl in Hvenv.
        exact (Hvenv eq_refl).
      + eexists rp, _; split; [| split; reflexivity].
        unfold subEnv, cast_recv_inv in Hrpenv; apply HE in Hrpenv.
        unfold implExtRegionEnv, extRegionEnvCtx in Hrpenv.
        cbn -[eq_rect evalLineWriteRqTrace implAccWrites implDataLineAddr] in Hrpenv.
        rewrite ?eq_rect_Kind_refl in Hrpenv.
        exact Hrpenv.
    - destruct Hbr as [<- <-].
      left; split; reflexivity.
  Qed.

  (* One region's data response port step, with the port's output *)
  Definition RegionDataRpStep (fwc : nat -> nat) (r : MemRegion)
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> type (Option LineReadRp) -> Prop :=
    match r.(regionKind) as k
          return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> type (Option LineReadRp) -> Prop with
    | ExternalMem => fun y y' o =>
        (optValid o = false /\ y' = dataRpNone r y) \/
        ((length (dataRcv r y) < length (implDataAccRqs r y))%nat /\
         exists rp z, rp = evalLineWriteRqTrace (initLine r) (implAccWrites r y) (implDataLineAddr r y) /\
                      o = (rp ,, (true ,, tt)) /\ y' = dataRpTaken r y rp z)
    | CustomMem _ _ _ _ => fun _ _ _ => False
    end.

  (* One position of the list takes a data response port step, the others are unchanged *)
  Fixpoint DataRpPortStepL (fwcs : nat -> nat -> nat) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> type (Option LineReadRp) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> type (Option LineReadRp) -> Prop with
    | [] => fun _ _ _ => False
    | r :: rs => fun mi mi' o =>
        (RegionDataRpStep (fwcs 0%nat) r mi.(Fst) mi'.(Fst) o /\ mi'.(Snd) = mi.(Snd)) \/
        (mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\
         DataRpPortStepL (fun i => fwcs (S i)) rs mi.(Snd).(Fst) mi'.(Snd).(Fst) o)
    end.

  Lemma dataRpPorts_step :
    forall l fwcs (aI : forall ty, Action ty (implRegionsTree l) (Option LineReadRp)) env mi mi' o,
      ImplEnvOK initLine l fwcs env ->
      In aI (implCollectLineRpPorts l) ->
      SemAction env (aI type) mi mi' o -> DataRpPortStepL fwcs l mi mi' o.
  Proof.
    induction l as [| r rs IH]; intros fwcs aI env mi mi' o HE Hin Hsem; [destruct Hin |].
    unfold implCollectLineRpPorts, implCollectRegionActions in Hin; cbn [genCollectRegionActions] in Hin.
    apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as [f [<- Hf]].
    - left; apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
      split; [| reflexivity]; cbn [writeSubTreeState readSubTreeState] in Hy' |- *.
      pose proof (ImplEnvOK_head initLine r rs fwcs env mi HE) as HE0.
      revert f Hf Hy' HE0; destruct r as [nm bs sz kd sn im ba sa]; destruct kd;
        cbn [implMemRegionLineRpPorts regionKind In RegionDataRpStep implRegionEnv];
        intros f Hf Hy' HE0; try contradiction.
      destruct Hf as [<- | []].
      exact (dataRpPort_cases _ _ _ _ _ _ HE0 Hy').
    - right; apply SemAction_liftAction_iff in Hsem as [z' [Hz' ->]].
      split; [reflexivity | split; [reflexivity |]].
      exact (IH _ f _ _ _ _ (ImplEnvOK_tail initLine r rs fwcs env mi HE) Hf Hz').
  Qed.
End DataRpPortRegion.

(* --- 2. The Port on the Memory Subtree --- *)

Section MemLineRpPort.
  Variable regions : list MemRegion.

  Ltac mem_cbn H := cbn -[evalExpr evalLetExpr toAction liftAction] in H.

  (* `implMemLineRpPort port`: with `readRp` full nothing changes; otherwise the port runs on the
   * regions and a valid output fills `readRp` *)
  Lemma memLineRpPort_char :
    forall (port : Action type (implRegionsTree regions) (Option LineReadRp)) env mr mst mrq mrp m' v,
      SemAction env (@implMemLineRpPort regions type port) (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      (optValid mrp = true /\ m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt))))) \/
      (optValid mrp = false /\ exists mr' o,
         SemAction (subEnv child0Path env (mr ,, (mst ,, (mrq ,, (mrp ,, tt))))) port mr mr' o /\
         m' = (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt))))).
  Proof.
    intros port env mr mst mrq mrp m' v H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemLineRpPort in H; cbn [evalActionPropGen] in H.
    mem_cbn H.
    match type of H with context [if ?cd then _ else _] =>
      replace cd with (negb (optValid mrp)) in H by reflexivity
    end.
    destruct (optValid mrp) eqn:Ev; cbn [negb] in H.
    - left; split; [reflexivity |].
      mem_cbn H; destruct H as [H _]; symmetry; exact H.
    - right; split; [reflexivity |].
      rewrite evalActionPropGen_liftAction in H.
      apply evalActionPropGen_to_SemAction in H as [mr' [o [Hp Hpost]]].
      exists mr', o; split; [exact Hp |].
      mem_cbn Hpost.
      match type of Hpost with context [if ?cd then _ else _] =>
        replace cd with (optValid o) in Hpost by reflexivity
      end.
      destruct (optValid o) eqn:Eo; mem_cbn Hpost; destruct Hpost as [Hpost _]; symmetry; exact Hpost.
  Qed.
End MemLineRpPort.

(* --- 3. A Response Is the Content of the Line Read --- *)

Section DataContent.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* The port predicate of `PortsReadOut L` *)
  Definition readOutP (L : type Addr) : forall r, ExtI r -> Prop :=
    fun r y => optValid (extPortRq r y) = false /\
               (if isRegionAddrB r L then extDataOut r y /\ hd Zmod.zero (implDataAccRqs r y) = L
                else extDataQuiet r y).

  (* The content of line `L` by the impl's accepted writes (the router picks the first region) *)
  Definition ImplRegionLineContent (r : MemRegion) : TS (implMemRegionTree r) -> type Addr -> type LineReadRp :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> type Addr -> type LineReadRp with
    | ExternalMem => fun y L => evalLineWriteRqTrace (initLine r) (implAccWrites r y) L
    | CustomMem _ _ _ _ => fun _ _ => getDefault LineReadRp
    end.

  Fixpoint implLineContent (l : list MemRegion) : TS (implRegionsTree l) -> type Addr -> type LineReadRp :=
    match l as l0 return TS (implRegionsTree l0) -> type Addr -> type LineReadRp with
    | [] => fun _ _ => getDefault LineReadRp
    | r :: rs => fun mi L =>
        if isRegionAddrB r L then ImplRegionLineContent r mi.(Fst) L else implLineContent rs mi.(Snd).(Fst) L
    end.

  (* A region's valid output: its unanswered read is `L`, and the output is `L`'s content *)
  Lemma dataRp_region :
    forall fwc r (y y' : TS (implMemRegionTree r)) o L,
      RegionDataRpStep initLine fwc r y y' o -> optValid o = true -> RegionPort (readOutP L) r y ->
      isRegionAddrB r L = true /\ optData o = ImplRegionLineContent r y L.
  Proof.
    intros fwc r; unfold RegionDataRpStep, RegionPort, ImplRegionLineContent, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' o L Hs Hv H;
      [| destruct Hs].
    destruct Hs as [[Hf _] | [Hlt [rp [z [Hrp [Eo _]]]]]]; [rewrite Hf in Hv; discriminate Hv |].
    unfold readOutP in H; destruct H as [_ HL].
    destruct (isRegionAddrB _ L) eqn:Hm.
    - destruct HL as [Hout Hhd]; split; [reflexivity |].
      subst o; cbn [optData Fst]; rewrite Hrp; f_equal.
      unfold implDataLineAddr, fifoRq; unfold extDataOut in Hout.
      rewrite Hout, Nat.sub_diag; rewrite <- Hhd.
      destruct (implDataAccRqs _ y); reflexivity.
    - exfalso; unfold extDataQuiet in HL; rewrite HL in Hlt; exact (Nat.lt_irrefl _ Hlt).
  Qed.

  (* No region holds `L`: no valid output *)
  Lemma dataRp_noL :
    forall l fwcs (mi mi' : TS (implRegionsTree l)) o L,
      lineKind l L = None -> AllPorts (readOutP L) l mi -> DataRpPortStepL initLine fwcs l mi mi' o ->
      optValid o = false.
  Proof.
    induction l as [| r rs IH]; intros fwcs mi mi' o L Hk H Hst; [destruct Hst |].
    cbn [lineKind] in Hk; cbn [AllPorts] in H; cbn [DataRpPortStepL] in Hst.
    destruct (isRegionAddrB r L) eqn:Hm; [discriminate Hk |].
    destruct H as [H0 H1].
    destruct Hst as [[Hs _] | [_ [_ Hrest]]]; [| exact (IH _ _ _ _ L Hk H1 Hrest)].
    destruct (optValid o) eqn:Hv; [| reflexivity].
    destruct (dataRp_region _ _ _ _ _ L Hs Hv H0) as [Hm' _]; rewrite Hm in Hm'; discriminate Hm'.
  Qed.

  Lemma dataRp_content :
    forall l fwcs (mi mi' : TS (implRegionsTree l)) o L,
      lineUnique l L -> AllPorts (readOutP L) l mi -> DataRpPortStepL initLine fwcs l mi mi' o ->
      optValid o = true -> optData o = implLineContent l mi L.
  Proof.
    induction l as [| r rs IH]; intros fwcs mi mi' o L Hu H Hst Hv; [destruct Hst |].
    cbn [lineUnique] in Hu; cbn [AllPorts] in H; cbn [DataRpPortStepL] in Hst; cbn [implLineContent].
    destruct H as [H0 H1].
    destruct Hst as [[Hs _] | [_ [_ Hrest]]].
    - destruct (dataRp_region _ _ _ _ _ L Hs Hv H0) as [Hm E]; rewrite Hm; exact E.
    - destruct (isRegionAddrB r L) eqn:Hm.
      + rewrite (dataRp_noL _ _ _ _ _ L Hu H1 Hrest) in Hv; discriminate Hv.
      + exact (IH _ _ _ _ L Hu H1 Hrest Hv).
  Qed.

  (* The impl's content of a line is the spec's (`ExtRel`: spec writes = accepted writes) *)
  Variables cp pp : nat.

  Lemma lineContent_region :
    forall i r x (y : TS (implMemRegionTree r)) L,
      RegionRelAt cp pp i r x y -> ImplRegionLineContent r y L = RegionLineContent initLine r x L.
  Proof.
    intros i r; unfold RegionRelAt, ImplRegionLineContent, RegionLineContent, memRegionTree, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros x y L Hr; [| reflexivity].
    destruct Hr as [Ew _]; rewrite <- Ew; reflexivity.
  Qed.

  Lemma lineContent_post :
    forall l i ms mi L, MemRelPost cp pp i l ms mi -> implLineContent l mi L = lineContent initLine l ms L.
  Proof.
    induction l as [| r rs IH]; intros i ms mi L Hm; cbn [implLineContent lineContent MemRelPost] in *;
      [reflexivity |].
    destruct Hm as [Hr Hl].
    destruct (isRegionAddrB r L); [exact (lineContent_region _ _ _ _ L Hr) | exact (IH _ _ _ L Hl)].
  Qed.

  Lemma lineContent_pre :
    forall sRev iRev post l i ms mi L,
      isCustomR sRev -> isCustomR iRev -> isRegionAddrB sRev L = isRegionAddrB iRev L ->
      MemRelPre cp pp i l sRev iRev post ms mi ->
      implLineContent (l ++ iRev :: post) mi L = lineContent initLine (l ++ sRev :: post) ms L.
  Proof.
    intros sRev iRev post; induction l as [| r rs IH]; intros i ms mi L Hcs Hci Ea Hm.
    - cbn [app implLineContent lineContent MemRelPre] in *.
      rewrite Ea; destruct (isRegionAddrB iRev L).
      + revert Hcs Hci; generalize (ms.(Fst)) (mi.(Fst)).
        unfold isCustomR, RegionLineContent, ImplRegionLineContent, memRegionTree, implMemRegionTree.
        destruct (regionKind sRev), (regionKind iRev); intros x y H1 H2; cbn in H1, H2;
          first [contradiction | reflexivity].
      + exact (lineContent_post _ _ _ _ L Hm).
    - cbn [app implLineContent lineContent MemRelPre] in *.
      destruct Hm as [Hr Hl].
      destruct (isRegionAddrB r L); [exact (lineContent_region _ _ _ _ L Hr) | exact (IH _ _ _ L Hcs Hci Ea Hl)].
  Qed.
End DataContent.

(* --- 4. Frame Facts of a Data Port Step --- *)

Section DataRpFrame.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* Device (CustomMem) positions are untouched *)
  Lemma regionStateAt_dataRpStep :
    forall l fwcs j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree l)) o,
      DataRpPortStepL initLine fwcs l mi mi' o -> isCustomR r0 ->
      regionStateAt implMemRegionTree j l r0 pf mi' = regionStateAt implMemRegionTree j l r0 pf mi.
  Proof.
    induction l as [| r rs IH]; intros fwcs [| j'] r0 pf mi mi' o H Hc; try discriminate pf;
      cbn [DataRpPortStepL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o0) return match o0 with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct H as [[Hs _] | [Hf _]]; [| rewrite Hf; reflexivity].
      exfalso; revert Hs; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionDataRpStep, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt].
      destruct H as [[_ Hs] | [_ [_ Hrest]]].
      + rewrite Hs; reflexivity.
      + exact (IH _ j' r0 pf _ _ _ Hrest Hc).
  Qed.

  (* A step with no response changes only the impl's lineReadRpValid trace of one region *)
  Lemma AllPorts_dataRpNone :
    forall (P : forall r, ExtI r -> Prop), (forall r y, P r (dataRpNone r y) = P r y) ->
      forall l fwcs (mi mi' : TS (implRegionsTree l)) o,
        DataRpPortStepL initLine fwcs l mi mi' o -> optValid o = false -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HP; induction l as [| r rs IH]; intros fwcs mi mi' o Hst Hv; [destruct Hst |].
    cbn [DataRpPortStepL] in Hst; cbn [AllPorts].
    destruct Hst as [[Hr Hs] | [Hf [Hs Hl]]].
    - rewrite Hs; f_equal.
      revert Hr; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionDataRpStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hr; [| contradiction].
      destruct Hr as [[_ ->] | [_ [rp [z [_ [Eo _]]]]]]; [apply HP | subst o; discriminate Hv].
    - rewrite Hf, (IH _ _ _ _ Hl Hv); reflexivity.
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_dataRpStep :
    forall fwc i r x (y y' : TS (implMemRegionTree r)) o,
      RegionDataRpStep initLine fwc r y y' o -> RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r x y'.
  Proof.
    intros fwc i r x y y' o; unfold RegionRelAt, RegionDataRpStep, implMemRegionTree, memRegionTree in *.
    revert x y y'; destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind];
      intros x y y' Hs Hr; [| contradiction].
    destruct Hs as [[_ ->] | [_ [rp [z [_ [_ ->]]]]]]; exact Hr.
  Qed.

  Lemma MemRelPost_dataRpStep :
    forall l fwcs i ms mi mi' o, DataRpPortStepL initLine fwcs l mi mi' o ->
      MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l ms mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs i ms mi mi' o Hst H; [destruct Hst |].
    cbn [DataRpPortStepL] in Hst; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - rewrite Ht; split; [exact (RegionRelAt_dataRpStep _ _ _ _ _ _ _ Hs Hr) | exact Hl].
    - rewrite Hf; split; [exact Hr | exact (IH _ _ _ _ _ _ Hrest Hl)].
  Qed.

  Lemma MemRelPre_dataRpStep :
    forall sRev iRev post l fwcs i ms mi mi' o, isCustomR iRev ->
      DataRpPortStepL initLine fwcs (l ++ iRev :: post) mi mi' o ->
      MemRelPre cp pp i l sRev iRev post ms mi -> MemRelPre cp pp i l sRev iRev post ms mi'.
  Proof.
    intros sRev iRev post; induction l as [| r rs IH]; intros fwcs i ms mi mi' o Hc Hst H.
    - cbn [app DataRpPortStepL] in Hst; cbn [MemRelPre] in H |- *.
      destruct Hst as [[Hs _] | [_ [_ Hrest]]]; [| exact (MemRelPost_dataRpStep _ _ _ _ _ _ _ Hrest H)].
      exfalso; revert Hs; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionDataRpStep, isCustomR, implMemRegionTree in *.
      destruct (regionKind iRev); [contradiction | intros y' y Hy; exact Hy].
    - cbn [app DataRpPortStepL] in Hst; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
      + rewrite Ht; split; [exact (RegionRelAt_dataRpStep _ _ _ _ _ _ _ Hs Hr) | exact Hl].
      + rewrite Hf; split; [exact Hr | exact (IH _ _ _ _ _ _ Hc Hrest Hl)].
  Qed.

  (* The handshake invariant and the fence.i count invariant are kept *)
  Lemma handshake_dataRpStep :
    forall l fwcs mi mi' o, DataRpPortStepL initLine fwcs l mi mi' o ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) l mi ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) l mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs mi mi' o Hst H; [destruct Hst |].
    cbn [DataRpPortStepL] in Hst; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - rewrite Ht; split; [| exact H1].
      revert H0 Hs; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionDataRpStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs; [| exact I].
      destruct H0 as [Hh Hf].
      destruct Hs as [[_ ->] | [_ [rp [z [_ [_ ->]]]]]].
      + split; [| exact Hf].
        unfold ImplExternalRegionHandshakeInv in Hh |- *; cbn [dataRpNone Fst Snd count_true] in Hh |- *.
        exact Hh.
      + split; [| exact Hf].
        unfold ImplExternalRegionHandshakeInv in Hh |- *; cbn [dataRpTaken Fst Snd length count_true] in Hh |- *.
        destruct Hh as [H1' [H2 [H3 [H4 H5]]]].
        exact (conj H1' (conj H2 (conj H3 (conj (f_equal S H4) (f_equal S H5))))).
    - rewrite Hf; split; [exact H0 | exact (IH _ _ _ _ Hrest H1)].
  Qed.

  (* After the response for line `L`, every region is quiet (no staged request, every read
   * answered) *)
  Lemma quiet_dataRpTaken :
    forall l fwcs (mi mi' : TS (implRegionsTree l)) o L,
      lineUnique l L -> AllPorts (readOutP L) l mi -> DataRpPortStepL initLine fwcs l mi mi' o ->
      optValid o = true ->
      AllPorts (fun r y => optValid (extPortRq r y) = false /\ extDataQuiet r y) l mi'.
  Proof.
    induction l as [| r rs IH]; intros fwcs mi mi' o L Hu H Hst Hv; [destruct Hst |].
    cbn [lineUnique] in Hu; cbn [AllPorts] in H |- *; cbn [DataRpPortStepL] in Hst.
    destruct H as [H0 H1].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - destruct (dataRp_region initLine _ _ _ _ _ L Hs Hv H0) as [Hm _].
      rewrite Hm in Hu; rewrite Ht; split.
      + revert H0 Hs Hm; generalize (mi.(Fst)) (mi'.(Fst)).
        unfold RegionPort, RegionDataRpStep, implMemRegionTree.
        destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs Hm; [| exact I].
        destruct Hs as [[Hf _] | [Hlt [rp [z [_ [_ ->]]]]]]; [rewrite Hf in Hv; discriminate Hv |].
        unfold readOutP in H0; rewrite Hm in H0; destruct H0 as [Hp [Hout _]].
        split; [exact Hp |].
        unfold extDataQuiet, extDataOut in *; cbn [dataRpTaken Fst Snd length].
        exact Hout.
      + (* no other region holds `L`: all quiet *)
        clear IH Ht Hs H0.
        revert Hu H1; generalize (mi.(Snd).(Fst)); clear; induction rs as [| r' rs IH]; intros mr Hu H; [exact I |].
        cbn [lineKind] in Hu; cbn [AllPorts] in H |- *; destruct H as [H0 H1].
        destruct (isRegionAddrB r' L) eqn:Hm; [discriminate Hu |].
        split; [| exact (IH _ Hu H1)].
        revert H0; generalize (mr.(Fst)); unfold RegionPort, readOutP, implMemRegionTree.
        destruct (regionKind r'); intros y H0; [| exact I].
        rewrite Hm in H0; exact H0.
    - destruct (isRegionAddrB r L) eqn:Hm.
      + rewrite (dataRp_noL initLine _ _ _ _ _ L Hu H1 Hrest) in Hv; discriminate Hv.
      + rewrite Hf; split; [| exact (IH _ _ _ _ L Hu H1 Hrest Hv)].
        clear Hf Ht Hrest IH H1.
        revert H0; generalize (mi.(Fst)); unfold RegionPort, readOutP, implMemRegionTree.
        destruct (regionKind r); intros y H0; [| exact I].
        rewrite Hm in H0; exact H0.
  Qed.
End DataRpFrame.

(* --- 5. The Data Response Ports at System Level; Steps with No Response --- *)

Section ReadRpPorts.
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
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).

  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).

  Local Abbreviation UPD s1 mi' := (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd))).

  Lemma iMem_read2 : forall (s1 : IState), readSubTreeState NPMI s1 = iMemA s1.
  Proof. reflexivity. Qed.

  Lemma iRegions_upd : forall (s1 : IState) mi', iRegionsA (UPD s1 mi') = mi'.
  Proof. reflexivity. Qed.

  (* One step of a data response port, on the impl memory subtree *)
  Lemma readRpPorts_mem :
    forall act (s1 s1' : IState),
      In act (@readRpPorts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
      SemAction envI act s1 s1' Zmod.zero ->
      forall mr mst mrq mrp, iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      (optValid mrp = true /\ s1' = s1) \/
      (optValid mrp = false /\ exists mr' o, DataRpPortStepL initLine fwcs implRegions mr mr' o /\
         s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt))))).
  Proof.
    intros act s1 s1' Hin Hsem mr mst mrq mrp EM.
    unfold readRpPorts, implMemCollectLineReadRpPorts in Hin.
    rewrite map_map in Hin; apply in_map_iff in Hin as [f [<- Hf]]; cbv beta in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read2, EM in Hm'.
    destruct (memLineRpPort_char implRegions (f type) _ mr mst mrq mrp m' _ Hm') as [[Hv Em'] | [Hv [mr' [o [Hp Em']]]]].
    - left; split; [exact Hv |].
      subst m'; rewrite <- EM in E1; rewrite E1; reflexivity.
    - right; split; [exact Hv |].
      exists mr', o; split; [| subst m'; exact E1].
      exact (dataRpPorts_step initLine implRegions fwcs f _ _ _ _
               (implEnvOK_regions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  initLine fwcs s1 _) Hf Hp).
  Qed.

  (* A step that changes only the impl's lineReadRpValid trace of one region: the spec stutters *)
  Lemma RefRelG_dataRpNone_frame :
    forall g (s1 s1' : IState) (s2 : SState) mi',
      s1' = UPD s1 mi' ->
      (forall P, (forall r y, P r (dataRpNone r y) = P r y) ->
                 AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      iRevA s1' = iRevA s1 ->
      MEMC g s1' s2 ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1') ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 mi' E1 HP HR Hmem Hhs H.
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
      + unfold PortsQuiet; apply HP; intros r y; reflexivity.
      + intros L; unfold PortsReadStaged; apply HP; intros r y; reflexivity.
      + intros L; unfold PortsReadOut; apply HP; intros r y; reflexivity.
      + intros L rq; unfold PortsWriteStaged; apply HP; intros r y; reflexivity.
      + rewrite E1; reflexivity.
      + rewrite E1; reflexivity.
      + rewrite E1; reflexivity.
    - unfold CnwbRel in *; rewrite Edm; exact Hc.
    - rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite HP by (intros r y; reflexivity); rewrite E1; exact Hf.
    - rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split; [rewrite E1; exact F6 |].
      unfold FetchRespRel in *; rewrite HP by (intros r y; reflexivity); rewrite E1; exact F7.
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd _]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 | split; [rewrite E1; exact Wmd | exact Hhs]].
    - exact (RevokerRel_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine
               g g s1 s1' s2 s2 eq_refl eq_refl HR (fun L => eq_refl) Hrk).
  Qed.

  (* No response taken (no valid output): the spec stutters *)
  Lemma readRpPorts_noValid :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions mr mr' o -> optValid o = false ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' o EM E1 Hst Hv Hg.
    rewrite Hv in E1; cbv iota in E1.
    assert (Es1 : s1' = UPD s1 mr') by (rewrite E1, EM; reflexivity).
    assert (Emr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    rewrite <- Emr in Hst.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hfe Hs Hfr Hw Hrk].
    assert (HR : iRevA s1' = iRevA s1).
    { rewrite Es1; change (implRevState pre post revBase revPfB revPfA mr' =
                           implRevState pre post revBase revPfB revPfA (iRegionsA s1)).
      unfold implRevState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    apply (RefRelG_dataRpNone_frame g s1 s1' s2 mr' Es1); [| exact HR | | | exact Hg].
    - intros P HPi; rewrite Es1, iRegions_upd; exact (AllPorts_dataRpNone initLine P HPi _ _ _ _ _ Hst Hv).
    - rewrite Es1; unfold MemRelC, MemRel, DevInv in *; rewrite iRegions_upd.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
      assert (Ec : implClintState pre post revBase revPfB revPfA clint mr' =
                   implClintState pre post revBase revPfB revPfA clint (iRegionsA s1)).
      { unfold implClintState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
      assert (Ep : implPlicState pre post revBase revPfB revPfA plic mr' =
                   implPlicState pre post revBase revPfB revPfA plic (iRegionsA s1)).
      { unfold implPlicState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
      assert (Er : implRevState pre post revBase revPfB revPfA mr' =
                   implRevState pre post revBase revPfB revPfA (iRegionsA s1)).
      { unfold implRevState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
      rewrite Ec, Ep, Er.
      refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
      eapply MemRelPre_dataRpStep; [exact I | exact Hst | exact Hpre].
    - rewrite Es1, iRegions_upd.
      unfold WfRel in Hw; destruct Hw as [_ [_ [_ [_ [_ W5]]]]].
      exact (handshake_dataRpStep initLine _ _ _ _ _ Hst W5).
  Qed.

  (* --- 6. Steps with a Response --- *)

  Local Abbreviation ACC := (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation REVK := (RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation PRO := (PortsReadOut pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).

  (* A port predicate that ignores the data responses and their valid/ready traces *)
  Lemma AllPorts_dataRpStep :
    forall (P : forall r, TS (implExternalMemRegionTree r) -> Prop),
      (forall r y rp z, P r (dataRpTaken r y rp z) = P r y) -> (forall r y, P r (dataRpNone r y) = P r y) ->
      forall l fs (mi mi' : TS (implRegionsTree l)) o,
        DataRpPortStepL initLine fs l mi mi' o -> AllPorts P l mi' = AllPorts P l mi.
  Proof.
    intros P HT HN; induction l as [| r rs IH]; intros fs mi mi' o Hst; [destruct Hst |].
    cbn [DataRpPortStepL] in Hst; cbn [AllPorts].
    destruct Hst as [[Hr Hs] | [Hf [Hs Hl]]].
    - rewrite Hs; f_equal.
      revert Hr; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionDataRpStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hr; [| contradiction].
      destruct Hr as [[_ ->] | [_ [rp [z [_ [_ ->]]]]]]; [apply HN | apply HT].
    - rewrite Hf, (IH _ _ _ _ Hl); reflexivity.
  Qed.

  (* A step of the impl memory where the spec stutters, with the access in flight and the revoker
   * facts supplied for the new ghost *)
  Lemma RefRelG_dataRp_frame :
    forall g g' (s1 s1' : IState) (s2 : SState) mi',
      s1' = writeSubTreeState NPMI s1 mi' ->
      g_chain pcAddrInit g' = g_chain pcAddrInit g -> g_rf0 pcAddrInit g' = g_rf0 pcAddrInit g ->
      g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g -> g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g ->
      accTakesHead (g_acc pcAddrInit g') = accTakesHead (g_acc pcAddrInit g) ->
      (forall P, (forall r y rp z, P r (dataRpTaken r y rp z) = P r y) -> (forall r y, P r (dataRpNone r y) = P r y) ->
                 AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      MEMC g' s1' s2 -> ACC g' s1' s2 -> REVK g' s1' s2 ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1') ->
      RELG g s1 s2 -> RELG g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 mi' E1 Ech Erf Ecn Ed2a Eacc HP Hmem Hacc Hrev Hhs H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    assert (Edm : iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                  iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
      by (rewrite E1; reflexivity).
    constructor.
    - unfold RfRel in *; rewrite Ech, Erf, Ecn; rewrite E1; exact Hrf.
    - exact Hmem.
    - unfold LatchRel in *; rewrite Ech; exact Hl.
    - unfold ReplayRel in *; rewrite Ech, Erf; exact Hrp.
    - unfold EagerRel in *; rewrite Ech; exact He.
    - exact Hacc.
    - unfold CnwbRel in *; rewrite Ecn, Ech, Eacc, Edm; exact Hc.
    - unfold DmQueueRel in *; rewrite Ech, Eacc; rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite Ech, HP by (intros; reflexivity); rewrite E1; exact Hf.
    - unfold ScoreRel in *; rewrite Ed2a; rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split; [unfold LiveChain, liveInsts in *; rewrite Ed2a, E1; exact F6 |].
      unfold FetchRespRel in *; rewrite HP by (intros; reflexivity); rewrite E1; exact F7.
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd _]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 | split; [rewrite E1; exact Wmd | exact Hhs]].
    - exact Hrev.
  Qed.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  (* A response taken while the read of line `L` is out is the spec memory's content of `L` *)
  Lemma rp_spec_content :
    forall g (s1 : IState) (s2 : SState) mr' o L,
      MEMC g s1 s2 -> PRO L s1 ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      optData o = lineContent initLine specRegions (sMemA s2) L.
  Proof.
    intros g s1 s2 mr' o L Hm Hout Hst Hv.
    rewrite (dataRp_content initLine implRegions fwcs _ _ _ L
               ltac:(apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj) Hout Hst Hv).
    unfold MemRelC, MemRel in Hm; destruct Hm as [[Hpre _] _].
    exact (lineContent_pre initLine (clintIdx clintS) (plicIdx plicS) (specRevRegion revBase revPfB revPfA)
             (implRevRegion revBase revPfB revPfA) post pre 0 _ _ L I I eq_refl Hpre).
  Qed.

  Local Abbreviation iMemStA := (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA := (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA := (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The memory relation after any data port step (it reads the regions only where unchanged) *)
  Lemma MemRelC_dataRpStep :
    forall g (s1 s1' : IState) (s2 : SState) mr' x o,
      s1' = writeSubTreeState NPMI s1 (mr' ,, x) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o ->
      MEMC g s1 s2 -> MEMC g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' x o E1 Hst Hm.
    rewrite E1; unfold MemRelC, MemRel, DevInv in *.
    change (iRegionsA (writeSubTreeState NPMI s1 (mr' ,, x))) with mr'.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    assert (Ec : implClintState pre post revBase revPfB revPfA clint mr' =
                 implClintState pre post revBase revPfB revPfA clint (iRegionsA s1)).
    { unfold implClintState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    assert (Ep : implPlicState pre post revBase revPfB revPfA plic mr' =
                 implPlicState pre post revBase revPfB revPfA plic (iRegionsA s1)).
    { unfold implPlicState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    assert (Er : implRevState pre post revBase revPfB revPfA mr' =
                 implRevState pre post revBase revPfB revPfA (iRegionsA s1)).
    { unfold implRevState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    rewrite Ec, Ep, Er.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    eapply MemRelPre_dataRpStep; [exact I | exact Hst | exact Hpre].
  Qed.

  (* The impl after a response for line `L` was taken *)
  Lemma taken_impl :
    forall (s1 s1' : IState) mr mst mrq mrp mr' o L,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true -> PRO L s1 ->
      iRevA s1' = iRevA s1 /\ iMemStA s1' = iMemStA s1 /\ iRequesterA s1' = iRequesterA s1 /\
      iDmStA s1' = iDmStA s1 /\ iReadRpA s1' = (optData o ,, (true ,, tt)) /\ PQ s1'.
  Proof.
    intros s1 s1' mr mst mrq mrp mr' o L EM E1 Hst Hv Hout.
    rewrite Hv in E1; cbv iota in E1.
    split; [| split; [| split; [| split; [| split]]]].
    - rewrite E1; change (implRevState pre post revBase revPfB revPfA mr' =
                          implRevState pre post revBase revPfB revPfA (iRegionsA s1)).
      unfold implRevState; rewrite (regionStateAt_dataRpStep initLine _ _ _ _ _ _ _ _ Hst); [reflexivity | exact I].
    - rewrite E1; unfold iMemSt; rewrite EM; reflexivity.
    - rewrite E1; unfold iRequester; rewrite EM; reflexivity.
    - rewrite E1; reflexivity.
    - rewrite E1; clear - Hv; destruct o as [d [b []]]; cbn in Hv; subst b; reflexivity.
    - rewrite E1; unfold PortsQuiet.
      change (AllPorts (fun r y => optValid (extPortRq r y) = false /\ extDataQuiet r y) implRegions mr').
      exact (quiet_dataRpTaken initLine implRegions fwcs _ _ _ L
               ltac:(apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj) Hout Hst Hv).
  Qed.

  (* The data port steps keep the handshake invariant *)
  Lemma handshake_s1' :
    forall g (s1 s1' : IState) (s2 : SState) mr' x o,
      s1' = writeSubTreeState NPMI s1 (mr' ,, x) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> RELG g s1 s2 ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1').
  Proof.
    intros g s1 s1' s2 mr' x o E1 Hst Hg.
    rewrite E1; change (AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions mr').
    destruct Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; unfold WfRel in Hw; destruct Hw as [_ [_ [_ [_ [_ W5]]]]].
    exact (handshake_dataRpStep initLine _ _ _ _ _ Hst W5).
  Qed.

  (* The revoker's cap read is answered: the spec stutters, the value is the spec's at scanAddr *)
  Lemma readRpPorts_revCap :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      g_acc pcAddrInit g = AccRevCap (RdOut false) ->
      RELG g s1 s2 -> RELG (gWithAcc pcAddrInit g (AccRevCap (RdArrived false (optData o)))) s1' s2.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' o EM E1 Hst Hv Eacc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hsent [_ [Hlk Hout]]] [Hreq [Hph [Hdna [Hoff [Hsec _]]]]]].
    destruct (taken_impl s1 s1' mr mst mrq mrp mr' o _ EM E1 Hst Hv Hout) as [ER [Est [Ereq [Edm [Erp' HPQ]]]]].
    pose proof (rp_spec_content g s1 s2 mr' o _ Hm Hout Hst Hv) as Hcont.
    rewrite Hv in E1; cbv iota in E1.
    apply (RefRelG_dataRp_frame g _ s1 s1' s2 _ E1); try reflexivity.
    - rewrite Eacc; reflexivity.
    - intros P HT HN; rewrite E1; exact (AllPorts_dataRpStep P HT HN _ _ _ _ _ Hst).
    - exact (MemRelC_dataRpStep g s1 s1' s2 mr' _ o E1 Hst Hm).
    - unfold AccessRel, RdStageRel, dmNotAccessing, iRevPhase, iScanAddr in *; cbn [gWithAcc g_acc g_revOff].
      rewrite ER, Est, Ereq, Edm, Erp'.
      refine (conj (conj Hsent (conj eq_refl HPQ)) (conj Hreq (conj Hph (conj Hdna (conj _ (conj Hsec eq_refl)))))).
      rewrite Hoff; discriminate.
    - unfold RevokerRel, RevAccRel, RevCapOK in *; cbn [gWithAcc g_acc g_revOff].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite ER; rewrite Eacc in Hrk.
      destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      refine (conj K1 (conj K2 (conj K3 (conj K4 _)))).
      rewrite Hoff; split; [exact Hlk |].
      unfold lineVal, memValAt; rewrite Hcont; reflexivity.
    - exact (handshake_s1' g s1 s1' s2 mr' _ o E1 Hst Hg).
    - exact Hg.
  Qed.

  (* The revoker's rev-bit read is answered: the spec stutters, the value is the spec's *)
  Lemma readRpPorts_revBit :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      g_acc pcAddrInit g = AccRevBit (RdOut false) ->
      RELG g s1 s2 -> RELG (gWithAcc pcAddrInit g (AccRevBit (RdArrived false (optData o)))) s1' s2.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' o EM E1 Hst Hv Eacc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hsent [_ [Hlk Hout]]] [Hreq [Hph [Hdna [Hoff [Hsec _]]]]]].
    destruct (taken_impl s1 s1' mr mst mrq mrp mr' o _ EM E1 Hst Hv Hout) as [ER [Est [Ereq [Edm [Erp' HPQ]]]]].
    pose proof (rp_spec_content g s1 s2 mr' o _ Hm Hout Hst Hv) as Hcont.
    rewrite Hv in E1; cbv iota in E1.
    apply (RefRelG_dataRp_frame g _ s1 s1' s2 _ E1); try reflexivity.
    - rewrite Eacc; reflexivity.
    - intros P HT HN; rewrite E1; exact (AllPorts_dataRpStep P HT HN _ _ _ _ _ Hst).
    - exact (MemRelC_dataRpStep g s1 s1' s2 mr' _ o E1 Hst Hm).
    - unfold AccessRel, RdStageRel, dmNotAccessing, iRevPhase, iRevScanBase in *; cbn [gWithAcc g_acc g_revOff].
      rewrite ER, Est, Ereq, Edm, Erp'.
      exact (conj (conj Hsent (conj eq_refl HPQ)) (conj Hreq (conj Hph (conj Hdna (conj Hoff (conj Hsec eq_refl)))))).
    - unfold RevokerRel, RevAccRel in *; cbn [gWithAcc g_acc g_revOff].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite ER; rewrite Eacc in Hrk.
      destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      refine (conj K1 (conj K2 (conj K3 (conj K4 _)))).
      unfold lineVal, memValAt; rewrite Hcont; reflexivity.
    - exact (handshake_s1' g s1 s1' s2 mr' _ o E1 Hst Hg).
    - exact Hg.
  Qed.

  (* dataMem's rev-byte read (`AccDmRev`) is answered: the spec stutters, the value is the spec's *)
  Lemma readRpPorts_dmRev :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o rc,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      g_acc pcAddrInit g = AccDmRev rc (RdOut false) ->
      RELG g s1 s2 -> RELG (gWithAcc pcAddrInit g (AccDmRev rc (RdArrived false (optData o)))) s1' s2.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' o rc EM E1 Hst Hv Eacc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hsent [_ [Hlk Hout]]] [Hreq [Hdr [Hdv [Hrnr [Hoff [Hsec [Hcn [_ [Hbr _]]]]]]]]]].
    destruct (taken_impl s1 s1' mr mst mrq mrp mr' o _ EM E1 Hst Hv Hout) as [ER [Est [Ereq [Edm [Erp' HPQ]]]]].
    pose proof (rp_spec_content g s1 s2 mr' o _ Hm Hout Hst Hv) as Hcont.
    rewrite Hv in E1; cbv iota in E1.
    apply (RefRelG_dataRp_frame g _ s1 s1' s2 _ E1); try reflexivity.
    - rewrite Eacc; reflexivity.
    - intros P HT HN; rewrite E1; exact (AllPorts_dataRpStep P HT HN _ _ _ _ _ Hst).
    - exact (MemRelC_dataRpStep g s1 s1' s2 mr' _ o E1 Hst Hm).
    - unfold AccessRel, RdStageRel, revNotReading, iRevPhase in *; cbn [gWithAcc g_acc g_revOff g_cnwb].
      rewrite ER, Est, Ereq, Edm, Erp'.
      refine (conj (conj Hsent (conj eq_refl HPQ))
                (conj Hreq (conj Hdr (conj Hdv (conj Hrnr (conj Hoff (conj Hsec (conj Hcn (conj eq_refl (conj Hbr _)))))))))).
      unfold lineVal, memValAt; rewrite Hcont; reflexivity.
    - unfold RevokerRel, RevAccRel in *; cbn [gWithAcc g_acc g_revOff].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite ER; rewrite Eacc in Hrk.
      destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      exact (conj K1 (conj K2 (conj K3 (conj K4 I)))).
    - exact (handshake_s1' g s1 s1' s2 mr' _ o E1 Hst Hg).
    - exact Hg.
  Qed.

  (* --- 7. Assembly --- *)

  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).

  (* While every region has all its reads answered, no response comes *)
  Lemma dataRp_quiet :
    forall (P : forall r, TS (implExternalMemRegionTree r) -> Prop), (forall r y, P r y -> extDataQuiet r y) ->
      forall l fs (mi mi' : TS (implRegionsTree l)) o,
        AllPorts P l mi -> DataRpPortStepL initLine fs l mi mi' o -> optValid o = false.
  Proof.
    intros P HP; induction l as [| r rs IH]; intros fs mi mi' o H Hst; [destruct Hst |].
    cbn [AllPorts] in H; cbn [DataRpPortStepL] in Hst; destruct H as [H0 H1].
    destruct Hst as [[Hs _] | [_ [_ Hrest]]]; [| exact (IH _ _ _ _ H1 Hrest)].
    clear IH H1; revert H0 Hs; generalize (mi.(Fst)) (mi'.(Fst)).
    unfold RegionPort, RegionDataRpStep, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs; [| destruct Hs].
    destruct Hs as [[Hf _] | [Hlt _]]; [exact Hf |].
    exfalso; pose proof (HP _ y H0) as Hq; unfold extDataQuiet in Hq; rewrite Hq in Hlt.
    exact (Nat.lt_irrefl _ Hlt).
  Qed.

  Local Abbreviation PRS := (PortsReadStaged pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PWS := (PortsWriteStaged pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* A response comes only for a read that is out *)
  Lemma AccessRel_rdOut :
    forall g (s1 : IState) (s2 : SState) mr' o,
      ACC g s1 s2 -> DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      (exists ld pkt0 b, g_acc pcAddrInit g = AccLoad ld pkt0 (RdOut b)) \/
      (exists rc, g_acc pcAddrInit g = AccDmRev rc (RdOut false)) \/
      g_acc pcAddrInit g = AccRevCap (RdOut false) \/ g_acc pcAddrInit g = AccRevBit (RdOut false).
  Proof.
    intros g s1 s2 mr' o Ha Hst Hv.
    assert (HQ1 : ~ PQ s1).
    { intros H; unfold PortsQuiet in H.
      assert (Hq : optValid o = false)
        by (refine (dataRp_quiet _ _ _ _ _ _ _ H Hst); intros r y Hp; exact (proj2 Hp)).
      rewrite Hq in Hv; discriminate Hv. }
    assert (HQ2 : forall L, ~ PRS L s1).
    { intros L H; unfold PortsReadStaged in H.
      assert (Hq : optValid o = false)
        by (refine (dataRp_quiet _ _ _ _ _ _ _ H Hst); intros r y Hp; exact (proj1 Hp)).
      rewrite Hq in Hv; discriminate Hv. }
    assert (HQ3 : forall L rq, ~ PWS L rq s1).
    { intros L rq H; unfold PortsWriteStaged in H.
      assert (Hq : optValid o = false)
        by (refine (dataRp_quiet _ _ _ _ _ _ _ H Hst); intros r y Hp; exact (proj1 Hp)).
      rewrite Hq in Hv; discriminate Hv. }
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [b|b] | ld pkt0 [b|b|b|b rp|res]
                                     | rc [b|b|b|b rp|res] | [b|b|b|b rp|res]
                                     | [b|b|b|b rp|res] | addr pkt [b|b]];
      unfold WrStageRel, RdStageRel, rdSecond, wrSecond in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (exfalso; first [ match goal with H : PQ s1 |- _ => exact (HQ1 H) end
                          | match goal with H : PRS _ s1 |- _ => exact (HQ2 _ H) end
                          | match goal with H : PWS _ _ s1 |- _ => exact (HQ3 _ _ H) end ]).
    all: try match goal with H : ?b = false |- _ => is_var b; subst b end.
    - left; eexists _, _, _; reflexivity.
    - right; left; eexists; reflexivity.
    - right; right; left; reflexivity.
    - right; right; right; reflexivity.
  Qed.

  (* `readRpPorts` refines the spec, given the commits of the load lines (`AccLoad .. (RdOut b)`) *)
  Theorem stepOK_readRpPorts_of :
    (forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o ld pkt0 b,
       iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
       s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
       DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
       g_acc pcAddrInit g = AccLoad ld pkt0 (RdOut b) -> RELG g s1 s2 ->
       exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2') ->
    forall act,
      In act (@readRpPorts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
      STEPOK act.
  Proof.
    intros HL act Hin s1 s1' s2 Hsem [g Hg].
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    destruct (readRpPorts_mem act s1 s1' Hin Hsem mr mst mrq mrp EM) as [[_ E1] | [_ [mr' [o [Hst E1]]]]].
    - exists s2; split; [apply NilAction; reflexivity | exists g; rewrite E1; exact Hg].
    - assert (Emr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
      assert (Hdec : optValid o = true \/ optValid o = false) by (destruct (optValid o); [left | right]; reflexivity).
      destruct Hdec as [Hv | Hv].
      + rewrite <- Emr in Hst.
        pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
        destruct (AccessRel_rdOut g s1 s2 mr' o Ha Hst Hv) as [[ld [pkt0 [b Eacc]]] | [[rc Eacc] | [Eacc | Eacc]]].
        * exact (HL g s1 s1' s2 mr mst mrq mrp mr' o ld pkt0 b EM E1 Hst Hv Eacc Hg).
        * exists s2; split; [apply NilAction; reflexivity |].
          eexists; exact (readRpPorts_dmRev g s1 s1' s2 mr mst mrq mrp mr' o rc EM E1 Hst Hv Eacc Hg).
        * exists s2; split; [apply NilAction; reflexivity |].
          eexists; exact (readRpPorts_revCap g s1 s1' s2 mr mst mrq mrp mr' o EM E1 Hst Hv Eacc Hg).
        * exists s2; split; [apply NilAction; reflexivity |].
          eexists; exact (readRpPorts_revBit g s1 s1' s2 mr mst mrq mrp mr' o EM E1 Hst Hv Eacc Hg).
      + exists s2; split; [apply NilAction; reflexivity |].
        exists g; exact (readRpPorts_noValid g s1 s1' s2 mr mst mrq mrp mr' o EM E1 Hst Hv Hg).
  Qed.
End ReadRpPorts.
