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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic Spec.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefPeriph RefFrame.
From Cheriot.Proof Require Import RefSpecRead RefMemStep RefExecAux RefExecFrame RefDecodeStep RefPcEven RefFetchRqImpl.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 6: `fetchRqStage` (the spec stutters)
 * ===========================================================================
 * Branches (RefFetchRqImpl.v): nothing happens; a prefaulted entry is enqueued; the line's region
 * takes the request and the entry is enqueued (the request is the newest accepted one of that
 * region, matching the new entry in `FetchRespRel`); or the region refuses it (only its traces
 * change). The new entry is live, continues the fetchBuf chain at fetchPc, and its predicted PC
 * (the new fetchPc) is even. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Lists and Lines --- *)

Lemma lineAddrOf_idem : forall x, lineAddrOf (lineAddrOf x) = lineAddrOf x.
Proof.
  intros x; unfold lineAddrOf, memLineAddr; cbn [evalExpr].
  rewrite Zmod_lastn_app by (cbv; congruence).
  reflexivity.
Qed.

Lemma FbChain_snoc :
  forall l f, FbChain l (fbPcAddr f) -> FbChain (l ++ [f]) (fbPredPc f).
Proof.
  intros l; induction l as [| x l IH]; intros f H; [reflexivity |].
  destruct l as [| y l'].
  - cbn in H |- *; split; [exact H | reflexivity].
  - cbn [app] in IH |- *; cbn [FbChain] in H |- *.
    destruct H as [H1 H2]; split; [exact H1 | exact (IH f H2)].
Qed.

Lemma filter_nil_head :
  forall {A : Type} (p : A -> bool) x l, filter p (x :: l) = [] -> p x = false.
Proof. intros A p x l H; cbn [filter] in H; destruct (p x); [discriminate H | reflexivity]. Qed.

Lemma StalePrefix_snoc :
  forall {A : Type} (p : A -> bool) l x, StalePrefix p l -> p x = true -> StalePrefix p (l ++ [x]).
Proof.
  intros A p l x [l1 [l2 [E [F1 F2]]]] Hx.
  exists l1, (l2 ++ [x])%list; split; [rewrite E, app_assoc; reflexivity |].
  split; [exact F1 | apply Forall_app; split; [exact F2 | constructor; [exact Hx | constructor]]].
Qed.

(* --- 2. The Relation Across a Fetch Request --- *)

Section FetchRqStep.
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
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation STEPOK :=
    (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
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
  Local Abbreviation iFlushA := (ACC iFlush).
  Local Abbreviation iRegionsA := (ACC iRegions).
  Local Abbreviation iFetchBufA := (ACC iFetchBuf).
  Local Abbreviation iInstBufA := (ACC iInstBuf).
  Local Abbreviation iD2aA := (ACC iD2a).
  Local Abbreviation iExecEpochA := (ACC iExecEpoch).
  Local Abbreviation iFenceIPendingA := (ACC iFenceIPending).
  Local Abbreviation iPccA := (ACC iPcc).
  Local Abbreviation iRevA := (ACC iRev).
  Local Abbreviation olderWritersA := (ACC olderWriters).
  Local Abbreviation daLiveA := (ACC daLive).
  Local Abbreviation aiLiveA := (ACC aiLive).
  Local Abbreviation fbLiveA := (ACC fbLive).
  Local Abbreviation liveInstsA := (ACC liveInsts).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* A port predicate that reads neither the fetch requests nor their readies *)
  Definition FrqInsensitive (P : forall r, TS (implExternalMemRegionTree r) -> Prop) : Prop :=
    forall r y L rdy, P r (fetchRqUpd r y L rdy) = P r y.

  (* --- 2A. The Memory Side --- *)

  Lemma iRev_fetchRq :
    forall (s1 s1' : IState) mr' A v,
      iRegionsA s1' = mr' -> FetchRqAtL A v implRegions (iRegionsA s1) mr' -> iRevA s1' = iRevA s1.
  Proof.
    intros s1 s1' mr' A v Ei Hat.
    unfold iRev, implRevState; rewrite Ei.
    rewrite (regionStateAt_fetchRqAt _ _ _ _ _ _ _ _ Hat) by exact I; reflexivity.
  Qed.

  Lemma MemRelC_fetchRq :
    forall g (s1 s1' : IState) (s2 : SState) mr' A v,
      iRegionsA s1' = mr' -> FetchRqAtL A v implRegions (iRegionsA s1) mr' -> MEMC g s1 s2 -> MEMC g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' A v Ei Hat Hm.
    unfold MemRelC, MemRel, DevInv in *; rewrite Ei.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_fetchRqAt _ _ _ _ _ _ _ _ Hat) by exact I.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    eapply MemRelPre_fetchRqAt; [exact Hat | exact Hpre].
  Qed.

  (* The components that read neither the frontend nor the wait bits, across a memory step that
   * only logs a fetch request *)
  Lemma core_fetchRq :
    forall g (s1 s1' : IState) (s2 : SState) mr' A v,
      iRfA s1' = iRfA s1 -> iMemA s1' = (mr' ,, (iMemA s1).(Snd)) -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      FetchRqAtL A v implRegions (iRegionsA s1) mr' ->
      RELG g s1 s2 ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 /\
      MEMC g s1' s2 /\
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' /\
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      (forall P, FrqInsensitive P -> AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)).
  Proof.
    intros g s1 s1' s2 mr' A v Erf Emem Edm Emd Hat H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    assert (Ei : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
    assert (HP : forall P, FrqInsensitive P -> AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P HP; rewrite Ei; exact (AllPorts_fetchRqAt P HP _ _ _ _ _ Hat)).
    pose proof (iRev_fetchRq s1 s1' mr' A v Ei Hat) as HR.
    destruct H as [Hrf Hm _ _ _ Ha Hc Hd _ _ _ _ Hrk].
    split; [unfold RfRel in *; rewrite Efl; exact Hrf |].
    split; [exact (MemRelC_fetchRq g s1 s1' s2 mr' A v Ei Hat Hm) |].
    split.
    { eapply AccessRel_frame_ports with (s1 := s1) (s2 := s2); try reflexivity.
      - unfold PortsQuiet; apply HP; intros r y L rdy; reflexivity.
      - intros L; unfold PortsReadStaged; apply HP; intros r y L' rdy; reflexivity.
      - intros L; unfold PortsReadOut; apply HP; intros r y L' rdy; reflexivity.
      - intros L rq; unfold PortsWriteStaged; apply HP; intros r y L' rdy; reflexivity.
      - exact HR.
      - unfold iMemSt; rewrite Emem; reflexivity.
      - unfold iReadRp; rewrite Emem; reflexivity.
      - unfold iRequester; rewrite Emem; reflexivity.
      - unfold iDmSt; rewrite Edm; reflexivity.
      - exact Ha. }
    split; [unfold CnwbRel in *; unfold iDmSt in *; rewrite Edm; exact Hc |].
    split; [unfold DmQueueRel, iDmBuf in *; rewrite Edm; exact Hd |].
    split; [| exact HP].
    eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2); try reflexivity; [exact HR | exact Hrk].
  Qed.

  (* --- 2B. The Frontend --- *)

  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation FRREL := (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 initLine fwcs).
  Local Abbreviation FRONTIER := (FrontierRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                    initLine fwcs).

  Lemma fifo_to_list_enq_nf :
    forall cap k (f : TS (fifoTree cap k)) v,
      fifo_wf f -> Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) = false ->
      fifo_to_list (fifoEnqState f v) = (fifo_to_list f ++ [v])%list.
  Proof.
    intros cap k f v Hwf Hnf.
    rewrite fifo_size_eqb_cap in Hnf; apply Nat.eqb_neq in Hnf.
    apply fifo_to_list_enq; [exact Hwf |].
    pose proof (length_fifo_to_list_le cap k f Hwf) as Hle.
    rewrite (length_fifo_to_list cap k f Hwf) in Hle |- *; lia.
  Qed.

  (* A new live entry at the end of fetchBuf, from fetchPc, predicting the new fetchPc *)
  Lemma FrontierRel_enq :
    forall (s1 s1' : IState) (s2 : SState) e fp,
      iFetchBufA s1' = (iFetchBufA s1 ++ [e])%list ->
      ACC iFetchPc s1' = fbPredPc e -> fbPcAddr e = ACC iFetchPc s1 ->
      ACC iCurParcel s1' = ACC iCurParcel s1 -> ACC iStraddle s1' = ACC iStraddle s1 ->
      fbLiveA s1' = fbLiveA s1 -> fbLiveA s1 e = true -> iPccA s1' = iPccA s1 ->
      fbFetchExc e = preExcAt (iPccA s1) (fbPcAddr e) ->
      (optValid (ACC iCurParcel s1) = true -> iFetchBufA s1 <> []) ->
      FRONTIER s1 s2 fp -> FRONTIER s1' s2 fp.
  Proof.
    intros s1 s1' s2 e fp Efb Efpc Epc Ecp Estr Elv He Epcc Hexc Hwf H.
    unfold FrontierRel in *; cbv zeta in *.
    rewrite Efb, Efpc, Ecp, Estr, Elv, Epcc.
    rewrite filter_app; cbn [filter]; rewrite He.
    destruct H as [Hch [Hx [Hm Hal]]].
    split; [apply FbChain_snoc; rewrite Epc; exact Hch |].
    split; [apply Forall_app; split; [exact Hx | constructor; [exact Hexc | constructor]] |].
    split; [| exact Hal].
    destruct (optValid (ACC iStraddle s1)).
    - destruct Hm as [A1 [A2 [A3 [A4 A5]]]].
      refine (conj A1 (conj A2 (conj A3 (conj A4 _)))).
      destruct (filter (fbLiveA s1) (iFetchBufA s1)) as [| f l]; cbn [app]; [rewrite Epc; exact A5 | exact A5].
    - destruct (iFetchBufA s1) as [| f0 fb0].
      + cbn [filter app] in Hm |- *.
        rewrite He.
        destruct (optValid (ACC iCurParcel s1)); [exfalso; exact (Hwf eq_refl eq_refl) |].
        cbn [andb]; rewrite Epc; exact Hm.
      + cbn [app].
        destruct (filter (fbLiveA s1) (f0 :: fb0)) as [| f l] eqn:El.
        * cbn [app]; rewrite (filter_nil_head _ _ _ El); cbn [andb]; rewrite Epc; exact Hm.
        * cbn [app]; exact Hm.
  Qed.

  (* The relation after an enqueue: the memory side is given by the caller *)
  Lemma fetch_enq :
    forall g (s1 s1' : IState) (s2 : SState) m nio,
      ACC frFull s1 = false -> iFenceIPendingA s1 = false -> anyWait implRegions (iRegionsA s1) = false ->
      ACC FrqStep s1 s1' m (ACC frEnqF s1 (ACC frEntry s1 nio)) ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 ->
      MEMC g s1' s2 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' ->
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      (forall P, FrqInsensitive P -> AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      (iFetchBufA s1' = (iFetchBufA s1 ++ [ACC frEntry s1 nio])%list -> fbLiveA s1' = fbLiveA s1 -> FRREL s1' s2) ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 m nio Hf Hfip Hw [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] Crf Cm Ca Cc Cd Crk HP Cfr H.
    set (e := ACC frEntry s1 nio) in *.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Eib : iInstBufA s1' = iInstBufA s1) by (unfold iInstBuf; rewrite Efe; reflexivity).
    assert (Epe : ACC iPredEpoch s1' = ACC iPredEpoch s1) by (unfold iPredEpoch; rewrite Efe; reflexivity).
    assert (Ecp : ACC iCurParcel s1' = ACC iCurParcel s1) by (unfold iCurParcel; rewrite Efe; reflexivity).
    assert (Estr : ACC iStraddle s1' = ACC iStraddle s1) by (unfold iStraddle; rewrite Efe; reflexivity).
    assert (Efpc : ACC iFetchPc s1' = fbPredPc e) by (unfold iFetchPc; rewrite Efe; reflexivity).
    assert (Edl : daLiveA s1' = daLiveA s1) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA s1' = aiLiveA s1) by (unfold aiLive; rewrite Eep; reflexivity).
    assert (Elv : fbLiveA s1' = fbLiveA s1) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
    assert (He : fbLiveA s1 e = true).
    { unfold fbLive.
      change (andb (Zmod.eqb (iExecEpochA s1) (iExecEpochA s1)) (Zmod.eqb (ACC iPredEpoch s1) (ACC iPredEpoch s1)) = true).
      rewrite !Zmod.eqb_refl; reflexivity. }
    destruct H as [_ _ Hl Hrp He' _ _ _ Hfe Hs Hfr Hwf].
    destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    assert (Efb : iFetchBufA s1' = (iFetchBufA s1 ++ [e])%list).
    { unfold iFetchBuf; rewrite Efe.
      change (fifo_to_list (fifoEnqState (FBF s1) e) = (fifo_to_list (FBF s1) ++ [e])%list).
      exact (fifo_to_list_enq_nf _ _ _ _ W1a Hf). }
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - unfold FenceRel; split; [| split].
      + intros C; rewrite Efip, Hfip in C; discriminate C.
      + intros C; exfalso; apply C.
        unfold NoFenceIWait; rewrite HP by (intros r y L rdy; reflexivity).
        exact (anyWait_false _ _ Hw).
      + intros G1 e0 G2 Hc Hfi; destruct (proj2 (proj2 Hfe) G1 e0 G2 Hc Hfi) as [Hp _].
        rewrite Hfip in Hp; discriminate Hp.
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel; rewrite Ed2a, Edl, Eib, Eal, Efb, Elv, Eep.
      refine (conj F1 (conj F2 (conj (StalePrefix_snoc _ _ _ F3 He) (conj F4 (conj _ (conj _ (Cfr Efb Elv))))))).
      + intros Hx; apply Forall_app; split; [exact (F5 Hx) | constructor; [exact (Zmod.eqb_refl _) | constructor]].
      + assert (Elive : liveInstsA g s1' = liveInstsA g s1)
          by (unfold liveInsts; rewrite Ed2a, Eib, Edl, Eal; reflexivity).
        unfold LiveChain in *; rewrite Elive, Epcc.
        refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                  (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
        intros p Hp; exact (FrontierRel_enq s1 s1' s2 e p Efb Efpc eq_refl Ecp Estr Elv He Epcc eq_refl W1b Hp).
    - unfold WfRel; rewrite Ecp, Efb, Epcc, Ed2a, Eib.
      rewrite HP by (intros r y L rdy; reflexivity).
      split; [split; [rewrite Efe; exact (fifo_wf_enq _ _ _ _ W1a) |] |].
      + split; [intros _ C; apply app_eq_nil in C as [_ C]; discriminate C |].
        split; [exact W1c |]; split; [exact W1d |]; split; [exact W1e |].
        apply Forall_app; split; [exact W1f | constructor; [exact (pcAligned_clear _) | constructor]].
      + split; [rewrite Efe; exact W2 |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
    - exact Crk.
  Qed.

  (* The relation after a refused request: fetch is unchanged *)
  Lemma fetch_mem :
    forall g (s1 s1' : IState) (s2 : SState) m,
      ACC FrqStep s1 s1' m (iFetchA s1) ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 ->
      MEMC g s1' s2 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' ->
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      (forall P, FrqInsensitive P -> AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      FRREL s1' s2 ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 m [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] Crf Cm Ca Cc Cd Crk HP Cfr H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    destruct H as [_ _ Hl Hrp He' _ _ _ Hfe Hs Hfr Hwf].
    constructor; try assumption.
    - unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *.
      rewrite HP by (intros r y L rdy; reflexivity).
      rewrite Efe, Ed2a, Eep, Efip; exact Hfe.
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel, daLive, aiLive, fbLive, iInstBuf, iFetchBuf, iPredEpoch in *.
      rewrite Ed2a, Eep, Efe.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj _ Cfr)))))).
      assert (Elive : liveInstsA g s1' = liveInstsA g s1)
        by (unfold liveInsts, daLive, aiLive, iInstBuf; rewrite Ed2a, Eep, Efe; reflexivity).
      unfold LiveChain in *; rewrite Elive, Epcc.
      refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
      intros p Hp; unfold FrontierRel, fbLive, iFetchBuf, iCurParcel, iStraddle, iFetchPc, iPredEpoch in Hp |- *.
      rewrite Efe, Eep, Epcc; exact Hp.
    - unfold WfRel, iCurParcel, iFetchBuf, iInstBuf, iPcc, iD2a in *.
      rewrite HP by (intros r y L rdy; reflexivity).
      rewrite Erf, Efe, ED, Edm, Emd; exact Hwf.
  Qed.

  (* --- 2C. Fetch Responses --- *)

  (* A prefaulted entry has no request *)
  Lemma FetchRespRel_pre :
    forall (s1 s1' : IState) (s2 : SState) e,
      iRegionsA s1' = iRegionsA s1 -> iFetchBufA s1' = (iFetchBufA s1 ++ [e])%list -> fbLiveA s1' = fbLiveA s1 ->
      excAny (fbFetchExc e) = true ->
      FRREL s1 s2 -> FRREL s1' s2.
  Proof.
    intros s1 s1' s2 e Ereg Efb Elv Hexc H.
    unfold FetchRespRel in *; rewrite Ereg.
    revert H; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
    assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                 fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r).
    { unfold fbInRegion; rewrite Efb, filter_app; cbn [filter]; rewrite Hexc; cbn [negb andb].
      apply app_nil_r. }
    rewrite EE, Elv; exact HC.
  Qed.

  (* The request the line's region accepted is the new entry's *)
  Lemma FetchRespRel_acc :
    forall (s1 s1' : IState) (s2 : SState) e mr',
      FetchRqAtL (lineAddrOf (ACC iFetchPc s1)) true implRegions (iRegionsA s1) mr' -> iRegionsA s1' = mr' ->
      iFetchBufA s1' = (iFetchBufA s1 ++ [e])%list -> fbLiveA s1' = fbLiveA s1 ->
      fbPcAddr e = ACC iFetchPc s1 -> excAny (fbFetchExc e) = false ->
      FRREL s1 s2 -> FRREL s1' s2.
  Proof.
    intros s1 s1' s2 e mr' Hat Ereg Efb Elv Epc Hexc H.
    pose proof (lineUnique_implRegions pre post revBase revPfB revPfA (lineAddrOf (ACC iFetchPc s1))
                  (Is_true_eq_true _ Hdisj)) as Hu.
    unfold FetchRespRel in *; rewrite Ereg.
    refine (AllPorts_fetchRqAt_impl _ _ _ _ _ _ _ _ _ Hu Hat H).
    - intros r y Hm HC; cbv zeta in HC |- *.
      destruct HC as [C [HC1 [HC2 HC3]]].
      assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                   (fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r ++ [e])%list).
      { unfold fbInRegion; rewrite Efb, filter_app; cbn [filter]; rewrite Hexc, Epc, Hm; reflexivity. }
      rewrite EE, Elv.
      exists C; split; [| split; [exact HC2 |]].
      + change (lineAddrOf (lineAddrOf (ACC iFetchPc s1)) :: implFetchAccRqs r y =
                (rev (map (fun f => lineAddrOf (fbPcAddr f))
                          (fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r ++ [e])) ++ C)%list).
        rewrite HC1, lineAddrOf_idem, map_app, rev_app_distr; cbn [map rev app]; rewrite Epc; reflexivity.
      + intros Hv; destruct (HC3 Hv) as [f [E' [HE Hl']]].
        exists f, (E' ++ [e])%list; split; [rewrite HE; reflexivity | exact Hl'].
    - intros r y Hm HC; cbv zeta in HC |- *.
      assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                   fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r).
      { unfold fbInRegion; rewrite Efb, filter_app; cbn [filter]; rewrite Hexc, Epc, Hm; cbn [negb andb].
        apply app_nil_r. }
      rewrite EE, Elv; exact HC.
  Qed.

  (* A refused request leaves the accepted ones *)
  Lemma FetchRespRel_rej :
    forall (s1 s1' : IState) (s2 : SState) mr' A,
      FetchRqAtL A false implRegions (iRegionsA s1) mr' -> iRegionsA s1' = mr' ->
      iFetchBufA s1' = iFetchBufA s1 -> fbLiveA s1' = fbLiveA s1 ->
      FRREL s1 s2 -> FRREL s1' s2.
  Proof.
    intros s1 s1' s2 mr' A Hat Ereg Efb Elv H.
    pose proof (lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    assert (EE : forall r, fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                           fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r)
      by (intros r; unfold fbInRegion; rewrite Efb; reflexivity).
    unfold FetchRespRel in *; rewrite Ereg.
    refine (AllPorts_fetchRqAt_impl _ _ _ _ _ _ _ _ _ Hu Hat H).
    - intros r y _ HC; cbv zeta in HC |- *; rewrite EE, Elv; exact HC.
    - intros r y _ HC; cbv zeta in HC |- *; rewrite EE, Elv; exact HC.
  Qed.

  (* --- 3. The Theorem --- *)

  Local Abbreviation FRQSTEP := (FrqStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Lemma frq_fetchBuf :
    forall (s1 s1' : IState) m nio,
      FRQSTEP s1 s1' m (ACC frEnqF s1 (ACC frEntry s1 nio)) ->
      fifo_wf (FBF s1) -> ACC frFull s1 = false ->
      iFetchBufA s1' = (iFetchBufA s1 ++ [ACC frEntry s1 nio])%list /\ fbLiveA s1' = fbLiveA s1.
  Proof.
    intros s1 s1' m nio [_ [_ [_ [Efe [_ [Eex _]]]]]] Hwf Hf; split.
    - unfold iFetchBuf; rewrite Efe.
      change (fifo_to_list (fifoEnqState (FBF s1) (ACC frEntry s1 nio)) =
              (fifo_to_list (FBF s1) ++ [ACC frEntry s1 nio])%list).
      exact (fifo_to_list_enq_nf _ _ _ _ Hwf Hf).
    - unfold fbLive, iExecEpoch, iPredEpoch; rewrite Eex, Efe; reflexivity.
  Qed.

  Theorem stepOK_fetchRqStage : STEPOK STAGE.
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    exists s2; split; [apply NilAction; reflexivity |].
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    pose proof Hg as [_ _ _ _ _ _ _ _ _ _ Hfr0 Hw0 _].
    pose proof (proj1 (proj1 Hw0)) as Wfb.
    pose proof Hfr0 as [_ [_ [_ [_ [_ [_ F7]]]]]].
    destruct (andb (negb (ACC frFull s1)) (andb (negb (iFenceIPendingA s1)) (negb (anyWait implRegions (iRegionsA s1)))))
      eqn:Hgo.
    2: { rewrite (fetchRq_idle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    _ s1 s1' Hsem Hgo); exists g; exact Hg. }
    apply andb_prop in Hgo as [Hf Hgo]; apply andb_prop in Hgo as [Hfip Hw].
    apply negb_true_iff in Hf, Hfip, Hw.
    exists g.
    destruct (excAny (ACC frExc s1)) eqn:Hpre.
    - pose proof (fetchRq_pre pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    _ s1 s1' Hsem Hf Hfip Hw Hpre) as Hst.
      pose proof Hst as [Erf [_ [Emem [_ [_ [_ [Edm Emd]]]]]]].
      assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
      destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem Edm Emd Hg)
        as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
      refine (fetch_enq g s1 s1' s2 _ _ Hf Hfip Hw Hst Crf Cm Ca Cc Cd Crk _ _ Hg).
      + intros P _; rewrite Ereg; reflexivity.
      + intros Efb Elv; exact (FetchRespRel_pre s1 s1' s2 _ Ereg Efb Elv Hpre F7).
    - destruct (fetchRq_noPre pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  _ s1 s1' Hu Hsem Hf Hfip Hw Hpre) as [mr' [rdy [Hat [Hk Hst]]]].
      destruct rdy.
      + destruct Hst as [nio Hst].
        pose proof Hst as [Erf [_ [Emem [_ [_ [_ [Edm Emd]]]]]]].
        destruct (core_fetchRq g s1 s1' s2 mr' _ true Erf Emem Edm Emd Hat Hg)
          as [Crf [Cm [Ca [Cc [Cd [Crk HP]]]]]].
        assert (Ereg : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
        refine (fetch_enq g s1 s1' s2 _ _ Hf Hfip Hw Hst Crf Cm Ca Cc Cd Crk HP _ Hg).
        intros Efb Elv; exact (FetchRespRel_acc s1 s1' s2 _ mr' Hat Ereg Efb Elv eq_refl Hpre F7).
      + pose proof Hst as [Erf [_ [Emem [Efe [_ [Eex [Edm Emd]]]]]]].
        destruct (core_fetchRq g s1 s1' s2 mr' _ false Erf Emem Edm Emd Hat Hg)
          as [Crf [Cm [Ca [Cc [Cd [Crk HP]]]]]].
        assert (Ereg : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
        refine (fetch_mem g s1 s1' s2 _ Hst Crf Cm Ca Cc Cd Crk HP _ Hg).
        refine (FetchRespRel_rej s1 s1' s2 mr' _ Hat Ereg _ _ F7).
        * unfold iFetchBuf; rewrite Efe; reflexivity.
        * unfold fbLive, iExecEpoch, iPredEpoch; rewrite Eex, Efe; reflexivity.
  Qed.
End FetchRqStep.
