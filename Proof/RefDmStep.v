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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute SimDataMem GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker.
From Cheriot.Proof Require Import RefExecAux RefExecLive RefLoadCommit RefDmImpl.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 5: THE DATAMEM WRITE-BACK STAGES (RELATION SIDE)
 * ===========================================================================
 * - `flushMulDivCaps_writeGprVal`: a GPR write commutes with the mulDiv flush of other registers.
 * - `RefRelG_dmWb`: a dataMem write-back of the committed, not written back load (`g_cnwb`):
 *   the value moves into `g_rf0`, the access in flight ends (`AccNone`); the spec stutters.
 * - `stepOK_revRpAndWriteBackStage`. *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma flushMulDivCaps_writeGprVal :
  forall pcAddrInit entries d v (rf : RfState pcAddrInit),
    (forall m c, In (m, c) entries -> Zmod.eqb d Zmod.zero = false -> Zmod.eqb m Zmod.zero = false -> m <> d) ->
    flushMulDivCaps pcAddrInit entries (writeGprVal pcAddrInit d v rf) =
    writeGprVal pcAddrInit d v (flushMulDivCaps pcAddrInit entries rf).
Proof.
  intros pcAddrInit entries; induction entries as [| [m c] rest IH]; intros d v rf H; cbn [flushMulDivCaps];
    [reflexivity |].
  rewrite (writeGprVal_comm pcAddrInit m c d v rf).
  - apply IH; intros m' c' Hin; exact (H m' c' (or_intror Hin)).
  - intros Hm Hd E; exact (H m c (or_introl eq_refl) Hd Hm E).
Qed.

Section DmStep.
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
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

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
  Local Abbreviation GhostT := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation DWS :=
    (DmWbStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA := (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA := (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA := (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmBufA := (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA := (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iPccA := (iPcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA := (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRpReadyA := (iRpReady pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation ARR := (AccessRel_rpReady pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation iD2aA := (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecEpochA := (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA := (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation olderWritersA := (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation dmInFlightDstA := (dmInFlightDst pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PortsQuietA := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation revNotReadingA := (revNotReading pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation EXTA md := (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode md).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind.

  Lemma dmInFlightDst_loadRq :
    forall s1 : IState, dmLoadRq (iDmStA s1) = true -> dmInFlightDstA s1 = [].
  Proof.
    intros s1 H; destruct (dmLoadRq_excl3 _ H) as [E1 [E2 E3]].
    unfold dmInFlightDst; cbv zeta; rewrite E1, E2, E3; reflexivity.
  Qed.

  (* The older writers lose the written-back register, at their front *)
  Lemma olderWriters_dmWb :
    forall (s1 s1' : IState) d v,
      DWS s1 s1' d v -> dmInFlightDstA s1 = [d] ->
      olderWritersA s1 = ((if negb (Zmod.eqb d Zmod.zero) then [d] else []) ++ olderWritersA s1')%list.
  Proof.
    intros s1 s1' d v Hw Hin.
    destruct Hw as [_ _ _ _ _ _ _ _ _ _ Hmd Hdmf Hdmst].
    pose proof (dmInFlightDst_loadRq s1' Hdmst) as Hin'.
    unfold olderWriters; rewrite Hin, Hin'.
    unfold iDmBuf; rewrite Hdmf, Hmd.
    cbn [app filter]; destruct (negb (Zmod.eqb d Zmod.zero)); reflexivity.
  Qed.

  (* The ghost after the write-back of the committed load `g_cnwb g = Some (d, v)` *)
  Definition gWb (g : GhostT) (d : bits RegIdxSzReal) (v : type FullECapWithTag) : GhostT :=
    mkGhost pcAddrInit (g_chain pcAddrInit g) (writeGprVal pcAddrInit d v (g_rf0 pcAddrInit g)) None RevEq
            (g_d2aFo pcAddrInit g) AccNone.

  Lemma RefRelG_dmWb :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState) d v,
      RELG g s1 s2 ->
      g_cnwb pcAddrInit g = Some (d, v) ->
      optValid (iReadRpA s1) = false -> PortsQuietA s1 -> g_revOff pcAddrInit g = RevEq ->
      revNotReadingA s1 -> optValid (sSecondA s2) = false -> accTakesHead (g_acc pcAddrInit g) = false ->
      DWS s1 s1' d v ->
      RELG (gWb g d v) s1' s2.
  Proof.
    intros g s1 s1' s2 d v Hg Hcn Hrp0 HPQ Hoff HrnR Hsec Htake Hw.
    pose proof Hw as Hw0.
    destruct Hw0 as [Erf Ewb Ereg Erq Erp Eidle Erdy Efe Ede Eex Emd Edmf Edmst].
    destruct Hg as [Hrf Hm Hl Hrpl He Ha Hc Hd Hf Hs Hfr Hwf Hrk].
    assert (Hin : dmInFlightDstA s1 = [d]) by (eapply cnwb_dmInFlightDst; eassumption).
    pose proof (olderWriters_dmWb s1 s1' d v Hw Hin) as Eow.
    destruct (dmLoadRq_excl3 _ Edmst) as [Elrp [Errq Errp]].
    assert (Erev : iRevA s1' = iRevA s1) by (unfold iRev; rewrite Ereg; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1)
      by (unfold iPcc; rewrite Erf; apply readPcc_writeGprVal).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite Ede; reflexivity).
    assert (Edmb : iDmBufA s1' = iDmBufA s1) by (unfold iDmBuf; rewrite Edmf; reflexivity).
    (* the mulDiv results avoid `d` *)
    assert (Hmd : forall m c, In (m, c) (EXTA (iMdA s1)) ->
                    Zmod.eqb d Zmod.zero = false -> Zmod.eqb m Zmod.zero = false -> m <> d).
    { intros m c Hmc Hdz Hmz E; subst m.
      destruct Hs as [S1 _].
      rewrite Eow, Hdz in S1; cbn [negb app] in S1.
      inversion S1 as [| ? ? Hnin _]; apply Hnin; apply in_or_app; left.
      unfold olderWriters; apply filter_In; split; [| rewrite Hdz; reflexivity].
      rewrite (dmInFlightDst_loadRq s1' Edmst); cbn [app]; apply in_or_app; right.
      rewrite Emd; apply in_map_iff; exists (d, c); split; [reflexivity | exact Hmc]. }
    assert (Eflush : iFlushA s1' = writeGprVal pcAddrInit d v (iFlushA s1)).
    { unfold iFlush, flushMulDiv, flushMulDivOn.
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1') with (iRfA s1').
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1) with (iRfA s1).
      rewrite Erf, Emd; apply flushMulDivCaps_writeGprVal; exact Hmd. }
    destruct Hrf as [R1 [R2 [R3 R4]]].
    pose proof (R3 d v Hcn) as Hav.
    constructor.
    - (* rr_rf *)
      unfold RfRel; cbn [gWb g_chain g_rf0 g_cnwb cnwbApply].
      split; [rewrite Hcn in R1; exact R1 |].
      split; [rewrite Eflush; exact (GChain_writeGprVal pcAddrInit _ _ _ d v Hav R2) |].
      split; [intros d' v' Hn; discriminate Hn | exact R4].
    - (* rr_mem *)
      unfold MemRelC in *; cbn [gWb g_revOff]; rewrite Hoff in Hm; rewrite Ereg; exact Hm.
    - exact Hl.
    - (* rr_replay *)
      unfold ReplayRel in *; cbn [gWb g_chain g_rf0].
      intros G1 e G2 rfe HG Hch.
      rewrite HG in R2, Hav.
      destruct (GChain_app_inv pcAddrInit G1 _ _ _ R2) as [rfa [Hga _]].
      apply ChainAvoids_app_inv in Hav as [Hav1 _].
      pose proof (GChain_writeGprVal pcAddrInit _ _ _ d v Hav1 Hga) as Hga'.
      rewrite (GChain_det pcAddrInit G1 _ _ _ Hch Hga'), readPcc_writeGprVal.
      exact (Hrpl G1 e G2 rfa HG Hga).
    - exact He.
    - (* rr_acc *)
      unfold AccessRel; cbn [gWb g_acc g_revOff].
      split; [exact Eidle |]; split; [rewrite Erp; exact Hrp0 |]; split; [exact Erdy |].
      split; [unfold PortsQuiet in *; rewrite Ereg; exact HPQ |]; split; [reflexivity |].
      split; [unfold dmNotAccessing; rewrite Elrp, Errp; split; reflexivity |].
      split; [unfold revNotReading, iRevPhase in *; rewrite Erev; exact HrnR | exact Hsec].
    - (* rr_cnwb *)
      unfold CnwbRel; cbn [gWb g_cnwb g_chain g_acc].
      split; [intros _; reflexivity |].
      split; [intros E; rewrite Errq in E; discriminate E |].
      split; [intros E; rewrite Errq in E; discriminate E |].
      intros E; rewrite Elrp in E; discriminate E.
    - (* rr_dmq *)
      unfold DmQueueRel in *; cbn [gWb g_chain g_acc accTakesHead].
      rewrite Htake in Hd; rewrite Edmb; exact Hd.
    - (* rr_fence *)
      unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *; cbn [gWb g_chain].
      rewrite Ereg, Efe, Ed2a, Eep, Efip; exact Hf.
    - (* rr_score *)
      unfold ScoreRel in *; cbv zeta in *; cbn [gWb g_d2aFo].
      rewrite Eow in Hs; destruct Hs as [S1 [S2 [S3 S4]]].
      unfold daLive in *; rewrite Ed2a, Eep, Ewb, Eflush.
      split; [rewrite <- app_assoc in S1; exact (NoDup_app_remove_l _ _ S1) |].
      split.
      + intros r; specialize (S2 r); unfold wbClr.
        destruct (negb (Zmod.eqb d Zmod.zero)) eqn:Ez; cbn [app] in S1, S2 |- *; [| exact S2].
        change (readWaitBit r) with (evalReadWaitBit r) in *.
        assert (Hdz : Zmod.eqb d Zmod.zero = false) by (apply negb_true_iff; exact Ez).
        destruct (Zmod.eqb r d) eqn:Er.
        * apply Zmod.eqb_eq in Er; subst r.
          rewrite (evalReadWaitBit_write_same d false _ Hdz).
          split; [discriminate | intros Hin2; exfalso].
          inversion S1 as [| ? ? Hnin _]; exact (Hnin Hin2).
        * assert (Hne : r <> d) by (intros E; subst r; rewrite Zmod.eqb_refl in Er; discriminate Er).
          rewrite (evalReadWaitBit_write_other r d false _ Hne), S2.
          split; [intros [E | H0]; [exfalso; exact (Hne (eq_sym E)) | exact H0] | intros H0; right; exact H0].
      + split; [exact S3 |].
        intros l1 j l2 fo Hl1 Hnth Hlv.
        destruct (S4 l1 j l2 fo Hl1 Hnth Hlv) as [T1 [T2 T3]].
        assert (Hdin : Zmod.eqb d Zmod.zero = false ->
                       In d (((if negb (Zmod.eqb d Zmod.zero) then [d] else []) ++ olderWritersA s1') ++ d2aWriters l1)%list).
        { intros Hdz; rewrite Hdz; left; reflexivity. }
        split; [| split].
        * rewrite T1; symmetry; apply evalRegRead_writeGprVal.
          -- intros Hdz Hcz; exact (T2 d (Hdin Hdz) Hdz Hcz).
          -- intros Hdz Hcz; exact (T3 d (Hdin Hdz) Hdz Hcz).
        * intros x Hx; apply T2; rewrite <- app_assoc; apply in_or_app; right; exact Hx.
        * intros x Hx; apply T3; rewrite <- app_assoc; apply in_or_app; right; exact Hx.
    - (* rr_front *)
      unfold FrontRel, LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf in *; cbn [gWb g_d2aFo].
      rewrite Epcc, Ereg, Efe, Ed2a, Eep; exact Hfr.
    - (* rr_wf *)
      unfold WfRel, iCurParcel, iFetchBuf, iInstBuf in *.
      rewrite Epcc, Efe, Ed2a, Ede, Edmf, Emd, Ereg; exact Hwf.
    - (* rr_rev *)
      unfold RevokerRel, RevAccRel in *; cbn [gWb g_acc].
      destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite Erev; exact (conj K1 (conj K2 (conj K3 (conj K4 I)))).
  Qed.

  Local Abbreviation REVRP :=
    (@revRpAndWriteBackStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation iMemStA := (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).

  (* The rev-bit response is the spec memory's rev byte: its write is the spec's `revWb` *)
  Lemma revWbVal_revWb :
    forall m rc,
      revWbVal config rc (memValAt pre post revBase revPfB revPfA initLine m (revByteAddrOf config (rcBase rc)) byteSz) =
      revWb config pre post revBase revPfB revPfA initLine m rc.
  Proof. intros m rc; reflexivity. Qed.

  (* Milestone 5: dataMem's rev-bit response and write-back (the spec stutters) *)
  Theorem stepOK_revRpAndWriteBackStage :
    StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
           clintS clint plicS plic initLine fwcs REVRP.
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    destruct (revRpStage_char pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                _ s1 s1' _ Hsem) as [-> | [Hrv [Hr1 [Hr2 Hw]]]].
    { exists s2; split; [apply NilAction; reflexivity | exists g; exact Hg]. }
    exists s2; split; [apply NilAction; reflexivity |].
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    destruct (dmRevRp_excl3 _ Hrv) as [Elrq [Elrp Errq]].
    destruct (msReadRpReady_excl2 _ (ARR g s1 s2 Ha Hr1)) as [Emrq Emsent].
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt st] eqn:Eacc.
    - destruct Ha as [_ [_ [_ [_ [_ [[_ E] _]]]]]]; rewrite Hrv in E; discriminate E.
    - destruct Ha as [_ [E _]]; rewrite Elrq in E; discriminate E.
    - destruct Ha as [_ [_ [E _]]]; rewrite Elrp in E; discriminate E.
    - destruct Ha as [Hst [_ [_ [Erc [HrnR [Hoff [Hsec [Hcn [_ [_ Hval]]]]]]]]]].
      destruct st as [b | b | b | b rp | res]; unfold RdStageRel in Hst; cbv zeta in Hst.
      + destruct Hst as [E _]; rewrite Emrq in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [_ [Eres0 [Hrp0 HPQ]]].
        assert (Eres : optData (iRpReadyA s1) = res) by (rewrite Eres0; reflexivity); clear Eres0.
        exists (gWb g (fst (revWbVal config (dmRevRpV (iDmStA s1)) (optData (iRpReadyA s1))))
                       (snd (revWbVal config (dmRevRpV (iDmStA s1)) (optData (iRpReadyA s1))))).
        apply (RefRelG_dmWb g s1 s1' s2); [exact Hg | | exact Hrp0 | exact HPQ | exact Hoff | exact HrnR |
                                           exact Hsec | rewrite Eacc; reflexivity | exact Hw].
        cbv beta iota in Hval.
        rewrite Hcn, Erc, Eres, Hval, revWbVal_revWb, <- surjective_pairing; reflexivity.
    - destruct Ha as [_ [_ [_ [[_ E] _]]]]; rewrite Hrv in E; discriminate E.
    - destruct Ha as [_ [_ [_ [[_ E] _]]]]; rewrite Hrv in E; discriminate E.
    - destruct Ha as [_ [_ [[_ E] _]]]; rewrite Hrv in E; discriminate E.
  Qed.

  Local Abbreviation iRequesterA := (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation DFR :=
    (DmFrame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* A dataMem step that changes only the memory `state`, the requester, dataMem's state, the access in
   * flight and the committed load's position (not its value) *)
  Lemma RefRelG_dmFrame :
    forall (g g' : GhostT) (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 ->
      g_chain pcAddrInit g' = g_chain pcAddrInit g -> g_rf0 pcAddrInit g' = g_rf0 pcAddrInit g ->
      g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g -> g_revOff pcAddrInit g' = g_revOff pcAddrInit g ->
      g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g ->
      accTakesHead (g_acc pcAddrInit g') = accTakesHead (g_acc pcAddrInit g) ->
      DFR s1 s1' -> olderWritersA s1' = olderWritersA s1 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g' s1' s2 ->
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g' s1' s2 ->
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g' s1' s2 ->
      RELG g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 Hg Ech Erf0 Ecn Eoff Ed2f Etake Hfr' Eow Hacc Hcnw Hrev.
    destruct Hfr' as [Erf Ewb Ereg Erp Efe Ede Eex Emd Edmf].
    destruct Hg as [Hrf Hm Hl Hrpl He Ha Hc Hd Hf Hs Hfr Hwf Hrk].
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite Ede; reflexivity).
    assert (Edmb : iDmBufA s1' = iDmBufA s1) by (unfold iDmBuf; rewrite Edmf; reflexivity).
    assert (Eflush : iFlushA s1' = iFlushA s1).
    { unfold iFlush, flushMulDiv, flushMulDivOn.
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1') with (iRfA s1').
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1) with (iRfA s1).
      rewrite Erf, Emd; reflexivity. }
    constructor.
    - unfold RfRel in *; rewrite Ech, Erf0, Ecn, Eflush; exact Hrf.
    - unfold MemRelC in *; rewrite Eoff, Ereg; exact Hm.
    - unfold LatchRel in *; rewrite Ech; exact Hl.
    - unfold ReplayRel in *; rewrite Ech, Erf0; exact Hrpl.
    - unfold EagerRel in *; rewrite Ech; exact He.
    - exact Hacc.
    - exact Hcnw.
    - unfold DmQueueRel in *; rewrite Ech, Etake, Edmb; exact Hd.
    - unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *; rewrite Ech.
      rewrite Ereg, Efe, Ed2a, Eep, Efip; exact Hf.
    - unfold ScoreRel, daLive in *; rewrite Ed2f, Eow, Ed2a, Eep, Ewb, Eflush; exact Hs.
    - unfold FrontRel, LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf in *; rewrite Ed2f.
      rewrite Epcc, Ereg, Efe, Ed2a, Eep; exact Hfr.
    - unfold WfRel, iCurParcel, iFetchBuf, iInstBuf in *.
      rewrite Epcc, Efe, Ed2a, Ede, Edmf, Emd, Ereg; exact Hwf.
    - exact Hrev.
  Qed.

  Local Abbreviation ACCREL :=
    (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine).
  Local Abbreviation SLW := (specLoadWb config pre post revBase revPfB revPfA initLine).
  Local Abbreviation RWB := (revWb config pre post revBase revPfB revPfA initLine).
  Local Abbreviation OUT s1 :=
    (evalLetExpr (dispatchLoadResponse config (ldPending (dmLoadRpV (iDmStA s1))) (optData (iRpReadyA s1)))).

  Lemma specLoadWb_rev :
    forall m pl v, outIsRev (evalLetExpr (dispatchLoadResponse config pl v)) = true ->
      SLW m pl v = RWB m (outRevV (evalLetExpr (dispatchLoadResponse config pl v))).
  Proof. intros m pl v H; unfold specLoadWb; cbv zeta; unfold outIsRev in H; rewrite H; reflexivity. Qed.

  Lemma specLoadWb_wb :
    forall m pl v, outIsRev (evalLetExpr (dispatchLoadResponse config pl v)) = false ->
      SLW m pl v = outWb (evalLetExpr (dispatchLoadResponse config pl v)).
  Proof. intros m pl v H; unfold specLoadWb; cbv zeta; unfold outIsRev in H; rewrite H; reflexivity. Qed.

  Lemma outRev_facts :
    forall pl v, outIsRev (evalLetExpr (dispatchLoadResponse config pl v)) = true ->
      (outRevV (evalLetExpr (dispatchLoadResponse config pl v))).(Snd).(Fst).(Fst) = pl.(Fst) /\
      baseRevokable config (rcBase (outRevV (evalLetExpr (dispatchLoadResponse config pl v)))) = true.
  Proof. intros pl v; unfold outIsRev, outRevV; exact (proj1 (loadOutcome_facts config pl v)). Qed.

  Lemma outWb_dst :
    forall pl v, outIsRev (evalLetExpr (dispatchLoadResponse config pl v)) = false ->
      fst (outWb (evalLetExpr (dispatchLoadResponse config pl v))) = pl.(Fst).
  Proof. intros pl v; unfold outIsRev, outWb; exact (proj2 (loadOutcome_facts config pl v)). Qed.

  (* A load response waits in `state` for dataMem: the access in flight is that load's *)
  Lemma accLoad_ready :
    forall (g : GhostT) (s1 : IState) (s2 : SState),
      ACCREL g s1 s2 -> dmLoadRp (iDmStA s1) = true -> optValid (iRpReadyA s1) = true ->
      exists pkt0,
        g_acc pcAddrInit g = AccLoad (dmLoadRpV (iDmStA s1)) pkt0 (RdReady (optData (iRpReadyA s1))) /\
        optValid (iReadRpA s1) = false /\ PortsQuietA s1 /\ g_revOff pcAddrInit g = RevEq /\
        revNotReadingA s1 /\ optValid (sSecondA s2) = false /\
        g_cnwb pcAddrInit g = Some (SLW (sMemA s2) (ldPending (dmLoadRpV (iDmStA s1))) (optData (iRpReadyA s1))).
  Proof.
    intros g s1 s2 Ha Hlrp Hr1.
    destruct (dmLoadRp_excl3 _ Hlrp) as [Elrq [Errq Errp]].
    destruct (msReadRpReady_excl2 _ (ARR g s1 s2 Ha Hr1)) as [Emrq Emsent].
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt st] eqn:Eacc.
    - destruct Ha as [_ [_ [_ [_ [_ [[E _] _]]]]]]; rewrite Hlrp in E; discriminate E.
    - destruct Ha as [_ [E _]]; rewrite Elrq in E; discriminate E.
    - destruct Ha as [Hst [_ [_ [Eld [HrnR [Hoff Hmt]]]]]].
      destruct st as [b | b | b | b rp | res]; unfold RdStageRel in Hst; cbv zeta in Hst.
      + destruct Hst as [E _]; rewrite Emrq in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [_ [Eres0 [Hrp HPQ]]]; cbv beta iota zeta in Hmt; destruct Hmt as [Hsec Hcn].
        assert (Eres : optData (iRpReadyA s1) = res) by (rewrite Eres0; reflexivity); clear Eres0.
        exists pkt0; subst ld res.
        split; [reflexivity |]; split; [exact Hrp |]; split; [exact HPQ |]; split; [exact Hoff |].
        split; [exact HrnR |]; split; [exact Hsec | exact Hcn].
    - destruct Ha as [_ [_ [E _]]]; rewrite Errp in E; discriminate E.
    - destruct Ha as [_ [_ [_ [[E _] _]]]]; rewrite Hlrp in E; discriminate E.
    - destruct Ha as [_ [_ [_ [[E _] _]]]]; rewrite Hlrp in E; discriminate E.
    - destruct Ha as [_ [_ [[E _] _]]]; rewrite Hlrp in E; discriminate E.
  Qed.

  Definition gNone (g : GhostT) : GhostT :=
    mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g) RevEq
            (g_d2aFo pcAddrInit g) AccNone.

  Definition gIssue (g : GhostT) (rc : type RevCmd) : GhostT :=
    mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g)
            (g_d2aFo pcAddrInit g) (AccDmRev rc (RdPend false)).

  Local Abbreviation RRQ :=
    (RevRqStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation ISS :=
    (IssueStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* A load response that needs a rev-bit lookup: dataMem takes it, the access in flight ends *)
  Lemma RefRelG_revRq :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState) pkt0,
      RELG g s1 s2 ->
      g_acc pcAddrInit g = AccLoad (dmLoadRpV (iDmStA s1)) pkt0 (RdReady (optData (iRpReadyA s1))) ->
      dmLoadRp (iDmStA s1) = true ->
      outIsRev (OUT s1) = true -> RRQ s1 s1' (outRevV (OUT s1)) ->
      RELG (gNone g) s1' s2.
  Proof.
    intros g s1 s1' s2 pkt0 Hg Eacc Hlrp Hrev [Hfr' [Erq [Eidle [Erdy' [Hrq' Erc']]]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha.
    destruct Ha as [[_ [_ [Hrp HPQ]]] [_ [_ [_ [HrnR [Hoff [Hsec Hcn]]]]]]].
    destruct (outRev_facts _ _ Hrev) as [Edst Hbr].
    destruct (dmRevRq_excl3 _ Hrq') as [Elrq' [Elrp' Errp']].
    pose proof Hfr' as Hfr0; destruct Hfr0 as [_ _ Ereg _ _ _ _ Emd Edmf].
    assert (Erev : iRevA s1' = iRevA s1) by (unfold iRev; rewrite Ereg; reflexivity).
    apply (RefRelG_dmFrame g (gNone g) s1 s1' s2 Hg); try reflexivity.
    - cbn [gNone g_revOff]; symmetry; exact Hoff.
    - rewrite Eacc; reflexivity.
    - exact Hfr'.
    - unfold olderWriters, dmInFlightDst, iDmBuf; cbv zeta.
      rewrite Elrp', Hrq', Erc', Hlrp, Edmf, Emd, Edst; reflexivity.
    - unfold AccessRel; cbn [gNone g_acc g_revOff].
      split; [exact Eidle |]; split; [destruct Hfr' as [_ _ _ E _ _ _ _ _]; rewrite E; exact Hrp |].
      split; [exact Erdy' |].
      split; [unfold PortsQuiet in *; rewrite Ereg; exact HPQ |]; split; [reflexivity |].
      split; [unfold dmNotAccessing; rewrite Elrp', Errp'; split; reflexivity |].
      split; [unfold revNotReading, iRevPhase in *; rewrite Erev; exact HrnR | exact Hsec].
    - unfold CnwbRel; cbn [gNone g_cnwb g_chain g_acc].
      split; [intros E; rewrite Elrq' in E; discriminate E |].
      split; [intros _; rewrite Erc', Hcn, specLoadWb_rev by exact Hrev; reflexivity |].
      split; [intros _; rewrite Erc'; exact Hbr |].
      intros E; rewrite Elrp' in E; discriminate E.
    - unfold RevokerRel, RevAccRel in *; cbn [gNone g_acc].
      destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite Erev; exact (conj K1 (conj K2 (conj K3 (conj K4 I)))).
  Qed.

  (* dataMem hands its rev-bit read to the memory *)
  Lemma RefRelG_issue :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> g_acc pcAddrInit g = AccNone -> dmRevRq (iDmStA s1) = true ->
      ISS s1 s1' (dmRevRqV (iDmStA s1)) ->
      RELG (gIssue g (dmRevRqV (iDmStA s1))) s1' s2.
  Proof.
    intros g s1 s1' s2 Hg Eacc Hrq [Hfr' [Erdy [Hmrq [Emv [Hreq [Hrp' Erc']]]]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha Hc _ _ _ _ _ Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha.
    destruct Ha as [Hidle [Hrp [Hrdy [HPQ [Hoff [Hdna [HrnR Hsec]]]]]]].
    destruct Hc as [_ [C2 [C3 _]]].
    destruct (dmRevRq_excl3 _ Hrq) as [Elrq [Elrp Errp]].
    destruct (dmRevRp_excl3 _ Hrp') as [Elrq' [Elrp' Errq']].
    pose proof Hfr' as Hfr0; destruct Hfr0 as [_ _ Ereg Erp _ _ _ Emd Edmf].
    assert (Erev : iRevA s1' = iRevA s1) by (unfold iRev; rewrite Ereg; reflexivity).
    apply (RefRelG_dmFrame g (gIssue g (dmRevRqV (iDmStA s1))) s1 s1' s2 Hg); try reflexivity.
    - rewrite Eacc; reflexivity.
    - exact Hfr'.
    - unfold olderWriters, dmInFlightDst, iDmBuf; cbv zeta.
      rewrite Elrp', Errq', Hrp', Erc', Elrp, Hrq, Edmf, Emd; reflexivity.
    - unfold AccessRel; cbn [gIssue g_acc g_revOff g_cnwb].
      split; [unfold RdStageRel; split; [exact Hmrq | split; [exact Emv | split;
                [rewrite Erp; exact Hrp | split; [rewrite Erdy; exact Hrdy |
                 unfold PortsQuiet in *; rewrite Ereg; exact HPQ]]]] |].
      split; [exact Hreq |]; split; [exact Hrp' |]; split; [exact Erc' |].
      split; [unfold revNotReading, iRevPhase in *; rewrite Erev; exact HrnR |].
      split; [exact Hoff |]; split; [exact Hsec |]; split; [exact (C2 Hrq) |].
      split; [reflexivity |]; split; [exact (C3 Hrq) | exact I].
    - unfold CnwbRel; cbn [gIssue g_cnwb g_chain g_acc].
      split; [intros E; rewrite Elrq' in E; discriminate E |].
      split; [intros E; rewrite Errq' in E; discriminate E |].
      split; [intros E; rewrite Errq' in E; discriminate E |].
      intros E; rewrite Elrp' in E; discriminate E.
    - unfold RevokerRel, RevAccRel in *; cbn [gIssue g_acc].
      destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite Erev; exact (conj K1 (conj K2 (conj K3 (conj K4 I)))).
  Qed.

  (* dataMem's rev-bit read can be handed to the memory only when no access is in flight *)
  Lemma accNone_of_issue :
    forall (g : GhostT) (s1 : IState) (s2 : SState),
      ACCREL g s1 s2 -> dmRevRq (iDmStA s1) = true -> msIdle (iMemStA s1) = true ->
      noPortWriteB implRegions (iRegionsA s1) = true ->
      g_acc pcAddrInit g = AccNone.
  Proof.
    intros g s1 s2 Ha Hrq Hid Hnp.
    destruct (dmRevRq_excl3 _ Hrq) as [Elrq [Elrp Errp]].
    destruct (msIdle_excl2 _ Hid) as [Emrq [Emsent [Emrdy Emwr]]].
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt st] eqn:Eacc;
      [reflexivity | exfalso ..].
    - destruct Ha as [_ [E _]]; rewrite Elrq in E; discriminate E.
    - destruct Ha as [_ [_ [E _]]]; rewrite Elrp in E; discriminate E.
    - destruct Ha as [_ [_ [E _]]]; rewrite Errp in E; discriminate E.
    - destruct Ha as [Hst _]; destruct st as [b | b | b | b rp | res]; unfold RdStageRel in Hst; cbv zeta in Hst.
      + destruct Hst as [E _]; rewrite Emrq in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [E _]; rewrite Emrdy in E; discriminate E.
    - destruct Ha as [Hst _]; destruct st as [b | b | b | b rp | res]; unfold RdStageRel in Hst; cbv zeta in Hst.
      + destruct Hst as [E _]; rewrite Emrq in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [[E _] _]; rewrite Emsent in E; discriminate E.
      + destruct Hst as [E _]; rewrite Emrdy in E; discriminate E.
    - destruct Ha as [Hst _]; destruct st as [b | b]; unfold WrStageRel in Hst.
      + destruct Hst as [_ [_ [E _]]]; rewrite Emwr in E; discriminate E.
      + destruct Hst as [_ [_ [_ [Hk HPW]]]].
        unfold PortsWriteStaged in HPW.
        rewrite (noPortWriteB_false _ (buildW b addr pkt capSz) implRegions (iRegionsA s1) Hk) in Hnp; [discriminate Hnp |].
        revert HPW; apply AllPorts_impl; intros r y [_ Hif] HL; rewrite HL in Hif; exact Hif.
  Qed.

  Local Abbreviation LRIR :=
    (@loadRpAndIssueRevRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation NPCORE :=
    (Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).

  (* The second half of the stage (`issueRevRq`) from a related state *)
  Lemma issue_half :
    forall (g : GhostT) (sm s1' : IState) (s2 : SState),
      RELG g sm s2 ->
      (writeSubTreeState NPCORE sm (readSubTreeState NPCORE s1') = sm \/
       (dmRevRq (iDmStA sm) = true /\ msIdle (iMemStA sm) = true /\ noPortWriteB implRegions (iRegionsA sm) = true /\
        ISS sm (writeSubTreeState NPCORE sm (readSubTreeState NPCORE s1')) (dmRevRqV (iDmStA sm)))) ->
      s1' = writeSubTreeState NPCORE sm (readSubTreeState NPCORE s1') ->
      REL s1' s2.
  Proof.
    intros g sm s1' s2 Hg [Eq | [Hrq [Hid [Hnp His]]]] E1.
    - exists g; rewrite E1, Eq; exact Hg.
    - pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
      exists (gIssue g (dmRevRqV (iDmStA sm))); rewrite E1.
      exact (RefRelG_issue g sm _ s2 Hg (accNone_of_issue g sm s2 Ha Hrq Hid Hnp) Hrq His).
  Qed.

  (* Milestone 5: dataMem's load response (write-back or rev-bit lookup) and its rev-bit read
   * request (the spec stutters) *)
  Theorem stepOK_loadRpAndIssueRevRqStage :
    StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
           clintS clint plicS plic initLine fwcs LRIR.
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    exists s2; split; [apply NilAction; reflexivity |].
    unfold loadRpAndIssueRevRqStage in Hsem.
    apply SemAction_liftAction_iff in Hsem as [c' [Hc ->]].
    unfold loadRpAndIssueRevRq in Hc; rewrite SemAction_iff_evalActionPropGen in Hc.
    cbn [evalActionPropGen] in Hc.
    apply evalActionPropGen_to_SemAction in Hc as [c1 [r1 [Ha Hb]]].
    apply evalActionPropGen_to_SemAction in Hb as [c2 [r2 [Hb [E2 _]]]]; subst c2.
    pose proof (loadRpWb_char pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  _ s1 c1 r1 Ha) as Hld.
    assert (Erd : readSubTreeState NPCORE (writeSubTreeState NPCORE s1 c1) = c1)
      by apply readSubTreeState_writeSubTreeState_same.
    assert (Ewr : writeSubTreeState NPCORE s1 c' = writeSubTreeState NPCORE (writeSubTreeState NPCORE s1 c1) c')
      by (symmetry; apply writeSubTreeState_writeSubTreeState_same).
    rewrite <- Erd in Hb.
    remember (writeSubTreeState NPCORE s1 c1) as sm eqn:Esm.
    pose proof (issueRevRq_char pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  _ sm c' r2 Hb) as Hiss.
    assert (Efin : writeSubTreeState NPCORE s1 c' =
                   writeSubTreeState NPCORE sm (readSubTreeState NPCORE (writeSubTreeState NPCORE s1 c')))
      by (rewrite readSubTreeState_writeSubTreeState_same; exact Ewr).
    rewrite <- (readSubTreeState_writeSubTreeState_same NPCORE s1 c') in Hiss.
    clear Erd Ewr Hb Ha.
    destruct Hld as [Emid | [Hlrp [Hr1 [Hr2 [[Hrev Hrrq] | [Hwbo Hdws]]]]]].
    - (* nothing happened in the first half *)
      rewrite Emid in Hiss, Efin.
      exact (issue_half g s1 _ s2 Hg Hiss Efin).
    - (* a rev-bit lookup: dataMem takes it *)
      pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha0 _ _ _ _ _ _ _].
      destruct (accLoad_ready g s1 s2 Ha0 Hlrp Hr1) as [pkt0 [Eacc _]].
      exact (issue_half (gNone g) sm _ s2 (RefRelG_revRq g s1 sm s2 pkt0 Hg Eacc Hlrp Hrev Hrrq) Hiss Efin).
    - (* a write-back *)
      pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha0 _ _ _ _ _ _ _].
      destruct (accLoad_ready g s1 s2 Ha0 Hlrp Hr1) as [pkt0 [Eacc [Hrp [HPQ [Hoff [HrnR [Hsec Hcn]]]]]]].
      assert (Hgm : RELG (gWb g (fst (outWb (OUT s1))) (snd (outWb (OUT s1)))) sm s2).
      { apply (RefRelG_dmWb g s1 sm s2); [exact Hg | | exact Hrp | exact HPQ | exact Hoff | exact HrnR |
                                          exact Hsec | rewrite Eacc; reflexivity | exact Hdws].
        rewrite Hcn, specLoadWb_wb by exact Hwbo; rewrite <- surjective_pairing; reflexivity. }
      apply (issue_half _ sm _ s2 Hgm); [| exact Efin].
      destruct Hiss as [Eq | [Hrq _]]; [left; exact Eq | exfalso].
      destruct (dmLoadRq_excl3 _ (dw_dmst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hdws)) as [_ [E _]].
      rewrite E in Hrq; discriminate Hrq.
  Qed.

End DmStep.
