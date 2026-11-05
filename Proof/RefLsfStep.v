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
From Cheriot.Proof Require Import RefExecAux RefExecLive RefLoadCommit RefDmImpl RefDmStep RefLsfImpl RefRevokerStep.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 5: `loadRqOrStoreOrFenceStage` (RELATION SIDE)
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState ElemState t).

Section LsfStep.
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
  Local Abbreviation iFetchA := (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA := (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecA := (iExec pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA := (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation ACCREL :=
    (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine).
  Local Abbreviation CNWBREL :=
    (CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine).
  Local Abbreviation REVREL :=
    (RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine).
  Local Abbreviation MEMC :=
    (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clintS clint plicS plic fwcs).
  Local Abbreviation DMQ :=
    (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* With nothing in flight dataMem's head is the chain's head entry *)
  Lemma head_of_dm :
    forall (g : GhostT) (s1 : IState) (s2 : SState) q rest,
      EagerRel pcAddrInit pre post revBase revPfB revPfA g s2 -> optValid (sSecondA s2) = false ->
      DMQ g s1 -> accTakesHead (g_acc pcAddrInit g) = false ->
      iDmBufA s1 = q :: rest -> isPlainFence q = false -> HeadReq pcAddrInit g q.
  Proof.
    intros g s1 s2 q rest He Hsec Hd Ht Eb Hp.
    unfold DmQueueRel in Hd; rewrite Ht, Eb in Hd; cbn [filter] in Hd; rewrite Hp in Hd; cbn [negb] in Hd.
    unfold EagerRel in He; destruct He as [Hn | [e [G' [Hc [Hs | Hb]]]]].
    - rewrite Hn in Hd; discriminate Hd.
    - rewrite Hsec in Hs; discriminate Hs.
    - rewrite Hc in Hd; unfold entryBlocking in Hb.
      exists e, G'; split; [exact Hc |].
      destruct (entryReq e) as [q0 |] eqn:Er; [| discriminate Hb].
      cbn [chainReqs flat_map] in Hd; rewrite Er in Hd; cbn [app filter] in Hd.
      rewrite Hb in Hd; injection Hd as -> _; reflexivity.
  Qed.

  (* A step of this stage: only the memory, dataMem and the access in flight change (and, for a
   * store, the revoker's snoop flag) *)
  Lemma RefRelG_lsfFrame :
    forall (g g' : GhostT) (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 ->
      g_chain pcAddrInit g' = g_chain pcAddrInit g -> g_rf0 pcAddrInit g' = g_rf0 pcAddrInit g ->
      g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g -> g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g ->
      iRfA s1' = iRfA s1 -> iWbA s1' = iWbA s1 -> iFetchA s1' = iFetchA s1 -> iDecodeA s1' = iDecodeA s1 ->
      iExecA s1' = iExecA s1 -> iMdA s1' = iMdA s1 ->
      (forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1')) ->
      olderWritersA s1' = olderWritersA s1 ->
      MEMC g' s1' s2 -> ACCREL g' s1' s2 -> CNWBREL g' s1' s2 -> DMQ g' s1' -> REVREL g' s1' s2 ->
      RELG g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 Hg Ech Erf0 Ecn Ed2f Erf Ewb Efe Ede Eex Emd HP Hwfd Eow Hm' Ha' Hc' Hd' Hr'.
    destruct Hg as [Hrf Hm Hl Hrpl He Ha Hc Hd Hf Hs Hfr Hwf Hrk].
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite Ede; reflexivity).
    assert (Eflush : iFlushA s1' = iFlushA s1).
    { unfold iFlush, flushMulDiv, flushMulDivOn.
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1') with (iRfA s1').
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1) with (iRfA s1).
      rewrite Erf, Emd; reflexivity. }
    constructor.
    - unfold RfRel in *; rewrite Ech, Erf0, Ecn, Eflush; exact Hrf.
    - exact Hm'.
    - unfold LatchRel in *; rewrite Ech; exact Hl.
    - unfold ReplayRel in *; rewrite Ech, Erf0; exact Hrpl.
    - unfold EagerRel in *; rewrite Ech; exact He.
    - exact Ha'.
    - exact Hc'.
    - exact Hd'.
    - unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *; rewrite Ech.
      rewrite !HP, Efe, Ed2a, Eep, Efip; exact Hf.
    - unfold ScoreRel, daLive in *; rewrite Ed2f, Eow, Ed2a, Eep, Ewb, Eflush; exact Hs.
    - unfold FrontRel, LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf in *; rewrite Ed2f.
      rewrite Epcc, !HP, Efe, Ed2a, Eep; exact Hfr.
    - unfold WfRel, iCurParcel, iFetchBuf, iInstBuf in *.
      rewrite Epcc, Efe, Ed2a, Ede, Emd, !HP.
      destruct Hwf as [W1 [W2 [W3 [_ [W5 W6]]]]].
      exact (conj W1 (conj W2 (conj W3 (conj Hwfd (conj W5 W6))))).
    - exact Hr'.
  Qed.


  (* the dequeued request's list facts *)
  Lemma dm_deq_buf :
    forall (s1 s1' : IState) q rest,
      fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1)) ->
      dataMem_fifo dataMemCapacity (iDmA s1') = fifoDeqState (dataMem_fifo dataMemCapacity (iDmA s1)) ->
      iDmBufA s1 = q :: rest ->
      iDmBufA s1' = rest /\ fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1')).
  Proof.
    intros s1 s1' q rest Hw Ed Eb; unfold iDmBuf in *; rewrite Ed.
    split; [rewrite (fifo_to_list_deq _ _ _ Hw), Eb; reflexivity | apply fifo_wf_deq; exact Hw].
  Qed.

  Lemma RefRelG_plain :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState) q rest,
      RELG g s1 s2 ->
      PlainAcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 s1' ->
      iDmBufA s1 = q :: rest -> isPlainFence q = true ->
      RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 q rest Hg Hpa Eb Hp.
    destruct Hpa as [[Erf Ewb Efe Ede Emd Edmf] Eex Edmst Emem].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ Ha Hc Hd _ _ _ [_ [_ [_ [Hwd _]]]] Hr].
    destruct (dm_deq_buf s1 s1' q rest Hwd Edmf Eb) as [Eb' Hwd'].
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Hpl : opIsLoad (mrOp q) = false).
    { unfold isPlainFence in Hp; apply andb_prop in Hp as [Hp1 _]; apply negb_true_iff in Hp1.
      unfold opIsLoad; rewrite Hp1; reflexivity. }
    apply (RefRelG_lsfFrame g g s1 s1' s2 Hg eq_refl eq_refl eq_refl eq_refl Erf Ewb Efe Ede Eex Emd).
    - intros P; rewrite Ereg; reflexivity.
    - exact Hwd'.
    - unfold olderWriters, dmInFlightDst; rewrite Edmst, Emd, Eb', Eb.
      cbn [filter]; rewrite Hpl; reflexivity.
    - unfold MemRelC in *; rewrite Ereg; exact Hm.
    - eapply AccessRel_frame; [| | | | | | reflexivity | | exact Ha].
      + intros P; rewrite Ereg; reflexivity.
      + unfold iRev; rewrite Ereg; reflexivity.
      + unfold iMemSt; rewrite Emem; reflexivity.
      + unfold iRdBufs; rewrite Emem; reflexivity.
      + unfold iRequester; rewrite Emem; reflexivity.
      + exact Edmst.
      + intros L; reflexivity.
    - unfold CnwbRel in *; rewrite Edmst; exact Hc.
    - unfold DmQueueRel in *; rewrite Eb'; rewrite Eb in Hd; cbn [filter] in Hd; rewrite Hp in Hd; exact Hd.
    - eapply RevokerRel_frame; [reflexivity | reflexivity | | | exact Hr].
      + unfold iRev; rewrite Ereg; reflexivity.
      + intros L; reflexivity.
  Qed.

  Definition gLoad (g : GhostT) (q : type MemFenceReq) : GhostT :=
    mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g)
            (g_d2aFo pcAddrInit g) (AccLoad (loadCmdOf q) (getDefault CapPacket) (RdPend false)).

  Lemma RefRelG_load :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState) q rest,
      RELG g s1 s2 ->
      LoadAcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 s1' q ->
      iDmBufA s1 = q :: rest -> dmLoadRq (iDmStA s1) = true ->
      opIsMem (mrOp q) = true -> opIsStore (mrOp q) = false ->
      RELG (gLoad g q) s1' s2.
  Proof.
    intros g s1 s1' s2 q rest Hg Hla Eb Hlrq Hm Hs.
    destruct Hla as [[Erf Ewb Efe Ede Emd Edmf] Eex Edm Edmv Hi Hnp Ereg Hms Hmsv Hrq Erp Erdy].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hmem _ _ He Ha Hc Hd _ _ _ [_ [_ [_ [Hwd _]]]] Hr].
    assert (Hacc : g_acc pcAddrInit g = AccNone) by (eapply AccessRel_rdy_none; eassumption).
    pose proof Ha as Ha0; unfold AccessRel in Ha0; rewrite Hacc in Ha0.
    destruct Ha0 as [Hidle [Hrp0 [Hrdy0 [HPQ [Hoff [Hdna [Hrnr Hsec]]]]]]].
    assert (Hcn : g_cnwb pcAddrInit g = None) by (exact (proj1 Hc Hlrq)).
    assert (Hpl : isPlainFence q = false) by (unfold isPlainFence; rewrite Hm; reflexivity).
    assert (HH : HeadReq pcAddrInit g q)
      by (apply (head_of_dm g s1 s2 q rest He Hsec Hd); [rewrite Hacc; reflexivity | exact Eb | exact Hpl]).
    destruct (dm_deq_buf s1 s1' q rest Hwd Edmf Eb) as [Eb' Hwd'].
    pose proof (opIsLoad_of _ Hm Hs) as Hld.
    destruct (dmLoadRq_excl3 _ Hlrq) as [N1 [N2 N3]].
    destruct (dmLoadRp_excl3 _ Edm) as [M1 [M2 M3]].
    apply (RefRelG_lsfFrame g (gLoad g q) s1 s1' s2 Hg eq_refl eq_refl eq_refl eq_refl Erf Ewb Efe Ede Eex Emd).
    - intros P; rewrite Ereg; reflexivity.
    - exact Hwd'.
    - pose proof (dmNotCheck _ (orb_true_intro _ _ (or_introl Hlrq))) as N4.
      unfold olderWriters, dmInFlightDst; rewrite Emd, Eb', Eb, Edm, N1, N2, N3, N4, Edmv, (loadCmd_dst q Hm Hs).
      cbn [filter app map]; rewrite Hld; reflexivity.
    - unfold MemRelC in *; cbn [gLoad g_revOff]; rewrite Ereg; exact Hmem.
    - unfold AccessRel, RdStageRel; cbn [gLoad g_acc g_revOff g_cnwb g_chain]; cbv zeta.
      split; [split; [exact Hms | split; [exact Hmsv | split; [rewrite Erp; exact Hrp0 |
               split; [rewrite Erdy; exact Hrdy0 | unfold PortsQuiet in *; rewrite Ereg; exact HPQ]]]] |].
      split; [exact Hrq | split; [exact Edm | split; [exact Edmv |]]].
      split; [unfold revNotReading, iRevPhase, iRev in *; rewrite Ereg; exact Hrnr |].
      split; [exact Hoff |].
      split; [exact Hsec | split; [reflexivity | split; [exact Hcn |]]].
      exists q; split; [exact HH | split; [exact Hld | reflexivity]].
    - unfold CnwbRel; cbn [gLoad g_cnwb g_acc g_chain accTakesHead].
      split; [intros E; rewrite M1 in E; discriminate E |].
      split; [intros E; rewrite M2 in E; discriminate E |].
      split; [intros E; rewrite M2 in E; discriminate E |].
      split; [intros _ _ E; discriminate E |]. cnwb_fin.
    - unfold DmQueueRel in *; cbn [gLoad g_acc g_chain accTakesHead]; rewrite Eb'.
      rewrite Hacc, Eb in Hd; cbn [accTakesHead filter] in Hd; rewrite Hpl in Hd; cbn [negb] in Hd.
      rewrite <- Hd; reflexivity.
    - unfold RevokerRel, RevAccRel in *; cbn [gLoad g_acc].
      destruct Hr as [R1 [R2 [R3 [R4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr, iRev in *; rewrite Ereg.
      exact (conj R1 (conj R2 (conj R3 (conj R4 I)))).
  Qed.

  Local Abbreviation stA q := (stAddrOf (storeCmdOf q)).
  Local Abbreviation stZ q := (stSizeOf (storeCmdOf q)).
  Local Abbreviation stP q := (disassembleW (stAddrOf (storeCmdOf q)) (stValOf (storeCmdOf q)) (stSizeOf (storeCmdOf q))).

  Definition gStore (g : GhostT) (q : type MemFenceReq) : GhostT :=
    mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g)
            (g_d2aFo pcAddrInit g) (AccStore (stA q) (stZ q) (stP q) (WrPend false)).

  Lemma RefRelG_store :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState) q rest,
      RELG g s1 s2 ->
      StoreAcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 s1' q ->
      iDmBufA s1 = q :: rest -> dmLoadRq (iDmStA s1) = true ->
      opIsMem (mrOp q) = true -> opIsStore (mrOp q) = true ->
      RELG (gStore g q) s1' s2.
  Proof.
    intros g s1 s1' s2 q rest Hg Hsa Eb Hlrq Hm Hs.
    destruct Hsa as [[Erf Ewb Efe Ede Emd Edmf] Eex Edmst Hi Hnp Ereg Hms Hmsv Erq Erp Erdy].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hmem _ _ He Ha Hc Hd _ _ _ [_ [_ [_ [Hwd _]]]] Hr].
    assert (Hacc : g_acc pcAddrInit g = AccNone) by (eapply AccessRel_rdy_none; eassumption).
    pose proof Ha as Ha0; unfold AccessRel in Ha0; rewrite Hacc in Ha0.
    destruct Ha0 as [Hidle [Hrp0 [Hrdy0 [HPQ [Hoff [Hdna [Hrnr Hsec]]]]]]].
    destruct Hc as [C1 [C2 [C3 [C4 C5]]]].
    assert (Hcn : g_cnwb pcAddrInit g = None) by (exact (C1 Hlrq)).
    assert (Hpl : isPlainFence q = false) by (unfold isPlainFence; rewrite Hm; reflexivity).
    assert (HH : HeadReq pcAddrInit g q)
      by (apply (head_of_dm g s1 s2 q rest He Hsec Hd); [rewrite Hacc; reflexivity | exact Eb | exact Hpl]).
    destruct (dm_deq_buf s1 s1' q rest Hwd Edmf Eb) as [Eb' Hwd'].
    pose proof (opIsLoad_store _ Hm Hs) as Hnl.
    destruct (dmLoadRq_excl3 _ Hlrq) as [N1 [N2 N3]].
    set (x' := snoopRev (stA q) (stZ q) (revOfR pre post revBase revPfB revPfA (iRegionsA s1))) in Ereg.
    assert (Erev : iRevA s1' = x') by (unfold iRev; rewrite Ereg; apply revOfR_setRevR).
    assert (Erev0 : iRevA s1 = revOfR pre post revBase revPfB revPfA (iRegionsA s1)) by reflexivity.
    assert (HP : forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P; rewrite Ereg; unfold setRevR; apply AllPorts_upd; exact I).
    apply (RefRelG_lsfFrame g (gStore g q) s1 s1' s2 Hg eq_refl eq_refl eq_refl eq_refl Erf Ewb Efe Ede Eex Emd HP
             Hwd').
    - unfold olderWriters, dmInFlightDst; rewrite Emd, Eb', Eb, Edmst.
      cbn [filter]; rewrite Hnl; reflexivity.
    - eapply MemRelC_revImpl with (g := g) (s1 := s1) (mr := iRegionsA s1) (x' := x');
        [reflexivity | exact Ereg | | exact Hmem].
      destruct Hmem as [[_ [_ [_ Hrv]]] _]; exact Hrv.
    - unfold AccessRel, WrStageRel; cbn [gStore g_acc g_revOff g_chain].
      split; [split; [rewrite Erp; exact Hrp0 | split; [rewrite Erdy; exact Hrdy0 | split; [exact Hms | split; [exact Hmsv |
               unfold PortsQuiet in *; rewrite HP; exact HPQ]]]] |].
      split; [rewrite Edmst; exact Hlrq |].
      split; [unfold revNotReading, iRevPhase in *; rewrite Erev; rewrite Erev0 in Hrnr; exact Hrnr |].
      split; [exact Hoff |].
      split; [unfold iScanMsb, iRevSnoopHit; rewrite Erev; unfold x', snoopRev; cbn [Fst Snd];
              intros Hh; unfold revScanAddr, projImplRevokerArchState in Hh; cbn [Fst Snd] in Hh; rewrite Hh; reflexivity |].
      split; [exact Hsec |].
      exists q; split; [exact HH | split; [exact Hs | split; [reflexivity | split; reflexivity]]].
    - unfold CnwbRel; cbn [gStore g_cnwb g_acc g_chain accTakesHead]; rewrite Edmst.
      split; [intros _; exact Hcn |].
      split; [intros E; rewrite N2 in E; discriminate E |].
      split; [intros E; rewrite N2 in E; discriminate E |].
      split; [intros E; rewrite N1 in E; discriminate E |]. cnwb_fin.
    - unfold DmQueueRel in *; cbn [gStore g_acc g_chain accTakesHead]; rewrite Eb'.
      rewrite Hacc, Eb in Hd; cbn [accTakesHead filter] in Hd; rewrite Hpl in Hd; cbn [negb] in Hd.
      rewrite <- Hd; reflexivity.
    - unfold RevokerRel, RevAccRel in *; cbn [gStore g_acc].
      destruct Hr as [R1 [R2 [R3 [R4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite Erev; rewrite Erev0 in R1, R2, R3, R4; unfold x', snoopRev; cbn [Fst Snd].
      split; [exact R1 | split; [exact R2 | split; [| split; [| exact I]]]].
      + intros Hck Hsn; apply orb_false_elim in Hsn; exact (R3 Hck (proj2 Hsn)).
      + intros Hwc Hsn; apply orb_false_elim in Hsn; exact (R4 Hwc (proj2 Hsn)).
  Qed.

End LsfStep.
