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
From Cheriot.Proof Require Import RefSpecRead RefMemStep RefExecAux RefExecFrame RefDecodeStep RefPcEven RefFetchRqImpl
  RefFetchRqStep RefFetchAsmImpl.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 6: `fetchAssembleStage` (the spec stutters)
 * ===========================================================================
 * Branches (RefFetchAsmImpl.v): no `canProceed`, no head, no response or a full instBuf change
 * nothing the relation reads; a stale head is dropped with its response; a live head assembles an
 * instruction (or saves a straddle). *)

Local Abbreviation TS t := (TreeState ElemState t).


(* A valid response read for line `A` comes from the `readRp` of the ExternalMem region holding it *)
Lemma AllPorts_true :
  forall l (mi : TS (implRegionsTree l)), AllPorts (fun _ _ => True) l mi.
Proof.
  intros l; induction l as [| r rs IH]; intros mi; [exact I |].
  cbn [AllPorts]; split; [| apply IH].
  generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree; destruct (regionKind r); intros; exact I.
Qed.

Lemma fetchRpAt_valid_ports :
  forall l (mi : TS (implRegionsTree l)) A, lineUnique l A -> (fetchRpAt l mi A).(Snd).(Fst) = true ->
    AllPorts (fun r y => isRegionAddrB r A = true -> (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst)).(Snd).(Fst) = true) l mi.
Proof.
  intros l; induction l as [| r rs IH]; intros mi A Hu Hv; [exact I |].
  cbn [lineUnique] in Hu; cbn [fetchRpAt] in Hv; cbn [AllPorts].
  destruct (isRegionAddrB r A) eqn:Em.
  - split.
    + revert Hv; generalize (mi.(Fst)); unfold RegionPort, regionFetchRp, implMemRegionTree.
      destruct (regionKind r); intros y Hv; [| exact I].
      intros _; destruct (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst)); [reflexivity | exact Hv].
    + refine (AllPorts_none_impl _ _ A _ rs _ Hu (AllPorts_true _ _)).
      intros r' y Hf _ C; rewrite Hf in C; discriminate C.
  - split; [| exact (IH _ _ Hu Hv)].
    generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree; destruct (regionKind r);
      intros y; [intros C; rewrite Em in C; discriminate C | exact I].
Qed.

Section FetchAsmStep.
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

  Local Abbreviation FASM := (FasmStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* Only fetch's `canProceed` changed *)
  Lemma asm_stutter_rel :
    forall g (s1 s1' : IState) (s2 : SState),
      FASM s1 s1' (iMemA s1) (ACC aF0 s1) -> RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] H.
    destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    destruct H as [_ _ Hl Hrp He _ _ _ Hf Hs Hfr Hw _].
    constructor; try assumption.
    - unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *;
        rewrite Ereg, Efe, Ed2a, Eep, Efip; exact Hf.
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - unfold FrontRel, LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iPcc, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf in *;
        rewrite Erf, Ereg, Efe, Ed2a, Eep; exact Hfr.
    - unfold WfRel, iCurParcel, iFetchBuf, iInstBuf, iPcc in *;
        rewrite ?Erf, ?Ed2a, ?ED, ?Efe, ?Edm, ?Emd, ?Ereg; exact Hw.
  Qed.

  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation FRREL := (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 initLine fwcs).
  Local Abbreviation aEA := (ACC aE).

  Lemma fb_head :
    forall (s1 : IState),
      fifo_wf (FBF s1) -> (ACC aHead s1).(Snd).(Fst) = true ->
      exists rest, iFetchBufA s1 = aEA s1 :: rest /\ fifo_to_list (fifoDeqState (FBF s1)) = rest.
  Proof.
    intros s1 Hwf Hv.
    unfold aHead in Hv; rewrite (fifoFirstVal_valid _ _ _ Hwf) in Hv.
    unfold iFetchBuf; destruct (fifo_to_list (FBF s1)) as [| a rest] eqn:El; [discriminate Hv |].
    exists rest; split.
    - f_equal; unfold aE, aHead; symmetry; exact (fifoFirstVal_data _ _ _ a rest El).
    - rewrite (fifo_to_list_deq _ _ _ Hwf), El; reflexivity.
  Qed.

  Lemma MemRelC_fetchDeq :
    forall g (s1 s1' : IState) (s2 : SState) mr' A,
      iRegionsA s1' = mr' -> FetchDeqAtL A implRegions (iRegionsA s1) mr' -> MEMC g s1 s2 -> MEMC g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' A Ei Hat Hm.
    unfold MemRelC, MemRel, DevInv in *; rewrite Ei.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_fetchDeqAt _ _ _ _ _ _ _ Hat) by exact I.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    eapply MemRelPre_fetchDeqAt; [exact Hat | exact Hpre].
  Qed.

  (* The components that read neither the frontend nor the wait bits, across a response dequeue *)
  Lemma core_fetchDeq :
    forall g (s1 s1' : IState) (s2 : SState) mr' A,
      iRfA s1' = iRfA s1 -> iMemA s1' = (mr' ,, (iMemA s1).(Snd)) -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      FetchDeqAtL A implRegions (iRegionsA s1) mr' ->
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
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' A Erf Emem Edm Emd Hat H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    assert (Ei : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
    assert (HP : forall P, (forall r y, P r (clearReadRp r y) = P r y) ->
                   AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P HP; rewrite Ei; exact (AllPorts_fetchDeqAt P HP _ _ _ _ Hat)).
    assert (HR : iRevA s1' = iRevA s1).
    { unfold iRev, implRevState; rewrite Ei.
      rewrite (regionStateAt_fetchDeqAt _ _ _ _ _ _ _ Hat) by exact I; reflexivity. }
    destruct H as [Hrf Hm _ _ _ Ha Hc Hd _ _ _ _ Hrk].
    split; [unfold RfRel in *; rewrite Efl; exact Hrf |].
    split; [exact (MemRelC_fetchDeq g s1 s1' s2 mr' A Ei Hat Hm) |].
    split.
    { eapply AccessRel_frame_ports with (s1 := s1) (s2 := s2); try reflexivity.
      - unfold PortsQuiet; apply HP; intros r y; reflexivity.
      - intros L; unfold PortsReadStaged; apply HP; intros r y; reflexivity.
      - intros L; unfold PortsReadOut; apply HP; intros r y; reflexivity.
      - intros L rq; unfold PortsWriteStaged; apply HP; intros r y; reflexivity.
      - exact HR.
      - unfold iMemSt; rewrite Emem; reflexivity.
      - unfold iReadRp; rewrite Emem; reflexivity.
      - unfold iRequester; rewrite Emem; reflexivity.
      - unfold iDmSt; rewrite Edm; reflexivity.
      - exact Ha. }
    split; [unfold CnwbRel in *; unfold iDmSt in *; rewrite Edm; exact Hc |].
    split; [unfold DmQueueRel, iDmBuf in *; rewrite Edm; exact Hd |].
    eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2); try reflexivity; [exact HR | exact Hrk].
  Qed.

  Local Abbreviation FRONTIER := (FrontierRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                    initLine fwcs).

  (* A stale head leaves fetchBuf and no parcel is assembled any more *)
  Lemma FrontierRel_drop :
    forall (s1 s1' : IState) (s2 : SState) h rest fp,
      iFetchBufA s1 = h :: rest -> iFetchBufA s1' = rest -> fbLiveA s1 h = false ->
      optValid (ACC iCurParcel s1') = false -> ACC iStraddle s1' = ACC iStraddle s1 ->
      ACC iFetchPc s1' = ACC iFetchPc s1 -> fbLiveA s1' = fbLiveA s1 -> iPccA s1' = iPccA s1 ->
      FRONTIER s1 s2 fp -> FRONTIER s1' s2 fp.
  Proof.
    intros s1 s1' s2 h rest fp Efb0 Efb Hst Ecp Estr Efpc Elv Epcc H.
    unfold FrontierRel in *; cbv zeta in *.
    rewrite Efb0 in H; rewrite Efb, Elv, Estr, Efpc, Epcc, Ecp.
    cbn [filter] in H; rewrite Hst in H.
    destruct H as [Hch [Hx [Hm Hal]]].
    split; [exact Hch | split; [exact Hx | split; [| exact Hal]]].
    destruct (optValid (ACC iStraddle s1)); [exact Hm |].
    destruct (filter (fbLiveA s1) rest) as [| f l]; [exact Hm |].
    rewrite andb_false_r; cbn [andb] in Hm; exact Hm.
  Qed.

  Lemma NoLive_drop :
    forall (s1 s1' : IState) h rest,
      iFetchBufA s1 = h :: rest -> iFetchBufA s1' = rest -> fbLiveA s1' = fbLiveA s1 ->
      iD2aA s1' = iD2aA s1 -> iInstBufA s1' = iInstBufA s1 -> iExecEpochA s1' = iExecEpochA s1 ->
      ACC NoLive s1 -> ACC NoLive s1'.
  Proof.
    intros s1 s1' h rest Efb0 Efb Elv Ed2a Eib Eep [N1 [N2 N3]].
    unfold NoLive, daLive, aiLive in *; rewrite Ed2a, Eib, Eep.
    split; [exact N1 | split; [exact N2 |]].
    rewrite Efb, Elv; rewrite Efb0 in N3; exact (Forall_inv_tail N3).
  Qed.

  (* The relation after dropping a stale head; the memory side is given by the caller *)
  Lemma asm_drop_rel :
    forall g (s1 s1' : IState) (s2 : SState) m,
      FASM s1 s1' m (ACC aFDrop s1) ->
      (ACC aHead s1).(Snd).(Fst) = true -> fbLiveA s1 (aEA s1) = false ->
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
      ACC NoFenceIWait s1' = ACC NoFenceIWait s1 ->
      (AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1) ->
       AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1')) ->
      (iFetchBufA s1' = tl (iFetchBufA s1) -> fbLiveA s1' = fbLiveA s1 -> FRREL s1' s2) ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 m [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] Hv Hst Crf Cm Ca Cc Cd Crk HNF HW Cfr H.
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
    assert (Ecp : optValid (ACC iCurParcel s1') = false) by (unfold iCurParcel; rewrite Efe; reflexivity).
    assert (Estr : ACC iStraddle s1' = ACC iStraddle s1) by (unfold iStraddle; rewrite Efe; reflexivity).
    assert (Efpc : ACC iFetchPc s1' = ACC iFetchPc s1) by (unfold iFetchPc; rewrite Efe; reflexivity).
    assert (Edl : daLiveA s1' = daLiveA s1) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA s1' = aiLiveA s1) by (unfold aiLive; rewrite Eep; reflexivity).
    assert (Elv : fbLiveA s1' = fbLiveA s1) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
    destruct H as [_ _ Hl Hrp He' _ _ _ Hfe Hs Hfr Hwf].
    destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (fb_head s1 W1a Hv) as [rest [Efb0 Erest]].
    assert (Efb : iFetchBufA s1' = rest).
    { unfold iFetchBuf; rewrite Efe.
      change (fifo_to_list (fifoDeqState (FBF s1)) = rest); exact Erest. }
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - unfold FenceRel in *; rewrite HNF, Efip, Estr.
      pose proof (NoLive_drop s1 s1' _ rest Efb0 Efb Elv Ed2a Eib Eep) as HNL.
      destruct Hfe as [Hf1 Hf2]; split.
      + intros Hp; destruct (Hf1 Hp) as [Hn Hr]; exact (conj (HNL Hn) Hr).
      + intros Hq; destruct (Hf2 Hq) as [Hp [Hn Hr]]; exact (conj Hp (conj (HNL Hn) Hr)).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel; rewrite Ed2a, Edl, Eib, Eal, Efb, Elv, Eep.
      rewrite Efb0 in F3, F5.
      refine (conj F1 (conj F2 (conj (StalePrefix_tail _ _ _ F3) (conj F4 (conj _ (conj _ _)))))).
      + intros Hx; exact (Forall_inv_tail (F5 Hx)).
      + assert (Elive : liveInstsA g s1' = liveInstsA g s1)
          by (unfold liveInsts; rewrite Ed2a, Eib, Edl, Eal; reflexivity).
        unfold LiveChain in *; rewrite Elive, Epcc.
        refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                  (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
        intros p Hp; exact (FrontierRel_drop s1 s1' s2 _ rest p Efb0 Efb Hst Ecp Estr Efpc Elv Epcc Hp).
      + apply Cfr; [rewrite Efb, Efb0; reflexivity | exact Elv].
    - unfold WfRel; rewrite Efb, Epcc, Ed2a, Eib.
      split; [split; [rewrite Efe; exact (fifo_wf_deq _ _ _ W1a) |] |].
      + split; [intros C; rewrite Ecp in C; discriminate C |].
        rewrite Efb0 in W1f.
        split; [exact W1c |]; split; [exact W1d |]; split; [exact W1e | exact (Forall_inv_tail W1f)].
      + split; [rewrite Efe; exact W2 |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact (HW W6)].
    - exact Crk.
  Qed.

  Lemma asm_stale_rel :
    forall g (s1 s1' : IState) (s2 : SState) mr',
      (ACC aPre s1 = true -> mr' = iRegionsA s1) ->
      (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) mr') ->
      FASM s1 s1' (mr' ,, (iMemA s1).(Snd)) (ACC aFDrop s1) ->
      (ACC aHead s1).(Snd).(Fst) = true -> (ACC aPkt s1).(Snd).(Fst) = true -> ACC aMatch s1 = false ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' Hmr1 Hmr2 Hst Hv Hpv Hm H.
    pose proof Hst as [Erf [_ [Emem [Efe [_ [Eex [Edm Emd]]]]]]].
    assert (Hsl : fbLiveA s1 (aEA s1) = false) by (rewrite <- (ACC aMatch_eq s1); exact Hm).
    pose proof H as [_ _ _ _ _ _ _ _ _ _ Hfr0 Hw0 _].
    destruct (fb_head s1 (proj1 (proj1 Hw0)) Hv) as [rest [Efb0 Erest]].
    assert (Efb : iFetchBufA s1' = rest).
    { unfold iFetchBuf; rewrite Efe.
      change (fifo_to_list (fifoDeqState (FBF s1)) = rest); exact Erest. }
    assert (Elv : fbLiveA s1' = fbLiveA s1) by (unfold fbLive, iExecEpoch, iPredEpoch; rewrite Eex, Efe; reflexivity).
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hfr0)))))) as F7.
    destruct (ACC aPre s1) eqn:Hpre.
    - assert (Emem' : iMemA s1' = iMemA s1) by (rewrite Emem, (Hmr1 eq_refl); reflexivity).
      assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem'; reflexivity).
      destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem' Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
      refine (asm_drop_rel g s1 s1' s2 _ Hst Hv Hsl Crf Cm Ca Cc Cd Crk _ _ _ H).
      + unfold NoFenceIWait; rewrite Ereg; reflexivity.
      + rewrite Ereg; exact (fun X => X).
      + intros _ _.
        assert (Hx : excAny (fbFetchExc (aEA s1)) = true) by (rewrite <- (ACC aPre_excAny s1); exact Hpre).
        unfold FetchRespRel in *; rewrite Ereg.
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                     fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r)
          by (unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx; reflexivity).
        rewrite EE, Elv; exact HC.
    - pose proof (Hmr2 eq_refl) as Hat.
      assert (Ei : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
      destruct (core_fetchDeq g s1 s1' s2 mr' _ Erf Emem Edm Emd Hat H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
      pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
      refine (asm_drop_rel g s1 s1' s2 _ Hst Hv Hsl Crf Cm Ca Cc Cd Crk _ _ _ H).
      + unfold NoFenceIWait; rewrite Ei; refine (AllPorts_fetchDeqAt _ _ _ _ _ _ Hat); intros r y; reflexivity.
      + rewrite Ei; intros W; refine (AllPorts_fetchDeqAt_impl _ _ (ACC aAligned s1) _ _ _ _ _ (Hu _) Hat W).
        * intros r y _ [[H1 [H2 [H3 [H4 H5]]]] H6].
          refine (conj (conj H1 (conj H2 (conj _ (conj H4 H5)))) H6).
          intros C; discriminate C.
        * intros r y _ X; exact X.
      + intros _ _.
        assert (Hrp : (fetchRpAt implRegions (iRegionsA s1) (ACC aAligned s1)).(Snd).(Fst) = true)
          by (unfold aPkt in Hpv; rewrite Hpre in Hpv; exact Hpv).
        pose proof (AllPorts_conj _ _ _ _ F7 (fetchRpAt_valid_ports _ _ _ (Hu _) Hrp)) as F7'.
        assert (Hx : excAny (fbFetchExc (aEA s1)) = false) by (rewrite <- (ACC aPre_excAny s1); exact Hpre).
        unfold FetchRespRel; rewrite Ei.
        refine (AllPorts_fetchDeqAt_impl _ _ _ _ _ _ _ _ (Hu _) Hat F7').
        * intros r y Hr [HC Hval]; cbv zeta in HC |- *.
          destruct HC as [C [HC1 [HC2 _]]].
          assert (EE0 : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r =
                        aEA s1 :: fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r).
          { unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx.
            rewrite (ACC aAligned_eq s1) in Hr; rewrite Hr; reflexivity. }
          rewrite EE0 in HC1.
          exists (lineAddrOf (fbPcAddr (aEA s1)) :: C); split; [| split].
          -- change (implFetchAccRqs r y = (rev (map (fun f => lineAddrOf (fbPcAddr f))
                       (fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r))
                     ++ lineAddrOf (fbPcAddr (aEA s1)) :: C)%list).
             rewrite HC1; cbn [map rev]; rewrite <- app_assoc; reflexivity.
          -- unfold optValid in HC2; rewrite (Hval Hr) in HC2.
             change (S (length C) + 0 = length (Fst (Snd (Fst (Fst y)))))%nat; lia.
          -- intros C0; discriminate C0.
        * intros r y Hr [HC _]; cbv zeta in HC |- *.
          assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                       fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r).
          { unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx.
            rewrite (ACC aAligned_eq s1) in Hr; rewrite Hr; reflexivity. }
          rewrite EE, Elv; exact HC.
  Qed.
End FetchAsmStep.
