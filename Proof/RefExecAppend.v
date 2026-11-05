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

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead RefSpecFetch RefRevoker RefReplay.
From Cheriot.Proof Require Export RefExecAux RefExecFrame RefExecStep RefExecLive RefExecFlush.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

Local Strategy expand [loadCmdOf ldAddr ldPending plSize].

Local Ltac strip_var u :=
  lazymatch u with
  | evalExpr (Var _ _ ?u') => strip_var u'
  | _ => u
  end.

Local Ltac readback :=
  match goal with |- context [evalExpr (ReadUnionData (Var type ?k ?u) ?i)] =>
    let w := strip_var u in
    lazymatch w with evalExpr (@BuildUnion type ?ls _ (Var _ _ ?x)) =>
      replace (evalExpr (ReadUnionData (Var type k u) i)) with x
        by (symmetry; exact (evalExpr_ReadUnionData_BuildUnion ls i (Var _ _ x) eq_refl))
    end
  end.

Local Ltac store_case Hs :=
  match goal with |- context [evalExpr (ReadUnionTag (Var ?ty ?k ?x) ?j)] =>
    assert (Hs' : evalExpr (ReadUnionTag (Var ty k x) j) = false) by exact Hs;
    rewrite Hs'; cbv iota
  end.

Lemma opLoad_notStore_local : forall op, opIsLoad op = true -> opIsStore op = false.
Proof.
  intros op H; unfold opIsLoad, opIsStore in *; cbv zeta in *.
  apply andb_prop in H as [Hm Hl]; rewrite Hm; cbn [andb].
  cbn [evalExpr] in Hl |- *.
  apply Zmod.eqb_eq in Hl; rewrite Hl; reflexivity.
Qed.

Lemma loadCmdOf_dst : forall q, opIsLoad (mrOp q) = true -> (ldPending (loadCmdOf q)).(Fst) = mrDst q.
Proof.
  intros q H.
  pose proof (opLoad_notStore_local _ H) as Hs.
  unfold opIsLoad, opIsStore, opMemPayload, opIsMem in *; cbv zeta in *.
  apply andb_prop in H as [Hm _]; rewrite Hm in Hs; cbn [andb] in Hs.
  unfold loadCmdOf; cbv zeta.
  unfold dispatchMemFence; cbn [evalLetExpr]; rewrite Hm; cbv beta iota.
  store_case Hs.
  readback; readback; reflexivity.
Qed.

Lemma opIsStore_opIsLoad_contra :
  forall op, opIsStore op = true -> opIsLoad op = true -> False.
Proof.
  intros op Hs Hl; rewrite (opLoad_notStore_local op Hl) in Hs; discriminate Hs.
Qed.

(* ===========================================================================
 * MILESTONE 7 LOCKSTEP COMMIT & GHOST-CHAIN APPEND (`RefExecAppend.v`)
 * =========================================================================== *)

Section ExecAppend.
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

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation RfSt := (RfState pcAddrInit).
  Local Abbreviation Ghost := (Ghost pcAddrInit).

  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation envI := (defaultEnv : Env ITree).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).

  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELNE :=
    (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
  Local Abbreviation FrontRelA :=
    (FrontRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              initLine fwcs).
  Local Abbreviation FrontierRelA :=
    (FrontierRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                 initLine fwcs).
  Local Abbreviation FetchRespRelA :=
    (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  initLine fwcs).
  Local Abbreviation LiveChainG_A := (LiveChainG pre post revBase revPfB revPfA initLine fwcs).
  Local Abbreviation NoLiveA :=
    (NoLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation NoFenceIWaitA :=
    (NoFenceIWait pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation ScoreRelA :=
    (ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation MemRelCA :=
    (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic fwcs).
  Local Abbreviation LatchRelA := (LatchRel pcAddrInit pre post revBase revPfB revPfA clintS plicS).
  Local Abbreviation ReplayRelA := (ReplayRel pcAddrInit pre post revBase revPfB revPfA initLine fwcs).
  Local Abbreviation AccessRelA :=
    (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
               initLine).
  Local Abbreviation CnwbRelA :=
    (CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             initLine).
  Local Abbreviation DmQueueRelA :=
    (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation FenceRelA :=
    (FenceRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation WfRelA :=
    (WfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RevokerRelA :=
    (RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                initLine).
  Local Abbreviation daLiveA :=
    (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation aiLiveA :=
    (aiLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation fbLiveA :=
    (fbLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA :=
    (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA :=
    (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemA :=
    (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchA :=
    (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA :=
    (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA :=
    (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iRegionsA :=
    (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA :=
    (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA :=
    (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA :=
    (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA :=
    (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchPcA :=
    (iFetchPc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iPredEpochA :=
    (iPredEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iCurParcelA :=
    (iCurParcel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iStraddleA :=
    (iStraddle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchBufA :=
    (iFetchBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iInstBufA :=
    (iInstBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iD2aA :=
    (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecEpochA :=
    (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA :=
    (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmBufA :=
    (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA :=
    (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iPccA :=
    (iPcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sClintA := (sClint pcAddrInit pre post revBase revPfB revPfA clintS).
  Local Abbreviation sPlicA := (sPlic pcAddrInit pre post revBase revPfB revPfA plicS).
  Local Abbreviation iClintA :=
    (iClint pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clint).
  Local Abbreviation iPlicA :=
    (iPlic pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA plic).
  Local Abbreviation olderWritersA :=
    (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* --- 1. Live Head Extraction & FenceI / NoFenceIWait Consequences --- *)

  Lemma NoFenceIWait_dec :
    forall (s1 : IState), NoFenceIWaitA s1 \/ ~ NoFenceIWaitA s1.
  Proof.
    intros s1; unfold NoFenceIWait.
    assert (Hdec : forall r (y : TS (implExternalMemRegionTree r)),
               y.(Fst).(Fst).(Snd).(Snd).(Fst) = false \/ ~ y.(Fst).(Fst).(Snd).(Snd).(Fst) = false)
      by (intros r y; destruct (y.(Fst).(Fst).(Snd).(Snd).(Fst)); [right; discriminate | left; reflexivity]).
    exact (AllPorts_dec (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) Hdec implRegions (iRegionsA s1)).
  Qed.

  Lemma not_NoLive_of_head :
    forall (s1 : IState) (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry)),
      iD2aA s1 = j :: d2a_tail ->
      daLiveA s1 j = true ->
      ~ NoLiveA s1.
  Proof.
    intros s1 j d2a_tail Ed2a Hlive [Hfa _].
    rewrite Ed2a in Hfa; inversion Hfa as [| ? ? Hj _]; subst.
    rewrite Hj in Hlive; discriminate Hlive.
  Qed.

  Lemma live_head_fence_facts :
    forall (g : Ghost) (s1 : IState) (s2 : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry)),
      FenceRelA g s1 ->
      MemRelCA g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      daLiveA s1 j = true ->
      iFenceIPendingA s1 = false /\
      NoFenceIWaitA s1 /\
      SpecNoWait specRegions (sMemA s2).
  Proof.
    intros g s1 s2 j d2a_tail [Hf1 [Hf2 _]] [[Hpre _] _] Ed2a Hlive.
    pose proof (not_NoLive_of_head s1 j d2a_tail Ed2a Hlive) as HnotLive.
    assert (Hfip : iFenceIPendingA s1 = false).
    { destruct (iFenceIPendingA s1) eqn:Ep; [| reflexivity].
      destruct (Hf1 eq_refl) as [Hnl _]; exfalso; exact (HnotLive Hnl). }
    assert (Hnfw : NoFenceIWaitA s1).
    { destruct (NoFenceIWait_dec s1) as [H | H]; [exact H |].
      destruct (Hf2 H) as [_ [Hnl _]]; exfalso; exact (HnotLive Hnl). }
    split; [exact Hfip | split; [exact Hnfw |]].
    eapply noWait_pre; [exact I | exact Hpre | exact Hnfw].
  Qed.

  Lemma live_head_front_facts :
    forall (g : Ghost) (s1 : IState) (s2 : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (fo0 : type FetchOut) (fo_tail : list (type FetchOut)),
      FrontRelA g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      daLiveA s1 j = true ->
      FetchAllowedInst initLine fwcs specRegions (sMemA s2) (iPccA s1) fo0 /\
      (foFault fo0 = false ->
         (needsPredOf (foInst fo0) = false -> daPredPc j = seqPcOf (iPccA s1).(Snd).(Snd).(Fst) (foInst fo0)) /\
         LiveChainG_A (iPccA s1) (sMemA s2) (FrontierRelA s1 s2) (daPredPc j)
           (map (fun jf => (snd jf, daPredPc (fst jf)))
                (filter (fun jf => daLiveA s1 (fst jf)) (combine d2a_tail fo_tail)) ++
            map (fun a => (aiFetchOut a, aiPredPc a)) (filter (aiLiveA s1) (iInstBufA s1)))%list).
  Proof.
    intros g s1 s2 j d2a_tail fo0 fo_tail [_ [_ [_ [_ [_ [F6 _]]]]]] Ed2a Efo Hlive.
    unfold LiveChain, liveInsts in F6.
    rewrite Ed2a, Efo in F6; cbn [combine filter fst] in F6.
    rewrite Hlive in F6; cbn [map app snd LiveChainG] in F6.
    destruct F6 as [Hfa Hrest].
    rewrite (pccWithAddr_self (iPccA s1)) in Hfa.
    split; [exact Hfa |].
    intros Hnf; rewrite Hnf in Hrest; exact Hrest.
  Qed.

  (* --- 2. Non-Redirecting Frontend Step & Spec Trace Frame --- *)

  Lemma FrontRel_traceFrame :
    forall (g : Ghost) (s1 : IState) (s2 s2' : SState),
      SnapshotOK fwcs specRegions (sMemA s2) ->
      TraceFrameS specRegions (sMemA s2) (sMemA s2') ->
      FrontRelA g s1 s2 ->
      FrontRelA g s1 s2'.
  Proof.
    intros g s1 s2 s2' Hsnap Hm' [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
    pose proof (FetchViewExt_traceFrame specRegions (sMemA s2) (sMemA s2') Hm') as Hext.
    split; [exact F1 |]; split; [exact F2 |]; split; [exact F3 |].
    split; [exact F4 |]; split; [exact F5 |].
    split.
    - unfold LiveChain in *.
      eapply LiveChainG_mono; [exact Hsnap | exact Hext | | exact F6].
      intros p Hp; exact (FrontierRel_mono pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                            initLine fwcs s1 s2 s2' p Hsnap Hext Hp).
    - unfold FetchRespRel in *.
      refine (AllPorts_impl _ _ implRegions (iRegionsA s1) _ F7).
      intros r y HP; cbv beta zeta in HP |- *.
      destruct HP as [C [HC1 [HC2 HC3]]]; exists C; split; [exact HC1 | split; [exact HC2 |]].
      intros Hv; destruct (HC3 Hv) as [f [E' [HE Hla]]]; exists f, E'; split; [exact HE |].
      intros Hlv; eapply LineAllowed_fetchViewExt; [exact Hsnap | exact Hext | exact (Hla Hlv)].
  Qed.

  Lemma LiveChainG_pcc_tag_ecap :
    forall (pcc1 pcc2 : type FullECapWithTag) m F pc l,
      pcc1.(Fst) = pcc2.(Fst) ->
      pcc1.(Snd).(Fst) = pcc2.(Snd).(Fst) ->
      LiveChainG_A pcc1 m F pc l ->
      LiveChainG_A pcc2 m F pc l.
  Proof.
    intros pcc1 pcc2 m F l0 l Ht He; revert l0.
    induction l as [| [fo pp] l IH]; intros pc H; cbn [LiveChainG] in *.
    - exact H.
    - destruct H as [Hfa Hrest]; split.
      + unfold pccWithAddr in Hfa |- *; rewrite <- Ht, <- He; exact Hfa.
      + destruct (foFault fo); [exact I |].
        destruct Hrest as [Hp Hl]; split; [exact Hp | exact (IH pp Hl)].
  Qed.

  Lemma FrontierRel_pcc_tag_ecap :
    forall (s1 s1' : IState) (s2 : SState) fp,
      iFetchBufA s1' = iFetchBufA s1 ->
      iExecEpochA s1' = iExecEpochA s1 ->
      iPredEpochA s1' = iPredEpochA s1 ->
      iFetchPcA s1' = iFetchPcA s1 ->
      iCurParcelA s1' = iCurParcelA s1 ->
      iStraddleA s1' = iStraddleA s1 ->
      (iPccA s1').(Fst) = (iPccA s1).(Fst) ->
      (iPccA s1').(Snd).(Fst) = (iPccA s1).(Snd).(Fst) ->
      FrontierRelA s1 s2 fp ->
      FrontierRelA s1' s2 fp.
  Proof.
    intros s1 s1' s2 fp Efb Eep Epep Efpc Ecp Estr Et Ee H.
    unfold FrontierRel in H |- *; cbv zeta in H |- *.
    assert (Elive : filter (fbLiveA s1') (iFetchBufA s1') = filter (fbLiveA s1) (iFetchBufA s1)).
    { rewrite Efb; apply filter_ext; intros f; unfold fbLive; rewrite Eep, Epep; reflexivity. }
    assert (Epre : forall a, preExcAt (iPccA s1') a = preExcAt (iPccA s1) a).
    { intros a.
      rewrite <- (preExcAt_pccWithAddr (iPccA s1') (iPccA s1).(Snd).(Snd).(Fst) a).
      rewrite <- (preExcAt_pccWithAddr (iPccA s1) (iPccA s1).(Snd).(Snd).(Fst) a).
      unfold pccWithAddr; rewrite Et, Ee; reflexivity. }
    assert (Etop : forall a c, topExcAt (iPccA s1') a c = topExcAt (iPccA s1) a c)
      by (intros a c; apply topExcAt_ecap; exact Ee).
    rewrite Elive, Efb, Efpc, Ecp, Estr.
    destruct H as [H1 [H2 [H3 H4]]]; split; [exact H1 |]; split; [| split; [| exact H4]].
    - eapply Forall_impl; [| exact H2]; intros f Hf; rewrite Epre; exact Hf.
    - destruct (optValid (iStraddleA s1)).
      + rewrite Epre, Etop; exact H3.
      + destruct (filter (fbLiveA s1) (iFetchBufA s1)) as [| f l]; [exact H3 |].
        destruct (iFetchBufA s1) as [| f0 rest]; [exact H3 |].
        replace (fbLiveA s1' f0) with (fbLiveA s1 f0) by (unfold fbLive; rewrite Eep, Epep; reflexivity).
        rewrite Epre; exact H3.
  Qed.

  Lemma FrontRel_step_no_redirect :
    forall (g g' : Ghost) (s1 s1' : IState) (s2 : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (fo0 : type FetchOut) (fo_tail : list (type FetchOut)),
      FrontRelA g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      daLiveA s1 j = true ->
      foFault fo0 = false ->
      iD2aA s1' = d2a_tail ->
      g_d2aFo pcAddrInit g' = fo_tail ->
      iExecEpochA s1' = iExecEpochA s1 ->
      iInstBufA s1' = iInstBufA s1 ->
      iFetchBufA s1' = iFetchBufA s1 ->
      iFetchPcA s1' = iFetchPcA s1 ->
      iPredEpochA s1' = iPredEpochA s1 ->
      iCurParcelA s1' = iCurParcelA s1 ->
      iStraddleA s1' = iStraddleA s1 ->
      iRegionsA s1' = iRegionsA s1 ->
      (iPccA s1').(Fst) = (iPccA s1).(Fst) ->
      (iPccA s1').(Snd).(Fst) = (iPccA s1).(Snd).(Fst) ->
      (iPccA s1').(Snd).(Snd).(Fst) = daPredPc j ->
      FrontRelA g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 j d2a_tail fo0 fo_tail Hfr Ed2a Efo Hlive Hnf
           Ed2a' Efo' Eep Eib Efb Efpc Epep Ecp Estr Ereg Et Ee Epc'.
    pose proof (live_head_front_facts g s1 s2 j d2a_tail fo0 fo_tail Hfr Ed2a Efo Hlive) as [_ Hnf_f].
    destruct (Hnf_f Hnf) as [_ Hlc_tail].
    destruct Hfr as [F1 [F2 [F3 [F4 [F5 [_ F7]]]]]].
    assert (Edlive : forall x, daLiveA s1' x = daLiveA s1 x)
      by (intros x; unfold daLive; rewrite Eep; reflexivity).
    assert (Eilive : forall x, aiLiveA s1' x = aiLiveA s1 x)
      by (intros x; unfold aiLive; rewrite Eep; reflexivity).
    split.
    - rewrite Ed2a'; rewrite Ed2a in F1.
      pose proof (StalePrefix_tail (daLiveA s1) j d2a_tail F1) as [l1 [l2 [-> [Hl1 Hl2]]]].
      exists l1, l2; split; [reflexivity | split].
      + eapply Forall_impl; [| exact Hl1]; intros x Hx; rewrite Edlive; exact Hx.
      + eapply Forall_impl; [| exact Hl2]; intros x Hx; rewrite Edlive; exact Hx.
    - split.
      + rewrite Eib; destruct F2 as [l1 [l2 [El [Hl1 Hl2]]]].
        exists l1, l2; split; [exact El | split].
        * eapply Forall_impl; [| exact Hl1]; intros x Hx; rewrite Eilive; exact Hx.
        * eapply Forall_impl; [| exact Hl2]; intros x Hx; rewrite Eilive; exact Hx.
      + split.
        * rewrite Efb; destruct F3 as [l1 [l2 [El [Hl1 Hl2]]]].
          exists l1, l2; split; [exact El | split].
          -- eapply Forall_impl; [| exact Hl1]; intros x Hx; unfold fbLive in *; rewrite Eep, Epep; exact Hx.
          -- eapply Forall_impl; [| exact Hl2]; intros x Hx; unfold fbLive in *; rewrite Eep, Epep; exact Hx.
        * split.
          -- intros Hex; rewrite Eib.
             assert (Hex1 : Exists (fun x => daLiveA s1 x = true) (iD2aA s1))
               by (rewrite Ed2a; left; exact Hlive).
             pose proof (F4 Hex1) as Hall.
             eapply Forall_impl; [| exact Hall]; intros x Hx; rewrite Eilive; exact Hx.
          -- split.
             ++ intros _; rewrite Efb, Eep.
                assert (Hex1 : Exists (fun x => daLiveA s1 x = true) (iD2aA s1))
                  by (rewrite Ed2a; left; exact Hlive).
                exact (F5 (or_introl Hex1)).
             ++ split.
                ** unfold LiveChain, liveInsts; rewrite Ed2a', Efo', Eib, Epc'.
                   replace (filter (fun jf => daLiveA s1' (fst jf)) (combine d2a_tail fo_tail))
                     with (filter (fun jf => daLiveA s1 (fst jf)) (combine d2a_tail fo_tail))
                     by (apply filter_ext; intros jf; rewrite Edlive; reflexivity).
                   replace (filter (aiLiveA s1') (iInstBufA s1))
                     with (filter (aiLiveA s1) (iInstBufA s1))
                     by (apply filter_ext; intros a; rewrite Eilive; reflexivity).
                   apply (LiveChainG_pcc_tag_ecap (iPccA s1) (iPccA s1')); [symmetry; exact Et | symmetry; exact Ee |].
                   revert Hlc_tail.
                   generalize (daPredPc j) as pc0.
                   generalize (map (fun jf => (snd jf, daPredPc (fst jf)))
                                   (filter (fun jf => daLiveA s1 (fst jf)) (combine d2a_tail fo_tail)) ++
                               map (fun a => (aiFetchOut a, aiPredPc a)) (filter (aiLiveA s1) (iInstBufA s1)))%list as l.
                   induction l as [| [fo1 pp1] l IH]; intros pc0 H; cbn [LiveChainG] in *.
                   --- exact (FrontierRel_pcc_tag_ecap s1 s1' s2 pc0 Efb Eep Epep Efpc Ecp Estr Et Ee H).
                   --- destruct H as [Hfa1 Hrest1]; split; [exact Hfa1 |].
                       destruct (foFault fo1); [exact I |].
                       destruct Hrest1 as [Hp1 Hl1]; split; [exact Hp1 | exact (IH pp1 Hl1)].
                ** unfold FetchRespRel, fbInRegion in *.
                   rewrite Efb, Ereg.
                   refine (AllPorts_impl _ _ implRegions (iRegionsA s1) _ F7).
                   intros r y [C [HC1 [HC2 HC3]]].
                   exists C; split; [exact HC1 | split; [exact HC2 |]].
                   intros Hv; destruct (HC3 Hv) as [f [E' [HE Hla]]].
                   exists f, E'; split; [exact HE |].
                   intros Hlv; apply Hla; unfold fbLive in *; rewrite <- Eep, <- Epep; exact Hlv.
  Qed.

  (* --- 3. Latch Monotonicity on Ghost Snoc (`LatchRel_snoc_inst`) --- *)

  Lemma plicMeipOf_eq_rect :
    forall (n1 n2 : nat) (e : n1 = n2) (xs : TS (plicTree n1)),
      plicMeipOf (eq_rect n1 (fun n => TS (plicTree n)) xs n2 e) = plicMeipOf xs.
  Proof. intros n1 n2 <- xs; reflexivity. Qed.

  Lemma LatchRel_snoc_inst :
    forall (g g1 : Ghost) (s1 : IState) (s2 : SState) (e : GEntry),
      LatchRelA g s2 ->
      MemRelCA g s1 s2 ->
      g_chain pcAddrInit g1 = (g_chain pcAddrInit g ++ [GInst e])%list ->
      ge_mtip e = clintSampled (iClintA s1) ->
      ge_meip e = plicMeipOf (iPlicA s1) ->
      LatchRelA g1 s2.
  Proof.
    intros g g1 s1 s2 e Hl [[_ [Hcl [Hpl _]]] _] Egh Emtip Emeip.
    unfold LatchRel in *; rewrite Egh.
    intros e' Hin; apply in_app_or in Hin as [Hin | [Heq | []]].
    - exact (Hl e' Hin).
    - injection Heq as <-.
      rewrite Emtip, Emeip.
      split.
      + destruct Hcl as [_ Hcl2]; exact Hcl2.
      + destruct Hpl as [e_eq [_ Hpl2]]; rewrite plicMeipOf_eq_rect in Hpl2; exact Hpl2.
  Qed.

  (* --- 4. Older Loads in `g_chain` Have Destinations in `olderWriters s1` --- *)

  Lemma headReq_first_req :
    forall G e_h G_h q_h,
      G = GInst e_h :: G_h ->
      entryReq e_h = Some q_h ->
      negb (isPlainFence q_h) = true ->
      filter (fun q => negb (isPlainFence q)) (chainReqs G) =
      q_h :: filter (fun q => negb (isPlainFence q)) (chainReqs G_h).
  Proof.
    intros G e_h G_h q_h -> Eq_h Hnpf_h.
    unfold chainReqs; cbn [flat_map]; rewrite Eq_h, filter_app; cbn [filter]; rewrite Hnpf_h; reflexivity.
  Qed.

  Lemma accTakesHead_cases :
    forall (g : Ghost) (s1 : IState) (s2 : SState),
      AccessRelA g s1 s2 ->
      accTakesHead (g_acc pcAddrInit g) = true ->
      (exists q_h, HeadReq pcAddrInit g q_h /\ opIsStore (mrOp q_h) = true) \/
      (dmLoadRp (iDmStA s1) = true /\
       exists q_h, HeadReq pcAddrInit g q_h /\ opIsLoad (mrOp q_h) = true /\ loadCmdOf q_h = dmLoadRpV (iDmStA s1)).
  Proof.
    intros g s1 s2 Hacc Etake; unfold AccessRel in Hacc.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                                      | rc st | st | st | addr pkt st];
      try (cbn [accTakesHead] in Etake; discriminate Etake).
    - destruct Hacc as [_ [_ [_ [_ [_ [_ [q_h [Hh [Hst _]]]]]]]]]; left; exists q_h; exact (conj Hh Hst).
    - destruct Hacc as [_ [_ [_ [_ [_ [_ [q_h [Hh [Hst _]]]]]]]]]; left; exists q_h; exact (conj Hh Hst).
    - destruct Hacc as [_ [_ [Elrp [Eld [_ [_ [_ [_ [_ [q_h [Hh [Hld Elc]]]]]]]]]]]];
        right; split; [exact Elrp | exists q_h; subst ld; exact (conj Hh (conj Hld Elc))].
    - destruct Hacc as [_ [_ [Elrp [Eld [_ [_ [_ [_ [_ [q_h [Hh [Hld Elc]]]]]]]]]]]];
        right; split; [exact Elrp | exists q_h; subst ld; exact (conj Hh (conj Hld Elc))].
    - destruct Hacc as [_ [_ [Elrp [Eld [_ [_ [_ [_ [_ [q_h [Hh [Hld Elc]]]]]]]]]]]];
        right; split; [exact Elrp | exists q_h; subst ld; exact (conj Hh (conj Hld Elc))].
  Qed.

  Lemma entryIsLoad_in_olderWriters :
    forall (g : Ghost) (s1 : IState) (s2 : SState) (G1 G2 : list GItem) (e0 : GEntry),
      DmQueueRelA g s1 ->
      AccessRelA g s1 s2 ->
      g_chain pcAddrInit g = (G1 ++ GInst e0 :: G2)%list ->
      entryIsLoad e0 = true ->
      Zmod.eqb (aluDstIdx (ge_aluOut e0)) Zmod.zero = false ->
      In (aluDstIdx (ge_aluOut e0)) (olderWritersA s1).
  Proof.
    intros g s1 s2 G1 G2 e0 Hdmq Hacc Egh Hld Hnz.
    unfold entryIsLoad in Hld.
    destruct (entryReq e0) as [q0 |] eqn:Eq0; [| discriminate Hld].
    assert (Edst : mrDst q0 = aluDstIdx (ge_aluOut e0)).
    { unfold entryReq in Eq0; destruct (optValid (ge_dm e0)); [injection Eq0 as <-; reflexivity | discriminate Eq0]. }
    assert (Hnpf : negb (isPlainFence q0) = true).
    { unfold isPlainFence; unfold opIsLoad in Hld; apply andb_prop in Hld as [Hm _]; rewrite Hm; reflexivity. }
    unfold DmQueueRel in Hdmq; cbv zeta in Hdmq.
    set (reqs := filter (fun q => negb (isPlainFence q)) (chainReqs (g_chain pcAddrInit g))) in Hdmq.
    assert (Hreqs_split : reqs = (filter (fun q => negb (isPlainFence q)) (chainReqs G1) ++
                                  q0 :: filter (fun q => negb (isPlainFence q)) (chainReqs G2))%list).
    { unfold reqs; rewrite Egh; unfold chainReqs.
      rewrite !flat_map_app, !filter_app; cbn [flat_map]; rewrite Eq0, filter_app; cbn [filter].
      rewrite Hnpf; reflexivity. }
    destruct (accTakesHead (g_acc pcAddrInit g)) eqn:Etake.
    - destruct (filter (fun q => negb (isPlainFence q)) (chainReqs G1)) as [| q1 rest1] eqn:Er1.
      + cbn [app] in Hreqs_split.
        destruct (accTakesHead_cases g s1 s2 Hacc Etake)
          as [[q_h [[e_h [G_h [Ech_h Eq_h]]] Hst_h]]
             | [Elrp [q_h [[e_h [G_h [Ech_h Eq_h]]] [Hld_h Elc]]]]].
        * assert (Hnpf_h : negb (isPlainFence q_h) = true)
            by (unfold isPlainFence; unfold opIsStore in Hst_h; apply andb_prop in Hst_h as [Hm _]; rewrite Hm; reflexivity).
          pose proof (headReq_first_req _ _ _ _ Ech_h Eq_h Hnpf_h) as Eq_head.
          change (filter (fun q => negb (isPlainFence q)) (chainReqs (g_chain pcAddrInit g))) with reqs in Eq_head.
          rewrite Hreqs_split in Eq_head; injection Eq_head as <-.
          exfalso; exact (opIsStore_opIsLoad_contra (mrOp q0) Hst_h Hld).
        * assert (Hnpf_h : negb (isPlainFence q_h) = true)
            by (unfold isPlainFence; unfold opIsLoad in Hld_h; apply andb_prop in Hld_h as [Hm _]; rewrite Hm; reflexivity).
          pose proof (headReq_first_req _ _ _ _ Ech_h Eq_h Hnpf_h) as Eq_head.
          change (filter (fun q => negb (isPlainFence q)) (chainReqs (g_chain pcAddrInit g))) with reqs in Eq_head.
          rewrite Hreqs_split in Eq_head; injection Eq_head as <-.
          assert (Eld_dst : (ldPending (dmLoadRpV (iDmStA s1))).(Fst) = aluDstIdx (ge_aluOut e0))
            by (rewrite <- Elc, (loadCmdOf_dst q0 Hld), Edst; reflexivity).
          rewrite <- Eld_dst in Hnz |- *.
          exact (dmLoadRp_in_olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                   s1 Elrp Hnz).
      + assert (Hin_tl : In q0 (tl reqs))
          by (rewrite Hreqs_split; cbn [app tl]; apply in_or_app; right; left; reflexivity).
        rewrite <- Hdmq in Hin_tl; apply filter_In in Hin_tl as [Hin_buf _].
        unfold olderWriters; apply filter_In; split; [| rewrite Hnz; reflexivity].
        apply in_or_app; right; apply in_or_app; left.
        rewrite <- Edst; apply in_map; apply filter_In; split; [exact Hin_buf | exact Hld].
    - assert (Hin_reqs : In q0 reqs)
        by (rewrite Hreqs_split; apply in_or_app; right; left; reflexivity).
      rewrite <- Hdmq in Hin_reqs; apply filter_In in Hin_reqs as [Hin_buf _].
      unfold olderWriters; apply filter_In; split; [| rewrite Hnz; reflexivity].
      apply in_or_app; right; apply in_or_app; left.
      rewrite <- Edst; apply in_map; apply filter_In; split; [exact Hin_buf | exact Hld].
  Qed.

  (* --- 5. Lockstep Spec Commit Step (`step_lockstep_commit`) --- *)

  Lemma readPcc_iFlush :
    forall (s1 : IState),
      readPcc pcAddrInit (iFlushA s1) = readPcc pcAddrInit (iRfA s1).
  Proof.
    intros s1; unfold iFlush, flushMulDiv; apply readPcc_flushMulDivCaps.
  Qed.

  Lemma step_lockstep_commit :
    forall (g : Ghost) (s1 s1' : IState) (s2 : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (aluOut : type AluOutUnion) (rfMid : RfSt) (execOut : type ExecuteOut),
      RELG g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      daLiveA s1 j = true ->
      iDmBufA s1 = [] ->
      dmLoadRq (iDmStA s1) = true ->
      msWriteRq (iMemStA s1) = false ->
      noPortWriteB implRegions (iRegionsA s1) = true ->
      aluOut = evalAluOut (readPcc pcAddrInit (iRfA s1)) (daAluIn j) ->
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type (readPcc pcAddrInit (iRfA s1))
           (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) aluOut)
        (iRfA s1) rfMid execOut ->
      optValid (execDataMem execOut) = false ->
      optValid (execMulDiv execOut) = false ->
      iFlushA s1' = writePcc pcAddrInit (defNextPcc execOut) (flushMulDivCaps pcAddrInit
                      (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1)) rfMid) ->
      iMemA s1' = iMemA s1 ->
      iDmA s1' = iDmA s1 ->
      iMdA s1' = iMdA s1 ->
      iFenceIPendingA s1' = false ->
      (forall g' s2m s2',
         RELG g s1 s2m ->
         g_d2aFo pcAddrInit g' = tl (g_d2aFo pcAddrInit g) ->
         TraceFrameS specRegions (sMemA s2m) (sMemA s2') ->
         ScoreRelA g' s1' /\ FrontRelA g' s1' s2' /\ WfRelA g' s1' s2') ->
      exists g' s2',
        SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 j d2a_tail aluOut rfMid execOut
           Hg Ed2a Hlive Hbuf Hlrq Hms Hnp Halu Hsem Hdm Hmd
           Efl' Emem Edm Emd Efip' Hrest.
    destruct (empty_dm_quiescent pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs g s1 s2 Hg Hbuf Hlrq Hms Hnp)
      as [Hch [Hcnwb _]].
    destruct (catchup_latches pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs HclintIdx HplicIdx g s1 s2 Hch Hg)
      as [s2m [Hdev [Hgm [Emeip Emtip]]]].
    destruct (empty_dm_quiescent pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs g s1 s2m Hgm Hbuf Hlrq Hms Hnp)
      as [_ [_ [Hsl [Erf0 Esrf]]]].
    pose proof Hgm as Hgm0; destruct Hgm0 as [Hrfm Hmm Hlm Hrpm Hem Ham Hcm Hdmqm Hfm Hsm Hfrm Hwm Hrkm].
    destruct (live_head_fence_facts g s1 s2m j d2a_tail Hfm Hmm Ed2a Hlive)
      as [Hfip [Hnfw Hsnw]].
    destruct Hsm as [Hnd [Hwb [Hlen Hreg]]].
    pose proof Hlen as Hlen0; rewrite Ed2a in Hlen0.
    destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen0; discriminate Hlen0 |].
    destruct (Hreg [] j d2a_tail fo0 Ed2a eq_refl Hlive) as [HaluIn [Hcs1 Hcs2]].
    destruct (live_head_front_facts g s1 s2m j d2a_tail fo0 fo_tail Hfrm Ed2a Efo Hlive) as [Hfa _].
    assert (Hneq_md :
      forall dstIdx resCap,
        In (dstIdx, resCap) (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1)) ->
        Zmod.eqb dstIdx Zmod.zero = false ->
        Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
        dstIdx <> aluOut.(Snd).(Fst)).
    { intros dstIdx resCap Hin_md Hz_d Hz_a Heq_d; subst dstIdx.
      assert (Hin_ow : In (aluOut.(Snd).(Fst)) (olderWritersA s1)).
      { unfold olderWriters; apply filter_In; split; [| rewrite Hz_d; reflexivity].
        apply in_or_app; right; apply in_or_app; right.
        change (aluOut.(Snd).(Fst)) with (fst (aluOut.(Snd).(Fst), resCap)); apply in_map; exact Hin_md. }
      assert (Hin_dw : In (aluOut.(Snd).(Fst)) (d2aWriters (iD2aA s1))).
      { change (aluOut.(Snd).(Fst)) with (aluDstIdx aluOut) in *.
        rewrite Halu, d2aDst_aluDstIdx in Hz_a |- *.
        rewrite Ed2a, d2aWriters_cons, Hz_a; left; reflexivity. }
      rewrite NoDup_app_iff in Hnd; destruct Hnd as [_ [_ Hdisj_ow]].
      exact (Hdisj_ow _ Hin_ow Hin_dw). }
    pose proof (SemAction_executeNonDeferred_flushMulDivCaps pcAddrInit
                  (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1))
                  (readPcc pcAddrInit (iRfA s1)) (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1))
                  aluOut (iRfA s1) rfMid execOut Hneq_md Hsem) as Hsem_fl.
    change (flushMulDivCaps pcAddrInit
              (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1)) (iRfA s1))
      with (iFlushA s1) in Hsem_fl.
    rewrite <- Emeip, <- Emtip, <- (readPcc_iFlush s1) in Hsem_fl.
    assert (Halu_fl :
      aluOut = evalAluOut (readPcc pcAddrInit (iFlushA s1))
                          (evalRegRead pcAddrInit (evalDecode fo0) (iFlushA s1)))
      by (rewrite <- HaluIn, (readPcc_iFlush s1); exact Halu).
    assert (Hfa_fl : FetchAllowedInst initLine fwcs specRegions (sMemA s2m) (readPcc pcAddrInit (iFlushA s1)) fo0)
      by (rewrite (readPcc_iFlush s1); exact Hfa).
    destruct (specStep_lockstep pcAddrInit config pre post revBase revPfB revPfA
                clintS plicS initLine fwcs Hdisj
                (iFlushA s1) (sMemA s2m) (sSecondA s2m) fo0 aluOut
                (flushMulDivCaps pcAddrInit
                   (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1)) rfMid)
                execOut Hsnw Hsl Hfa_fl Halu_fl Hsem_fl Hdm Hmd)
      as [m' [Hm' Hstep]].
    rewrite <- Esrf, mkSys_eta in Hstep.
    set (s2' := (mkCore pcAddrInit specRegions (iFlushA s1') m' (sSecondA s2m) ,, tt)).
    rewrite <- Efl' in Hstep.
    set (g' := mkGhost pcAddrInit [] (iFlushA s1') None (g_revOff pcAddrInit g) fo_tail (g_acc pcAddrInit g)).
    exists g', s2'; split.
    - eapply SemActions_trans; [exact Hdev |].
      eapply ConsAction;
        [apply In_specStep_spec
        | exact Hstep
        | apply NilAction; reflexivity].
    - assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
      assert (Hlc : forall L, lineContent initLine specRegions (sMemA s2') L = lineContent initLine specRegions (sMemA s2m) L)
        by (intros L; eapply lineContent_traceFrame; exact Hm').
      destruct (Hrest g' s2m s2' Hgm eq_refl Hm') as [Hs' [Hfr' Hwf']].
      constructor.
      + unfold RfRel; cbn [g_chain g_rf0 g_cnwb cnwbApply].
        split; [reflexivity | split; [apply GChainNil | split; [intros d v H; discriminate H | intros G1 e G2 H; destruct G1; discriminate H]]].
      + unfold MemRelC in *; cbn [g_revOff]; rewrite Ereg.
        eapply MemRelC_traceFrame; [exact Hm' | exact Hmm].
      + unfold LatchRel; cbn [g_chain]; intros e [].
      + unfold ReplayRel; cbn [g_chain]; intros G1 e G2 rfe H; destruct G1; discriminate H.
      + left; reflexivity.
      + eapply AccessRel_ghost_mem with (g := g); [reflexivity | reflexivity | symmetry; exact Hcnwb | |].
        * intros q [e [G' [HG _]]]; rewrite Hch in HG; discriminate HG.
        * eapply AccessRel_frame with (s1 := s1) (s2 := s2m);
            try reflexivity;
            try (unfold iMemSt, iRequester, iReadRp, iRdBufs, iDmSt, iRev, iRegions; rewrite ?Emem, ?Edm; reflexivity);
            [exact Hlc | exact Ham].
      + unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        unfold iDmSt in *; rewrite Edm.
        pose proof (dmLoadRq_excl _ Hlrq) as [Hlrp [Hrrq _]].
        split; [intros _; reflexivity | split; [rewrite Hrrq; intros H; discriminate H |
                split; [rewrite Hrrq; intros H; discriminate H | rewrite Hlrp; intros H; discriminate H]]].
      + unfold DmQueueRel, iDmBuf in *; cbn [g_chain g_acc]; rewrite Edm; rewrite Hch in Hdmqm; exact Hdmqm.
      + unfold FenceRel, NoFenceIWait; cbn [g_chain]; rewrite Efip', Ereg.
        split; [intros H; discriminate H | split; [| intros G1 e0 G2 H; destruct G1; discriminate H]].
        intros Hc; exfalso; exact (Hc Hnfw).
      + exact Hs'.
      + exact Hfr'.
      + exact Hwf'.
      + eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2m);
          try reflexivity;
          try (unfold iRev, iRegions; rewrite Emem; reflexivity);
          [exact Hlc | exact Hrkm].
  Qed.

  (* --- 6. Ghost Chain Append + Eager Replay (`step_append_nonvirt`) --- *)

  Lemma step_append_nonvirt :
    forall (g : Ghost) (s1 s1' : IState) (s2 : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (fo0 : type FetchOut) (fo_tail : list (type FetchOut))
           (e : GEntry) (g1 : Ghost),
      RELG g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      daLiveA s1 j = true ->
      ge_fetchOut e = fo0 ->
      ge_mtip e = clintSampled (iClintA s1) ->
      ge_meip e = plicMeipOf (iPlicA s1) ->
      GInstStep pcAddrInit (iFlushA s1) (iFlushA s1') e ->
      g1 = mkGhost pcAddrInit (g_chain pcAddrInit g ++ [GInst e])%list (g_rf0 pcAddrInit g)
                   (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g) fo_tail (g_acc pcAddrInit g) ->
      iMemA s1' = iMemA s1 ->
      iDmStA s1' = iDmStA s1 ->
      DmQueueRelA g1 s1' ->
      FenceRelA g1 s1' ->
      ScoreRelA g1 s1' ->
      FrontRelA g1 s1' s2 ->
      WfRelA g1 s1' s2 ->
      exists g' s2',
        SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 j d2a_tail fo0 fo_tail e g1
           Hg Ed2a Efo Hlive Efo0 Emtip Emeip Hstep Eg1
           Emem Edmst Hdmq' Hf' Hs' Hfr' Hwf'.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    destruct Hg as [Hrf Hm Hl Hrp _ Ha Hc Hd _ Hs Hfr _ Hrk].
    destruct (live_head_front_facts g s1 s2 j d2a_tail fo0 fo_tail Hfr Ed2a Efo Hlive) as [Hfa _].
    destruct Hrf as [R1 [R2 [R3 R4]]].
    assert (Hav_e :
      forall d : bits RegIdxSzReal,
        (Zmod.eqb d Zmod.zero = false -> In d (olderWritersA s1)) ->
        EntryAvoids e d).
    { intros d Hd_in.
      eapply (EntryAvoids_of_in_olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                g s1 j d2a_tail fo0 fo_tail e d Hs Ed2a Efo Hlive Efo0);
        [ destruct Hstep as [_ [Halu_e _]]; unfold geAluOut, geAluIn in Halu_e;
          rewrite Halu_e, wrappedAlu_dstIdx, Efo0; reflexivity
        | exact Hd_in ]. }
    assert (Hne : RELNE g1 s1' s2).
    { subst g1; constructor.
      - unfold RfRel; cbn [g_chain g_rf0 g_cnwb].
        split; [exact R1 |].
        split; [exact (GChain_snoc_inst pcAddrInit (g_rf0 pcAddrInit g) (g_chain pcAddrInit g)
                         (iFlushA s1) e (iFlushA s1') R2 Hstep) |].
        split.
        + intros d v Hcn.
          apply (RefExecFrame.ChainAvoids_app (g_chain pcAddrInit g) [GInst e] d (R3 d v Hcn)).
          intros e' [Heq | []]; injection Heq as <-.
          apply Hav_e; intros Hnz.
          eapply cnwb_in_olderWriters; [exact Hc | exact Ha | exact Hcn | exact Hnz].
        + intros G1 e0 G2 Eapp Hld.
          destruct (snoc_split_GInst (g_chain pcAddrInit g) G1 G2 e e0 Eapp)
            as [[-> [-> ->]] | [G2' [Eg_split ->]]].
          * intros e' [].
          * apply (RefExecFrame.ChainAvoids_app G2' [GInst e] (aluDstIdx (ge_aluOut e0))
                     (R4 G1 e0 G2' Eg_split Hld)).
            intros e' [Heq | []]; injection Heq as <-.
            apply Hav_e; intros Hnz.
            exact (entryIsLoad_in_olderWriters g s1 s2 G1 G2' e0 Hd Ha Eg_split Hld Hnz).
      - unfold MemRelC in *; cbn [g_revOff]; rewrite Ereg; exact Hm.
      - exact (LatchRel_snoc_inst g
                 (mkGhost pcAddrInit (g_chain pcAddrInit g ++ [GInst e])%list (g_rf0 pcAddrInit g)
                    (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g) fo_tail (g_acc pcAddrInit g))
                 s1 s2 e Hl Hm eq_refl Emtip Emeip).
      - unfold ReplayRel; cbn [g_chain g_rf0].
        intros G1 e0 G2 rfe Eapp Hch1.
        destruct (snoc_split_GInst (g_chain pcAddrInit g) G1 G2 e e0 Eapp)
          as [[-> [-> ->]] | [G2' [Eg_split ->]]].
        + pose proof (GChain_det pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) rfe (iFlushA s1) Hch1 R2) as ->.
          rewrite Efo0, (readPcc_iFlush s1); exact Hfa.
        + exact (Hrp G1 e0 G2' rfe Eg_split Hch1).
      - eapply AccessRel_ghost_mem with (g := g); [reflexivity | reflexivity | reflexivity | |].
        + intros q [e0 [G' [HG Hq]]] _.
          exists e0, (G' ++ [GInst e])%list; split; [cbn [g_chain]; rewrite HG; reflexivity | exact Hq].
        + eapply AccessRel_frame with (s1 := s1) (s2 := s2);
            try reflexivity;
            try (unfold iMemSt, iRequester, iReadRp, iRdBufs, iRev, iRegions; rewrite ?Emem, ?Edmst; reflexivity);
            exact Ha.
      - unfold CnwbRel in *; cbn [g_cnwb g_chain g_acc]; rewrite Edmst.
        destruct Hc as [C1 [C2 [C3 C4]]].
        split; [exact C1 | split; [exact C2 | split; [exact C3 |]]].
        intros Hlrp Hcn Hat.
        apply (RefExecFrame.ChainAvoids_app (g_chain pcAddrInit g) [GInst e]
                 (ldPending (dmLoadRpV (iDmStA s1))).(Fst) (C4 Hlrp Hcn Hat)).
        intros e' [Heq | []]; injection Heq as <-.
        apply Hav_e; intros Hnz.
        exact (dmLoadRp_in_olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                 s1 Hlrp Hnz).
      - exact Hdmq'.
      - exact Hf'.
      - exact Hs'.
      - exact Hfr'.
      - exact Hwf'.
      - eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2);
          try reflexivity;
          try (unfold iRev, iRegions; rewrite Emem; reflexivity);
          exact Hrk. }
    exact (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs Hdisj
             (length (g_chain pcAddrInit g1)) g1 s1' s2 (Nat.le_refl _) Hne).
  Qed.

End ExecAppend.
