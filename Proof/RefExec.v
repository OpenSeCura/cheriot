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
From Cheriot.Proof Require Export RefExecAux RefExecFrame RefExecStep RefExecLive RefExecFlush RefExecAppend.
From Stdlib Require Import Permutation.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* ===========================================================================
 * MILESTONE 7: `aluAndExecuteNonDeferredStage` REFINEMENT (`StepOK`)
 * =========================================================================== *)

Section ExecStageStepOK.
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
  Local Abbreviation STEPOK :=
    (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).

  Local Abbreviation FrontRelA :=
    (FrontRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              initLine fwcs).
  Local Abbreviation NoLiveA :=
    (NoLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation NoFenceIWaitA :=
    (NoFenceIWait pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation ScoreRelA :=
    (ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation DmQueueRelA :=
    (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation FenceRelA :=
    (FenceRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation WfRelA :=
    (WfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation daLiveA :=
    (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation iExecA :=
    (iExec pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation iClintA :=
    (iClint pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clint).
  Local Abbreviation iPlicA :=
    (iPlic pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA plic).
  Local Abbreviation olderWritersA :=
    (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* --- 1. Stutter Helper (`stutter_step`) --- *)

  Lemma stutter_step :
    forall (g : Ghost) (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 ->
      iRfA s1' = iRfA s1 ->
      iWbA s1' = iWbA s1 ->
      iMemA s1' = iMemA s1 ->
      iFetchA s1' = iFetchA s1 ->
      iDecodeA s1' = iDecodeA s1 ->
      iExecEpochA s1' = iExecEpochA s1 ->
      iFenceIPendingA s1' = iFenceIPendingA s1 ->
      iDmA s1' = iDmA s1 ->
      iMdA s1' = iMdA s1 ->
      exists g' s2',
        SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 Hg Erf Ewb Emem Efe Ede Eep Efip Edm Emd.
    exists g, s2; split; [apply NilAction; reflexivity |].
    exact (RefRelG_impl_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs g s1 s1' s2
             Erf Ewb Emem Efe Ede Edm Emd Eep Efip Hg).
  Qed.

  (* --- 2. Device & Memory Read Action Helpers --- *)

  Lemma SemAction_implMeip_eq :
    forall env m m' b,
      SemAction env (Impl.implPlicAction plic (@plicMeip (S (S (length (collectIrqActions implRegions)))) type)) m m' b ->
      m' = m /\ b = plicMeipOf (implPlicState pre post revBase revPfB revPfA plic m.(Fst)).
  Proof.
    intros env m m' b H.
    unfold Impl.implPlicAction, implNthRegionAction, implRegionsNthRegionAction, liftToImplRegion in H.
    apply SemAction_liftAction_iff in H as [rg' [H ->]].
    apply SemAction_genNthRegionAction_iff in H as [y' [H ->]].
    apply SemAction_liftAction_iff in H as [x' [H ->]].
    rewrite SemAction_iff_evalActionPropGen in H; cbn [evalActionPropGen] in H.
    destruct H as [<- <-].
    split; [| reflexivity].
    destruct m as [rg ms].
    rewrite !writeSubTreeState_readSubTreeState, updRegionStateAt_regionStateAt, writeSubTreeState_readSubTreeState; reflexivity.
  Qed.

  Lemma SemAction_implMtip_eq :
    forall env m m' b,
      SemAction env (Impl.implClintAction clint (readClintMtip type)) m m' b ->
      m' = m /\ b = clintSampled (implClintState pre post revBase revPfB revPfA clint m.(Fst)).
  Proof.
    intros env m m' b H.
    unfold Impl.implClintAction, implNthRegionAction, implRegionsNthRegionAction, liftToImplRegion in H.
    apply SemAction_liftAction_iff in H as [rg' [H ->]].
    apply SemAction_genNthRegionAction_iff in H as [y' [H ->]].
    apply SemAction_liftAction_iff in H as [x' [H ->]].
    rewrite SemAction_iff_evalActionPropGen in H; cbn [evalActionPropGen] in H.
    destruct H as [<- <-].
    split; [| reflexivity].
    destruct m as [rg ms].
    rewrite !writeSubTreeState_readSubTreeState, updRegionStateAt_regionStateAt, writeSubTreeState_readSubTreeState; reflexivity.
  Qed.

  Lemma SemAction_mem_noWriteRq_eq :
    forall env m m' b,
      SemAction env ((@implMemIfc config implRegions type revI).(mem_noWriteRq)) m m' b ->
      m' = m /\ b = andb (negb (msWriteRq m.(Snd).(Fst))) (noPortWriteB implRegions m.(Fst)).
  Proof.
    intros env m m' b H.
    rewrite SemAction_iff_evalActionPropGen in H.
    cbn [mem_noWriteRq implMemIfc] in H.
    unfold implMemNoPendingWrite, implMemNoWriteRq, implMemNoPortWriteRq, toAction in H.
    cbn [evalActionPropGen] in H.
    apply noPortWrite_wp in H; cbn [evalActionPropGen] in H.
    destruct H as [<- <-]; split; reflexivity.
  Qed.

  (* --- 3. Post-State Invariant Preservation Helpers --- *)

  Lemma WfRel_exec_step :
    forall (g g' : Ghost) (s1 s1' : IState) (s2 s2' : SState),
      WfRelA g s1 s2 ->
      fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') =
        fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) ->
      fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') =
        fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) ->
      fifo_wf (decode_toAluFifo decodeCapacity (iDecodeA s1')) ->
      fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1')) ->
      MulDivWf mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1') ->
      iRegionsA s1' = iRegionsA s1 ->
      iCurParcelA s1' = iCurParcelA s1 ->
      pcAligned (iPccA s1').(Snd).(Snd).(Fst) ->
      (forall x, In x (iD2aA s1') -> In x (iD2aA s1)) ->
      WfRelA g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' [[W1a [W1b [_ [W1d [W1e W1f]]]]] [W2 [_ [_ [_ W5]]]]] Efb Eib Hwd Hwm Hmd Ereg Ecp Hpc Hd2a.
    unfold WfRel; rewrite Efb, Eib, Ereg.
    refine (conj (conj W1a (conj _ (conj Hpc (conj _ _)))) (conj W2 (conj Hwd (conj Hwm (conj Hmd W5))))).
    - rewrite Ecp; unfold iFetchBuf; rewrite Efb; exact W1b.
    - rewrite Forall_forall in W1d |- *; intros x Hx; exact (W1d x (Hd2a x Hx)).
    - unfold iInstBuf, iFetchBuf; rewrite Eib, Efb; exact (conj W1e W1f).
  Qed.

  Lemma DmQueueRel_snoc_none :
    forall (g g1 : Ghost) (s1 s1' : IState) (e : GEntry),
      DmQueueRelA g s1 ->
      g_chain pcAddrInit g1 = (g_chain pcAddrInit g ++ [GInst e])%list ->
      g_acc pcAddrInit g1 = g_acc pcAddrInit g ->
      optValid (ge_dm e) = false ->
      iDmBufA s1' = iDmBufA s1 ->
      DmQueueRelA g1 s1'.
  Proof.
    intros g g1 s1 s1' e Hdmq Ech Eacc Edm Ebuf.
    unfold DmQueueRel in *; cbv zeta in *.
    rewrite Ebuf, Ech, Eacc.
    unfold chainReqs; rewrite flat_map_app, filter_app.
    cbn [flat_map]; unfold entryReq; rewrite Edm; cbn [app filter].
    rewrite app_nil_r; exact Hdmq.
  Qed.

  Local Lemma tl_app_nonempty :
    forall {A : Type} (l1 l2 : list A),
      l1 <> [] -> tl (l1 ++ l2)%list = (tl l1 ++ l2)%list.
  Proof.
    intros A [| x xs] l2 Hne; [exfalso; exact (Hne eq_refl) | reflexivity].
  Qed.

  Local Abbreviation AccessRelA :=
    (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
               initLine).

  Lemma DmQueueRel_snoc_some :
    forall (g g1 : Ghost) (s1 s1' : IState) (s2 : SState) (e : GEntry) (q : type MemFenceReq),
      DmQueueRelA g s1 ->
      AccessRelA g s1 s2 ->
      g_chain pcAddrInit g1 = (g_chain pcAddrInit g ++ [GInst e])%list ->
      g_acc pcAddrInit g1 = g_acc pcAddrInit g ->
      entryReq e = Some q ->
      iDmBufA s1' = (iDmBufA s1 ++ [q])%list ->
      DmQueueRelA g1 s1'.
  Proof.
    intros g g1 s1 s1' s2 e q Hdmq Hacc Ech Eacc Ereq Ebuf.
    unfold DmQueueRel in *; cbv zeta in *.
    rewrite Ebuf, filter_app, Ech, Eacc.
    unfold chainReqs; rewrite flat_map_app, filter_app.
    cbn [flat_map]; rewrite Ereq, app_nil_r.
    destruct (accTakesHead (g_acc pcAddrInit g)) eqn:Etake; [| rewrite Hdmq; reflexivity].
    assert (Hne : filter (fun q0 => negb (isPlainFence q0)) (chainReqs (g_chain pcAddrInit g)) <> []).
    { intros Hnil.
      destruct (accTakesHead_cases pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  initLine g s1 s2 Hacc Etake)
        as [[q_h [[e_h [G_h [Ech_h Eq_h]]] Hst_h]]
           | [_ [q_h [[e_h [G_h [Ech_h Eq_h]]] [Hld_h _]]]]].
      - assert (Hnpf_h : negb (isPlainFence q_h) = true)
          by (unfold isPlainFence; unfold opIsStore in Hst_h; apply andb_prop in Hst_h as [Hm _]; rewrite Hm; reflexivity).
        pose proof (headReq_first_req _ _ _ _ Ech_h Eq_h Hnpf_h) as Eq_head.
        rewrite Hnil in Eq_head; discriminate Eq_head.
      - assert (Hnpf_h : negb (isPlainFence q_h) = true)
          by (unfold isPlainFence; unfold opIsLoad in Hld_h; apply andb_prop in Hld_h as [Hm _]; rewrite Hm; reflexivity).
        pose proof (headReq_first_req _ _ _ _ Ech_h Eq_h Hnpf_h) as Eq_head.
        rewrite Hnil in Eq_head; discriminate Eq_head. }
    unfold chainReqs in Hne.
    rewrite (tl_app_nonempty _ _ Hne), Hdmq; reflexivity.
  Qed.

  Local Abbreviation MemRelCA :=
    (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic fwcs).

  Lemma FenceRel_snoc_step :
    forall (g g1 : Ghost) (s1 s1' : IState) (s2 : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (e : GEntry),
      FenceRelA g s1 ->
      MemRelCA g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      daLiveA s1 j = true ->
      g_chain pcAddrInit g1 = (g_chain pcAddrInit g ++ [GInst e])%list ->
      iRegionsA s1' = iRegionsA s1 ->
      iFenceIPendingA s1' = entryIsFenceI e ->
      (entryIsFenceI e = true -> NoLiveA s1' /\ optValid (iStraddleA s1') = false) ->
      FenceRelA g1 s1'.
  Proof.
    intros g g1 s1 s1' s2 j d2a_tail e Hf Hm Ed2a Hlive Ech Ereg Efip' Hfi_post.
    destruct (live_head_fence_facts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic fwcs g s1 s2 j d2a_tail Hf Hm Ed2a Hlive)
      as [Hfip [Hnfw _]].
    destruct Hf as [_ [_ Hf3]].
    unfold FenceRel, NoFenceIWait; rewrite Ech, Ereg, Efip'.
    split; [| split].
    - intros Hfi; destruct (Hfi_post Hfi) as [Hnl' Hstr'].
      split; [exact Hnl' | split; [exact Hstr' |]].
      exists (g_chain pcAddrInit g), e, []; split; [reflexivity | split; [exact Hfi | constructor]].
    - intros Hc; exfalso; exact (Hc Hnfw).
    - intros G1 e' G2 Hc Hfi'.
      destruct G2 as [| x G2' _] using rev_ind.
      + apply app_inj_tail in Hc as [_ Hc]; injection Hc as <-; split; [exact Hfi' | constructor].
      + rewrite app_comm_cons, app_assoc in Hc; apply app_inj_tail in Hc as [Hc _].
        exfalso; destruct (Hf3 G1 e' G2' Hc Hfi') as [Hp _]; rewrite Hfip in Hp; discriminate Hp.
  Qed.

  (* The head's register moves to the older writers (a load enters dataMem, a mulDiv its request
   * FIFO): the older writers are a permutation of the old ones and the head's register *)
  Lemma ScoreRel_move_to_older :
    forall (g g' : Ghost) (s1 s1' : IState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (fo0 : type FetchOut) (fo_tail : list (type FetchOut)),
      ScoreRelA g s1 ->
      iD2aA s1 = j :: d2a_tail ->
      g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = d2a_tail ->
      g_d2aFo pcAddrInit g' = fo_tail ->
      Permutation (olderWritersA s1') (olderWritersA s1 ++ d2aWriters [j])%list ->
      iWbA s1' = iWbA s1 ->
      (forall x, In x d2a_tail -> daLiveA s1' x = true -> daLiveA s1 x = true) ->
      (forall l1 j2 l2 fo,
         d2a_tail = (l1 ++ j2 :: l2)%list ->
         nth_error fo_tail (length l1) = Some fo ->
         daLiveA s1' j2 = true ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs1 fo) ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs2 fo) ->
         evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) ->
      ScoreRelA g' s1'.
  Proof.
    intros g g' s1 s1' j d2a_tail fo0 fo_tail Hsc Ed2a Efo Ed2a' Efo' Hperm Ewb' Hlv Hrr.
    assert (Hperm2 : Permutation (olderWritersA s1 ++ d2aWriters (j :: d2a_tail))%list
                                 (olderWritersA s1' ++ d2aWriters d2a_tail ++ [])%list).
    { rewrite app_nil_r; change (j :: d2a_tail) with ([j] ++ d2a_tail)%list; rewrite d2aWriters_app, app_assoc.
      apply Permutation_app_tail, Permutation_sym; exact Hperm. }
    apply (ScoreRel_pop pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             g g' s1 s1' j d2a_tail fo0 fo_tail [] Hsc Ed2a Efo Ed2a' Efo' Hperm2); [| | exact Hlv | exact Hrr].
    - intros r; rewrite Ewb'.
      destruct Hsc as [_ [Hwb _]]; specialize (Hwb r); rewrite Ed2a in Hwb.
      rewrite app_nil_r in Hperm2.
      split; intros Hr.
      + eapply Permutation_in; [exact Hperm2 | apply Hwb; exact Hr].
      + apply Hwb; eapply Permutation_in; [exact (Permutation_sym Hperm2) | exact Hr].
    - intros r Hr; eapply Permutation_in; [exact Hperm | exact Hr].
  Qed.

  (* --- 4. Universal Live-Tail `evalRegRead` Preservation Helper --- *)

  Lemma evalRegRead_gpr_ext :
    forall (regReadIn : type RegReadIn) (rf1 rf2 : RfState pcAddrInit),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb cs1Idx Zmod.zero = false ->
         evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf1 =
         evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf2) ->
      (Zmod.eqb cs2Idx Zmod.zero = false ->
         evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf1 =
         evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf2) ->
      evalRegRead pcAddrInit regReadIn rf1 = evalRegRead pcAddrInit regReadIn rf2.
  Proof.
    intros regReadIn rf1 rf2 decodeOut cs1Idx cs2Idx H1 H2.
    unfold evalRegRead; fold decodeOut cs1Idx cs2Idx.
    set (cs1Raw1 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf1).
    set (cs1Raw2 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf2).
    set (cs2Raw1 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf1).
    set (cs2Raw2 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf2).
    replace (evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw1))
      with (evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw2)).
    - replace (evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw1))
        with (evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw2)).
      + reflexivity.
      + symmetry; apply evalExpr_ITE0_isNotZero_regIdx; intros Hc2.
        unfold cs2Raw1, cs2Raw2; exact (H2 Hc2).
    - symmetry; apply evalExpr_ITE0_isNotZero_regIdx; intros Hc1.
      unfold cs1Raw1, cs1Raw2; exact (H1 Hc1).
  Qed.

  Lemma evalRegRead_writePcc :
    forall (p : type FullECapWithTag) (regReadIn : type RegReadIn) (rf : RfState pcAddrInit),
      evalRegRead pcAddrInit regReadIn (writePcc pcAddrInit p rf) =
      evalRegRead pcAddrInit regReadIn rf.
  Proof.
    intros p regReadIn rf.
    apply evalRegRead_gpr_ext; intros Hz;
      unfold writePcc, updGpr;
      apply evalReadRegsList_evalWriteRegsList_other;
      try apply NoDup_gprPathsWithKind;
      intros Heq; rewrite Heq in Hz;
      change (evalExpr ($0 : Expr type (Bit RegIdxSzReal))) with (@Zmod.zero (2 ^ RegIdxSzReal)) in Hz;
      rewrite Zmod.eqb_refl in Hz; discriminate Hz.
  Qed.

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind.
  Local Strategy opaque [gprPathsWithKind scrPathsWithKind csrPathsWithKind].

  Inductive PreservesGpr (idx : bits RegIdxSzReal) :
    forall {k : Kind}, Action type (rfTree pcAddrInit) k -> Prop :=
    | PG_Return      : forall {k} e, PreservesGpr idx (@Return type _ k e)
    | PG_LetExp      : forall {k k'} nm e cont,
                         (forall v, PreservesGpr idx (cont v)) ->
                         PreservesGpr idx (@LetExp type _ k k' nm e cont)
    | PG_LetExp_eval : forall {k k'} nm e cont,
                         PreservesGpr idx (cont (evalExpr e)) ->
                         PreservesGpr idx (@LetExp type _ k k' nm e cont)
    | PG_LetAction   : forall {k k'} nm a cont,
                         PreservesGpr idx a ->
                         (forall v, PreservesGpr idx (cont v)) ->
                         PreservesGpr idx (@LetAction type _ k k' nm a cont)
    | PG_ReadReg     : forall {k} nm p cont,
                         (forall v, PreservesGpr idx (cont v)) ->
                         PreservesGpr idx (@ReadReg type _ k nm p cont)
    | PG_IfElse      : forall {k k'} (nm : string) (c : Expr type Bool)
                              (ta fa : Action type _ k') (cont : type k' -> Action type _ k),
                         (evalExpr c = true -> PreservesGpr idx ta) ->
                         (evalExpr c = false -> PreservesGpr idx fa) ->
                         (forall v, PreservesGpr idx (cont v)) ->
                         PreservesGpr idx (IfElse nm c ta fa cont)
    | PG_System      : forall {k} ls cont,
                         PreservesGpr idx cont -> PreservesGpr idx (@System type _ k ls cont)
    | PG_readRegs    : forall {vK sz} (p : list (@RegOfKind (rfTree pcAddrInit) vK)) (i : Expr type (Bit sz)),
                         PreservesGpr idx (readRegsList p i)
    | PG_writeScr    : forall (i : Expr type (Bit ScrIdxSz)) v,
                         PreservesGpr idx (writeRegsList (scrPathsWithKind pcAddrInit) i v)
    | PG_writeCsr    : forall (i : Expr type (Bit CsrIdxSz)) v,
                         PreservesGpr idx (writeRegsList (csrPathsWithKind pcAddrInit) i v)
    | PG_writeGpr    : forall (i : Expr type (Bit RegIdxSzReal)) v,
                         idx <> evalExpr i ->
                         PreservesGpr idx (writeRegsList (gprPathsWithKind pcAddrInit) i v).

  Lemma evalActionPropGen_PreservesGpr :
    forall idx {k : Kind} (a : Action type (rfTree pcAddrInit) k),
      PreservesGpr idx a ->
      forall env s P,
        evalActionPropGen env a s P ->
        evalActionPropGen env a s (fun s' r =>
          evalReadRegsList (gprPathsWithKind pcAddrInit) idx s' =
          evalReadRegsList (gprPathsWithKind pcAddrInit) idx s /\ P s' r).
  Proof.
    intros idx k a Hpg; induction Hpg; intros env s P HP.
    - cbn [evalActionPropGen] in HP |- *; exact (conj eq_refl HP).
    - cbn [evalActionPropGen] in HP |- *; exact (H0 (evalExpr e) env s P HP).
    - cbn [evalActionPropGen] in HP |- *; exact (IHHpg env s P HP).
    - cbn [evalActionPropGen] in HP |- *.
      eapply evalActionPropGen_mono; [| exact (IHHpg env s _ HP)].
      intros sm vm [Heq1 HPm]; cbn beta.
      eapply evalActionPropGen_mono; [| exact (H0 vm env sm P HPm)].
      intros s' r [Heq2 HPs]; exact (conj (eq_trans Heq2 Heq1) HPs).
    - cbn [evalActionPropGen] in HP |- *; exact (H0 _ env s P HP).
    - cbn [evalActionPropGen] in HP |- *; destruct (evalExpr c) eqn:Ec.
      + eapply evalActionPropGen_mono; [| exact (H0 eq_refl env s _ HP)].
        intros sm vm [Heq1 HPm]; cbn beta.
        eapply evalActionPropGen_mono; [| exact (H4 vm env sm P HPm)].
        intros s' r [Heq2 HPs]; exact (conj (eq_trans Heq2 Heq1) HPs).
      + eapply evalActionPropGen_mono; [| exact (H2 eq_refl env s _ HP)].
        intros sm vm [Heq1 HPm]; cbn beta.
        eapply evalActionPropGen_mono; [| exact (H4 vm env sm P HPm)].
        intros s' r [Heq2 HPs]; exact (conj (eq_trans Heq2 Heq1) HPs).
    - cbn [evalActionPropGen] in HP |- *; exact (IHHpg env s P HP).
    - rewrite evalActionPropGen_readRegsList in HP |- *; exact (conj eq_refl HP).
    - rewrite evalActionPropGen_writeRegsList in HP |- *.
      split; [exact (readGpr_Fst_ext pcAddrInit idx _ s (updScr_Fst pcAddrInit (evalExpr i) (evalExpr v) s)) | exact HP].
    - rewrite evalActionPropGen_writeRegsList in HP |- *.
      split; [exact (readGpr_updCsr pcAddrInit idx (evalExpr i) (evalExpr v) s) | exact HP].
    - rewrite evalActionPropGen_writeRegsList in HP |- *.
      split; [exact (readGpr_updGpr_other pcAddrInit idx (evalExpr i) (evalExpr v) s H) | exact HP].
  Qed.

  Local Ltac pg_base :=
    repeat lazymatch goal with
    | |- PreservesGpr _ (readRegsList _ _) => apply PG_readRegs
    | |- PreservesGpr _ (writeRegsList (scrPathsWithKind pcAddrInit) _ _) => apply PG_writeScr
    | |- PreservesGpr _ (writeRegsList (csrPathsWithKind pcAddrInit) _ _) => apply PG_writeCsr
    | |- PreservesGpr _ (Return _) => apply PG_Return
    | |- PreservesGpr _ (LetExp _ _ _) => apply PG_LetExp; intros ?
    | |- PreservesGpr _ (LetAction _ _ _) => apply PG_LetAction; [| intros ?]
    | |- PreservesGpr _ (ReadReg _ _ _) => apply PG_ReadReg; intros ?
    | |- PreservesGpr _ (System _ _) => apply PG_System
    end.

  Local Lemma PreservesGpr_isInterruptPending :
    forall idx meip mtip,
      PreservesGpr idx (@isInterruptPending pcAddrInit type meip mtip).
  Proof. intros; unfold isInterruptPending; pg_base. Qed.

  Local Lemma PreservesGpr_incrementMinstret :
    forall idx,
      PreservesGpr idx (@incrementMinstret pcAddrInit type).
  Proof. intros; unfold incrementMinstret; pg_base. Qed.

  Local Lemma PreservesGpr_updateMshwmOnStore :
    forall idx a,
      PreservesGpr idx (@updateMshwmOnStore pcAddrInit type a).
  Proof.
    intros; unfold updateMshwmOnStore; pg_base.
    apply PG_IfElse; [intros _; pg_base | intros _; pg_base | intros ?; pg_base].
  Qed.

  Local Lemma PreservesGpr_handleTrap :
    forall idx pcc mc mt,
      PreservesGpr idx (@handleTrap pcAddrInit type pcc mc mt).
  Proof. intros; unfold handleTrap; pg_base. Qed.

  Local Ltac pg_lin :=
    repeat lazymatch goal with
    | |- PreservesGpr _ (readRegsList _ _) => apply PG_readRegs
    | |- PreservesGpr _ (writeRegsList (scrPathsWithKind pcAddrInit) _ _) => apply PG_writeScr
    | |- PreservesGpr _ (writeRegsList (csrPathsWithKind pcAddrInit) _ _) => apply PG_writeCsr
    | |- PreservesGpr _ (@isInterruptPending pcAddrInit type _ _) => apply PreservesGpr_isInterruptPending
    | |- PreservesGpr _ (@incrementMinstret pcAddrInit type) => apply PreservesGpr_incrementMinstret
    | |- PreservesGpr _ (@updateMshwmOnStore pcAddrInit type _) => apply PreservesGpr_updateMshwmOnStore
    | |- PreservesGpr _ (@handleTrap pcAddrInit type _ _ _) => apply PreservesGpr_handleTrap
    | |- PreservesGpr _ (Return _) => apply PG_Return
    | |- PreservesGpr _ (LetExp _ _ _) => apply PG_LetExp; intros ?
    | |- PreservesGpr _ (LetAction _ _ _) => apply PG_LetAction; [| intros ?]
    | |- PreservesGpr _ (ReadReg _ _ _) => apply PG_ReadReg; intros ?
    | |- PreservesGpr _ (System _ _) => apply PG_System
    end.

  Local Ltac pg_if :=
    apply PG_IfElse; [intros _; pg_lin | intros _; pg_lin | intros ?; pg_lin].

  Local Ltac pg_if_nz Hdst :=
    apply PG_IfElse;
      [ let Hz := fresh "Hz" in
        intros Hz; apply isNotZero_true_iff in Hz; pg_lin; apply PG_writeGpr; exact (Hdst Hz)
      | intros _; pg_lin
      | intros ?; pg_lin ].

  Local Lemma PreservesGpr_executeInterrupt :
    forall idx pcc meip mtip,
      PreservesGpr idx (@executeInterrupt pcAddrInit type pcc meip mtip).
  Proof. intros; unfold executeInterrupt; pg_lin. Qed.

  Local Lemma PreservesGpr_executeSequential :
    forall idx pcc aluOut,
      (Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false -> idx <> aluDstIdx aluOut) ->
      PreservesGpr idx (@executeSequential pcAddrInit type pcc aluOut).
  Proof.
    intros idx pcc aluOut Hneq; unfold executeSequential.
    apply PG_LetExp_eval; cbn beta; pg_lin.
    pg_if; pg_if_nz Hneq.
  Qed.

  Local Lemma PreservesGpr_executeNonSequential :
    forall idx pcc meip mtip aluOut,
      (Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false -> idx <> aluDstIdx aluOut) ->
      PreservesGpr idx (@executeNonSequential pcAddrInit type pcc meip mtip aluOut).
  Proof.
    intros idx pcc meip mtip aluOut Hneq; unfold executeNonSequential.
    do 2 (apply PG_LetExp_eval; cbn beta); pg_lin.
    pg_if; pg_if.
    - pg_if; pg_if.
    - pg_if.
      + pg_if.
        * pg_if_nz Hneq; pg_if.
        * pg_if_nz Hneq; pg_if.
      + pg_if_nz Hneq; pg_if.
        * pg_if.
        * pg_if; pg_if.
  Qed.

  Lemma PreservesGpr_executeNonDeferred :
    forall idx pcc meip mtip aluOut,
      (Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false -> idx <> aluDstIdx aluOut) ->
      PreservesGpr idx (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut).
  Proof.
    intros idx pcc meip mtip aluOut Hneq; unfold executeNonDeferred; pg_lin.
    pg_if; [apply PreservesGpr_executeInterrupt | pg_if].
    - apply PreservesGpr_executeSequential; exact Hneq.
    - apply PreservesGpr_executeNonSequential; exact Hneq.
  Qed.

  Lemma evalReadRegsList_executeNonDeferred_other :
    forall (pcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf0 rfMid : RfState pcAddrInit) (execOut : type ExecuteOut) (idx : bits RegIdxSzReal),
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut)
        rf0 rfMid execOut ->
      (Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false -> idx <> aluDstIdx aluOut) ->
      evalReadRegsList (gprPathsWithKind pcAddrInit) idx rfMid =
      evalReadRegsList (gprPathsWithKind pcAddrInit) idx rf0.
  Proof.
    intros pcc meip mtip aluOut rf0 rfMid execOut idx Hsem Hneq.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    pose proof (evalActionPropGen_PreservesGpr idx _
                  (PreservesGpr_executeNonDeferred idx pcc meip mtip aluOut Hneq)
                  defaultEnv rf0 _ Hsem) as Hpg.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hpg) as [s' [r' [_ [Heq [-> _]]]]].
    exact Heq.
  Qed.

  Local Lemma RegAvoidAll_head_neq_aluDstIdx :
    forall (ow : list (bits RegIdxSzReal)) (j : type DecodeToAluEntry)
           (l1 : list (type DecodeToAluEntry)) (pcc : type FullECapWithTag)
           (idx : bits RegIdxSzReal),
      RegAvoidAll (ow ++ d2aWriters (j :: l1)) idx ->
      Zmod.eqb idx Zmod.zero = false ->
      Zmod.eqb (aluDstIdx (evalAluOut pcc (daAluIn j))) Zmod.zero = false ->
      idx <> aluDstIdx (evalAluOut pcc (daAluIn j)).
  Proof.
    intros ow j l1 pcc idx Havoid Hz Hdstz.
    rewrite d2aDst_aluDstIdx in Hdstz |- *.
    apply (Havoid (d2aDst j)); [| exact Hdstz | exact Hz].
    apply in_or_app; right; rewrite d2aWriters_cons, Hdstz; left; reflexivity.
  Qed.

  Lemma evalRegRead_executeNonDeferred_writePcc_other :
    forall (pcc nextPcc : type FullECapWithTag) (meip mtip : bool)
           (j : type DecodeToAluEntry) (l1 : list (type DecodeToAluEntry))
           (fo : type FetchOut) (ow : list (bits RegIdxSzReal))
           (rf0 rfMid : RfState pcAddrInit) (execOut : type ExecuteOut),
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type pcc meip mtip (evalAluOut pcc (daAluIn j)))
        rf0 rfMid execOut ->
      RegAvoidAll (ow ++ d2aWriters (j :: l1)) (decCs1 fo) ->
      RegAvoidAll (ow ++ d2aWriters (j :: l1)) (decCs2 fo) ->
      evalRegRead pcAddrInit (evalDecode fo) (writePcc pcAddrInit nextPcc rfMid) =
      evalRegRead pcAddrInit (evalDecode fo) rf0.
  Proof.
    intros pcc nextPcc meip mtip j l1 fo ow rf0 rfMid execOut Hsem Hav1 Hav2.
    rewrite evalRegRead_writePcc.
    apply evalRegRead_gpr_ext; intros Hz;
      [ eapply evalReadRegsList_executeNonDeferred_other;
          [ exact Hsem | exact (RegAvoidAll_head_neq_aluDstIdx ow j l1 pcc _ Hav1 Hz) ]
      | eapply evalReadRegsList_executeNonDeferred_other;
          [ exact Hsem | exact (RegAvoidAll_head_neq_aluDstIdx ow j l1 pcc _ Hav2 Hz) ] ].
  Qed.

End ExecStageStepOK.
