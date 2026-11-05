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
From Cheriot.Proof Require Import RefSpecRead RefSpecFetch RefReplay RefLoadCommit RefFenceISend.
From Cheriot.Proof Require Import RefExecAux RefExecLive RefDmImpl RefDmStep RefLsfImpl RefRevokerStep RefLsfStep.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 5: THE fence.i COMMIT (SPEC SIDE)
 * ===========================================================================
 * When dataMem sends a fence.i request, the spec steps the fence.i entry at the head of the
 * chain: its deferred part sends the same request to every region (`sendAllS`). *)

Local Abbreviation TS t := (TreeState ElemState t).

Section FenceISpec.
  Variable pcAddrInit : Z.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Local Abbreviation CT := (specCoreTree pcAddrInit specRegions).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specClintStateA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation specPlicStateA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation mkCoreA := (mkCore pcAddrInit specRegions).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).

  (* The deferred part of a fence.i: the request goes to every region *)
  Lemma deferred_fenceI_wp :
    forall (envC : Env CT) rfC m sl (d : type (Bit RegIdxSzReal)) (a : type Addr) (dm : type (Option MemFenceUnion))
           (md : type (Option MulDivUnion)) (Q : TS CT -> Prop),
      optValid dm = true -> opIsMem (optData dm) = false -> opIsFenceI (optData dm) = true ->
      Q (mkCoreA rfC (sendAllS specRegions m) sl) ->
      evalActionPropGen envC (@specExecuteDeferred pcAddrInit config specRegions type d a dm md)
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl d a dm md Q Hv Hm Hfi HQ.
    unfold specExecuteDeferred.
    apply ev_ifElse_true; [exact Hv |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_ifElse_false; [exact (dispatchMemFence_notMem _ _ _ Hm) |].
    apply ev_letExp; cbv beta.
    apply ev_ifElse_true; [exact (eq_trans (dispatchMemFence_fenceI _ _ _ Hm) Hfi) |].
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    apply specMemSendFenceIRq_wp; intros v; cbv beta.
    repeat (apply ev_return; cbv beta).
    exact HQ.
  Qed.

  (* `specStep` for a fence.i at the head of the chain *)
  Lemma specStep_fenceI :
    forall rf0 rf1 m sl e q,
      GInstStep pcAddrInit rf0 rf1 e ->
      entryReq e = Some q -> opIsMem (mrOp q) = false -> opIsFenceI (mrOp q) = true ->
      SpecNoWait specRegions m -> optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      exists m', TraceFrameS specRegions m m' /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSysA rf0 m sl) (mkSysA rf1 (sendAllS specRegions m') sl) Zmod.zero.
  Proof.
    intros rf0 rf1 m sl e q [Hvc [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]]] Hq Hm Hfi Hnw Hsl Hfa Hmt Hme.
    pose proof Hq as Hq0; apply entryReq_some in Hq0 as [Hv Eq].
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSysA (cnwbApply pcAddrInit None rf0) m sl)
                    (fun s2' _ => exists m', TraceFrameS specRegions m m' /\
                       s2'.(Fst) = mkCoreA rf1 (sendAllS specRegions m') sl)).
    { apply specStep_wp with (Hdisj := Hdisj) (e := e) (rfMid := rfMid) (execOut := execOut)
        (Q := fun sc => exists m', TraceFrameS specRegions m m' /\ sc = mkCoreA rf1 (sendAllS specRegions m') sl);
        try assumption.
      - intros d v Hc; discriminate Hc.
      - intros m1 envC aluOut rfC HenvC Hm1 Ha Hrf.
        subst aluOut.
        assert (Erf : rfC = rf1).
        { rewrite Hrf, Hrf1, specMulDivWb_dmValid by (rewrite Hdm; exact Hv).
          rewrite defNextPcc_eq; reflexivity. }
        apply deferred_fenceI_wp.
        + rewrite defDm_eq, Hdm; exact Hv.
        + rewrite defDm_eq, Hdm; rewrite Eq in Hm; exact Hm.
        + rewrite defDm_eq, Hdm; rewrite Eq in Hfi; exact Hfi.
        + exists m1; split; [exact Hm1 | rewrite Erf; reflexivity]. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [m' [Hm' E]]]]].
    exists m'; split; [exact Hm' |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.
End FenceISpec.

(* ===========================================================================
 * THE fence.i COMMIT (RELATION SIDE) AND THE STAGE
 * ===========================================================================
 * The fence.i is the chain's head and pending, so nothing is live and only ticks follow it
 * (`FenceRel`). The spec steps it (`specStep_fenceI`); both sides have sent the same request
 * to every region (`sendAllS`, `sendAllI`); the ticks are then replayed eagerly. *)

Lemma ticks_no_inst :
  forall (G G1 G3 : list GItem) e, Forall (fun it => it = GTick) G -> G = (G1 ++ GInst e :: G3)%list -> False.
Proof.
  intros G G1 G3 e HF E; subst G; apply Forall_app in HF as [_ HF]; inversion HF; discriminate.
Qed.

Lemma ticks_not_in : forall (G : list GItem) e, Forall (fun it => it = GTick) G -> ~ In (GInst e) G.
Proof. intros G e HF Hin; rewrite Forall_forall in HF; discriminate (HF _ Hin). Qed.

Lemma chainReqs_ticks : forall (G : list GItem), Forall (fun it => it = GTick) G -> chainReqs G = [].
Proof.
  induction G as [| it G IH]; intros HF; [reflexivity |].
  inversion HF as [| ? ? E HF']; subst; exact (IH HF').
Qed.

Lemma chainReqs_inst :
  forall e (G : list GItem),
    chainReqs (GInst e :: G) = ((match entryReq e with Some q => [q] | None => [] end) ++ chainReqs G)%list.
Proof. reflexivity. Qed.

Section LsfFenceI.
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

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation GhostT := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELNE :=
    (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs).
  Local Abbreviation ACCREL :=
    (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine).
  Local Abbreviation MEMC :=
    (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clintS clint plicS plic fwcs).
  Local Abbreviation LSFFR :=
    (LsfFrame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation FIACC :=
    (FenceIAcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation ACCF f := (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (ACCF iRegions).
  Local Abbreviation iMemA := (ACCF iMem).
  Local Abbreviation iMemStA := (ACCF iMemSt).
  Local Abbreviation iDmStA := (ACCF iDmSt).
  Local Abbreviation iDmBufA := (ACCF iDmBuf).
  Local Abbreviation iFlushA := (ACCF iFlush).
  Local Abbreviation iStraddleA := (ACCF iStraddle).
  Local Abbreviation iFenceIPendingA := (ACCF iFenceIPending).
  Local Abbreviation iExecEpochA := (ACCF iExecEpoch).
  Local Abbreviation NoLiveA := (ACCF NoLive).
  Local Abbreviation NoFenceIWaitA := (ACCF NoFenceIWait).
  Local Abbreviation fbLiveA := (ACCF fbLive).
  Local Abbreviation iFetchBufA := (ACCF iFetchBuf).

  (* A fence.i is accepted with no write pending: the access in flight, if any, is a revoker
   * read, and no second line is pending *)
  Lemma AccessRel_fenceI :
    forall g (s1 : IState) (s2 : SState),
      ACCREL g s1 s2 -> dmLoadRq (iDmStA s1) = true ->
      msWriteRq (iMemStA s1) = false -> noPortWriteB implRegions (iRegionsA s1) = true ->
      optValid (sSecondA s2) = false /\
      (g_acc pcAddrInit g = AccNone \/ (exists st, g_acc pcAddrInit g = AccRevCap st) \/
       (exists st, g_acc pcAddrInit g = AccRevBit st)).
  Proof.
    intros g s1 s2 Ha Hlrq Hwr Hnpw.
    destruct (dmLoadRq_excl3 _ Hlrq) as [N1 [N2 N3]].
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      unfold WrStageRel, RdStageRel in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      first
        [ split; [assumption | left; reflexivity]
        | split; [assumption | right; left; eexists; reflexivity]
        | split; [assumption | right; right; eexists; reflexivity]
        | exfalso;
          first
            [ match goal with H : ?f ?x = true, N : ?f ?x = false |- _ => rewrite N in H; discriminate H end
            | match goal with Hk : lineKind _ _ = Some true |- _ =>
                assert (Hz : noPortWriteB implRegions (iRegionsA s1) = false)
                  by (eapply PortsWriteStaged_npw; [exact Hk | eassumption]);
                rewrite Hz in Hnpw; discriminate Hnpw
              end ] ].
  Qed.

  (* The relation after the commit, before the ticks are replayed *)
  Lemma RefRelNE_fenceI :
    forall (g : GhostT) e G2 rf1 (s1 s1' : IState) (s2 : SState) m' q rest,
      RELG g s1 s2 ->
      g_chain pcAddrInit g = GInst e :: G2 -> Forall (fun it => it = GTick) G2 ->
      GChain pcAddrInit rf1 G2 (iFlushA s1) ->
      entryReq e = Some q -> isPlainFence q = false -> opIsLoad (mrOp q) = false ->
      g_cnwb pcAddrInit g = None ->
      iDmBufA s1 = q :: rest -> dmLoadRq (iDmStA s1) = true ->
      LSFFR s1 s1' -> iDmStA s1' = iDmStA s1 -> iFenceIPendingA s1' = false -> iExecEpochA s1' = iExecEpochA s1 ->
      iMemA s1' = (sendAllI implRegions (iRegionsA s1) ,, (iMemA s1).(Snd)) ->
      NoFenceIWaitA s1 -> NoLiveA s1 -> optValid (iStraddleA s1) = false ->
      (g_acc pcAddrInit g = AccNone \/ (exists st, g_acc pcAddrInit g = AccRevCap st) \/
       (exists st, g_acc pcAddrInit g = AccRevBit st)) ->
      optValid (sSecondA s2) = false ->
      TraceFrameS specRegions (sMemA s2) m' ->
      RELNE (mkGhost pcAddrInit G2 rf1 None (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (g_acc pcAddrInit g)) s1'
            (mkSysA rf1 (sendAllS specRegions m') (sSecondA s2)).
  Proof.
    intros g e G2 rf1 s1 s1' s2 m' q rest Hg Hch Htk Hgc Hq Hpl Hnl Hcn Eb Hlrq
           [Erf Ewb Efe Ede Emd Edmf] Edmst Efip Eep Emem Hnfw Hnlv Hstr Hacc3 Hsec Htf.
    destruct Hg as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hwf Hrk].
    pose proof Hwf as [_ [_ [_ [Hwd _]]]].
    destruct (dm_deq_buf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                s1 s1' q rest Hwd Edmf Eb) as [Eb' Hwd'].
    assert (Ereg : iRegionsA s1' = sendAllI implRegions (iRegionsA s1)) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Emst : iMemStA s1' = iMemStA s1) by (unfold iMemSt; rewrite Emem; reflexivity).
    assert (Erq : ACCF iRequester s1' = ACCF iRequester s1) by (unfold iRequester; rewrite Emem; reflexivity).
    assert (Erp : ACCF iRdBufs s1' = ACCF iRdBufs s1) by (unfold iRdBufs; rewrite Emem; reflexivity).
    assert (Erev : ACCF iRev s1' = ACCF iRev s1)
      by (unfold iRev, implRevState; rewrite Ereg; rewrite regionStateAtI_send by exact I; reflexivity).
    assert (Epcc : ACCF iPcc s1' = ACCF iPcc s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Ed2a : ACCF iD2a s1' = ACCF iD2a s1) by (unfold iD2a; rewrite Ede; reflexivity).
    assert (Eflush : iFlushA s1' = iFlushA s1).
    { unfold iFlush, flushMulDiv, flushMulDivOn.
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1') with (ACCF iRf s1').
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1) with (ACCF iRf s1).
      rewrite Erf, Emd; reflexivity. }
    assert (Hlc : forall L, lineContent initLine specRegions (sMemA (mkSysA rf1 (sendAllS specRegions m') (sSecondA s2))) L =
                            lineContent initLine specRegions (sMemA s2) L).
    { intros L; change (sMemA (mkSysA rf1 (sendAllS specRegions m') (sSecondA s2))) with (sendAllS specRegions m').
      rewrite lineContent_send; exact (lineContent_traceFrame initLine specRegions _ _ Htf L). }
    assert (HNL' : NoLiveA s1').
    { unfold NoLive, daLive, aiLive, fbLive, iInstBuf, iFetchBuf, iPredEpoch in *; rewrite Ed2a, Efe, Eep; exact Hnlv. }
    assert (Hstr' : optValid (iStraddleA s1') = false) by (unfold iStraddle; rewrite Efe; exact Hstr).
    assert (Hnt : accTakesHead (g_acc pcAddrInit g) = false)
      by (destruct Hacc3 as [E | [[st E] | [st E]]]; rewrite E; reflexivity).
    constructor.
    - (* RfRel *)
      unfold RfRel; cbn [g_cnwb g_rf0 g_chain].
      split; [reflexivity |].
      split; [rewrite Eflush; exact Hgc |].
      split; [intros d v H; discriminate H |].
      intros G1 e0 G3 HG; exfalso; exact (ticks_no_inst _ _ _ _ Htk HG).
    - (* MemRelC: the fetch only reads; both sides sent the same request *)
      assert (Hm' : MEMC g s1 (mkSysA (sRfA s2) m' (sSecondA s2)))
        by (eapply MemRelC_traceFrame; [exact Htf | exact Hm]).
      unfold MemRelC in Hm' |- *; cbn [g_revOff]; rewrite Ereg.
      change (sMemA (mkSysA (sRfA s2) m' (sSecondA s2))) with m' in Hm'.
      change (sMemA (mkSysA rf1 (sendAllS specRegions m') (sSecondA s2))) with (sendAllS specRegions m').
      destruct Hm' as [Hmr [Hdev Hsnap]].
      split; [apply MemRel_send; exact Hmr | split; [apply DevInv_send; exact Hdev | apply SnapshotOK_send; exact Hsnap]].
    - unfold LatchRel; cbn [g_chain]; intros e0 Hin; exfalso; exact (ticks_not_in _ _ Htk Hin).
    - unfold ReplayRel; cbn [g_chain]; intros G1 e0 G3 rfe HG; exfalso; exact (ticks_no_inst _ _ _ _ Htk HG).
    - (* AccessRel: a revoker read (or nothing) is unaffected *)
      assert (Ha' : ACCREL g s1' (mkSysA rf1 (sendAllS specRegions m') (sSecondA s2))).
      { eapply AccessRel_frame_ports with (s1 := s1) (s2 := s2).
        - unfold PortsQuiet; rewrite Ereg; apply AllPorts_send; intros r y; reflexivity.
        - intros L; unfold PortsReadStaged; rewrite Ereg; apply AllPorts_send; intros r y; reflexivity.
        - intros L; unfold PortsReadOut; rewrite Ereg; apply AllPorts_send; intros r y; reflexivity.
        - intros L rq; unfold PortsWriteStaged; rewrite Ereg; apply AllPorts_send; intros r y; reflexivity.
        - exact Erev.
        - exact Emst.
        - exact Erp.
        - exact Erq.
        - exact Edmst.
        - reflexivity.
        - exact Hlc.
        - exact Ha. }
      unfold AccessRel in Ha' |- *; cbn [g_acc g_revOff g_cnwb g_chain].
      destruct Hacc3 as [E | [[st E] | [st E]]]; rewrite E in Ha' |- *; exact Ha'.
    - (* CnwbRel *)
      destruct (dmLoadRq_excl3 _ Hlrq) as [N1 [N2 _]].
      unfold CnwbRel; cbn [g_cnwb]; rewrite Edmst.
      split; [intros _; reflexivity |].
      split; [intros H; rewrite N2 in H; discriminate H |].
      split; [intros H; rewrite N2 in H; discriminate H |].
      intros H; rewrite N1 in H; discriminate H.
    - (* DmQueueRel: the fence.i left both *)
      unfold DmQueueRel in Hd |- *; cbv zeta in Hd |- *; cbn [g_chain g_acc].
      rewrite Eb', (chainReqs_ticks _ Htk), Hnt.
      rewrite Hnt, Eb, Hch, chainReqs_inst, Hq, (chainReqs_ticks _ Htk) in Hd.
      cbn [app filter] in Hd |- *; rewrite Hpl in Hd; cbn [negb] in Hd.
      injection Hd as Hd; exact Hd.
    - (* FenceRel: no fence.i is pending; the regions wait *)
      unfold FenceRel; cbn [g_chain]; rewrite Efip.
      split; [intros H; discriminate H |].
      split.
      + intros _; split; [reflexivity | split; [exact HNL' | split; [exact Hstr' |]]].
        intros e0 Hin; exact (ticks_not_in _ _ Htk Hin).
      + intros G1 e0 G3 HG; exfalso; exact (ticks_no_inst _ _ _ _ Htk HG).
    - (* ScoreRel *)
      assert (Eow : ACCF olderWriters s1' = ACCF olderWriters s1).
      { unfold olderWriters, dmInFlightDst; rewrite Edmst, Emd, Eb', Eb.
        cbn [filter]; rewrite Hnl; reflexivity. }
      unfold ScoreRel, daLive in *; cbn [g_d2aFo]; rewrite Eow, Ed2a, Eep, Ewb, Eflush; exact Hs.
    - (* FrontRel: nothing is live *)
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      + unfold daLive in *; rewrite Ed2a, Eep; exact F1.
      + unfold aiLive, iInstBuf in *; rewrite Efe, Eep; exact F2.
      + unfold fbLive, iFetchBuf, iPredEpoch in *; rewrite Efe, Eep; exact F3.
      + unfold daLive, aiLive, iInstBuf in *; rewrite Ed2a, Efe, Eep; exact F4.
      + unfold daLive, aiLive, iInstBuf, iFetchBuf in *; rewrite Ed2a, Efe, Eep; exact F5.
      + unfold LiveChain in *.
        rewrite liveInsts_noLive by exact HNL'; rewrite liveInsts_noLive in F6 by exact Hnlv.
        cbn [LiveChainG] in F6 |- *.
        eapply FrontierRel_noStraddle; [exact Hstr' |].
        unfold FrontierRel, fbLive, iFetchBuf, iFetchPc, iPredEpoch, iCurParcel, iStraddle in *.
        rewrite Efe, Epcc, Eep; exact F6.
      + unfold FetchRespRel in *.
        rewrite Ereg, AllPorts_send by (intros r y; reflexivity).
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        destruct HC as [C [HC1 [HC2 HC3]]].
        exists C; split; [unfold fbInRegion, iFetchBuf in *; rewrite Efe; exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE _]]].
        exists f, E'; split; [unfold fbInRegion, iFetchBuf in *; rewrite Efe; exact HE |].
        intros Hlv; exfalso.
        assert (Hin : In f (iFetchBufA s1)).
        { assert (Hin0 : In f (ACCF fbInRegion s1 r)) by (rewrite HE; left; reflexivity).
          unfold fbInRegion in Hin0; apply filter_In in Hin0; exact (proj1 Hin0). }
        destruct Hnlv as [_ [_ Hfb]]; rewrite Forall_forall in Hfb.
        assert (Elv : fbLiveA s1' f = fbLiveA s1 f) by (unfold fbLive, iPredEpoch; rewrite Efe, Eep; reflexivity).
        rewrite Elv, (Hfb f Hin) in Hlv; discriminate Hlv.
    - (* WfRel *)
      unfold WfRel in *.
      destruct Hwf as [W1 [W2 [W3 [_ [W5 W6]]]]].
      unfold iCurParcel, iFetchBuf, iInstBuf in *; rewrite Epcc, Efe, Ed2a, Ede, Emd.
      split; [exact W1 | split; [exact W2 | split; [exact W3 | split; [exact Hwd' | split; [exact W5 |]]]]].
      rewrite Ereg.
      apply (AllPorts_send_map
               (fun r y => (ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) /\
                           y.(Fst).(Fst).(Snd).(Snd).(Fst) = false)).
      + intros r y [[H1 H2] H3]; split; [exact H1 | exact (fenceICount_send r y H3 H2)].
      + exact (AllPorts_conj _ _ _ _ W6 Hnfw).
    - (* RevokerRel *)
      eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2); [reflexivity | reflexivity | exact Erev | exact Hlc | exact Hrk].
  Qed.

  Local Abbreviation eagerA := (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs Hdisj).

  (* dataMem sends a fence.i request: the spec steps the fence.i, then replays the ticks after it *)
  Lemma fenceI_commit :
    forall (g : GhostT) (s1 s1' : IState) (s2 : SState) q rest,
      RELG g s1 s2 -> FIACC s1 s1' ->
      iDmBufA s1 = q :: rest -> dmLoadRq (iDmStA s1) = true ->
      opIsMem (mrOp q) = false -> opIsFenceI (mrOp q) = true ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 q rest Hg [Hfr Edmst Hnpw [env' [mr' [v' [Hsend Emem]]]] Efip Eep] Eb Hlrq Hm Hfi.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm0 Hl Hrp He Ha Hc Hd Hf Hs Hfr0 Hw Hrk].
    apply andb_prop in Hnpw as [Hwr Hnpw]; apply negb_true_iff in Hwr.
    destruct (AccessRel_fenceI g s1 s2 Ha Hlrq Hwr Hnpw) as [Hsec Hacc3].
    assert (Hnt : accTakesHead (g_acc pcAddrInit g) = false)
      by (destruct Hacc3 as [E | [[st E] | [st E]]]; rewrite E; reflexivity).
    assert (Hpl : isPlainFence q = false) by (unfold isPlainFence; rewrite Hm, Hfi; reflexivity).
    assert (Hnl : opIsLoad (mrOp q) = false) by (unfold opIsLoad; rewrite Hm; reflexivity).
    assert (HH : HeadReq pcAddrInit g q)
      by (eapply head_of_dm; [exact He | exact Hsec | exact Hd | exact Hnt | exact Eb | exact Hpl]).
    destruct HH as [e [G2 [Hch Hq]]].
    (* the fence.i is pending and only ticks follow it, so nothing is live *)
    assert (Hefi : entryIsFenceI e = true) by (unfold entryIsFenceI; rewrite Hq; exact Hfi).
    destruct (proj2 (proj2 Hf) [] e G2 Hch Hefi) as [Hpend Htk].
    destruct (proj1 Hf Hpend) as [Hnlv [Hstr _]].
    assert (HdecW : forall r (y : TS (implExternalMemRegionTree r)),
               y.(Fst).(Fst).(Snd).(Snd).(Fst) = false \/ ~ y.(Fst).(Fst).(Snd).(Snd).(Fst) = false)
      by (intros r y; destruct (y.(Fst).(Fst).(Snd).(Snd).(Fst)); [right; discriminate | left; reflexivity]).
    destruct (AllPorts_dec (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) HdecW implRegions (iRegionsA s1))
      as [Hnfw | Hnfw].
    2: { exfalso; destruct (proj1 (proj2 Hf) Hnfw) as [Hp _]; rewrite Hpend in Hp; discriminate Hp. }
    assert (Hsnw : SpecNoWait specRegions (sMemA s2)).
    { unfold MemRelC, MemRel in Hm0; destruct Hm0 as [[Hpre _] _].
      eapply noWait_pre; [exact I | exact Hpre | exact Hnfw]. }
    assert (Hcn : g_cnwb pcAddrInit g = None) by exact (proj1 Hc Hlrq).
    destruct Hrf as [R1 [R2 _]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    rewrite Hch in R2.
    destruct (GChain_cons_inv pcAddrInit _ _ _ _ R2) as [rf1 [Hstep Hgc]]; cbn [ItemStep] in Hstep.
    assert (Hin : In (GInst e) (g_chain pcAddrInit g)) by (rewrite Hch; left; reflexivity).
    destruct (specStep_fenceI pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwcs Hdisj
                (g_rf0 pcAddrInit g) rf1 (sMemA s2) (sSecondA s2) e q Hstep Hq Hm Hfi Hsnw Hsec
                (Hrp [] e G2 (g_rf0 pcAddrInit g) Hch (GChainNil pcAddrInit _))
                (proj1 (Hl e Hin)) (proj2 (Hl e Hin)))
      as [m' [Htf Hsp]].
    rewrite <- R1, mkSys_eta in Hsp.
    pose proof (implRegionsSendFenceIRq_char _ _ _ _ _ Hsend) as Emr; rewrite Emr in Emem.
    pose proof (RefRelNE_fenceI g e G2 rf1 s1 s1' s2 m' q rest Hg Hch Htk Hgc Hq Hpl Hnl Hcn Eb Hlrq
                  Hfr Edmst Efip Eep Emem Hnfw Hnlv Hstr Hacc3 Hsec Htf) as Hne.
    assert (Hlen : (length (g_chain pcAddrInit (mkGhost pcAddrInit G2 rf1 None (g_revOff pcAddrInit g)
                                                    (g_d2aFo pcAddrInit g) (g_acc pcAddrInit g))) <= length G2)%nat)
      by apply le_n.
    destruct (eagerA (length G2) _ s1' _ Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction; [apply In_specStep_spec | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  Local Abbreviation LSF :=
    (@loadRqOrStoreOrFenceStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

  (* Milestone 5: dataMem's request stage. A store or a load enters the memory and a plain fence
   * leaves (the spec stutters); a fence.i commits. *)
  Theorem stepOK_loadRqOrStoreOrFenceStage :
    StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
           clintS clint plicS plic initLine fwcs LSF.
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [Hwd _]]]] _].
    destruct (lsf_char pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                _ s1 s1' _ Hwd Hsem) as [-> | [q [rest [Eb [Hlrq Hcase]]]]].
    - exists s2; split; [apply NilAction; reflexivity | exists g; exact Hg].
    - destruct Hcase as [[Hmm [Hst Hacc]] | [[Hmm [Hst Hacc]] | [[Hmm [Hfv Hacc]] | [Hmm [Hfv Hacc]]]]].
      + (* a store *)
        exists s2; split; [apply NilAction; reflexivity |].
        eexists; eapply RefRelG_store; [exact Hg | exact Hacc | exact Eb | exact Hlrq | |].
        * rewrite <- mfMem_op; exact Hmm.
        * rewrite <- (maStore_op q Hmm); exact Hst.
      + (* a load *)
        exists s2; split; [apply NilAction; reflexivity |].
        eexists; eapply RefRelG_load; [exact Hg | exact Hacc | exact Eb | exact Hlrq | |].
        * rewrite <- mfMem_op; exact Hmm.
        * rewrite <- (maStore_op q Hmm); exact Hst.
      + (* a plain fence *)
        exists s2; split; [apply NilAction; reflexivity |].
        exists g; eapply RefRelG_plain; [exact Hg | exact Hacc | exact Eb |].
        unfold isPlainFence; rewrite <- mfMem_op, <- (fvFenceI_op q Hmm), Hmm, Hfv; reflexivity.
      + (* a fence.i *)
        eapply fenceI_commit; [exact Hg | exact Hacc | exact Eb | exact Hlrq | |].
        * rewrite <- mfMem_op; exact Hmm.
        * rewrite <- (fvFenceI_op q Hmm); exact Hfv.
  Qed.
End LsfFenceI.
