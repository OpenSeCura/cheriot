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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefExecImpl.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 6: THE IMPL SIDE OF `decodeAndRegReadStage`
 * ===========================================================================
 * One lemma per branch of `decodeAndRegRead` (Impl/ImplDecode.v): from the stage's `SemAction`
 * and the branch condition, what the step does to each part of the impl state the relation
 * reads. The action is stepped one constructor at a time (`fw_*`, RefExecImpl.v). The decoder's
 * output stays a variable (`fw_letLGen`), so no conversion evaluates the decoder. *)

Local Abbreviation TS t := (TreeState ElemState t).

Section DecodeImpl.
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

  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable envI : Env (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STAGE :=
    (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation iExecEpochA :=
    (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation aiLiveA :=
    (aiLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation D2AF s1 := (decode_toAluFifo decodeCapacity (iDecodeA s1)).
  Local Abbreviation IBF s1 := (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* --- 1. What the Stage Reads and Computes --- *)

  Definition dHead (s1 : IState) : type (Option AssembledInst) := fifoFirstVal (IBF s1).
  Definition dA (s1 : IState) : type AssembledInst := (dHead s1).(Fst).
  Definition dFo (s1 : IState) : type FetchOut := aiFetchOut (dA s1).
  Definition dAluIn (s1 : IState) : type AluInInstGroup :=
    evalRegRead pcAddrInit (evalDecode (dFo s1)) (iRfA s1).
  Definition dFull (s1 : IState) : bool :=
    Zmod.eqb (fifo_size (D2AF s1)) (Zmod.of_Z _ (Z.of_nat decodeCapacity)).

  (* The issue test, in the stage's syntax *)
  Definition canIssueV (full : bool) (cs1 cs2 : bits RegIdxSzReal) (w1 w2 wcd writesCd : bool) : bool :=
    evalExpr (Not (Or [ Var type Bool full ;
                        And [ isNotZero (Var type (Bit RegIdxSzReal) cs1) ; Var type Bool w1 ] ;
                        And [ isNotZero (Var type (Bit RegIdxSzReal) cs2) ; Var type Bool w2 ] ;
                        And [ Var type Bool writesCd ; Var type Bool wcd ] ])).

  Definition dCanIssue (s1 : IState) : bool :=
    canIssueV (dFull s1) (decCs1 (dFo s1)) (decCs2 (dFo s1))
      (evalReadWaitBit (decCs1 (dFo s1)) (iWbA s1)) (evalReadWaitBit (decCs2 (dFo s1)) (iWbA s1))
      (evalReadWaitBit (instCd (foInst (dFo s1))) (iWbA s1)) (decWritesCd (dFo s1)).

  (* The decode-to-ALU entry the stage enqueues *)
  Definition dEntry (s1 : IState) : type DecodeToAluEntry :=
    (dAluIn s1 ,, (aiPredPc (dA s1) ,, (iExecEpochA s1 ,, tt))).

  (* The impl stutters: only the decode stage's `canProceed` may change *)
  Definition DecStutter (s1 s1' : IState) : Prop :=
    iRfA s1' = iRfA s1 /\ iWbA s1' = iWbA s1 /\ iMemA s1' = iMemA s1 /\ iFetchA s1' = iFetchA s1 /\
    D2AF s1' = D2AF s1 /\ iExecA s1' = iExecA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1.

  Lemma fetch_withInstFifo_eta :
    forall sf, fetch_withInstFifo pcAddrInit fetchCapacity instCapacity sf
                 (fetch_instFifo pcAddrInit fetchCapacity instCapacity sf) = sf.
  Proof. reflexivity. Qed.

  (* --- 2. Stepping Tactics --- *)

  Ltac dec_open H :=
    rewrite SemAction_iff_evalActionPropGen in H;
    unfold decodeAndRegReadStage in H;
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H;
    unfold decodeAndRegRead in H;
    cbn [fetch_instFirst fetch_instDeq implFetchIfc execute_readExecEpoch implExecuteIfc] in H.

  Ltac dec_canProceed H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readDecodeCanProceed decodeCapacity _ _) HQ_)];
    cbv beta in H.
  Ltac dec_clear H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_clearDecodeCanProceed decodeCapacity _ _) HQ_)];
    cbv beta in H.
  Ltac dec_head H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_fetchInstFirst pcAddrInit fetchCapacity instCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_first_iff instCapacity AssembledInst _ _ _)) in HQ_;
       cbv beta in HQ_; rewrite fetch_withInstFifo_eta in HQ_; exact HQ_]; cbv beta in H.
  Ltac dec_full H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_isFull_raw decodeCapacity DecodeToAluEntry _ _ _) HQ_)];
    cbv beta in H.
  Ltac dec_epoch H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecEpoch _ _) HQ_)]; cbv beta in H.
  Ltac dec_lets H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (LetExp _ _ _) _ _ => apply fw_letExp in H
            end; cbv beta in H).
  (* the decoder: its value becomes a fresh variable *)
  Ltac dec_decode H :=
    lazymatch type of H with
    | evalActionPropGen _ (LetAction _ (toAction _ _) _) _ _ =>
        let a := fresh "rri" in let Ea := fresh "Erri" in
        apply fw_letLGen in H; destruct H as [a [Ea H]]; cbv beta in H
    end.
  Ltac dec_regRead H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_regRead pcAddrInit _ _ _) HQ_)]; cbv beta in H.
  Ltac dec_wait H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readGprWaitBit _ _ _) HQ_)]; cbv beta in H.
  Ltac dec_ret H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (Return _) _ _ => apply fw_return in H
            | evalActionPropGen _ (LetAction _ _ _) _ _ => apply fw_letAction in H
            end; cbv beta in H).

  (* everything up to the valid test *)
  Ltac dec_prefix H Hcp :=
    dec_open H; dec_canProceed H;
    apply fw_ifTrue in H; [| exact Hcp];
    dec_clear H; dec_head H; dec_full H; dec_epoch H; dec_lets H; dec_decode H; dec_lets H;
    dec_regRead H; dec_lets H; dec_wait H; dec_wait H; dec_wait H.

  (* the fetch instBuf dequeue and the other writes *)
  Ltac dec_deqLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_fetchInstDeq pcAddrInit fetchCapacity instCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_deq_iff instCapacity AssembledInst _ _ _)) in HQ_;
       cbv beta in HQ_; exact HQ_]; cbv beta in H.
  Ltac dec_deq H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_fetchInstDeq pcAddrInit fetchCapacity instCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_deq_iff instCapacity AssembledInst _ _ _)) in HQ_;
       cbv beta in HQ_; exact HQ_]; cbv beta in H.
  Ltac dec_setCp H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setDecodeCanProceed decodeCapacity _ _) HQ_)];
    cbv beta in H.
  Ltac dec_wb H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setDstWaitBits _ _ _ _ _) HQ_)]; cbv beta in H.
  Ltac dec_enqLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_enq_iff decodeCapacity DecodeToAluEntry _ _ _ _) HQ_)]; cbv beta in H.

  (* --- 3. The Branches --- *)

  Lemma dec_noCanProceed :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      decode_canProceed decodeCapacity (iDecodeA s1) = false ->
      s1' = s1.
  Proof.
    intros s1 s1' H Hcp.
    dec_open H. dec_canProceed H.
    apply fw_ifFalse in H; [| exact Hcp]. dec_ret H.
    destruct H as [<- _]; reflexivity.
  Qed.

  Lemma dec_noHead :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      decode_canProceed decodeCapacity (iDecodeA s1) = true ->
      (dHead s1).(Snd).(Fst) = false ->
      DecStutter s1 s1'.
  Proof.
    intros s1 s1' H Hcp Hv.
    dec_prefix H Hcp.
    apply fw_ifFalse in H; [| exact Hv]. dec_ret H.
    destruct H as [<- _]; unfold DecStutter; repeat split; reflexivity.
  Qed.

  Lemma dec_stale :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      decode_canProceed decodeCapacity (iDecodeA s1) = true ->
      (dHead s1).(Snd).(Fst) = true ->
      aiLiveA s1 (dA s1) = false ->
      iRfA s1' = iRfA s1 /\ iWbA s1' = iWbA s1 /\ iMemA s1' = iMemA s1 /\
      iFetchA s1' = fetch_withInstFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) (fifoDeqState (IBF s1)) /\
      D2AF s1' = D2AF s1 /\ iExecA s1' = iExecA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1.
  Proof.
    intros s1 s1' H Hcp Hv Hst.
    dec_prefix H Hcp.
    apply fw_ifTrue in H; [| exact Hv].
    apply fw_ifTrue in H; [| change (negb (aiLiveA s1 (dA s1)) = true); rewrite Hst; reflexivity].
    dec_deqLast H. dec_ret H.
    destruct H as [<- _]; repeat split; reflexivity.
  Qed.

  Lemma dec_stall :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      decode_canProceed decodeCapacity (iDecodeA s1) = true ->
      (dHead s1).(Snd).(Fst) = true ->
      aiLiveA s1 (dA s1) = true ->
      dCanIssue s1 = false ->
      DecStutter s1 s1'.
  Proof.
    intros s1 s1' H Hcp Hv Hlive Hci.
    dec_prefix H Hcp.
    apply fw_ifTrue in H; [| exact Hv].
    apply fw_ifFalse in H; [| change (negb (aiLiveA s1 (dA s1)) = false); rewrite Hlive; reflexivity].
    dec_lets H.
    apply fw_ifFalse in H; [| subst rri; exact Hci].
    dec_ret H.
    destruct H as [<- _]; unfold DecStutter; repeat split; reflexivity.
  Qed.

  Lemma dec_issue :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      decode_canProceed decodeCapacity (iDecodeA s1) = true ->
      (dHead s1).(Snd).(Fst) = true ->
      aiLiveA s1 (dA s1) = true ->
      dCanIssue s1 = true ->
      iRfA s1' = iRfA s1 /\
      iWbA s1' = evalSetDstWaitBits (decWritesCd (dFo s1)) (instCd (foInst (dFo s1))) true (iWbA s1) /\
      iMemA s1' = iMemA s1 /\
      iFetchA s1' = fetch_withInstFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) (fifoDeqState (IBF s1)) /\
      D2AF s1' = fifoEnqState (D2AF s1) (dEntry s1) /\
      iExecA s1' = iExecA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1.
  Proof.
    intros s1 s1' H Hcp Hv Hlive Hci.
    dec_prefix H Hcp.
    apply fw_ifTrue in H; [| exact Hv].
    apply fw_ifFalse in H; [| change (negb (aiLiveA s1 (dA s1)) = false); rewrite Hlive; reflexivity].
    dec_lets H.
    apply fw_ifTrue in H; [| subst rri; exact Hci].
    dec_setCp H. dec_deq H. dec_lets H. dec_wb H. dec_lets H. dec_enqLast H. dec_ret H.
    destruct H as [<- _]; subst rri; repeat split; reflexivity.
  Qed.

End DecodeImpl.
