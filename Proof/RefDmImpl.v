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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker RefExecImpl.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 5: THE IMPL SIDE OF THE DATAMEM WRITE-BACK STAGES
 * ===========================================================================
 * - `getDeqRevDm_char`: dataMem's rev-bit response read on the impl memory subtree.
 * - `DmWbStep s1 s1' d v`: what a dataMem write-back step does (register `d` gets `v`, its wait
 *   bit is cleared, the memory `state` goes Idle, dataMem's state goes LoadRq).
 * - `revRpStage_char`: `revRpAndWriteBackStage` stutters or is a `DmWbStep`. *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma evalExpr_Var' : forall k (x : type k), evalExpr (Var type k x) = x.
Proof. reflexivity. Qed.

Ltac dm_cbn H :=
  cbn -[evalExpr evalLetExpr toAction implMemDeqRp revBitOfVal writeGprVal] in H.

Lemma dmLoadRq_excl3 :
  forall st, dmLoadRq st = true -> dmLoadRp st = false /\ dmRevRq st = false /\ dmRevRp st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma msReadRpReady_excl2 :
  forall st, msReadRpReady st = true -> msReadRq st = false /\ msReadRqSent st = false.
Proof.
  intros [d tg]; unfold msReadRq, msReadRqSent, msReadRpReady; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; split; reflexivity.
Qed.

Lemma dmRevRp_excl3 :
  forall st, dmRevRp st = true -> dmLoadRq st = false /\ dmLoadRp st = false /\ dmRevRq st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma dmRevRq_excl3 :
  forall st, dmRevRq st = true -> dmLoadRq st = false /\ dmLoadRp st = false /\ dmRevRp st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma dmLoadRp_excl3 :
  forall st, dmLoadRp st = true -> dmLoadRq st = false /\ dmRevRq st = false /\ dmRevRp st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma msIdle_excl2 :
  forall st, msIdle st = true ->
    msReadRq st = false /\ msReadRqSent st = false /\ msReadRpReady st = false /\ msWriteRq st = false.
Proof.
  intros [d tg]; unfold msIdle, msReadRq, msReadRqSent, msReadRpReady, msWriteRq; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

(* --- 1. The Rev-Bit Response on the Memory Subtree --- *)

Definition memIdleV : type MemState := evalExpr (UNION (MemStateList, "Idle" ::= ($0 : Expr type (Bit 0)))).

Lemma msIdle_idleV : msIdle memIdleV = true.
Proof. reflexivity. Qed.

Lemma getDeqRevDm_char :
  forall config regions env base (m m' : TS (implMemTree regions)) r,
    SemAction env (@implGetDeqRevBitRpFor config regions type ReqDataMem base) m m' r ->
    (andb (msReadRpReady m.(Snd).(Fst)) (isReqDataMem m.(Snd).(Snd).(Fst)) = false /\ m' = m /\ optValid r = false) \/
    (msReadRpReady m.(Snd).(Fst) = true /\ isReqDataMem m.(Snd).(Snd).(Fst) = true /\
     m' = (m.(Fst) ,, (memIdleV ,, m.(Snd).(Snd))) /\
     r = (revBitOfVal config base (msReadRpReadyV m.(Snd).(Fst)) ,, (true ,, tt))).
Proof.
  intros config regions env base [mr [mst [mrq [mrp []]]]] m' r H; cbn [Fst Snd].
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implGetDeqRevBitRpFor, implMemReadRp in H; cbn [evalActionPropGen] in H.
  apply evalActionPropGen_toAction in H; dm_cbn H; rewrite ?evalExpr_Var' in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Erp end.
  - match type of H with context [if ?c then _ else _] => destruct c eqn:Ev end.
    2: { exfalso; cbn in Ev; discriminate Ev. }
    assert (Hr : andb (msReadRpReady mst) (isReqDataMem mrq) = true) by exact Erp.
    apply andb_prop in Hr as [Hr1 Hr2].
    unfold implMemDeqRp in H; dm_cbn H; rewrite ?evalExpr_Var' in H.
    destruct H as [H1 H2]; subst m' r.
    right; split; [exact Hr1 | split; [exact Hr2 | split; reflexivity]].
  - match type of H with context [if ?c then _ else _] => destruct c eqn:Ev end.
    { exfalso; cbn in Ev; discriminate Ev. }
    destruct H as [H1 H2]; subst m' r.
    left; split; [exact Erp | split; reflexivity].
Qed.

Lemma readRevBitRqDm_char :
  forall config regions env base (m m' : TS (implMemTree regions)) r,
    SemAction env (@implReadRevBitRqFor config regions type ReqDataMem base) m m' r ->
    (andb (msIdle m.(Snd).(Fst)) (noPortWriteB regions m.(Fst)) = false /\ m' = m /\ r = false) \/
    (msIdle m.(Snd).(Fst) = true /\ noPortWriteB regions m.(Fst) = true /\ r = true /\
     exists st' rq', m' = (m.(Fst) ,, (st' ,, (rq' ,, m.(Snd).(Snd).(Snd)))) /\ msReadRq st' = true /\
       msReadRqV st' = stepOf false (revByteAddrOf config base) byteSz (getDefault CapPacket) /\
       isReqDataMem rq' = true).
Proof.
  intros config regions env base [mr [mst [mrq [mrp []]]]] m' r H; cbn [Fst Snd].
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implReadRevBitRqFor, implMemReadRq, implMemNoPortWriteRq in H.
  cbn [evalActionPropGen] in H.
  apply evalActionPropGen_toAction in H; dm_cbn H.
  apply noPortWrite_wp in H; dm_cbn H; rewrite ?evalExpr_Var' in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Erdy end.
  2: { left; destruct H as [H1 H2]; subst m' r; split; [exact Erdy | split; reflexivity]. }
  assert (Hr : andb (msIdle mst) (noPortWriteB regions mr) = true) by exact Erdy.
  apply andb_prop in Hr as [Hi Hn].
  destruct H as [H1 H2]; subst m' r.
  right; split; [exact Hi | split; [exact Hn | split; [reflexivity |]]].
  do 2 eexists; split; [reflexivity |].
  split; [reflexivity |]; split; [| reflexivity].
  rewrite msReadRqV_build; reflexivity.
Qed.

Lemma memReadRpDm_char :
  forall regions env (m m' : TS (implMemTree regions)) r,
    SemAction env (@implMemReadRp regions type ReqDataMem) m m' r ->
    m' = m /\ optValid r = andb (msReadRpReady m.(Snd).(Fst)) (isReqDataMem m.(Snd).(Snd).(Fst)) /\
    optData r = (if andb (msReadRpReady m.(Snd).(Fst)) (isReqDataMem m.(Snd).(Snd).(Fst))
                 then msReadRpReadyV m.(Snd).(Fst) else getDefault FullCapWithTag).
Proof.
  intros regions env [mr [mst [mrq [mrp []]]]] m' r H; cbn [Fst Snd].
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implMemReadRp in H; cbn [evalActionPropGen] in H; dm_cbn H; rewrite ?evalExpr_Var' in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Erp end;
    destruct H as [H1 H2]; subst m' r; (split; [reflexivity |]);
    (match type of Erp with ?L = _ =>
       assert (Hr : andb (msReadRpReady mst) (isReqDataMem mrq) = L) by reflexivity end);
    rewrite Hr, Erp; split; reflexivity.
Qed.

Lemma memDeqRp_char :
  forall regions env (m m' : TS (implMemTree regions)) r,
    SemAction env (@implMemDeqRp regions type) m m' r -> m' = (m.(Fst) ,, (memIdleV ,, m.(Snd).(Snd))).
Proof.
  intros regions env [mr [mst [mrq [mrp []]]]] m' r H; cbn [Fst Snd].
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implMemDeqRp in H; cbn [evalActionPropGen] in H; dm_cbn H.
  destruct H as [H1 _]; subst m'; reflexivity.
Qed.

(* --- 2. The Write-Back Step --- *)

Section DmImpl.
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

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA :=
    (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
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
  Local Abbreviation iDmStA :=
    (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  (* Register `d`'s wait bit cleared (x0 has none) *)
  Definition wbClr (d : bits RegIdxSzReal) (wb : TS waitBitsTree) : TS waitBitsTree :=
    if negb (Zmod.eqb d Zmod.zero) then evalWriteWaitBit d false wb else wb.

  (* A dataMem write-back step: register `d` gets `v`, its wait bit is cleared, the memory
   * `state` goes Idle and dataMem's state goes LoadRq; nothing else the relation reads changes *)
  Record DmWbStep (s1 s1' : IState) (d : bits RegIdxSzReal) (v : type FullECapWithTag) : Prop := {
    dw_rf    : iRfA s1' = writeGprVal pcAddrInit d v (iRfA s1) ;
    dw_wb    : iWbA s1' = wbClr d (iWbA s1) ;
    dw_reg   : iRegionsA s1' = iRegionsA s1 ;
    dw_rq    : iRequesterA s1' = iRequesterA s1 ;
    dw_rp    : iReadRpA s1' = iReadRpA s1 ;
    dw_idle  : msIdle (iMemStA s1') = true ;
    dw_fetch : iFetchA s1' = iFetchA s1 ;
    dw_dec   : iDecodeA s1' = iDecodeA s1 ;
    dw_exec  : iExecA s1' = iExecA s1 ;
    dw_md    : iMdA s1' = iMdA s1 ;
    dw_dmf   : dataMem_fifo dataMemCapacity (iDmA s1') = dataMem_fifo dataMemCapacity (iDmA s1) ;
    dw_dmst  : dmLoadRq (iDmStA s1') = true
  }.

  (* The register write of a rev-bit response `res` for command `rc` *)
  Definition revWbVal (rc : type RevCmd) (res : type FullCapWithTag) : bits RegIdxSzReal * type FullECapWithTag :=
    let pr : type PendingRev := evalExpr (##rc`"pendingRev") in
    let wb := evalLetExpr (dispatchRevResponse pr (revBitOfVal config (evalExpr (##rc`"base")) res)) in
    (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal")).

  Local Abbreviation iMemA :=
    (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation NPCORE :=
    (Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPMEM :=
    (ImplDataMem.np_mem dataMemCapacity pcAddrInit (withInst_BpTree bp)
       (implFetchTree pcAddrInit fetchCapacity instCapacity) (implDecodeTree decodeCapacity)
       (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)
       (fun ty => implExecuteIfc ty) (fun ty => implMemIfc config implRegions revI) type).

  Local Abbreviation NPDM :=
    (ImplDataMem.np_dataMem dataMemCapacity pcAddrInit (withInst_BpTree bp)
       (implFetchTree pcAddrInit fetchCapacity instCapacity) (implDecodeTree decodeCapacity)
       (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)
       (fun ty => implExecuteIfc ty) (fun ty => implMemIfc config implRegions revI) type).

  Local Abbreviation FT := (implFetchTree pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation DT := (implDecodeTree decodeCapacity).
  Local Abbreviation MDT := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation EIFC := (fun ty => @implExecuteIfc ty).
  Local Abbreviation MIFC := (fun ty => @implMemIfc config implRegions ty revI).

  Lemma commitWb_here :
    forall env d v c P,
      evalActionPropGen env
        (@ImplDataMem.commitWb dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC type d v) c P ->
      P (evalCommitWb dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC d v c) Zmod.zero.
  Proof.
    intros env d v c P H.
    exact (proj1 (@evalActionPropGen_commitWb dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC env d v c P) H).
  Qed.

  Definition dmLoadRqV : type DataMemState :=
    evalExpr (UNION (DataMemStateList, "LoadRq" ::= ($0 : Expr type (Bit 0)))).

  Local Abbreviation ECW := (evalCommitWb dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC).

  (* The state after a dataMem write-back: the memory `state` Idle, `commitWb`, dataMem LoadRq *)
  Lemma dmWb_final :
    forall (s1 s1' : IState) d v,
      writeSubTreeState NPCORE s1
        (writeSubTreeState NPDM
           (ECW d v (writeSubTreeState NPMEM (readSubTreeState NPCORE s1)
                       (Fst (iMemA s1) ,, (memIdleV ,, Snd (Snd (iMemA s1))))))
           (writeTreeState (getNode NPDM)
              (readSubTreeState NPDM
                 (ECW d v (writeSubTreeState NPMEM (readSubTreeState NPCORE s1)
                             (Fst (iMemA s1) ,, (memIdleV ,, Snd (Snd (iMemA s1)))))))
              (regPath (pState dataMemCapacity))
              (castStateRegInv (pState dataMemCapacity) dmLoadRqV))) = s1' ->
      DmWbStep s1 s1' d v.
  Proof.
    intros s1 s1' d v <-.
    unfold evalCommitWb; destruct (negb (Zmod.eqb d Zmod.zero)) eqn:Ez;
      (constructor; [unfold writeGprVal, wbClr; rewrite Ez; reflexivity
                    | unfold writeGprVal, wbClr; rewrite Ez; reflexivity | ..]); reflexivity.
  Qed.

  Local Abbreviation REVRP :=
    (@revRpAndWriteBackStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

  Lemma revRpStage_char :
    forall env (s1 s1' : IState) r,
      SemAction env REVRP s1 s1' r ->
      s1' = s1 \/
      (dmRevRp (iDmStA s1) = true /\ msReadRpReady (iMemStA s1) = true /\ isReqDataMem (iRequesterA s1) = true /\
       DmWbStep s1 s1' (fst (revWbVal (dmRevRpV (iDmStA s1)) (msReadRpReadyV (iMemStA s1))))
                       (snd (revWbVal (dmRevRpV (iDmStA s1)) (msReadRpReadyV (iMemStA s1))))).
  Proof.
    intros env s1 s1' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold revRpAndWriteBackStage in H; rewrite evalActionPropGen_liftAction in H.
    unfold revRpAndWriteBack in H.
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readState _ _ _) HQ_)];
      cbv beta in H.
    change (dm_state dataMemCapacity (readSubTreeState NPDM (readSubTreeState NPCORE s1))) with (iDmStA s1) in H.
    apply fw_ifTF in H as [[Hc H] | [Hc H]].
    2: { left; cbn [evalActionPropGen] in H; destruct H as [H _].
         rewrite writeSubTreeState_readSubTreeState in H; symmetry; exact H. }
    assert (Hrv : dmRevRp (iDmStA s1) = true) by exact Hc; clear Hc.
    do 3 (apply fw_letExp in H).
    apply fw_liftSem in H as [sm' [rb [Hm H]]].
    cbn [mem_getDeqRevBitRp implMemIfc] in Hm.
    apply getDeqRevDm_char in Hm.
    change (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) with (iMemA s1) in Hm, H.
    change (Fst (Snd (iMemA s1))) with (iMemStA s1) in Hm.
    change (Fst (Snd (Snd (iMemA s1)))) with (iRequesterA s1) in Hm.
    destruct Hm as [[Hn [-> Hv]] | [Hr1 [Hr2 [-> ->]]]].
    - left.
      apply fw_ifFalse in H; [| exact Hv].
      cbn [evalActionPropGen] in H; destruct H as [H _].
      change (iMemA s1) with (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) in H.
      rewrite !writeSubTreeState_readSubTreeState in H; symmetry; exact H.
    - right; split; [exact Hrv | split; [exact Hr1 | split; [exact Hr2 |]]].
      apply fw_ifTrue in H; [| reflexivity].
      apply fw_letExp in H; apply fw_letL in H; do 3 (apply fw_letExp in H).
      apply fw_letAction in H; timeout 10 (apply commitWb_here in H); cbv beta in H.
      rewrite evalActionPropGen_liftAction in H; unfold writeState in H; cbn [evalActionPropGen] in H.
      cbn [evalActionPropGen] in H; destruct H as [H _].
      exact (dmWb_final s1 s1' _ _ H).
  Qed.
  (* Nothing the relation reads changes but the memory `state`, the requester and dataMem's state *)
  Record DmFrame (s1 s1' : IState) : Prop := {
    df_rf    : iRfA s1' = iRfA s1 ;
    df_wb    : iWbA s1' = iWbA s1 ;
    df_reg   : iRegionsA s1' = iRegionsA s1 ;
    df_rp    : iReadRpA s1' = iReadRpA s1 ;
    df_fetch : iFetchA s1' = iFetchA s1 ;
    df_dec   : iDecodeA s1' = iDecodeA s1 ;
    df_exec  : iExecA s1' = iExecA s1 ;
    df_md    : iMdA s1' = iMdA s1 ;
    df_dmf   : dataMem_fifo dataMemCapacity (iDmA s1') = dataMem_fifo dataMemCapacity (iDmA s1)
  }.

  (* dataMem hands the rev-bit read of command `rc` to the memory *)
  Definition IssueStep (s1 s1' : IState) (rc : type RevCmd) : Prop :=
    DmFrame s1 s1' /\ msReadRq (iMemStA s1') = true /\
    msReadRqV (iMemStA s1') = stepOf false (revByteAddrOf config (rcBase rc)) byteSz (getDefault CapPacket) /\
    isReqDataMem (iRequesterA s1') = true /\ dmRevRp (iDmStA s1') = true /\ dmRevRpV (iDmStA s1') = rc.

  Local Abbreviation ISSUE :=
    (@issueRevRq dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC type).

  Definition dmRevRpOf (rc : type RevCmd) : type DataMemState :=
    evalExpr (UNION (DataMemStateList, "RevRp" ::= Var type RevCmd rc)).

  Lemma dmRevRpOf_facts : forall rc, dmRevRp (dmRevRpOf rc) = true /\ dmRevRpV (dmRevRpOf rc) = rc.
  Proof.
    intros rc; split; [reflexivity |].
    exact (evalExpr_ReadUnionData_BuildUnion DataMemStateList (@Build_FinType (length DataMemStateList) 3 I)
             (Var type RevCmd rc) eq_refl).
  Qed.

  Lemma issueRevRq_char :
    forall cenv (s1 : IState) c' r,
      SemAction cenv ISSUE (readSubTreeState NPCORE s1) c' r ->
      writeSubTreeState NPCORE s1 c' = s1 \/
      (dmRevRq (iDmStA s1) = true /\ msIdle (iMemStA s1) = true /\ noPortWriteB implRegions (iRegionsA s1) = true /\
       IssueStep s1 (writeSubTreeState NPCORE s1 c') (dmRevRqV (iDmStA s1))).
  Proof.
    intros cenv s1 c' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold issueRevRq in H.
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readState _ _ _) HQ_)];
      cbv beta in H.
    change (dm_state dataMemCapacity (readSubTreeState NPDM (readSubTreeState NPCORE s1))) with (iDmStA s1) in H.
    apply fw_ifTF in H as [[Hc H] | [Hc H]].
    2: { left; cbn [evalActionPropGen] in H; destruct H as [H _]; subst c'.
         apply writeSubTreeState_readSubTreeState. }
    assert (Hrq : dmRevRq (iDmStA s1) = true) by exact Hc; clear Hc.
    do 2 (apply fw_letExp in H).
    apply fw_liftSem in H as [sm' [acc [Hm H]]].
    cbn [mem_readRevBitRq implMemIfc] in Hm.
    apply readRevBitRqDm_char in Hm.
    change (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) with (iMemA s1) in Hm, H.
    change (Fst (Snd (iMemA s1))) with (iMemStA s1) in Hm.
    change (Fst (iMemA s1)) with (iRegionsA s1) in Hm.
    destruct Hm as [[Hn [-> ->]] | [Hi [Hnp [-> [st' [rq' [-> [Hst1 [Hst2 Hrq']]]]]]]]].
    - left.
      apply fw_ifFalse in H; [| reflexivity].
      cbn [evalActionPropGen] in H; destruct H as [H _]; subst c'.
      change (iMemA s1) with (readSubTreeState NPMEM (readSubTreeState NPCORE s1)).
      rewrite !writeSubTreeState_readSubTreeState; reflexivity.
    - right; split; [exact Hrq | split; [exact Hi | split; [exact Hnp |]]].
      apply fw_ifTrue in H; [| reflexivity].
      apply fw_letExp in H.
      rewrite evalActionPropGen_liftAction in H; unfold writeState in H; cbn [evalActionPropGen] in H.
      destruct H as [H _]; subst c'.
      destruct (dmRevRpOf_facts (dmRevRqV (iDmStA s1))) as [F1 F2].
      split; [constructor; reflexivity |].
      split; [exact Hst1 | split; [exact Hst2 | split; [exact Hrq' | split; [exact F1 | exact F2]]]].
  Qed.

  (* The outcome of a load response *)
  Definition outIsRev (out : type LoadOutcome) : bool := evalExpr ((Var type LoadOutcome out) `? "RevLookup").
  Definition outRevV (out : type LoadOutcome) : type RevCmd := evalExpr ((Var type LoadOutcome out) `! "RevLookup").
  Definition outWb (out : type LoadOutcome) : bits RegIdxSzReal * type FullECapWithTag :=
    let wb : type WbCmd := evalExpr ((Var type LoadOutcome out) `! "Writeback") in
    (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal")).

  (* dataMem takes a load response that needs a rev-bit lookup for command `rc` *)
  Definition RevRqStep (s1 s1' : IState) (rc : type RevCmd) : Prop :=
    DmFrame s1 s1' /\ iRequesterA s1' = iRequesterA s1 /\ msIdle (iMemStA s1') = true /\
    dmRevRq (iDmStA s1') = true /\ dmRevRqV (iDmStA s1') = rc.

  Definition dmRevRqOf (rc : type RevCmd) : type DataMemState :=
    evalExpr (UNION (DataMemStateList, "RevRq" ::= Var type RevCmd rc)).

  Lemma dmRevRqOf_facts : forall rc, dmRevRq (dmRevRqOf rc) = true /\ dmRevRqV (dmRevRqOf rc) = rc.
  Proof.
    intros rc; split; [reflexivity |].
    exact (evalExpr_ReadUnionData_BuildUnion DataMemStateList (@Build_FinType (length DataMemStateList) 2 I)
             (Var type RevCmd rc) eq_refl).
  Qed.

  Local Abbreviation LOADRP :=
    (@loadRpAndWriteback dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC type config).

  Lemma loadRpWb_char :
    forall cenv (s1 : IState) c' r,
      SemAction cenv LOADRP (readSubTreeState NPCORE s1) c' r ->
      writeSubTreeState NPCORE s1 c' = s1 \/
      (dmLoadRp (iDmStA s1) = true /\ msReadRpReady (iMemStA s1) = true /\ isReqDataMem (iRequesterA s1) = true /\
       let out := evalLetExpr (dispatchLoadResponse config (ldPending (dmLoadRpV (iDmStA s1))) (msReadRpReadyV (iMemStA s1))) in
       ((outIsRev out = true /\ RevRqStep s1 (writeSubTreeState NPCORE s1 c') (outRevV out)) \/
        (outIsRev out = false /\ DmWbStep s1 (writeSubTreeState NPCORE s1 c') (fst (outWb out)) (snd (outWb out))))).
  Proof.
    intros cenv s1 c' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold loadRpAndWriteback in H.
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readState _ _ _) HQ_)];
      cbv beta in H.
    change (dm_state dataMemCapacity (readSubTreeState NPDM (readSubTreeState NPCORE s1))) with (iDmStA s1) in H.
    apply fw_ifTF in H as [[Hc H] | [Hc H]].
    2: { left; cbn [evalActionPropGen] in H; destruct H as [H _]; subst c'.
         apply writeSubTreeState_readSubTreeState. }
    assert (Hlrp : dmLoadRp (iDmStA s1) = true) by exact Hc; clear Hc.
    do 2 (apply fw_letExp in H).
    apply fw_liftSem in H as [sm' [mv [Hm H]]].
    cbn [mem_getMemRp implMemIfc] in Hm.
    apply memReadRpDm_char in Hm.
    change (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) with (iMemA s1) in Hm, H.
    change (Fst (Snd (iMemA s1))) with (iMemStA s1) in Hm.
    change (Fst (Snd (Snd (iMemA s1)))) with (iRequesterA s1) in Hm.
    destruct Hm as [-> [Hv Hd]].
    change (iMemA s1) with (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) in H at 1.
    rewrite writeSubTreeState_readSubTreeState in H.
    destruct (andb (msReadRpReady (iMemStA s1)) (isReqDataMem (iRequesterA s1))) eqn:Erp.
    2: { left; apply fw_ifFalse in H; [| exact Hv].
         cbn [evalActionPropGen] in H; destruct H as [H _]; subst c'.
         apply writeSubTreeState_readSubTreeState. }
    apply andb_prop in Erp as [Hr1 Hr2].
    right; split; [exact Hlrp | split; [exact Hr1 | split; [exact Hr2 |]]].
    apply fw_ifTrue in H; [| exact Hv].
    apply fw_liftSem in H as [sm2 [rd [Hdq H]]].
    cbn [mem_deqMemRp implMemIfc] in Hdq; apply memDeqRp_char in Hdq; subst sm2.
    cbv iota in Hd.
    apply fw_letExp in H.
    apply fw_letLGen in H as [out [Eout H]].
    match type of Eout with _ = evalLetExpr (dispatchLoadResponse _ ?pl ?mvx) =>
      assert (Epl : pl = ldPending (dmLoadRpV (iDmStA s1))) by reflexivity; rewrite Epl in Eout;
      assert (Emv : mvx = msReadRpReadyV (iMemStA s1)) by (rewrite <- Hd; reflexivity); rewrite Emv in Eout
    end.
    cbv zeta; rewrite <- Eout.
    apply fw_ifTF in H as [[Hc H] | [Hc H]].
    - left; split; [exact Hc |].
      do 2 (apply fw_letExp in H).
      rewrite evalActionPropGen_liftAction in H; unfold writeState in H; cbn [evalActionPropGen] in H.
      destruct H as [H _]; subst c'.
      split; [constructor; reflexivity |].
      split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
      exact (proj2 (dmRevRqOf_facts (outRevV out))).
    - right; split; [exact Hc |].
      do 4 (apply fw_letExp in H).
      apply fw_letAction in H; timeout 10 (apply commitWb_here in H); cbv beta in H.
      rewrite evalActionPropGen_liftAction in H; unfold writeState in H; cbn [evalActionPropGen] in H.
      destruct H as [H _]; rewrite <- H.
      exact (dmWb_final s1 _ _ _ eq_refl).
  Qed.

End DmImpl.
