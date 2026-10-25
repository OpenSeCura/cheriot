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
From Cheriot Require Export SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Export Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Export TreeLemmas StateRel SimExecute.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. `implDataMemTree` STATE ACCESSORS & ACTION EVALUATION LEMMAS
 * =========================================================================== *)

Section DataMemTreeHelpers.
  Variable dom : string.
  Variable capacity : nat.

  Local Abbreviation dmTree := (implDataMemTree dom capacity).
  Local Abbreviation fTree := (fifoTree dom capacity MemFenceReq).

  Definition dm_inputFifo (dm : TreeState DomainElemState dmTree)
    : TreeState DomainElemState fTree :=
    dm.(Fst).(Fst).

  Definition dm_state (dm : TreeState DomainElemState dmTree)
    : type DataMemState :=
    dm.(Snd).(Fst).

  Definition dm_withInputFifo (dm : TreeState DomainElemState dmTree)
    (f : TreeState DomainElemState fTree) : TreeState DomainElemState dmTree :=
    ((f ,, dm.(Fst).(Snd)) ,, dm.(Snd)).

  Definition dm_withState (dm : TreeState DomainElemState dmTree)
    (st : type DataMemState) : TreeState DomainElemState dmTree :=
    (dm.(Fst) ,, (st ,, dm.(Snd).(Snd))).

  Lemma dm_inputFifo_withInputFifo :
    forall dm f, dm_inputFifo (dm_withInputFifo dm f) = f.
  Proof. reflexivity. Qed.

  Lemma dm_inputFifo_withState :
    forall dm st, dm_inputFifo (dm_withState dm st) = dm_inputFifo dm.
  Proof. reflexivity. Qed.

  Lemma dm_state_withInputFifo :
    forall dm f, dm_state (dm_withInputFifo dm f) = dm_state dm.
  Proof. reflexivity. Qed.

  Lemma dm_state_withState :
    forall dm st, dm_state (dm_withState dm st) = st.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readState :
    forall {env : Env dmTree} (dm : TreeState DomainElemState dmTree) P,
      evalActionPropGen env (@readState dom capacity type) dm P <->
      P dm (dm_state dm).
  Proof.
    intros env dm P; reflexivity.
  Qed.

  Lemma evalActionPropGen_writeState :
    forall {env : Env dmTree} (val : type DataMemState) (dm : TreeState DomainElemState dmTree) P,
      evalActionPropGen env (@writeState dom capacity type val) dm P <->
      P (dm_withState dm val) Zmod.zero.
  Proof.
    intros env val dm P; reflexivity.
  Qed.

  Lemma evalActionPropGen_dataMemIsEmpty :
    forall {env : Env dmTree} (dm : TreeState DomainElemState dmTree) P,
      evalActionPropGen env (@dataMemIsEmpty dom capacity type) dm P <->
      evalActionPropGen (subEnv (np_dmInputFifo dom capacity) env dm)
        (@isEmpty dom capacity MemFenceReq type) (dm_inputFifo dm)
        (fun f' inEmpty =>
           P (dm_withInputFifo dm f')
             (andb inEmpty (Zmod.eqb ((dm_state dm).(Snd)) Zmod.zero))).
  Proof.
    intros env dm P.
    unfold dataMemIsEmpty.
    cbn [evalActionPropGen].
    rewrite (evalActionPropGen_liftAction (np_dmInputFifo dom capacity)).
    eapply evalActionPropGen_ext; intros f' inEmpty.
    cbn [evalActionPropGen evalExpr].
    reflexivity.
  Qed.

  Lemma evalActionPropGen_dataMemIsFull :
    forall {env : Env dmTree} (dm : TreeState DomainElemState dmTree) P,
      evalActionPropGen env (@dataMemIsFull dom capacity type) dm P <->
      evalActionPropGen (subEnv (np_dmInputFifo dom capacity) env dm)
        (@isFull dom capacity MemFenceReq type) (dm_inputFifo dm)
        (fun f' res => P (dm_withInputFifo dm f') res).
  Proof.
    intros env dm P.
    unfold dataMemIsFull.
    rewrite (evalActionPropGen_liftAction (np_dmInputFifo dom capacity)).
    reflexivity.
  Qed.

  Lemma evalActionPropGen_dataMemEnq :
    forall {env : Env dmTree}
           (dstIdx : bits RegIdxSzReal) (addr : type Addr) (op : type MemFenceUnion)
           (dm : TreeState DomainElemState dmTree) P,
      evalActionPropGen env (@dataMemEnq dom capacity type dstIdx addr op) dm P <->
      let req : type MemFenceReq := (dstIdx ,, (addr ,, (op ,, tt))) in
      evalActionPropGen (subEnv (np_dmInputFifo dom capacity) env dm)
        (@enq dom capacity MemFenceReq type req) (dm_inputFifo dm)
        (fun f' res => P (dm_withInputFifo dm f') res).
  Proof.
    intros env dstIdx addr op dm P.
    unfold dataMemEnq.
    cbn [evalActionPropGen evalExpr].
    rewrite (evalActionPropGen_liftAction (np_dmInputFifo dom capacity)).
    reflexivity.
  Qed.

End DataMemTreeHelpers.

(* ===========================================================================
 * 2. `ImplDataMem` CORE WRITEBACK & STAGE FRAME LEMMAS
 * =========================================================================== *)

Section DataMemCoreLemmas.
  Variable dom : string.
  Variable capacity : nat.
  Variable pcAddrInit : Z.
  Variable bpT fetchT decodeT mulDivT : Tree DomainElem.
  Variable executeIfc : forall ty, @ExecuteIfc ty.
  Variable memIfc : forall ty, @MemIfc ty.

  Local Abbreviation rTree := (rfTree dom pcAddrInit).
  Local Abbreviation mTree := (memIfc type).(memTree).
  Local Abbreviation eTree := (executeIfc type).(executeTree).
  Local Abbreviation dmTree := (implDataMemTree dom capacity).
  Local Abbreviation cTree := (coreTree dom rTree bpT mTree fetchT decodeT eTree dmTree mulDivT).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  Definition dmCore_rf (c : TreeState DomainElemState cTree) : TreeState DomainElemState rTree :=
    c.(Fst).(Fst).

  Definition dmCore_waitBits (c : TreeState DomainElemState cTree) : TreeState DomainElemState (waitBitsTree dom) :=
    c.(Snd).(Fst).(Fst).

  Definition dmCore_bp (c : TreeState DomainElemState cTree) : TreeState DomainElemState bpT :=
    c.(Snd).(Snd).(Fst).(Fst).

  Definition dmCore_mem (c : TreeState DomainElemState cTree) : TreeState DomainElemState mTree :=
    c.(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition dmCore_fetch (c : TreeState DomainElemState cTree) : TreeState DomainElemState fetchT :=
    c.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition dmCore_decode (c : TreeState DomainElemState cTree) : TreeState DomainElemState decodeT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition dmCore_execute (c : TreeState DomainElemState cTree) : TreeState DomainElemState eTree :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition dmCore_dataMem (c : TreeState DomainElemState cTree) : TreeState DomainElemState dmTree :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition dmCore_mulDiv (c : TreeState DomainElemState cTree) : TreeState DomainElemState mulDivT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition evalCommitWb
    (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
    (c : TreeState DomainElemState cTree) : TreeState DomainElemState cTree :=
    if negb (Zmod.eqb dstIdx Zmod.zero)
    then
      ((evalWriteRegsList (gprPathsWithKind dom pcAddrInit) dstIdx dstVal (dmCore_rf c) ,, c.(Fst).(Snd)) ,,
       ((evalWriteRegsList (gprWaitPathsWithKind dom) dstIdx false (dmCore_waitBits c) ,, c.(Snd).(Fst).(Snd)) ,,
        c.(Snd).(Snd)))
    else c.

  Lemma evalActionPropGen_commitWb :
    forall {env : Env cTree}
           (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
           (c : TreeState DomainElemState cTree) P,
      evalActionPropGen env
        (@ImplDataMem.commitWb dom capacity pcAddrInit bpT fetchT decodeT mulDivT
                               executeIfc memIfc type dstIdx dstVal) c P <->
      P (evalCommitWb dstIdx dstVal c) Zmod.zero.
  Proof.
    intros env dstIdx dstVal c P.
    unfold ImplDataMem.commitWb, evalCommitWb.
    cbn [evalActionPropGen evalExpr isNotZero isZero evalNot isEq KindCustomInd getDefault].
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)) eqn:Hnz.
    - cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@ImplDataMem.np_rf dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)).
      rewrite (evalActionPropGen_writeRegsList (gprPathsWithKind dom pcAddrInit)
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type FullECapWithTag dstVal)).
      cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@ImplDataMem.np_waitBits dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)).
      unfold writeGprWaitBit.
      rewrite (evalActionPropGen_writeRegsList (gprWaitPathsWithKind dom)
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type Bool false)).
      cbn [evalActionPropGen evalExpr].
      reflexivity.
    - cbn [evalActionPropGen evalExpr]; reflexivity.
  Qed.

  Lemma evalCommitWb_frame :
    forall dstIdx dstVal (c : TreeState DomainElemState cTree),
      let c' := evalCommitWb dstIdx dstVal c in
      dmCore_bp c' = dmCore_bp c /\
      dmCore_mem c' = dmCore_mem c /\
      dmCore_fetch c' = dmCore_fetch c /\
      dmCore_decode c' = dmCore_decode c /\
      dmCore_execute c' = dmCore_execute c /\
      dmCore_dataMem c' = dmCore_dataMem c /\
      dmCore_mulDiv c' = dmCore_mulDiv c.
  Proof.
    intros dstIdx dstVal c.
    unfold evalCommitWb.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); repeat split; reflexivity.
  Qed.

  Theorem issueRevRq_core_frame :
    forall {env : Env cTree}
           (c c' : TreeState DomainElemState cTree) (res : type (Bit 0)),
      SemAction env
        (@issueRevRq dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)
        c c' res ->
      dmCore_rf c' = dmCore_rf c /\
      dmCore_waitBits c' = dmCore_waitBits c /\
      dmCore_bp c' = dmCore_bp c /\
      dmCore_fetch c' = dmCore_fetch c /\
      dmCore_decode c' = dmCore_decode c /\
      dmCore_execute c' = dmCore_execute c /\
      dmCore_mulDiv c' = dmCore_mulDiv c /\
      dm_inputFifo dom capacity (dmCore_dataMem c') = dm_inputFifo dom capacity (dmCore_dataMem c).
  Proof.
    intros env c c' res Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    unfold issueRevRq in Hsem.
    cbn [evalActionPropGen] in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@ImplDataMem.np_dataMem dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)) in Hsem.
    cbn [evalActionPropGen readState] in Hsem.
    lazymatch type of Hsem with
    | context[if ?b then _ else _] => destruct b
    end.
    - cbn [evalActionPropGen] in Hsem.
      rewrite (evalActionPropGen_liftAction
                 (@ImplDataMem.np_mem dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)) in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sm' [accepted [_ Hrest]]].
      cbn [evalActionPropGen evalExpr] in Hrest.
      destruct accepted.
      + cbn [evalActionPropGen] in Hrest.
        rewrite (evalActionPropGen_liftAction
                   (@ImplDataMem.np_dataMem dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)) in Hrest.
        cbn [evalActionPropGen writeState] in Hrest.
        destruct Hrest as [<- _]; repeat split; reflexivity.
      + cbn [evalActionPropGen] in Hrest.
        destruct Hrest as [<- _]; repeat split; reflexivity.
    - cbn [evalActionPropGen] in Hsem.
      destruct Hsem as [<- _]; repeat split; reflexivity.
  Qed.

  Theorem revRpAndWriteBack_core_frame :
    forall {env : Env cTree}
           (c c' : TreeState DomainElemState cTree) (res : type (Bit 0)),
      SemAction env
        (@revRpAndWriteBack dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)
        c c' res ->
      dmCore_bp c' = dmCore_bp c /\
      dmCore_fetch c' = dmCore_fetch c /\
      dmCore_decode c' = dmCore_decode c /\
      dmCore_execute c' = dmCore_execute c /\
      dmCore_mulDiv c' = dmCore_mulDiv c /\
      dm_inputFifo dom capacity (dmCore_dataMem c') = dm_inputFifo dom capacity (dmCore_dataMem c).
  Proof.
    intros env c c' res Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    unfold revRpAndWriteBack in Hsem.
    cbn [evalActionPropGen] in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@ImplDataMem.np_dataMem dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)) in Hsem.
    cbn [evalActionPropGen readState] in Hsem.
    lazymatch type of Hsem with
    | context[if ?b then _ else _] => destruct b
    end.
    - cbn [evalActionPropGen] in Hsem.
      rewrite (evalActionPropGen_liftAction
                 (@ImplDataMem.np_mem dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)) in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sm' [revBitOpt [_ Hrest]]].
      cbn [evalActionPropGen evalExpr readDiffTuple finNum Fst Snd] in Hrest.
      destruct (revBitOpt.(Snd).(Fst)).
      + cbn [evalActionPropGen] in Hrest.
        rewrite evalActionPropGen_toAction in Hrest.
        cbn [evalActionPropGen] in Hrest.
        rewrite evalActionPropGen_commitWb in Hrest.
        cbn [evalActionPropGen] in Hrest.
        rewrite (evalActionPropGen_liftAction
                   (@ImplDataMem.np_dataMem dom capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)) in Hrest.
        cbn [evalActionPropGen writeState] in Hrest.
        destruct Hrest as [<- _].
        unfold evalCommitWb.
        destruct (negb (Zmod.eqb _ Zmod.zero)); repeat split; reflexivity.
      + cbn [evalActionPropGen] in Hrest.
        destruct Hrest as [<- _]; repeat split; reflexivity.
    - cbn [evalActionPropGen] in Hsem.
      destruct Hsem as [<- _]; repeat split; reflexivity.
  Qed.

End DataMemCoreLemmas.

(* ===========================================================================
 * 3. SYSTEM-LEVEL SIMULATION FOR STAGE 5 (`ImplDataMem` & MEMORY ROUTING)
 * =========================================================================== *)

Section DataMemStageSimulation.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree core pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation SState := (SpecState core pcAddrInit regions).
  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
  Local Abbreviation specMod := (@spec core pcAddrInit config regions clint revSpec plic).
  Local Abbreviation cRel :=
    (CoreStateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions).
  Local Abbreviation sRel :=
    (stateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).

  Local Abbreviation rTree := (RfTree core pcAddrInit).
  Local Abbreviation bpT := BpTree.
  Local Abbreviation mTree := (ImplMemSubTree core regions).
  Local Abbreviation fTree := (FetchTree core pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (DecodeTree core decodeCapacity).
  Local Abbreviation eTree := (ExecuteTree core).
  Local Abbreviation dmTree := (DataMemTree core dataMemCapacity).
  Local Abbreviation mdTree := (MulDivSubTree core mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree core rTree bpT mTree fTree decTree eTree dmTree mdTree).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  (* --- 3A. `GhostList` Drain and In-Flight Transition Helpers --- *)

  Lemma GhostList_cons_inv_local :
    forall rf0 wm0 req reqs rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 (req :: reqs) rf2 wm2 ->
      exists rf1 wm1,
        GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req /\
        GhostList core pcAddrInit rf1 wm1 reqs rf2 wm2.
  Proof.
    intros rf0 wm0 req reqs rf2 wm2 Hgl.
    inversion Hgl; subst.
    eexists; eexists; split; eassumption.
  Qed.

  Lemma DataMemInFlightRel_LoadRq_inv_local :
    forall (sdm : DataMemSubState core dataMemCapacity)
           (rf_spec rf_after : RfState core pcAddrInit)
           (wm0 wm_after : bits RegIdxSzReal -> bool),
      isDataMemLoadRq core dataMemCapacity sdm = true ->
      DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
      rf_after = rf_spec /\ wm_after = wm0.
  Proof.
    intros sdm rf_spec rf_after wm0 wm_after Hrq Hrel.
    unfold DataMemInFlightRel in Hrel; rewrite Hrq in Hrel; exact Hrel.
  Qed.

  Lemma DataMemInFlightRel_NotLoadRq_inv_local :
    forall (sdm : DataMemSubState core dataMemCapacity)
           (rf_spec rf_after : RfState core pcAddrInit)
           (wm0 wm_after : bits RegIdxSzReal -> bool),
      isDataMemLoadRq core dataMemCapacity sdm = false ->
      DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
      exists req, GhostStep core pcAddrInit rf_spec rf_after wm0 wm_after req.
  Proof.
    intros sdm rf_spec rf_after wm0 wm_after Hrq Hrel.
    unfold DataMemInFlightRel in Hrel; rewrite Hrq in Hrel; exact Hrel.
  Qed.

  Theorem GhostList_drain_to_inflight_local :
    forall (sdm sdm' : DataMemSubState core dataMemCapacity)
           (rf_spec rf_after rf_impl : RfState core pcAddrInit)
           (wm0 wm_after wm_impl : bits RegIdxSzReal -> bool)
           (req : type MemFenceReq) (reqs : list (type MemFenceReq)),
      isDataMemLoadRq core dataMemCapacity sdm = true ->
      isDataMemLoadRq core dataMemCapacity sdm' = false ->
      DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
      GhostList core pcAddrInit rf_after wm_after (req :: reqs) rf_impl wm_impl ->
      exists rf_after' wm_after',
        GhostStep core pcAddrInit rf_spec rf_after' wm0 wm_after' req /\
        DataMemInFlightRel core pcAddrInit dataMemCapacity sdm' rf_spec rf_after' wm0 wm_after' /\
        GhostList core pcAddrInit rf_after' wm_after' reqs rf_impl wm_impl.
  Proof.
    intros sdm sdm' rf_spec rf_after rf_impl wm0 wm_after wm_impl req reqs Hrq HnotRq Hrel Hgl.
    destruct (DataMemInFlightRel_LoadRq_inv_local sdm rf_spec rf_after wm0 wm_after Hrq Hrel) as [-> ->].
    destruct (GhostList_cons_inv_local rf_spec wm0 req reqs rf_impl wm_impl Hgl)
      as [rf_after' [wm_after' [Hstep Hrest]]].
    exists rf_after', wm_after'.
    split; [exact Hstep | split; [| exact Hrest]].
    unfold DataMemInFlightRel; rewrite HnotRq; exists req; exact Hstep.
  Qed.

  (* --- 3B. `evalCommitWb` and Memory-Lifted Action Frame Lemmas --- *)

  Lemma dmCore_rf_evalCommitWb :
    forall (executeIfc : forall ty, @ExecuteIfc ty)
           (memIfc : forall ty, @MemIfc ty)
           dstIdx dstVal
           (c : TreeState DomainElemState
                  (coreTree core rTree bpT (memIfc type).(memTree) fTree decTree
                            (executeIfc type).(executeTree) dmTree mdTree)),
      dmCore_rf core dataMemCapacity pcAddrInit bpT fTree decTree mdTree executeIfc memIfc
        (evalCommitWb core dataMemCapacity pcAddrInit bpT fTree decTree mdTree executeIfc memIfc dstIdx dstVal c) =
      writeGprVal core pcAddrInit dstIdx dstVal
        (dmCore_rf core dataMemCapacity pcAddrInit bpT fTree decTree mdTree executeIfc memIfc c).
  Proof.
    intros executeIfc memIfc dstIdx dstVal c.
    unfold evalCommitWb, writeGprVal.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); reflexivity.
  Qed.

  Lemma SemAction_lift_np_mem_core_frame :
    forall {env1 : Env iTree} {k : Kind} (act : Action type mTree k)
           (s1 s1' : IState) (v : type k),
      SemAction env1
        (liftAction
           (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions)
           act)
        s1 s1' v ->
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 /\
      impl_waitBits core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1' =
        impl_waitBits core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1 /\
      impl_bp core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_bp core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1.
  Proof.
    intros env1 k act s1 s1' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem.
    destruct (evalActionPropGen_to_SemAction act _ _ Hsem) as [m' [v' [_ [<- _]]]].
    repeat split; reflexivity.
  Qed.

  Theorem dataReadRqs_frame :
    forall {env1 : Env iTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (v : bits 0),
      In act
        (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1.
  Proof.
    intros env1 act s1 s1' v Hin Hsem.
    unfold dataReadRqs in Hin.
    apply in_map_iff in Hin as [mAct [<- _]].
    destruct (SemAction_lift_np_mem_core_frame mAct s1 s1' v Hsem)
      as [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hdm Hmd]]]]]]].
    unfold flushMulDiv; rewrite Hrf, Hmd.
    repeat split; assumption.
  Qed.

  Theorem dataReadRps_frame :
    forall {env1 : Env iTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (v : bits 0),
      In act
        (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1.
  Proof.
    intros env1 act s1 s1' v Hin Hsem.
    unfold dataReadRps in Hin.
    apply in_map_iff in Hin as [mAct [<- _]].
    destruct (SemAction_lift_np_mem_core_frame mAct s1 s1' v Hsem)
      as [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hdm Hmd]]]]]]].
    unfold flushMulDiv; rewrite Hrf, Hmd.
    repeat split; assumption.
  Qed.

  Theorem dataWriteRqs_frame :
    forall {env1 : Env iTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (v : bits 0),
      In act
        (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1.
  Proof.
    intros env1 act s1 s1' v Hin Hsem.
    unfold dataWriteRqs in Hin.
    apply in_map_iff in Hin as [mAct [<- _]].
    destruct (SemAction_lift_np_mem_core_frame mAct s1 s1' v Hsem)
      as [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hdm Hmd]]]]]]].
    unfold flushMulDiv; rewrite Hrf, Hmd.
    repeat split; assumption.
  Qed.

  Theorem dataCrossLineSteps_frame :
    forall {env1 : Env iTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (v : bits 0),
      In act
        (@dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1.
  Proof.
    intros env1 act s1 s1' v Hin Hsem.
    unfold dataCrossLineSteps in Hin.
    apply in_map_iff in Hin as [mAct [<- _]].
    destruct (SemAction_lift_np_mem_core_frame mAct s1 s1' v Hsem)
      as [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hdm Hmd]]]]]]].
    unfold flushMulDiv; rewrite Hrf, Hmd.
    repeat split; assumption.
  Qed.

  (* --- 3C. `loadRqOrStoreOrFenceStage` Simulation --- *)

  (* Case 1: Stuttering step of `loadRqOrStoreOrFenceStage`
   * (`inputBuf` empty, `state != "LoadRq"`, or downstream memory/device port busy). *)
  Theorem sim_loadRqOrStoreOrFenceStage_stutter :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1' =
        impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 ->
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 ->
      (FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hflush Hmem Hdm Hfence Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [Hghost HmemRel HfenceInv].
      constructor.
      + rewrite Hdm, Hflush; exact Hghost.
      + rewrite Hmem; exact HmemRel.
      + exact (Hfence HfenceInv).
  Qed.

  (* Case 2: Store or Fence (or zero-addr Load) drained in `loadRqOrStoreOrFenceStage`
   * and committed architecturally via `specStep` (`ConsAction`). *)
  Theorem sim_loadRqOrStoreOrFenceStage_storeOrFence_commit :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 s2' : SState) (v : bits 0)
           (req : type MemFenceReq) (reqs : list (type MemFenceReq)),
      SemAction env1
        (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      cRel s1 s2 ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = true ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') = true ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = req :: reqs ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') = reqs ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      (forall rf1 wm1,
         GhostStep core pcAddrInit (spec_rf core pcAddrInit regions s2) rf1 (fun _ => false) wm1 req ->
         spec_rf core pcAddrInit regions s2' = rf1 /\ wm1 = (fun _ => false)) ->
      SemAction env2 (@specStep core pcAddrInit config regions clint plic type) s2 s2' Zmod.zero ->
      TreeContentRel (SpecMemSubTree core regions)
        (projImplMemSpecState core regions
           (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
        (spec_mem core pcAddrInit regions s2') ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 s1 s1' s2 s2' v req reqs _ Hrel Hrq1 Hrq1' Hq1 Hq1' Hflush HstepRf Hspec HmemRel' Hfence'.
    exists s2'; split.
    - exact (specMod_single_specStep core pcAddrInit config regions clint revSpec plic s2 s2' Hspec).
    - destruct Hrel as [[rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]] _ _].
      destruct (DataMemInFlightRel_LoadRq_inv_local _ _ _ _ _ Hrq1 Hinflight) as [-> ->].
      rewrite Hq1 in Hgl.
      destruct (GhostList_cons_inv_local _ _ req reqs _ _ Hgl) as [rf1 [wm1 [Hgstep HglRest]]].
      destruct (HstepRf rf1 wm1 Hgstep) as [Hrf2' ->].
      constructor.
      + exists (spec_rf core pcAddrInit regions s2'),
               (fun _ : bits RegIdxSzReal => false),
               wm_dm.
        split.
        * unfold DataMemInFlightRel; rewrite Hrq1'; split; reflexivity.
        * rewrite Hq1', Hflush, Hrf2'; exact HglRest.
      + exact HmemRel'.
      + exact Hfence'.
  Qed.

  (* Case 3: Load request issued in `loadRqOrStoreOrFenceStage`
   * (`state` transitions from `"LoadRq"` to `"LoadRp"`):
   * `s2` stutters via `NilAction` while the head `GhostStep` moves from
   * `dataMemPendingQueue` into `DataMemInFlightRel` via `GhostList_drain_to_inflight_local`! *)
  Theorem sim_loadRqOrStoreOrFenceStage_loadRq_issue :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0)
           (req : type MemFenceReq) (reqs : list (type MemFenceReq)),
      SemAction env1
        (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      cRel s1 s2 ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = true ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') = false ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = req :: reqs ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') = reqs ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      projImplMemSpecState core regions
        (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1') =
        projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v req reqs _ Hrel Hrq1 HnotRq1' Hq1 Hq1' Hflush HmemProj Hfence'.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [[rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]] HmemRel _].
      rewrite Hq1 in Hgl.
      destruct (GhostList_drain_to_inflight_local
                  _ _ (spec_rf core pcAddrInit regions s2) rf_mid _
                  (fun _ => false) wm_mid wm_dm req reqs
                  Hrq1 HnotRq1' Hinflight Hgl)
        as [rf_after' [wm_after' [_ [Hinflight' Hgl']]]].
      constructor.
      + exists rf_after', wm_after', wm_dm.
        split.
        * exact Hinflight'.
        * rewrite Hq1', Hflush; exact Hgl'.
      + rewrite HmemProj; exact HmemRel.
      + exact Hfence'.
  Qed.

  (* --- 3D. Memory Sub-Pipeline Stuttering Simulation (`dataCrossLineSteps`, `dataReadRqs`, `dataReadRps`, `dataWriteRqs`) --- *)

  Theorem sim_dataMem_mem_stutter :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type mTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (liftAction
           (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions)
           act)
        s1 s1' v ->
      cRel s1 s2 ->
      TreeContentRel (SpecMemSubTree core regions)
        (projImplMemSpecState core regions
           (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
        (spec_mem core pcAddrInit regions s2) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hsem Hrel HmemRel' Hfence'.
    destruct (SemAction_lift_np_mem_core_frame act s1 s1' v Hsem)
      as [Hrf [_ [_ [_ [_ [_ [Hdm Hmd]]]]]]].
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [Hghost _ _].
      constructor.
      + unfold flushMulDiv; rewrite Hdm, Hrf, Hmd; exact Hghost.
      + exact HmemRel'.
      + exact Hfence'.
  Qed.

  (* --- 3E. `issueRevRqStage`, `loadRpAndIssueRevRqStage`, and `revRpAndWriteBackStage` Simulation --- *)

  Theorem issueRevRqStage_frame :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      SemAction env1
        (@issueRevRqStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        dataMemPendingQueue core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1).
  Proof.
    intros env1 s1 s1' v Hsem.
    unfold issueRevRqStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [HsemC [<- _]]]].
    destruct (issueRevRq_core_frame core dataMemCapacity pcAddrInit bpT fTree decTree mdTree
                (@implExecuteIfc core)
                (fun ty => @implMemIfc core config regions ty rev)
                (Fst s1) c' v' HsemC)
      as [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hmd Hfifo]]]]]]].
    unfold flushMulDiv, dataMemPendingQueue, dataMem_fifo,
           impl_rf, impl_execute, impl_fetch, impl_decode, impl_dataMem, impl_mulDiv.
    change (impl_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions
              (writeSubTreeState
                 (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions) s1 c')) with c'.
    change (impl_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) with (Fst s1).
    unfold dmCore_rf, dmCore_fetch, dmCore_decode, dmCore_execute, dmCore_mulDiv,
           dm_inputFifo, dmCore_dataMem in *.
    rewrite Hrf, Hmd, Hfifo.
    repeat split; try assumption; reflexivity.
  Qed.

  Theorem revRpAndWriteBackStage_frame :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      SemAction env1
        (@revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        dataMemPendingQueue core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1).
  Proof.
    intros env1 s1 s1' v Hsem.
    unfold revRpAndWriteBackStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [HsemC [<- _]]]].
    destruct (revRpAndWriteBack_core_frame core dataMemCapacity pcAddrInit bpT fTree decTree mdTree
                (@implExecuteIfc core)
                (fun ty => @implMemIfc core config regions ty rev)
                (Fst s1) c' v' HsemC)
      as [_ [Hfetch [Hdecode [Hexec [Hmd Hfifo]]]]].
    unfold dataMemPendingQueue, dataMem_fifo,
           impl_execute, impl_fetch, impl_decode, impl_dataMem, impl_mulDiv.
    change (impl_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions
              (writeSubTreeState
                 (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions) s1 c')) with c'.
    change (impl_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) with (Fst s1).
    unfold dmCore_fetch, dmCore_decode, dmCore_execute, dmCore_mulDiv,
           dm_inputFifo, dmCore_dataMem in *.
    rewrite Hfifo.
    repeat split; try assumption; reflexivity.
  Qed.

  (* Stuttering simulation for `loadRpAndIssueRevRqStage` or `revRpAndWriteBackStage`
   * when an in-flight load advances state (`"LoadRp"` -> `"RevRq"` -> `"RevRp"`)
   * or stalls waiting for a memory/revoker response (`isDataMemLoadRq` stays `false`). *)
  Theorem sim_dataMem_inflight_stutter :
    forall {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState),
      cRel s1 s2 ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        isDataMemLoadRq core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1) ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        dataMemPendingQueue core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1) ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      TreeContentRel (SpecMemSubTree core regions)
        (projImplMemSpecState core regions
           (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
        (spec_mem core pcAddrInit regions s2) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env2 s1 s1' s2 Hrel Hrq' Hq' Hflush' HmemRel' Hfence'.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [[rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]] _ _].
      constructor.
      + exists rf_mid, wm_mid, wm_dm.
        split.
        * unfold DataMemInFlightRel in Hinflight |- *.
          rewrite Hrq'; exact Hinflight.
        * rewrite Hq', Hflush'; exact Hgl.
      + exact HmemRel'.
      + exact Hfence'.
  Qed.

  (* Commit simulation for in-flight Load writeback completion
   * (either in `loadRpAndIssueRevRqStage` when no revocation lookup is needed,
   *  or in `revRpAndWriteBackStage` when revocation lookup returns `revBit`):
   * - Before the step, `isDataMemLoadRq (impl_dataMem s1) = false`, so `DataMemInFlightRel`
   *   holds `exists req, GhostStep (spec_rf s2) rf_mid (fun _ => false) wm_mid req`.
   * - The hardware writes `dstVal` to `dstIdx` (`flushMulDiv s1' = writeGprVal dstIdx dstVal (flushMulDiv s1)`)
   *   and resets `dataMem_state` to `"LoadRq"` (`isDataMemLoadRq (impl_dataMem s1') = true`).
   * - Pushing `writeGprVal dstIdx dstVal` across `GhostList` yields
   *   `GhostList (writeGprVal dstIdx dstVal rf_mid) (fun _ => false) reqs (flushMulDiv s1') wm_dm'`,
   *   which matches `spec_rf s2' = writeGprVal dstIdx dstVal rf_mid` after `specStep`! *)
  Theorem sim_dataMem_load_writeback_commit :
    forall {env2 : Env sTree}
           (s1 s1' : IState) (s2 s2' : SState)
           (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag),
      cRel s1 s2 ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = false ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') = true ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        dataMemPendingQueue core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1) ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        writeGprVal core pcAddrInit dstIdx dstVal
          (flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1) ->
      (forall rf_mid wm_mid wm_dm req,
         GhostStep core pcAddrInit (spec_rf core pcAddrInit regions s2) rf_mid (fun _ => false) wm_mid req ->
         GhostList core pcAddrInit rf_mid wm_mid
           (dataMemPendingQueue core dataMemCapacity
              (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                            dataMemCapacity mulCapacity divCapacity mulStages divStages
                            mulDivMode config regions s1))
           (flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)
           wm_dm ->
         spec_rf core pcAddrInit regions s2' = writeGprVal core pcAddrInit dstIdx dstVal rf_mid /\
         exists wm_dm',
           GhostList core pcAddrInit
             (writeGprVal core pcAddrInit dstIdx dstVal rf_mid)
             (fun _ => false)
             (dataMemPendingQueue core dataMemCapacity
                (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                              dataMemCapacity mulCapacity divCapacity mulStages divStages
                              mulDivMode config regions s1))
             (writeGprVal core pcAddrInit dstIdx dstVal
                (flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                             dataMemCapacity mulCapacity divCapacity mulStages divStages
                             mulDivMode config regions s1))
             wm_dm') ->
      SemAction env2 (@specStep core pcAddrInit config regions clint plic type) s2 s2' Zmod.zero ->
      TreeContentRel (SpecMemSubTree core regions)
        (projImplMemSpecState core regions
           (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
        (spec_mem core pcAddrInit regions s2') ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env2 s1 s1' s2 s2' dstIdx dstVal Hrel HnotRq1 Hrq1' Hq' Hflush' Hcomm Hspec HmemRel' Hfence'.
    exists s2'; split.
    - exact (specMod_single_specStep core pcAddrInit config regions clint revSpec plic s2 s2' Hspec).
    - destruct Hrel as [[rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]] _ _].
      destruct (DataMemInFlightRel_NotLoadRq_inv_local _ _ _ _ _ HnotRq1 Hinflight)
        as [req Hgstep].
      destruct (Hcomm rf_mid wm_mid wm_dm req Hgstep Hgl)
        as [Hrf2' [wm_dm' Hgl']].
      constructor.
      + exists (spec_rf core pcAddrInit regions s2'),
               (fun _ : bits RegIdxSzReal => false),
               wm_dm'.
        split.
        * unfold DataMemInFlightRel; rewrite Hrq1'; split; reflexivity.
        * rewrite Hq', Hflush', Hrf2'; exact Hgl'.
      + exact HmemRel'.
      + exact Hfence'.
  Qed.

  (* --- 3F. Unconditional `stateRel` Simulation Theorems --- *)

  Theorem sim_loadRqOrStoreOrFenceStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_loadRqAndStoreStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2; exact sim_loadRqOrStoreOrFenceStage_stateRel.
  Qed.

  Theorem sim_loadRpAndIssueRevRqStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_revRpAndWriteBackStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_dataWriteRqs_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_dataReadRqs_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_dataReadRps_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_dataCrossLineSteps_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2) |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

End DataMemStageSimulation.

