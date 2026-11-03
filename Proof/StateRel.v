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

From Stdlib Require Import String List PeanoNat ZArith Zmod Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Export SpecDefines Decoder FunctionalUnits Alu Spec SpecFetchDeferred SpecDevice SpecRevoker SpecMulDiv Clint Plic.
From Cheriot Require Export Impl ImplCommon ImplBranchPredictor ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplDevice ImplRevoker ImplStaged ImplStagedProof.
From Cheriot Require Export ShiftFifo ShiftFifoLemmas FifoLemmas.
From Cheriot Require Export TreeLemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. SHIFT-FIFO LIST EXTRACTION & INITIALIZATION LEMMAS
 * =========================================================================== *)

Definition fifo_size {capacity : nat} {k : Kind}
  (f : TreeState ElemState (fifoTree capacity k))
  : bits (Z.log2_up (Z.of_nat (capacity + 1))) :=
  f.(Snd).(Fst).

Definition fifo_elems_all {capacity : nat} {k : Kind}
  (f : TreeState ElemState (fifoTree capacity k)) : list (type k) :=
  map (fun rk => readRegOfKind rk f) (elemPathsWithKind capacity k).

Definition fifo_to_list {capacity : nat} {k : Kind}
  (f : TreeState ElemState (fifoTree capacity k)) : list (type k) :=
  firstn (Z.to_nat (Zmod.unsigned (fifo_size f))) (fifo_elems_all f).

Lemma InitStateConsistent_fifo_size :
  forall (capacity : nat) (k : Kind)
         (f : TreeState ElemState (fifoTree capacity k)),
    InitStateConsistent (fifoTree capacity k) f ->
    fifo_size f = Zmod.zero.
Proof.
  intros capacity k [s_elems [s_size []]] [_ [Hsz _]].
  unfold fifo_size; cbn [Fst Snd].
  exact Hsz.
Qed.

Lemma InitStateConsistent_fifo_to_list :
  forall (capacity : nat) (k : Kind)
         (f : TreeState ElemState (fifoTree capacity k)),
    InitStateConsistent (fifoTree capacity k) f ->
    fifo_to_list f = [].
Proof.
  intros capacity k f Hinit.
  unfold fifo_to_list.
  rewrite (InitStateConsistent_fifo_size capacity k f Hinit).
  rewrite Zmod.unsigned_0.
  reflexivity.
Qed.

(* ===========================================================================
 * 3. SYSTEM STATE PROJECTIONS (`SpecState` AND `ImplState`)
 * =========================================================================== *)

Section StateProjections.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable revCfg : RevConfig.
  Variable regions : list MemRegion.

  (* --- 3A. Top-Level Tree & State Types --- *)

  Definition SpecTree : Tree Elem :=
    specSysTree pcAddrInit regions.

  Definition ImplTree : Tree Elem :=
    implSysTree pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode bp revCfg regions.

  Definition SpecState : Type :=
    TreeState ElemState SpecTree.

  Definition ImplState : Type :=
    TreeState ElemState ImplTree.

  Definition RfTree : Tree Elem :=
    rfTree pcAddrInit.

  Definition RfState : Type :=
    TreeState ElemState RfTree.

  Definition WaitBitsTree : Tree Elem :=
    waitBitsTree.

  Definition WaitBitsState : Type :=
    TreeState ElemState WaitBitsTree.

  Definition BpTree : Tree Elem :=
    withInst_BpTree bp.

  Definition FetchTree : Tree Elem :=
    implFetchTree pcAddrInit fetchCapacity instCapacity.

  Definition FetchState : Type :=
    TreeState ElemState FetchTree.

  Definition DecodeTree : Tree Elem :=
    implDecodeTree decodeCapacity.

  Definition DecodeState : Type :=
    TreeState ElemState DecodeTree.

  Definition ExecuteTree : Tree Elem :=
    implExecuteTree.

  Definition ExecuteState : Type :=
    TreeState ElemState ExecuteTree.

  Definition DataMemTree : Tree Elem :=
    implDataMemTree dataMemCapacity.

  Definition DataMemSubState : Type :=
    TreeState ElemState DataMemTree.

  Definition MulDivSubTree : Tree Elem :=
    implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode.

  Definition MulDivSubState : Type :=
    TreeState ElemState MulDivSubTree.

  Definition SpecMemSubTree : Tree Elem :=
    specMemTree regions.

  Definition SpecMemSubState : Type :=
    TreeState ElemState SpecMemSubTree.

  Definition ImplMemSubTree : Tree Elem :=
    implMemTree regions.

  Definition ImplMemSubState : Type :=
    TreeState ElemState ImplMemSubTree.

  (* --- 3B. Spec State Subtree Projections --- *)

  Definition spec_core (s2 : SpecState)
    : TreeState ElemState (specCoreTree pcAddrInit regions) :=
    s2.(Fst).

  Definition spec_rf (s2 : SpecState) : RfState :=
    (spec_core s2).(Fst).(Fst).

  Definition spec_mem (s2 : SpecState) : SpecMemSubState :=
    (spec_core s2).(Snd).(Fst).(Fst).

  (* --- 3C. Impl State Subtree Projections --- *)

  Definition impl_core (s1 : ImplState)
    : TreeState ElemState
        (coreTree RfTree BpTree ImplMemSubTree FetchTree DecodeTree ExecuteTree DataMemTree MulDivSubTree) :=
    s1.(Fst).

  Definition impl_rf (s1 : ImplState) : RfState :=
    (impl_core s1).(Fst).(Fst).

  Definition impl_waitBits (s1 : ImplState) : WaitBitsState :=
    (impl_core s1).(Snd).(Fst).(Fst).

  Definition impl_mem (s1 : ImplState) : ImplMemSubState :=
    (impl_core s1).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition impl_fetch (s1 : ImplState) : FetchState :=
    (impl_core s1).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition impl_decode (s1 : ImplState) : DecodeState :=
    (impl_core s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition impl_execute (s1 : ImplState) : ExecuteState :=
    (impl_core s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition impl_dataMem (s1 : ImplState) : DataMemSubState :=
    (impl_core s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition impl_mulDiv (s1 : ImplState) : MulDivSubState :=
    (impl_core s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  (* --- 3D. Memory Region & Device Projections (`revoker`, `clint`, `plic`, `fenceIAck`, `mems`) --- *)

  Definition projImplRegionSpecState (r : MemRegion)
    (sr : TreeState ElemState (implMemRegionTree r))
    : TreeState ElemState (memRegionTree r) :=
    sr.(Fst).

  (* Nth region state extraction for `specMemTree` and `implRegionsTree` *)

  (* Named projections for `mems`, `revoker`, `clint`, `plic`, `fenceIAck` *)

  (* Projection from `implRevokerTree core` (8 base leaves + 4 extra leaves)
   * onto `revokerTree []` (the 8 architectural revoker registers). *)
  Definition projImplRevokerArchState
    (s_rev : TreeState ElemState implRevokerTree)
    : TreeState ElemState (Node "revoker" (revokerChildren [])) :=
    (s_rev.(Fst) ,,
    (s_rev.(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt)))))))).

  (* --- 3E. Pipeline Stage Register & FIFO Projections --- *)

  (* 1. Execute stage (`implExecuteTree`) *)
  Definition exec_epoch (se : ExecuteState) : type Epoch :=
    se.(Fst).

  Definition exec_fenceIPending (se : ExecuteState) : bool :=
    se.(Snd).(Fst).

  Definition exec_canProceed (se : ExecuteState) : bool :=
    se.(Snd).(Snd).(Fst).

  (* 2. Fetch stage (`implFetchTree`) *)
  Definition fetch_pc (sf : FetchState) : type Addr :=
    sf.(Fst).

  Definition fetch_predEpoch (sf : FetchState) : type Epoch :=
    sf.(Snd).(Fst).

  Definition fetch_curParcelOpt (sf : FetchState) : type (Option (Bit LgFetchParcels)) :=
    sf.(Snd).(Snd).(Fst).

  Definition fetch_straddleOpt (sf : FetchState) : type (Option StraddleHalf) :=
    sf.(Snd).(Snd).(Snd).(Fst).

  Definition fetch_canProceed (sf : FetchState) : bool :=
    sf.(Snd).(Snd).(Snd).(Snd).(Fst).

  Definition fetch_fetchBufFifo (sf : FetchState)
    : TreeState ElemState (fifoTree fetchCapacity FetchBufEntry) :=
    sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition fetch_instFifo (sf : FetchState)
    : TreeState ElemState (fifoTree instCapacity AssembledInst) :=
    sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  (* 3. Decode stage (`implDecodeTree`) *)
  Definition decode_canProceed (sd : DecodeState) : bool :=
    sd.(Fst).

  Definition decode_toAluFifo (sd : DecodeState)
    : TreeState ElemState (fifoTree decodeCapacity DecodeToAluEntry) :=
    sd.(Snd).(Fst).(Fst).

  (* 4. DataMem stage (`implDataMemTree`) *)
  Definition dataMem_fifo (sdm : DataMemSubState)
    : TreeState ElemState (fifoTree dataMemCapacity MemFenceReq) :=
    sdm.(Fst).(Fst).

  Definition dataMem_state (sdm : DataMemSubState) : type DataMemState :=
    sdm.(Snd).(Fst).

  (* 5. Scoreboard WaitBits (`waitBitsTree`; x0 has no bit: the accessors start at index 1) *)
  Definition readWaitBit (idx : bits RegIdxSzReal) (wb : WaitBitsState) : bool :=
    evalReadRegsListHelper 1%nat nil gprWaitPathsWithKind idx wb.

  (* ===========================================================================
   * 4. `flushMulDiv`: PENDING MULDIV WRITEBACK TO REGISTER FILE
   * =========================================================================== *)

  Definition mkMulDivCap (resAddr : type Addr) : type FullECapWithTag :=
    (false ,, (getDefault ECap ,, (resAddr ,, tt))).

  Definition writeGprVal
    (dstIdx : bits RegIdxSzReal) (val : type FullECapWithTag) (rf : RfState) : RfState :=
    if negb (Zmod.eqb dstIdx Zmod.zero)
    then evalWriteRegsList (gprPathsWithKind pcAddrInit) dstIdx val rf
    else rf.

  (* Single-entry MulDiv writeback helper: if `busy = true`, write `dstIdx <- resCap` to `rf` *)

  (* Multi-entry MulDiv writeback fold over a list of pending `(dstIdx, resCap)` pairs *)
  Fixpoint flushMulDivCaps
    (entries : list (bits RegIdxSzReal * type FullECapWithTag))
    (rf : RfState) : RfState :=
    match entries with
    | nil => rf
    | (dstIdx, resCap) :: rest =>
        flushMulDivCaps rest (writeGprVal dstIdx resCap rf)
    end.

  (* Compute the architectural result capability for a `MulReq` *)
  Definition evalMulReqCap (req : type MulReq) : bits RegIdxSzReal * type FullECapWithTag :=
    let dstIdx := req.(Fst) in
    let op1    := req.(Snd).(Fst) in
    let mulOp  := req.(Snd).(Snd).(Fst) in
    let mdOp   : type MulDivUnion := evalExpr (UNION (MulDivType, "Mul" ::= Const type MulOp mulOp)) in
    let resAddr := evalLetExpr (@SpecMulDiv.MulDiv type op1 mdOp) in
    (dstIdx, mkMulDivCap resAddr).

  (* Compute the architectural result capability for a `DivReq` *)
  Definition evalDivReqCap (req : type DivReq) : bits RegIdxSzReal * type FullECapWithTag :=
    let dstIdx := req.(Fst) in
    let op1    := req.(Snd).(Fst) in
    let divOp  := req.(Snd).(Snd).(Fst) in
    let mdOp   : type MulDivUnion := evalExpr (UNION (MulDivType, "Div" ::= Const type DivOp divOp)) in
    let resAddr := evalLetExpr (@SpecMulDiv.MulDiv type op1 mdOp) in
    (dstIdx, mkMulDivCap resAddr).

  (* Compute the architectural result capability for a `MulDivReq` *)
  Definition evalMulDivReqCap (req : type MulDivReq) : bits RegIdxSzReal * type FullECapWithTag :=
    let dstIdx   := req.(Fst) in
    let op1      := req.(Snd).(Fst) in
    let mulDivOp := req.(Snd).(Snd).(Fst) in
    let resAddr  := evalLetExpr (@SpecMulDiv.MulDiv type op1 mulDivOp) in
    (dstIdx, mkMulDivCap resAddr).

  (* `n` more steps of an engine on state `st` *)
  Fixpoint iterStepN {StateK : Kind} (stepFn : forall ty, ty StateK -> LetExpr ty StateK) (n : nat)
    (st : type StateK) : type StateK :=
    match n with
    | 0%nat => st
    | S n' => iterStepN stepFn n' (evalLetExpr (stepFn type st))
    end.

  (* The pending `(dstIdx, resCap)` of an iterative engine + `RegIdx` FIFO: the result the engine
   * produces after its remaining `stepsRem` steps *)
  Definition extractIterEngineEntries {StateK OutK : Kind}
    (num_stages : nat)
    (stepFn : forall ty, ty StateK -> LetExpr ty StateK)
    (finishFn : forall ty, ty StateK -> LetExpr ty OutK)
    (projRes : type OutK -> type Addr)
    (s_iter : TreeState ElemState (stagedIterTree StateK num_stages))
    (s_dstFifo : TreeState ElemState (fifoTree MulDivFifoCapacity RegIdx))
    : list (bits RegIdxSzReal * type FullECapWithTag) :=
    let busy     := s_iter.(Fst) in
    let stepsRem := s_iter.(Snd).(Fst) in
    let st       := s_iter.(Snd).(Snd).(Fst) in
    match fifo_to_list s_dstFifo with
    | dstIdx :: _ =>
        if busy
        then
          let outVal := evalLetExpr (finishFn type (iterStepN stepFn (Z.to_nat (Zmod.unsigned stepsRem)) st)) in
          [(dstIdx, mkMulDivCap (projRes outVal))]
        else []
    | [] => []
    end.

  (* The states of a pipelined multiplier (`stagedStagesTree`), oldest first, each with the number
   * of steps it still needs (a state in stage `stages_k` needs `k`) *)
  Fixpoint extractPipeStageStates {StateK : Kind} (n : nat)
    : TreeState ElemState (stagedStagesTree StateK n) ->
      list (nat * type StateK) :=
    match n return
      TreeState ElemState (stagedStagesTree StateK n) ->
      list (nat * type StateK)
    with
    | 0%nat => fun s =>
        map (pair 0%nat) (@fifo_to_list 1 StateK (s.(Fst)))
    | S m => fun s =>
        (extractPipeStageStates m s.(Snd).(Fst) ++ map (pair (S m)) (@fifo_to_list 1 StateK (s.(Fst))))%list
    end.

  Definition extractPipeEngineEntries
    (s_pipe : TreeState ElemState (mulPipeTree (Z.to_nat Xlen) mulStages))
    (s_dstFifo : TreeState ElemState (fifoTree MulDivFifoCapacity RegIdx))
    : list (bits RegIdxSzReal * type FullECapWithTag) :=
    let stList  := extractPipeStageStates mulStages s_pipe in
    let dstList := fifo_to_list s_dstFifo in
    map (fun '(dstIdx, (k, st)) =>
           let outVal := evalLetExpr (@mulFinishStage (Z.to_nat Xlen) type
                           (iterStepN (fun ty' st' => @mulStageStep (Z.to_nat Xlen) ty' (Z.to_nat Xlen / mulStages)%nat st') k st)) in
           (dstIdx, mkMulDivCap (evalExpr (#outVal`"res"))))
        (combine dstList stList).

  (* Extract all pending `(dstIdx, resCap)` entries in `implMulDivTree` across all 3 modes *)
  Definition extractMulDivEntries (smd : MulDivSubState)
    : list (bits RegIdxSzReal * type FullECapWithTag) :=
    match mulDivMode as m
      return TreeState ElemState
               (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) ->
             list (bits RegIdxSzReal * type FullECapWithTag)
    with
    | PipelinedMul_IterDiv => fun s =>
        let s_mul     := s.(Fst) in
        let s_div     := s.(Snd).(Fst) in
        let mulReqF   := s_mul.(Fst) in
        let mulPipe   := s_mul.(Snd).(Fst).(Fst) in
        let mulDstF   := s_mul.(Snd).(Fst).(Snd).(Fst) in
        let divReqF   := s_div.(Fst) in
        let divIter   := s_div.(Snd).(Fst).(Fst) in
        let divDstF   := s_div.(Snd).(Fst).(Snd).(Fst) in
        (extractPipeEngineEntries mulPipe mulDstF ++
         map evalMulReqCap (fifo_to_list mulReqF) ++
         extractIterEngineEntries divStages
           (fun ty' st' => @divStageStep (Z.to_nat Xlen) ty' (Z.to_nat Xlen / divStages)%nat st')
           (@divFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) divIter divDstF ++
         map evalDivReqCap (fifo_to_list divReqF))%list
    | IterMul_SeparateIterDiv => fun s =>
        let s_mul     := s.(Fst) in
        let s_div     := s.(Snd).(Fst) in
        let mulReqF   := s_mul.(Fst) in
        let mulIter   := s_mul.(Snd).(Fst).(Fst) in
        let mulDstF   := s_mul.(Snd).(Fst).(Snd).(Fst) in
        let divReqF   := s_div.(Fst) in
        let divIter   := s_div.(Snd).(Fst).(Fst) in
        let divDstF   := s_div.(Snd).(Fst).(Snd).(Fst) in
        (extractIterEngineEntries mulStages
           (fun ty' st' => @mulStageStep (Z.to_nat Xlen) ty' (Z.to_nat Xlen / mulStages)%nat st')
           (@mulFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) mulIter mulDstF ++
         map evalMulReqCap (fifo_to_list mulReqF) ++
         extractIterEngineEntries divStages
           (fun ty' st' => @divStageStep (Z.to_nat Xlen) ty' (Z.to_nat Xlen / divStages)%nat st')
           (@divFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) divIter divDstF ++
         map evalDivReqCap (fifo_to_list divReqF))%list
    | IterMul_SharedIterDiv => fun s =>
        let reqF       := s.(Fst) in
        let sharedIter := s.(Snd).(Fst).(Fst) in
        let dstF       := s.(Snd).(Fst).(Snd).(Fst) in
        (extractIterEngineEntries (Nat.max mulStages divStages)
           (fun ty' st' => @sharedStageStep (Z.to_nat Xlen) ty' (Z.to_nat Xlen / mulStages)%nat
                             (Z.to_nat Xlen / divStages)%nat st')
           (@sharedFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) sharedIter dstF ++
         map evalMulDivReqCap (fifo_to_list reqF))%list
    end smd.

  Definition flushMulDivOn (rf : RfState) (smd : MulDivSubState) : RfState :=
    flushMulDivCaps (extractMulDivEntries smd) rf.

  Definition flushMulDiv (s1 : ImplState) : RfState :=
    flushMulDivOn (impl_rf s1) (impl_mulDiv s1).

  Lemma InitStateConsistent_extractMulDivEntries :
    forall (smd : MulDivSubState),
      InitStateConsistent MulDivSubTree smd ->
      extractMulDivEntries smd = [].
  Proof.
    unfold MulDivSubState, MulDivSubTree, extractMulDivEntries.
    destruct mulDivMode; intros smd Hinit.
    - (* PipelinedMul_IterDiv *)
      destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit.
      destruct Hinit as [[HmulReq [[HmulPipe [HmulDst _]] _]] [[HdivReq [[HdivIter [HdivDst _]] _]] _]].
      unfold extractPipeEngineEntries, extractIterEngineEntries; cbn [Fst Snd].
      rewrite (InitStateConsistent_fifo_to_list MulDivFifoCapacity RegIdx mulDstF HmulDst).
      rewrite (InitStateConsistent_fifo_to_list mulCapacity MulReq mulReqF HmulReq).
      rewrite (InitStateConsistent_fifo_to_list MulDivFifoCapacity RegIdx divDstF HdivDst).
      rewrite (InitStateConsistent_fifo_to_list divCapacity DivReq divReqF HdivReq).
      reflexivity.
    - (* IterMul_SeparateIterDiv *)
      destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit.
      destruct Hinit as [[HmulReq [[HmulIter [HmulDst _]] _]] [[HdivReq [[HdivIter [HdivDst _]] _]] _]].
      unfold extractIterEngineEntries; cbn [Fst Snd].
      rewrite (InitStateConsistent_fifo_to_list MulDivFifoCapacity RegIdx mulDstF HmulDst).
      rewrite (InitStateConsistent_fifo_to_list mulCapacity MulReq mulReqF HmulReq).
      rewrite (InitStateConsistent_fifo_to_list MulDivFifoCapacity RegIdx divDstF HdivDst).
      rewrite (InitStateConsistent_fifo_to_list divCapacity DivReq divReqF HdivReq).
      reflexivity.
    - (* IterMul_SharedIterDiv *)
      destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit.
      destruct Hinit as [Hreq [[Hiter [Hdst _]] _]].
      unfold extractIterEngineEntries; cbn [Fst Snd].
      rewrite (InitStateConsistent_fifo_to_list MulDivFifoCapacity RegIdx dstF Hdst).
      rewrite (InitStateConsistent_fifo_to_list mulCapacity MulDivReq reqF Hreq).
      reflexivity.
  Qed.

  Lemma InitStateConsistent_impl_mulDiv :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent MulDivSubTree (impl_mulDiv s1).
  Proof.
    intros s1 H; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H))))))))))).
  Qed.

  Lemma InitStateConsistent_flushMulDiv :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      flushMulDiv s1 = impl_rf s1.
  Proof.
    intros s1 Hinit.
    unfold flushMulDiv, flushMulDivOn.
    rewrite (InitStateConsistent_extractMulDivEntries (impl_mulDiv s1) (InitStateConsistent_impl_mulDiv s1 Hinit)).
    reflexivity.
  Qed.

  (* ===========================================================================
   * 5. `GhostStep` AND `Inductive GhostList` (DEFERRED STAGE-4 & DATAMEM QUEUE)
   * =========================================================================== *)

  (* Mask update helper matching `setDstWaitBits` / `commitWb` *)
  Definition updWaitMask
    (writesGpr : bool) (dstIdx : bits RegIdxSzReal) (val : bool)
    (mask : bits RegIdxSzReal -> bool) : bits RegIdxSzReal -> bool :=
    fun idx =>
      if andb writesGpr (Zmod.eqb idx dstIdx)
      then val
      else mask idx.

  (* Pure boolean predicate matching `isVirtCsr` in `aluAndExecuteNonDeferred` (`ImplExecute.v`):
   * checks whether `aluOut` is a non-sequential virtual CSR access (`VirtualCsrTable`). *)
  Definition isVirtualCsrAluOut (aluOut : type AluOutUnion) : bool :=
    let aluOp      : type AluOpUnion              := evalExpr (##aluOut`"Op") in
    let isNonSeq   : bool                         := evalExpr (#aluOp `? "NonSequential") in
    let nonSeqOp   : type NonSequentialUnion      := evalExpr (#aluOp `! "NonSequential") in
    let isNoExc    : bool                         := andb isNonSeq (evalExpr (#nonSeqOp `? "NoException")) in
    let noExc      : type NoExceptionUnion        := evalExpr (#nonSeqOp `! "NoException") in
    let isCfScrCsr : bool                         := andb isNoExc (evalExpr (#noExc `? "CfScrCsr")) in
    let cfScrCsr   : type CfScrCsrUnion           := evalExpr (#noExc `! "CfScrCsr") in
    let isScrCsr   : bool                         := andb isCfScrCsr (evalExpr (#cfScrCsr `? "ScrCsr")) in
    let scrCsr     : type ScrCsrPayload           := evalExpr (#cfScrCsr `! "ScrCsr") in
    let sDest      : type (TaggedUnion ScrCsrIdx) := evalExpr (##scrCsr`"SpecialDest") in
    let isCsr      : bool                         := andb isScrCsr (evalExpr (#sDest `? "Csr")) in
    let csrIdx     : bits CsrIdxSz                := evalExpr (#sDest `! "Csr") in
    andb isCsr (evalExpr (@csrIdxIsVirtual type csrIdx)).

  (* Pure specification of a single non-deferred Stage-4 execution step (`GhostStep`):
   * Given architectural `rf0` and scoreboard mask `waitMask0`, executing an instruction
   * whose non-deferred phase (`executeNonDeferred` + `nextPcc` write + optional `mulDiv`
   * writeback) transforms `rf0` into `rf1`, updates the scoreboard mask from `waitMask0`
   * to `waitMask1`, and enqueues `req : type MemFenceReq` into `dataMem`. *)
  Record GhostStep
    (rf0 rf1 : RfState)
    (waitMask0 waitMask1 : bits RegIdxSzReal -> bool)
    (req : type MemFenceReq) : Prop := {
    ghost_dstIdx : bits RegIdxSzReal := req.(Fst) ;
    ghost_addr   : type Addr         := req.(Snd).(Fst) ;
    ghost_op     : type MemFenceUnion := req.(Snd).(Snd).(Fst) ;
    (* Destination register waitBit is marked busy if `req` is a Load writing a non-zero GPR *)
    ghost_waitMask_step :
      let mfAct := evalLetExpr (@dispatchMemFence type ghost_dstIdx ghost_addr ghost_op) in
      let isLoad :=
        andb (evalExpr (#mfAct `? "Mem"))
             (evalExpr ((#mfAct `! "Mem") `? "Load")) in
      let writesDst := andb isLoad (negb (Zmod.eqb ghost_dstIdx Zmod.zero)) in
      waitMask1 = updWaitMask writesDst ghost_dstIdx true waitMask0 ;
    (* Non-deferred execution step from `rf0` to `rf1` *)
    ghost_rf_step :
      exists (pcc : type FullECapWithTag) (meip mtip : bool)
             (aluOut : type AluOutUnion) (execOut : type ExecuteOut)
             (rf_mid : RfState),
        SemAction defaultEnv (executeNonDeferred pcAddrInit pcc meip mtip aluOut) rf0 rf_mid execOut /\
        rf1 = evalWriteRegsList (gprPathsWithKind pcAddrInit) (Zmod.zero : bits RegIdxSzReal) (execOut.(Snd).(Snd).(Snd).(Snd).(Fst)) rf_mid /\
        execOut.(Snd).(Fst) = (req.(Snd).(Snd).(Fst) ,, (true ,, tt)) /\
        aluOut.(Snd).(Fst) = ghost_dstIdx /\
        aluOut.(Snd).(Snd).(Fst).(Snd).(Snd).(Fst) = ghost_addr
  }.

  (* Generalized `GhostStepOpt` indexed by `dmOpt : option (type MemFenceReq)`:
   * - Covers both `dmOpt = Some req` (DataMem/Fence instruction) and `dmOpt = None`
   *   (Sequential ALU/MulDiv or Non-Sequential Exception/SCR/physical-CSR/CF
   *   executed in Stage 4 while `dataMem` is non-empty; virtual CSRs and interrupts
   *   stall until `dataMem` is empty).
   * - Includes `ghost_nonInterference`: at issue/decode time, `waitMask0` was `false`
   *   on the destination GPR (if non-zero). *)
  Record GhostStepOpt
    (rf0 rf1 : RfState)
    (waitMask0 waitMask1 : bits RegIdxSzReal -> bool)
    (dmOpt : option (type MemFenceReq)) : Prop := {
    ghostOpt_nonInterference :
      match dmOpt with
      | Some req =>
          Zmod.eqb (req.(Fst)) Zmod.zero = false ->
          waitMask0 (req.(Fst)) = false
      | None => True
      end ;
    ghostOpt_step :
      match dmOpt with
      | Some req =>
          GhostStep rf0 rf1 waitMask0 waitMask1 req
      | None =>
          waitMask1 = waitMask0 /\
          exists (pcc : type FullECapWithTag) (meip mtip : bool)
                 (aluOut : type AluOutUnion) (execOut : type ExecuteOut)
                 (rf_mid : RfState),
            isVirtualCsrAluOut aluOut = false /\
            SemAction defaultEnv (executeNonDeferred pcAddrInit pcc meip mtip aluOut) rf0 rf_mid execOut /\
            execOut.(Snd).(Fst).(Snd).(Fst) = false /\
            rf1 = evalWriteRegsList (gprPathsWithKind pcAddrInit)
                    (Zmod.zero : bits RegIdxSzReal)
                    (execOut.(Snd).(Snd).(Snd).(Snd).(Fst)) rf_mid
      end
  }.

  (* Generalized inductive sequence `GhostListOpt` indexed by
   * `match dmOpt with Some req => req :: reqs | None => reqs end` so both
   * DataMem and non-DataMem instructions executed in Stage 4 while `dataMem`
   * is non-empty are recorded and drained via `SemActions` when `dataMem` drains. *)
  Inductive GhostListOpt
    : RfState -> (bits RegIdxSzReal -> bool) ->
      list (type MemFenceReq) ->
      RfState -> (bits RegIdxSzReal -> bool) -> Prop :=
  | GhostOptNil :
      forall (rf : RfState) (waitMask : bits RegIdxSzReal -> bool),
        GhostListOpt rf waitMask [] rf waitMask
  | GhostOptCons :
      forall (rf0 rf1 rf2 : RfState)
             (waitMask0 waitMask1 waitMask2 : bits RegIdxSzReal -> bool)
             (dmOpt : option (type MemFenceReq)) (reqs : list (type MemFenceReq)),
        GhostStepOpt rf0 rf1 waitMask0 waitMask1 dmOpt ->
        GhostListOpt rf1 waitMask1 reqs rf2 waitMask2 ->
        GhostListOpt rf0 waitMask0
          (match dmOpt with Some req => req :: reqs | None => reqs end)
          rf2 waitMask2.

  (* Inductive sequence of deferred `MemFenceReq` entries in `s1.dataMem` connecting
   * the speculative/committed register file `rf_spec` to `rf_impl = flushMulDiv s1`
   * and tracking the scoreboard waitBits mask `waitMask`. *)

  (* Queue of pending `MemFenceReq` entries in `s1.dataMem` *)

  Definition isDataMemLoadRq (sdm : DataMemSubState) : bool :=
    let st := dataMem_state sdm in
    evalExpr (#st `? "LoadRq").

  (* Predicate stating that `s1.dataMem` is completely idle/empty:
   * - `inputBuf` FIFO is empty (`dataMemPendingQueue sdm = []`),
   * - `state` is `"LoadRq"` (`isDataMemLoadRq sdm = true`). *)

  (* Detailed command correspondence for in-flight `dataMem_state` (`LoadRp ldCmd`,
   * `RevRq revCmd`, or `RevRp revCmd`) tying `dstIdx` and `addr` to the head
   * `GhostStep` request `req` and memory state. *)

  (* In-flight `dataMem_state` relation (`LoadRq` vs `LoadRp` / `RevRq` / `RevRp`):
   * When `dataMem_state` is `"LoadRq"`, there is no in-flight load response
   * awaiting writeback (`rf_after_inflight = rf_spec` and `waitMask_after_inflight = waitMask0`).
   * When `dataMem_state` is in `LoadRp` / `RevRq` / `RevRp`, one load has already dequeued
   * from `inputBuf` and its non-deferred RF update has already been applied. *)

  (* ===========================================================================
   * 6. `Fence.I` INVARIANTS (`FenceIActive`, MESSAGE CONSERVATION & QUIESCENCE)
   * =========================================================================== *)

  (* Check whether a `MemFenceReq` is a `Fence.I` request *)

  (* Check whether any external memory region has `fenceIWait = true` *)

  (* `FenceIActive`: holds when a `Fence.I` is in flight in Execute, DataMem, or Memory *)

  (* Message conservation between `fenceIRq`, `fenceIAck`, and `fenceIWait` across all regions *)

  (* System-level `Fence.I` message conservation conditioned on `~ FenceIActive s1` *)

  (* Pipeline epoch quiescence when `FenceIActive` holds:
   * All entries in `instFifo` and `decodeToAluFifo` with the current `execEpoch`
   * have been drained or invalidated by the `Fence.I` epoch increment. *)

  (* Extended frontend epoch quiescence relating `fetch_predEpoch` to `exec_epoch` *)

  (* Helper: `InitStateConsistent` on `implMemTree` implies `InitStateConsistent` on its projected `specMemTree` *)

  (* ===========================================================================
   * 7. SCOREBOARD `waitBits`, FRONTEND (`Fetch`/`Decode`) & `CoreStateRel`
   * =========================================================================== *)

  (* WaitBits consistency: at reset, all waitBits are `false`; during execution,
   * the hardware `waitBitsMask` matches the mask accumulated by `GhostList` plus
   * any in-flight `MulDiv` destination registers and valid-epoch `decodeToAluFifo`
   * destination registers. *)

  (* Frontend Fetch validity invariant (`FetchValidInv`):
   * Every valid-epoch (`entry.execEpoch = exec_epoch (impl_execute s1)`) entry in
   * `fetch_fetchBufFifo` and `fetch_instFifo` has an aligned PC and agrees with
   * instruction memory, and `FenceIFetchEpochQuiescent` holds when no Fence.I is active. *)

  (* Frontend Decode validity invariant (`DecodeValidInv`):
   * Every valid-epoch (`entry.execEpoch = exec_epoch (impl_execute s1)`) entry in
   * `decode_toAluFifo (impl_decode s1)` has `entry.execEpoch = ep` and its
   * non-zero destination register is tracked while in flight. *)

  (* Concrete register file + DataMem + MulDiv deferred execution invariant *)

  (* Concrete 3-field core state relation *)

  (* Corollary: When `s1.dataMem` is completely empty, `s2.rf = flushMulDiv s1`. *)

  Lemma allTreeInitDet_RfTree :
    allTreeInitDet RfTree = true.
  Proof.
    reflexivity.
  Qed.

  (* Concrete initialization theorem on `CoreStateRel` *)

End StateProjections.
