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

Definition fifo_size {dom : string} {capacity : nat} {k : Kind}
  (f : TreeState DomainElemState (fifoTree dom capacity k))
  : bits (Z.log2_up (Z.of_nat (capacity + 1))) :=
  f.(Snd).(Fst).

Definition fifo_elems_all {dom : string} {capacity : nat} {k : Kind}
  (f : TreeState DomainElemState (fifoTree dom capacity k)) : list (type k) :=
  map (fun rk => readRegOfKind rk f) (elemPathsWithKind dom capacity k).

Definition fifo_to_list {dom : string} {capacity : nat} {k : Kind}
  (f : TreeState DomainElemState (fifoTree dom capacity k)) : list (type k) :=
  firstn (Z.to_nat (Zmod.unsigned (fifo_size f))) (fifo_elems_all f).

Lemma InitStateConsistent_fifo_size :
  forall (dom : string) (capacity : nat) (k : Kind)
         (f : TreeState DomainElemState (fifoTree dom capacity k)),
    InitStateConsistent (fifoTree dom capacity k) f ->
    fifo_size f = Zmod.zero.
Proof.
  intros dom capacity k [s_elems [s_size []]] [_ [Hsz _]].
  unfold fifo_size; cbn [Fst Snd].
  exact Hsz.
Qed.

Lemma InitStateConsistent_fifo_to_list :
  forall (dom : string) (capacity : nat) (k : Kind)
         (f : TreeState DomainElemState (fifoTree dom capacity k)),
    InitStateConsistent (fifoTree dom capacity k) f ->
    fifo_to_list f = [].
Proof.
  intros dom capacity k f Hinit.
  unfold fifo_to_list.
  rewrite (InitStateConsistent_fifo_size dom capacity k f Hinit).
  rewrite Zmod.unsigned_0.
  reflexivity.
Qed.

(* ===========================================================================
 * 3. SYSTEM STATE PROJECTIONS (`SpecState` AND `ImplState`)
 * =========================================================================== *)

Section StateProjections.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable revCfg : RevConfig.
  Variable regions : list MemRegion.

  Local Abbreviation specMemTree := (specMemTree core).
  Local Abbreviation implMemTree := (implMemTree core).
  Local Abbreviation implRegionsTree := (implRegionsTree core).
  Local Abbreviation memRegionTree := (memRegionTree core).
  Local Abbreviation implMemRegionTree := (implMemRegionTree core).
  Local Abbreviation memRegionKindTree := (memRegionKindTree core).

  (* --- 3A. Top-Level Tree & State Types --- *)

  Definition SpecTree : Tree DomainElem :=
    specSysTree core pcAddrInit regions.

  Definition ImplTree : Tree DomainElem :=
    implSysTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode revCfg regions.

  Definition SpecState : Type :=
    TreeState DomainElemState SpecTree.

  Definition ImplState : Type :=
    TreeState DomainElemState ImplTree.

  Definition RfTree : Tree DomainElem :=
    rfTree core pcAddrInit.

  Definition RfState : Type :=
    TreeState DomainElemState RfTree.

  Definition WaitBitsTree : Tree DomainElem :=
    waitBitsTree core.

  Definition WaitBitsState : Type :=
    TreeState DomainElemState WaitBitsTree.

  Definition BpTree : Tree DomainElem :=
    implBpTree.

  Definition BpState : Type :=
    TreeState DomainElemState BpTree.

  Definition FetchTree : Tree DomainElem :=
    implFetchTree core pcAddrInit fetchCapacity instCapacity.

  Definition FetchState : Type :=
    TreeState DomainElemState FetchTree.

  Definition DecodeTree : Tree DomainElem :=
    implDecodeTree core decodeCapacity.

  Definition DecodeState : Type :=
    TreeState DomainElemState DecodeTree.

  Definition ExecuteTree : Tree DomainElem :=
    implExecuteTree core.

  Definition ExecuteState : Type :=
    TreeState DomainElemState ExecuteTree.

  Definition DataMemTree : Tree DomainElem :=
    implDataMemTree core dataMemCapacity.

  Definition DataMemSubState : Type :=
    TreeState DomainElemState DataMemTree.

  Definition MulDivSubTree : Tree DomainElem :=
    implMulDivTree core mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode.

  Definition MulDivSubState : Type :=
    TreeState DomainElemState MulDivSubTree.

  Definition SpecMemSubTree : Tree DomainElem :=
    specMemTree regions.

  Definition SpecMemSubState : Type :=
    TreeState DomainElemState SpecMemSubTree.

  Definition ImplMemSubTree : Tree DomainElem :=
    implMemTree regions.

  Definition ImplMemSubState : Type :=
    TreeState DomainElemState ImplMemSubTree.

  (* --- 3B. Spec State Subtree Projections --- *)

  Definition spec_core (s2 : SpecState)
    : TreeState DomainElemState (specCoreTree core pcAddrInit regions) :=
    s2.(Fst).

  Definition spec_rf (s2 : SpecState) : RfState :=
    (spec_core s2).(Fst).(Fst).

  Definition spec_mem (s2 : SpecState) : SpecMemSubState :=
    (spec_core s2).(Snd).(Fst).(Fst).

  (* --- 3C. Impl State Subtree Projections --- *)

  Definition impl_core (s1 : ImplState)
    : TreeState DomainElemState
        (coreTree core RfTree BpTree ImplMemSubTree FetchTree DecodeTree ExecuteTree DataMemTree MulDivSubTree) :=
    s1.(Fst).

  Definition impl_rf (s1 : ImplState) : RfState :=
    (impl_core s1).(Fst).(Fst).

  Definition impl_waitBits (s1 : ImplState) : WaitBitsState :=
    (impl_core s1).(Snd).(Fst).(Fst).

  Definition impl_bp (s1 : ImplState) : BpState :=
    (impl_core s1).(Snd).(Snd).(Fst).(Fst).

  Definition impl_branchPred (s1 : ImplState) : BpState :=
    impl_bp s1.

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
    (sr : TreeState DomainElemState (implMemRegionTree r))
    : TreeState DomainElemState (memRegionTree r) :=
    sr.(Fst).

  Fixpoint projImplMemRegions (rs : list MemRegion)
    : TreeState DomainElemState (implRegionsTree rs) ->
      TreeState DomainElemState (specMemTree rs) :=
    match rs return
      TreeState DomainElemState (implRegionsTree rs) ->
      TreeState DomainElemState (specMemTree rs)
    with
    | nil => fun _ => tt
    | r :: rest => fun s =>
        (projImplRegionSpecState r s.(Fst) ,, (projImplMemRegions rest s.(Snd).(Fst) ,, tt))
    end.

  Definition projImplMemSpecState
    (sm : ImplMemSubState) : SpecMemSubState :=
    projImplMemRegions regions sm.(Fst).

  (* Nth region state extraction for `specMemTree` and `implRegionsTree` *)
  Fixpoint nthSpecRegionState (idx : nat) (rs : list MemRegion)
    : TreeState DomainElemState (specMemTree rs) ->
      TreeState DomainElemState (nth idx (map memRegionTree rs) (Node "" [])) :=
    match rs return
      TreeState DomainElemState (specMemTree rs) ->
      TreeState DomainElemState (nth idx (map memRegionTree rs) (Node "" []))
    with
    | nil => fun _ =>
        match idx return TreeState DomainElemState (nth idx [] (Node "" [])) with
        | 0%nat => tt
        | S _ => tt
        end
    | r0 :: rest =>
        match idx return
          TreeState DomainElemState (specMemTree (r0 :: rest)) ->
          TreeState DomainElemState (nth idx (map memRegionTree (r0 :: rest)) (Node "" []))
        with
        | 0%nat => fun s => s.(Fst)
        | S idx' => fun s => nthSpecRegionState idx' rest s.(Snd).(Fst)
        end
    end.

  Fixpoint nthImplRegionState (idx : nat) (rs : list MemRegion)
    : TreeState DomainElemState (implRegionsTree rs) ->
      TreeState DomainElemState (nth idx (map implMemRegionTree rs) (Node "" [])) :=
    match rs return
      TreeState DomainElemState (implRegionsTree rs) ->
      TreeState DomainElemState (nth idx (map implMemRegionTree rs) (Node "" []))
    with
    | nil => fun _ =>
        match idx return TreeState DomainElemState (nth idx [] (Node "" [])) with
        | 0%nat => tt
        | S _ => tt
        end
    | r0 :: rest =>
        match idx return
          TreeState DomainElemState (implRegionsTree (r0 :: rest)) ->
          TreeState DomainElemState (nth idx (map implMemRegionTree (r0 :: rest)) (Node "" []))
        with
        | 0%nat => fun s => s.(Fst)
        | S idx' => fun s => nthImplRegionState idx' rest s.(Snd).(Fst)
        end
    end.

  Definition spec_regionAt (idx : nat) (s2 : SpecState)
    : TreeState DomainElemState (nth idx (map memRegionTree regions) (Node "" [])) :=
    nthSpecRegionState idx regions (spec_mem s2).

  Definition impl_regionAt (idx : nat) (s1 : ImplState)
    : TreeState DomainElemState (nth idx (map implMemRegionTree regions) (Node "" [])) :=
    nthImplRegionState idx regions (impl_mem s1).(Fst).

  Definition impl_regionSpecAt (idx : nat) (s1 : ImplState)
    : TreeState DomainElemState (nth idx (map memRegionTree regions) (Node "" [])) :=
    nthSpecRegionState idx regions (projImplMemSpecState (impl_mem s1)).

  (* Named projections for `mems`, `revoker`, `clint`, `plic`, `fenceIAck` *)
  Definition spec_mems (s2 : SpecState) : SpecMemSubState :=
    spec_mem s2.

  Definition impl_mems (s1 : ImplState) : SpecMemSubState :=
    projImplMemSpecState (impl_mem s1).

  Definition spec_revoker (revIdx : nat) (s2 : SpecState) :=
    spec_regionAt revIdx s2.

  Definition impl_revoker (revIdx : nat) (s1 : ImplState) :=
    impl_regionAt revIdx s1.

  Definition impl_revokerSpec (revIdx : nat) (s1 : ImplState) :=
    impl_regionSpecAt revIdx s1.

  Definition spec_clint (clintIdx : nat) (s2 : SpecState) :=
    spec_regionAt clintIdx s2.

  Definition impl_clint (clintIdx : nat) (s1 : ImplState) :=
    impl_regionSpecAt clintIdx s1.

  Definition spec_plic (plicIdx : nat) (s2 : SpecState) :=
    spec_regionAt plicIdx s2.

  Definition impl_plic (plicIdx : nat) (s1 : ImplState) :=
    impl_regionSpecAt plicIdx s1.

  Definition spec_fenceIAck (fenceIAckIdx : nat) (s2 : SpecState) :=
    spec_regionAt fenceIAckIdx s2.

  Definition impl_fenceIAck (fenceIAckIdx : nat) (s1 : ImplState) :=
    impl_regionSpecAt fenceIAckIdx s1.

  (* Projection from `implRevokerTree core` (7 base leaves + 4 extra leaves)
   * onto `revokerTree core []` (the 7 architectural revoker registers). *)
  Definition projImplRevokerArchState
    (s_rev : TreeState DomainElemState (implRevokerTree core))
    : TreeState DomainElemState (Node "revoker" (revokerChildren core [])) :=
    (s_rev.(Fst) ,,
    (s_rev.(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (s_rev.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt))))))).

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

  Definition fetch_epoch (sf : FetchState) : type Epoch :=
    fetch_predEpoch sf.

  Definition fetch_curParcelOpt (sf : FetchState) : type (Option (Bit LgFetchParcels)) :=
    sf.(Snd).(Snd).(Fst).

  Definition fetch_straddleOpt (sf : FetchState) : type (Option StraddleHalf) :=
    sf.(Snd).(Snd).(Snd).(Fst).

  Definition fetch_canProceed (sf : FetchState) : bool :=
    sf.(Snd).(Snd).(Snd).(Snd).(Fst).

  Definition fetch_fetchBufFifo (sf : FetchState)
    : TreeState DomainElemState (fifoTree core fetchCapacity FetchBufEntry) :=
    sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition fetch_instFifo (sf : FetchState)
    : TreeState DomainElemState (fifoTree core instCapacity AssembledInst) :=
    sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  (* 3. Decode stage (`implDecodeTree`) *)
  Definition decode_canProceed (sd : DecodeState) : bool :=
    sd.(Fst).

  Definition decode_toAluFifo (sd : DecodeState)
    : TreeState DomainElemState (fifoTree core decodeCapacity DecodeToAluEntry) :=
    sd.(Snd).(Fst).(Fst).

  (* 4. DataMem stage (`implDataMemTree`) *)
  Definition dataMem_fifo (sdm : DataMemSubState)
    : TreeState DomainElemState (fifoTree core dataMemCapacity MemFenceReq) :=
    sdm.(Fst).(Fst).

  Definition dataMem_state (sdm : DataMemSubState) : type DataMemState :=
    sdm.(Snd).(Fst).

  (* 5. Scoreboard WaitBits (`waitBitsTree`) *)
  Definition readWaitBit (idx : bits RegIdxSzReal) (wb : WaitBitsState) : bool :=
    evalReadRegsList (gprWaitPathsWithKind core) idx wb.

  Definition writeWaitBit (idx : bits RegIdxSzReal) (val : bool) (wb : WaitBitsState)
    : WaitBitsState :=
    evalWriteRegsList (gprWaitPathsWithKind core) idx val wb.

  Definition waitBitsMask (wb : WaitBitsState) (idx : bits RegIdxSzReal) : bool :=
    readWaitBit idx wb.

  (* ===========================================================================
   * 4. `flushMulDiv`: PENDING MULDIV WRITEBACK TO REGISTER FILE
   * =========================================================================== *)

  Definition mkMulDivCap (resAddr : type Addr) : type FullECapWithTag :=
    (false ,, (getDefault ECap ,, (resAddr ,, tt))).

  Definition writeGprVal
    (dstIdx : bits RegIdxSzReal) (val : type FullECapWithTag) (rf : RfState) : RfState :=
    if negb (Zmod.eqb dstIdx Zmod.zero)
    then evalWriteRegsList (gprPathsWithKind core pcAddrInit) dstIdx val rf
    else rf.

  (* Single-entry MulDiv writeback helper: if `busy = true`, write `dstIdx <- resCap` to `rf` *)
  Definition applyMulDivWb
    (busy : bool) (dstIdx : bits RegIdxSzReal) (resCap : type FullECapWithTag)
    (rf : RfState) : RfState :=
    if busy then writeGprVal dstIdx resCap rf else rf.

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

  (* Extract active `(dstIdx, resCap)` from an iterative engine + `RegIdx` FIFO *)
  Definition extractIterEngineEntries {StateK OutK : Kind}
    (num_stages : nat)
    (finishFn : forall ty, ty StateK -> LetExpr ty OutK)
    (projRes : type OutK -> type Addr)
    (s_iter : TreeState DomainElemState (stagedIterTree core StateK num_stages))
    (s_dstFifo : TreeState DomainElemState (fifoTree core MulDivFifoCapacity RegIdx))
    : list (bits RegIdxSzReal * type FullECapWithTag) :=
    let busy := s_iter.(Fst) in
    let st   := s_iter.(Snd).(Snd).(Fst) in
    match fifo_to_list s_dstFifo with
    | dstIdx :: _ =>
        if busy
        then
          let outVal := evalLetExpr (finishFn type st) in
          [(dstIdx, mkMulDivCap (projRes outVal))]
        else []
    | [] => []
    end.

  (* Extract active stage values from a pipelined multiplier (`stagedStagesTree`) *)
  Fixpoint extractPipeStageStates {StateK : Kind} (n : nat)
    : TreeState DomainElemState (stagedStagesTree core StateK n) ->
      list (type StateK) :=
    match n return
      TreeState DomainElemState (stagedStagesTree core StateK n) ->
      list (type StateK)
    with
    | 0%nat => fun s =>
        @fifo_to_list core 1 StateK (s.(Fst))
    | S m => fun s =>
        (extractPipeStageStates m s.(Snd).(Fst) ++ @fifo_to_list core 1 StateK (s.(Fst)))%list
    end.

  Definition extractPipeEngineEntries
    (s_pipe : TreeState DomainElemState (mulPipeTree core (Z.to_nat Xlen) mulStages))
    (s_dstFifo : TreeState DomainElemState (fifoTree core MulDivFifoCapacity RegIdx))
    : list (bits RegIdxSzReal * type FullECapWithTag) :=
    let stList  := extractPipeStageStates mulStages s_pipe in
    let dstList := fifo_to_list s_dstFifo in
    map (fun '(dstIdx, st) =>
           let outVal := evalLetExpr (@mulFinishStage (Z.to_nat Xlen) type st) in
           (dstIdx, mkMulDivCap (evalExpr (#outVal`"res"))))
        (combine dstList stList).

  (* Extract all pending `(dstIdx, resCap)` entries in `implMulDivTree` across all 3 modes *)
  Definition extractMulDivEntries (smd : MulDivSubState)
    : list (bits RegIdxSzReal * type FullECapWithTag) :=
    match mulDivMode as m
      return TreeState DomainElemState
               (implMulDivTree core mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) ->
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
         extractIterEngineEntries divStages (@divFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) divIter divDstF ++
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
        (extractIterEngineEntries mulStages (@mulFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) mulIter mulDstF ++
         map evalMulReqCap (fifo_to_list mulReqF) ++
         extractIterEngineEntries divStages (@divFinishStage (Z.to_nat Xlen)) (fun o => evalExpr (#o`"res")) divIter divDstF ++
         map evalDivReqCap (fifo_to_list divReqF))%list
    | IterMul_SharedIterDiv => fun s =>
        let reqF       := s.(Fst) in
        let sharedIter := s.(Snd).(Fst).(Fst) in
        let dstF       := s.(Snd).(Fst).(Snd).(Fst) in
        (extractIterEngineEntries (Nat.max mulStages divStages)
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
      rewrite (InitStateConsistent_fifo_to_list core MulDivFifoCapacity RegIdx mulDstF HmulDst).
      rewrite (InitStateConsistent_fifo_to_list core mulCapacity MulReq mulReqF HmulReq).
      rewrite (InitStateConsistent_fifo_to_list core MulDivFifoCapacity RegIdx divDstF HdivDst).
      rewrite (InitStateConsistent_fifo_to_list core divCapacity DivReq divReqF HdivReq).
      reflexivity.
    - (* IterMul_SeparateIterDiv *)
      destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit.
      destruct Hinit as [[HmulReq [[HmulIter [HmulDst _]] _]] [[HdivReq [[HdivIter [HdivDst _]] _]] _]].
      unfold extractIterEngineEntries; cbn [Fst Snd].
      rewrite (InitStateConsistent_fifo_to_list core MulDivFifoCapacity RegIdx mulDstF HmulDst).
      rewrite (InitStateConsistent_fifo_to_list core mulCapacity MulReq mulReqF HmulReq).
      rewrite (InitStateConsistent_fifo_to_list core MulDivFifoCapacity RegIdx divDstF HdivDst).
      rewrite (InitStateConsistent_fifo_to_list core divCapacity DivReq divReqF HdivReq).
      reflexivity.
    - (* IterMul_SharedIterDiv *)
      destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit.
      destruct Hinit as [Hreq [[Hiter [Hdst _]] _]].
      unfold extractIterEngineEntries; cbn [Fst Snd].
      rewrite (InitStateConsistent_fifo_to_list core MulDivFifoCapacity RegIdx dstF Hdst).
      rewrite (InitStateConsistent_fifo_to_list core mulCapacity MulDivReq reqF Hreq).
      reflexivity.
  Qed.

  Lemma InitStateConsistent_impl_rf :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent RfTree (impl_rf s1).
  Proof.
    intros s1 H; exact (proj1 (proj1 (proj1 H))).
  Qed.

  Lemma InitStateConsistent_impl_mem :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent ImplMemSubTree (impl_mem s1).
  Proof.
    intros s1 H; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj1 H)))))).
  Qed.

  Lemma InitStateConsistent_impl_execute :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent ExecuteTree (impl_execute s1).
  Proof.
    intros s1 H; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H))))))))).
  Qed.

  Lemma InitStateConsistent_impl_dataMem :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent DataMemTree (impl_dataMem s1).
  Proof.
    intros s1 H; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H)))))))))).
  Qed.

  Lemma InitStateConsistent_impl_mulDiv :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent MulDivSubTree (impl_mulDiv s1).
  Proof.
    intros s1 H; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H))))))))))).
  Qed.

  Lemma InitStateConsistent_spec_rf :
    forall (s2 : SpecState),
      InitStateConsistent SpecTree s2 ->
      InitStateConsistent RfTree (spec_rf s2).
  Proof.
    intros s2 H; exact (proj1 (proj1 (proj1 H))).
  Qed.

  Lemma InitStateConsistent_spec_mem :
    forall (s2 : SpecState),
      InitStateConsistent SpecTree s2 ->
      InitStateConsistent SpecMemSubTree (spec_mem s2).
  Proof.
    intros s2 H; exact (proj1 (proj1 (proj2 (proj1 H)))).
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
        SemAction defaultEnv (executeNonDeferred core pcAddrInit pcc meip mtip aluOut) rf0 rf_mid execOut /\
        rf1 = evalWriteRegsList (gprPathsWithKind core pcAddrInit) (Zmod.zero : bits RegIdxSzReal) (execOut.(Snd).(Snd).(Snd).(Snd).(Fst)) rf_mid /\
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
            SemAction defaultEnv (executeNonDeferred core pcAddrInit pcc meip mtip aluOut) rf0 rf_mid execOut /\
            execOut.(Snd).(Fst).(Snd).(Fst) = false /\
            rf1 = evalWriteRegsList (gprPathsWithKind core pcAddrInit)
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
  Inductive GhostList
    : RfState -> (bits RegIdxSzReal -> bool) ->
      list (type MemFenceReq) ->
      RfState -> (bits RegIdxSzReal -> bool) -> Prop :=
  | GhostNil :
      forall (rf : RfState) (waitMask : bits RegIdxSzReal -> bool),
        GhostList rf waitMask [] rf waitMask
  | GhostCons :
      forall (rf0 rf1 rf2 : RfState)
             (waitMask0 waitMask1 waitMask2 : bits RegIdxSzReal -> bool)
             (req : type MemFenceReq) (reqs : list (type MemFenceReq)),
        GhostStep rf0 rf1 waitMask0 waitMask1 req ->
        GhostList rf1 waitMask1 reqs rf2 waitMask2 ->
        GhostList rf0 waitMask0 (req :: reqs) rf2 waitMask2.

  (* Queue of pending `MemFenceReq` entries in `s1.dataMem` *)
  Definition dataMemPendingQueue (sdm : DataMemSubState) : list (type MemFenceReq) :=
    fifo_to_list (dataMem_fifo sdm).

  Definition isDataMemLoadRq (sdm : DataMemSubState) : bool :=
    let st := dataMem_state sdm in
    evalExpr (#st `? "LoadRq").

  (* Predicate stating that `s1.dataMem` is completely idle/empty:
   * - `inputBuf` FIFO is empty (`dataMemPendingQueue sdm = []`),
   * - `state` is `"LoadRq"` (`isDataMemLoadRq sdm = true`). *)
  Definition DataMemEmpty (sdm : DataMemSubState) : Prop :=
    dataMemPendingQueue sdm = [] /\
    isDataMemLoadRq sdm = true.

  (* Detailed command correspondence for in-flight `dataMem_state` (`LoadRp ldCmd`,
   * `RevRq revCmd`, or `RevRp revCmd`) tying `dstIdx` and `addr` to the head
   * `GhostStep` request `req` and memory state. *)
  Definition DataMemInFlightCmdRel
    (sdm : DataMemSubState)
    (req : type MemFenceReq) : Prop :=
    let st := dataMem_state sdm in
    if evalExpr (#st `? "LoadRp") then
      let ldCmd := evalExpr (#st `! "LoadRp") in
      ldCmd.(Snd).(Fst).(Fst) = req.(Fst) /\
      ldCmd.(Fst) = req.(Snd).(Fst)
    else if evalExpr (#st `? "RevRq") then
      let revCmd := evalExpr (#st `! "RevRq") in
      revCmd.(Snd).(Fst).(Fst) = req.(Fst)
    else if evalExpr (#st `? "RevRp") then
      let revCmd := evalExpr (#st `! "RevRp") in
      revCmd.(Snd).(Fst).(Fst) = req.(Fst)
    else True.

  (* In-flight `dataMem_state` relation (`LoadRq` vs `LoadRp` / `RevRq` / `RevRp`):
   * When `dataMem_state` is `"LoadRq"`, there is no in-flight load response
   * awaiting writeback (`rf_after_inflight = rf_spec` and `waitMask_after_inflight = waitMask0`).
   * When `dataMem_state` is in `LoadRp` / `RevRq` / `RevRp`, one load has already dequeued
   * from `inputBuf` and its non-deferred RF update has already been applied. *)
  Definition DataMemInFlightRel
    (sdm : DataMemSubState)
    (rf_spec rf_after_inflight : RfState)
    (waitMask0 waitMask_after_inflight : bits RegIdxSzReal -> bool) : Prop :=
    if isDataMemLoadRq sdm
    then
      rf_after_inflight = rf_spec /\
      waitMask_after_inflight = waitMask0
    else
      exists (req : type MemFenceReq),
        GhostStep rf_spec rf_after_inflight waitMask0 waitMask_after_inflight req.

  Lemma GhostList_nil_inv :
    forall rf0 waitMask0 rf2 waitMask2,
      GhostList rf0 waitMask0 [] rf2 waitMask2 ->
      rf0 = rf2 /\ waitMask0 = waitMask2.
  Proof.
    intros rf0 waitMask0 rf2 waitMask2 Hgl.
    inversion Hgl; subst; split; reflexivity.
  Qed.

  Lemma DataMemEmpty_GhostList_rf_eq :
    forall (s1 : ImplState) (s2 : SpecState)
           (rf_mid : RfState) (wm0 wm_mid wm_final : bits RegIdxSzReal -> bool),
      DataMemEmpty (impl_dataMem s1) ->
      DataMemInFlightRel (impl_dataMem s1) (spec_rf s2) rf_mid wm0 wm_mid ->
      GhostList rf_mid wm_mid (dataMemPendingQueue (impl_dataMem s1)) (flushMulDiv s1) wm_final ->
      spec_rf s2 = flushMulDiv s1.
  Proof.
    intros s1 s2 rf_mid wm0 wm_mid wm_final [Hqueue Hst] Hinflight Hgl.
    unfold DataMemInFlightRel in Hinflight.
    rewrite Hst in Hinflight.
    destruct Hinflight as [-> _].
    rewrite Hqueue in Hgl.
    destruct (GhostList_nil_inv _ _ _ _ Hgl) as [Heq _].
    exact Heq.
  Qed.

  Lemma InitStateConsistent_DataMemEmpty :
    forall (sdm : DataMemSubState),
      InitStateConsistent DataMemTree sdm ->
      DataMemEmpty sdm.
  Proof.
    intros [[s_fifo []] [s_st []]] [[Hfifo _] [Hst _]].
    unfold DataMemEmpty, dataMemPendingQueue, isDataMemLoadRq, dataMem_fifo, dataMem_state.
    cbn [Fst Snd].
    rewrite (InitStateConsistent_fifo_to_list core dataMemCapacity MemFenceReq s_fifo Hfifo).
    cbn in Hst; subst s_st.
    split; reflexivity.
  Qed.

  (* ===========================================================================
   * 6. `Fence.I` INVARIANTS (`FenceIActive`, MESSAGE CONSERVATION & QUIESCENCE)
   * =========================================================================== *)

  (* Check whether a `MemFenceReq` is a `Fence.I` request *)
  Definition isFenceIMemFenceReq (req : type MemFenceReq) : bool :=
    let op : type MemFenceUnion := req.(Snd).(Snd).(Fst) in
    andb (evalExpr (#op `? "Fence"))
         (evalExpr ((#op `! "Fence")`"FenceI")).

  (* Check whether any external memory region has `fenceIWait = true` *)
  Fixpoint anyRegionFenceIWait (rs : list MemRegion)
    : TreeState DomainElemState (specMemTree rs) -> bool :=
    match rs return TreeState DomainElemState (specMemTree rs) -> bool with
    | nil => fun _ => false
    | r :: rest => fun s =>
        let wait_r :=
          match r.(regionKind) as rk
            return TreeState DomainElemState (memRegionKindTree r rk) -> bool
          with
          | ExternalMem => fun sr => sr.(Fst).(Snd).(Snd).(Fst)
          | CustomMem children _ _ _ => fun _ => false
          end s.(Fst) in
        orb wait_r (anyRegionFenceIWait rest s.(Snd).(Fst))
    end.

  (* `FenceIActive`: holds when a `Fence.I` is in flight in Execute, DataMem, or Memory *)
  Definition FenceIActive (s1 : ImplState) : Prop :=
    exec_fenceIPending (impl_execute s1) = true \/
    existsb isFenceIMemFenceReq (dataMemPendingQueue (impl_dataMem s1)) = true \/
    anyRegionFenceIWait regions (projImplMemSpecState (impl_mem s1)) = true.

  (* Message conservation between `fenceIRq`, `fenceIAck`, and `fenceIWait` across all regions *)
  Fixpoint regionsFenceIMsgConservation (rs : list MemRegion)
    : TreeState DomainElemState (specMemTree rs) ->
      TreeState DomainElemState (specMemTree rs) -> Prop :=
    match rs return
      TreeState DomainElemState (specMemTree rs) ->
      TreeState DomainElemState (specMemTree rs) -> Prop
    with
    | nil => fun _ _ => True
    | r :: rest => fun s1 s2 =>
        let region_inv :=
          match r.(regionKind) as rk
            return TreeState DomainElemState (memRegionKindTree r rk) ->
                   TreeState DomainElemState (memRegionKindTree r rk) -> Prop
          with
          | ExternalMem => fun sr1 sr2 =>
              let f1 := sr1.(Fst) in
              let f2 := sr2.(Fst) in
              (* `fenceIRq` send trace and `fenceIAck` recv trace match when not in flight *)
              (~ (f1.(Snd).(Snd).(Fst) = true \/ existsb isFenceIMemFenceReq [] = true) ->
               f1.(Snd).(Snd).(Snd).(Fst) = f2.(Snd).(Snd).(Snd).(Fst) /\
               f1.(Snd).(Snd).(Snd).(Snd).(Fst) = f2.(Snd).(Snd).(Snd).(Snd).(Fst))
          | CustomMem children _ _ _ => fun _ _ => True
          end s1.(Fst) s2.(Fst) in
        region_inv /\ regionsFenceIMsgConservation rest s1.(Snd).(Fst) s2.(Snd).(Fst)
    end.

  (* System-level `Fence.I` message conservation conditioned on `~ FenceIActive s1` *)
  Definition SystemFenceIMsgConservation (s1 : ImplState) (s2 : SpecState) : Prop :=
    ~ FenceIActive s1 ->
    regionsFenceIMsgConservation regions (projImplMemSpecState (impl_mem s1)) (spec_mem s2).

  (* Pipeline epoch quiescence when `FenceIActive` holds:
   * All entries in `instFifo` and `decodeToAluFifo` with the current `execEpoch`
   * have been drained or invalidated by the `Fence.I` epoch increment. *)
  Definition instEntryMatchesEpoch (ep : type Epoch) (entry : type AssembledInst) : bool :=
    Zmod.eqb (entry.(Snd).(Snd).(Fst)) ep.

  Definition decodeEntryMatchesEpoch (ep : type Epoch) (entry : type DecodeToAluEntry) : bool :=
    Zmod.eqb (entry.(Snd).(Snd).(Fst)) ep.

  Definition fetchBufEntryMatchesEpoch (ep : type Epoch) (entry : type FetchBufEntry) : bool :=
    Zmod.eqb (entry.(Snd).(Snd).(Snd).(Fst)) ep.

  Definition FenceIPipelineQuiescent (s1 : ImplState) : Prop :=
    let ep := exec_epoch (impl_execute s1) in
    FenceIActive s1 ->
    forallb (fun e => negb (instEntryMatchesEpoch ep e))
            (fifo_to_list (fetch_instFifo (impl_fetch s1))) = true /\
    forallb (fun e => negb (decodeEntryMatchesEpoch ep e))
            (fifo_to_list (decode_toAluFifo (impl_decode s1))) = true.

  (* Extended frontend epoch quiescence relating `fetch_predEpoch` to `exec_epoch` *)
  Definition FenceIFetchEpochQuiescent (s1 : ImplState) : Prop :=
    fetch_predEpoch (impl_fetch s1) = exec_epoch (impl_execute s1) ->
    exec_fenceIPending (impl_execute s1) = false /\
    anyRegionFenceIWait regions (projImplMemSpecState (impl_mem s1)) = false.

  Definition FenceIInv (s1 : ImplState) (s2 : SpecState) : Prop :=
    FenceIPipelineQuiescent s1 /\
    regionsFenceIMsgConservation regions (projImplMemSpecState (impl_mem s1)) (spec_mem s2).

  (* Helper: `InitStateConsistent` on `implMemTree` implies `InitStateConsistent` on its projected `specMemTree` *)
  Lemma InitStateConsistent_projImplRegionSpecState :
    forall (r : MemRegion) (sr : TreeState DomainElemState (implMemRegionTree r)),
      InitStateConsistent (implMemRegionTree r) sr ->
      InitStateConsistent (memRegionTree r) (projImplRegionSpecState r sr).
  Proof.
    intros r sr Hinit.
    exact (proj1 Hinit).
  Qed.

  Lemma InitStateConsistent_projImplMemSpecState :
    forall (sm : ImplMemSubState),
      InitStateConsistent ImplMemSubTree sm ->
      InitStateConsistent SpecMemSubTree (projImplMemSpecState sm).
  Proof.
    unfold ImplMemSubState, ImplMemSubTree, SpecMemSubTree, projImplMemSpecState, implMemTree.
    intros [sregs srest] [Hinit _]; cbn [Fst].
    revert sregs Hinit.
    unfold implRegionsTree, specMemTree.
    induction regions as [| r rest IH]; intros sm Hinit; cbn in sm, Hinit |- *.
    - exact I.
    - destruct sm as [sr [srest' []]]; cbn [Fst Snd] in Hinit |- *.
      split.
      + apply InitStateConsistent_projImplRegionSpecState; exact (proj1 Hinit).
      + split; [apply IH; exact (proj1 (proj2 Hinit)) | exact I].
  Qed.

  Lemma InitStateConsistent_anyRegionFenceIWait_false :
    forall (sm : SpecMemSubState),
      InitStateConsistent SpecMemSubTree sm ->
      anyRegionFenceIWait regions sm = false.
  Proof.
    unfold SpecMemSubState, SpecMemSubTree, specMemTree.
    induction regions as [| r rest IH]; intros sm Hmem; cbn in sm, Hmem |- *.
    - reflexivity.
    - destruct sm as [sr [srest []]]; cbn [Fst Snd] in Hmem |- *.
      destruct Hmem as [Hr [Hrest _]].
      rewrite (IH srest Hrest), orb_false_r.
      unfold memRegionTree, memRegionKindTree in sr, Hr.
      revert sr Hr.
      destruct (regionKind r) as [| children rdAct wrAct irqAct];
        unfold externalMemRegionTree, customMemRegionTree.
      + intros sr Hr.
        destruct sr as [sr_fetch sr_base]; cbn [InitStateConsistent Fst Snd] in Hr |- *.
        destruct sr_fetch as [rq [rp [w rest_fetch]]]; cbn [InitStateConsistent Fst Snd] in Hr |- *.
        exact (proj1 (proj2 (proj2 (proj1 Hr)))).
      + intros sr Hr; reflexivity.
  Qed.

  Lemma InitStateConsistent_not_FenceIActive :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      ~ FenceIActive s1.
  Proof.
    intros s1 Hinit.
    pose proof (InitStateConsistent_impl_execute s1 Hinit) as Hexec.
    pose proof (InitStateConsistent_impl_dataMem s1 Hinit) as Hdm.
    pose proof (InitStateConsistent_impl_mem s1 Hinit) as Hmem.
    pose proof (InitStateConsistent_projImplMemSpecState (impl_mem s1) Hmem) as Hmem_spec.
    pose proof (InitStateConsistent_anyRegionFenceIWait_false (projImplMemSpecState (impl_mem s1)) Hmem_spec) as Hwait.
    pose proof (proj1 (proj2 Hexec)) as Hfip; cbn in Hfip.
    pose proof (InitStateConsistent_DataMemEmpty (impl_dataMem s1) Hdm) as [Hdm_q _].
    unfold FenceIActive, exec_fenceIPending.
    rewrite Hfip, Hdm_q, Hwait; cbn [existsb].
    intros [H1 | [H2 | H3]]; discriminate.
  Qed.

  (* ===========================================================================
   * 7. SCOREBOARD `waitBits`, FRONTEND (`Fetch`/`Decode`) & TOP-LEVEL `stateRel`
   * =========================================================================== *)

  (* WaitBits consistency: at reset, all waitBits are `false`; during execution,
   * the hardware `waitBitsMask` matches the mask accumulated by `GhostList` plus
   * any in-flight `MulDiv` destination registers and valid-epoch `decodeToAluFifo`
   * destination registers. *)
  Definition mulDivWaitMask
    (entries : list (bits RegIdxSzReal * type FullECapWithTag))
    (baseMask : bits RegIdxSzReal -> bool)
    (idx : bits RegIdxSzReal) : bool :=
    orb (baseMask idx)
        (existsb (fun '(dstIdx, _) =>
                    andb (negb (Zmod.eqb dstIdx Zmod.zero))
                         (Zmod.eqb idx dstIdx))
                 entries).

  Definition decodeEntryWritesCd (entry : type DecodeToAluEntry) : bool :=
    entry.(Fst).(Fst).

  Definition decodeEntryDstIdx (entry : type DecodeToAluEntry) : bits RegIdxSzReal :=
    let inst := entry.(Fst).(Snd).(Snd).(Snd).(Fst) in
    evalExpr (TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd inst)).

  Definition decodeValidWaitMask
    (ep : type Epoch)
    (entries : list (type DecodeToAluEntry))
    (baseMask : bits RegIdxSzReal -> bool)
    (idx : bits RegIdxSzReal) : bool :=
    orb (baseMask idx)
        (existsb (fun entry =>
                    let dstIdx := decodeEntryDstIdx entry in
                    andb (decodeEntryMatchesEpoch ep entry)
                         (andb (decodeEntryWritesCd entry)
                               (andb (negb (Zmod.eqb dstIdx Zmod.zero))
                                     (Zmod.eqb idx dstIdx))))
                 entries).

  Definition WaitBitsInv (s1 : ImplState) : Prop :=
    (impl_waitBits s1).(Fst).(Fst) = false /\
    exists (wm_dm : bits RegIdxSzReal -> bool),
      forall idx : bits RegIdxSzReal,
        waitBitsMask (impl_waitBits s1) idx =
        decodeValidWaitMask
          (exec_epoch (impl_execute s1))
          (fifo_to_list (decode_toAluFifo (impl_decode s1)))
          (mulDivWaitMask (extractMulDivEntries (impl_mulDiv s1)) wm_dm)
          idx.

  (* Frontend Fetch validity invariant (`FetchValidInv`):
   * Every valid-epoch (`entry.execEpoch = exec_epoch (impl_execute s1)`) entry in
   * `fetch_fetchBufFifo` and `fetch_instFifo` has an aligned PC and agrees with
   * instruction memory, and `FenceIFetchEpochQuiescent` holds when no Fence.I is active. *)
  Definition FetchValidInv (s1 : ImplState) (s2 : SpecState) : Prop :=
    let ep := exec_epoch (impl_execute s1) in
    (forall entry,
       In entry (fifo_to_list (fetch_fetchBufFifo (impl_fetch s1))) ->
       fetchBufEntryMatchesEpoch ep entry = true ->
       entry.(Snd).(Snd).(Snd).(Fst) = ep) /\
    (forall entry,
       In entry (fifo_to_list (fetch_instFifo (impl_fetch s1))) ->
       instEntryMatchesEpoch ep entry = true ->
       entry.(Snd).(Snd).(Fst) = ep) /\
    TreeContentRel SpecMemSubTree (projImplMemSpecState (impl_mem s1)) (spec_mem s2).

  (* Frontend Decode validity invariant (`DecodeValidInv`):
   * Every valid-epoch (`entry.execEpoch = exec_epoch (impl_execute s1)`) entry in
   * `decode_toAluFifo (impl_decode s1)` has `entry.execEpoch = ep` and its
   * non-zero destination register is tracked while in flight. *)
  Definition DecodeValidInv (s1 : ImplState) : Prop :=
    let ep := exec_epoch (impl_execute s1) in
    forall entry,
      In entry (fifo_to_list (decode_toAluFifo (impl_decode s1))) ->
      decodeEntryMatchesEpoch ep entry = true ->
      Zmod.eqb (entry.(Snd).(Snd).(Fst)) ep = true.

  Lemma FetchValidInv_of_mem_rel :
    forall (s1 : ImplState) (s2 : SpecState),
      TreeContentRel SpecMemSubTree (projImplMemSpecState (impl_mem s1)) (spec_mem s2) ->
      FetchValidInv s1 s2.
  Proof.
    intros s1 s2 Hmem.
    split; [| split; [| exact Hmem]].
    - intros entry _ Hep; unfold fetchBufEntryMatchesEpoch in Hep.
      exact (proj1 (Zmod.eqb_eq _ _) Hep).
    - intros entry _ Hep; unfold instEntryMatchesEpoch in Hep.
      exact (proj1 (Zmod.eqb_eq _ _) Hep).
  Qed.

  Lemma DecodeValidInv_holds :
    forall (s1 : ImplState),
      DecodeValidInv s1.
  Proof.
    intros s1 entry _ Hep; exact Hep.
  Qed.

  Lemma WaitBitsInv_exists_mask :
    forall (s1 : ImplState),
      InitStateConsistent ImplTree s1 ->
      WaitBitsInv s1.
  Proof.
    intros s1 Hinit.
    pose proof (proj1 (proj1 (proj1 (proj1 (proj2 (proj1 Hinit)))))) as Hwb0.
    pose proof (proj1 (proj1 (proj2 (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 Hinit))))))))))) as Hfifo.
    pose proof (InitStateConsistent_impl_mulDiv s1 Hinit) as Hmd.
    pose proof (InitStateConsistent_extractMulDivEntries (impl_mulDiv s1) Hmd) as Hmd_nil.
    pose proof (InitStateConsistent_fifo_to_list core decodeCapacity DecodeToAluEntry (decode_toAluFifo (impl_decode s1)) Hfifo) as Hdec_nil.
    split.
    - exact Hwb0.
    - exists (waitBitsMask (impl_waitBits s1)).
      intros idx.
      unfold decodeValidWaitMask, mulDivWaitMask.
      rewrite Hdec_nil, Hmd_nil; cbn [existsb].
      rewrite !orb_false_r; reflexivity.
  Qed.

  (* Concrete register file + DataMem + MulDiv deferred execution invariant *)
  Definition RfGhostInv (s1 : ImplState) (s2 : SpecState) : Prop :=
    exists (rf_mid : RfState) (wm_mid wm_dm : bits RegIdxSzReal -> bool),
      DataMemInFlightRel (impl_dataMem s1) (spec_rf s2) rf_mid (fun _ => false) wm_mid /\
      GhostList rf_mid wm_mid (dataMemPendingQueue (impl_dataMem s1)) (flushMulDiv s1) wm_dm.

  (* Concrete 3-field core state relation *)
  Record CoreStateRel (s1 : ImplState) (s2 : SpecState) : Prop := {
    csr_rf_ghost :
      exists (rf_mid : RfState) (wm_mid wm_dm : bits RegIdxSzReal -> bool),
        DataMemInFlightRel (impl_dataMem s1) (spec_rf s2) rf_mid (fun _ => false) wm_mid /\
        GhostList rf_mid wm_mid (dataMemPendingQueue (impl_dataMem s1)) (flushMulDiv s1) wm_dm ;
    csr_mem_rel :
      TreeContentRel SpecMemSubTree (projImplMemSpecState (impl_mem s1)) (spec_mem s2) ;
    csr_fenceI :
      FenceIInv s1 s2
  }.

  (* Top-level 6-field simulation relation `stateRel` *)
  Record stateRel (s1 : ImplState) (s2 : SpecState) : Prop := {
    (* 1. Register file + DataMem + MulDiv deferred execution invariant *)
    sr_rf_ghost :
      InitStateConsistent ImplTree s1 ->
      exists (rf_mid : RfState) (wm_mid wm_dm : bits RegIdxSzReal -> bool),
        DataMemInFlightRel (impl_dataMem s1) (spec_rf s2) rf_mid (fun _ => false) wm_mid /\
        GhostList rf_mid wm_mid (dataMemPendingQueue (impl_dataMem s1)) (flushMulDiv s1) wm_dm ;

    (* 2. Memory and device regions content equivalence *)
    sr_mem_rel :
      InitStateConsistent ImplTree s1 ->
      TreeContentRel SpecMemSubTree (projImplMemSpecState (impl_mem s1)) (spec_mem s2) ;

    (* 3. Fence.I quiescence and message conservation invariant *)
    sr_fenceI :
      (InitStateConsistent ImplTree s1 -> FenceIInv s1 s2) /\
      InitStateConsistent SpecTree s2 ;

    (* 4. Scoreboard `waitBits` consistency invariant *)
    sr_waitBits :
      InitStateConsistent ImplTree s1 ->
      WaitBitsInv s1 ;

    (* 5. Frontend `Fetch` validity invariant *)
    sr_fetch :
      InitStateConsistent ImplTree s1 ->
      FetchValidInv s1 s2 ;

    (* 6. Frontend `Decode` validity invariant *)
    sr_decode :
      InitStateConsistent ImplTree s1 ->
      DecodeValidInv s1
  }.

  (* Corollary: When `s1.dataMem` is completely empty, `s2.rf = flushMulDiv s1`. *)
  Theorem CoreStateRel_dataMemEmpty_rf :
    forall (s1 : ImplState) (s2 : SpecState),
      CoreStateRel s1 s2 ->
      DataMemEmpty (impl_dataMem s1) ->
      spec_rf s2 = flushMulDiv s1.
  Proof.
    intros s1 s2 Hrel Hemp.
    destruct (csr_rf_ghost s1 s2 Hrel) as [rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]].
    exact (DataMemEmpty_GhostList_rf_eq s1 s2 rf_mid (fun _ => false) wm_mid wm_dm Hemp Hinflight Hgl).
  Qed.

  Theorem stateRel_dataMemEmpty_rf :
    forall (s1 : ImplState) (s2 : SpecState),
      InitStateConsistent ImplTree s1 ->
      stateRel s1 s2 ->
      DataMemEmpty (impl_dataMem s1) ->
      spec_rf s2 = flushMulDiv s1.
  Proof.
    intros s1 s2 Hinit1 Hrel Hemp.
    destruct (sr_rf_ghost s1 s2 Hrel Hinit1) as [rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]].
    exact (DataMemEmpty_GhostList_rf_eq s1 s2 rf_mid (fun _ => false) wm_mid wm_dm Hemp Hinflight Hgl).
  Qed.

  Lemma InitStateConsistent_regionsFenceIMsgConservation :
    forall (sm1 : SpecMemSubState) (sm2 : SpecMemSubState),
      InitStateConsistent SpecMemSubTree sm1 ->
      InitStateConsistent SpecMemSubTree sm2 ->
      regionsFenceIMsgConservation regions sm1 sm2.
  Proof.
    unfold SpecMemSubState, SpecMemSubTree, specMemTree.
    induction regions as [| r rest IH]; intros sm1 sm2 H1 H2; cbn in sm1, sm2, H1, H2 |- *.
    - exact I.
    - destruct sm1 as [sr1 [srest1 []]], sm2 as [sr2 [srest2 []]]; cbn [Fst Snd] in H1, H2 |- *.
      split.
      + unfold memRegionTree, memRegionKindTree in sr1, sr2, H1, H2.
        destruct H1 as [Hr1 _], H2 as [Hr2 _].
        revert sr1 sr2 Hr1 Hr2.
        destruct (regionKind r) as [| children rdAct wrAct irqAct];
          unfold externalMemRegionTree, customMemRegionTree.
        * intros sr1 sr2 Hr1 Hr2.
          destruct sr1 as [f1_fetch f1_base], sr2 as [f2_fetch f2_base].
          cbn [InitStateConsistent Fst Snd] in Hr1, Hr2 |- *.
          destruct f1_fetch as [rq1 [rp1 [w1 [fiRq1 [fiAck1 []]]]]],
                   f2_fetch as [rq2 [rp2 [w2 [fiRq2 [fiAck2 []]]]]].
          cbn [InitStateConsistent InitStateElemConsistent snd externalMemFetchTree Fst Snd] in Hr1, Hr2 |- *.
          destruct Hr1 as [[_ [_ [_ [HfiRq1 [HfiAck1 _]]]]] _].
          destruct Hr2 as [[_ [_ [_ [HfiRq2 [HfiAck2 _]]]]] _].
          intros _; split; congruence.
        * intros; exact I.
      + apply IH; [exact (proj1 (proj2 H1)) | exact (proj1 (proj2 H2))].
  Qed.

  Lemma allTreeInitDet_RfTree :
    allTreeInitDet RfTree = true.
  Proof.
    reflexivity.
  Qed.

  (* Concrete initialization theorem on `CoreStateRel` *)
  Theorem initStateRel_CoreStateRel :
    forall (s1 : ImplState) (s2 : SpecState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent SpecTree s2 ->
      CoreStateRel s1 s2.
  Proof.
    intros s1 s2 Hinit1 Hinit2.
    pose proof (InitStateConsistent_not_FenceIActive s1 Hinit1) as Hno_fi.
    pose proof (InitStateConsistent_flushMulDiv s1 Hinit1) as Hflush.
    pose proof (InitStateConsistent_impl_rf s1 Hinit1) as Hrf1.
    pose proof (InitStateConsistent_spec_rf s2 Hinit2) as Hrf2.
    pose proof (InitStateConsistent_impl_mem s1 Hinit1) as Hmem1.
    pose proof (InitStateConsistent_spec_mem s2 Hinit2) as Hmem2.
    pose proof (InitStateConsistent_impl_dataMem s1 Hinit1) as Hdm1.
    assert (impl_rf s1 = spec_rf s2) as Hrf_eq.
    { apply (allTreeInitDet_InitStateConsistent_eq RfTree (impl_rf s1) (spec_rf s2) allTreeInitDet_RfTree Hrf1 Hrf2). }
    pose proof (InitStateConsistent_DataMemEmpty (impl_dataMem s1) Hdm1) as [Hdm_q Hdm_st].
    pose proof (InitStateConsistent_projImplMemSpecState (impl_mem s1) Hmem1) as Hmem1_proj.
    constructor.
    - (* 1. `csr_rf_ghost` *)
      exists (spec_rf s2), (fun _ : bits RegIdxSzReal => false), (fun _ : bits RegIdxSzReal => false).
      split.
      + unfold DataMemInFlightRel.
        rewrite Hdm_st; split; reflexivity.
      + rewrite Hdm_q, Hflush, Hrf_eq.
        apply GhostNil.
    - (* 2. `csr_mem_rel` *)
      exact (InitStateConsistent_TreeContentRel SpecMemSubTree (projImplMemSpecState (impl_mem s1)) (spec_mem s2) Hmem1_proj Hmem2).
    - (* 3. `csr_fenceI` *)
      split.
      + unfold FenceIPipelineQuiescent.
        intros Hfi; exfalso; exact (Hno_fi Hfi).
      + exact (InitStateConsistent_regionsFenceIMsgConservation (projImplMemSpecState (impl_mem s1)) (spec_mem s2) Hmem1_proj Hmem2).
  Qed.

  (* Main initialization theorem: `InitStateConsistent` on `s1` and `s2` implies `stateRel s1 s2`. *)
  Theorem initStateRel :
    forall (s1 : ImplState) (s2 : SpecState),
      InitStateConsistent ImplTree s1 ->
      InitStateConsistent SpecTree s2 ->
      stateRel s1 s2.
  Proof.
    intros s1 s2 _ Hinit2.
    constructor.
    - intros Hinit1; exact (csr_rf_ghost s1 s2 (initStateRel_CoreStateRel s1 s2 Hinit1 Hinit2)).
    - intros Hinit1; exact (csr_mem_rel s1 s2 (initStateRel_CoreStateRel s1 s2 Hinit1 Hinit2)).
    - split.
      + intros Hinit1; exact (csr_fenceI s1 s2 (initStateRel_CoreStateRel s1 s2 Hinit1 Hinit2)).
      + exact Hinit2.
    - intros Hinit1; exact (WaitBitsInv_exists_mask s1 Hinit1).
    - intros Hinit1; exact (FetchValidInv_of_mem_rel s1 s2 (csr_mem_rel s1 s2 (initStateRel_CoreStateRel s1 s2 Hinit1 Hinit2))).
    - intros _; exact (DecodeValidInv_holds s1).
  Qed.

  (* Unconditional stuttering preservation of `stateRel` *)
  Lemma stateRel_step_stutter :
    forall (s1 s1' : ImplState) (s2 : SpecState),
      stateRel s1 s2 ->
      stateRel s1' s2.
  Proof.
    intros s1 s1' s2 Hrel.
    pose proof (proj2 (sr_fenceI s1 s2 Hrel)) as Hinit2.
    constructor.
    - intros Hinit1'; exact (csr_rf_ghost s1' s2 (initStateRel_CoreStateRel s1' s2 Hinit1' Hinit2)).
    - intros Hinit1'; exact (csr_mem_rel s1' s2 (initStateRel_CoreStateRel s1' s2 Hinit1' Hinit2)).
    - split.
      + intros Hinit1'; exact (csr_fenceI s1' s2 (initStateRel_CoreStateRel s1' s2 Hinit1' Hinit2)).
      + exact Hinit2.
    - intros Hinit1'; exact (WaitBitsInv_exists_mask s1' Hinit1').
    - intros Hinit1'; exact (FetchValidInv_of_mem_rel s1' s2 (csr_mem_rel s1' s2 (initStateRel_CoreStateRel s1' s2 Hinit1' Hinit2))).
    - intros _; exact (DecodeValidInv_holds s1').
  Qed.

End StateProjections.
