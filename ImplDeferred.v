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

From Stdlib Require Import String List ZArith.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines FunctionalUnits ImplDefines ImplMemory Alu Fifo SpecFetchMemory.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section DeferredStages.
  Variable fetchCapacity deferredCapacity : nat.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation tree := (coreTree memTree fetchCapacity deferredCapacity).
  Local Notation capacity := deferredCapacity.

  Definition np_rf : NodePath tree :=
    getNodePath tree "core.rf".

  Definition np_mem : NodePath tree :=
    embedNodeIntoPath (getNodePath tree "core.mem") singletonChildPath.

  Definition np_inputFifo : NodePath tree :=
    getNodePath tree "core.deferred.inputBuf.fifo".

  Definition np_loadFifo : NodePath tree :=
    getNodePath tree "core.deferred.loadBuf.fifo".

  Definition np_revFifo : NodePath tree :=
    getNodePath tree "core.deferred.revBuf.fifo".

  (* =========================================================================
   * STAGE 1: loadRqOrStoreOrFence
   *
   * - Dequeues DeferredReq from inputFifo.
   * - Uses dispatchDeferredReq for combinational command extraction.
   * - Store: writes to memory via mem_writeMem if canStoreMemRq.
   * - Load:  issues mem_readMemRq, enqueues PendingLoad if canLoadMemRq.
   * - Fence: drains pending loads/revocations if needed, issues mem_fence_req.
   * ========================================================================= *)
  Definition loadRqOrStoreOrFence : Action ty tree (Bit 0) :=
    LetA inputHead           : Option DeferredReq <- liftAction np_inputFifo (@first capacity DeferredReq ty) ;
    LetA outputBuffer_isFull : Bool               <- liftAction np_loadFifo (@isFull capacity PendingLoad ty) ;

    Let inputBuffer_isValid  : Bool               <- #inputHead `? "Some" ;

    If #inputBuffer_isValid Then (
      Let req     : DeferredReq    <- #inputHead `! "Some" ;
      LetL action : DeferredAction <- dispatchDeferredReq req (memIfc ty).(mem_needsRotation) ;

      If (##action `? "Mem") Then (
        Let memAct : MemAction <- ##action `! "Mem" ;

        If (##memAct `? "Store") Then (
          (* --- STORE ACTION: requires canStoreMemRq --- *)
          Let st        : StoreCmd       <- ##memAct `! "Store" ;
          LetA canStore : Bool           <- liftAction np_mem ((memIfc ty).(mem_canStoreMemRq)) ;
          If #canStore Then (
            Act (liftAction np_mem ((memIfc ty).(mem_writeMem) (##st`"addr") (##st`"stVal") (##st`"memSize"))) ;
            liftAction np_inputFifo (@deq capacity DeferredReq ty)
          ) ;
          Retv
        ) Else (
          (* --- LOAD ACTION: requires canLoadMemRq AND loadFifo is NOT full --- *)
          Let ld      : LoadCmd     <- ##memAct `! "Load" ;
          Let pending : PendingLoad <- ##ld`"pending" ;
          LetA canLoad : Bool       <- liftAction np_mem ((memIfc ty).(mem_canLoadMemRq)) ;
          If (And [ #canLoad ; Not #outputBuffer_isFull ]) Then (
            Act (liftAction np_mem ((memIfc ty).(mem_readMemRq) (##ld`"addr"))) ;
            Act (liftAction np_loadFifo (@enq capacity PendingLoad ty pending)) ;
            liftAction np_inputFifo (@deq capacity DeferredReq ty)
          ) ;
          Retv
        ) ;
        Retv
      ) Else (
        (* --- FENCE ACTION: requires canFenceMemRq AND drained queues if needsEmpty --- *)
        Let fn        : FenceCmd <- ##action `! "Fence" ;
        LetA canFence : Bool     <- liftAction np_mem ((memIfc ty).(mem_canFenceMemRq)) ;
        If #canFence Then (
          LetA outputBuffer_isEmpty : Bool <- liftAction np_loadFifo (@isEmpty capacity PendingLoad ty) ;
          LetA rev_isEmpty          : Bool <- liftAction np_revFifo (@isEmpty capacity PendingRev ty) ;
          If (Or [ Not (##fn`"needsEmpty") ; And [ #outputBuffer_isEmpty ; #rev_isEmpty ] ]) Then (
            Act (liftAction np_mem ((memIfc ty).(mem_fence_req) (##fn`"fenceOp"))) ;
            liftAction np_inputFifo (@deq capacity DeferredReq ty)
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: loadRpAndWritebackOrRevRq
   *
   * - Dequeues PendingLoad from loadFifo.
   * - Uses dispatchLoadResponse for pure combinational response handling.
   *     - RevLookup: issues mem_readRevBitRq on ldECap.base, enqueues PendingRev.
   *     - Writeback: writes back directly to Register File.
   * ========================================================================= *)
  Definition loadRpAndWritebackOrRevRq : Action ty tree (Bit 0) :=
    LetA inputHead           : Option PendingLoad <- liftAction np_loadFifo (@first capacity PendingLoad ty) ;
    LetA outputBuffer_isFull : Bool               <- liftAction np_revFifo (@isFull capacity PendingRev ty) ;

    Let inputBuffer_isValid  : Bool               <- #inputHead `? "Some" ;

    If #inputBuffer_isValid Then (
      LetA isMemRpValid : Bool <- liftAction np_mem ((memIfc ty).(mem_isMemRpValid)) ;

      If #isMemRpValid Then (
        Let pl          : PendingLoad      <- #inputHead `! "Some" ;
        LetA memVal     : FullCapWithTag   <- liftAction np_mem ((memIfc ty).(mem_getMemRp)) ;
        LetL outcome    : LoadOutcome      <- dispatchLoadResponse pl memVal (memIfc ty).(mem_needsRotation) ;

        If (#outcome `? "RevLookup") Then (
          (* 1A. Tagged Memory Capability -> Revocation Lookup *)
          Let revInfo     : RevCmd     <- #outcome `! "RevLookup" ;
          Let pendingRev  : PendingRev <- ##revInfo`"pendingRev" ;
          LetA canReadRev : Bool       <- liftAction np_mem ((memIfc ty).(mem_canReadRevBitRq)) ;

          If (And [ #canReadRev ; Not #outputBuffer_isFull ]) Then (
            Act (liftAction np_mem ((memIfc ty).(mem_readRevBitRq) (##revInfo`"base"))) ;
            Act (liftAction np_revFifo (@enq capacity PendingRev ty pendingRev)) ;
            liftAction np_loadFifo (@deq capacity PendingLoad ty)
          ) ;
          Retv
        ) Else (
          (* 1B. Sealing Capability, Untagged Full-Cap, or Sub-Word Load -> Direct Writeback *)
          Let wbInfo : WbCmd <- #outcome `! "Writeback" ;
          If (isNotZero (##wbInfo`"dstIdx")) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))
          ) ;
          liftAction np_loadFifo (@deq capacity PendingLoad ty)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 3: revRpAndWriteBack
   *
   * - Dequeues PendingRev from revFifo.
   * - Uses dispatchRevResponse for pure combinational final writeback value.
   * - Writes back final capability to Register File.
   * ========================================================================= *)
  Definition revRpAndWriteBack : Action ty tree (Bit 0) :=
    LetA inputHead          : Option PendingRev <- liftAction np_revFifo (@first capacity PendingRev ty) ;
    Let inputBuffer_isValid : Bool              <- #inputHead `? "Some" ;

    If #inputBuffer_isValid Then (
      LetA isRevRpValid : Bool <- liftAction np_mem ((memIfc ty).(mem_isRevBitRpValid)) ;

      If #isRevRpValid Then (
        Let  pr       : PendingRev      <- #inputHead `! "Some" ;
        LetA revBit   : Bool            <- liftAction np_mem ((memIfc ty).(mem_getRevBitRp)) ;
        LetL wbInfo   : WbCmd           <- dispatchRevResponse pr revBit ;
        If (isNotZero (##wbInfo`"dstIdx")) Then (
          liftAction np_rf (writeRegsList gprPathsWithKind (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))
        ) ;
        liftAction np_revFifo (@deq capacity PendingRev ty)
      ) ;
      Retv
    ) ;
    Retv.

  Definition deferredRuleList : list (Action ty tree (Bit 0)) := [
    revRpAndWriteBack ;
    loadRpAndWritebackOrRevRq ;
    loadRqOrStoreOrFence
  ].

End DeferredStages.
