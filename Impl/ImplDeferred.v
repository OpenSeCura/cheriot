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
From Cheriot Require Import SpecDefines FunctionalUnits ImplDefines ImplDevice Alu Fifo SpecFetchDeferred SpecMulDiv ImplMulDiv.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section DeferredStages.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable tohostAddr : Z.
  Variable fetchCapacity deferredCapacity : nat.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation coreTree := (coreTree dom pcAddrInit memTree fetchCapacity deferredCapacity).
  Local Notation capacity := deferredCapacity.
  Local Notation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).
  Local Notation updateMshwmOnStore := (updateMshwmOnStore dom pcAddrInit).
  Local Notation incrementMinstret := (incrementMinstret dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits").

  Definition np_mem : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_inputFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.inputBuf.fifo").

  Definition np_loadFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.loadBuf.fifo").

  Definition np_revRqFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.revRqBuf.fifo").

  Definition np_revFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.revBuf.fifo").

  Definition np_mulDiv : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.mulDiv").

  (* =========================================================================
   * STAGE 1: loadRqOrStoreOrFence
   *
   * - Dequeues DeferredReq from inputFifo.
   * - Uses dispatchDeferredReq for combinational command extraction.
   * - Store: writes to memory via mem_writeMem.
   * - Load:  issues mem_readMemRq, enqueues PendingLoad if accepted.
   * - Fence: drains pending loads/revocations if needed, issues mem_fence_req.
   * ========================================================================= *)
  Definition loadRqOrStoreOrFence : Action ty coreTree (Bit 0) :=
    LetA inputHead           : Option DeferredReq <- liftAction np_inputFifo (@first dom capacity DeferredReq ty) ;
    LetA outputBuffer_isFull : Bool               <- liftAction np_loadFifo (@isFull dom capacity LoadCmd ty) ;
    LetA revRq_isEmpty       : Bool               <- liftAction np_revRqFifo (@isEmpty dom capacity RevCmd ty) ;

    Let inputBuffer_isValid  : Bool               <- #inputHead `? "Some" ;

    If #inputBuffer_isValid Then (
      Let req     : DeferredReq    <- #inputHead `! "Some" ;
      LetL action : DeferredAction <- dispatchDeferredReq req false ;

      If (##action `? "MemFence") Then (
        Let mfAct : MemFenceAction <- ##action `! "MemFence" ;

        If (##mfAct `? "Mem") Then (
          Let memAct : MemAction <- ##mfAct `! "Mem" ;

          If (##memAct `? "Store") Then (
            (* --- STORE ACTION --- *)
            Let st        : StoreCmd                  <- ##memAct `! "Store" ;
            Let stAddr    : Addr                      <- ##st`"addr" ;
            Let stVal     : FullCapWithTag            <- ##st`"stVal" ;
            Let memSize   : Bit LgLgNumBytesFullCapSz <- ##st`"memSize" ;
            LetA accepted : Bool                      <- liftAction np_mem ((memIfc ty).(mem_writeMem) stAddr stVal memSize) ;
            If #accepted Then (
              Act (liftAction np_rf (updateMshwmOnStore stAddr)) ;
              Act (liftAction np_rf incrementMinstret) ;
              Act (liftAction np_waitBits (@writeWaitBit dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool false))) ;
              Act (liftAction np_inputFifo (@deq dom capacity DeferredReq ty)) ;
              If (And [ Eq #stAddr ($ tohostAddr) ; isNotZero (##stVal`"addr") ]) Then (
                Let tohostVal : Addr <- ##stVal`"addr" ;
                If (Eq #tohostVal $1) Then (
                  Sys [ DispString ty "TEST PASSED!\n" ; Finish ty ] ; Retv
                ) ;
                If (Not (Eq #tohostVal $1)) Then (
                  Sys [ DispString ty "TEST FAILED at test case: " ; DispDecimal #tohostVal ; DispString ty "\n" ; Finish ty ] ; Retv
                ) ;
                Retv
              ) ;
              Retv
            ) ;
            Retv
          ) Else (
            (* --- LOAD ACTION --- *)
            Let ld      : LoadCmd                   <- ##memAct `! "Load" ;
            Let ldAddr  : Addr                      <- ##ld`"addr" ;
            Let pending : PendingLoad               <- ##ld`"pending" ;
            Let memSize : Bit LgLgNumBytesFullCapSz <- ##pending`"memSize" ;
            If (And [ Not #outputBuffer_isFull ; #revRq_isEmpty ]) Then (
              LetA accepted : Bool <- liftAction np_mem ((memIfc ty).(mem_readMemRq) ldAddr memSize) ;
              If #accepted Then (
                Act (liftAction np_loadFifo (@enq dom capacity LoadCmd ty ld)) ;
                liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
              ) ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          (* --- FENCE ACTION --- *)
          Let fn                    : FenceCmd <- ##mfAct `! "Fence" ;
          Let fenceOp               : FenceOp  <- ##fn`"fenceOp" ;
          LetA outputBuffer_isEmpty : Bool     <- liftAction np_loadFifo (@isEmpty dom capacity LoadCmd ty) ;
          LetA rev_isEmpty          : Bool     <- liftAction np_revFifo (@isEmpty dom capacity RevCmd ty) ;
          If (Or [ Not (##fn`"needsEmpty") ; And [ #outputBuffer_isEmpty ; #revRq_isEmpty ; #rev_isEmpty ] ]) Then (
            LetA accepted : Bool <- liftAction np_mem ((memIfc ty).(mem_fence_req) fenceOp) ;
            If #accepted Then (
              Act (liftAction np_rf incrementMinstret) ;
              Act (liftAction np_waitBits (@writeWaitBit dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool false))) ;
              liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) Else (
        (* --- MULDIV ACTION: Enqueue into parameterized MulDiv subsystem --- *)
        Let md       : MulDivCmd   <- ##action `! "MulDiv" ;
        Let op1      : Addr        <- ##md`"op1" ;
        Let mulDivOp : MulDivUnion <- ##md`"mulDivOp" ;
        Let dstIdx   : Bit RegIdxSz <- ##md`"dstIdx" ;
        Let isMul    : Bool        <- #mulDivOp `? "Mul" ;
        LetA canEnq  : Bool        <-
          liftAction np_mulDiv
            (@modeCanEnq dom ImplInputWidth ImplMulStages ImplDivStages ImplMulDivMode ty isMul) ;
        If #canEnq Then (
          Act (liftAction np_mulDiv
                 (@modeEnqReq dom ImplInputWidth ImplMulStages ImplDivStages ImplMulDivMode ty dstIdx op1 mulDivOp)) ;
          liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2A: loadRpAndWritebackOrEnqueueRevRq
   *
   * - Dequeues LoadCmd from loadFifo when mem_getMemRp returns Some.
   * - Uses dispatchLoadResponse for pure combinational response handling.
   *     - RevLookup: enqueues RevCmd into revRqFifo (separate from mem_readRevBitRq).
   *     - Writeback: writes back directly to Register File and clears waitBits.
   * ========================================================================= *)
  Definition loadRpAndWritebackOrEnqueueRevRq : Action ty coreTree (Bit 0) :=
    LetA inputHead       : Option LoadCmd <- liftAction np_loadFifo (@first dom capacity LoadCmd ty) ;
    LetA revRqBuf_isFull : Bool           <- liftAction np_revRqFifo (@isFull dom capacity RevCmd ty) ;

    If (And [ #inputHead `? "Some" ; Not #revRqBuf_isFull ]) Then (
      Let  ld        : LoadCmd                   <- #inputHead `! "Some" ;
      Let  ldAddr    : Addr                      <- ##ld`"addr" ;
      Let  pl        : PendingLoad               <- ##ld`"pending" ;
      Let  memSize   : Bit LgLgNumBytesFullCapSz <- ##pl`"memSize" ;
      LetA memValOpt : Option FullCapWithTag     <- liftAction np_mem ((memIfc ty).(mem_getMemRp) ldAddr memSize) ;

      If (##memValOpt `? "Some") Then (
        Let memVal   : FullCapWithTag <- ##memValOpt `! "Some" ;
        LetL outcome : LoadOutcome    <- dispatchLoadResponse pl memVal false ;

        If (#outcome `? "RevLookup") Then (
          Let revInfo : RevCmd <- #outcome `! "RevLookup" ;
          Act (liftAction np_revRqFifo (@enq dom capacity RevCmd ty revInfo)) ;
          liftAction np_loadFifo (@deq dom capacity LoadCmd ty)
        ) Else (
          Let wbInfo     : WbCmd            <- #outcome `! "Writeback" ;
          Let dstIdxReal : Bit RegIdxSzReal <- TruncLsb 1 RegIdxSzReal (##wbInfo`"dstIdx") ;
          If (isNotZero #dstIdxReal) Then (
            Act (liftAction np_rf (writeRegsList gprPathsWithKind (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))) ;
            Retv
          ) ;
          Act (liftAction np_waitBits (@clearWaitBits2 dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool true) #dstIdxReal (isNotZero #dstIdxReal))) ;
          Act (liftAction np_rf incrementMinstret) ;
          liftAction np_loadFifo (@deq dom capacity LoadCmd ty)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2B: revRq
   *
   * - Dequeues RevCmd from revRqFifo, issues mem_readRevBitRq, and enqueues
   *   RevCmd into revFifo.
   * ========================================================================= *)
  Definition revRq : Action ty coreTree (Bit 0) :=
    LetA inputHead     : Option RevCmd <- liftAction np_revRqFifo (@first dom capacity RevCmd ty) ;
    LetA revBuf_isFull : Bool          <- liftAction np_revFifo (@isFull dom capacity RevCmd ty) ;

    If (And [ #inputHead `? "Some" ; Not #revBuf_isFull ]) Then (
      Let revInfo   : RevCmd           <- #inputHead `! "Some" ;
      Let revBase   : Bit (AddrSz + 1) <- ##revInfo`"base" ;
      LetA accepted : Bool             <- liftAction np_mem ((memIfc ty).(mem_readRevBitRq) revBase) ;

      If #accepted Then (
        Act (liftAction np_revFifo (@enq dom capacity RevCmd ty revInfo)) ;
        liftAction np_revRqFifo (@deq dom capacity RevCmd ty)
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 3: revRpAndWriteBack
   *
   * - Dequeues RevCmd from revFifo when mem_getRevBitRp returns Some.
   * - Uses dispatchRevResponse for pure combinational final writeback value.
   * - Writes back final capability to Register File and clears waitBits.
   * ========================================================================= *)
  Definition revRpAndWriteBack : Action ty coreTree (Bit 0) :=
    LetA inputHead : Option RevCmd <- liftAction np_revFifo (@first dom capacity RevCmd ty) ;

    If (#inputHead `? "Some") Then (
      Let  revInfo   : RevCmd           <- #inputHead `! "Some" ;
      Let  revBase   : Bit (AddrSz + 1) <- ##revInfo`"base" ;
      Let  pr        : PendingRev       <- ##revInfo`"pendingRev" ;
      LetA revBitOpt : Option Bool      <- liftAction np_mem ((memIfc ty).(mem_getRevBitRp) revBase) ;

      If (##revBitOpt `? "Some") Then (
        Let  revBit     : Bool             <- ##revBitOpt `! "Some" ;
        LetL wbInfo     : WbCmd            <- dispatchRevResponse pr revBit ;
        Let  dstIdxReal : Bit RegIdxSzReal <- TruncLsb 1 RegIdxSzReal (##wbInfo`"dstIdx") ;
        If (isNotZero #dstIdxReal) Then (
          Act (liftAction np_rf (writeRegsList gprPathsWithKind (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))) ;
          Retv
        ) ;
        Act (liftAction np_waitBits (@clearWaitBits2 dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool true) #dstIdxReal (isNotZero #dstIdxReal))) ;
        Act (liftAction np_rf incrementMinstret) ;
        liftAction np_revFifo (@deq dom capacity RevCmd ty)
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * MULDIV SUBSYSTEM STAGES & WRITEBACK
   * ========================================================================= *)

  Definition mulStageRules : list (Action ty coreTree (Bit 0)) :=
    map (fun a => liftAction np_mulDiv a)
        (@modeAllStageRules dom ImplInputWidth ImplMulStages ImplDivStages ImplMulDivMode ty).

  Definition mulWriteBack : Action ty coreTree (Bit 0) :=
    LetA wbOpt : Option (MulDivWbResp ImplInputWidth) <-
      liftAction np_mulDiv
        (@modePopMulResp dom ImplInputWidth ImplMulStages ImplDivStages ImplMulDivMode ty) ;
    If (#wbOpt `? "Some") Then (
      Let wb         : MulDivWbResp ImplInputWidth <- #wbOpt `! "Some" ;
      Let dstIdx     : Bit RegIdxSz <- ##wb`"dst" ;
      Let resAddr    : Addr         <- ##wb`"res" ;
      Let wbVal      : FullECapWithTag <- STRUCT {
        "tag"  ::= Const ty Bool false ;
        "ecap" ::= Const ty ECap (getDefault _) ;
        "addr" ::= #resAddr
      } ;
      Let dstIdxReal : Bit RegIdxSzReal <- TruncLsb 1 RegIdxSzReal #dstIdx ;
      If (isNotZero #dstIdxReal) Then (
        Act (liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #wbVal)) ;
        Retv
      ) ;
      Act (liftAction np_waitBits (@clearWaitBits2 dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool true) #dstIdxReal (isNotZero #dstIdxReal))) ;
      Act (liftAction np_rf incrementMinstret) ;
      Retv
    ) ;
    Retv.

  Definition divStageRules : list (Action ty coreTree (Bit 0)) := [].

  Definition divWriteBack : Action ty coreTree (Bit 0) :=
    LetA wbOpt : Option (MulDivWbResp ImplInputWidth) <-
      liftAction np_mulDiv
        (@modePopDivResp dom ImplInputWidth ImplMulStages ImplDivStages ImplMulDivMode ty) ;
    If (#wbOpt `? "Some") Then (
      Let wb         : MulDivWbResp ImplInputWidth <- #wbOpt `! "Some" ;
      Let dstIdx     : Bit RegIdxSz <- ##wb`"dst" ;
      Let resAddr    : Addr         <- ##wb`"res" ;
      Let wbVal      : FullECapWithTag <- STRUCT {
        "tag"  ::= Const ty Bool false ;
        "ecap" ::= Const ty ECap (getDefault _) ;
        "addr" ::= #resAddr
      } ;
      Let dstIdxReal : Bit RegIdxSzReal <- TruncLsb 1 RegIdxSzReal #dstIdx ;
      If (isNotZero #dstIdxReal) Then (
        Act (liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #wbVal)) ;
        Retv
      ) ;
      Act (liftAction np_waitBits (@clearWaitBits2 dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool true) #dstIdxReal (isNotZero #dstIdxReal))) ;
      Act (liftAction np_rf incrementMinstret) ;
      Retv
    ) ;
    Retv.

End DeferredStages.
