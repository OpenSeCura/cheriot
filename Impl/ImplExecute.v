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

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu ImplCommon ImplBranchPredictor ImplDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section ExecuteStage.
  Variable dom : string.

  Definition implExecuteTree : Tree DomainElem :=
    Node "" [
      Leaf "execEpoch"     (dom, EReg (Build_Reg Epoch (Some Zmod.zero) false)) ;
      Leaf "fenceIPending" (dom, EReg (Build_Reg Bool (Some false) false))
    ].

  Definition pExecEpoch : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "execEpoch").

  Definition readExecEpoch (ty : Kind -> Type) : Action ty implExecuteTree Epoch :=
    ReadReg "execEpoch" pExecEpoch (fun v => Return #v).

  Definition writeExecEpoch (ty : Kind -> Type) (val : ty Epoch) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecEpoch #val Retv.

  Definition pFenceIPending : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "fenceIPending").

  Definition readFenceIPending (ty : Kind -> Type) : Action ty implExecuteTree Bool :=
    ReadReg "fenceIPending" pFenceIPending (fun v => Return #v).

  Definition setFenceIPending (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pFenceIPending (ConstBool true) Retv.

  Definition clearFenceIPending (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pFenceIPending (ConstBool false) Retv.

  Definition implExecuteIfc (ty : Kind -> Type) : @ExecuteIfc ty := {|
    executeTree             := implExecuteTree ;
    execute_readExecEpoch   := @readExecEpoch ty ;
    execute_readFenceIPend  := @readFenceIPending ty ;
    execute_clearFenceIPend := @clearFenceIPending ty
  |}.

  Variable pcAddrInit : Z.
  Variable noInstTree : Tree DomainElem.
  Variable withInstIfc : forall ty, @WithInstPredIfc noInstTree ty.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable fetchIfc : forall ty, @FetchIfc ty.
  Variable decodeIfc : forall ty, @DecodeIfc ty.
  Variable deferredIfc : forall ty, @DeferredIfc ty.
  Variable ty : Kind -> Type.
  Variable meipAct mtipAct : Action ty (memIfc ty).(memTree) Bool.

  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation bpTree := (bpTree noInstTree (withInstIfc ty).(withInstTree)).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation fetchTree := (fetchIfc ty).(fetchTree).
  Local Abbreviation decodeTree := (decodeIfc ty).(decodeTree).
  Local Abbreviation deferredTree := (deferredIfc ty).(deferredTree).
  Local Abbreviation coreTree := (coreTree dom rfTree bpTree memTree fetchTree decodeTree implExecuteTree deferredTree).
  Local Abbreviation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).
  Local Abbreviation isInterruptPending := (isInterruptPending dom pcAddrInit).
  Local Abbreviation executeNonDeferred := (executeNonDeferred dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf.").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits.").

  Definition np_bp : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.bp") singletonChildPath).

  Definition np_mem : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_fetch : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.fetch") singletonChildPath).

  Definition np_decode : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.decode") singletonChildPath).

  Definition np_execute : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.execute.").

  Definition np_deferred : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.deferred") singletonChildPath).

  (* =========================================================================
   * STAGE 4: aluAndExecuteNonDeferred
   *
   * - Precondition: decodeToAluBuf is non-empty, deferred inputBuf is not
   *                 full when the instruction is deferred, and if an enabled
   *                 interrupt is pending, the deferred pipeline is empty.
   * - Action:       Dequeue d2aEntry { aluIn, predPc, execEpoch } from
   *                 decodeToAluBuf.
   *                 - If execEpoch != currExecEpoch: drop entry and clear its
   *                   destination GPR/SCR/CSR wait bits.
   *                 - If execEpoch == currExecEpoch: run AluRouting, Alu, and
   *                   executeNonDeferred; update branch predictor; on
   *                   ControlFlowAddrECap or committedNextPc != predPc,
   *                   advance execEpoch, clear straddleOpt, and redirect
   *                   fetchPc; clear destination SCR/CSR wait bits (and GPR
   *                   wait bit when not deferred), or enqueue deferredReq into
   *                   deferred inputBuf.
   * ========================================================================= *)
  Definition aluAndExecuteNonDeferred : Action ty coreTree (Bit 0) :=
    LetA d2aHead           : Option DecodeToAluEntry <- liftAction np_decode (decodeIfc ty).(decode_first) ;
    LetA deferredIn_isFull : Bool                    <- liftAction np_deferred (deferredIfc ty).(deferred_isFull) ;
    LetA deferred_isEmpty  : Bool                    <- liftAction np_deferred (deferredIfc ty).(deferred_isEmpty) ;

    If (##d2aHead`"valid") Then (
      Let  d2aEntry       : DecodeToAluEntry <- ##d2aHead`"data" ;
      Let  pkg            : AluInInstGroup   <- ##d2aEntry`"aluIn" ;
      Let  predPc         : Addr             <- ##d2aEntry`"predPc" ;
      Let  entryExecEpoch : Epoch            <- ##d2aEntry`"execEpoch" ;

      Let  instBits        : Inst             <- ##pkg`"inst" ;
      Let  writesCd        : Bool             <- ##pkg`"writesCd" ;
      Let  dstIdxReal      : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd instBits) ;
      Let  writesScr       : Bool             <- ##pkg`"writesScr" ;
      Let  readWriteScrIdx : Bit ScrIdxSz     <- ##pkg`"readWriteScrIdx" ;
      Let  writesCsr       : Bool             <- ##pkg`"writesCsr" ;
      Let  readWriteCsrIdx : Bit CsrIdxSz     <- ##pkg`"readWriteCsrIdx" ;

      Let  waitFalse : Bool <- ConstBool false ;
      LetA currExecEpoch : Epoch <- liftAction np_execute (@readExecEpoch ty) ;

      If (Not (Eq #entryExecEpoch #currExecEpoch)) Then (
        Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
        liftAction np_waitBits
          (@setDstWaitBits dom ty
             writesCd dstIdxReal
             writesScr readWriteScrIdx
             writesCsr readWriteCsrIdx
             waitFalse)
      ) Else (
        LetA pcc           : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
        Let  pcAddr        : Addr            <- ##pcc`"addr" ;
        LetL aluOut        : AluOutUnion     <- wrappedAlu pcc pkg ;

        Let  aluOp         : AluOpUnion       <- ##aluOut`"Op" ;
        Let  isExc         : Bool             <- #aluOp `? "Exception" ;
        Let  noExc         : NoExceptionUnion <- #aluOp `! "NoException" ;
        Let  isDeferredAlu : Bool             <- And [ #aluOp `? "NoException" ; #noExc `? "Deferred" ] ;

        LetA meip          : Bool                 <- liftAction np_mem meipAct ;
        LetA mtip          : Bool                 <- liftAction np_mem mtipAct ;
        LetA intInfo       : InterruptPendingInfo <- liftAction np_rf (isInterruptPending meip mtip) ;
        Let  isInterrupt   : Bool                 <- ##intInfo`"isInterrupt" ;
        Let  isTrap        : Bool                 <- Or [ #isInterrupt ; #isExc ] ;
        Let  intStall      : Bool                 <- And [ #isInterrupt ; Not #deferred_isEmpty ] ;

        If (And [ Not #intStall ; Or [ Not #isDeferredAlu ; Not #deferredIn_isFull ] ]) Then (
          Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;

          LetA execOut : ExecuteOut <- liftAction np_rf (executeNonDeferred pcc meip mtip aluOut) ;

          Let  cfOpt           : Option CfPayload <- ##execOut`"cf" ;
          Let  hasCf           : Bool             <- #cfOpt`"valid" ;
          Let  cf              : CfPayload        <- #cfOpt`"data" ;
          Let  committedNextPc : Addr             <- ##execOut`"nextPc" ;
          Let  capChanged      : Bool             <- And [ #hasCf ; ##cf`"capChanged" ] ;

          If #hasCf Then (
            liftAction np_bp ((withInstIfc ty).(withInst_updCf) pcAddr cf)
          ) ;

          If #isExc Then (
            liftAction np_bp ((withInstIfc ty).(withInst_updException) pcAddr)
          ) ;

          If (Or [ #isTrap ; #capChanged ; ##execOut`"isFenceIRq" ; Not (Eq #committedNextPc #predPc) ]) Then (
            Let nextExecEpoch : Epoch <- Add [ #currExecEpoch ; $1 ] ;
            Act (liftAction np_execute (@writeExecEpoch ty nextExecEpoch)) ;
            Act (liftAction np_fetch (fetchIfc ty).(fetch_clearStraddle)) ;
            liftAction np_fetch ((fetchIfc ty).(fetch_writeFetchPc) committedNextPc)
          ) ;

          If (##execOut`"isFenceIRq") Then (
            liftAction np_execute (@setFenceIPending ty)
          ) ;

          Let reqOpt     : Option DeferredReq <- ##execOut`"deferredReq" ;
          Let isDeferred : Bool               <- #reqOpt`"valid" ;

          If #isDeferred Then (
            Let req : DeferredReq <- #reqOpt`"data" ;
            liftAction np_deferred ((deferredIfc ty).(deferred_enq) req)
          ) Else (
            liftAction np_waitBits
              (@setDstWaitBits dom ty
                 writesCd dstIdxReal
                 writesScr readWriteScrIdx
                 writesCsr readWriteCsrIdx
                 waitFalse)
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End ExecuteStage.
