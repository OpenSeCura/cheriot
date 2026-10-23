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
      Leaf "fenceIPending" (dom, EReg (Build_Reg Bool (Some false) false)) ;
      Leaf "canProceed"    (dom, EReg (Build_Reg Bool (Some true) false))
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

  Definition pExecuteCanProceed : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "canProceed").

  Definition readExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree Bool :=
    ReadReg "canProceed" pExecuteCanProceed (fun v => Return #v).

  Definition setExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecuteCanProceed (ConstBool true) Retv.

  Definition clearExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecuteCanProceed (ConstBool false) Retv.

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
  Variable dataMemIfc : forall ty, @DataMemIfc ty.
  Variable mulDivIfc : forall ty, @MulDivIfc ty.
  Variable ty : Kind -> Type.
  Variable meipAct mtipAct : Action ty (memIfc ty).(memTree) Bool.

  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation bpTree := (bpTree noInstTree (withInstIfc ty).(withInstTree)).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation fetchTree := (fetchIfc ty).(fetchTree).
  Local Abbreviation decodeTree := (decodeIfc ty).(decodeTree).
  Local Abbreviation dataMemTree := (dataMemIfc ty).(dataMemTree).
  Local Abbreviation mulDivTree := (mulDivIfc ty).(mulDivTree).
  Local Abbreviation coreTree := (coreTree dom rfTree bpTree memTree fetchTree decodeTree implExecuteTree dataMemTree mulDivTree).
  Local Abbreviation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).
  Local Abbreviation isInterruptPending := (isInterruptPending dom pcAddrInit).
  Local Abbreviation executeInterrupt := (executeInterrupt dom pcAddrInit).
  Local Abbreviation executeSequential := (executeSequential dom pcAddrInit).
  Local Abbreviation executeNonSequential := (executeNonSequential dom pcAddrInit).

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

  Definition np_dataMem : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.dataMem") singletonChildPath).

  Definition np_mulDiv : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.mulDiv") singletonChildPath).

  (* =========================================================================
   * STAGE 4: aluAndExecuteNonDeferred
   *
   * - Precondition: decodeToAluBuf is non-empty, the target input FIFO
   *                 (dataMem / mul / div) is not full when applicable, and
   *                 if an enabled interrupt is pending, the dataMem (Mem/Fence)
   *                 pipeline is empty.
   * - Action:       Dequeue d2aEntry { aluIn, predPc, execEpoch } from
   *                 decodeToAluBuf.
   *                 - If execEpoch != currExecEpoch: drop entry and clear its
   *                   destination GPR wait bit.
   *                 - If execEpoch == currExecEpoch: run AluRouting, Alu, and
   *                   dispatch to executeInterrupt, executeSequential, or
   *                   executeNonSequential; update branch predictor; on
   *                   ControlFlowAddrECap or committedNextPc != predPc,
   *                   advance execEpoch, clear straddleOpt, and redirect
   *                   fetchPc; clear destination GPR wait bit when not
   *                   deferred, or enqueue MemFence into dataMemIfc and
   *                   Mul/Div into mulDivIfc.
   * ========================================================================= *)
  Definition aluAndExecuteNonDeferred : Action ty coreTree (Bit 0) :=
    LetA canProceed       : Bool                    <- liftAction np_execute (@readExecuteCanProceed ty) ;

    If #canProceed Then (
      Act (liftAction np_execute (@clearExecuteCanProceed ty)) ;

      LetA d2aHead          : Option DecodeToAluEntry <- liftAction np_decode (decodeIfc ty).(decode_first) ;
      LetA dataMemIn_isFull : Bool                    <- liftAction np_dataMem (dataMemIfc ty).(dataMem_isFull) ;
      LetA dataMem_isEmpty  : Bool                    <- liftAction np_dataMem (dataMemIfc ty).(dataMem_isEmpty) ;
      LetA mulIn_isFull     : Bool                    <- liftAction np_mulDiv (mulDivIfc ty).(mulDiv_isFullMul) ;
      LetA divIn_isFull     : Bool                    <- liftAction np_mulDiv (mulDivIfc ty).(mulDiv_isFullDiv) ;
      LetA currExecEpoch    : Epoch                   <- liftAction np_execute (@readExecEpoch ty) ;
      LetA pcc              : FullECapWithTag         <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
      LetA meip             : Bool                    <- liftAction np_mem meipAct ;
      LetA mtip             : Bool                    <- liftAction np_mem mtipAct ;
      LetA isInterrupt      : Bool                    <- liftAction np_rf (isInterruptPending meip mtip) ;

      Let  d2aEntry       : DecodeToAluEntry <- ##d2aHead`"data" ;
      Let  pkg            : AluInInstGroup   <- ##d2aEntry`"aluIn" ;
      Let  predPc         : Addr             <- ##d2aEntry`"predPc" ;
      Let  entryExecEpoch : Epoch            <- ##d2aEntry`"execEpoch" ;

      Let  instBits        : Inst             <- ##pkg`"inst" ;
      Let  writesCd        : Bool             <- ##pkg`"writesCd" ;
      Let  dstIdxReal      : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd instBits) ;

      Let  pcAddr          : Addr               <- ##pcc`"addr" ;
      LetL aluOut          : AluOutUnion        <- wrappedAlu pcc pkg ;

      Let  aluOp           : AluOpUnion         <- ##aluOut`"Op" ;
      Let  isSeq           : Bool               <- #aluOp `? "Sequential" ;
      Let  seqOp           : SequentialUnion    <- #aluOp `! "Sequential" ;
      Let  isMulDiv        : Bool               <- And [ #isSeq ; #seqOp `? "MulDiv" ] ;
      Let  mulDivOp        : MulDivUnion        <- #seqOp `! "MulDiv" ;
      Let  isMul           : Bool               <- And [ #isMulDiv ; #mulDivOp `? "Mul" ] ;
      Let  isDiv           : Bool               <- And [ #isMulDiv ; #mulDivOp `? "Div" ] ;

      Let  nonSeqOp        : NonSequentialUnion <- #aluOp `! "NonSequential" ;
      Let  isNonSeq        : Bool               <- #aluOp `? "NonSequential" ;
      Let  isExc           : Bool               <- And [ #isNonSeq ; #nonSeqOp `? "Exception" ] ;
      Let  isNoExc         : Bool               <- And [ #isNonSeq ; #nonSeqOp `? "NoException" ] ;
      Let  noExc           : NoExceptionUnion   <- #nonSeqOp `! "NoException" ;
      Let  isMemOrFence    : Bool               <- And [ #isNoExc ; #noExc `? "DataMem" ] ;

      Let  dstVal          : FullECapWithTag    <- ##aluOut`"dstValue" ;
      Let  reqDst          : Bit RegIdxSzReal   <- ##aluOut`"dstIdx" ;
      Let  reqAddr         : Addr               <- ##dstVal`"addr" ;

      Let  waitFalse : Bool <- ConstBool false ;

      If (##d2aHead`"valid") Then (
        If (Not (Eq #entryExecEpoch #currExecEpoch)) Then (
          Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
          liftAction np_waitBits
            (@setDstWaitBits dom ty
               writesCd dstIdxReal
               waitFalse)
        ) Else (
          If #isInterrupt Then (
            If #dataMem_isEmpty Then (
              Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
              LetA execOut         : ExecuteOut      <- liftAction np_rf (executeInterrupt pcc meip mtip) ;
              Let  nextPcc         : FullECapWithTag <- ##execOut`"nextPcc" ;
              Let  committedNextPc : Addr            <- ##nextPcc`"addr" ;
              Act (liftAction np_rf (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc)) ;

              Let nextExecEpoch : Epoch <- Add [ #currExecEpoch ; $1 ] ;
              Act (liftAction np_execute (@writeExecEpoch ty nextExecEpoch)) ;
              Act (liftAction np_fetch (fetchIfc ty).(fetch_clearStraddle)) ;
              Act (liftAction np_fetch ((fetchIfc ty).(fetch_writeFetchPc) committedNextPc)) ;

              liftAction np_waitBits
                (@setDstWaitBits dom ty
                   writesCd dstIdxReal
                   waitFalse)
            ) ;
            Retv
          ) Else (
            If #isSeq Then (
              If (And [ Or [ Not #isMul ; Not #mulIn_isFull ] ;
                        Or [ Not #isDiv ; Not #divIn_isFull ] ]) Then (
                Act (liftAction np_execute (@setExecuteCanProceed ty)) ;
                Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
                LetA mulDivOpt : Option MulDivUnion <- liftAction np_rf (executeSequential pcc aluOut) ;
                Let  nextPcc   : FullECapWithTag    <- #pcc `{ "addr" <- #predPc } ;
                Act (liftAction np_rf (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc)) ;

                If (#mulDivOpt`"valid") Then (
                  Let mdOp : MulDivUnion <- #mulDivOpt`"data" ;
                  If (#mdOp `? "Mul") Then (
                    Let mOp : MulOp <- #mdOp `! "Mul" ;
                    liftAction np_mulDiv ((mulDivIfc ty).(mulDiv_enqMul) reqDst reqAddr mOp)
                  ) Else (
                    Let dOp : DivOp <- #mdOp `! "Div" ;
                    liftAction np_mulDiv ((mulDivIfc ty).(mulDiv_enqDiv) reqDst reqAddr dOp)
                  ) ;
                  Retv
                ) Else (
                  liftAction np_waitBits
                    (@setDstWaitBits dom ty
                       writesCd dstIdxReal
                       waitFalse)
                ) ;
                Retv
              ) ;
              Retv
            ) Else (
              If (Or [ Not #isMemOrFence ; Not #dataMemIn_isFull ]) Then (
                Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
                LetA execOut         : ExecuteOut      <- liftAction np_rf (executeNonSequential pcc meip mtip aluOut) ;
                Let  nextPcc         : FullECapWithTag <- ##execOut`"nextPcc" ;
                Act (liftAction np_rf (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc)) ;

                Let  cfOpt           : Option CfPayload <- ##execOut`"cf" ;
                Let  hasCf           : Bool             <- #cfOpt`"valid" ;
                Let  cf              : CfPayload        <- #cfOpt`"data" ;
                Let  committedNextPc : Addr             <- ##nextPcc`"addr" ;
                Let  capChanged      : Bool             <- And [ #hasCf ; ##cf`"capChanged" ] ;

                If #hasCf Then (
                  liftAction np_bp ((withInstIfc ty).(withInst_updCf) pcAddr cf)
                ) ;

                If #isExc Then (
                  liftAction np_bp ((withInstIfc ty).(withInst_updException) pcAddr)
                ) ;

                If (Or [ #isExc ; #capChanged ; ##execOut`"isFenceIRq" ; Not (Eq #committedNextPc #predPc) ]) Then (
                  Let nextExecEpoch : Epoch <- Add [ #currExecEpoch ; $1 ] ;
                  Act (liftAction np_execute (@writeExecEpoch ty nextExecEpoch)) ;
                  Act (liftAction np_fetch (fetchIfc ty).(fetch_clearStraddle)) ;
                  liftAction np_fetch ((fetchIfc ty).(fetch_writeFetchPc) committedNextPc)
                ) ;

                If (##execOut`"isFenceIRq") Then (
                  liftAction np_execute (@setFenceIPending ty)
                ) ;

                Let dataMemOpt : Option MemFenceUnion <- ##execOut`"dataMem" ;
                If (#dataMemOpt`"valid") Then (
                  Let mfOp : MemFenceUnion <- #dataMemOpt`"data" ;
                  liftAction np_dataMem ((dataMemIfc ty).(dataMem_enq) reqDst reqAddr mfOp)
                ) Else (
                  liftAction np_waitBits
                    (@setDstWaitBits dom ty
                       writesCd dstIdxReal
                       waitFalse)
                ) ;
                Retv
              ) ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End ExecuteStage.
