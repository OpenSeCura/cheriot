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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu Fifo ImplCommon ImplBranchPredictor ImplDevice ImplFetch ImplDecode ImplDeferred.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section ExecuteStage.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity decodeCapacity deferredCapacity : nat.
  Variable noInstTree : Tree DomainElem.
  Variable withInstIfc : forall ty, @WithInstPredIfc noInstTree ty.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.
  Variable meipAct mtipAct : Action ty (memIfc ty).(memTree) Bool.

  Local Notation bpTree := (bpTree noInstTree (withInstIfc ty).(withInstTree)).
  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation fTree := (fetchTree dom pcAddrInit fetchCapacity).
  Local Notation decTree := (decodeTree dom pcAddrInit decodeCapacity).
  Local Notation dTree := (deferredTree dom deferredCapacity).
  Local Notation coreTree := (coreTree dom pcAddrInit bpTree memTree fTree decTree dTree).
  Local Notation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).
  Local Notation executeNonDeferred := (executeNonDeferred dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits").

  Definition np_bp : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.bp") singletonChildPath).

  Definition np_mem : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_fetch : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.fetch").

  Definition np_decode : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode.decode").

  Definition np_decodeToAluFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode.decode.decodeToAluBuf.fifo").

  Definition np_deferredInFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.deferred.inputBuf.fifo").

  (* =========================================================================
   * STAGE 3: aluAndExecuteNonDeferred
   *
   * - Precondition: decodeToAluBuf is non-empty (and deferred inputBuf is not
   *                 full when the instruction is deferred).
   * - Action:       Dequeue d2aEntry { aluIn, predPc, epoch } from
   *                 decodeToAluBuf.
   *                 - If epoch != currEpoch: drop entry and clear its
   *                   destination GPR/SCR/CSR wait bits.
   *                 - If epoch == currEpoch: run AluRouting, Alu, and
   *                   executeNonDeferred; update branch predictor; on
   *                   ControlFlowAddrECap or committedNextPc != predPc,
   *                   advance currEpoch, update decodePc, and redirect fetchPc;
   *                   clear destination SCR/CSR wait bits (and GPR wait bit
   *                   when not deferred), or enqueue deferredReq into
   *                   deferred inputBuf.
   * ========================================================================= *)
  Definition aluAndExecuteNonDeferred : Action ty coreTree (Bit 0) :=
    LetA d2aHead           : Option DecodeToAluEntry <- liftAction np_decodeToAluFifo (@first dom decodeCapacity DecodeToAluEntry ty) ;
    LetA deferredIn_isFull : Bool                    <- liftAction np_deferredInFifo (@isFull dom deferredCapacity DeferredReq ty) ;

    If (##d2aHead`"valid") Then (
      Let  d2aEntry : DecodeToAluEntry <- ##d2aHead`"data" ;
      Let  pkg      : AluInInstGroup   <- ##d2aEntry`"aluIn" ;
      Let  predPc   : Addr             <- ##d2aEntry`"predPc" ;
      Let  epoch    : Epoch            <- ##d2aEntry`"epoch" ;

      Let  instBits   : Inst                  <- ##pkg`"inst" ;
      Let  instGroup  : InstGroup             <- ##pkg`"instGroup" ;
      Let  cs2Source  : TaggedUnion Cs2Source <- ##pkg`"cs2Idx" ;
      Let  writesCd   : Bool                  <- ##pkg`"writesCd" ;
      Let  dstIdxReal : Bit RegIdxSzReal      <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd instBits) ;

      LetL wInfo      : WaitSpecialInfo <- getWaitSpecialInfo instGroup cs2Source ;

      LetA currEpoch  : Epoch <- @readCurrEpoch dom pcAddrInit bpTree memTree fTree decTree dTree ty ;

      If (Not (Eq #epoch #currEpoch)) Then (
        Act (liftAction np_decodeToAluFifo (@deq dom decodeCapacity DecodeToAluEntry ty)) ;
        liftAction np_waitBits
          (@setDstWaitBits dom ty
             #writesCd #dstIdxReal
             wInfo
             (ConstBool false))
      ) Else (
        LetA pcc           : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
        Let  pcAddr        : Addr            <- ##pcc`"addr" ;
        LetL aluOut        : AluOutUnion     <- wrappedAlu pcc pkg ;

        Let  aluOp         : AluOpUnion       <- ##aluOut`"Op" ;
        Let  noExc         : NoExceptionUnion <- #aluOp `! "NoException" ;
        Let  isDeferredAlu : Bool             <- And [ #aluOp `? "NoException" ; #noExc `? "Deferred" ] ;

        If (Or [ Not #isDeferredAlu ; Not #deferredIn_isFull ]) Then (
          Act (liftAction np_decodeToAluFifo (@deq dom decodeCapacity DecodeToAluEntry ty)) ;

          LetA meip    : Bool       <- liftAction np_mem meipAct ;
          LetA mtip    : Bool       <- liftAction np_mem mtipAct ;
          LetA execOut : ExecuteOut <- liftAction np_rf (executeNonDeferred pcc meip mtip aluOut) ;

          Let  cfOpt           : Option CfPayload <- ##execOut`"cf" ;
          Let  hasCf           : Bool             <- #cfOpt`"valid" ;
          Let  cf              : CfPayload        <- #cfOpt`"data" ;
          Let  cfOp            : CfOp             <- ##cf`"CfOp" ;
          Let  committedNextPc : Addr             <- ##execOut`"nextPc" ;
          Let  isAddrECap      : Bool             <- And [ #hasCf ; #cfOp `? "ControlFlowAddrECap" ] ;

          If #hasCf Then (
            liftAction np_bp ((withInstIfc ty).(withInst_updCf) pcAddr cf)
          ) ;

          If (Or [ #isAddrECap ; Not (Eq #committedNextPc #predPc) ]) Then (
            Let nextEpoch : Epoch <- Add [ #currEpoch ; $1 ] ;
            Act (@writeCurrEpoch dom pcAddrInit bpTree memTree fTree decTree dTree ty #nextEpoch) ;
            Act (liftAction np_decode (@writeDecodePc dom pcAddrInit decodeCapacity ty #committedNextPc)) ;
            liftAction np_fetch (@writeFetchPc dom pcAddrInit fetchCapacity ty #committedNextPc)
          ) ;

          If (##execOut`"isFenceIRq") Then (
            liftAction np_mem ((memIfc ty).(mem_fenceI_req))
          ) ;

          Let reqOpt     : Option DeferredReq <- ##execOut`"deferredReq" ;
          Let isDeferred : Bool               <- #reqOpt`"valid" ;

          If #isDeferred Then (
            Let req : DeferredReq <- #reqOpt`"data" ;
            liftAction np_deferredInFifo (@enq dom deferredCapacity DeferredReq ty req)
          ) Else (
            liftAction np_waitBits
              (@setDstWaitBits dom ty
                 #writesCd #dstIdxReal
                 wInfo
                 (ConstBool false))
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End ExecuteStage.
