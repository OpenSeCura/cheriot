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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu ShiftFifo ImplCommon ImplBranchPredictor ImplDevice ImplFetch ImplDeferred.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section DecodeStage.
  Variable dom : string.
  Variable capacity : nat.

  Definition decodeTree : Tree DomainElem :=
    Node "" [
      Node "decodeToAluBuf" [ fifoTree dom capacity DecodeToAluEntry ]
    ].

  Variable pcAddrInit : Z.
  Variable fetchCapacity deferredCapacity : nat.
  Variable bpTree : Tree DomainElem.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.
  Variable meipAct mtipAct : Action ty (memIfc ty).(memTree) Bool.

  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation fTree := (fetchTree dom pcAddrInit fetchCapacity).
  Local Abbreviation dTree := (deferredTree dom deferredCapacity).
  Local Abbreviation coreTree := (coreTree dom rfTree bpTree memTree fTree decodeTree dTree).
  Local Abbreviation regRead := (regRead dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf.").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits.").

  Definition np_mem : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_instFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch..instBuf.fifo").

  Definition np_decodeToAluFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode..decodeToAluBuf.fifo").

  Definition np_deferred : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.").

  (* =========================================================================
   * STAGE 3: decodeAndRegRead
   *
   * - Precondition: instBuf is non-empty and decodeToAluBuf is not full.
   * - Action:       Obtain assembled instruction from instBuf, drop entries
   *                 with mismatched execEpoch, perform full uncompressed
   *                 decode, check GPR/SCR/CSR scoreboard wait bits, read RF,
   *                 set destination wait bits, and enqueue
   *                 { aluIn, predPc, execEpoch } into decodeToAluBuf.
   * ========================================================================= *)
  Definition decodeAndRegRead : Action ty coreTree (Bit 0) :=
    LetA instHead            : Option AssembledInst <- liftAction np_instFifo (@first dom fetchCapacity AssembledInst ty) ;
    LetA decodeToAlu_isFull  : Bool                 <- liftAction np_decodeToAluFifo (@isFull dom capacity DecodeToAluEntry ty) ;
    LetA decodeToAlu_isEmpty : Bool                 <- liftAction np_decodeToAluFifo (@isEmpty dom capacity DecodeToAluEntry ty) ;
    LetA deferred_isEmpty    : Bool                 <- liftAction np_deferred (@deferredIsEmpty dom deferredCapacity ty) ;
    Let  pipelineEmpty       : Bool                 <- And [ #decodeToAlu_isEmpty ; #deferred_isEmpty ] ;

    If (##instHead`"valid") Then (
      Let  asmInst        : AssembledInst  <- ##instHead`"data" ;
      Let  fetchOut       : FetchOut       <- ##asmInst`"fetchOut" ;
      Let  inst           : Inst           <- ##fetchOut`"inst" ;
      Let  predPc         : Addr           <- ##asmInst`"predPc" ;
      Let  entryExecEpoch : Epoch          <- ##asmInst`"execEpoch" ;

      LetA currExecEpoch  : Epoch          <- @readExecEpoch dom rfTree bpTree memTree fTree decodeTree dTree ty ;

      (* Wrong-execEpoch instructions are dropped here *)
      If (Not (Eq #entryExecEpoch #currExecEpoch)) Then (
        liftAction np_instFifo (@deq dom fetchCapacity AssembledInst ty)
      ) Else (
        LetL regReadIn : RegReadIn <- wrappedDecode fetchOut ;
        Let  decodeOut : DecodeOut <- ##regReadIn`"decodeOut" ;

        Let  cs1Idx          : Bit RegIdxSzReal <- ##decodeOut`"cs1Idx" ;
        Let  cs2Idx          : Bit RegIdxSzReal <- ##decodeOut`"cs2Idx" ;
        Let  writesCd        : Bool             <- ##decodeOut`"writesCd" ;
        Let  cdIdx           : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd inst) ;
        Let  readsScr        : Bool             <- ##decodeOut`"readsScr" ;
        Let  writesScr       : Bool             <- ##decodeOut`"writesScr" ;
        Let  readWriteScrIdx : Bit ScrIdxSz     <- ##decodeOut`"readWriteScrIdx" ;
        Let  readsCsr        : Bool             <- ##decodeOut`"readsCsr" ;
        Let  writesCsr       : Bool             <- ##decodeOut`"writesCsr" ;
        Let  readWriteCsrIdx : Bit CsrIdxSz     <- ##decodeOut`"readWriteCsrIdx" ;

        LetA cs1Wait         : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty cs1Idx) ;
        LetA cs2Wait         : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty cs2Idx) ;
        LetA cdWait          : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty cdIdx) ;
        LetA scrWait         : Bool <- liftAction np_waitBits (@readScrWaitBit dom ty readWriteScrIdx) ;
        LetA csrWait         : Bool <- liftAction np_waitBits (@readCsrWaitBit dom ty readWriteCsrIdx) ;

        Let  scrStallEmpty : Bool <- And [ #readsScr ; isStallUntilEmptyScr readWriteScrIdx ] ;
        Let  csrStallEmpty : Bool <- And [ #readsCsr ; isStallUntilEmptyCsr readWriteCsrIdx ] ;

        (* cs1Idx and cs2Idx are set to 0 for instructions that don't read them *)
        (* However, faulting instructions do not set them to 0 *)
        Let  cs1Stall  : Bool <- And [ isNotZero #cs1Idx ; #cs1Wait ] ;
        Let  cs2Stall  : Bool <- And [ isNotZero #cs2Idx ; #cs2Wait ] ;
        Let  cdStall   : Bool <- And [ #writesCd ; #cdWait ] ;
        Let  scrStall  : Bool <- Or [ And [ Or [ #readsScr ; #writesScr ] ; #scrWait ] ;
                                      And [ #scrStallEmpty ; Not #pipelineEmpty ] ] ;
        Let  csrStall  : Bool <- Or [ And [ Or [ #readsCsr ; #writesCsr ] ; #csrWait ] ;
                                      And [ #csrStallEmpty ; Not #pipelineEmpty ] ] ;
        Let  canIssue  : Bool <- Not (Or [ #decodeToAlu_isFull ; #cs1Stall ; #cs2Stall ; #cdStall ; #scrStall ; #csrStall ]) ;

        If #canIssue Then (
          Act (liftAction np_instFifo (@deq dom fetchCapacity AssembledInst ty)) ;

          LetA meip : Bool <- liftAction np_mem meipAct ;
          LetA mtip : Bool <- liftAction np_mem mtipAct ;
          LetA aluInInstGroup : AluInInstGroup <- liftAction np_rf (regRead meip mtip regReadIn) ;

          (* Faulting instructions set random indices to wait, and unset them when the faults are handled *)
          Let waitTrue : Bool <- ConstBool true ;
          Act (liftAction np_waitBits
                 (@setDstWaitBits dom ty
                    writesCd cdIdx
                    writesScr readWriteScrIdx
                    writesCsr readWriteCsrIdx
                    waitTrue)) ;

          Let d2aEntry : DecodeToAluEntry <- STRUCT {
            "aluIn"     ::= #aluInInstGroup ;
            "predPc"    ::= #predPc ;
            "execEpoch" ::= #currExecEpoch
          } ;
          liftAction np_decodeToAluFifo (@enq dom capacity DecodeToAluEntry ty d2aEntry)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End DecodeStage.
