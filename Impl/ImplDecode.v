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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu Fifo ImplCommon ImplBranchPredictor ImplDevice ImplFetch ImplDeferred.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section DecodeStage.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable capacity : nat.

  Definition decodeTree : Tree DomainElem :=
    Node "decode" [
      Leaf "decodePc"        (dom, EReg (Build_Reg Addr (Some (Zmod.of_Z _ pcAddrInit)) false)) ;
      Node "decodeToAluBuf" [ fifoTree dom capacity DecodeToAluEntry ]
    ].

  Definition pDecodePc : RegPath decodeTree :=
    Eval cbn in (getChildRegPathTree decodeTree "decodePc").

  Definition readDecodePc (ty : Kind -> Type) : Action ty decodeTree Addr :=
    ReadReg "decodePc" pDecodePc (fun v => Return #v).

  Definition writeDecodePc (ty : Kind -> Type) (val : Expr ty Addr) : Action ty decodeTree (Bit 0) :=
    WriteReg pDecodePc val Retv.

  Variable fetchCapacity deferredCapacity : nat.
  Variable noInstTree : Tree DomainElem.
  Variable withInstIfc : forall ty, @WithInstPredIfc noInstTree ty.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.
  Variable meipAct mtipAct : Action ty (memIfc ty).(memTree) Bool.

  Local Notation bpTree := (bpTree noInstTree (withInstIfc ty).(withInstTree)).
  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation fTree := (fetchTree dom pcAddrInit fetchCapacity).
  Local Notation dTree := (deferredTree dom deferredCapacity).
  Local Notation coreTree := (coreTree dom pcAddrInit bpTree memTree fTree decodeTree dTree).
  Local Notation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).
  Local Notation regRead := (regRead dom pcAddrInit).

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

  Definition np_fetchFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.fetch.fetchBuf.fifo").

  Definition np_decode : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode.decode").

  Definition np_decodeToAluFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode.decode.decodeToAluBuf.fifo").

  Definition np_deferred : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.deferred").

  (* =========================================================================
   * STAGE 2: decodeAndRegRead
   *
   * - Precondition: fetchBuf is non-empty and decodeToAluBuf is not full.
   * - Action:       Obtain instruction response (or synthesize 0 on pre-fault),
   *                 drop wrong-epoch or wrong-PC entries, decode instruction,
   *                 check GPR/SCR/CSR scoreboard wait bits, read RF, set
   *                 destination wait bits, query Level-2 branch predictor,
   *                 and enqueue { aluIn, predPc, epoch } into decodeToAluBuf.
   * ========================================================================= *)
  Definition decodeAndRegRead : Action ty coreTree (Bit 0) :=
    LetA fetchHead           : Option FetchBufEntry <- liftAction np_fetchFifo (@first dom fetchCapacity FetchBufEntry ty) ;
    LetA decodeToAlu_isFull  : Bool                 <- liftAction np_decodeToAluFifo (@isFull dom capacity DecodeToAluEntry ty) ;
    LetA decodeToAlu_isEmpty : Bool                 <- liftAction np_decodeToAluFifo (@isEmpty dom capacity DecodeToAluEntry ty) ;
    LetA deferred_isEmpty    : Bool                 <- liftAction np_deferred (@deferredIsEmpty dom deferredCapacity ty) ;
    Let  pipelineEmpty       : Bool                 <- And [ #decodeToAlu_isEmpty ; #deferred_isEmpty ] ;

    If (And [ ##fetchHead`"valid" ; Not #decodeToAlu_isFull ]) Then (
      Let entry       : FetchBufEntry  <- ##fetchHead`"data" ;
      Let pcAddr      : Addr           <- ##entry`"pcAddr" ;
      Let predPc      : Addr           <- ##entry`"predPc" ;
      Let epoch       : Epoch          <- ##entry`"epoch" ;
      Let preExc      : FetchException <- ##entry`"fetchExc" ;
      Let hasPreFault : Bool           <- Or [ ##preExc`"tag" ;
                                               ##preExc`"seal" ;
                                               ##preExc`"perm" ;
                                               ##preExc`"bounds" ] ;

      LetIf instOpt : Option Inst <-
        If #hasPreFault Then (
          Return (mkSome ($0 : Expr ty Inst))
        ) Else (
          liftAction np_mem ((memIfc ty).(mem_getInstRp) pcAddr)
        ) ;

      If (##instOpt`"valid") Then (
        Let  rawInst    : Inst        <- ##instOpt`"data" ;
        LetA currEpoch  : Epoch       <- @readCurrEpoch dom pcAddrInit bpTree memTree fTree decodeTree dTree ty ;
        LetA decodePc   : Addr        <- liftAction np_decode (@readDecodePc ty) ;

        (* Bad epoch instructions need to be dropped here. Otherwise decode will redirect PC
           even though it is in the wrong path *)
        Let  isExpected : Bool        <- And [ Eq #epoch #currEpoch ;
                                               Eq #pcAddr #decodePc ] ;

        If (Not #isExpected) Then (
          Act (liftAction np_fetchFifo (@deq dom fetchCapacity FetchBufEntry ty)) ;
          If (Not #hasPreFault) Then (
            liftAction np_mem ((memIfc ty).(mem_deqInstRp) pcAddr)
          ) ;
          Retv
        ) Else (
          LetA pcc       : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
          Let  pccECap   : ECap            <- ##pcc`"ecap" ;
          Let  isComp    : Bool            <- isCompressed rawInst ;
          Let  instBytes : Addr            <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
          Let  topExc    : Bool            <- Ugt (ZeroExtendTo (AddrSz + 2) (Add [ #pcAddr ; #instBytes ])) (##pccECap`"top") ;
          Let  fetchExc  : FetchException  <- #preExc `{ "bounds" <- Or [ ##preExc`"bounds" ; #topExc ] } ;
          Let  instPcc   : FullECapWithTag <- #pcc `{ "addr" <- #pcAddr } ;
          Let  fetchOut  : FetchOut        <- STRUCT {
            "pcc"      ::= #instPcc ;
            "inst"     ::= #rawInst ;
            "fetchExc" ::= #fetchExc
          } ;

          LetL regReadIn : RegReadIn <- wrappedDecode fetchOut ;
          Let  decodeOut : DecodeOut <- ##regReadIn`"decodeOut" ;

          Let  instGroup : InstGroup             <- ##decodeOut`"instGroup" ;
          Let  cs1Idx    : Bit RegIdxSzReal      <- ##decodeOut`"cs1Idx" ;
          Let  cs2Source : TaggedUnion Cs2Source <- ##decodeOut`"cs2Idx" ;
          Let  cs2IsReg  : Bool                  <- #cs2Source `? "Reg" ;
          Let  cs2Idx    : Bit RegIdxSzReal      <- #cs2Source `! "Reg" ;
          Let  writesCd  : Bool                  <- ##decodeOut`"writesCd" ;
          Let  instBits  : Inst                  <- ##decodeOut`"instBits" ;
          Let  cdIdx     : Bit RegIdxSzReal      <- TruncLsb 1 RegIdxSzReal (getCd instBits) ;

          LetL wInfo           : WaitSpecialInfo <- getWaitSpecialInfo instGroup cs2Source ;
          Let  readsScr        : Bool            <- ##wInfo`"readsScr" ;
          Let  writesScr       : Bool            <- ##wInfo`"writesScr" ;
          Let  readWriteScrIdx : Bit ScrIdxSz    <- ##wInfo`"readWriteScrIdx" ;
          Let  readsCsr        : Bool            <- ##wInfo`"readsCsr" ;
          Let  readCsrIdx      : Bit CsrIdxSz    <- ##wInfo`"readCsrIdx" ;
          Let  writesCsr       : Bool            <- ##wInfo`"writesCsr" ;
          Let  writeCsrIdx     : Bit CsrIdxSz    <- ##wInfo`"writeCsrIdx" ;

          LetA cs1Wait      : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty #cs1Idx) ;
          LetA cs2Wait      : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty #cs2Idx) ;
          LetA cdWait       : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty #cdIdx) ;
          LetA scrWait      : Bool <- liftAction np_waitBits (@readScrWaitBit dom ty #readWriteScrIdx) ;
          LetA csrReadWait  : Bool <- liftAction np_waitBits (@readCsrWaitBit dom ty #readCsrIdx) ;
          LetA csrWriteWait : Bool <- liftAction np_waitBits (@readCsrWaitBit dom ty #writeCsrIdx) ;
          LetA mstatusWait  : Bool <- liftAction np_waitBits (@readCsrWaitBit dom ty ($(getCsrPhysicalIdx "mstatus") : Expr ty (Bit CsrIdxSz))) ;

          Let  scrStallEmpty : Bool <- And [ #readsScr ; isStallUntilEmptyScr #readWriteScrIdx ] ;
          Let  csrStallEmpty : Bool <- And [ #readsCsr ; isStallUntilEmptyCsr #readCsrIdx ] ;

          (* cs1Idx and cs2Idx are set to 0 for instructions that don't read them *)
          (* However, faulting instructions do not set them to 0 *)
          Let  cs1Stall  : Bool <- And [ isNotZero #cs1Idx ; #cs1Wait ] ;
          Let  cs2Stall  : Bool <- And [ #cs2IsReg ; isNotZero #cs2Idx ; #cs2Wait ] ;
          Let  cdStall   : Bool <- And [ #writesCd ; isNotZero #cdIdx ; #cdWait ] ;
          Let  scrStall  : Bool <- Or [ And [ Or [#readsScr ; #writesScr ] ; #scrWait ] ;
                                        And [ #scrStallEmpty ; Not #pipelineEmpty ] ] ;
          Let  csrStall  : Bool <- Or [ #mstatusWait ;
                                        And [ #readsCsr ; #csrReadWait ] ;
                                        And [ #writesCsr ; #csrWriteWait ] ;
                                        And [ #csrStallEmpty ; Not #pipelineEmpty ] ] ;
          Let  canIssue  : Bool <- Not (Or [ #cs1Stall ; #cs2Stall ; #cdStall ; #scrStall ; #csrStall ]) ;

          If #canIssue Then (
            Act (liftAction np_fetchFifo (@deq dom fetchCapacity FetchBufEntry ty)) ;
            If (Not #hasPreFault) Then (
              liftAction np_mem ((memIfc ty).(mem_deqInstRp) pcAddr)
            ) ;

            LetA meip : Bool <- liftAction np_mem meipAct ;
            LetA mtip : Bool <- liftAction np_mem mtipAct ;
            LetA aluInInstGroup : AluInInstGroup <- liftAction np_rf (regRead meip mtip regReadIn) ;

            (* Faulting instructions set random indices to wait, and unset them when the faults are handled *)
            Act (liftAction np_waitBits
                   (@setDstWaitBits dom ty
                      (And [ #writesCd ; isNotZero #cdIdx ]) #cdIdx
                      wInfo
                      (ConstBool true))) ;

            LetA withInstPcPred : Addr <- liftAction np_bp ((withInstIfc ty).(withInst_getPred) pcAddr predPc decodeOut) ;
            Act (liftAction np_decode (@writeDecodePc ty #withInstPcPred)) ;
            If (Not (Eq #withInstPcPred #predPc)) Then (
              liftAction np_fetch (@writeFetchPc dom pcAddrInit fetchCapacity ty #withInstPcPred)
            ) ;

            Let d2aEntry : DecodeToAluEntry <- STRUCT {
              "aluIn"  ::= #aluInInstGroup ;
              "predPc" ::= #withInstPcPred ;
              "epoch"  ::= #currEpoch
            } ;
            liftAction np_decodeToAluFifo (@enq dom capacity DecodeToAluEntry ty d2aEntry)
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End DecodeStage.
