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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu ShiftFifo ImplCommon ImplDevice.

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

  Definition implDecodeTree : Tree DomainElem :=
    Node "" [
      Leaf "canProceed"      (dom, EReg (Build_Reg Bool (Some true) false)) ;
      Node "decodeToAluBuf" [ fifoTree dom capacity DecodeToAluEntry ]
    ].

  Definition pDecodeCanProceed : RegPath implDecodeTree :=
    Eval cbn in (getChildRegPathTree implDecodeTree "canProceed").

  Definition readDecodeCanProceed (ty : Kind -> Type) : Action ty implDecodeTree Bool :=
    ReadReg "canProceed" pDecodeCanProceed (fun v => Return #v).

  Definition setDecodeCanProceed (ty : Kind -> Type) : Action ty implDecodeTree (Bit 0) :=
    WriteReg pDecodeCanProceed (ConstBool true) Retv.

  Definition clearDecodeCanProceed (ty : Kind -> Type) : Action ty implDecodeTree (Bit 0) :=
    WriteReg pDecodeCanProceed (ConstBool false) Retv.

  Definition np_decToAluFifo : NodePath implDecodeTree :=
    Eval cbn in (getNodePath implDecodeTree ".decodeToAluBuf.fifo").

  Definition decodeFirst (ty : Kind -> Type) : Action ty implDecodeTree (Option DecodeToAluEntry) :=
    liftAction np_decToAluFifo (@first dom capacity DecodeToAluEntry ty).

  Definition decodeDeq (ty : Kind -> Type) : Action ty implDecodeTree (Bit 0) :=
    liftAction np_decToAluFifo (@deq dom capacity DecodeToAluEntry ty).

  Definition implDecodeIfc (ty : Kind -> Type) : @DecodeIfc ty := {|
    decodeTree   := implDecodeTree ;
    decode_first := @decodeFirst ty ;
    decode_deq   := @decodeDeq ty
  |}.

  Variable pcAddrInit : Z.
  Variable bpTree mulDivTree : Tree DomainElem.
  Variable fetchIfc : forall ty, @FetchIfc ty.
  Variable executeIfc : forall ty, @ExecuteIfc ty.
  Variable dataMemIfc : forall ty, @DataMemIfc ty.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation fetchTree := (fetchIfc ty).(fetchTree).
  Local Abbreviation executeTree := (executeIfc ty).(executeTree).
  Local Abbreviation dataMemTree := (dataMemIfc ty).(dataMemTree).
  Local Abbreviation coreTree := (coreTree dom rfTree bpTree memTree fetchTree implDecodeTree executeTree dataMemTree mulDivTree).
  Local Abbreviation regRead := (regRead dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf.").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits.").

  Definition np_fetch : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.fetch") singletonChildPath).

  Definition np_decode : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode.").

  Definition np_decodeToAluFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.decode..decodeToAluBuf.fifo").

  Definition np_execute : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.execute") singletonChildPath).

  (* =========================================================================
   * STAGE 3: decodeAndRegRead
   *
   * - Precondition: instBuf is non-empty and decodeToAluBuf is not full.
   * - Action:       Obtain assembled instruction from instBuf, drop entries
   *                 with mismatched execEpoch, perform full uncompressed
   *                 decode, check GPR scoreboard wait bits, read GPRs,
   *                 set destination GPR wait bit, and enqueue
   *                 { aluIn, predPc, execEpoch } into decodeToAluBuf.
   * ========================================================================= *)
  Definition decodeAndRegRead : Action ty coreTree (Bit 0) :=
    LetA canProceed          : Bool                 <- liftAction np_decode (@readDecodeCanProceed ty) ;

    If #canProceed Then (
      Act (liftAction np_decode (@clearDecodeCanProceed ty)) ;

      LetA instHead            : Option AssembledInst <- liftAction np_fetch (fetchIfc ty).(fetch_instFirst) ;
      LetA decodeToAlu_isFull  : Bool                 <- liftAction np_decodeToAluFifo (@isFull dom capacity DecodeToAluEntry ty) ;
      LetA currExecEpoch       : Epoch                <- liftAction np_execute (executeIfc ty).(execute_readExecEpoch) ;

      Let  asmInst          : AssembledInst   <- ##instHead`"data" ;
      Let  fetchOut         : FetchOut        <- ##asmInst`"fetchOut" ;
      Let  inst             : Inst            <- ##fetchOut`"inst" ;
      Let  predPc           : Addr            <- ##asmInst`"predPc" ;
      Let  entryExecEpoch   : Epoch           <- ##asmInst`"execEpoch" ;

      LetL regReadIn        : RegReadIn       <- wrappedDecode fetchOut ;
      Let  decodeOut        : DecodeOut       <- ##regReadIn`"decodeOut" ;
      LetA aluInInstGroup   : AluInInstGroup  <- liftAction np_rf (regRead regReadIn) ;

      Let  cs1Idx           : Bit RegIdxSzReal <- ##decodeOut`"cs1Idx" ;
      Let  cs2Idx           : Bit RegIdxSzReal <- ##decodeOut`"cs2Idx" ;
      Let  writesCd         : Bool             <- ##decodeOut`"writesCd" ;
      Let  cdIdx            : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd inst) ;

      LetA cs1Wait          : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty cs1Idx) ;
      LetA cs2Wait          : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty cs2Idx) ;
      LetA cdWait           : Bool <- liftAction np_waitBits (@readGprWaitBit dom ty cdIdx) ;

      If (##instHead`"valid") Then (
        (* Wrong-execEpoch instructions are dropped here *)
        If (Not (Eq #entryExecEpoch #currExecEpoch)) Then (
          liftAction np_fetch (fetchIfc ty).(fetch_instDeq)
        ) Else (
          (* cs1Idx and cs2Idx are set to 0 for instructions that don't read them *)
          (* However, faulting instructions do not set them to 0 *)
          Let  cs1Stall  : Bool <- And [ isNotZero #cs1Idx ; #cs1Wait ] ;
          Let  cs2Stall  : Bool <- And [ isNotZero #cs2Idx ; #cs2Wait ] ;
          Let  cdStall   : Bool <- And [ #writesCd ; #cdWait ] ;
          Let  canIssue  : Bool <- Not (Or [ #decodeToAlu_isFull ; #cs1Stall ; #cs2Stall ; #cdStall ]) ;

          If #canIssue Then (
            Act (liftAction np_decode (@setDecodeCanProceed ty)) ;
            Act (liftAction np_fetch (fetchIfc ty).(fetch_instDeq)) ;

            (* Faulting instructions set random indices to wait, and unset them when the faults are handled *)
            Let waitTrue : Bool <- ConstBool true ;
            Act (liftAction np_waitBits
                   (@setDstWaitBits dom ty
                      writesCd cdIdx
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
      Retv
    ) ;
    Retv.

End DecodeStage.
