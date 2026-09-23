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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits ImplDefines ImplDevice Alu Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section FetchStages.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity deferredCapacity : nat.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation coreTree := (coreTree dom pcAddrInit memTree fetchCapacity deferredCapacity).
  Local Notation capacity := fetchCapacity.
  Local Notation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits").

  Definition np_mem : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_fetchFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.fetchBuf.fifo").

  Definition np_fetchOutFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.fetchOutBuf.fifo").

  (* =========================================================================
   * STAGE 1: fetchRq
   *
   * - Preconditions: fetchBuf is not full (!isFull) and PCC waitBit ($0) is false.
   * - Action:        Read architectural PCC from Register File (GPR 0).
   *                  Issue mem_readInstRq pcc.addr to instruction memory.
   *                  If accepted, enqueue pcc into fetchBuf and set waitBits[$0].
   * ========================================================================= *)
  Definition fetchRq : Action ty coreTree (Bit 0) :=
    LetA fetchBuf_isFull : Bool <- liftAction np_fetchFifo (@isFull dom capacity FullECapWithTag ty) ;
    LetA pccWait         : Bool <- liftAction np_waitBits (@readWaitBit dom ty ($0 : Expr ty (Bit RegIdxSzReal))) ;

    If (And [ Not #fetchBuf_isFull ; Not #pccWait ]) Then (
      LetA pcc      : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
      Let  pccAddr  : Addr            <- ##pcc`"addr" ;
      LetA accepted : Bool            <- liftAction np_mem ((memIfc ty).(mem_readInstRq) pccAddr) ;
      If #accepted Then (
        Act (liftAction np_fetchFifo (@enq dom capacity FullECapWithTag ty pcc)) ;
        liftAction np_waitBits (@writeWaitBit dom ty ($0 : Expr ty (Bit RegIdxSzReal)) (ConstBool true))
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: fetchRp
   *
   * - Preconditions: fetchBuf has pending request (!isEmpty) and fetchOutBuf is not full.
   * - Action:        Poll mem_getInstRp. If Some rawInst:
   *                  Dequeue pcc from fetchBuf.
   *                  Evaluate CHERIoT Fetch Exceptions on PCC and instruction length.
   *                  Enqueue FetchOut { pcc, inst, fetchExc } into fetchOutBuf.
   * ========================================================================= *)
  Definition fetchRp : Action ty coreTree (Bit 0) :=
    LetA inputHead          : Option FullECapWithTag <- liftAction np_fetchFifo (@first dom capacity FullECapWithTag ty) ;
    LetA fetchOutBuf_isFull : Bool                   <- liftAction np_fetchOutFifo (@isFull dom capacity FetchOut ty) ;

    If (And [ ##inputHead `? "Some" ; Not #fetchOutBuf_isFull ]) Then (
      LetA instOpt : Option Inst <- liftAction np_mem ((memIfc ty).(mem_getInstRp)) ;
      If (##instOpt `? "Some") Then (
        Let pcc     : FullECapWithTag <- ##inputHead `! "Some" ;
        Let rawInst : Inst            <- ##instOpt `! "Some" ;
        Act (liftAction np_fetchFifo (@deq dom capacity FullECapWithTag ty)) ;

        (* Fetch Exception Checks *)
        Let pccECap   : ECap <- ##pcc`"ecap" ;
        Let isComp    : Bool <- isCompressed rawInst ;
        Let instBytes : Addr <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
        Let tagExc    : Bool <- Not ##pcc`"tag" ;
        Let sealExc   : Bool <- isSealed pccECap ;
        Let permExc   : Bool <- Not (##pccECap`"perms"`"EX") ;
        Let boundsExc : Bool <- Or [
          Ult (ZeroExtendTo (AddrSz + 2) ##pcc`"addr") (ZeroExtendTo (AddrSz + 2) ##pccECap`"base") ;
          Ugt (ZeroExtendTo (AddrSz + 2) (Add [ ##pcc`"addr" ; #instBytes ])) (##pccECap`"top")
        ] ;

        Let fetchOut : FetchOut <- STRUCT {
          "pcc"         ::= #pcc ;
          "inst"        ::= #rawInst ;
          "fetchExc"    ::= STRUCT {
            "tag"    ::= #tagExc ;
            "seal"   ::= #sealExc ;
            "perm"   ::= #permExc ;
            "bounds" ::= #boundsExc
          }
        } ;
        liftAction np_fetchOutFifo (@enq dom capacity FetchOut ty fetchOut)
      ) ;
      Retv
    ) ;
    Retv.
End FetchStages.
