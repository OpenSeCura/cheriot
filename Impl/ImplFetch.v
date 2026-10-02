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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits ImplCommon ImplBranchPredictor ImplDevice Alu Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section FetchStage.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable capacity : nat.

  Definition fetchTree : Tree DomainElem :=
    Node "fetch" [
      Leaf "fetchPc"  (dom, EReg (Build_Reg Addr (Some (Zmod.of_Z _ pcAddrInit)) false)) ;
      Node "fetchBuf" [ fifoTree dom capacity FetchBufEntry ]
    ].

  Definition pFetchPc : RegPath fetchTree :=
    Eval cbn in (getChildRegPathTree fetchTree "fetchPc").

  Definition readFetchPc (ty : Kind -> Type) : Action ty fetchTree Addr :=
    ReadReg "fetchPc" pFetchPc (fun v => Return #v).

  Definition writeFetchPc (ty : Kind -> Type) (val : Expr ty Addr) : Action ty fetchTree (Bit 0) :=
    WriteReg pFetchPc val Retv.

  Variable noInstIfc : forall ty, @NoInstPredIfc ty.
  Variable withInstTree : Tree DomainElem.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable decodeTree deferredTree : Tree DomainElem.
  Variable ty : Kind -> Type.

  Local Notation bpTree := (bpTree (noInstIfc ty).(noInstTree) withInstTree).
  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation coreTree := (coreTree dom pcAddrInit bpTree memTree fetchTree decodeTree deferredTree).
  Local Notation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf").

  Definition np_noInst : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.bp.bp.noInst") singletonChildPath).

  Definition np_mem : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_fetch : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.fetch").

  Definition np_fetchFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.fetch.fetchBuf.fifo").

  (* =========================================================================
   * STAGE 1: fetchRq
   *
   * - Precondition: fetchBuf is not full (!isFull).
   * - Action:       Read fetchPc, currEpoch, and global PCC metadata from GPR 0.
   *                 Perform pre-fetch Tag, Seal, EX-perm, and Base-bounds checks.
   *                 If no fault so far, issue mem_readInstRq(fetchPc).
   *                 When pre-fault or request accepted, predict nextPc via
   *                 noInst_getPred(fetchPc), enqueue { pcAddr, predPc, epoch,
   *                 fetchExc } into fetchBuf, and advance fetchPc to predPc.
   * ========================================================================= *)
  Definition fetchRq : Action ty coreTree (Bit 0) :=
    LetA fetchBuf_isFull : Bool <- liftAction np_fetchFifo (@isFull dom capacity FetchBufEntry ty) ;

    If (Not #fetchBuf_isFull) Then (
      LetA fetchPc   : Addr            <- liftAction np_fetch (@readFetchPc ty) ;
      LetA currEpoch : Epoch           <- @readCurrEpoch dom pcAddrInit bpTree memTree fetchTree decodeTree deferredTree ty ;
      LetA pcc       : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;

      Let  pccECap     : ECap <- ##pcc`"ecap" ;
      Let  tagExc      : Bool <- Not ##pcc`"tag" ;
      Let  sealExc     : Bool <- isSealed pccECap ;
      Let  permExc     : Bool <- Not (##pccECap`"perms"`"EX") ;
      Let  baseBndsExc : Bool <- Ult (ZeroExtendTo (AddrSz + 2) #fetchPc) (ZeroExtendTo (AddrSz + 2) ##pccECap`"base") ;
      Let  hasPreFault : Bool <- Or [ #tagExc ; #sealExc ; #permExc ; #baseBndsExc ] ;

      Let  preFetchExc : FetchException <- STRUCT {
        "tag"    ::= #tagExc ;
        "seal"   ::= #sealExc ;
        "perm"   ::= #permExc ;
        "bounds" ::= #baseBndsExc
      } ;

      LetIf canEnq : Bool <-
        If #hasPreFault Then (
          Return (ConstBool true)
        ) Else (
          liftAction np_mem ((memIfc ty).(mem_readInstRq) fetchPc)
        ) ;

      If #canEnq Then (
        LetA predPc : Addr <- liftAction np_noInst ((noInstIfc ty).(noInst_getPred) fetchPc) ;
        Let  entry  : FetchBufEntry <- STRUCT {
          "pcAddr"   ::= #fetchPc ;
          "predPc"   ::= #predPc ;
          "epoch"    ::= #currEpoch ;
          "fetchExc" ::= #preFetchExc
        } ;
        Act (liftAction np_fetchFifo (@enq dom capacity FetchBufEntry ty entry)) ;
        liftAction np_fetch (@writeFetchPc ty #predPc)
      ) ;
      Retv
    ) ;
    Retv.

End FetchStage.
