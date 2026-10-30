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
From Cheriot Require Import SpecDefines FunctionalUnits ShiftFifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Hardware Pipeline Parameters & Data Types
 * =========================================================================== *)

Definition EpochSz : Z := 1.
Definition Epoch   : Kind := Bit EpochSz.

(* A fetch packet is a whole memory line of 16-bit parcels *)
Definition LgFetchParcels  : Z    := Eval compute in (LgLineBytes - Z.log2 (CompInstSz / 8)).
Definition NumFetchParcels : nat  := Eval compute in Z.to_nat (2 ^ LgFetchParcels).
Definition FetchPacket     : Kind := Array NumFetchParcels (Bit CompInstSz).

Definition PreBranchInfo := STRUCT_TYPE {
  "isCjal"   :: Bool ;
  "isBranch" :: Bool ;
  "isCjalr"  :: Bool ;
  "isCall"   :: Bool ;
  "isReturn" :: Bool
}.

Definition FetchBufEntry := STRUCT_TYPE {
  "pcAddr"     :: Addr ;
  "predPc"     :: Addr ;
  "exitParcel" :: Bit LgFetchParcels ;
  "execEpoch"  :: Epoch ;
  "predEpoch"  :: Epoch ;
  "fetchExc"   :: FetchException
}.

Definition AssembledInst := STRUCT_TYPE {
  "fetchOut"  :: FetchOut ;
  "predPc"    :: Addr ;
  "execEpoch" :: Epoch
}.

Definition DecodeToAluEntry := STRUCT_TYPE {
  "aluIn"     :: AluInInstGroup ;
  "predPc"    :: Addr ;
  "execEpoch" :: Epoch
}.

(* ===========================================================================
 * Pipeline Stage Interfaces
 * =========================================================================== *)

Record FetchIfc {ty : Kind -> Type} := {
  fetchTree           : Tree DomainElem ;
  fetch_instFirst     : Action ty fetchTree (Option AssembledInst) ;
  fetch_instDeq       : Action ty fetchTree (Bit 0) ;
  fetch_clearStraddle : Action ty fetchTree (Bit 0) ;
  fetch_writeFetchPc  : ty Addr -> Action ty fetchTree (Bit 0)
}.

Record DecodeIfc {ty : Kind -> Type} := {
  decodeTree   : Tree DomainElem ;
  decode_first : Action ty decodeTree (Option DecodeToAluEntry) ;
  decode_deq   : Action ty decodeTree (Bit 0)
}.

Record ExecuteIfc {ty : Kind -> Type} := {
  executeTree             : Tree DomainElem ;
  execute_readExecEpoch   : Action ty executeTree Epoch ;
  execute_readFenceIPend  : Action ty executeTree Bool ;
  execute_clearFenceIPend : Action ty executeTree (Bit 0)
}.

Record DataMemIfc {ty : Kind -> Type} := {
  dataMemTree     : Tree DomainElem ;
  dataMem_isEmpty : Action ty dataMemTree Bool ;
  dataMem_isFull  : Action ty dataMemTree Bool ;
  dataMem_enq     : ty (Bit RegIdxSzReal) -> ty Addr -> ty MemFenceUnion -> Action ty dataMemTree (Bit 0)
}.

Record MulDivIfc {ty : Kind -> Type} := {
  mulDivTree       : Tree DomainElem ;
  mulDiv_isFullMul : Action ty mulDivTree Bool ;
  mulDiv_isFullDiv : Action ty mulDivTree Bool ;
  mulDiv_enqMul    : ty (Bit RegIdxSzReal) -> ty Addr -> ty MulOp -> Action ty mulDivTree (Bit 0) ;
  mulDiv_enqDiv    : ty (Bit RegIdxSzReal) -> ty Addr -> ty DivOp -> Action ty mulDivTree (Bit 0)
}.

(* ===========================================================================
 * Hardware Pipeline State Trees & Register Accessors
 * =========================================================================== *)

Section ImplCommon.
  Variable dom : string.

  (* 1. Scoreboard (waitBits) *)
  Definition gprWaitLeaves : list (Tree DomainElem) :=
    map (fun '(_, idx) =>
      Leaf ("waitBit_" ++ hex_string_of_Z idx)%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (enumerate (repeat tt (Z.to_nat NumRegs))).

  Definition waitBitsTree : Tree DomainElem :=
    Node "" [
      Node "gprs" gprWaitLeaves
    ].

  Definition np_waitGprs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree ".gprs").

  Definition gprWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbv in (map (embedRegOfKind np_waitGprs)
                     (getTreeRegsOfKind Bool (getNode np_waitGprs))).

  Definition readGprWaitBit (ty : Kind -> Type) (idx : ty (Bit RegIdxSzReal))
    : Action ty waitBitsTree Bool :=
    readRegsList gprWaitPathsWithKind #idx.

  Definition writeGprWaitBit (ty : Kind -> Type) (idx : ty (Bit RegIdxSzReal)) (val : ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList gprWaitPathsWithKind #idx #val.

  Definition setDstWaitBits (ty : Kind -> Type)
    (writesGpr : ty Bool) (gprIdx : ty (Bit RegIdxSzReal))
    (val : ty Bool) : Action ty waitBitsTree (Bit 0) :=
    If #writesGpr Then (
      writeGprWaitBit gprIdx val
    ) ;
    Retv.

  (* 2. Core Tree *)
  Definition coreTree (rfTree bpTree memTree fetchTree decodeTree executeTree dataMemTree mulDivTree : Tree DomainElem) : Tree DomainElem :=
    Node "core" [
      Node "rf"       [ rfTree ] ;
      Node "waitBits" [ waitBitsTree ] ;
      Node "bp"       [ bpTree ] ;
      Node "mem"      [ memTree ] ;
      Node "fetch"    [ fetchTree ] ;
      Node "decode"   [ decodeTree ] ;
      Node "execute"  [ executeTree ] ;
      Node "dataMem"  [ dataMemTree ] ;
      Node "mulDiv"   [ mulDivTree ]
    ].

End ImplCommon.
