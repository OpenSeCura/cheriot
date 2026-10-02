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
From Cheriot Require Import SpecDefines Fifo.

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

Definition FetchBufEntry := STRUCT_TYPE {
  "pcAddr"   :: Addr ;
  "predPc"   :: Addr ;
  "epoch"    :: Epoch ;
  "fetchExc" :: FetchException
}.

Definition DecodeToAluEntry := STRUCT_TYPE {
  "aluIn"  :: AluInInstGroup ;
  "predPc" :: Addr ;
  "epoch"  :: Epoch
}.

(* ===========================================================================
 * Hardware Pipeline State Trees & Register Accessors
 * =========================================================================== *)

Section ImplCommon.
  Variable dom : string.
  Variable pcAddrInit : Z.

  (* 1. Scoreboard (waitBits) *)
  Definition gprWaitLeaves : list (Tree DomainElem) :=
    map (fun '(_, idx) =>
      Leaf ("waitBit_" ++ hex_string_of_Z idx)%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (enumerate (repeat tt (Z.to_nat NumRegs))).

  Definition scrWaitLeaves : list (Tree DomainElem) :=
    map (fun e =>
      Leaf ("waitBit_" ++ e.(scrName))%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (ScrTable 0).

  Definition csrWaitLeaves : list (Tree DomainElem) :=
    map (fun e =>
      Leaf ("waitBit_" ++ e.(csrName))%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) PhysicalCsrTable.

  Definition waitBitsTree : Tree DomainElem :=
    Node "waitBits" [
      Node "gprs" gprWaitLeaves ;
      Node "scrs" scrWaitLeaves ;
      Node "csrs" csrWaitLeaves
    ].

  Definition np_waitGprs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree "waitBits.gprs").
  Definition np_waitScrs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree "waitBits.scrs").
  Definition np_waitCsrs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree "waitBits.csrs").

  Definition gprWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (map (embedRegOfKind np_waitGprs)
                     (getTreeRegsOfKind Bool (getNode np_waitGprs))).

  Definition scrWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (map (embedRegOfKind np_waitScrs)
                     (getTreeRegsOfKind Bool (getNode np_waitScrs))).

  Definition csrWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (map (embedRegOfKind np_waitCsrs)
                     (getTreeRegsOfKind Bool (getNode np_waitCsrs))).

  Definition readGprWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal))
    : Action ty waitBitsTree Bool :=
    readRegsList gprWaitPathsWithKind idx.

  Definition writeGprWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList gprWaitPathsWithKind idx val.

  Definition readScrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit ScrIdxSz))
    : Action ty waitBitsTree Bool :=
    readRegsList scrWaitPathsWithKind idx.

  Definition writeScrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit ScrIdxSz)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList scrWaitPathsWithKind idx val.

  Definition readCsrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit CsrIdxSz))
    : Action ty waitBitsTree Bool :=
    readRegsList csrWaitPathsWithKind idx.

  Definition writeCsrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit CsrIdxSz)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList csrWaitPathsWithKind idx val.

  (* 2. Core Tree *)
  Definition coreTree (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem) : Tree DomainElem :=
    Node "core" [
      rfTree dom pcAddrInit ;
      waitBitsTree ;
      Node "bp"       [ bpTree ] ;
      Leaf "currEpoch" (dom, EReg (Build_Reg Epoch (Some Zmod.zero) false)) ;
      Node "mem"      [ memTree ] ;
      Node "fetch"    [ fetchTree ] ;
      Node "decode"   [ decodeTree ] ;
      Node "deferred" [ deferredTree ]
    ].

  Definition pCurrEpoch (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem)
    : RegPath (coreTree bpTree memTree fetchTree decodeTree deferredTree) :=
    Eval cbn in (getChildRegPathTree (coreTree bpTree memTree fetchTree decodeTree deferredTree) "currEpoch").

  Definition readCurrEpoch (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem) (ty : Kind -> Type)
    : Action ty (coreTree bpTree memTree fetchTree decodeTree deferredTree) Epoch :=
    ReadReg "currEpoch" (pCurrEpoch bpTree memTree fetchTree decodeTree deferredTree) (fun v => Return #v).

  Definition writeCurrEpoch (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem) (ty : Kind -> Type)
    (val : Expr ty Epoch) : Action ty (coreTree bpTree memTree fetchTree decodeTree deferredTree) (Bit 0) :=
    WriteReg (pCurrEpoch bpTree memTree fetchTree decodeTree deferredTree) val Retv.

End ImplCommon.
