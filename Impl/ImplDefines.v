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
From Cheriot Require Import SpecDefines SpecFetchDeferred Fifo ImplMulDiv.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Hardware Pipeline / Queue Tree Definitions
 * =========================================================================== *)

Definition ImplInputWidth : nat := 32%nat.
Definition ImplMulStages  : nat := 1%nat.
Definition ImplDivStages  : nat := 1%nat.
Definition ImplMulDivMode : MulDivMode := IterMul_SharedIterDiv.

Section ImplDefines.
  Variable dom : string.
  Variable pcAddrInit : Z.

  Definition WaitBitsKind : Kind := Array (Z.to_nat (2 ^ RegIdxSzReal)) Bool.

  Definition waitBitsTree : Tree DomainElem :=
    Leaf "waitBits" (dom, EReg (Build_Reg WaitBitsKind (Some (getDefault _)) false)).

  Definition pWaitBits : RegPath waitBitsTree := Build_RegPath waitBitsTree tt I.

  Definition readWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal))
    : Action ty waitBitsTree Bool :=
    ReadReg "waitBits" pWaitBits (fun arr =>
    Return (ReadArray #arr idx)).

  Definition writeWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    ReadReg "waitBits" pWaitBits (fun arr =>
    WriteReg pWaitBits (UpdateArray #arr idx val) Retv).

  Definition clearWaitBits2 (ty : Kind -> Type)
    (idx1 : Expr ty (Bit RegIdxSzReal)) (en1 : Expr ty Bool)
    (idx2 : Expr ty (Bit RegIdxSzReal)) (en2 : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    ReadReg "waitBits" pWaitBits (fun arr0 =>
    Let arr1 : WaitBitsKind <- ITE en1 (UpdateArray #arr0 idx1 (ConstBool false)) #arr0 ;
    Let arr2 : WaitBitsKind <- ITE en2 (UpdateArray #arr1 idx2 (ConstBool false)) #arr1 ;
    WriteReg pWaitBits #arr2 Retv).

  Definition fetchTree (capacity : nat) : Tree DomainElem :=
    Node "fetch" [
      Node "fetchBuf"    [ fifoTree dom capacity FullECapWithTag ] ;
      Node "fetchOutBuf" [ fifoTree dom capacity FetchOut ]
    ].

  Definition deferredTree (capacity : nat) : Tree DomainElem :=
    Node "deferred" [
      Node "inputBuf" [ fifoTree dom capacity DeferredReq ] ;
      Node "loadBuf"  [ fifoTree dom capacity PendingLoad ] ;
      Node "revRqBuf" [ fifoTree dom capacity RevCmd ] ;
      Node "revBuf"   [ fifoTree dom capacity PendingRev ] ;
      modeMulDivTree dom ImplInputWidth ImplMulStages ImplDivStages ImplMulDivMode
    ].

  Definition coreTree (memTree : Tree DomainElem) (fetchCapacity deferredCapacity : nat) : Tree DomainElem :=
    Node "core" [
      rfTree dom pcAddrInit ;
      waitBitsTree ;
      Node "mem" [ memTree ] ;
      fetchTree fetchCapacity ;
      Node "decodeToAluBuf" [ fifoTree dom fetchCapacity AluInInstGroup ] ;
      Node "aluToExecBuf"   [ fifoTree dom fetchCapacity AluOutUnion ] ;
      deferredTree deferredCapacity
    ].

End ImplDefines.
