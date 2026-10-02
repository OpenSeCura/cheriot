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

Definition DecodeToAluEntry := AluInInstGroup.

(* ===========================================================================
 * Hardware Pipeline State Trees & Register Accessors
 * =========================================================================== *)

Section ImplCommon.
  Variable dom : string.
  Variable pcAddrInit : Z.

  (* 1. Scoreboard (waitBits) *)
  Definition waitBitLeaves : list (Tree DomainElem) :=
    map (fun '(_, idx) =>
      Leaf ("waitBit_" ++ hex_string_of_Z idx)%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (enumerate (repeat tt (Z.to_nat NumRegs))).

  Definition waitBitsTree : Tree DomainElem :=
    Node "waitBits" waitBitLeaves.

  Definition waitBitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (getTreeRegsOfKind Bool waitBitsTree).

  Definition readWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal))
    : Action ty waitBitsTree Bool :=
    readRegsList waitBitPathsWithKind idx.

  Definition writeWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList waitBitPathsWithKind idx val.

  (* 2. Decode Subtree & Core Tree *)
  Definition decodeTree : Tree DomainElem :=
    Node "decode" [
      Leaf "decodePc"        (dom, EReg (Build_Reg (Option Addr) (Some (getDefault (Option Addr))) false)) ;
      Node "decodeToAluBuf" [ fifoTree dom 1 DecodeToAluEntry ]
    ].

  Definition pDecodePc : RegPath decodeTree :=
    Eval cbn in (getChildRegPathTree decodeTree "decodePc").

  Definition readDecodePc (ty : Kind -> Type) : Action ty decodeTree (Option Addr) :=
    ReadReg "decodePc" pDecodePc (fun v => Return #v).

  Definition writeDecodePc (ty : Kind -> Type) (val : Expr ty (Option Addr)) : Action ty decodeTree (Bit 0) :=
    WriteReg pDecodePc val Retv.

  Definition coreTree (bpTree memTree fetchTree deferredTree : Tree DomainElem) : Tree DomainElem :=
    Node "core" [
      rfTree dom pcAddrInit ;
      waitBitsTree ;
      Node "bp"       [ bpTree ] ;
      Leaf "currEpoch" (dom, EReg (Build_Reg Epoch (Some Zmod.zero) false)) ;
      Node "mem"      [ memTree ] ;
      Node "fetch"    [ fetchTree ] ;
      decodeTree ;
      Node "deferred" [ deferredTree ]
    ].

  Definition pCurrEpoch (bpTree memTree fetchTree deferredTree : Tree DomainElem)
    : RegPath (coreTree bpTree memTree fetchTree deferredTree) :=
    Eval cbn in (getChildRegPathTree (coreTree bpTree memTree fetchTree deferredTree) "currEpoch").

  Definition readCurrEpoch (bpTree memTree fetchTree deferredTree : Tree DomainElem) (ty : Kind -> Type)
    : Action ty (coreTree bpTree memTree fetchTree deferredTree) Epoch :=
    ReadReg "currEpoch" (pCurrEpoch bpTree memTree fetchTree deferredTree) (fun v => Return #v).

  Definition writeCurrEpoch (bpTree memTree fetchTree deferredTree : Tree DomainElem) (ty : Kind -> Type)
    (val : Expr ty Epoch) : Action ty (coreTree bpTree memTree fetchTree deferredTree) (Bit 0) :=
    WriteReg (pCurrEpoch bpTree memTree fetchTree deferredTree) val Retv.

End ImplCommon.
