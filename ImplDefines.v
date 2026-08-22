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
From Cheriot Require Import SpecDefines Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Hardware Pipeline / Queue Tree Definitions
 * =========================================================================== *)

Definition fetchTree (capacity : nat) : Tree Elem :=
  Node "fetch" [
    Node "fetchBuf" [ fifoTree capacity FullECapWithTag ]
  ].

Definition deferredTree (capacity : nat) : Tree Elem :=
  Node "deferred" [
    Node "inputBuf" [ fifoTree capacity DeferredReq ] ;
    Node "loadBuf"  [ fifoTree capacity PendingLoad ] ;
    Node "revBuf"   [ fifoTree capacity PendingRev ]
  ].

Definition coreTree (memTree : Tree Elem) (fetchCapacity deferredCapacity : nat) : Tree Elem :=
  Node "core" [
    rfTree ;
    Node "mem" [ memTree ] ;
    fetchTree fetchCapacity ;
    deferredTree deferredCapacity
  ].
