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

From Stdlib Require Import String List ZArith Zmod Bool Psatz Nat Arith.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic SpecInst ImplRevoker ImplDevice ImplMulDiv ImplCommon ImplBranchPredictor ImplFetch ImplDecode ImplExecute ImplDataMem Impl ImplInst.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Fully Instantiated Forward-Datapath Implementation Mod (simulation only)
 * =========================================================================== *)

Definition forwardDatapathModInst : Mod implSysTreeInst :=
  @forwardDatapathMod
                      PcAddrInit
                      DefaultFetchCapacity
                      DefaultInstCapacity
                      DefaultDecodeCapacity
                      DefaultDataMemCapacity
                      DefaultMulCapacity
                      DefaultDivCapacity
                      ImplMulStages
                      ImplDivStages
                      ImplMulDivMode
                      (implWithInstIfc implNoInstIfc)
                      concreteRevConfig
                      implConcreteRegions
                      implConcreteClint
                      implConcreteRevoker
                      implConcretePlic.

From Guru Require Import Extraction Compiler.
Set Extraction Output Directory "./Impl/Fwd".

Definition compiledMod := compile forwardDatapathModInst.
Extraction "Compile" kindSize Z.log2_up getDefault isEq compiledMod.
