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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Extraction Simulator.
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic SpecInst ImplRevoker ImplDevice ImplCommon ImplBranchPredictor ImplFetch ImplDecode ImplExecute ImplDeferred Impl Binary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Fully Instantiated System Tree and Implementation Mod
 * =========================================================================== *)

Definition DefaultFetchCapacity    : nat := 1%nat.
Definition DefaultDecodeCapacity   : nat := 1%nat.
Definition DefaultDeferredCapacity : nat := 1%nat.

Definition implConcreteRegions : list MemRegion := [
  ramRegion ;
  revTableRegion ;
  @clintMemRegion "core" ClintBaseAddr I I ;
  @revokerMemRegion "core" (implRevokerExtraChildren "core") RevokerBaseAddr I I ;
  @plicMemRegion "core" 3 PlicBaseAddr I I ;
  extMemRegion
].

Definition implConcreteClint : @ClintInstance "core" implConcreteRegions :=
  @Build_ClintInstance "core" implConcreteRegions 2%nat ClintBaseAddr I I eq_refl.

Definition implConcreteRevoker : @RevokerInstance "core" (implRevokerExtraChildren "core") implConcreteRegions :=
  @Build_RevokerInstance "core" (implRevokerExtraChildren "core") implConcreteRegions 3%nat RevokerBaseAddr I I eq_refl.

Definition implConcretePlic : @PlicInstance "core" 3%nat implConcreteRegions :=
  @Build_PlicInstance "core" 3%nat implConcreteRegions 4%nat PlicBaseAddr I I I eq_refl.

Definition implSysTreeInst : Tree DomainElem :=
  implSysTree "core" PcAddrInit DefaultFetchCapacity DefaultDecodeCapacity DefaultDeferredCapacity concreteRevConfig implConcreteRegions.

Definition implModInst : Mod implSysTreeInst :=
  @impl "core"
        PcAddrInit
        tohostAddr
        DefaultFetchCapacity
        DefaultDecodeCapacity
        DefaultDeferredCapacity
        concreteRevConfig
        implConcreteRegions
        implConcreteClint
        implConcreteRevoker
        implConcretePlic.

Set Extraction Output Directory "./Impl".

Definition main : IO unit := evalModCyclesIO implSysTreeInst (Z.to_nat 50000000) implModInst.
Extraction "Simulate" main.
