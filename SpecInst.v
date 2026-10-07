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
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic Spec.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Physical Memory Map & Device Addresses
 * =========================================================================== *)

Definition PcAddrInit     : Z := 0x80000000.
Definition RamBase        : Z := 0x80000000.
Definition RamSize        : Z := 256 * 1024. (* 256 KB *)
Definition RamLineConfig  : LineConfig := @TaggedLine (Z.to_nat LgNumBytesFullCapSz) I.

Definition RevTableBase       : Z := 0x83000000.
Definition RevTableSize       : Z := 4 * 1024. (* 4 KB bitmap *)
Definition RevTableLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

Definition ClintBaseAddr   : Z := 0x02000000.
Definition RevokerBaseAddr : Z := 0x03000000.
Definition PlicBaseAddr    : Z := 0x04000000.

Definition ExtMemBase        : Z := 0x10000000.
Definition ExtMemSize        : Z := 0x70000000.
Definition LgExtMemLineBytes : Z := 4.
Definition ExtMemLineConfig  : LineConfig := @TaggedLine (Z.to_nat LgExtMemLineBytes) I.

(* ===========================================================================
 * Revoker Configuration
 * =========================================================================== *)

Definition concreteRevConfig : RevConfig := {|
  heapStartAddr       := RamBase ;
  revTableStartAddr   := RevTableBase ;
  revTableSizeInBytes := RevTableSize ;
  lgRevGranularity    := LgNumBytesFullCapSz
|}.

(* ===========================================================================
 * Concrete Memory Regions
 * =========================================================================== *)

Definition ramRegion : MemRegion := {|
  regionName        := "ram" ;
  regionDom         := "core" ;
  regionBase        := RamBase ;
  regionSize        := RamSize ;
  regionLineCfg     := RamLineConfig ;
  isReadOnly        := false ;
  hasExtraFetchPort := true ;
  regionKind        := ExternalMem ;
  regionInMemory    := I ;
  regionBaseAligned := I ;
  regionSizeAligned := I
|}.

Definition revTableRegion : MemRegion := {|
  regionName        := "revTable" ;
  regionDom         := "core" ;
  regionBase        := RevTableBase ;
  regionSize        := RevTableSize ;
  regionLineCfg     := RevTableLineConfig ;
  isReadOnly        := false ;
  hasExtraFetchPort := false ;
  regionKind        := InternalMem false None (defaultTagsInit RevTableLineConfig RevTableSize) ;
  regionInMemory    := I ;
  regionBaseAligned := I ;
  regionSizeAligned := I
|}.

Definition extMemRegion : MemRegion := {|
  regionName        := "extMem" ;
  regionDom         := "core" ;
  regionBase        := ExtMemBase ;
  regionSize        := ExtMemSize ;
  regionLineCfg     := ExtMemLineConfig ;
  isReadOnly        := false ;
  hasExtraFetchPort := false ;
  regionKind        := ExternalMem ;
  regionInMemory    := I ;
  regionBaseAligned := I ;
  regionSizeAligned := I
|}.

Definition concreteRegions : list MemRegion := [
  ramRegion ;
  revTableRegion ;
  @clintMemRegion "core" ClintBaseAddr I I ;
  @revokerMemRegion "core" [] RevokerBaseAddr I I ;
  @plicMemRegion "core" 3 PlicBaseAddr I I ;
  extMemRegion
].

Definition concreteRegionsDisjoint : Is_true (pairwiseDisjoint concreteRegions) := I.

Definition concreteClint : @ClintInstance "core" concreteRegions :=
  @Build_ClintInstance "core" concreteRegions 2%nat ClintBaseAddr I I eq_refl.

Definition concreteRevoker : @RevokerInstance "core" [] concreteRegions :=
  @Build_RevokerInstance "core" [] concreteRegions 3%nat RevokerBaseAddr I I eq_refl.

Definition concretePlic : @PlicInstance "core" 3%nat concreteRegions :=
  @Build_PlicInstance "core" 3%nat concreteRegions 4%nat PlicBaseAddr I I I eq_refl.

(* ===========================================================================
 * Fully Instantiated System Tree and Specification Mod
 * =========================================================================== *)

Definition specSysTreeInst : Tree DomainElem :=
  specSysTree "core" PcAddrInit concreteRegions.

Definition specModInst : Mod specSysTreeInst :=
  @spec "core"
        PcAddrInit
        concreteRevConfig
        concreteRegions
        concreteClint
        concreteRevoker
        concretePlic.
