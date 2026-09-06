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

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic Uart Spec.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. Physical Memory Map & Device Addresses
 * =========================================================================== *)

Definition RamBase        : Z := 0x80000000.
Definition RamSize        : nat := Z.to_nat (256 * 1024). (* 256 KB *)
Definition RamLineConfig  : LineConfig := @TaggedLine (Z.to_nat LgNumBytesFullCapSz) I.

Definition RevTableBase       : Z := 0x00001000.
Definition RevTableSize       : nat := Z.to_nat (4 * 1024). (* 4 KB bitmap *)
Definition RevTableLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

Definition ClintBaseAddr   : Z := 0x02000000.
Definition RevokerBaseAddr : Z := 0x03000000.
Definition PlicBaseAddr    : Z := 0x04000000.
Definition UartBaseAddr    : Z := 0x05000000.

(* ===========================================================================
 * 2. Revoker Configuration
 * =========================================================================== *)

Definition concreteRevConfig : RevConfig := {|
  heapStartAddr       := RamBase ;
  revTableStartAddr   := RevTableBase ;
  revTableSizeInBytes := RevTableSize ;
  lgRevGranularity    := LgNumBytesFullCapSz
|}.

(* ===========================================================================
 * 3. Concrete Memory Regions
 * =========================================================================== *)

Definition ramRegion : MemRegion := {|
  regionName        := "ram" ;
  regionBase        := RamBase ;
  regionSize        := RamSize ;
  regionLineCfg     := RamLineConfig ;
  isReadOnly        := false ;
  regionKind        := InternalMem None (defaultTagsInit RamSize RamLineConfig) ;
  regionInMemory    := I ;
  regionBaseAligned := I ;
  regionSizeAligned := I
|}.

Definition revTableRegion : MemRegion := {|
  regionName        := "revTable" ;
  regionBase        := RevTableBase ;
  regionSize        := RevTableSize ;
  regionLineCfg     := RevTableLineConfig ;
  isReadOnly        := false ;
  regionKind        := InternalMem None (defaultTagsInit RevTableSize RevTableLineConfig) ;
  regionInMemory    := I ;
  regionBaseAligned := I ;
  regionSizeAligned := I
|}.

Definition concreteRegions : list MemRegion := [
  ramRegion ;
  revTableRegion ;
  clintMemRegion ClintBaseAddr I I ;
  revokerMemRegion RevokerBaseAddr I I ;
  plicMemRegion 2 PlicBaseAddr I I ;
  uartMemRegion UartBaseAddr I I
].

(* TODO: 
 * fix Uart
 * fix comments all over
 *)

Lemma concreteRegionsDisjoint : Is_true (pairwiseDisjoint concreteRegions).
Proof.
  exact I.
Qed.

(* ===========================================================================
 * 4. Peripheral Instances (Proofs of Membership by Index)
 * =========================================================================== *)

Definition concreteClint : ClintInstance concreteRegions :=
  @Build_ClintInstance concreteRegions 2%nat ClintBaseAddr I I eq_refl.

Definition concreteRevoker : RevokerInstance concreteRegions :=
  @Build_RevokerInstance concreteRegions 3%nat RevokerBaseAddr I I eq_refl.

Definition concretePlic : PlicInstance 2%nat concreteRegions :=
  @Build_PlicInstance 2%nat concreteRegions 4%nat PlicBaseAddr I I I eq_refl.

Definition concreteUart : UartInstance concreteRegions :=
  @Build_UartInstance concreteRegions 5%nat UartBaseAddr I I eq_refl.

(* ===========================================================================
 * 5. Fully Instantiated System Tree and Specification Mod
 * =========================================================================== *)

Definition specSysTreeInst : Tree Elem :=
  specSysTree concreteRegions.

Definition specModInst : Mod specSysTreeInst :=
  @spec concreteRevConfig
        concreteRegions
        concreteClint
        concreteRevoker
        concreteUart
        concretePlic.
