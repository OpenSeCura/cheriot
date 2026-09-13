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
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic SifiveUartController Spec Binary.

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

Definition RamBase        : Z := MemStartAddr.
Definition RamSize        : Z := 256 * 1024. (* 256 KB *)
Definition RamLineConfig  : LineConfig := @TaggedLine (Z.to_nat LgNumBytesFullCapSz) I.

Definition RevTableBase       : Z := 0x00001000.
Definition RevTableSize       : Z := 4 * 1024. (* 4 KB bitmap *)
Definition RevTableLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

Definition ClintBaseAddr   : Z := 0x02000000.
Definition RevokerBaseAddr : Z := 0x03000000.
Definition PlicBaseAddr    : Z := 0x04000000.
Definition UartBaseAddr    : Z := 0x05000000.

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

Definition fixedBinary : list (bits 8) := map (fun v => bits.of_Z 8 v) binary.

Definition binary_le_RamSize : Is_true (List.length binary <=? Z.to_nat RamSize)%nat := I.

Definition paddedBinary : list (bits 8) :=
  (fixedBinary ++ List.repeat (bits.of_Z 8 0) (Z.to_nat RamSize - List.length binary))%list.

Lemma paddedBinary_length :
  List.length paddedBinary = Z.to_nat RamSize.
Proof.
  unfold paddedBinary, fixedBinary.
  rewrite length_app.
  rewrite repeat_length.
  rewrite length_map.
  pose proof binary_le_RamSize as H.
  apply Is_true_eq_true in H.
  rewrite Nat.leb_le in H.
  lia.
Qed.

Definition ramInitData : option (option (type (Array (Z.to_nat RamSize) (Bit 8)))) :=
  Some (Some (Build_SameTuple (tupleElems := paddedBinary)
                              (Is_true_Nat_eq_implies paddedBinary_length))).

Definition ramRegion : MemRegion := {|
  regionName        := "ram" ;
  regionDom         := "core" ;
  regionBase        := RamBase ;
  regionSize        := RamSize ;
  regionLineCfg     := RamLineConfig ;
  isReadOnly        := false ;
  regionKind        := InternalMem ramInitData (defaultTagsInit RamSize RamLineConfig) ;
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
  regionKind        := InternalMem None (defaultTagsInit RevTableSize RevTableLineConfig) ;
  regionInMemory    := I ;
  regionBaseAligned := I ;
  regionSizeAligned := I
|}.

Definition concreteRegions : list MemRegion := [
  ramRegion ;
  revTableRegion ;
  @clintMemRegion "core" ClintBaseAddr I I ;
  @revokerMemRegion "core" RevokerBaseAddr I I ;
  @plicMemRegion "core" 3 PlicBaseAddr I I ;
  @sifiveUartMemRegion "peripheral" UartBaseAddr I I
].

Definition concreteRegionsDisjoint : Is_true (pairwiseDisjoint concreteRegions) := I.

Definition concreteClint : @ClintInstance "core" concreteRegions :=
  @Build_ClintInstance "core" concreteRegions 2%nat ClintBaseAddr I I eq_refl.

Definition concreteRevoker : @RevokerInstance "core" concreteRegions :=
  @Build_RevokerInstance "core" concreteRegions 3%nat RevokerBaseAddr I I eq_refl.

Definition concretePlic : @PlicInstance "core" 3%nat concreteRegions :=
  @Build_PlicInstance "core" 3%nat concreteRegions 4%nat PlicBaseAddr I I I eq_refl.

Definition concreteUart : @SifiveUartInstance "peripheral" concreteRegions :=
  @Build_SifiveUartInstance "peripheral" concreteRegions 5%nat UartBaseAddr I I eq_refl.

(* ===========================================================================
 * Fully Instantiated System Tree and Specification Mod
 * =========================================================================== *)

Definition specSysTreeInst : Tree DomainElem :=
  specSysTree "core" PcAddrInit concreteRegions.

Definition specModInst : Mod specSysTreeInst :=
  @spec "core"
        "peripheral"
        PcAddrInit
        concreteRevConfig
        concreteRegions
        concreteClint
        concreteRevoker
        concreteUart
        concretePlic.

From Guru Require Import Extraction Simulator.
Set Extraction Output Directory ".".

Extract Constant io_send => "(\name k val ->
  if (Prelude.||) (name Prelude.== ""txData"") (Data.List.isSuffixOf "".txData"" name)
  then let byte = Prelude.fromIntegral (unsafeCoerce val :: Prelude.Integer)
       in Prelude.putChar (Data.Char.chr byte)
  else Prelude.return ())".

Extract Constant io_recv => "(\name k ->
  if (Prelude.||) (name Prelude.== ""txRdy"") (Data.List.isSuffixOf "".txRdy"" name)
  then Prelude.return (unsafeCoerce Prelude.True)
  else Prelude.return (unsafeCoerce (getDefault k)))".

Extract Constant io_stepCycle => "(\c ->
  Prelude.putStrLn (""[Cycle "" Prelude.++ Prelude.show (c :: Prelude.Integer) Prelude.++ ""]"") Prelude.>>
  System.IO.hFlush System.IO.stdout)".

Definition main : IO unit := evalModCyclesIO specSysTreeInst (Z.to_nat 100) specModInst.
Extraction "Simulate" main.
