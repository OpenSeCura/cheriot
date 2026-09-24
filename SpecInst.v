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
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic Spec Binary.

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

Definition fixedBinary : list (bits 8) := map (fun v => bits.of_Z 8 v) binary.

Definition ramInitData
  : option (option (type (Array (Z.to_nat RamSize) (Bit 8)))) :=
  bytesToMemInit RamSize fixedBinary.

Definition ramRegion : MemRegion := {|
  regionName        := "ram" ;
  regionDom         := "core" ;
  regionBase        := RamBase ;
  regionSize        := RamSize ;
  regionLineCfg     := RamLineConfig ;
  isReadOnly        := false ;
  regionKind        := InternalMem true ramInitData (defaultTagsInit RamSize RamLineConfig) ;
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
  regionKind        := InternalMem false None (defaultTagsInit RevTableSize RevTableLineConfig) ;
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
  regionKind        := ExternalMem ;
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
  extMemRegion
].

Definition concreteRegionsDisjoint : Is_true (pairwiseDisjoint concreteRegions) := I.

Definition concreteClint : @ClintInstance "core" concreteRegions :=
  @Build_ClintInstance "core" concreteRegions 2%nat ClintBaseAddr I I eq_refl.

Definition concreteRevoker : @RevokerInstance "core" concreteRegions :=
  @Build_RevokerInstance "core" concreteRegions 3%nat RevokerBaseAddr I I eq_refl.

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
        tohostAddr
        concreteRevConfig
        concreteRegions
        concreteClint
        concreteRevoker
        concretePlic.

From Guru Require Import Extraction Simulator.
Set Extraction Output Directory ".".

Extract Constant IoEnv => "(Data.IORef.IORef Prelude.Integer, Data.IORef.IORef Prelude.Bool, Data.IORef.IORef Prelude.Integer, Data.IORef.IORef (Prelude.Maybe Prelude.Integer))".

Extract Constant io_initEnv => "(do
  r1 <- Data.IORef.newIORef 0
  r2 <- Data.IORef.newIORef Prelude.False
  r3 <- Data.IORef.newIORef 0
  r4 <- Data.IORef.newIORef Prelude.Nothing
  Prelude.return (r1, r2, r3, r4))".

Extract Constant io_send => "(\(readAddrRef, dlabRef, ieRef, _) name k val ->
  if name Prelude.== ""lineReadRq""
  then Data.IORef.writeIORef readAddrRef (unsafeCoerce val :: Prelude.Integer)
  else if name Prelude.== ""lineWriteRq""
  then let (addr, (dataVec, (maskVec, _))) =
             unsafeCoerce val :: (Prelude.Integer, (Data.Vector.Vector Prelude.Integer, (Data.Vector.Vector Prelude.Bool, ())))
           b0  = dataVec Data.Vector.! 0
           m0  = maskVec Data.Vector.! 0
           b4  = dataVec Data.Vector.! 4
           m4  = maskVec Data.Vector.! 4
           b12 = dataVec Data.Vector.! 12
           m12 = maskVec Data.Vector.! 12
       in if addr Prelude.== 0x10000000 then do
            if m12
              then Data.IORef.writeIORef dlabRef (Data.Bits.testBit b12 7)
              else Prelude.return ()
            dlab <- Data.IORef.readIORef dlabRef
            if m0 Prelude.&& Prelude.not dlab
              then Prelude.putChar (Data.Char.chr (Prelude.fromIntegral (b0 Data.Bits..&. 0xff))) Prelude.>>
                   System.IO.hFlush System.IO.stdout
              else Prelude.return ()
            if m4 Prelude.&& Prelude.not dlab
              then Data.IORef.writeIORef ieRef (b4 Data.Bits..&. 0xff)
              else Prelude.return ()
          else Prelude.return ()
  else Prelude.return ())".

Extract Constant io_recv => "(\(readAddrRef, _, ieRef, rxBufRef) name k ->
  let pollRx = do
        cur <- Data.IORef.readIORef rxBufRef
        case cur of
          Prelude.Just _ -> Prelude.return Prelude.True
          Prelude.Nothing -> do
            rdy <- System.IO.hReady System.IO.stdin
            if rdy then do
              c <- System.IO.getChar
              Data.IORef.writeIORef rxBufRef (Prelude.Just (Prelude.toInteger (Data.Char.ord c Data.Bits..&. 0xff)))
              Prelude.return Prelude.True
            else Prelude.return Prelude.False
  in if name Prelude.== ""lineReadRqReady"" Prelude.|| name Prelude.== ""lineWriteRqReady"" then
       Prelude.return (unsafeCoerce Prelude.True)
     else if name Prelude.== ""lineReadRp"" then do
       addr <- Data.IORef.readIORef readAddrRef
       bytes <- if addr Prelude.== 0x10000000 then do
                  _ <- pollRx
                  cur <- Data.IORef.readIORef rxBufRef
                  b0 <- case cur of
                    Prelude.Just b -> Data.IORef.writeIORef rxBufRef Prelude.Nothing Prelude.>> Prelude.return b
                    Prelude.Nothing -> Prelude.return 0
                  Prelude.return (Data.Vector.fromList [b0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
                else if addr Prelude.== 0x10000010 then do
                  hasRx <- pollRx
                  let b4 = if hasRx then 0x21 else 0x20
                  Prelude.return (Data.Vector.fromList [0, 0, 0, 0, b4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
                else Prelude.return (Data.Vector.replicate 16 0)
       let tags = Data.Vector.replicate 2 Prelude.False
       Prelude.return (unsafeCoerce (Prelude.True, ((bytes, (tags, ())), ())))
     else if name Prelude.== ""UartIrq"" then do
       ie <- Data.IORef.readIORef ieRef
       if Data.Bits.testBit ie 0 then do
         hasRx <- pollRx
         Prelude.return (unsafeCoerce (hasRx Prelude.|| Data.Bits.testBit ie 1))
       else
         Prelude.return (unsafeCoerce (Data.Bits.testBit ie 1))
     else Prelude.return (unsafeCoerce (getDefault k)))".

Extract Constant io_stepCycle => "(\c ->
  if Prelude.rem (c :: Prelude.Integer) 250000 Prelude.== 0
  then Prelude.putStrLn (""[Cycle "" Prelude.++ Prelude.show (c :: Prelude.Integer) Prelude.++ ""]"") Prelude.>>
       System.IO.hFlush System.IO.stdout
  else Prelude.return ())".

Definition main : IO unit := evalModCyclesIO specSysTreeInst (Z.to_nat 50000000) specModInst.
Extraction "Simulate" main.
