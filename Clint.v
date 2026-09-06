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
From Guru Require Import Syntax Notations Semantics Library Composition SimulatorOnly.
From Cheriot Require Import SpecDefines SpecDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Notation ByteSz := 8%Z.

(* ===========================================================================
 * 1. CLINT Register Offsets & Tree Structure
 * =========================================================================== *)

Definition ClintSizeBytes : Z := 8.

Definition CLINT_MTIME_OFFSET  : Z := 0x00.
Definition CLINT_MTIMEH_OFFSET : Z := 0x04.

Definition clintChildren : list (Tree Elem) :=
  [ Leaf "mtime"  (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Leaf "mtimeh" (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ].

Local Notation tClint := (Node "clint" clintChildren).

Definition clintMtimePath  : RegPath tClint := getChildRegPathTree tClint "mtime".
Definition clintMtimehPath : RegPath tClint := getChildRegPathTree tClint "mtimeh".

Definition ClintLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

(* ===========================================================================
 * 2. CLINT Atomic Actions
 * =========================================================================== *)

Section ClintActions.
  Variable ty : Kind -> Type.

  Definition readClintMtime : Action ty tClint (Bit DXlen) :=
    LetA lo : Bit Xlen <- ReadReg "mtime" clintMtimePath (fun v => Return #v) ;
    LetA hi : Bit Xlen <- ReadReg "mtimeh" clintMtimehPath (fun v => Return #v) ;
    Return {< #hi, #lo >}.

  Definition clintTick : Action ty tClint (Bit 0) :=
    LetA mtimeDXlen : Bit DXlen <- readClintMtime ;
    Let  nextMtime  : Bit DXlen <- Add [ #mtimeDXlen ; $1 ] ;
    Act (WriteReg clintMtimePath (TruncLsb Xlen Xlen #nextMtime) Retv) ;
    Act (WriteReg clintMtimehPath (TruncMsb Xlen Xlen #nextMtime) Retv) ;
    Retv.

End ClintActions.

Definition ClintRegNames : list string :=
  [ "mtime" ; "mtimeh" ].

Definition clintRegIdx (name : string) :=
  forceOption (getStrIndexOption name ClintRegNames).

Definition ClintRegIdxWidth : Z := Eval compute in (Z.log2_up ClintSizeBytes - LgNumBytesXlen).

Notation clintRegIdxBit name :=
  ($(Z.of_nat (clintRegIdx name))).

Definition clintLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty tClint (LineReadRp ClintLineConfig) :=
  Let offset <- getMemOffset base ClintSizeBytes addr ;
  Let regIdx : Bit ClintRegIdxWidth <- TruncMsb ClintRegIdxWidth LgNumBytesXlen #offset ;
  ReadReg "mtime" clintMtimePath (fun mtimeVal =>
  ReadReg "mtimeh" clintMtimehPath (fun mtimehVal =>
  Let readWord : Bit Xlen <-
    Or [ ITE0 (Eq #regIdx (clintRegIdxBit "mtime")) #mtimeVal ;
         ITE0 (Eq #regIdx (clintRegIdxBit "mtimeh")) #mtimehVal ] ;
  Let readBytes : Array (cfgLineBytes ClintLineConfig) (Bit ByteSz) <-
    FromBit (Array (cfgLineBytes ClintLineConfig) (Bit ByteSz)) #readWord ;
  @Return ty tClint (LineReadRp ClintLineConfig) (STRUCT {
    "data" ::= #readBytes ;
    "tag"  ::= Const ty (Array (cfgNumLineTags ClintLineConfig) Bool) (getDefault _)
  }))).

Definition clintLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq ClintLineConfig))
           : Action ty tClint (Bit 0) :=
  Let offset <- getMemOffset base ClintSizeBytes (rq`"addr") ;
  Let regIdx : Bit ClintRegIdxWidth <- TruncMsb ClintRegIdxWidth LgNumBytesXlen #offset ;
  Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
  If (Eq #regIdx (clintRegIdxBit "mtime")) Then (
    WriteReg clintMtimePath #writeWord Retv
  ) ;
  If (Eq #regIdx (clintRegIdxBit "mtimeh")) Then (
    WriteReg clintMtimehPath #writeWord Retv
  ) ;
  Retv.

Arguments clintLineReadAction base ty addr : clear implicits.
Arguments clintLineWriteAction base ty rq : clear implicits.

(* ===========================================================================
 * 3. MemRegion Constructor
 * =========================================================================== *)

Definition clintMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + ClintSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes ClintLineConfig)) =? 0)%Z)
           : MemRegion := {|
  regionName        := "clint" ;
  regionBase        := base ;
  regionSize        := Z.to_nat ClintSizeBytes ;
  regionLineCfg     := ClintLineConfig ;
  isReadOnly        := false ;
  regionKind        := @CustomMem "clint" (Z.to_nat ClintSizeBytes) ClintLineConfig clintChildren (clintLineReadAction base) (clintLineWriteAction base) None ;
  regionInMemory    := pfBound ;
  regionBaseAligned := pfAligned ;
  regionSizeAligned := I
|}.

Arguments clintMemRegion base pfBound pfAligned : clear implicits.

(* ===========================================================================
 * 4. System Integration Helpers
 * =========================================================================== *)

Record ClintInstance (regions : list MemRegion) := {
  clintIdx      : nat ;
  clintBaseAddr : Z ;
  pfBound       : Is_true ((0 <=? clintBaseAddr) && (clintBaseAddr + ClintSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  pfAligned     : Is_true (clintBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes ClintLineConfig)) =? 0)%Z ;
  pfClint       : nth_error regions clintIdx = Some (clintMemRegion clintBaseAddr pfBound pfAligned)
}.

Definition clintRegion {regions} (clint : ClintInstance regions) : MemRegion :=
  clintMemRegion clint.(clintBaseAddr) clint.(pfBound) clint.(pfAligned).

Section ClintSystem.
  Variable regions : list MemRegion.
  Variable clint : ClintInstance regions.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Definition clintAction {k : Kind} (act : Action ty tClint k) : Action ty memTree k :=
    nthRegionAction clint.(clintIdx) regions (clintRegion clint) clint.(pfClint) act.

  Definition clintTickAction : Action ty memTree (Bit 0) :=
    clintAction (clintTick ty).

  Definition readClintMtimeAction : Action ty memTree (Bit DXlen) :=
    clintAction (readClintMtime ty).

End ClintSystem.
