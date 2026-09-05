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
From Cheriot Require Import SpecDefines SpecDevice SpecRevoker.

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

Definition ClintSizeBytes : Z := 256.

Definition CLINT_MTIMECMP_OFFSET  : Z := 0x00.
Definition CLINT_MTIMECMPH_OFFSET : Z := 0x04.
Definition CLINT_MTIME_OFFSET     : Z := 0x08.
Definition CLINT_MTIMEH_OFFSET    : Z := 0x0C.

Definition clintChildren : list (Tree Elem) :=
  [ Leaf "mtimecmp"         (EReg (Build_Reg (Bit Xlen) (Some (bits.of_Z Xlen (-1))))) ;
    Leaf "mtimecmph"        (EReg (Build_Reg (Bit Xlen) (Some (bits.of_Z Xlen (-1))))) ;
    Leaf "mtime"            (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Leaf "mtimeh"           (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Leaf "interruptPending" (EReg (Build_Reg Bool (Some false))) ].

Local Notation tClint := (Node "clint" clintChildren).

Definition clintMtimecmpPath         : RegPath tClint := getChildRegPathTree tClint "mtimecmp".
Definition clintMtimecmphPath        : RegPath tClint := getChildRegPathTree tClint "mtimecmph".
Definition clintMtimePath            : RegPath tClint := getChildRegPathTree tClint "mtime".
Definition clintMtimehPath           : RegPath tClint := getChildRegPathTree tClint "mtimeh".
Definition clintInterruptPendingPath : RegPath tClint := getChildRegPathTree tClint "interruptPending".

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

  Definition readClintMtimecmp : Action ty tClint (Bit DXlen) :=
    LetA lo : Bit Xlen <- ReadReg "mtimecmp" clintMtimecmpPath (fun v => Return #v) ;
    LetA hi : Bit Xlen <- ReadReg "mtimecmph" clintMtimecmphPath (fun v => Return #v) ;
    Return {< #hi, #lo >}.

  Definition clintTick : Action ty tClint (Bit 0) :=
    LetA mtime64    : Bit DXlen <- readClintMtime ;
    LetA mtimecmp64 : Bit DXlen <- readClintMtimecmp ;
    Let  nextMtime  : Bit DXlen <- Add [ #mtime64 ; $1 ] ;
    Act (WriteReg clintMtimePath (TruncLsb Xlen Xlen #nextMtime) Retv) ;
    Act (WriteReg clintMtimehPath (TruncMsb Xlen Xlen #nextMtime) Retv) ;
    If (Sge #nextMtime #mtimecmp64) Then (
      WriteReg clintInterruptPendingPath (Const ty Bool true) Retv
    ) ;
    Retv.

  Definition clintMtip : Action ty tClint Bool :=
    LetA pending    : Bool      <- ReadReg "interruptPending" clintInterruptPendingPath (fun v => Return #v) ;
    LetA mtime64    : Bit DXlen <- readClintMtime ;
    LetA mtimecmp64 : Bit DXlen <- readClintMtimecmp ;
    Return (Or [ #pending ; Sge #mtime64 #mtimecmp64 ]).

End ClintActions.

Definition ClintRegNames : list string :=
  [ "mtimecmp" ; "mtimecmph" ; "mtime" ; "mtimeh" ].

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
  ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
  ReadReg "mtimecmph" clintMtimecmphPath (fun mtimecmphVal =>
  ReadReg "mtime" clintMtimePath (fun mtimeVal =>
  ReadReg "mtimeh" clintMtimehPath (fun mtimehVal =>
  Let readWord : Bit Xlen <-
    Or [ ITE0 (Eq #regIdx (clintRegIdxBit "mtimecmp")) #mtimecmpVal ;
         ITE0 (Eq #regIdx (clintRegIdxBit "mtimecmph")) #mtimecmphVal ;
         ITE0 (Eq #regIdx (clintRegIdxBit "mtime")) #mtimeVal ;
         ITE0 (Eq #regIdx (clintRegIdxBit "mtimeh")) #mtimehVal ] ;
  Let readBytes : Array (cfgLineBytes ClintLineConfig) (Bit ByteSz) <-
    FromBit (Array (cfgLineBytes ClintLineConfig) (Bit ByteSz)) #readWord ;
  @Return ty tClint (LineReadRp ClintLineConfig) (STRUCT {
    "data" ::= #readBytes ;
    "tag"  ::= Const ty (Array (cfgNumLineTags ClintLineConfig) Bool) (getDefault _)
  }))))).

Definition clintLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq ClintLineConfig))
           : Action ty tClint (Bit 0) :=
  Let offset <- getMemOffset base ClintSizeBytes (rq`"addr") ;
  Let regIdx : Bit ClintRegIdxWidth <- TruncMsb ClintRegIdxWidth LgNumBytesXlen #offset ;
  Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
  ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
  ReadReg "mtimecmph" clintMtimecmphPath (fun mtimecmphVal =>
  ReadReg "mtime" clintMtimePath (fun mtimeVal =>
  ReadReg "mtimeh" clintMtimehPath (fun mtimehVal =>
  Let newMtimecmpLo : Bit Xlen <- ITE (Eq #regIdx (clintRegIdxBit "mtimecmp")) #writeWord #mtimecmpVal ;
  Let newMtimecmpHi : Bit Xlen <- ITE (Eq #regIdx (clintRegIdxBit "mtimecmph")) #writeWord #mtimecmphVal ;
  Let newMtimeLo    : Bit Xlen <- ITE (Eq #regIdx (clintRegIdxBit "mtime")) #writeWord #mtimeVal ;
  Let newMtimeHi    : Bit Xlen <- ITE (Eq #regIdx (clintRegIdxBit "mtimeh")) #writeWord #mtimehVal ;
  Let newMtimecmp   : Bit DXlen <- {< #newMtimecmpHi, #newMtimecmpLo >} ;
  Let newMtime      : Bit DXlen <- {< #newMtimeHi, #newMtimeLo >} ;
  If (Eq #regIdx (clintRegIdxBit "mtimecmp")) Then (
    WriteReg clintMtimecmpPath #writeWord Retv
  ) ;
  If (Eq #regIdx (clintRegIdxBit "mtimecmph")) Then (
    WriteReg clintMtimecmphPath #writeWord Retv
  ) ;
  If (Eq #regIdx (clintRegIdxBit "mtime")) Then (
    WriteReg clintMtimePath #writeWord Retv
  ) ;
  If (Eq #regIdx (clintRegIdxBit "mtimeh")) Then (
    WriteReg clintMtimehPath #writeWord Retv
  ) ;
  Let isClintReg : Bool <-
    Or [ Eq #regIdx (clintRegIdxBit "mtimecmp") ;
         Eq #regIdx (clintRegIdxBit "mtimecmph") ;
         Eq #regIdx (clintRegIdxBit "mtime") ;
         Eq #regIdx (clintRegIdxBit "mtimeh") ] ;
  If #isClintReg Then (
    WriteReg clintInterruptPendingPath (Sge #newMtime #newMtimecmp) Retv
  ) ;
  Retv)))).

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
  regionKind        := @CustomMem "clint" (Z.to_nat ClintSizeBytes) ClintLineConfig clintChildren (clintLineReadAction base) (clintLineWriteAction base) ;
  regionInMemory    := pfBound ;
  regionBaseAligned := pfAligned ;
  regionSizeAligned := I
|}.

Arguments clintMemRegion base pfBound pfAligned : clear implicits.

(* ===========================================================================
 * 4. System Integration Helpers
 * =========================================================================== *)

Record ClintDevice := {
  clintBase    : Z ;
  clintPfBound : Is_true ((0 <=? clintBase) && (clintBase + ClintSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  clintPfAlign : Is_true (clintBase mod (2 ^ Z.of_nat (cfgLgLineBytes ClintLineConfig)) =? 0)%Z
}.

Section ClintSystem.
  Variable clint : ClintDevice.
  Variable regions : list MemRegion.
  Variable clintIdx : nat.
  Variable pfClint : nth_error regions clintIdx = Some (clintMemRegion clint.(clintBase) clint.(clintPfBound) clint.(clintPfAlign)).
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Definition clintAction {k : Kind} (act : Action ty tClint k) : Action ty memTree k :=
    nthRegionAction clintIdx regions (clintMemRegion clint.(clintBase) clint.(clintPfBound) clint.(clintPfAlign)) pfClint act.

  Definition clintTickAction : Action ty memTree (Bit 0) :=
    clintAction (clintTick ty).

  Definition clintMtipAction : Action ty memTree Bool :=
    clintAction (clintMtip ty).

End ClintSystem.
