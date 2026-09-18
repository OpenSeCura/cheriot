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
 * CLINT Register Offsets & Tree Structure
 * =========================================================================== *)

Definition ClintSizeBytes : Z := 0x10000.

Definition CLINT_MTIMECMP_OFFSET  : Z := 0x4000.
Definition CLINT_MTIMECMPH_OFFSET : Z := 0x4004.
Definition CLINT_MTIME_OFFSET     : Z := 0xbff8.
Definition CLINT_MTIMEH_OFFSET    : Z := 0xbffc.

Section Clint.
  Variable dom : string.

  Definition clintChildren : list (Tree DomainElem) :=
    [ Leaf "mtime"     (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false)) ;
      Leaf "mtimeh"    (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false)) ;
      Leaf "mtimecmp"  (dom, EReg (Build_Reg (Bit Xlen) (Some (Zmod.of_Z _ (2^Xlen - 1))) false)) ;
      Leaf "mtimecmph" (dom, EReg (Build_Reg (Bit Xlen) (Some (Zmod.of_Z _ (2^Xlen - 1))) false)) ;
      Leaf "mtip"      (dom, EReg (Build_Reg Bool       (Some false)     false)) ].

  Local Notation tClint := (Node "clint" clintChildren).

  Definition clintMtimePath     : RegPath tClint := getChildRegPathTree tClint "mtime".
  Definition clintMtimehPath    : RegPath tClint := getChildRegPathTree tClint "mtimeh".
  Definition clintMtimecmpPath  : RegPath tClint := getChildRegPathTree tClint "mtimecmp".
  Definition clintMtimecmphPath : RegPath tClint := getChildRegPathTree tClint "mtimecmph".
  Definition clintMtipPath      : RegPath tClint := getChildRegPathTree tClint "mtip".

  Definition ClintLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

  (* ===========================================================================
   * CLINT Atomic Actions
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

    Definition readClintMtip : Action ty tClint Bool :=
      ReadReg "mtip" clintMtipPath (fun v => Return #v).

    Definition clintTick : Action ty tClint (Bit 0) :=
      LetA mtimeDXlen    : Bit DXlen <- readClintMtime ;
      LetA mtimecmpDXlen : Bit DXlen <- readClintMtimecmp ;
      Let  nextMtime     : Bit DXlen <- Add [ #mtimeDXlen ; $1 ] ;
      Act (WriteReg clintMtimePath (TruncLsb Xlen Xlen #nextMtime) Retv) ;
      Act (WriteReg clintMtimehPath (TruncMsb Xlen Xlen #nextMtime) Retv) ;
      Let  isMatch       : Bool      <- Uge #nextMtime #mtimecmpDXlen ;
      LetA currMtip      : Bool      <- readClintMtip;
      WriteReg clintMtipPath (Or [#currMtip ; #isMatch]) Retv.

  End ClintActions.

  Definition clintLineReadAction
             (base : Z)
             (ty : Kind -> Type)
             (addr : ty Addr)
             : Action ty tClint (LineReadRp ClintLineConfig) :=
    Let offset <- getMemOffset base ClintSizeBytes #addr ;
    ReadReg "mtime" clintMtimePath (fun mtimeVal =>
    ReadReg "mtimeh" clintMtimehPath (fun mtimehVal =>
    ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
    ReadReg "mtimecmph" clintMtimecmphPath (fun mtimecmphVal =>
    Let readWord : Bit Xlen <-
      Or [ ITE0 (Eq #offset $(CLINT_MTIME_OFFSET))     #mtimeVal ;
           ITE0 (Eq #offset $(CLINT_MTIMEH_OFFSET))    #mtimehVal ;
           ITE0 (Eq #offset $(CLINT_MTIMECMP_OFFSET))  #mtimecmpVal ;
           ITE0 (Eq #offset $(CLINT_MTIMECMPH_OFFSET)) #mtimecmphVal ] ;
    Let readBytes : Array (cfgLineBytes ClintLineConfig) (Bit ByteSz) <-
      FromBit (Array (cfgLineBytes ClintLineConfig) (Bit ByteSz)) #readWord ;
    @Return ty tClint (LineReadRp ClintLineConfig) (STRUCT {
      "data" ::= #readBytes ;
      "tag"  ::= Const ty (Array (cfgNumLineTags ClintLineConfig) Bool) (getDefault _)
    }))))).

  Definition clintLineWriteAction
             (base : Z)
             (ty : Kind -> Type)
             (rq : ty (LineWriteRq ClintLineConfig))
             : Action ty tClint (Bit 0) :=
    Let offset <- getMemOffset base ClintSizeBytes (##rq`"addr") ;
    Let writeWord : Bit Xlen <- ToBit (##rq`"data") ;
    If (Eq #offset $(CLINT_MTIME_OFFSET)) Then (
      WriteReg clintMtimePath #writeWord Retv
    ) ;
    If (Eq #offset $(CLINT_MTIMEH_OFFSET)) Then (
      WriteReg clintMtimehPath #writeWord Retv
    ) ;
    If (Eq #offset $(CLINT_MTIMECMP_OFFSET)) Then (
      WriteReg clintMtimecmpPath #writeWord (
      WriteReg clintMtipPath (ConstBool false) Retv)
    ) ;
    If (Eq #offset $(CLINT_MTIMECMPH_OFFSET)) Then (
      WriteReg clintMtimecmphPath #writeWord (
      WriteReg clintMtipPath (ConstBool false) Retv)
    ) ;
    Retv.

  Arguments clintLineReadAction base ty addr : clear implicits.
  Arguments clintLineWriteAction base ty rq : clear implicits.

  (* ===========================================================================
   * MemRegion Constructor
   * =========================================================================== *)

  Definition clintMemRegion
             (base : Z)
             (pfBound : Is_true ((0 <=? base) && (base + ClintSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
             (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes ClintLineConfig)) =? 0)%Z)
             : MemRegion := {|
    regionName        := "clint" ;
    regionDom         := dom ;
    regionBase        := base ;
    regionSize        := ClintSizeBytes ;
    regionLineCfg     := ClintLineConfig ;
    isReadOnly        := false ;
    regionKind        := @CustomMem "clint" ClintSizeBytes ClintLineConfig clintChildren (clintLineReadAction base) (clintLineWriteAction base) None ;
    regionInMemory    := pfBound ;
    regionBaseAligned := pfAligned ;
    regionSizeAligned := I
  |}.

  Arguments clintMemRegion base pfBound pfAligned : clear implicits.

  (* ===========================================================================
   * System Integration Helpers
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

    Definition readClintMtipAction : Action ty memTree Bool :=
      clintAction (readClintMtip ty).

  End ClintSystem.

End Clint.
