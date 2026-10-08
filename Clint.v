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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition SimulatorOnly.
From Cheriot Require Import SpecDefines SpecDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation ByteSz := 8%Z.

(* ===========================================================================
 * CLINT Register Offsets & Tree Structure
 * =========================================================================== *)

Definition ClintSizeBytes : Z := 0x10000.

Definition CLINT_MTIMECMP_OFFSET : Z := 0x4000.
Definition CLINT_MTIME_OFFSET    : Z := 0xbff8.

Section Clint.
  Variable dom : string.

  Definition clintChildren : list (Tree DomainElem) :=
    [ Leaf "mtime"       (dom, EReg (Build_Reg (Bit DXlen) (Some Zmod.zero) false)) ;
      Leaf "mtimecmp"    (dom, EReg (Build_Reg (Bit DXlen) (Some (Zmod.of_Z _ (2^DXlen - 1))) false)) ;
      Leaf "mtip"        (dom, EReg (Build_Reg Bool        (Some false)     false)) ;
      Leaf "sampledMtip" (dom, EReg (Build_Reg Bool        (Some false)     false)) ].

  Local Abbreviation tClint := (Node "clint" clintChildren).

  Definition clintMtimePath       : RegPath tClint := getChildRegPathTree tClint "mtime".
  Definition clintMtimecmpPath    : RegPath tClint := getChildRegPathTree tClint "mtimecmp".
  Definition clintMtipPath        : RegPath tClint := getChildRegPathTree tClint "mtip".
  Definition clintSampledMtipPath : RegPath tClint := getChildRegPathTree tClint "sampledMtip".

  Definition ClintLineConfig : LineConfig := {|
    cfgLgLineBytes := Z.to_nat LgNumBytesFullCapSz ;
    cfgHasTags     := false ;
    cfgLinePf      := I
  |}.

  (* ===========================================================================
   * CLINT Atomic Actions
   * =========================================================================== *)

  Section ClintActions.
    Variable ty : Kind -> Type.

    Definition readClintMtime : Action ty tClint (Bit DXlen) :=
      ReadReg "mtime" clintMtimePath (fun v => Return #v).

    Definition readClintMtimecmp : Action ty tClint (Bit DXlen) :=
      ReadReg "mtimecmp" clintMtimecmpPath (fun v => Return #v).

    Definition readClintMtip : Action ty tClint Bool :=
      ReadReg "sampledMtip" clintSampledMtipPath (fun v => Return #v).

    Definition clintTick : Action ty tClint (Bit 0) :=
      LetA mtimeDXlen    : Bit DXlen <- readClintMtime ;
      LetA mtimecmpDXlen : Bit DXlen <- readClintMtimecmp ;
      Let  nextMtime     : Bit DXlen <- Add [ #mtimeDXlen ; $1 ] ;
      Act (WriteReg clintMtimePath #nextMtime Retv) ;
      Let  isMatch       : Bool      <- Uge #nextMtime #mtimecmpDXlen ;
      LetA currMtip      : Bool      <- ReadReg "mtip" clintMtipPath (fun v => Return #v) ;
      Let  nextMtip      : Bool      <- Or [#currMtip ; #isMatch] ;
      Act (WriteReg clintMtipPath #nextMtip Retv) ;
      If (Not #nextMtip) Then (
        WriteReg clintSampledMtipPath (ConstBool false) Retv
      ) ;
      Retv.

    Definition clintSampleMtip : Action ty tClint (Bit 0) :=
      ReadReg "mtip" clintMtipPath (fun currMtip =>
        If #currMtip Then (
          WriteReg clintSampledMtipPath (ConstBool true) Retv
        ) ;
        Retv
      ).

  End ClintActions.

  Definition clintLineReadAction
             (base : Z)
             (ty : Kind -> Type)
             (_ : ReadPortSel false)
             (addr : ty Addr)
             (_ : ty (Array (cfgLineBytes ClintLineConfig) Bool))
             : Action ty tClint (LineReadRp ClintLineConfig false) :=
    Let offset <- getMemOffset base ClintSizeBytes #addr ;
    ReadReg "mtime" clintMtimePath (fun mtimeVal =>
    ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
    Let rawData : Bit DXlen <-
      Or [ ITE0 (Eq #offset $(CLINT_MTIME_OFFSET))    #mtimeVal ;
           ITE0 (Eq #offset $(CLINT_MTIMECMP_OFFSET)) #mtimecmpVal ] ;
    Let readBytes : Array (cfgLineBytes ClintLineConfig) (Bit ByteSz) <-
      FromBit (Array (cfgLineBytes ClintLineConfig) (Bit ByteSz)) #rawData ;
    @Return ty tClint (LineReadRp ClintLineConfig false) (STRUCT {
      "data" ::= #readBytes ;
      "tag"  ::= Const ty (Array (cfgNumLineTags ClintLineConfig false) Bool) (getDefault _)
    }))).

  Definition clintLineWriteAction
             (base : Z)
             (ty : Kind -> Type)
             (rq : ty (LineWriteRq ClintLineConfig false))
             : Action ty tClint (Bit 0) :=
    Let offset   <- getMemOffset base ClintSizeBytes (##rq`"addr") ;
    Let anyWrite : Bool <- isNotZero (ToBit (##rq`"dataMask")) ;
    let mergeReg (oldVal : Expr ty (Bit DXlen)) : Expr ty (Bit DXlen) :=
      let oldBytes := FromBit (Array (cfgLineBytes ClintLineConfig) (Bit ByteSz)) oldVal in
      ToBit (ArrayBuilder (fun i =>
        ITE (ReadArrayConst (##rq`"dataMask") i)
            (ReadArrayConst (##rq`"data") i)
            (ReadArrayConst oldBytes i))) in
    If #anyWrite Then (
      Act (If (Eq #offset $(CLINT_MTIME_OFFSET)) Then (
        ReadReg "mtime" clintMtimePath (fun mtimeVal =>
        WriteReg clintMtimePath (mergeReg #mtimeVal) Retv)
      ) ; Retv) ;
      If (Eq #offset $(CLINT_MTIMECMP_OFFSET)) Then (
        ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
        WriteReg clintMtimecmpPath (mergeReg #mtimecmpVal) (
        WriteReg clintMtipPath (ConstBool false) (
        WriteReg clintSampledMtipPath (ConstBool false) Retv)))
      ) ;
      Retv
    ) ;
    Retv.

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
    hasExtraFetchPort := false ;
    regionKind        := @CustomMem "clint" ClintSizeBytes ClintLineConfig false clintChildren (@clintLineReadAction base) (@clintLineWriteAction base) None ;
    regionInMemory    := pfBound ;
    regionBaseAligned := pfAligned ;
    regionSizeAligned := I
  |}.

  (* ===========================================================================
   * System Integration Helpers
   * =========================================================================== *)

  Record ClintInstance (regions : list MemRegion) := {
    clintIdx      : nat ;
    clintBaseAddr : Z ;
    pfBound       : Is_true ((0 <=? clintBaseAddr) && (clintBaseAddr + ClintSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
    pfAligned     : Is_true (clintBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes ClintLineConfig)) =? 0)%Z ;
    pfClint       : nth_error regions clintIdx = Some (@clintMemRegion clintBaseAddr pfBound pfAligned)
  }.

  Definition clintRegion {regions} (clint : ClintInstance regions) : MemRegion :=
    @clintMemRegion clint.(clintBaseAddr) clint.(pfBound) clint.(pfAligned).

  Section ClintSystem.
    Variable regions : list MemRegion.
    Variable clint : ClintInstance regions.
    Variable ty : Kind -> Type.

    Local Abbreviation memTree := (specMemTree regions).

    Definition clintAction {k : Kind} (act : Action ty tClint k) : Action ty memTree k :=
      nthRegionAction clint.(clintIdx) regions (clintRegion clint) clint.(pfClint) act.

    Definition clintTickAction : Action ty memTree (Bit 0) :=
      clintAction (clintTick ty).

    Definition clintSampleMtipAction : Action ty memTree (Bit 0) :=
      clintAction (clintSampleMtip ty).

    Definition readClintMtipAction : Action ty memTree Bool :=
      clintAction (readClintMtip ty).

  End ClintSystem.

End Clint.
