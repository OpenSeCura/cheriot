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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
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

  Definition clintMtimePath       : RegPath tClint := Eval cbn in (getChildRegPathTree tClint "mtime").
  Definition clintMtimecmpPath    : RegPath tClint := Eval cbn in (getChildRegPathTree tClint "mtimecmp").
  Definition clintMtipPath        : RegPath tClint := Eval cbn in (getChildRegPathTree tClint "mtip").
  Definition clintSampledMtipPath : RegPath tClint := Eval cbn in (getChildRegPathTree tClint "sampledMtip").

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

  (* The line at `offset`: each 64-bit register in its doubleword slot of its line *)
  Definition clintLine {ty : Kind -> Type}
             (offset : Expr ty (Bit (Z.log2_up ClintSizeBytes)))
             (mtimeVal mtimecmpVal : Expr ty (Bit DXlen))
             : Expr ty (Array LineBytes (Bit ByteSz)) :=
    let regs : list (Z * Expr ty (Bit DXlen)) :=
      [ (CLINT_MTIME_OFFSET, mtimeVal) ; (CLINT_MTIMECMP_OFFSET, mtimecmpVal) ] in
    FromBit (Array LineBytes (Bit ByteSz))
      (ToBit (ArrayBuilder (fun j : FinType NumLineDWords =>
         Or (map (fun ov =>
                    if Nat.eqb (slotOf (DXlen / ByteSz) (fst ov)) (finNum j)
                    then ITE0 (Eq offset $(lineOffsetOf (fst ov))) (snd ov)
                    else $0) regs)))).

  Definition clintLineReadAction
             (base : Z)
             (ty : Kind -> Type)
             (addr : ty Addr)
             (_ : ty (Array LineBytes Bool))
             : Action ty tClint (Array LineBytes (Bit ByteSz)) :=
    Let offset <- getMemOffset base ClintSizeBytes #addr ;
    ReadReg "mtime" clintMtimePath (fun mtimeVal =>
    ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
    Let readBytes : Array LineBytes (Bit ByteSz) <- clintLine #offset #mtimeVal #mtimecmpVal ;
    Return #readBytes)).

  (* A register takes the merged doubleword of its slot when the write covers one of its bytes *)
  Definition clintLineWriteAction
             (base : Z)
             (ty : Kind -> Type)
             (addr : ty Addr)
             (data : ty (Array LineBytes (Bit ByteSz)))
             (dataMask : ty (Array LineBytes Bool))
             : Action ty tClint (Bit 0) :=
    Let offset <- getMemOffset base ClintSizeBytes #addr ;
    ReadReg "mtime" clintMtimePath (fun mtimeVal =>
    ReadReg "mtimecmp" clintMtimecmpPath (fun mtimecmpVal =>
    Let oldBytes : Array LineBytes (Bit ByteSz) <- clintLine #offset #mtimeVal #mtimecmpVal ;
    Let newBytes : Array LineBytes (Bit ByteSz) <-
      ArrayBuilder (fun i =>
        ITE (ReadArrayConst #dataMask i)
            (ReadArrayConst #data i)
            (ReadArrayConst #oldBytes i)) ;
    Let newDWords : Array NumLineDWords (Bit DXlen) <-
      FromBit (Array NumLineDWords (Bit DXlen)) (ToBit ##newBytes) ;
    Let maskDWords : Array NumLineDWords (Bit (DXlen / ByteSz)) <-
      FromBit (Array NumLineDWords (Bit (DXlen / ByteSz))) (ToBit ##dataMask) ;
    If (And [ Eq #offset $(lineOffsetOf CLINT_MTIME_OFFSET) ;
              isNotZero ((##maskDWords) $[slotOf (DXlen / ByteSz) CLINT_MTIME_OFFSET]) ]) Then (
      WriteReg clintMtimePath ((##newDWords) $[slotOf (DXlen / ByteSz) CLINT_MTIME_OFFSET]) Retv
    ) ;
    If (And [ Eq #offset $(lineOffsetOf CLINT_MTIMECMP_OFFSET) ;
              isNotZero ((##maskDWords) $[slotOf (DXlen / ByteSz) CLINT_MTIMECMP_OFFSET]) ]) Then (
      WriteReg clintMtimecmpPath ((##newDWords) $[slotOf (DXlen / ByteSz) CLINT_MTIMECMP_OFFSET]) (
      WriteReg clintMtipPath (ConstBool false) (
      WriteReg clintSampledMtipPath (ConstBool false) Retv))
    ) ;
    Retv)).

  (* ===========================================================================
   * MemRegion Constructor
   * =========================================================================== *)

  Definition clintMemRegion
             (base : Z)
             (pfBound : Is_true ((0 <=? base) && (base + ClintSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
             (pfAligned : Is_true (base mod (2 ^ LgLineBytes) =? 0)%Z)
             : MemRegion := {|
    regionName        := "clint" ;
    regionBase        := base ;
    regionSize        := ClintSizeBytes ;
    regionKind        := @CustomMem "clint" clintChildren (@clintLineReadAction base) (@clintLineWriteAction base) None ;
    regionSizeNonNeg  := I ;
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
    pfAligned     : Is_true (clintBaseAddr mod (2 ^ LgLineBytes) =? 0)%Z ;
    pfClint       : nth_error regions clintIdx = Some (@clintMemRegion clintBaseAddr pfBound pfAligned)
  }.

  Definition clintRegion {regions} (clint : ClintInstance regions) : MemRegion :=
    @clintMemRegion clint.(clintBaseAddr) clint.(pfBound) clint.(pfAligned).

  Section ClintSystem.
    Variable regions : list MemRegion.
    Variable clint : ClintInstance regions.
    Variable ty : Kind -> Type.

    Local Abbreviation memTree := (specMemTree dom regions).

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
