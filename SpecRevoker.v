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
From Cheriot Require Import SpecDefines SpecDevice FunctionalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. Revoker Register Map & MemRegion Constructor
 * =========================================================================== *)

Local Abbreviation ByteSz := 8%Z.

Definition RevokerControlSignature : Z := 0x5500.
Definition RevokerControlSignatureWidth : Z := Eval compute in (Xlen / 2).

Definition RevokerRegNames : list string :=
  [ "base" ; "top" ; "control" ; "epoch" ; "interruptStatus" ; "interruptRequested" ].

Definition RevokerNumRegs : nat := Eval compute in (length RevokerRegNames).
Definition RevokerSizeBytes : Z := Eval compute in (Z.of_nat RevokerNumRegs * NumBytesXlen)%Z.
Definition RevokerOffsetSz : Z := Eval compute in (Z.log2_up RevokerSizeBytes).

Definition REVOKER_BASE_LINE_OFFSET      : Z := 0x00.
Definition REVOKER_CONTROL_LINE_OFFSET   : Z := 0x08.
Definition REVOKER_INTERRUPT_LINE_OFFSET : Z := 0x10.

Section Revoker.
  Variable dom : string.
  Variable extraChildren : list (Tree DomainElem).

  Definition revokerChildren : list (Tree DomainElem) :=
    ([ Leaf "base" (dom, EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero) false)) ;
       Leaf "top" (dom, EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero) false)) ;
       Leaf "control" (dom, EReg (Build_Reg Bool (Some false) false)) ;
       Leaf "epoch" (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false)) ;
       Leaf "interruptStatus" (dom, EReg (Build_Reg Bool (Some false) false)) ;
       Leaf "interruptRequested" (dom, EReg (Build_Reg Bool (Some false) false)) ;
       Leaf "scanAddr" (dom, EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero) false)) ] ++ extraChildren)%list.

  Local Abbreviation tRev := (Node "revoker" revokerChildren).

  Definition revokerBasePath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "base").
  Definition revokerTopPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "top").
  Definition revokerControlPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "control").
  Definition revokerEpochPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "epoch").
  Definition revokerInterruptStatusPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "interruptStatus").
  Definition revokerInterruptRequestedPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "interruptRequested").
  Definition revokerScanAddrPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "scanAddr").

  Definition RevokerLineConfig : LineConfig := {|
    cfgLgLineBytes := Z.to_nat LgNumBytesFullCapSz ;
    cfgHasTags     := false ;
    cfgLinePf      := I
  |}.

  Local Abbreviation numLineWords := (Z.to_nat (NumBytesFullCapSz / NumBytesXlen)).

  Definition readRevokerLine
             {ty : Kind -> Type} {ans : Kind}
             (offset : Expr ty (Bit RevokerOffsetSz))
             (k : ty (Array (cfgLineBytes RevokerLineConfig) (Bit ByteSz)) -> Action ty tRev ans)
             : Action ty tRev ans :=
    ReadReg "base" revokerBasePath (fun baseVal =>
    ReadReg "top" revokerTopPath (fun topVal =>
    ReadReg "control" revokerControlPath (fun kickVal =>
    ReadReg "epoch" revokerEpochPath (fun epochVal =>
    ReadReg "interruptStatus" revokerInterruptStatusPath (fun statusVal =>
    ReadReg "interruptRequested" revokerInterruptRequestedPath (fun reqVal =>
      let baseWord    := {< #baseVal, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} in
      let topWord     := {< #topVal, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} in
      let controlWord := {< Const ty (Bit RevokerControlSignatureWidth) (bits.of_Z RevokerControlSignatureWidth RevokerControlSignature),
                            Const ty (Bit (RevokerControlSignatureWidth - 1)) Zmod.zero,
                            ToBit #kickVal >} in
      let epochWord   := #epochVal in
      let statusWord  := ZeroExtendTo Xlen (ToBit #statusVal) in
      let reqWord     := ZeroExtendTo Xlen (ToBit #reqVal) in
      Let readData : Bit FullCapSz <-
        Or [ ITE0 (Eq offset $(REVOKER_BASE_LINE_OFFSET))      {< topWord, baseWord >} ;
             ITE0 (Eq offset $(REVOKER_CONTROL_LINE_OFFSET))   {< epochWord, controlWord >} ;
             ITE0 (Eq offset $(REVOKER_INTERRUPT_LINE_OFFSET)) {< reqWord, statusWord >} ] ;
      Let lineBytes : Array (cfgLineBytes RevokerLineConfig) (Bit ByteSz) <-
        FromBit (Array (cfgLineBytes RevokerLineConfig) (Bit ByteSz)) #readData ;
      k lineBytes
    )))))).

  Definition revokerLineReadAction
             (base : Z)
             (ty : Kind -> Type)
             (_ : ReadPortSel false)
             (addr : ty Addr)
             (_ : ty (Array (cfgLineBytes RevokerLineConfig) Bool))
             : Action ty tRev (LineReadRp RevokerLineConfig false) :=
    Let offset : Bit RevokerOffsetSz <- getMemOffset base RevokerSizeBytes #addr ;
    readRevokerLine #offset (fun readBytes =>
      @Return ty tRev (LineReadRp RevokerLineConfig false) (STRUCT {
        "data" ::= #readBytes ;
        "tag"  ::= Const ty (Array (cfgNumLineTags RevokerLineConfig false) Bool) (getDefault _)
      })
    ).

  Definition revokerLineWriteAction
             (base : Z)
             (ty : Kind -> Type)
             (rq : ty (LineWriteRq RevokerLineConfig false))
             : Action ty tRev (Bit 0) :=
    Let offset : Bit RevokerOffsetSz <- getMemOffset base RevokerSizeBytes (##rq`"addr") ;
    readRevokerLine #offset (fun oldBytes =>
      Let newBytes : Array (cfgLineBytes RevokerLineConfig) (Bit ByteSz) <-
        ArrayBuilder (fun i =>
          ITE (ReadArrayConst (##rq`"dataMask") i)
              (ReadArrayConst (##rq`"data") i)
              (ReadArrayConst #oldBytes i)) ;
      Let newWords : Array numLineWords (Bit Xlen) <-
        FromBit (Array numLineWords (Bit Xlen)) (ToBit ##newBytes) ;
      If (Eq #offset $(REVOKER_BASE_LINE_OFFSET)) Then (
        Let newBase : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz ((##newWords) $[0%nat]) ;
        Let newTop  : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz ((##newWords) $[1%nat]) ;
        Act (WriteReg revokerBasePath #newBase Retv) ;
        Act (WriteReg revokerTopPath #newTop Retv) ;
        Retv
      ) ;
      If (Eq #offset $(REVOKER_CONTROL_LINE_OFFSET)) Then (
        Let newKick : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 ((##newWords) $[0%nat])) ;
        Act (WriteReg revokerControlPath #newKick Retv) ;
        Act (WriteReg revokerEpochPath ((##newWords) $[1%nat]) Retv) ;
        Retv
      ) ;
      If (Eq #offset $(REVOKER_INTERRUPT_LINE_OFFSET)) Then (
        Let clearStatus : Bool <-
          And [ (##rq`"dataMask") $[0%nat] ;
                FromBit Bool (TruncLsb (ByteSz - 1) 1 ((##rq`"data") $[0%nat])) ] ;
        If #clearStatus Then (
          Act (WriteReg revokerInterruptStatusPath (ConstBool false) Retv) ;
          Retv
        ) ;
        Let newReq : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 ((##newWords) $[1%nat])) ;
        Act (WriteReg revokerInterruptRequestedPath #newReq Retv) ;
        Retv
      ) ;
      Retv
    ).

  Definition revokerLocalInterrupt
             {ty : Kind -> Type}
             : Action ty tRev Bool :=
    ReadReg "intStatus" revokerInterruptStatusPath (fun intStatus =>
    ReadReg "intRequest" revokerInterruptRequestedPath (fun intRequest =>
    Return (And [#intStatus ; #intRequest]))).

  Definition revokerMemRegion
             (base : Z)
             (pfBound : Is_true ((0 <=? base) && (base + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
             (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes RevokerLineConfig)) =? 0)%Z)
             : MemRegion := {|
    regionName        := "revoker" ;
    regionDom         := dom ;
    regionBase        := base ;
    regionSize        := RevokerSizeBytes ;
    regionLineCfg     := RevokerLineConfig ;
    isReadOnly        := false ;
    hasExtraFetchPort := false ;
    regionKind        := @CustomMem "revoker" RevokerSizeBytes RevokerLineConfig false revokerChildren
                                    (@revokerLineReadAction base)
                                    (@revokerLineWriteAction base)
                                    (Some (fun ty => revokerLocalInterrupt)) ;
    regionInMemory    := pfBound ;
    regionBaseAligned := pfAligned ;
    regionSizeAligned := I
  |}.

  Record RevokerInstance (regions : list MemRegion) := {
    revokerIdx      : nat ;
    revokerBaseAddr : Z ;
    pfBound         : Is_true ((0 <=? revokerBaseAddr) && (revokerBaseAddr + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
    pfAligned       : Is_true (revokerBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes RevokerLineConfig)) =? 0)%Z ;
    pfRevoker       : nth_error regions revokerIdx = Some (@revokerMemRegion revokerBaseAddr pfBound pfAligned)
  }.

  Definition revokerRegion {regions} (rev : RevokerInstance regions) : MemRegion :=
    @revokerMemRegion rev.(revokerBaseAddr) rev.(pfBound) rev.(pfAligned).

  (* ===========================================================================
   * 2. Autonomous Revoker Step Action & Interrupt Query
   * =========================================================================== *)

  Section RevokerAction.
    Variable regions : list MemRegion.
    Variable rev : RevokerInstance regions.
    Variable config : RevConfig.
    Variable ty : Kind -> Type.

    Local Abbreviation memTree := (specMemTree regions).

    Local Definition revokerAction {k : Kind} (act : Action ty tRev k) : Action ty memTree k :=
      nthRegionAction rev.(revokerIdx) regions (revokerRegion rev) rev.(pfRevoker) act.

    Local Definition readRevokerBase : Action ty memTree (Bit TagAddrWidth) :=
      revokerAction (ReadReg "base" revokerBasePath (fun v => Return #v)).

    Local Definition readRevokerTop : Action ty memTree (Bit TagAddrWidth) :=
      revokerAction (ReadReg "top" revokerTopPath (fun v => Return #v)).

    Local Definition readRevokerControl : Action ty memTree Bool :=
      revokerAction (ReadReg "control" revokerControlPath (fun v => Return #v)).

    Local Definition writeRevokerControl (v : ty Bool) : Action ty memTree (Bit 0) :=
      revokerAction (WriteReg revokerControlPath #v Retv).

    Local Definition readRevokerEpoch : Action ty memTree (Bit Xlen) :=
      revokerAction (ReadReg "epoch" revokerEpochPath (fun v => Return #v)).

    Local Definition writeRevokerEpoch (v : ty (Bit Xlen)) : Action ty memTree (Bit 0) :=
      revokerAction (WriteReg revokerEpochPath #v Retv).

    Local Definition readRevokerInterruptStatus : Action ty memTree Bool :=
      revokerAction (ReadReg "interruptStatus" revokerInterruptStatusPath (fun v => Return #v)).

    Local Definition writeRevokerInterruptStatus (v : ty Bool) : Action ty memTree (Bit 0) :=
      revokerAction (WriteReg revokerInterruptStatusPath #v Retv).

    Local Definition readRevokerInterruptRequested : Action ty memTree Bool :=
      revokerAction (ReadReg "interruptRequested" revokerInterruptRequestedPath (fun v => Return #v)).

    Local Definition writeRevokerInterruptRequested (v : ty Bool) : Action ty memTree (Bit 0) :=
      revokerAction (WriteReg revokerInterruptRequestedPath #v Retv).

    Local Definition readRevokerScanAddr : Action ty memTree (Bit TagAddrWidth) :=
      revokerAction (ReadReg "scanAddr" revokerScanAddrPath (fun v => Return #v)).

    Local Definition writeRevokerScanAddr (v : ty (Bit TagAddrWidth)) : Action ty memTree (Bit 0) :=
      revokerAction (WriteReg revokerScanAddrPath #v Retv).

    Local Abbreviation readRevBit := (readRevBit config regions).

    Definition specRevokerStep : Action ty memTree (Bit 0) :=
      LetA epoch : Bit Xlen <- readRevokerEpoch ;
      Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;

      If #isOddEpoch Then (
        (* SWEEPING STATE: epoch is odd *)
        LetA scanAddrMsb : Bit TagAddrWidth <- readRevokerScanAddr ;
        LetA topAddrMsb  : Bit TagAddrWidth <- readRevokerTop ;
        Let scanAddr     : Addr <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Let isDone       : Bool <- Uge #scanAddrMsb #topAddrMsb ;

        If (Not #isDone) Then (
          (* 1. Inspect capability at current scanAddr *)
          Let capSz      : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
          LetA ldFullCap : FullCapWithTag            <- specMemRead regions false scanAddr capSz ;
          Let ldTag      : Bool                      <- ##ldFullCap`"tag" ;
          Let ldCap      : Cap                       <- ##ldFullCap`"cap" ;
          Let ldAddr     : Addr                      <- ##ldFullCap`"addr" ;
          LetL ldECap    : ECap                      <- DecodeCap ldCap ldAddr ;
          If (needsRevocationCheck config ldECap ldTag) Then (
            Let ldBase : Bit (AddrSz + 1) <- ##ldECap`"base" ;
            LetA revBit : Bool <- readRevBit ldBase ;
            If #revBit Then (
              (* Capability revoked: invalidate tag in memory *)
              Let untaggedCap : FullCapWithTag <- STRUCT {
                "tag"  ::= Const ty Bool false ;
                "cap"  ::= #ldCap ;
                "addr" ::= #ldAddr
              } ;
              Act (specMemWrite regions scanAddr untaggedCap capSz) ;
              Retv
            ) ;
            Retv
          ) ;
          (* Advance scan pointer: increment scanAddrMsb *)
          Let nextScanAddrMsb : Bit TagAddrWidth <-
            Add [ #scanAddrMsb ; $1 ] ;
          Act (writeRevokerScanAddr nextScanAddrMsb) ;
          Retv
        ) Else (
          (* SWEEP COMPLETE: scanAddr reached top *)
          (* Transition epoch from odd (sweeping) to even (idle) *)
          Let nextEpoch : Bit Xlen <- Add [ #epoch ; $1 ] ;
          Act (writeRevokerEpoch nextEpoch) ;
          (* Record sweep completion in interruptStatus if software requested an interrupt *)
          LetA intReq : Bool <- readRevokerInterruptRequested ;
          If #intReq Then (
            Let bTrue : Bool <- ConstBool true ;
            Act (writeRevokerInterruptStatus bTrue) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) Else (
        (* IDLE STATE: epoch is even *)
        Let bFalse : Bool <- ConstBool false ;
        Act (writeRevokerInterruptStatus bFalse) ;
        LetA isKicked : Bool <- readRevokerControl ;
        If #isKicked Then (
          (* Start sweep: initialize scanAddr to base and advance epoch to odd *)
          LetA baseAddrMsb : Bit TagAddrWidth <- readRevokerBase ;
          Act (writeRevokerScanAddr baseAddrMsb) ;
          Let oddEpoch : Bit Xlen <-
            {< TruncMsb (Xlen - 1) 1 #epoch, Const ty (Bit 1) (bits.of_Z 1 1) >} ;
          Act (writeRevokerEpoch oddEpoch) ;
          (* Clear kick bit in control *)
          Act (writeRevokerControl bFalse) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.
  End RevokerAction.

End Revoker.
