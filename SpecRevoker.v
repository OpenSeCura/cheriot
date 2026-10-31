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
(* One word per register; the region is a whole number of lines *)
Definition RevokerRegsBytes : Z := Eval compute in (Z.of_nat RevokerNumRegs * NumBytesXlen)%Z.
Definition RevokerSizeBytes : Z :=
  Eval compute in ((RevokerRegsBytes + 2 ^ LgLineBytes - 1) / 2 ^ LgLineBytes * 2 ^ LgLineBytes)%Z.
Definition RevokerOffsetSz : Z := Eval compute in (Z.log2_up RevokerSizeBytes).

(* Byte offsets of the registers *)
Definition REVOKER_BASE_OFFSET          : Z := 0x00.
Definition REVOKER_TOP_OFFSET           : Z := 0x04.
Definition REVOKER_CONTROL_OFFSET       : Z := 0x08.
Definition REVOKER_EPOCH_OFFSET         : Z := 0x0c.
Definition REVOKER_INT_STATUS_OFFSET    : Z := 0x10.
Definition REVOKER_INT_REQUESTED_OFFSET : Z := 0x14.

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
       Leaf "scanAddr" (dom, EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero) false)) ;
       (* The sweep's copy of top, taken at the kick: software may write top during a sweep,
        * the sweep in progress ends at the top it started with *)
       Leaf "sweepTop" (dom, EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero) false)) ] ++ extraChildren)%list.

  Local Abbreviation tRev := (Node "revoker" revokerChildren).

  Definition revokerBasePath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "base").
  Definition revokerTopPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "top").
  Definition revokerControlPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "control").
  Definition revokerEpochPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "epoch").
  Definition revokerInterruptStatusPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "interruptStatus").
  Definition revokerInterruptRequestedPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "interruptRequested").
  Definition revokerScanAddrPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "scanAddr").
  Definition revokerSweepTopPath : RegPath tRev := Eval cbn in (getChildRegPathTree tRev "sweepTop").

  (* The line at `offset`: each register word in its slot of its line *)
  Definition readRevokerLine
             {ty : Kind -> Type} {ans : Kind}
             (offset : Expr ty (Bit RevokerOffsetSz))
             (k : ty (Array LineBytes (Bit ByteSz)) -> Action ty tRev ans)
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
      let regWords : list (Z * Expr ty (Bit Xlen)) :=
        [ (REVOKER_BASE_OFFSET, baseWord) ; (REVOKER_TOP_OFFSET, topWord) ;
          (REVOKER_CONTROL_OFFSET, controlWord) ; (REVOKER_EPOCH_OFFSET, epochWord) ;
          (REVOKER_INT_STATUS_OFFSET, statusWord) ; (REVOKER_INT_REQUESTED_OFFSET, reqWord) ] in
      Let lineWords : Array NumLineWords (Bit Xlen) <-
        ArrayBuilder (fun j : FinType NumLineWords =>
          Or (map (fun ow =>
                     if Nat.eqb (slotOf NumBytesXlen (fst ow)) (finNum j)
                     then ITE0 (Eq offset $(lineOffsetOf (fst ow))) (snd ow)
                     else $0) regWords)) ;
      Let lineBytes : Array LineBytes (Bit ByteSz) <-
        FromBit (Array LineBytes (Bit ByteSz)) (ToBit ##lineWords) ;
      k lineBytes
    )))))).

  Definition revokerLineReadAction
             (base : Z)
             (ty : Kind -> Type)
             (addr : ty Addr)
             (_ : ty (Array LineBytes Bool))
             : Action ty tRev (Array LineBytes (Bit ByteSz)) :=
    Let offset : Bit RevokerOffsetSz <- getMemOffset base RevokerSizeBytes #addr ;
    readRevokerLine #offset (fun readBytes => Return #readBytes).

  (* The registers in the line written take the merged words of their slots *)
  Definition revokerLineWriteAction
             (base : Z)
             (ty : Kind -> Type)
             (addr : ty Addr)
             (data : ty (Array LineBytes (Bit ByteSz)))
             (dataMask : ty (Array LineBytes Bool))
             : Action ty tRev (Bit 0) :=
    Let offset : Bit RevokerOffsetSz <- getMemOffset base RevokerSizeBytes #addr ;
    readRevokerLine #offset (fun oldBytes =>
      Let newBytes : Array LineBytes (Bit ByteSz) <-
        ArrayBuilder (fun i =>
          ITE (ReadArrayConst (#dataMask) i)
              (ReadArrayConst (#data) i)
              (ReadArrayConst #oldBytes i)) ;
      Let newWords : Array NumLineWords (Bit Xlen) <-
        FromBit (Array NumLineWords (Bit Xlen)) (ToBit ##newBytes) ;
      If (Eq #offset $(lineOffsetOf REVOKER_BASE_OFFSET)) Then (
        Let newBase : Bit TagAddrWidth <-
          TruncMsb TagAddrWidth LgNumBytesFullCapSz ((##newWords) $[slotOf NumBytesXlen REVOKER_BASE_OFFSET]) ;
        Act (WriteReg revokerBasePath #newBase Retv) ;
        Retv
      ) ;
      If (Eq #offset $(lineOffsetOf REVOKER_TOP_OFFSET)) Then (
        Let newTop : Bit TagAddrWidth <-
          TruncMsb TagAddrWidth LgNumBytesFullCapSz ((##newWords) $[slotOf NumBytesXlen REVOKER_TOP_OFFSET]) ;
        Act (WriteReg revokerTopPath #newTop Retv) ;
        Retv
      ) ;
      (* The epoch is read-only: only the revoker changes it *)
      If (Eq #offset $(lineOffsetOf REVOKER_CONTROL_OFFSET)) Then (
        Let newKick : Bool <-
          FromBit Bool (TruncLsb (Xlen - 1) 1 ((##newWords) $[slotOf NumBytesXlen REVOKER_CONTROL_OFFSET])) ;
        Act (WriteReg revokerControlPath #newKick Retv) ;
        Retv
      ) ;
      (* Writing 1 to bit 0 of interruptStatus clears it *)
      If (Eq #offset $(lineOffsetOf REVOKER_INT_STATUS_OFFSET)) Then (
        Let clearStatus : Bool <-
          And [ (Var ty (Array LineBytes Bool) dataMask) $[byteOf REVOKER_INT_STATUS_OFFSET] ;
                FromBit Bool (TruncLsb (ByteSz - 1) 1
                  ((Var ty (Array LineBytes (Bit ByteSz)) data) $[byteOf REVOKER_INT_STATUS_OFFSET])) ] ;
        If #clearStatus Then (
          Act (WriteReg revokerInterruptStatusPath (ConstBool false) Retv) ;
          Retv
        ) ;
        Retv
      ) ;
      If (Eq #offset $(lineOffsetOf REVOKER_INT_REQUESTED_OFFSET)) Then (
        Let newReq : Bool <-
          FromBit Bool (TruncLsb (Xlen - 1) 1 ((##newWords) $[slotOf NumBytesXlen REVOKER_INT_REQUESTED_OFFSET])) ;
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
             (pfAligned : Is_true (base mod (2 ^ LgLineBytes) =? 0)%Z)
             : MemRegion := {|
    regionName        := "revoker" ;
    regionBase        := base ;
    regionSize        := RevokerSizeBytes ;
    regionKind        := @CustomMem "revoker" revokerChildren
                                    (@revokerLineReadAction base)
                                    (@revokerLineWriteAction base)
                                    (Some (fun ty => revokerLocalInterrupt)) ;
    regionSizeNonNeg  := I ;
    regionInMemory    := pfBound ;
    regionBaseAligned := pfAligned ;
    regionSizeAligned := I
  |}.

  Record RevokerInstance (regions : list MemRegion) := {
    revokerIdx      : nat ;
    revokerBaseAddr : Z ;
    pfBound         : Is_true ((0 <=? revokerBaseAddr) && (revokerBaseAddr + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
    pfAligned       : Is_true (revokerBaseAddr mod (2 ^ LgLineBytes) =? 0)%Z ;
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

    Local Abbreviation memTree := (specMemTree dom regions).

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

    Local Definition readRevokerSweepTop : Action ty memTree (Bit TagAddrWidth) :=
      revokerAction (ReadReg "sweepTop" revokerSweepTopPath (fun v => Return #v)).

    Local Definition writeRevokerSweepTop (v : ty (Bit TagAddrWidth)) : Action ty memTree (Bit 0) :=
      revokerAction (WriteReg revokerSweepTopPath #v Retv).

    Local Abbreviation readRevBit := (readRevBit config regions).

    Definition specRevokerStep : Action ty memTree (Bit 0) :=
      LetA epoch : Bit Xlen <- readRevokerEpoch ;
      Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;

      If #isOddEpoch Then (
        (* SWEEPING STATE: epoch is odd *)
        LetA scanAddrMsb : Bit TagAddrWidth <- readRevokerScanAddr ;
        LetA topAddrMsb  : Bit TagAddrWidth <- readRevokerSweepTop ;
        Let scanAddr     : Addr <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Let isDone       : Bool <- Uge #scanAddrMsb #topAddrMsb ;

        If (Not #isDone) Then (
          (* 1. Inspect capability at current scanAddr *)
          Let capSz      : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
          LetA ldFullCap : FullCapWithTag            <- specMemRead regions scanAddr capSz ;
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
          (* SWEEP COMPLETE: scanAddr reached the sweep's copy of top *)
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
          (* Start sweep: initialize scanAddr to base, take the sweep's copy of top and
           * advance epoch to odd *)
          LetA baseAddrMsb : Bit TagAddrWidth <- readRevokerBase ;
          Act (writeRevokerScanAddr baseAddrMsb) ;
          LetA topAddrMsb : Bit TagAddrWidth <- readRevokerTop ;
          Act (writeRevokerSweepTop topAddrMsb) ;
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
