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

Definition RevokerRegNames : list string :=
  [ "base" ; "top" ; "control" ; "epoch" ; "interruptStatus" ; "interruptRequested" ].

Definition getStrIndexOption (s : string) (ls : list string) : option nat :=
  (fix loop (l : list string) (idx : nat) : option nat :=
     match l with
     | [] => None
     | x :: xs => if String.eqb s x then Some idx else loop xs (S idx)
     end) ls 0%nat.

Definition revokerRegIdx (name : string) :=
  forceOption (getStrIndexOption name RevokerRegNames).

Local Notation ByteSz := 8%Z.

Definition RevokerControlSignature : Z := 0x5500.
Definition RevokerControlSignatureWidth : Z := Eval compute in (Xlen / 2).

Definition RevokerNumRegs : nat := Eval compute in (length RevokerRegNames).
Definition RevokerSizeBytes : nat := Eval compute in (RevokerNumRegs * Z.to_nat NumBytesXlen)%nat.

Definition revokerChildren : list (Tree Elem) :=
  [ Leaf "base" (EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero))) ;
    Leaf "top" (EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero))) ;
    Leaf "control" (EReg (Build_Reg Bool (Some false))) ;
    Leaf "epoch" (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Leaf "interruptStatus" (EReg (Build_Reg Bool (Some false))) ;
    Leaf "interruptRequested" (EReg (Build_Reg Bool (Some false))) ;
    Leaf "scanAddr" (EReg (Build_Reg (Bit TagAddrWidth) (Some Zmod.zero))) ].

Local Notation tRev := (Node "revoker" revokerChildren).

Definition revokerBasePath : RegPath tRev := getChildRegPathTree tRev "base".
Definition revokerTopPath : RegPath tRev := getChildRegPathTree tRev "top".
Definition revokerControlPath : RegPath tRev := getChildRegPathTree tRev "control".
Definition revokerEpochPath : RegPath tRev := getChildRegPathTree tRev "epoch".
Definition revokerInterruptStatusPath : RegPath tRev := getChildRegPathTree tRev "interruptStatus".
Definition revokerInterruptRequestedPath : RegPath tRev := getChildRegPathTree tRev "interruptRequested".
Definition revokerScanAddrPath : RegPath tRev := getChildRegPathTree tRev "scanAddr".

Definition RevokerLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

Definition RevokerRegIdxWidth : Z := Eval compute in (Z.log2_up (Z.of_nat RevokerNumRegs)).

Notation revokerRegIdxBit name :=
  ($(Z.of_nat (revokerRegIdx name))).

Definition revokerLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty tRev (LineReadRp RevokerLineConfig) :=
  Let offset <- getMemOffset base (Z.of_nat RevokerSizeBytes) addr ;
  Let regIdx : Bit RevokerRegIdxWidth <- TruncMsb RevokerRegIdxWidth LgNumBytesXlen #offset ;
  ReadReg "base" revokerBasePath (fun baseVal =>
  ReadReg "top" revokerTopPath (fun topVal =>
  ReadReg "control" revokerControlPath (fun kickVal =>
  ReadReg "epoch" revokerEpochPath (fun epochVal =>
  ReadReg "interruptStatus" revokerInterruptStatusPath (fun statusVal =>
  ReadReg "interruptRequested" revokerInterruptRequestedPath (fun reqVal =>
  Let readWord : Bit Xlen <-
    Or [ ITE0 (Eq #regIdx (revokerRegIdxBit "base")) {< #baseVal, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
         ITE0 (Eq #regIdx (revokerRegIdxBit "top")) {< #topVal, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
         ITE0 (Eq #regIdx (revokerRegIdxBit "control")) {< Const ty (Bit RevokerControlSignatureWidth) (bits.of_Z RevokerControlSignatureWidth RevokerControlSignature),
                                                           Const ty (Bit (RevokerControlSignatureWidth - 1)) Zmod.zero,
                                                           ToBit #kickVal >} ;
         ITE0 (Eq #regIdx (revokerRegIdxBit "epoch")) #epochVal ;
         ITE0 (Eq #regIdx (revokerRegIdxBit "interruptStatus")) (ZeroExtendTo Xlen (ToBit #statusVal)) ;
         ITE0 (Eq #regIdx (revokerRegIdxBit "interruptRequested")) (ZeroExtendTo Xlen (ToBit #reqVal)) ] ;
  Let readBytes : Array (Z.to_nat NumBytesXlen) (Bit ByteSz) <-
    FromBit (Array (Z.to_nat NumBytesXlen) (Bit ByteSz)) #readWord ;
  @Return ty tRev (LineReadRp RevokerLineConfig) (STRUCT {
    "data" ::= #readBytes ;
    "tag"  ::= Const ty (Array (cfgNumLineTags RevokerLineConfig) Bool) (getDefault _)
  }))))))).

Arguments revokerLineReadAction base ty addr : clear implicits.

Definition revokerLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq RevokerLineConfig))
           : Action ty tRev (Bit 0) :=
  Let offset <- getMemOffset base (Z.of_nat RevokerSizeBytes) (rq`"addr") ;
  Let regIdx : Bit RevokerRegIdxWidth <- TruncMsb RevokerRegIdxWidth LgNumBytesXlen #offset ;
  Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
  If (Eq #regIdx (revokerRegIdxBit "base")) Then (
    Let newBase : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #writeWord ;
    WriteReg revokerBasePath #newBase Retv
  ) ;
  If (Eq #regIdx (revokerRegIdxBit "top")) Then (
    Let newTop : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #writeWord ;
    WriteReg revokerTopPath #newTop Retv
  ) ;
  If (Eq #regIdx (revokerRegIdxBit "control")) Then (
    Let newKick : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #writeWord) ;
    WriteReg revokerControlPath #newKick Retv
  ) ;
  If (Eq #regIdx (revokerRegIdxBit "epoch")) Then (
    WriteReg revokerEpochPath #writeWord Retv
  ) ;
  If (Eq #regIdx (revokerRegIdxBit "interruptStatus")) Then (
    Let clearBit : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #writeWord) ;
    If #clearBit Then (
      WriteReg revokerInterruptStatusPath (ConstBool false) Retv
    ) ;
    Retv
  ) ;
  If (Eq #regIdx (revokerRegIdxBit "interruptRequested")) Then (
    Let newReq : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #writeWord) ;
    WriteReg revokerInterruptRequestedPath #newReq Retv
  ) ;
  Retv.

Arguments revokerLineWriteAction base ty rq : clear implicits.

Lemma revokerBaseAlignedLemma (base : Z) (pf : Is_true (base mod NumBytesXlen =? 0)%Z) :
  Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes RevokerLineConfig)) =? 0)%Z.
Proof.
  exact pf.
Qed.

Definition revokerMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (pfAligned : Is_true (base mod NumBytesXlen =? 0)%Z)
           : MemRegion := {|
  regionName        := "revoker" ;
  regionBase        := base ;
  regionSize        := RevokerSizeBytes ;
  regionLineCfg     := RevokerLineConfig ;
  isReadOnly        := false ;
  regionKind        := @CustomMem "revoker" RevokerSizeBytes RevokerLineConfig revokerChildren (revokerLineReadAction base) (revokerLineWriteAction base) ;
  regionInMemory    := pfBound ;
  regionBaseAligned := revokerBaseAlignedLemma pfAligned ;
  regionSizeAligned := I
|}.

Arguments revokerMemRegion base pfBound pfAligned : clear implicits.

Record RevokerInstance (regions : list MemRegion) := {
  revokerIdx      : nat ;
  revokerBaseAddr : Z ;
  pfBound         : Is_true ((0 <=? revokerBaseAddr) && (revokerBaseAddr + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  pfAligned       : Is_true (revokerBaseAddr mod NumBytesXlen =? 0)%Z ;
  pfRevoker       : nth_error regions revokerIdx = Some (revokerMemRegion revokerBaseAddr pfBound pfAligned)
}.

Definition revokerRegion {regions} (rev : RevokerInstance regions) : MemRegion :=
  revokerMemRegion rev.(revokerBaseAddr) rev.(pfBound) rev.(pfAligned).

(* ===========================================================================
 * 2. Accessing Region at Index in Spec Memory Tree
 * =========================================================================== *)

Definition none_neq_some {A} {x : A} (pf : None = Some x) : False :=
  match pf in (_ = y) return match y with Some _ => False | None => True end with
  | eq_refl => I
  end.

Section NthRegionAction.
  Variable ty : Kind -> Type.

  Fixpoint nthRegionAction
             (idx : nat)
             {struct idx}
             : forall (regions : list MemRegion) (r0 : MemRegion),
               nth_error regions idx = Some r0 ->
               forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k :=
    match idx with
    | 0%nat =>
        fun regions =>
          match regions return forall r0, nth_error regions 0 = Some r0 ->
                                forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k with
          | nil => fun r0 pf => False_rect _ (none_neq_some pf)
          | cons r rs => fun r0 pf k act =>
              let eq_r0_r : r0 = r :=
                match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end with
                | eq_refl => eq_refl
                end in
              liftAction child0Path
                (match eq_r0_r in (_ = y) return Action ty (memRegionTree y) k with
                 | eq_refl => act
                 end)
          end
    | S idx' =>
        fun regions =>
          match regions return forall r0, nth_error regions (S idx') = Some r0 ->
                                forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k with
          | nil => fun r0 pf => False_rect _ (none_neq_some pf)
          | cons r rs => fun r0 pf k act =>
              liftAction child1Path (@nthRegionAction idx' rs r0 pf k act)
          end
    end.

End NthRegionAction.

Arguments nthRegionAction {ty} idx regions r0 pf {k} act.

(* ===========================================================================
 * 3. Autonomous Revoker Step Action & Interrupt Query
 * =========================================================================== *)

Section RevokerAction.
  Variable regions : list MemRegion.
  Variable rev : RevokerInstance regions.
  Variable config : RevConfig.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Local Definition revokerAction {k : Kind} (act : Action ty tRev k) : Action ty memTree k :=
    nthRegionAction rev.(revokerIdx) regions (revokerRegion rev) rev.(pfRevoker) act.

  Local Definition readRevokerBase : Action ty memTree (Bit TagAddrWidth) :=
    revokerAction (ReadReg "base" revokerBasePath (fun v => Return #v)).

  Local Definition readRevokerTop : Action ty memTree (Bit TagAddrWidth) :=
    revokerAction (ReadReg "top" revokerTopPath (fun v => Return #v)).

  Local Definition readRevokerControl : Action ty memTree Bool :=
    revokerAction (ReadReg "control" revokerControlPath (fun v => Return #v)).

  Local Definition writeRevokerControl (v : Expr ty Bool) : Action ty memTree (Bit 0) :=
    revokerAction (WriteReg revokerControlPath v Retv).

  Local Definition readRevokerEpoch : Action ty memTree (Bit Xlen) :=
    revokerAction (ReadReg "epoch" revokerEpochPath (fun v => Return #v)).

  Local Definition writeRevokerEpoch (v : Expr ty (Bit Xlen)) : Action ty memTree (Bit 0) :=
    revokerAction (WriteReg revokerEpochPath v Retv).

  Local Definition readRevokerInterruptStatus : Action ty memTree Bool :=
    revokerAction (ReadReg "interruptStatus" revokerInterruptStatusPath (fun v => Return #v)).

  Local Definition writeRevokerInterruptStatus (v : Expr ty Bool) : Action ty memTree (Bit 0) :=
    revokerAction (WriteReg revokerInterruptStatusPath v Retv).

  Local Definition readRevokerInterruptRequested : Action ty memTree Bool :=
    revokerAction (ReadReg "interruptRequested" revokerInterruptRequestedPath (fun v => Return #v)).

  Local Definition writeRevokerInterruptRequested (v : Expr ty Bool) : Action ty memTree (Bit 0) :=
    revokerAction (WriteReg revokerInterruptRequestedPath v Retv).

  Local Definition readRevokerScanAddr : Action ty memTree (Bit TagAddrWidth) :=
    revokerAction (ReadReg "scanAddr" revokerScanAddrPath (fun v => Return #v)).

  Local Definition writeRevokerScanAddr (v : Expr ty (Bit TagAddrWidth)) : Action ty memTree (Bit 0) :=
    revokerAction (WriteReg revokerScanAddrPath v Retv).

  Local Notation readRevBit := (readRevBit config regions).

  Definition specRevokerStep : Action ty memTree (Bit 0) :=
    LetA epoch : Bit Xlen <- readRevokerEpoch ;
    Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;

    If #isOddEpoch Then (
      (* SWEEPING STATE: epoch is odd *)
      LetA scanAddrMsb : Bit TagAddrWidth <- readRevokerScanAddr ;
      LetA topAddrMsb  : Bit TagAddrWidth <- readRevokerTop ;
      Let scanAddr     : Addr <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let isDone       : Bool <- Sge #scanAddrMsb #topAddrMsb ;

      If (Not #isDone) Then (
        (* 1. Inspect capability at current scanAddr *)
        LetA ldFullCap : FullCapWithTag <- specMemRead regions #scanAddr $LgNumBytesFullCapSz ;
        If (#ldFullCap`"tag") Then (
          Let ldCap : Cap <- #ldFullCap`"cap" ;
          Let ldAddr : Addr <- #ldFullCap`"addr" ;
          LetA ldECap : ECap <- toAction memTree (DecodeCap ldCap ldAddr) ;
          Let isSealing : Bool <- isSealingCap ldECap ;
          If (Not #isSealing) Then (
            LetA revBit : Bool <- readRevBit (#ldECap`"base") ;
            If #revBit Then (
              (* Capability revoked: invalidate tag in memory *)
              Let untaggedCap : FullCapWithTag <- STRUCT {
                "tag"  ::= Const ty Bool false ;
                "cap"  ::= #ldFullCap`"cap" ;
                "addr" ::= #ldFullCap`"addr"
              } ;
              Act (specMemWrite regions #scanAddr #untaggedCap $LgNumBytesFullCapSz) ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        (* Advance scan pointer: increment scanAddrMsb *)
        Let nextScanAddrMsb : Bit TagAddrWidth <-
          Add [ #scanAddrMsb ; $1 ] ;
        Act (writeRevokerScanAddr #nextScanAddrMsb) ;
        Retv
      ) Else (
        (* SWEEP COMPLETE: scanAddr reached top *)
        (* Transition epoch from odd (sweeping) to even (idle) *)
        Act (writeRevokerEpoch (Add [ #epoch ; $1 ])) ;
        (* Record sweep completion in interruptStatus if software requested an interrupt *)
        LetA intReq : Bool <- readRevokerInterruptRequested ;
        If #intReq Then (
          Act (writeRevokerInterruptStatus (ConstBool true)) ;
          Act (writeRevokerInterruptRequested (ConstBool false)) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) Else (
      (* IDLE STATE: epoch is even *)
      LetA isKicked : Bool <- readRevokerControl ;
      If #isKicked Then (
        (* Start sweep: initialize scanAddr to base and advance epoch to odd *)
        LetA baseAddrMsb : Bit TagAddrWidth <- readRevokerBase ;
        Act (writeRevokerScanAddr #baseAddrMsb) ;
        Let oddEpoch : Bit Xlen <-
          {< TruncMsb (Xlen - 1) 1 #epoch, Const ty (Bit 1) (bits.of_Z 1 1) >} ;
        Act (writeRevokerEpoch #oddEpoch) ;
        (* Clear kick bit in control *)
        Act (writeRevokerControl (ConstBool false)) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  Definition revokerInterrupt : Action ty memTree Bool :=
    readRevokerInterruptStatus.

End RevokerAction.
