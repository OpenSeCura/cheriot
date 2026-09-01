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
  [ "base" ; "top" ; "control" ; "epoch" ; "interruptStatus" ; "interruptRequested" ; "scanAddr" ].

Definition LgRevokerRegBytes : nat := Eval compute in Z.to_nat LgNumBytesXlen.

Definition revokerRegInit (name : string) : type (Bit (regBits LgRevokerRegBytes)) :=
  if String.eqb name "control" then
    bits.of_Z (regBits LgRevokerRegBytes) (Z.shiftl 0x5500 16)
  else
    Zmod.zero.

Definition revokerRegs : list (string * option (type (Bit (regBits LgRevokerRegBytes)))) :=
  map (fun name => (name, Some (revokerRegInit name))) RevokerRegNames.

Definition RevokerNumRegs : nat := length revokerRegs.
Definition RevokerSizeBytes : nat := (RevokerNumRegs * Z.to_nat NumBytesXlen)%nat.

Definition revokerMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 Xlen))%Z)
           : MemRegion := {|
  regionName     := "revoker" ;
  regionBase     := base ;
  regionSize     := RevokerSizeBytes ;
  hasTags        := false ;
  isReadOnly     := false ;
  regionKind     := @RegisterMem RevokerSizeBytes false LgRevokerRegBytes revokerRegs I I ;
  regionInMemory := pfBound ;
  regionAligned  := I
|}.

(* ===========================================================================
 * 2. Accessing Region at Index in Spec Memory Tree
 * =========================================================================== *)

Section NthRegionAction.
  Variable ty : Kind -> Type.
  Variable k : Kind.
  Variable act : forall r : MemRegion, Action ty (memRegionTree r) k.

  Fixpoint nthRegionAction
           (idx : nat)
           (regions : list MemRegion)
           : Action ty (specMemTree regions) k :=
    match regions as l return Action ty (specMemTree l) k with
    | [] => Return ConstDef
    | r :: rs =>
        match idx with
        | 0%nat => liftAction child0Path (act r)
        | S idx' =>
            liftAction child1Path (nthRegionAction idx' rs)
        end
    end.

End NthRegionAction.

Definition getStrIndexOption (s : string) (ls : list string) : option nat :=
  (fix loop (l : list string) (idx : nat) : option nat :=
     match l with
     | [] => None
     | x :: xs => if String.eqb s x then Some idx else loop xs (S idx)
     end) ls 0%nat.

(* ===========================================================================
 * 3. Autonomous Revoker Step Action & Interrupt Query
 * =========================================================================== *)

Section RevokerAction.
  Variable regions : list MemRegion.
  Variable revokerIdx : nat.
  Variable config : RevConfig.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Local Definition readRevokerRegByIdx (regIdx : nat) : Action ty memTree (Bit Xlen) :=
    nthRegionAction
      (fun r =>
         let tR := memRegionTree r in
         let pths := getTreeRegsOfKind (Bit (regBits 2)) tR in
         readRegsList pths (Const ty (Bit (AddrSz - 2)%Z) (bits.of_Z _ (Z.of_nat regIdx))))
      revokerIdx regions.

  Local Definition writeRevokerRegByIdx (regIdx : nat) (val : Expr ty (Bit Xlen)) : Action ty memTree (Bit 0) :=
    nthRegionAction
      (fun r =>
         let tR := memRegionTree r in
         let pths := getTreeRegsOfKind (Bit (regBits 2)) tR in
         writeRegsList pths (Const ty (Bit (AddrSz - 2)%Z) (bits.of_Z _ (Z.of_nat regIdx))) val)
      revokerIdx regions.

  Local Definition readRevokerReg (regName : string) :=
    forceOption (option_map readRevokerRegByIdx
                            (getStrIndexOption regName RevokerRegNames)).

  Local Definition writeRevokerReg (regName : string) (val : Expr ty (Bit Xlen)) :=
    forceOption (option_map (fun idx => writeRevokerRegByIdx idx val)
                            (getStrIndexOption regName RevokerRegNames)).

  Definition readRevBit (base : Expr ty (Bit (AddrSz + 1))) : Action ty memTree Bool :=
    LetA lookup  : RevBitLookup   <- toAction memTree (computeRevBitAddr config base) ;
    LetA revCap  : FullCapWithTag <- specMemRead regions (#lookup`"revByteAddr") $0 ;
    Let  revByte : Bit 8          <- TruncLsb (Xlen - 8) 8 (#revCap`"addr") ;
    Let  revBit  : Bool           <- extractRevBit lookup #revByte ;
    Return #revBit.

  Definition specRevokerStep : Action ty memTree (Bit 0) :=
    LetA epoch : Bit Xlen <- readRevokerReg "epoch" ;
    Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;

    If #isOddEpoch Then (
      (* SWEEPING STATE: epoch is odd *)
      LetA scanAddrRaw : Bit Xlen <- readRevokerReg "scanAddr" ;
      LetA topAddrRaw  : Bit Xlen <- readRevokerReg "top" ;
      Let scanAddrMsb  : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #scanAddrRaw ;
      Let topAddrMsb   : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #topAddrRaw ;
      Let scanAddr     : Bit Xlen <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let topAddr      : Bit Xlen <- {< #topAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let isDone       : Bool     <- Sge #scanAddrMsb #topAddrMsb ;

      If (Not #isDone) Then (
        (* 1. Inspect capability at current scanAddr *)
        LetA ldFullCap : FullCapWithTag <- specMemRead regions #scanAddr $LgNumBytesFullCapSz ;
        If (#ldFullCap`"tag") Then (
          Let ldCap : Cap <- #ldFullCap`"cap" ;
          Let ldAddr : Addr <- #ldFullCap`"addr" ;
          LetA ldECap : ECap <- toAction memTree (DecodeCap ldCap ldAddr) ;
          Let isSealingCap : Bool <- Or [ (#ldECap`"perms")`"SE" ;
                                         (#ldECap`"perms")`"US" ;
                                         (#ldECap`"perms")`"U0" ] ;
          If (Not #isSealingCap) Then (
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
        (* Advance scan pointer by capability size (8 bytes) *)
        Act (writeRevokerReg "scanAddr" (Add [ #scanAddr ; Const ty (Bit Xlen) (bits.of_Z _ NumBytesFullCapSz) ])) ;
        Retv
      ) Else (
        (* SWEEP COMPLETE: scanAddr reached top *)
        (* Transition epoch from odd (sweeping) to even (idle) *)
        Act (writeRevokerReg "epoch" (Add [ #epoch ; Const ty (Bit Xlen) (bits.of_Z _ 1) ])) ;
        (* Assert interrupt if software requested it *)
        LetA intReq : Bit Xlen <- readRevokerReg "interruptRequested" ;
        Let isIntReq : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #intReq) ;
        If #isIntReq Then (
          Act (writeRevokerReg "interruptStatus" (Const ty (Bit Xlen) (bits.of_Z _ 1))) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) Else (
      (* IDLE STATE: epoch is even *)
      LetA control : Bit Xlen <- readRevokerReg "control" ;
      Let isKicked : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #control) ;
      If #isKicked Then (
        (* Start sweep: initialize scanAddr to base and advance epoch to odd *)
        LetA baseAddr : Bit Xlen <- readRevokerReg "base" ;
        Act (writeRevokerReg "scanAddr" #baseAddr) ;
        Act (writeRevokerReg "epoch" (Add [ #epoch ; Const ty (Bit Xlen) (bits.of_Z _ 1) ])) ;
        (* Clear kick bit in control, preserving upper signature bits *)
        Let clearedControl : Bit Xlen <-
          {< TruncMsb (Xlen - 1) 1 #control, Const ty (Bit 1) Zmod.zero >} ;
        Act (writeRevokerReg "control" #clearedControl) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  Definition revokerInterrupt : Action ty memTree Bool :=
    LetA status : Bit Xlen <- readRevokerReg "interruptStatus" ;
    Let isPending : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #status) ;
    Return #isPending.

End RevokerAction.
