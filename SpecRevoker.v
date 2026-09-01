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
  [ "start" ; "endAddr" ; "epoch" ; "kick" ; "revokeAddr" ].

Definition revokerRegs : list (string * option (type (Bit (regBits 2)))) :=
  map (fun name => (name, Some (Zmod.zero : type (Bit (regBits 2))))) RevokerRegNames.

Definition RevokerNumRegs : nat := length revokerRegs.
Definition RevokerSizeBytes : nat := (RevokerNumRegs * Z.to_nat (Xlen / 8))%nat.

Definition revokerMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 Xlen))%Z)
           : MemRegion := {|
  regionName     := "revoker" ;
  regionBase     := base ;
  regionSize     := RevokerSizeBytes ;
  hasTags        := false ;
  isReadOnly     := false ;
  regionKind     := @RegisterMem RevokerSizeBytes false 2%nat revokerRegs I I ;
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
        | 0%nat => liftAction (@pairChild0Path "mem" (memRegionTree r) (specMemTree rs)) (act r)
        | S idx' =>
            liftAction (@pairChild1Path "mem" (memRegionTree r) (specMemTree rs))
                       (nthRegionAction idx' rs)
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
 * 3. Autonomous Revoker Step Action
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
    LetA revokerStart  : Bit Xlen <- readRevokerReg "start" ;
    LetA revokerEnd    : Bit Xlen <- readRevokerReg "endAddr" ;
    LetA revokerEpoch  : Bit Xlen <- readRevokerReg "epoch" ;
    LetA revokerKick   : Bit Xlen <- readRevokerReg "kick" ;
    LetA revokeAddr    : Bit Xlen <- readRevokerReg "revokeAddr" ;

    Let isWaiting : Bool <- Sge #revokeAddr #revokerEnd ;

    If (Not #isWaiting) Then (
      LetA ldFullCap : FullCapWithTag <- specMemRead regions #revokeAddr $LgNumBytesFullCapSz ;
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
            Let untaggedCap : FullCapWithTag <- STRUCT {
              "tag"  ::= Const ty Bool false ;
              "cap"  ::= #ldFullCap`"cap" ;
              "addr" ::= #ldFullCap`"addr"
            } ;
            Act (specMemWrite regions #revokeAddr #untaggedCap $LgNumBytesFullCapSz) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Act (writeRevokerReg "revokeAddr" (Add [ #revokeAddr ; Const ty (Bit Xlen) (bits.of_Z _ NumBytesFullCapSz) ])) ;
      Retv
    ) Else (
      Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #revokerEpoch) ;
      If #isOddEpoch Then (
        Act (writeRevokerReg "epoch" (Add [ #revokerEpoch ; Const ty (Bit Xlen) (bits.of_Z _ 1) ])) ;
        Retv
      ) Else (
        Let isKicked : Bool <- isNotZero #revokerKick ;
        If #isKicked Then (
          Act (writeRevokerReg "epoch" (Add [ #revokerEpoch ; Const ty (Bit Xlen) (bits.of_Z _ 1) ])) ;
          Act (writeRevokerReg "revokeAddr" #revokerStart) ;
          Act (writeRevokerReg "kick" (Const ty (Bit Xlen) Zmod.zero)) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End RevokerAction.
