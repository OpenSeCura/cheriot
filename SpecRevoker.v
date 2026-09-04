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

Definition revokerChildren : list (Tree Elem) :=
  map (fun '(name, initVal) =>
    Leaf name (EReg (Build_Reg (Bit Xlen) initVal))
  ) revokerRegs.

Definition revokerRegPaths : list (RegOfKind (t:=Node "revoker" revokerChildren) (Bit Xlen)) :=
  getTreeRegsOfKind (Bit Xlen) (Node "revoker" revokerChildren).

Definition revokerLineConfig : LineConfig := RawLine 2.

Definition revokerLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty (Node "revoker" revokerChildren) (LineReadRp revokerLineConfig) :=
  Let offset <- Sub addr $base ;
  Let regIdx : Bit (AddrSz - 2)%Z <- TruncMsb (AddrSz - 2)%Z 2%Z (castBits (eq_sym (add_sub_cancel AddrSz 2)) #offset) ;
  LetA regVal : Bit Xlen <- readRegsList revokerRegPaths #regIdx ;
  @Return ty (Node "revoker" revokerChildren) (LineReadRp revokerLineConfig) (STRUCT {
    "data" ::= FromBit (Array 4 (Bit 8)) #regVal ;
    "tag"  ::= Const ty (Array 0 Bool) (getDefault (Array 0 Bool))
  }).

Arguments revokerLineReadAction base ty addr : clear implicits.

Definition revokerLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq revokerLineConfig))
           : Action ty (Node "revoker" revokerChildren) (Bit 0) :=
  Let offset <- Sub (rq`"addr") $base ;
  Let regIdx : Bit (AddrSz - 2)%Z <- TruncMsb (AddrSz - 2)%Z 2%Z (castBits (eq_sym (add_sub_cancel AddrSz 2)) #offset) ;
  LetA oldVal : Bit Xlen <- readRegsList revokerRegPaths #regIdx ;
  Let oldBytes : Array 4 (Bit 8) <- FromBit (Array 4 (Bit 8)) #oldVal ;
  Let isW1C : Bool <- Eq #regIdx $4 ;
  Let newBytes : Array 4 (Bit 8) <-
    ArrayBuilder (fun (i : FinType 4) =>
      let dMask := ReadArrayConst (rq`"dataMask") i in
      let dByte := ReadArrayConst (rq`"data") i in
      let oByte := ReadArrayConst #oldBytes i in
      ITE #isW1C
          (And [ oByte ; Not (And [ ITE dMask (Const ty (Bit 8) (bits.of_Z 8 (-1))) (Const ty (Bit 8) Zmod.zero) ; dByte ]) ])
          (ITE dMask dByte oByte)) ;
  Act (writeRegsList revokerRegPaths #regIdx (ToBit #newBytes)) ;
  Retv.

Arguments revokerLineWriteAction base ty rq : clear implicits.

Lemma revokerAlignedLemma (base : Z) (pf : Is_true (base mod 4 =? 0)%Z) :
  Is_true (
    (base mod (2 ^ Z.of_nat (cfgLgLineBytes revokerLineConfig)) =? 0)%Z &&
    (RevokerSizeBytes mod (cfgLineBytes revokerLineConfig) =? 0)%nat
  ).
Proof.
  change (cfgLgLineBytes revokerLineConfig) with 2%nat.
  change (cfgLineBytes revokerLineConfig) with 4%nat.
  change (2 ^ Z.of_nat 2)%Z with 4%Z.
  change (RevokerSizeBytes mod 4 =? 0)%nat with true.
  rewrite Bool.andb_true_r.
  exact pf.
Qed.

Definition revokerMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 Xlen))%Z)
           (pfAligned : Is_true (base mod 4 =? 0)%Z)
           : MemRegion := {|
  regionName     := "revoker" ;
  regionBase     := base ;
  regionSize     := RevokerSizeBytes ;
  regionLineCfg  := revokerLineConfig ;
  isReadOnly     := false ;
  regionKind     := @CustomMem "revoker" RevokerSizeBytes revokerLineConfig revokerChildren (revokerLineReadAction base) (revokerLineWriteAction base) ;
  regionInMemory := pfBound ;
  regionAligned  := revokerAlignedLemma pfAligned
|}.

Record RevokerInstance (regions : list MemRegion) := {
  revokerIdx    : nat ;
  revokerRegion : MemRegion ;
  pfRevoker     : nth_error regions revokerIdx = Some revokerRegion
}.

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
  Variable rev : RevokerInstance regions.
  Variable config : RevConfig.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Local Definition readRevokerRegByIdx (regIdx : nat) : Action ty memTree (Bit Xlen) :=
    nthRegionAction
      (fun r =>
         let tR := memRegionTree r in
         let pths := getTreeRegsOfKind (Bit (regBits LgRevokerRegBytes)) tR in
         readRegsList pths (Const ty (Bit (AddrSz - Z.of_nat LgRevokerRegBytes)%Z) (bits.of_Z _ (Z.of_nat regIdx))))
      rev.(revokerIdx) regions.

  Local Definition writeRevokerRegByIdx (regIdx : nat) (val : Expr ty (Bit Xlen)) : Action ty memTree (Bit 0) :=
    nthRegionAction
      (fun r =>
         let tR := memRegionTree r in
         let pths := getTreeRegsOfKind (Bit (regBits LgRevokerRegBytes)) tR in
         writeRegsList pths (Const ty (Bit (AddrSz - Z.of_nat LgRevokerRegBytes)%Z) (bits.of_Z _ (Z.of_nat regIdx))) val)
      rev.(revokerIdx) regions.

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
        (* Advance scan pointer: increment scanAddrMsb and zero lower bits *)
        Let nextScanAddr : Bit Xlen <-
          {< Add [ #scanAddrMsb ; Const ty (Bit TagAddrWidth) (bits.of_Z _ 1) ],
             Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Act (writeRevokerReg "scanAddr" #nextScanAddr) ;
        Retv
      ) Else (
        (* SWEEP COMPLETE: scanAddr reached top *)
        (* Transition epoch from odd (sweeping) to even (idle) *)
        Act (writeRevokerReg "epoch" (Add [ #epoch ; Const ty (Bit Xlen) (bits.of_Z _ 1) ])) ;
        (* Record sweep completion in interruptStatus *)
        Act (writeRevokerReg "interruptStatus" (Const ty (Bit Xlen) (bits.of_Z _ 1))) ;
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
        Let baseAddrMsb : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #baseAddr ;
        Let initScanAddr : Bit Xlen <- {< #baseAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Act (writeRevokerReg "scanAddr" #initScanAddr) ;
        Let oddEpoch : Bit Xlen <-
          {< TruncMsb (Xlen - 1) 1 #epoch, Const ty (Bit 1) (bits.of_Z 1 1) >} ;
        Act (writeRevokerReg "epoch" #oddEpoch) ;
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
    LetA req    : Bit Xlen <- readRevokerReg "interruptRequested" ;
    Let isPending : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #status) ;
    Let isReq     : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #req) ;
    Return (And [ #isPending ; #isReq ]).

End RevokerAction.
