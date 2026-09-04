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

Notation ByteSz := 8%Z.
Definition RevokerRegBytes : nat := Eval compute in Z.to_nat NumBytesXlen.
Definition LgRevokerRegBytes : nat := Eval compute in Z.to_nat LgNumBytesXlen.

Definition RevokerControlSignature : Z := 0x5500.
Definition RevokerControlSignatureWidth : Z := Eval compute in (Xlen / 2).

Definition RevokerNumRegs : nat := Eval compute in (length RevokerRegNames).
Definition RevokerSizeBytes : nat := Eval compute in (RevokerNumRegs * RevokerRegBytes)%nat.

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

Definition revokerLineConfig : LineConfig := RawLine LgRevokerRegBytes.

Definition revokerRegToWord {ty : Kind -> Type}
  (baseVal : Expr ty (Bit TagAddrWidth))
  (topVal : Expr ty (Bit TagAddrWidth))
  (kickVal : Expr ty Bool)
  (epochVal : Expr ty (Bit Xlen))
  (statusVal : Expr ty Bool)
  (reqVal : Expr ty Bool)
  (name : string) : Expr ty (Bit Xlen) :=
  if String.eqb name "base" then
    {< baseVal, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >}
  else if String.eqb name "top" then
    {< topVal, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >}
  else if String.eqb name "control" then
    {< Const ty (Bit RevokerControlSignatureWidth) (bits.of_Z RevokerControlSignatureWidth RevokerControlSignature),
       Const ty (Bit (RevokerControlSignatureWidth - 1)) Zmod.zero,
       ToBit kickVal >}
  else if String.eqb name "epoch" then
    epochVal
  else if String.eqb name "interruptStatus" then
    ZeroExtendTo Xlen (ToBit statusVal)
  else if String.eqb name "interruptRequested" then
    ZeroExtendTo Xlen (ToBit reqVal)
  else
    ConstDef.

Definition revokerWordsArray {ty : Kind -> Type}
  (baseVal : Expr ty (Bit TagAddrWidth))
  (topVal : Expr ty (Bit TagAddrWidth))
  (kickVal : Expr ty Bool)
  (epochVal : Expr ty (Bit Xlen))
  (statusVal : Expr ty Bool)
  (reqVal : Expr ty Bool) : Expr ty (Array RevokerNumRegs (Bit Xlen)) :=
  BuildArray (Build_SameTuple (n := RevokerNumRegs)
                (tupleElems := map (revokerRegToWord baseVal topVal kickVal epochVal statusVal reqVal) RevokerRegNames)
                I).

Definition readRevokerWord
           {ty : Kind -> Type}
           (arr : Expr ty (Array RevokerNumRegs (Bit Xlen)))
           (idx : nat)
           : Expr ty (Bit Xlen) :=
  readNatToFinType ConstDef (ReadArrayConst arr) idx.

Definition updateArraySliceMask
  {ty : Kind -> Type}
  {n : nat} {k : Kind} {m : Z} {sliceSz : nat}
  (arr : Expr ty (Array n k))
  (addr : Expr ty (Bit m))
  (upd : Expr ty (Array sliceSz k))
  (mask : Expr ty (Array sliceSz Bool)) : Expr ty (Array n k) :=
  fold_left (fun curArr (i : FinType sliceSz) =>
    let idx := Add [ addr ; Const ty (Bit m) (bits.of_Z m (Z.of_nat i.(finNum))) ] in
    let dMask := ReadArrayConst mask i in
    let dVal := ReadArrayConst upd i in
    let oVal := ReadArray curArr idx in
    UpdateArray curArr idx (ITE dMask dVal oVal)
  ) (genFinType sliceSz) arr.

Definition revokerLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty tRev (LineReadRp revokerLineConfig) :=
  Let offset <- getMemOffset base (Z.of_nat RevokerSizeBytes) addr ;
  ReadReg "base" revokerBasePath (fun baseVal =>
  ReadReg "top" revokerTopPath (fun topVal =>
  ReadReg "control" revokerControlPath (fun kickVal =>
  ReadReg "epoch" revokerEpochPath (fun epochVal =>
  ReadReg "interruptStatus" revokerInterruptStatusPath (fun statusVal =>
  ReadReg "interruptRequested" revokerInterruptRequestedPath (fun reqVal =>
  Let words : Array RevokerNumRegs (Bit Xlen) <-
    revokerWordsArray #baseVal #topVal #kickVal #epochVal #statusVal #reqVal ;
  Let bytes : Array RevokerSizeBytes (Bit ByteSz) <-
    FromBit (Array RevokerSizeBytes (Bit ByteSz)) (@ToBit ty (Array RevokerNumRegs (Bit Xlen)) #words) ;
  Let readBytes : Array RevokerRegBytes (Bit ByteSz) <-
    slice #bytes #offset RevokerRegBytes ;
  @Return ty tRev (LineReadRp revokerLineConfig) (STRUCT {
    "data" ::= #readBytes ;
    "tag"  ::= Const ty (Array (cfgNumLineTags revokerLineConfig) Bool) (getDefault _)
  }))))))).

Arguments revokerLineReadAction base ty addr : clear implicits.

Definition revokerLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq revokerLineConfig))
           : Action ty tRev (Bit 0) :=
  Let offset <- getMemOffset base (Z.of_nat RevokerSizeBytes) (rq`"addr") ;
  ReadReg "base" revokerBasePath (fun baseVal =>
  ReadReg "top" revokerTopPath (fun topVal =>
  ReadReg "control" revokerControlPath (fun kickVal =>
  ReadReg "epoch" revokerEpochPath (fun epochVal =>
  ReadReg "interruptStatus" revokerInterruptStatusPath (fun statusVal =>
  ReadReg "interruptRequested" revokerInterruptRequestedPath (fun reqVal =>
  Let oldWords : Array RevokerNumRegs (Bit Xlen) <-
    revokerWordsArray #baseVal #topVal #kickVal #epochVal (ConstBool false) #reqVal ;
  Let oldBytes : Array RevokerSizeBytes (Bit ByteSz) <-
    FromBit (Array RevokerSizeBytes (Bit ByteSz)) (@ToBit ty (Array RevokerNumRegs (Bit Xlen)) #oldWords) ;
  Let updatedBytes : Array RevokerSizeBytes (Bit ByteSz) <-
    updateArraySliceMask #oldBytes #offset (rq`"data") (rq`"dataMask") ;
  Let updatedWords : Array RevokerNumRegs (Bit Xlen) <-
    FromBit (Array RevokerNumRegs (Bit Xlen)) (@ToBit ty (Array RevokerSizeBytes (Bit ByteSz)) #updatedBytes) ;

  Let newBase : Bit TagAddrWidth <-
    TruncMsb TagAddrWidth LgNumBytesFullCapSz (readRevokerWord #updatedWords (revokerRegIdx "base")) ;
  WriteReg revokerBasePath #newBase (

  Let newTop : Bit TagAddrWidth <-
    TruncMsb TagAddrWidth LgNumBytesFullCapSz (readRevokerWord #updatedWords (revokerRegIdx "top")) ;
  WriteReg revokerTopPath #newTop (

  Let newKick : Bool <-
    FromBit Bool (TruncLsb (Xlen - 1) 1 (readRevokerWord #updatedWords (revokerRegIdx "control"))) ;
  WriteReg revokerControlPath #newKick (

  Let newEpoch : Bit Xlen <-
    readRevokerWord #updatedWords (revokerRegIdx "epoch") ;
  WriteReg revokerEpochPath #newEpoch (

  Let didClearStatus : Bool <-
    FromBit Bool (TruncLsb (Xlen - 1) 1 (readRevokerWord #updatedWords (revokerRegIdx "interruptStatus"))) ;
  WriteReg revokerInterruptStatusPath (ITE #didClearStatus (ConstBool false) #statusVal) (

  Let newReq : Bool <-
    FromBit Bool (TruncLsb (Xlen - 1) 1 (readRevokerWord #updatedWords (revokerRegIdx "interruptRequested"))) ;
  WriteReg revokerInterruptRequestedPath #newReq Retv))))))))))).

Arguments revokerLineWriteAction base ty rq : clear implicits.

Lemma revokerAlignedLemma (base : Z) (pf : Is_true (base mod NumBytesXlen =? 0)%Z) :
  Is_true (
    (base mod (2 ^ Z.of_nat (cfgLgLineBytes revokerLineConfig)) =? 0)%Z &&
    (RevokerSizeBytes mod (cfgLineBytes revokerLineConfig) =? 0)%nat
  ).
Proof.
  change (cfgLgLineBytes revokerLineConfig) with LgRevokerRegBytes.
  change (cfgLineBytes revokerLineConfig) with RevokerRegBytes.
  change (2 ^ Z.of_nat LgRevokerRegBytes)%Z with NumBytesXlen.
  change (RevokerSizeBytes mod RevokerRegBytes =? 0)%nat with true.
  rewrite Bool.andb_true_r.
  exact pf.
Qed.

Definition revokerMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 Xlen))%Z)
           (pfAligned : Is_true (base mod NumBytesXlen =? 0)%Z)
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

Arguments revokerMemRegion base pfBound pfAligned : clear implicits.

Record RevokerInstance (regions : list MemRegion) := {
  revokerIdx      : nat ;
  revokerBaseAddr : Z ;
  pfBound         : Is_true ((0 <=? revokerBaseAddr) && (revokerBaseAddr + Z.of_nat RevokerSizeBytes <=? Z.shiftl 1 Xlen))%Z ;
  pfAligned       : Is_true (revokerBaseAddr mod NumBytesXlen =? 0)%Z ;
  pfRevoker       : nth_error regions revokerIdx = Some (revokerMemRegion revokerBaseAddr pfBound pfAligned)
}.

Definition revokerRegion {regions} (rev : RevokerInstance regions) : MemRegion :=
  revokerMemRegion rev.(revokerBaseAddr) rev.(pfBound) rev.(pfAligned).

(* ===========================================================================
 * 2. Accessing Region at Index in Spec Memory Tree
 * =========================================================================== *)

Section NthRegionAction.
  Variable ty : Kind -> Type.

  Definition nthRegionActionExact
             (idx : nat)
             (regions : list MemRegion)
             : forall r0, nth_error regions idx = Some r0 ->
               forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k.
  Proof.
    revert idx.
    induction regions as [| r rs IH]; intros [| idx'] r0 pf k act; simpl in pf.
    - discriminate pf.
    - discriminate pf.
    - inversion pf; subst.
      exact (liftAction child0Path act).
    - exact (liftAction child1Path (IH idx' r0 pf k act)).
  Defined.

End NthRegionAction.

Arguments nthRegionActionExact {ty} idx regions r0 pf {k} act.

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
    nthRegionActionExact rev.(revokerIdx) regions (revokerRegion rev) rev.(pfRevoker) act.

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

  Definition readRevBit (base : Expr ty (Bit (AddrSz + 1))) : Action ty memTree Bool :=
    LetA lookup  : RevBitLookup   <- toAction memTree (computeRevBitAddr config base) ;
    LetA revCap  : FullCapWithTag <- specMemRead regions (#lookup`"revByteAddr") $0 ;
    Let  revByte : Bit ByteSz     <- TruncLsb (Xlen - ByteSz) ByteSz (#revCap`"addr") ;
    Let  revBit  : Bool           <- extractRevBit lookup #revByte ;
    Return #revBit.

  Definition specRevokerStep : Action ty memTree (Bit 0) :=
    LetA epoch : Bit Xlen <- readRevokerEpoch ;
    Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;

    If #isOddEpoch Then (
      (* SWEEPING STATE: epoch is odd *)
      LetA scanAddrMsb : Bit TagAddrWidth <- readRevokerScanAddr ;
      LetA topAddrMsb  : Bit TagAddrWidth <- readRevokerTop ;
      Let scanAddr     : Bit Xlen <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
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
        (* Advance scan pointer: increment scanAddrMsb *)
        Let nextScanAddrMsb : Bit TagAddrWidth <-
          Add [ #scanAddrMsb ; Const ty (Bit TagAddrWidth) (bits.of_Z _ 1) ] ;
        Act (writeRevokerScanAddr #nextScanAddrMsb) ;
        Retv
      ) Else (
        (* SWEEP COMPLETE: scanAddr reached top *)
        (* Transition epoch from odd (sweeping) to even (idle) *)
        Act (writeRevokerEpoch (Add [ #epoch ; Const ty (Bit Xlen) (bits.of_Z _ 1) ])) ;
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
