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
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. MemRegion Definition & Disjointness Checking
 * =========================================================================== *)

Definition regBits (lgRegBytes : nat) : Z :=
  NatZ_mul (Nat.pow 2 lgRegBytes) 8.

Inductive RegionKind (regionSize : nat) (hasTags : bool) :=
| InternalMem (init : option (option (type (Array regionSize (Bit 8)))))
| ExternalMem (numDXlen : nat)
| RegisterMem (lgRegBytes : nat)
              (regs : list (string * option (type (Bit (regBits lgRegBytes)))))
              (pfSize : Is_true (regionSize =? (length regs * Nat.pow 2 lgRegBytes))%nat)
              (pfRegAligned : Is_true (if hasTags then (Nat.pow 2 lgRegBytes mod DXlenBytes =? 0)%nat else true)).

Arguments InternalMem [regionSize hasTags] init.
Arguments ExternalMem [regionSize hasTags] numDXlen.
Arguments RegisterMem [regionSize hasTags] lgRegBytes regs pfSize pfRegAligned.

Record MemRegion := {
  regionName       : string ;
  regionBase       : Z ;
  regionSize       : nat ;
  hasTags          : bool ;
  isReadOnly       : bool ;
  regionKind       : RegionKind regionSize hasTags ;
  regionInMemory   : Is_true ((0 <=? regionBase) && (regionBase + Z.of_nat regionSize <=? Z.shiftl 1 Xlen))%Z ;
  regionAligned    : Is_true (if hasTags
                              then (regionBase mod Z.of_nat DXlenBytes =? 0)%Z && (regionSize mod DXlenBytes =? 0)%nat
                              else true)
}.

Definition disjointBool (r1 r2 : MemRegion) : bool :=
  (r1.(regionBase) + Z.of_nat r1.(regionSize) <=? r2.(regionBase))%Z ||
  (r2.(regionBase) + Z.of_nat r2.(regionSize) <=? r1.(regionBase))%Z.

Fixpoint pairwiseDisjoint (l : list MemRegion) : bool :=
  match l with
  | [] => true
  | r :: rs => forallb (disjointBool r) rs && pairwiseDisjoint rs
  end.

Definition isRegionAddr {ty : Kind -> Type} (r : MemRegion) (addr : Expr ty Addr) : Expr ty Bool :=
  And [ Sge addr $(r.(regionBase)) ; Slt addr $(r.(regionBase) + Z.of_nat r.(regionSize)) ].

Definition regionTagSize (r : MemRegion) : nat :=
  if r.(hasTags) then (r.(regionSize) / DXlenBytes)%nat else 0%nat.

(* ===========================================================================
 * 2. External Transaction Payloads
 * =========================================================================== *)

Definition ExternalMemWriteRq (numBytes : nat) := STRUCT_TYPE {
  "addr" :: Addr ;
  "data" :: Array numBytes (Bit 8) ;
  "mask" :: Array numBytes Bool
}.

Definition ExternalTagWriteRq (numDXlen : nat) := STRUCT_TYPE {
  "addr" :: Bit TagAddrWidth ;
  "tag"  :: Array numDXlen Bool ;
  "mask" :: Array numDXlen Bool
}.

Definition embedCapBytes {ty : Kind -> Type} (numBytes : nat)
  (capBytes : Expr ty (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)))
  : Expr ty (Array numBytes (Bit 8)) :=
  ArrayBuilder (fun (i : FinType numBytes) =>
    if (finNum i <? Z.to_nat NumBytesFullCapSz)%nat then
      ReadArray capBytes (Const ty (Bit LgNumBytesFullCapSz) (bits.of_Z LgNumBytesFullCapSz (Z.of_nat (finNum i))))
    else
      Const ty (Bit 8) Zmod.zero).

Lemma add_sub_cancel (A L : Z) : (L + (A - L))%Z = A.
Proof. lia. Qed.

(* ===========================================================================
 * 3. Converting a MemRegion into a Tree
 * =========================================================================== *)

Definition internalMemRegionChildren (r : MemRegion) (init : option (option (type (Array r.(regionSize) (Bit 8))))) : list (Tree Elem) :=
  [ Leaf "mainMem" (EMem {| memSize := r.(regionSize);
                            memKind := Bit 8;
                            memPort := 1;
                            memInit := init |}) ;
    Leaf "tags" (EMem {| memSize := regionTagSize r;
                         memKind := Bool;
                         memPort := 1;
                         memInit := Some (Some (Build_SameTuple (tupleElems := List.repeat false (regionTagSize r))
                                            (Is_true_Nat_eq_implies (repeat_length _ _)))) |})
  ].

Definition externalMemRegionChildren (r : MemRegion) (numDXlen : nat) : list (Tree Elem) :=
  let numBytes := (numDXlen * DXlenBytes)%nat in
  [ Leaf "externalMemReadRq"  (ESend Addr) ;
    Leaf "externalMemReadRp"  (ERecv (Array numBytes (Bit 8))) ;
    Leaf "externalMemWriteRq" (ESend (ExternalMemWriteRq numBytes)) ;
    Leaf "externalTagReadRq"  (ESend (Bit TagAddrWidth)) ;
    Leaf "externalTagReadRp"  (ERecv (Array numDXlen Bool)) ;
    Leaf "externalTagWriteRq" (ESend (ExternalTagWriteRq numDXlen))
  ].

Definition registerMemRegionChildren
           (r : MemRegion)
           (lgRegBytes : nat)
           (regs : list (string * option (type (Bit (regBits lgRegBytes)))))
           : list (Tree Elem) :=
  [ Node "regs" (
      map (fun '(name, initVal) =>
        Leaf name (EReg (Build_Reg (Bit (regBits lgRegBytes)) initVal))
      ) regs
    ) ;
    Leaf "tags" (EReg (Build_Reg (Array (regionTagSize r) Bool)
                                 (Some (Build_SameTuple (tupleElems := List.repeat false (regionTagSize r))
                                                        (Is_true_Nat_eq_implies (repeat_length _ _))))))
  ].

Arguments internalMemRegionChildren r init : clear implicits.
Arguments externalMemRegionChildren r numDXlen : clear implicits.
Arguments registerMemRegionChildren r lgRegBytes regs : clear implicits.

Definition internalMemRegionTree (r : MemRegion) (init : option (option (type (Array r.(regionSize) (Bit 8))))) : Tree Elem :=
  Node r.(regionName) (internalMemRegionChildren r init).

Definition externalMemRegionTree (r : MemRegion) (numDXlen : nat) : Tree Elem :=
  Node r.(regionName) (externalMemRegionChildren r numDXlen).

Definition registerMemRegionTree
           (r : MemRegion)
           (lgRegBytes : nat)
           (regs : list (string * option (type (Bit (regBits lgRegBytes)))))
           : Tree Elem :=
  Node r.(regionName) (registerMemRegionChildren r lgRegBytes regs).

Arguments internalMemRegionTree r init : clear implicits.
Arguments externalMemRegionTree r numDXlen : clear implicits.
Arguments registerMemRegionTree r lgRegBytes regs : clear implicits.

Definition memRegionTree (r : MemRegion) : Tree Elem :=
  match r.(regionKind) with
  | InternalMem init => internalMemRegionTree r init
  | ExternalMem numDXlen => externalMemRegionTree r numDXlen
  | RegisterMem lg regs _ _ => registerMemRegionTree r lg regs
  end.

(* ===========================================================================
 * 4. Generic Multi-Byte Read & Write for a MemRegion
 * =========================================================================== *)

Section InternalMemRegionActions.
  Variable r : MemRegion.
  Variable init : option (option (type (Array r.(regionSize) (Bit 8)))).
  Variable ty : Kind -> Type.

  Local Definition tInt := internalMemRegionTree r init.

  Local Definition mainMemPath : MemPath tInt := getChildMemPathTree tInt "mainMem".
  Local Definition tagsPath : MemPath tInt := getChildMemPathTree tInt "tags".

  Definition internalMemRegionRead (addr : Expr ty Addr) : Action ty tInt FullCapWithTag :=
    Let offset <- getMemOffset r.(regionBase) (Z.of_nat r.(regionSize)) addr ;
    Let tagAddr : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
    Let tagOffset <- getMemOffset (Z.shiftr r.(regionBase) LgNumBytesFullCapSz) (Z.of_nat (regionTagSize r)) #tagAddr ;
    LetA dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      sliceMem mainMemPath I (Z.to_nat NumBytesFullCapSz) #offset ;
    Let rawData : Bit FullCapSz <- ToBit #dataBytes ;
    LetA tagArr : Array 1 Bool <-
      if r.(hasTags) then
        sliceMem tagsPath I 1 #tagOffset
      else
        Return ConstDef ;
    Let rawTag : Bool <- ReadArrayConst #tagArr (@Build_FinType 1 0 I) ;
    Let res : FullCapWithTag <- STRUCT {
      "tag"  ::= #rawTag ;
      "cap"  ::= FromBit Cap (TruncMsb Xlen Xlen #rawData) ;
      "addr" ::= TruncLsb Xlen Xlen #rawData
    } ;
    Return #res.

  Definition internalMemRegionWrite
             (addr : Expr ty Addr)
             (stVal : Expr ty FullCapWithTag)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tInt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let offset <- getMemOffset r.(regionBase) (Z.of_nat r.(regionSize)) addr ;
      Let tagAddr : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
      Let tagOffset <- getMemOffset (Z.shiftr r.(regionBase) LgNumBytesFullCapSz) (Z.of_nat (regionTagSize r)) #tagAddr ;
      Let isCap : Bool <- Eq memSize $LgNumBytesFullCapSz ;
      Let rawData : Bit FullCapSz <-
        ITE #isCap
            {< ToBit (stVal`"cap"), stVal`"addr" >}
            (ZeroExtendTo FullCapSz (stVal`"addr")) ;
      Let num_bytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 memSize ;
      Let byteMask : Array (Z.to_nat NumBytesFullCapSz) Bool <- Not (invMask (Z.to_nat NumBytesFullCapSz) #num_bytes) ;
      Act (updSliceMem mainMemPath (Z.to_nat NumBytesFullCapSz) #offset (FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData) #byteMask) ;
      if r.(hasTags) then (
        WriteMem tagsPath #tagOffset (stVal`"tag") Retv
      ) else (
        Retv
      )
    ).

End InternalMemRegionActions.

Arguments internalMemRegionRead r init [ty] addr.
Arguments internalMemRegionWrite r init [ty] addr stVal memSize.

Section ExternalMemRegionActions.
  Variable r : MemRegion.
  Variable numDXlen : nat.
  Variable ty : Kind -> Type.

  Local Definition tExt := externalMemRegionTree r numDXlen.
  Local Definition numBytes := (numDXlen * DXlenBytes)%nat.
  Local Definition lgNumDXlen := Z.log2_up (Z.of_nat numDXlen).
  Local Definition lgLineBytes := (LgNumBytesFullCapSz + lgNumDXlen)%Z.

  Local Definition castAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytes + (AddrSz - lgLineBytes))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytes)) addr.

  Local Definition lineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytes) :=
    TruncLsb (AddrSz - lgLineBytes)%Z lgLineBytes (castAddr addr).

  Local Definition lineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgLineBytes)%Z) :=
    TruncMsb (AddrSz - lgLineBytes)%Z lgLineBytes (castAddr addr).

  Local Definition lineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytes) {< lineIndex addr, Const ty (Bit lgLineBytes) Zmod.zero >}.

  Local Definition nextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytes) {< Add [ lineIndex addr ; Const ty (Bit (AddrSz - lgLineBytes)%Z) (Zmod.of_Z _ 1) ], Const ty (Bit lgLineBytes) Zmod.zero >}.

  Local Definition lineTagAddr (addr : Expr ty Addr) : Expr ty (Bit TagAddrWidth) :=
    TruncMsb TagAddrWidth LgNumBytesFullCapSz (lineAddr addr).

  Local Definition add1 (addr : Expr ty Addr) : Expr ty (Array numBytes Bool) :=
    FromBit (Array numBytes Bool)
      (Not (Sll (ConstBit (InvDefault _)) (lineOffset addr))).

  Local Definition pMemReadRq : SendPath tExt := getChildSendPathTree tExt "externalMemReadRq".
  Local Definition pMemReadRp : RecvPath tExt := getChildRecvPathTree tExt "externalMemReadRp".
  Local Definition pMemWriteRq : SendPath tExt := getChildSendPathTree tExt "externalMemWriteRq".
  Local Definition pTagReadRq : SendPath tExt := getChildSendPathTree tExt "externalTagReadRq".
  Local Definition pTagReadRp : RecvPath tExt := getChildRecvPathTree tExt "externalTagReadRp".
  Local Definition pTagWriteRq : SendPath tExt := getChildSendPathTree tExt "externalTagWriteRq".

  Definition externalMemRegionRead
             (addr : Expr ty Addr)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tExt FullCapWithTag :=
    Let numBytesActive : Bit (lgLineBytes + 1)%Z <-
                           Sll (Const ty (Bit (lgLineBytes + 1)%Z) (bits.of_Z _ 1))
                             (ZeroExtend (lgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
    Let endOffset : Bit (lgLineBytes + 1)%Z <-
      Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
    Let crosses : Bool <- FromBit Bool (TruncMsb 1 lgLineBytes #endOffset) ;
    Send pMemReadRq (lineAddr addr) (
    Recv "lineData1" pMemReadRp (fun lineData1 =>
    LetIf lineDataMerged : Array numBytes (Bit 8) <-
      If #crosses Then (
        Send pMemReadRq (nextLineAddr addr) (
        Recv "lineData2" pMemReadRp (fun lineData2 =>
        Return (ArrayBuilder (fun (i : FinType numBytes) =>
          ITE (ReadArrayConst (add1 addr) i)
              (ReadArrayConst #lineData2 i)
              (ReadArrayConst #lineData1 i)))))
      ) Else (
        Return #lineData1
      ) ;
    Let rotData : Array numBytes (Bit 8) <- ArrayRotr 8 #lineDataMerged (lineOffset addr) ;
    Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      slice #rotData (Const ty (Bit 0) Zmod.zero) (Z.to_nat NumBytesFullCapSz) ;
    Let rawData : Bit FullCapSz <- ToBit #capBytes ;
    LetA rawTag : Bool <-
      if r.(hasTags) then (
        Send pTagReadRq (lineTagAddr addr) (
        Recv "lineTags1" pTagReadRp (fun lineTags1 =>
        Let isAligned : Bool <- Eq (lineOffset addr) (Const ty (Bit lgLineBytes) Zmod.zero) ;
        Let isCap : Bool <- Eq memSize $LgNumBytesFullCapSz ;
        Let tagSlot : Bit lgNumDXlen <- TruncMsb lgNumDXlen LgNumBytesFullCapSz (lineOffset addr) ;
        Return (And [ #isAligned ; #isCap ; ReadArray #lineTags1 #tagSlot ])))
      ) else (
        Return (ConstBool false)
      ) ;
    Let res : FullCapWithTag <- STRUCT {
      "tag"  ::= #rawTag ;
      "cap"  ::= FromBit Cap (TruncMsb Xlen Xlen #rawData) ;
      "addr" ::= TruncLsb Xlen Xlen #rawData
    } ;
    Return #res)).

  Definition externalMemRegionWrite
             (addr : Expr ty Addr)
             (stVal : Expr ty FullCapWithTag)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tExt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let isCap : Bool <- Eq memSize $LgNumBytesFullCapSz ;
      Let rawData : Bit FullCapSz <-
        ITE #isCap
            {< ToBit (stVal`"cap"), stVal`"addr" >}
            (ZeroExtendTo FullCapSz (stVal`"addr")) ;
      Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData ;
      Let baseData : Array numBytes (Bit 8) <- embedCapBytes numBytes #capBytes ;
      Let rotData : Array numBytes (Bit 8) <- ArrayRotl 8 #baseData (lineOffset addr) ;
      Let numBytesActive : Bit (lgLineBytes + 1)%Z <-
                             Sll (Const ty (Bit (lgLineBytes + 1)%Z) (bits.of_Z _ 1))
                               (ZeroExtend (lgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      Let endOffset : Bit (lgLineBytes + 1)%Z <-
        Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
      Let crosses : Bool <- FromBit Bool (TruncMsb 1 lgLineBytes #endOffset) ;
      Let isWrites : Array numBytes Bool <-
        FromBit (Array numBytes Bool)
          (rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (lineOffset addr)) ;
      Let mask1 : Array numBytes Bool <-
        ArrayBuilder (fun (i : FinType numBytes) =>
          And [ ReadArrayConst #isWrites i ; Not (ReadArrayConst (add1 addr) i) ]) ;
      Send pMemWriteRq (STRUCT {
        "addr" ::= lineAddr addr ;
        "data" ::= #rotData ;
        "mask" ::= #mask1
      }) (
      Act (
        if r.(hasTags) then (
          Let tagSlot : Bit lgNumDXlen <- TruncMsb lgNumDXlen LgNumBytesFullCapSz (lineOffset addr) ;
          Let tagMask1 : Array numDXlen Bool <-
            FromBit (Array numDXlen Bool)
              (Sll (ConstT (Bit (NatZ_mul numDXlen 1)) Zmod.one) #tagSlot) ;
          Let tagVal1 : Array numDXlen Bool <-
            FromBit (Array numDXlen Bool)
              (Sll (ITE0 (And [ #isCap ; stVal`"tag" ]) (ConstT (Bit (NatZ_mul numDXlen 1)) Zmod.one)) #tagSlot) ;
          Send pTagWriteRq (STRUCT {
            "addr" ::= lineTagAddr addr ;
            "tag"  ::= #tagVal1 ;
            "mask" ::= #tagMask1
          }) Retv
        ) else (
          Retv
        )) ;
      If #crosses Then (
        Let mask2 : Array numBytes Bool <-
          ArrayBuilder (fun (i : FinType numBytes) =>
            And [ ReadArrayConst #isWrites i ; ReadArrayConst (add1 addr) i ]) ;
        Send pMemWriteRq (STRUCT {
          "addr" ::= nextLineAddr addr ;
          "data" ::= #rotData ;
          "mask" ::= #mask2
        }) Retv
      ) ;
      Retv)
    ).

End ExternalMemRegionActions.

Arguments externalMemRegionRead r numDXlen [ty] addr memSize.
Arguments externalMemRegionWrite r numDXlen [ty] addr stVal memSize.

Section RegisterMemRegionActions.
  Variable r : MemRegion.
  Variable lgRegBytes : nat.
  Variable regs : list (string * option (type (Bit (regBits lgRegBytes)))).
  Variable ty : Kind -> Type.

  Local Definition tReg := registerMemRegionTree r lgRegBytes regs.
  Local Definition numRegBytes : nat := Nat.pow 2 lgRegBytes.
  Local Definition regBitsVal : Z := regBits lgRegBytes.
  Local Definition regPaths : list (RegOfKind (t:=tReg) (Bit regBitsVal)) :=
    getTreeRegsOfKind (Bit regBitsVal) tReg.

  Local Definition castToRegSum (e : Expr ty Addr) : Expr ty (Bit (Z.of_nat lgRegBytes + (AddrSz - Z.of_nat lgRegBytes))%Z) :=
    castBits (eq_sym (add_sub_cancel AddrSz (Z.of_nat lgRegBytes))) e.

  Local Definition castFromRegSum (e : Expr ty (Bit (Z.of_nat lgRegBytes + (AddrSz - Z.of_nat lgRegBytes))%Z)) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz (Z.of_nat lgRegBytes)) e.

  Local Definition byteOffset (offset : Expr ty Addr) : Expr ty (Bit (Z.of_nat lgRegBytes)) :=
    TruncLsb (AddrSz - Z.of_nat lgRegBytes) (Z.of_nat lgRegBytes) (castToRegSum offset).

  Local Definition regIdx (offset : Expr ty Addr) : Expr ty (Bit (AddrSz - Z.of_nat lgRegBytes)) :=
    TruncMsb (AddrSz - Z.of_nat lgRegBytes) (Z.of_nat lgRegBytes) (castToRegSum offset).

  Local Definition byteOffsetAddr (offset : Expr ty Addr) : Expr ty Addr :=
    castFromRegSum (ZeroExtend (AddrSz - Z.of_nat lgRegBytes)%Z (byteOffset offset)).

  Local Definition numBytesActive (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Expr ty Addr :=
    Sll (Const ty Addr (bits.of_Z _ 1)) (ZeroExtend (AddrSz - LgLgNumBytesFullCapSz)%Z memSize).

  Local Definition endOffset (offset : Expr ty Addr) (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Expr ty Addr :=
    Add [ byteOffsetAddr offset ; numBytesActive memSize ].

  Local Definition crosses (offset : Expr ty Addr) (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Expr ty Bool :=
    Sgt (endOffset offset memSize) $(Z.of_nat numRegBytes).

  Local Definition tagSlot (offset : Expr ty Addr) : Expr ty (Bit TagAddrWidth) :=
    TruncMsb TagAddrWidth LgNumBytesFullCapSz offset.

  Local Definition tagsRegPath : RegPath tReg := getChildRegPathTree tReg "tags".

  Definition registerMemRegionRead
             (addr : Expr ty Addr)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tReg FullCapWithTag :=
    Let offset : Addr <- Sub addr $(r.(regionBase)) ;
    Let isCross : Bool <- crosses #offset memSize ;
    LetA regVal1 : Bit regBitsVal <- readRegsList regPaths (regIdx #offset) ;
    LetIf regVal2 : Bit regBitsVal <-
      If #isCross Then (
        readRegsList regPaths (Add [ regIdx #offset ; Const ty (Bit (AddrSz - Z.of_nat lgRegBytes)%Z) (Zmod.of_Z _ 1) ])
      ) Else (
        Return (Const ty (Bit regBitsVal) Zmod.zero)
      ) ;
    Let bytes1 : Array numRegBytes (Bit 8) <- FromBit (Array numRegBytes (Bit 8)) #regVal1 ;
    Let bytes2 : Array numRegBytes (Bit 8) <- FromBit (Array numRegBytes (Bit 8)) #regVal2 ;
    Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      ArrayBuilder (fun (i : FinType (Z.to_nat NumBytesFullCapSz)) =>
        let srcByte :=
          Add [ byteOffsetAddr #offset ;
                Const ty Addr (bits.of_Z _ (Z.of_nat (finNum i))) ] in
        let inReg2 := Sge srcByte $(Z.of_nat numRegBytes) in
        let idxInReg :=
          TruncLsb (AddrSz - Z.of_nat lgRegBytes)%Z (Z.of_nat lgRegBytes) (castToRegSum srcByte) in
        ITE inReg2
            (ReadArray #bytes2 idxInReg)
            (ReadArray #bytes1 idxInReg)) ;
    LetA rawTag : Bool <-
      if r.(hasTags) then (
        ReadReg "allTags" tagsRegPath (fun allTags =>
        Return (ReadArray #allTags (tagSlot #offset)))
      ) else (
        Return (Const ty Bool false)
      ) ;
    Let res : FullCapWithTag <- STRUCT {
      "tag"  ::= #rawTag ;
      "cap"  ::= FromBit Cap (TruncMsb (FullCapSz - Xlen) Xlen (ToBit #capBytes)) ;
      "addr" ::= TruncLsb (FullCapSz - Xlen) Xlen (ToBit #capBytes)
    } ;
    Return #res.

  Definition registerMemRegionWrite
             (addr : Expr ty Addr)
             (stVal : Expr ty FullCapWithTag)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tReg (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let offset : Addr <- Sub addr $(r.(regionBase)) ;
      Let isCross : Bool <- crosses #offset memSize ;
      Let isCap : Bool <- Eq memSize $LgNumBytesFullCapSz ;
      Let rawData : Bit FullCapSz <-
        ITE #isCap
            {< ToBit (stVal`"cap"), stVal`"addr" >}
            (ZeroExtendTo FullCapSz (stVal`"addr")) ;
      Let writeBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData ;
      Let numActive : Addr <- numBytesActive memSize ;
      Let bOffset : Addr <- byteOffsetAddr #offset ;
      LetA oldVal1 : Bit regBitsVal <- readRegsList regPaths (regIdx #offset) ;
      Let oldBytes1 : Array numRegBytes (Bit 8) <- FromBit (Array numRegBytes (Bit 8)) #oldVal1 ;
      Let newBytes1 : Array numRegBytes (Bit 8) <-
        ArrayBuilder (fun (k : FinType numRegBytes) =>
          let kVal := Const ty Addr (bits.of_Z _ (Z.of_nat (finNum k))) in
          let active :=
            And [ Sge kVal #bOffset ;
                  Slt (Sub kVal #bOffset) #numActive ] in
          let srcIdx :=
            TruncLsb TagAddrWidth LgNumBytesFullCapSz (Sub kVal #bOffset) in
          ITE active (ReadArray #writeBytes srcIdx) (ReadArrayConst #oldBytes1 k)) ;
      Act (writeRegsList regPaths (regIdx #offset) (ToBit #newBytes1)) ;
      If #isCross Then (
        Let nextIdx : Bit (AddrSz - Z.of_nat lgRegBytes)%Z <-
          Add [ regIdx #offset ; Const ty (Bit (AddrSz - Z.of_nat lgRegBytes)%Z) (Zmod.of_Z _ 1) ] ;
        LetA oldVal2 : Bit regBitsVal <- readRegsList regPaths #nextIdx ;
        Let oldBytes2 : Array numRegBytes (Bit 8) <- FromBit (Array numRegBytes (Bit 8)) #oldVal2 ;
        Let newBytes2 : Array numRegBytes (Bit 8) <-
          ArrayBuilder (fun (k : FinType numRegBytes) =>
            let dist :=
              Sub $(Z.of_nat numRegBytes + Z.of_nat (finNum k)) #bOffset in
            let active := Slt dist #numActive in
            let srcIdx := TruncLsb TagAddrWidth LgNumBytesFullCapSz dist in
            ITE active (ReadArray #writeBytes srcIdx) (ReadArrayConst #oldBytes2 k)) ;
        writeRegsList regPaths #nextIdx (ToBit #newBytes2)
      ) ;
      if r.(hasTags) then (
        ReadReg "oldTags" tagsRegPath (fun oldTags =>
        Let newTags : Array (regionTagSize r) Bool <-
          ArrayBuilder (fun (s : FinType (regionTagSize r)) =>
            let sVal := Const ty (Bit TagAddrWidth) (bits.of_Z _ (Z.of_nat (finNum s))) in
            let isTargetSlot := Eq sVal (tagSlot #offset) in
            let isNextSlot :=
              And [ #isCross ;
                    Eq sVal (Add [ tagSlot #offset ;
                                   Const ty (Bit TagAddrWidth) (bits.of_Z _ 1) ]) ] in
            ITE isTargetSlot
                (ITE #isCap (stVal`"tag") (Const ty Bool false))
                (ITE isNextSlot
                     (Const ty Bool false)
                     (ReadArrayConst #oldTags s))) ;
        WriteReg tagsRegPath #newTags Retv)
      ) else (
        Retv
      )
    ).

End RegisterMemRegionActions.

Arguments registerMemRegionRead r lgRegBytes regs [ty] addr memSize.
Arguments registerMemRegionWrite r lgRegBytes regs [ty] addr stVal memSize.

Definition memRegionRead
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : Expr ty Addr)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (memRegionTree r) FullCapWithTag :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem init => internalMemRegionTree r init
                                              | ExternalMem numDXlen => externalMemRegionTree r numDXlen
                                              | RegisterMem lg regs _ _ => registerMemRegionTree r lg regs
                                              end) FullCapWithTag with
  | InternalMem init => internalMemRegionRead r init addr
  | ExternalMem numDXlen => externalMemRegionRead r numDXlen addr memSize
  | RegisterMem lg regs _ _ => registerMemRegionRead r lg regs addr memSize
  end.

Definition memRegionWrite
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : Expr ty Addr)
           (stVal : Expr ty FullCapWithTag)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (memRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem init => internalMemRegionTree r init
                                              | ExternalMem numDXlen => externalMemRegionTree r numDXlen
                                              | RegisterMem lg regs _ _ => registerMemRegionTree r lg regs
                                              end) (Bit 0) with
  | InternalMem init => internalMemRegionWrite r init addr stVal memSize
  | ExternalMem numDXlen => externalMemRegionWrite r numDXlen addr stVal memSize
  | RegisterMem lg regs _ _ => registerMemRegionWrite r lg regs addr stVal memSize
  end.

(* ===========================================================================
 * 5. Composite Memory Tree & System Routing
 * =========================================================================== *)

Fixpoint specMemChildren (regions : list MemRegion) : list (Tree Elem) :=
  match regions with
  | [] => []
  | r :: rs => [ memRegionTree r ; Node "mem" (specMemChildren rs) ]
  end.

Definition specMemTree (regions : list MemRegion) : Tree Elem :=
  Node "mem" (specMemChildren regions).

Definition child0Path {A : Type} {name : string} {c0 : Tree A} {cs : list (Tree A)}
  : NodePath (Node name (c0 :: cs)) :=
  inr (inl (inl tt)).

Definition child1Path {A : Type} {name : string} {c0 c1 : Tree A} {cs : list (Tree A)}
  : NodePath (Node name (c0 :: c1 :: cs)) :=
  inr (inr (inl (inl tt))).

Arguments child0Path {A name c0 cs}.
Arguments child1Path {A name c0 c1 cs}.

Section SpecMemRouter.
  Variable ty : Kind -> Type.

  Fixpoint specMemRead
           (regions : list MemRegion)
           (addr : Expr ty Addr)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (specMemTree regions) FullCapWithTag :=
    match regions return Action ty (specMemTree regions) FullCapWithTag with
    | [] => Return ConstDef
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r addr ;
        LetIf devVal : FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (memRegionRead r addr memSize)
          ) Else (
            Return ConstDef
          ) ;
        LetA restVal : FullCapWithTag <-
          liftAction child1Path (specMemRead rs addr memSize) ;
        Return (Or [ #devVal ; #restVal ])
    end.

  Fixpoint specMemWrite
           (regions : list MemRegion)
           (addr : Expr ty Addr)
           (stVal : Expr ty FullCapWithTag)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (specMemTree regions) (Bit 0) :=
    match regions return Action ty (specMemTree regions) (Bit 0) with
    | [] => Retv
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r addr ;
        If #isMatch Then (
          liftAction child0Path (memRegionWrite r addr stVal memSize)
        ) ;
        liftAction child1Path (specMemWrite rs addr stVal memSize)
    end.

End SpecMemRouter.
