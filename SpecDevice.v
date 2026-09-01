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

From Stdlib Require Import String List ZArith Zmod Bool Psatz.
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

Record MemRegion := {
  regionName   : string ;
  regionBase   : Z ;
  regionSize   : nat ;
  hasTags      : bool ;
  isReadOnly   : bool ;
  regionInit   : option (option (type (Array regionSize (Bit 8)))) ;
  isExternal   : option nat ; (* Some numDXlen: external memory with numDXlen * DXlenBytes width *)
  regionProof  : Is_true ((0 <=? regionBase) && (0 <? Z.of_nat regionSize) && (regionBase + Z.of_nat regionSize <=? Z.shiftl 1 Xlen))%Z
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
  (r.(regionSize) / Z.to_nat NumBytesFullCapSz)%nat.

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
      ReadArray capBytes (Const ty (Bit 3) (bits.of_Z 3 (Z.of_nat (finNum i))))
    else
      Const ty (Bit 8) Zmod.zero).

Lemma add_sub_cancel (A L : Z) : (L + (A - L))%Z = A.
Proof. lia. Qed.

(* ===========================================================================
 * 3. Converting a MemRegion into a Tree
 * =========================================================================== *)

Definition internalMemRegionTree (r : MemRegion) : Tree Elem :=
  Node "region" [
    Leaf "mainMem" (EMem {| memSize := r.(regionSize);
                            memKind := Bit 8;
                            memPort := 1;
                            memInit := r.(regionInit) |}) ;
    Leaf "tags" (EMem {| memSize := regionTagSize r;
                         memKind := Bool;
                         memPort := 1;
                         memInit := Some (Some (Build_SameTuple (tupleElems := List.repeat false (regionTagSize r))
                                            (Is_true_Nat_eq_implies (repeat_length _ _)))) |})
  ].

Definition externalMemRegionTree (r : MemRegion) (numDXlen : nat) : Tree Elem :=
  let numBytes := (numDXlen * DXlenBytes)%nat in
  Node "region" [
    Leaf "externalMemReadRq"  (ESend Addr) ;
    Leaf "externalMemReadRp"  (ERecv (Array numBytes (Bit 8))) ;
    Leaf "externalMemWriteRq" (ESend (ExternalMemWriteRq numBytes)) ;
    Leaf "externalTagReadRq"  (ESend (Bit TagAddrWidth)) ;
    Leaf "externalTagReadRp"  (ERecv (Array numDXlen Bool)) ;
    Leaf "externalTagWriteRq" (ESend (ExternalTagWriteRq numDXlen))
  ].

Definition memRegionTree (r : MemRegion) : Tree Elem :=
  match r.(isExternal) with
  | None => internalMemRegionTree r
  | Some numDXlen => externalMemRegionTree r numDXlen
  end.

(* ===========================================================================
 * 4. Generic Multi-Byte Read & Write for a MemRegion
 * =========================================================================== *)

Section InternalMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tInt := internalMemRegionTree r.

  Local Definition mainMemPath : MemPath tInt := getMemPathTree tInt "region.mainMem".
  Local Definition tagsPath : MemPath tInt := getMemPathTree tInt "region.tags".

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

Section ExternalMemRegionActions.
  Variable r : MemRegion.
  Variable numDXlen : nat.
  Variable ty : Kind -> Type.

  Local Definition tExt := externalMemRegionTree r numDXlen.
  Local Definition numBytes := (numDXlen * DXlenBytes)%nat.
  Local Definition LgNumDXlen := Z.log2_up (Z.of_nat numDXlen).
  Local Definition LgLineBytes := (3 + LgNumDXlen)%Z.

  Local Definition castAddr (addr : Expr ty Addr) : Expr ty (Bit ((LgLineBytes + (AddrSz - LgLineBytes))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz LgLineBytes)) addr.

  Local Definition lineOffset (addr : Expr ty Addr) : Expr ty (Bit LgLineBytes) :=
    TruncLsb (AddrSz - LgLineBytes)%Z LgLineBytes (castAddr addr).

  Local Definition lineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - LgLineBytes)%Z) :=
    TruncMsb (AddrSz - LgLineBytes)%Z LgLineBytes (castAddr addr).

  Local Definition lineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz LgLineBytes) {< lineIndex addr, Const ty (Bit LgLineBytes) Zmod.zero >}.

  Local Definition nextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz LgLineBytes) {< Add [ lineIndex addr ; Const ty (Bit (AddrSz - LgLineBytes)%Z) (Zmod.of_Z _ 1) ], Const ty (Bit LgLineBytes) Zmod.zero >}.

  Local Definition lineTagAddr (addr : Expr ty Addr) : Expr ty (Bit TagAddrWidth) :=
    TruncMsb TagAddrWidth LgNumBytesFullCapSz (lineAddr addr).

  Local Definition add1 (addr : Expr ty Addr) : Expr ty (Array numBytes Bool) :=
    FromBit (Array numBytes Bool)
      (Not (Sll (ConstBit (InvDefault _)) (lineOffset addr))).

  Definition externalMemRegionRead
             (addr : Expr ty Addr)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tExt FullCapWithTag :=
    Let numBytesActive : Bit (LgLineBytes + 1)%Z <-
                           Sll (Const ty (Bit (LgLineBytes + 1)%Z) (bits.of_Z _ 1))
                             (ZeroExtend (LgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
    Let endOffset : Bit (LgLineBytes + 1)%Z <-
      Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
    Let crosses : Bool <- FromBit Bool (TruncMsb 1 LgLineBytes #endOffset) ;
    Put "region.externalMemReadRq" in tExt <- lineAddr addr ;
    Get lineData1 <- "region.externalMemReadRp" in tExt ;
    LetIf lineDataMerged : Array numBytes (Bit 8) <-
      If #crosses Then (
        Put "region.externalMemReadRq" in tExt <- nextLineAddr addr ;
        Get lineData2 <- "region.externalMemReadRp" in tExt ;
        Return (ArrayBuilder (fun (i : FinType numBytes) =>
          ITE (ReadArrayConst (add1 addr) i)
              (ReadArrayConst #lineData2 i)
              (ReadArrayConst #lineData1 i)))
      ) Else (
        Return #lineData1
      ) ;
    Let rotData : Array numBytes (Bit 8) <- ArrayRotr 8 #lineDataMerged (lineOffset addr) ;
    Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      slice #rotData (Const ty (Bit 0) Zmod.zero) (Z.to_nat NumBytesFullCapSz) ;
    Let rawData : Bit FullCapSz <- ToBit #capBytes ;
    LetA rawTag : Bool <-
      if r.(hasTags) then (
        Put "region.externalTagReadRq" in tExt <- lineTagAddr addr ;
        Get lineTags1 <- "region.externalTagReadRp" in tExt ;
        Let isAligned : Bool <- Eq (lineOffset addr) (Const ty (Bit LgLineBytes) Zmod.zero) ;
        Let isCap : Bool <- Eq memSize $LgNumBytesFullCapSz ;
        Let tagSlot : Bit LgNumDXlen <- TruncMsb LgNumDXlen 3 (lineOffset addr) ;
        Return (And [ #isAligned ; #isCap ; ReadArray #lineTags1 #tagSlot ])
      ) else (
        Return (ConstBool false)
      ) ;
    Let res : FullCapWithTag <- STRUCT {
      "tag"  ::= #rawTag ;
      "cap"  ::= FromBit Cap (TruncMsb Xlen Xlen #rawData) ;
      "addr" ::= TruncLsb Xlen Xlen #rawData
    } ;
    Return #res.

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
      Let numBytesActive : Bit (LgLineBytes + 1)%Z <-
                             Sll (Const ty (Bit (LgLineBytes + 1)%Z) (bits.of_Z _ 1))
                               (ZeroExtend (LgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      Let endOffset : Bit (LgLineBytes + 1)%Z <-
        Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
      Let crosses : Bool <- FromBit Bool (TruncMsb 1 LgLineBytes #endOffset) ;
      Let isWrites : Array numBytes Bool <-
        FromBit (Array numBytes Bool)
          (rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (lineOffset addr)) ;
      Let mask1 : Array numBytes Bool <-
        ArrayBuilder (fun (i : FinType numBytes) =>
          And [ ReadArrayConst #isWrites i ; Not (ReadArrayConst (add1 addr) i) ]) ;
      Put "region.externalMemWriteRq" in tExt <- STRUCT {
        "addr" ::= lineAddr addr ;
        "data" ::= #rotData ;
        "mask" ::= #mask1
      } ;
      Act (
        if r.(hasTags) then (
          Let tagSlot : Bit LgNumDXlen <- TruncMsb LgNumDXlen 3 (lineOffset addr) ;
          Let tagMask1 : Array numDXlen Bool <-
            FromBit (Array numDXlen Bool)
              (Sll (ConstT (Bit (NatZ_mul numDXlen 1)) Zmod.one) #tagSlot) ;
          Let tagVal1 : Array numDXlen Bool <-
            FromBit (Array numDXlen Bool)
              (Sll (ITE0 (And [ #isCap ; stVal`"tag" ]) (ConstT (Bit (NatZ_mul numDXlen 1)) Zmod.one)) #tagSlot) ;
          Put "region.externalTagWriteRq" in tExt <- STRUCT {
            "addr" ::= lineTagAddr addr ;
            "tag"  ::= #tagVal1 ;
            "mask" ::= #tagMask1
          } ;
          Retv
        ) else (
          Retv
        )) ;
      If #crosses Then (
        Let mask2 : Array numBytes Bool <-
          ArrayBuilder (fun (i : FinType numBytes) =>
            And [ ReadArrayConst #isWrites i ; ReadArrayConst (add1 addr) i ]) ;
        Put "region.externalMemWriteRq" in tExt <- STRUCT {
          "addr" ::= nextLineAddr addr ;
          "data" ::= #rotData ;
          "mask" ::= #mask2
        } ;
        Retv
      ) ;
      Retv
    ).

End ExternalMemRegionActions.

Definition memRegionRead
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : Expr ty Addr)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (memRegionTree r) FullCapWithTag :=
  match r.(isExternal) as ext return Action ty (match ext with None => internalMemRegionTree r | Some n => externalMemRegionTree r n end) FullCapWithTag with
  | None => internalMemRegionRead r addr
  | Some numDXlen => externalMemRegionRead r numDXlen addr memSize
  end.

Definition memRegionWrite
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : Expr ty Addr)
           (stVal : Expr ty FullCapWithTag)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (memRegionTree r) (Bit 0) :=
  match r.(isExternal) as ext return Action ty (match ext with None => internalMemRegionTree r | Some n => externalMemRegionTree r n end) (Bit 0) with
  | None => internalMemRegionWrite r addr stVal memSize
  | Some numDXlen => externalMemRegionWrite r numDXlen addr stVal memSize
  end.

(* ===========================================================================
 * 5. Aggregated Spec Memory Tree & Router
 * =========================================================================== *)

Fixpoint specMemChildren (regions : list MemRegion) : list (Tree Elem) :=
  match regions with
  | [] => []
  | r :: rs => [ memRegionTree r ; Node "mem" (specMemChildren rs) ]
  end.

Definition specMemTree (regions : list MemRegion) : Tree Elem :=
  Node "mem" (specMemChildren regions).

Definition pairChild0Path {name : string} {c0 c1 : Tree Elem} : NodePath (Node name [c0; c1]) :=
  inr (inl (inl tt)).

Definition pairChild1Path {name : string} {c0 c1 : Tree Elem} : NodePath (Node name [c0; c1]) :=
  inr (inr (inl (inl tt))).

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
            liftAction pairChild0Path (memRegionRead r addr memSize)
          ) Else (
            Return ConstDef
          ) ;
        LetA restVal : FullCapWithTag <-
          liftAction pairChild1Path (specMemRead rs addr memSize) ;
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
          liftAction pairChild0Path (memRegionWrite r addr stVal memSize)
        ) ;
        liftAction pairChild1Path (specMemWrite rs addr stVal memSize)
    end.

End SpecMemRouter.
