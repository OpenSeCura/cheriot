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
 * 3. Converting a MemRegion into an EMem Tree
 * =========================================================================== *)

Definition memRegionTree (r : MemRegion) : Tree Elem :=
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

(* ===========================================================================
 * 4. Generic Multi-Byte Read & Write for a MemRegion
 * =========================================================================== *)

Section MemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition t := memRegionTree r.

  Local Definition mainMemPath : MemPath t := getMemPathTree t "region.mainMem".
  Local Definition tagsPath : MemPath t := getMemPathTree t "region.tags".

  Definition memRegionRead (addr : Expr ty Addr) : Action ty t FullCapWithTag :=
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

  Definition memRegionWrite
             (addr : Expr ty Addr)
             (stVal : Expr ty FullCapWithTag)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty t (Bit 0) :=
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

End MemRegionActions.

(* ===========================================================================
 * 5. SpecDevice Interface & Aggregator
 * =========================================================================== *)

Record SpecDevice (sysTree : Tree Elem) := {
  devRegion : MemRegion ;
  devRead   : forall {ty : Kind -> Type}, Expr ty Addr -> Action ty sysTree FullCapWithTag ;
  devWrite  : forall {ty : Kind -> Type}, Expr ty Addr -> Expr ty FullCapWithTag -> Expr ty (Bit LgLgNumBytesFullCapSz) -> Action ty sysTree (Bit 0)
}.

Section SpecRouter.
  Variable tree : Tree Elem.
  Variable ty : Kind -> Type.

  Fixpoint routeSpecRead
           (devs : list (SpecDevice tree))
           (addr : Expr ty Addr)
           : Action ty tree FullCapWithTag :=
    match devs with
    | [] => Return ConstDef
    | d :: ds =>
        Let isMatch : Bool <- isRegionAddr d.(devRegion) addr ;
        LetIf devVal : FullCapWithTag <-
          If #isMatch Then (
            d.(devRead) addr
          ) Else (
            Return ConstDef
          ) ;
        LetA restVal : FullCapWithTag <- routeSpecRead ds addr ;
        Return (Or [ #devVal ; #restVal ])
    end.

  Fixpoint routeSpecWrite
           (devs : list (SpecDevice tree))
           (addr : Expr ty Addr)
           (stVal : Expr ty FullCapWithTag)
           (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
           : Action ty tree (Bit 0) :=
    match devs with
    | [] => Retv
    | d :: ds =>
        Let isMatch : Bool <- isRegionAddr d.(devRegion) addr ;
        If #isMatch Then (
          d.(devWrite) addr stVal memSize
        ) ;
        routeSpecWrite ds addr stVal memSize
    end.

End SpecRouter.
