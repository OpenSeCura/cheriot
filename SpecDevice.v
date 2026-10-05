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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition SimulatorOnly.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * MemRegion Definition & Disjointness Checking
 * =========================================================================== *)

Record LineConfig := {
  cfgLgLineBytes : nat ;
  cfgHasTags     : bool ;
  cfgTaggedPf    : if cfgHasTags
                   then Is_true (Z.to_nat LgNumBytesFullCapSz <=? cfgLgLineBytes)%nat
                   else True
}.

Definition TaggedLine (lgLineBytes : nat) (pf : Is_true (Z.to_nat LgNumBytesFullCapSz <=? lgLineBytes)%nat) : LineConfig :=
  {| cfgLgLineBytes := lgLineBytes ; cfgHasTags := true ; cfgTaggedPf := pf |}.

Definition RawLine (lgLineBytes : nat) : LineConfig :=
  {| cfgLgLineBytes := lgLineBytes ; cfgHasTags := false ; cfgTaggedPf := I |}.

Definition cfgLineBytes (cfg : LineConfig) : nat :=
  Nat.pow 2 (cfgLgLineBytes cfg).

Definition cfgLgNumLineTags (isInternalMem : bool) (cfg : LineConfig) : nat :=
  if isInternalMem
  then Nat.max 1 (cfgLgLineBytes cfg - Z.to_nat LgNumBytesFullCapSz)
  else (cfgLgLineBytes cfg - Z.to_nat LgNumBytesFullCapSz)%nat.

Definition cfgNumLineTags (isInternalMem : bool) (cfg : LineConfig) : nat :=
  if cfgHasTags cfg
  then Nat.pow 2 (cfgLgNumLineTags isInternalMem cfg)
  else 0%nat.

Definition cfgLgTagRowBytes (isInternalMem : bool) (cfg : LineConfig) : nat :=
  (Z.to_nat LgNumBytesFullCapSz + cfgLgNumLineTags isInternalMem cfg)%nat.

Definition cfgTagRowBytes (isInternalMem : bool) (cfg : LineConfig) : nat :=
  Nat.pow 2 (cfgLgTagRowBytes isInternalMem cfg).

Definition cfgLgAlignBytes (isInternalMem : bool) (cfg : LineConfig) : nat :=
  if cfgHasTags cfg then cfgLgTagRowBytes isInternalMem cfg else cfgLgLineBytes cfg.

Definition cfgNumLines (regionSize : Z) (cfg : LineConfig) : nat :=
  Z.to_nat (regionSize / Z.of_nat (cfgLineBytes cfg)).

Definition cfgTagNumLines (isInternalMem : bool) (regionSize : Z) (cfg : LineConfig) : nat :=
  if cfgHasTags cfg then Z.to_nat (regionSize / Z.of_nat (cfgTagRowBytes isInternalMem cfg)) else 0%nat.

Definition cfgTagTotal (isInternalMem : bool) (regionSize : Z) (cfg : LineConfig) : nat :=
  (cfgTagNumLines isInternalMem regionSize cfg * cfgNumLineTags isInternalMem cfg)%nat.

Definition defaultTagsInit (regionSize : Z) (cfg : LineConfig)
  : option (option (type (Array (cfgTagTotal true regionSize cfg) Bool))) :=
  Some (Some (getDefault _)).

Fixpoint takeChunk {A} (k : nat) (def : A) (ls : list A) : list A :=
  match k with
  | 0%nat => []
  | S k' =>
      match ls with
      | [] => def :: takeChunk k' def []
      | x :: xs => x :: takeChunk k' def xs
      end
  end.

Lemma takeChunk_length {A} (k : nat) (def : A) (ls : list A) :
  List.length (takeChunk k def ls) = k.
Proof.
  revert ls; induction k as [| k' IH]; intros ls; simpl; auto.
  destruct ls; simpl; f_equal; apply IH.
Qed.

Definition bytesToMemInit (regionSize : Z) (bytes : list (bits 8))
  : option (option (type (Array (Z.to_nat regionSize) (Bit 8)))) :=
  let sz := Z.to_nat regionSize in
  Some (Some (Build_SameTuple (tupleElems := takeChunk sz Zmod.zero bytes)
                              (transparent_Is_true _ (Is_true_Nat_eq_implies (takeChunk_length sz Zmod.zero bytes))))).

Fixpoint strideStep {A} (stride : nat) (def : A) (n : nat) (ls : list A) : list A :=
  match n with
  | 0%nat => []
  | S n' =>
      match ls with
      | [] => def :: strideStep stride def n' []
      | x :: _ => x :: strideStep stride def n' (skipn stride ls)
      end
  end.

Lemma strideStep_length {A} (stride : nat) (def : A) (n : nat) (ls : list A) :
  List.length (strideStep stride def n ls) = n.
Proof.
  revert ls; induction n as [| n' IH]; intros ls; simpl; auto.
  destruct ls; simpl; f_equal; apply IH.
Qed.

Definition buildStrideTuple {A} (stride : nat) (def : A) (n b : nat) (ls : list A)
  : SameTuple A n :=
  Build_SameTuple (tupleElems := strideStep stride def n (skipn b ls))
                  (transparent_Is_true _ (Is_true_Nat_eq_implies (strideStep_length stride def n (skipn b ls)))).

Notation LineReadRp isInternalMem cfg := (STRUCT_TYPE {
  "data" :: Array (cfgLineBytes cfg) (Bit 8) ;
  "tag"  :: Array (cfgNumLineTags isInternalMem cfg) Bool
}).

Notation LineWriteRq isInternalMem cfg := (STRUCT_TYPE {
  "addr"     :: Addr ;
  "data"     :: Array (cfgLineBytes cfg) (Bit 8) ;
  "dataMask" :: Array (cfgLineBytes cfg) Bool ;
  "tag"      :: Array (cfgNumLineTags isInternalMem cfg) Bool ;
  "tagMask"  :: Array (cfgNumLineTags isInternalMem cfg) Bool
}).

Definition ReadPortSel (hasExtraFetchPort : bool) : Type :=
  if hasExtraFetchPort then bool else unit.

Definition selectReadPortSel (hasExtraFetchPort : bool) (isFetch : bool) : ReadPortSel hasExtraFetchPort :=
  match hasExtraFetchPort as b return ReadPortSel b with
  | true  => isFetch
  | false => tt
  end.

Inductive RegionKind (regionName : string) (regionSize : Z) (cfg : LineConfig) (hasExtraFetchPort : bool) :=
| InternalMem (isAccessible : bool)
              (initData : option (option (type (Array (Z.to_nat regionSize) (Bit 8)))))
              (initTags : option (option (type (Array (cfgTagTotal true regionSize cfg) Bool))))
| ExternalMem
| CustomMem (children : list (Tree DomainElem))
            (readAction : forall ty, ReadPortSel hasExtraFetchPort -> ty Addr ->
                          Action ty (Node regionName children) (LineReadRp false cfg))
            (writeAction : forall ty, ty (LineWriteRq false cfg) ->
                           Action ty (Node regionName children) (Bit 0))
            (irqAction : option (forall ty, Action ty (Node regionName children) Bool)).

Arguments InternalMem {regionName regionSize cfg hasExtraFetchPort} isAccessible initData initTags.
Arguments ExternalMem {regionName regionSize cfg hasExtraFetchPort}.
Arguments CustomMem {regionName regionSize cfg hasExtraFetchPort} children readAction writeAction irqAction.

Definition isInternalRegionKind {regionName regionSize cfg hasExtraFetchPort}
  (k : RegionKind regionName regionSize cfg hasExtraFetchPort) : bool :=
  match k with
  | InternalMem _ _ _ => true
  | _ => false
  end.

Record MemRegion := {
  regionName        : string ;
  regionDom         : string ;
  regionBase        : Z ;
  regionSize        : Z ;
  regionLineCfg     : LineConfig ;
  isReadOnly        : bool ;
  hasExtraFetchPort : bool ;
  regionKind        : RegionKind regionName regionSize regionLineCfg hasExtraFetchPort ;
  regionInMemory    : Is_true ((0 <=? regionBase) && (regionBase + regionSize <=? Z.shiftl 1 AddrSz))%Z ;
  regionBaseAligned : Is_true (regionBase mod (2 ^ Z.of_nat (cfgLgAlignBytes (isInternalRegionKind regionKind) regionLineCfg)) =? 0)%Z ;
  regionSizeAligned : Is_true (regionSize mod (2 ^ Z.of_nat (cfgLgAlignBytes (isInternalRegionKind regionKind) regionLineCfg)) =? 0)%Z
}.

Definition regionNumReadPorts (r : MemRegion) : nat :=
  if r.(hasExtraFetchPort) then 2%nat else 1%nat.

Definition selectReadPort (r : MemRegion) (isFetch : bool) : FinType (regionNumReadPorts r) :=
  match r.(hasExtraFetchPort) as b return FinType (if b then 2%nat else 1%nat) with
  | true => if isFetch then @Build_FinType 2%nat 1%nat I else @Build_FinType 2%nat 0%nat I
  | false => @Build_FinType 1%nat 0%nat I
  end.

Definition isInternalMem (r : MemRegion) : bool :=
  isInternalRegionKind r.(regionKind).

Definition hasTags (r : MemRegion) : bool :=
  cfgHasTags r.(regionLineCfg).

Definition lgLineBytes (r : MemRegion) : nat :=
  cfgLgLineBytes r.(regionLineCfg).

Definition lineBytes (r : MemRegion) : nat :=
  cfgLineBytes r.(regionLineCfg).

Definition numLineTags (isInternal : bool) (r : MemRegion) : nat :=
  cfgNumLineTags isInternal r.(regionLineCfg).

Definition disjointBool (r1 r2 : MemRegion) : bool :=
  (r1.(regionBase) + r1.(regionSize) <=? r2.(regionBase))%Z ||
  (r2.(regionBase) + r2.(regionSize) <=? r1.(regionBase))%Z.

Fixpoint pairwiseDisjoint (l : list MemRegion) : bool :=
  match l with
  | [] => true
  | r :: rs => forallb (disjointBool r) rs && pairwiseDisjoint rs
  end.

Definition isRegionAddr {ty : Kind -> Type} (r : MemRegion) (addr : Expr ty Addr) : Expr ty Bool :=
  And [ Uge addr $(r.(regionBase)) ; Ult addr $(r.(regionBase) + r.(regionSize)) ].

Definition regionNumLines (r : MemRegion) : nat :=
  cfgNumLines r.(regionSize) r.(regionLineCfg).

Definition regionTagSize (isInternal : bool) (r : MemRegion) : nat :=
  cfgTagNumLines isInternal r.(regionSize) r.(regionLineCfg).

(* ===========================================================================
 * Payload Utilities
 * =========================================================================== *)

Definition embedCapBytes {ty : Kind -> Type} (numBytes : nat)
  (capBytes : Expr ty (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)))
  : Expr ty (Array numBytes (Bit 8)) :=
  ArrayBuilder (fun (i : FinType numBytes) =>
    readNatToFinType (Const ty (Bit 8) Zmod.zero)
                     (ReadArrayConst capBytes)
                     (finNum i)).

Lemma add_sub_cancel (a l : Z) : (l + (a - l))%Z = a.
Proof. lia. Qed.

Definition memLgLineBytesZ (r : MemRegion) : Z :=
  Z.of_nat (lgLineBytes r).

Definition memLgNumLineTagsZ (isInternal : bool) (r : MemRegion) : Z :=
  Z.of_nat (cfgLgNumLineTags isInternal r.(regionLineCfg)).

Definition memLgTagRowBytesZ (isInternal : bool) (r : MemRegion) : Z :=
  (LgNumBytesFullCapSz + memLgNumLineTagsZ isInternal r)%Z.

Section MemAddrHelpers.
  Variable isInternal : bool.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Let lBytes := lineBytes r.
  Let nTags := numLineTags isInternal r.
  Let numLines := regionNumLines r.
  Let numTagLines := regionTagSize isInternal r.
  Let lgLineBytesZ := memLgLineBytesZ r.
  Let lgNumLineTagsZ := memLgNumLineTagsZ isInternal r.
  Let lgTagRowBytesZ := memLgTagRowBytesZ isInternal r.

  Definition memCastAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

  Definition memLineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgLineBytesZ)%Z) :=
    TruncMsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (memCastAddr addr).

  Definition memLineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytesZ) :=
    TruncLsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (memCastAddr addr).

  Definition memLineOffsetIdx (addr : Expr ty Addr) : Expr ty (Bit (Z.log2_up (Z.of_nat numLines))) :=
    getMemOffset (Z.shiftr r.(regionBase) lgLineBytesZ) (Z.of_nat numLines) (memLineIndex addr).

  Definition memLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< memLineIndex addr, Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Definition memNextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    Add [ memLineAddr addr ; $(Z.of_nat lBytes) ].

  Definition memAdd1 (addr : Expr ty Addr) : Expr ty (Array lBytes Bool) :=
    FromBit (Array lBytes Bool)
      (Not (Sll (ConstBit (InvDefault _)) (memLineOffset addr))).

  Definition memCastAddrForTag (addr : Expr ty Addr) : Expr ty (Bit ((lgTagRowBytesZ + (AddrSz - lgTagRowBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgTagRowBytesZ)) addr.

  Definition memTagLineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgTagRowBytesZ)%Z) :=
    TruncMsb (AddrSz - lgTagRowBytesZ)%Z lgTagRowBytesZ (memCastAddrForTag addr).

  Definition memTagRowOffset (addr : Expr ty Addr) : Expr ty (Bit lgTagRowBytesZ) :=
    TruncLsb (AddrSz - lgTagRowBytesZ)%Z lgTagRowBytesZ (memCastAddrForTag addr).

  Definition memTagLineOffsetIdx (addr : Expr ty Addr) : Expr ty (Bit (Z.log2_up (Z.of_nat numTagLines))) :=
    getMemOffset (Z.shiftr r.(regionBase) lgTagRowBytesZ) (Z.of_nat numTagLines) (memTagLineIndex addr).

  Definition memTagSlot (addr : Expr ty Addr) : Expr ty (Bit lgNumLineTagsZ) :=
    TruncMsb lgNumLineTagsZ LgNumBytesFullCapSz (memTagRowOffset addr).

  Definition memAdd1Tag (addr : Expr ty Addr) : Expr ty (Array nTags Bool) :=
    FromBit (Array nTags Bool)
      (Not (Sll (ConstBit (InvDefault _)) (memTagSlot addr))).

  Definition memTagMasks
    (addr : Expr ty Addr)
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : Expr ty (Array nTags Bool) * Expr ty (Array nTags Bool) :=
    if hasTags r then
      let capOffset := TruncLsb TagAddrWidth LgNumBytesFullCapSz addr in
      let wTagCnt := (lgNumLineTagsZ + 2)%Z in
      let numBytesActiveTag : Expr ty (Bit (LgNumBytesFullCapSz + wTagCnt)%Z) :=
        Sll $1 (ZeroExtend (LgNumBytesFullCapSz + wTagCnt - LgLgNumBytesFullCapSz)%Z memSize) in
      let endByteOffset : Expr ty (Bit (LgNumBytesFullCapSz + wTagCnt)%Z) :=
        Sub (Add [ ZeroExtend wTagCnt capOffset ; numBytesActiveTag ]) $1 in
      let numTagsActive : Expr ty (Bit wTagCnt) :=
        Add [ TruncMsb wTagCnt LgNumBytesFullCapSz endByteOffset ; $1 ] in
      let w := kindSize (Array nTags Bool) in
      let baseMask : Expr ty (Bit (w + w)%Z) :=
        Not (Sll (ConstBit (InvDefault (Bit (w + w)%Z))) numTagsActive) in
      let shiftedMask : Expr ty (Bit (w + w)%Z) := Sll baseMask (memTagSlot addr) in
      (FromBit (Array nTags Bool) (TruncLsb w w shiftedMask),
       FromBit (Array nTags Bool) (TruncMsb w w shiftedMask))
    else
      (ConstDef, ConstDef).

  Definition memMergeLineReadRp
    (addr : Expr ty Addr)
    (rp0 rp1 : Expr ty (LineReadRp isInternal r.(regionLineCfg)))
    : Expr ty (LineReadRp isInternal r.(regionLineCfg)) :=
    let add1    := memAdd1 addr in
    let add1Tag := memAdd1Tag addr in
    STRUCT {
      "data" ::= ArrayBuilder (fun i =>
                   ITE (ReadArrayConst add1 i)
                       (ReadArrayConst (rp1`"data") i)
                       (ReadArrayConst (rp0`"data") i)) ;
      "tag"  ::= ArrayBuilder (fun t =>
                   ITE (ReadArrayConst add1Tag t)
                       (ReadArrayConst (rp1`"tag") t)
                       (ReadArrayConst (rp0`"tag") t))
    }.

  Definition memExtractReadCap
    (addr : Expr ty Addr)
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    (rp : Expr ty (LineReadRp isInternal r.(regionLineCfg)))
    : Expr ty FullCapWithTag :=
    let capOffset := TruncLsb TagAddrWidth LgNumBytesFullCapSz addr in
    let isCapAligned := isZero capOffset in
    let isCap := And [ Eq memSize $LgNumBytesFullCapSz ; isCapAligned ] in
    let rotData := ArrayRotr (rp`"data") (memLineOffset addr) in
    let dataBytes := slice rotData (Const ty (Bit lgLineBytesZ) Zmod.zero) (Z.to_nat NumBytesFullCapSz) in
    let rawData := ToBit dataBytes in
    let rawTag :=
      if hasTags r then
        ReadArray (rp`"tag") (memTagSlot addr)
      else
        ConstBool false in
    STRUCT {
      "tag"  ::= And [ isCap ; rawTag ] ;
      "cap"  ::= FromBit Cap (TruncMsb CapSz AddrSz rawData) ;
      "addr" ::= TruncLsb CapSz AddrSz rawData
    }.

  Definition memBuildLineWriteRq
    (addr : Expr ty Addr)
    (stVal : Expr ty FullCapWithTag)
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : Expr ty (LineWriteRq isInternal r.(regionLineCfg)) :=
    let capOffset := TruncLsb TagAddrWidth LgNumBytesFullCapSz addr in
    let isCapAligned := isZero capOffset in
    let isCap := And [ Eq memSize $LgNumBytesFullCapSz ; isCapAligned ] in
    let rawData :=
      ITE isCap
          {< ToBit (stVal`"cap"), stVal`"addr" >}
          (ZeroExtendTo FullCapSz (stVal`"addr")) in
    let capBytes := FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) rawData in
    let baseData := embedCapBytes lBytes capBytes in
    let rotData := ArrayRotl baseData (memLineOffset addr) in
    let numBytesActive : Expr ty (Bit (lgLineBytesZ + 1)%Z) :=
      Sll $1 (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) in
    let isWrites :=
      FromBit (Array lBytes Bool)
        (rotateLeft (Not (Sll (ConstBit (InvDefault _)) numBytesActive)) (memLineOffset addr)) in
    let tagData : Expr ty (Array nTags Bool) :=
      if hasTags r then
        UpdateArray ConstDef (memTagSlot addr) (And [ isCap ; stVal`"tag" ])
      else
        ConstDef in
    let '(tagMask0, tagMask1) := memTagMasks addr memSize in
    let tagMask : Expr ty (Array nTags Bool) :=
      FromBit (Array nTags Bool) (Or [ ToBit tagMask0 ; ToBit tagMask1 ]) in
    STRUCT {
      "addr"     ::= addr ;
      "data"     ::= rotData ;
      "dataMask" ::= isWrites ;
      "tag"      ::= tagData ;
      "tagMask"  ::= tagMask
    }.

  Definition memLineWriteRq0
    (rq : Expr ty (LineWriteRq isInternal r.(regionLineCfg)))
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : Expr ty (LineWriteRq isInternal r.(regionLineCfg)) :=
    let addr := rq`"addr" in
    let add1Bits := memAdd1 addr in
    let '(tagMask0, _) := memTagMasks addr memSize in
    STRUCT {
      "addr"     ::= memLineAddr addr ;
      "data"     ::= rq`"data" ;
      "dataMask" ::= FromBit (Array lBytes Bool) (And [ ToBit (rq`"dataMask") ; Not (ToBit add1Bits) ]) ;
      "tag"      ::= rq`"tag" ;
      "tagMask"  ::= tagMask0
    }.

  Definition memLineWriteRq1
    (rq : Expr ty (LineWriteRq isInternal r.(regionLineCfg)))
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : Expr ty (LineWriteRq isInternal r.(regionLineCfg)) :=
    let addr := rq`"addr" in
    let add1Bits := memAdd1 addr in
    let '(_, tagMask1) := memTagMasks addr memSize in
    STRUCT {
      "addr"     ::= memNextLineAddr addr ;
      "data"     ::= rq`"data" ;
      "dataMask" ::= FromBit (Array lBytes Bool) (And [ ToBit (rq`"dataMask") ; ToBit add1Bits ]) ;
      "tag"      ::= rq`"tag" ;
      "tagMask"  ::= tagMask1
    }.

  Definition memCrossesLine
    (addr : Expr ty Addr)
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : Expr ty Bool :=
    let lineOffset := memLineOffset addr in
    let numBytesActive : Expr ty (Bit (lgLineBytesZ + 1)%Z) :=
      Sll $1 (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) in
    let endOffset : Expr ty (Bit (lgLineBytesZ + 1)%Z) :=
      Add [ ZeroExtend 1 lineOffset ; numBytesActive ] in
    FromBit Bool (TruncMsb 1 lgLineBytesZ (Sub endOffset $1)).

End MemAddrHelpers.

Arguments memCastAddr r [ty] addr.
Arguments memLineIndex r [ty] addr.
Arguments memLineOffset r [ty] addr.
Arguments memLineOffsetIdx r [ty] addr.
Arguments memLineAddr r [ty] addr.
Arguments memNextLineAddr r [ty] addr.
Arguments memAdd1 r [ty] addr.
Arguments memCastAddrForTag isInternal r [ty] addr.
Arguments memTagLineIndex isInternal r [ty] addr.
Arguments memTagRowOffset isInternal r [ty] addr.
Arguments memTagLineOffsetIdx isInternal r [ty] addr.
Arguments memTagSlot isInternal r [ty] addr.
Arguments memAdd1Tag isInternal r [ty] addr.
Arguments memTagMasks isInternal r [ty] addr memSize.
Arguments memMergeLineReadRp isInternal r [ty] addr rp0 rp1.
Arguments memExtractReadCap isInternal r [ty] addr memSize rp.
Arguments memBuildLineWriteRq isInternal r [ty] addr stVal memSize.
Arguments memLineWriteRq0 isInternal r [ty] rq memSize.
Arguments memLineWriteRq1 isInternal r [ty] rq memSize.
Arguments memCrossesLine r [ty] addr memSize.

Definition child0Path {A : Type} {name : string} {c0 : Tree A} {cs : list (Tree A)}
  : NodePath (Node name (c0 :: cs)) :=
  inr (inl (inl tt)).

Definition child1Path {A : Type} {name : string} {c0 c1 : Tree A} {cs : list (Tree A)}
  : NodePath (Node name (c0 :: c1 :: cs)) :=
  inr (inr (inl (inl tt))).

Arguments child0Path {A name c0 cs}.
Arguments child1Path {A name c0 c1 cs}.

(* ===========================================================================
 * Banked Internal Memory Helpers & Converting a MemRegion into a Tree
 * =========================================================================== *)

Definition extractBankDataInit (r : MemRegion) (b : nat)
  : option (option (type (Array (regionNumLines r) (Bit 8)))) :=
  match r.(regionKind) with
  | InternalMem _ (Some (Some tup)) _ =>
      Some (Some (buildStrideTuple (lineBytes r) Zmod.zero (regionNumLines r) b tup.(tupleElems)))
  | InternalMem _ (Some None) _ => Some None
  | _ => None
  end.

Definition extractBankTagInit (r : MemRegion) (b : nat)
  : option (option (type (Array (regionTagSize true r) Bool))) :=
  match r.(regionKind) with
  | InternalMem _ _ (Some (Some tup)) =>
      if hasTags r
      then Some (Some (buildStrideTuple (numLineTags true r) false (regionTagSize true r) b tup.(tupleElems)))
      else None
  | InternalMem _ _ (Some None) => Some None
  | _ => None
  end.

Definition memBankLeaf (r : MemRegion) (b : nat) : Tree DomainElem :=
  Leaf "memBank" (r.(regionDom), EMem (@Build_Mem (regionNumLines r) (Bit 8) (regionNumReadPorts r) (extractBankDataInit r b))).

Definition tagBankLeaf (r : MemRegion) (b : nat) : Tree DomainElem :=
  Leaf "tagBank" (r.(regionDom), EMem (@Build_Mem (regionTagSize true r) Bool (regionNumReadPorts r) (extractBankTagInit r b))).

Definition internalMemTargetPortChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "lineReadRqValid"  (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRq"       (r.(regionDom), ERecv Addr) ;
    Leaf "lineReadRp"       (r.(regionDom), ESend (LineReadRp true r.(regionLineCfg))) ;
    Leaf "lineWriteRqValid" (r.(regionDom), ERecv Bool) ;
    Leaf "lineWriteRq"      (r.(regionDom), ERecv (LineWriteRq true r.(regionLineCfg)))
  ].

Definition internalMemRegionChildren
           (r : MemRegion)
           (isAccessible : bool)
           : list (Tree DomainElem) :=
  ([ Node "memBanks" (map (memBankLeaf r) (seq 0 (lineBytes r))) ;
     Node "tagBanks" (map (tagBankLeaf r) (seq 0 (numLineTags true r)))
   ] ++ if isAccessible then internalMemTargetPortChildren r else [])%list.

Definition externalMemRegionChildren (r : MemRegion) (hasExtraFetchPort : bool) : list (Tree DomainElem) :=
  ([ Leaf "lineReadRq"  (r.(regionDom), ESend Addr) ;
     Leaf "lineReadRp"  (r.(regionDom), ERecv (LineReadRp false r.(regionLineCfg))) ;
     Leaf "lineWriteRq" (r.(regionDom), ESend (LineWriteRq false r.(regionLineCfg)))
   ] ++
   if hasExtraFetchPort then
     [ Leaf "fetchLineReadRq" (r.(regionDom), ESend Addr) ;
       Leaf "fetchLineReadRp" (r.(regionDom), ERecv (LineReadRp false r.(regionLineCfg))) ]
   else [])%list.

Definition internalMemRegionTree
           (r : MemRegion)
           (isAccessible : bool)
           : Tree DomainElem :=
  Node r.(regionName) (internalMemRegionChildren r isAccessible).

Definition externalMemRegionTree (r : MemRegion) (hasExtraFetchPort : bool) : Tree DomainElem :=
  Node r.(regionName) (externalMemRegionChildren r hasExtraFetchPort).

Definition customMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
  Node r.(regionName) children.

Definition memRegionTree (r : MemRegion) : Tree DomainElem :=
  match r.(regionKind) with
  | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
  | ExternalMem => externalMemRegionTree r r.(hasExtraFetchPort)
  | CustomMem children _ _ _ => customMemRegionTree r children
  end.

(* ===========================================================================
 * Line-Level Actions for Each Region Kind
 * =========================================================================== *)

Section InternalMemRegionActions.
  Variable r : MemRegion.
  Variable isAccessible : bool.
  Variable ty : Kind -> Type.

  Let tInt := internalMemRegionTree r isAccessible.
  Let numLines := regionNumLines r.
  Let numTagLines := regionTagSize true r.
  Let lBytes := lineBytes r.
  Let nTags := numLineTags true r.

  Local Definition leaf_list_path_mem (n : nat) (p : FinType n) :=
    leaf_list_path_seq (memBankLeaf r) (fun _ => tt) 0 p.

  Local Definition leaf_list_path_tag (n : nat) (p : FinType n) :=
    leaf_list_path_seq (tagBankLeaf r) (fun _ => tt) 0 p.

  Local Lemma leaf_list_path_mem_is_mem n (i : FinType n) :
    Is_true (isMemElem (@getLeafElem (Node "memBanks" (map (memBankLeaf r) (seq 0 n))) (leaf_list_path_mem i))).
  Proof.
    unfold leaf_list_path_mem, getLeafElem.
    rewrite getLeaf_seq.
    simpl.
    exact I.
  Qed.

  Local Lemma leaf_list_path_tag_is_mem n (i : FinType n) :
    Is_true (isMemElem (@getLeafElem (Node "tagBanks" (map (tagBankLeaf r) (seq 0 n))) (leaf_list_path_tag i))).
  Proof.
    unfold leaf_list_path_tag, getLeafElem.
    rewrite getLeaf_seq.
    simpl.
    exact I.
  Qed.

  Local Definition memBankPath (i : FinType lBytes) : MemPath tInt.
  Proof.
    refine (Build_MemPath tInt (inl (leaf_list_path_mem i)) _).
    exact (leaf_list_path_mem_is_mem i).
  Defined.

  Local Definition tagBankPath (i : FinType nTags) : MemPath tInt.
  Proof.
    refine (Build_MemPath tInt (inr (inl (leaf_list_path_tag i))) _).
    exact (leaf_list_path_tag_is_mem i).
  Defined.

  Local Lemma memBankEq n (i : FinType n) :
    @getMemFromPathUnsafe (Node "memBanks" (map (memBankLeaf r) (seq 0 n))) (leaf_list_path_mem i) =
    {| memSize := numLines; memKind := Bit 8; memPort := regionNumReadPorts r; memInit := extractBankDataInit r (0 + i.(finNum)) |}.
  Proof.
    unfold leaf_list_path_mem, getMemFromPathUnsafe, getLeafElem.
    rewrite getLeaf_seq.
    reflexivity.
  Qed.

  Local Lemma tagBankEq n (i : FinType n) :
    @getMemFromPathUnsafe (Node "tagBanks" (map (tagBankLeaf r) (seq 0 n))) (leaf_list_path_tag i) =
    {| memSize := numTagLines; memKind := Bool; memPort := regionNumReadPorts r; memInit := extractBankTagInit r (0 + i.(finNum)) |}.
  Proof.
    unfold leaf_list_path_tag, getMemFromPathUnsafe, getLeafElem.
    rewrite getLeaf_seq.
    reflexivity.
  Qed.

  Local Definition memPortCast (i : FinType lBytes) (p : FinType (regionNumReadPorts r)) : FinType (memPort (getMemFromPath (memBankPath i))) :=
    match eq_sym (f_equal memPort (memBankEq i)) in _ = Y return FinType Y with
    | eq_refl => p
    end.

  Local Definition tagPortCast (i : FinType nTags) (p : FinType (regionNumReadPorts r)) : FinType (memPort (getMemFromPath (tagBankPath i))) :=
    match eq_sym (f_equal memPort (tagBankEq i)) in _ = Y return FinType Y with
    | eq_refl => p
    end.

  Local Definition memSizeCast (i : FinType lBytes) (e : Expr ty (Bit (Z.log2_up (Z.of_nat numLines)))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (memBankPath i)))))) :=
    match eq_sym (f_equal memSize (memBankEq i)) in _ = Y return Expr ty (Bit (Z.log2_up (Z.of_nat Y))) with
    | eq_refl => e
    end.

  Local Definition tagSizeCast (i : FinType nTags) (e : Expr ty (Bit (Z.log2_up (Z.of_nat numTagLines)))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (tagBankPath i)))))) :=
    match eq_sym (f_equal memSize (tagBankEq i)) in _ = Y return Expr ty (Bit (Z.log2_up (Z.of_nat Y))) with
    | eq_refl => e
    end.

  Local Definition memKindCast (i : FinType lBytes) (e : Expr ty (Bit 8)) :
    Expr ty (memKind (getMemFromPath (memBankPath i))) :=
    match eq_sym (f_equal memKind (memBankEq i)) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Definition memKindCastInv (i : FinType lBytes) (e : Expr ty (memKind (getMemFromPath (memBankPath i)))) :
    Expr ty (Bit 8) :=
    match f_equal memKind (memBankEq i) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Definition tagKindCast (i : FinType nTags) (e : Expr ty Bool) :
    Expr ty (memKind (getMemFromPath (tagBankPath i))) :=
    match eq_sym (f_equal memKind (tagBankEq i)) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Definition tagKindCastInv (i : FinType nTags) (e : Expr ty (memKind (getMemFromPath (tagBankPath i)))) :
    Expr ty Bool :=
    match f_equal memKind (tagBankEq i) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Let bankLineIdx (lineIdx : Expr ty (Bit (Z.log2_up (Z.of_nat numLines))))
                  (add1Bits : Expr ty (Array lBytes Bool))
                  (memIdx : FinType lBytes)
    : Expr ty (Bit (Z.log2_up (Z.of_nat numLines))) :=
    Add [ lineIdx ; ITE0 (ReadArrayConst add1Bits memIdx) $1 ].

  Let tagBankLineIdx (tagLineIdx : Expr ty (Bit (Z.log2_up (Z.of_nat numTagLines))))
                     (add1TagBits : Expr ty (Array nTags Bool))
                     (tagIdx : FinType nTags)
    : Expr ty (Bit (Z.log2_up (Z.of_nat numTagLines))) :=
    Add [ tagLineIdx ; ITE0 (ReadArrayConst add1TagBits tagIdx) $1 ].

  Definition internalMemRegionIssueReadRq (isFetch : bool) (addr : ty Addr)
             : Action ty tInt (Bit 0) :=
    let port := selectReadPort r isFetch in
    Let lineIdx  : Bit (Z.log2_up (Z.of_nat numLines)) <- memLineOffsetIdx r #addr ;
    Let add1Bits : Array lBytes Bool                   <- memAdd1 r #addr ;
    Act (fold_right (fun memIdx acc =>
                       ReadRqMem (memBankPath memIdx) (memSizeCast memIdx (bankLineIdx #lineIdx #add1Bits memIdx)) (memPortCast memIdx port) acc)
                    Retv (genFinType lBytes)) ;
    if hasTags r then (
      Let tagLineIdx  : Bit (Z.log2_up (Z.of_nat numTagLines)) <- memTagLineOffsetIdx true r #addr ;
      Let add1TagBits : Array nTags Bool                       <- memAdd1Tag true r #addr ;
      fold_right (fun tagIdx acc =>
                    ReadRqMem (tagBankPath tagIdx) (tagSizeCast tagIdx (tagBankLineIdx #tagLineIdx #add1TagBits tagIdx)) (tagPortCast tagIdx port) acc)
                 Retv (genFinType nTags)
    ) else (
      Retv
    ).

  Definition internalMemRegionGetReadRp (isFetch : bool)
             : Action ty tInt (LineReadRp true r.(regionLineCfg)) :=
    let port := selectReadPort r isFetch in
    LetA dataBytes : Array lBytes (Bit 8) <-
      fold_right (fun memIdx acc =>
                    ReadRpMem "readByteRp" (memBankPath memIdx) (memPortCast memIdx port)
                      (fun val =>
                         LetA rest : Array lBytes (Bit 8) <- acc ;
                         Return (UpdateArrayConst #rest memIdx (memKindCastInv #val))))
                 (Return ConstDef) (genFinType lBytes) ;
    LetA tagArr : Array nTags Bool <-
      if hasTags r then (
        fold_right (fun tagIdx acc =>
                      ReadRpMem "readTagRp" (tagBankPath tagIdx) (tagPortCast tagIdx port)
                        (fun val =>
                           LetA rest : Array nTags Bool <- acc ;
                           Return (UpdateArrayConst #rest tagIdx (tagKindCastInv #val))))
                   (Return ConstDef) (genFinType nTags)
      ) else (
        Return ConstDef
      ) ;
    @Return ty tInt (LineReadRp true r.(regionLineCfg)) (STRUCT {
      "data" ::= #dataBytes ;
      "tag"  ::= #tagArr
    }).

  Definition internalMemRegionLineRead (isFetch : bool) (addr : ty Addr)
             : Action ty tInt (LineReadRp true r.(regionLineCfg)) :=
    Act (internalMemRegionIssueReadRq isFetch addr) ;
    internalMemRegionGetReadRp isFetch.

  Definition internalMemRegionLineWrite
             (rq : ty (LineWriteRq true r.(regionLineCfg)))
             : Action ty tInt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let lineIdx  : Bit (Z.log2_up (Z.of_nat numLines)) <- memLineOffsetIdx r (##rq`"addr") ;
      Let add1Bits : Array lBytes Bool                   <- memAdd1 r (##rq`"addr") ;
      Act (fold_right (fun memIdx acc =>
                         If (ReadArrayConst (##rq`"dataMask") memIdx) Then (
                           WriteMem (memBankPath memIdx) (memSizeCast memIdx (bankLineIdx #lineIdx #add1Bits memIdx))
                             (memKindCast memIdx (ReadArrayConst (##rq`"data") memIdx)) Retv
                         ) ;
                         acc)
                      Retv (genFinType lBytes)) ;
      if hasTags r then (
        Let tagLineIdx  : Bit (Z.log2_up (Z.of_nat numTagLines)) <- memTagLineOffsetIdx true r (##rq`"addr") ;
        Let add1TagBits : Array nTags Bool                       <- memAdd1Tag true r (##rq`"addr") ;
        fold_right (fun tagIdx acc =>
                      If (ReadArrayConst (##rq`"tagMask") tagIdx) Then (
                        WriteMem (tagBankPath tagIdx) (tagSizeCast tagIdx (tagBankLineIdx #tagLineIdx #add1TagBits tagIdx))
                          (tagKindCast tagIdx (ReadArrayConst (##rq`"tag") tagIdx)) Retv
                      ) ;
                      acc)
                   Retv (genFinType nTags)
      ) else (
        Retv
      )
    ).

End InternalMemRegionActions.

Arguments internalMemRegionIssueReadRq r isAccessible [ty] isFetch addr.
Arguments internalMemRegionGetReadRp r isAccessible {ty} isFetch.
Arguments internalMemRegionLineRead r isAccessible [ty] isFetch addr.
Arguments internalMemRegionLineWrite r isAccessible [ty] rq.

Section InternalMemTargetPortActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tIntTargetPort := internalMemRegionTree r true.
  Local Definition pTargetPortLineReadRqValid  : RecvPath tIntTargetPort := getChildRecvPathTree tIntTargetPort "lineReadRqValid".
  Local Definition pTargetPortLineReadRq       : RecvPath tIntTargetPort := getChildRecvPathTree tIntTargetPort "lineReadRq".
  Local Definition pTargetPortLineReadRp       : SendPath tIntTargetPort := getChildSendPathTree tIntTargetPort "lineReadRp".
  Local Definition pTargetPortLineWriteRqValid : RecvPath tIntTargetPort := getChildRecvPathTree tIntTargetPort "lineWriteRqValid".
  Local Definition pTargetPortLineWriteRq      : RecvPath tIntTargetPort := getChildRecvPathTree tIntTargetPort "lineWriteRq".

  Definition internalMemRegionTargetPortRead : Action ty tIntTargetPort (Bit 0) :=
    Recv "valid" pTargetPortLineReadRqValid (fun valid =>
    If #valid Then (
      Recv "addr" pTargetPortLineReadRq (fun addr =>
      LetA rp : LineReadRp true r.(regionLineCfg) <-
        internalMemRegionLineRead r true false addr ;
      Send pTargetPortLineReadRp #rp Retv)
    ) ;
    Retv).

  Definition internalMemRegionTargetPortWrite : Action ty tIntTargetPort (Bit 0) :=
    Recv "valid" pTargetPortLineWriteRqValid (fun valid =>
    If #valid Then (
      Recv "rq" pTargetPortLineWriteRq (fun rq =>
      internalMemRegionLineWrite r true rq)
    ) ;
    Retv).

End InternalMemTargetPortActions.

Arguments internalMemRegionTargetPortRead r {ty}.
Arguments internalMemRegionTargetPortWrite r {ty}.

Section ExternalMemRegionActions.
  Variable r : MemRegion.
  Variable hasExtraFetchPort : bool.
  Variable ty : Kind -> Type.

  Local Definition tExt := externalMemRegionTree r hasExtraFetchPort.
  Local Definition pLineReadRqTrue      : SendPath (externalMemRegionTree r true)  := Eval cbn in (getChildSendPathTree (externalMemRegionTree r true) "lineReadRq").
  Local Definition pFetchLineReadRqTrue : SendPath (externalMemRegionTree r true)  := Eval cbn in (getChildSendPathTree (externalMemRegionTree r true) "fetchLineReadRq").
  Local Definition pLineReadRqFalse     : SendPath (externalMemRegionTree r false) := Eval cbn in (getChildSendPathTree (externalMemRegionTree r false) "lineReadRq").
  Local Definition pLineReadRpTrue      : RecvPath (externalMemRegionTree r true)  := Eval cbn in (getChildRecvPathTree (externalMemRegionTree r true) "lineReadRp").
  Local Definition pFetchLineReadRpTrue : RecvPath (externalMemRegionTree r true)  := Eval cbn in (getChildRecvPathTree (externalMemRegionTree r true) "fetchLineReadRp").
  Local Definition pLineReadRpFalse     : RecvPath (externalMemRegionTree r false) := Eval cbn in (getChildRecvPathTree (externalMemRegionTree r false) "lineReadRp").
  Local Definition pLineWriteRq         : SendPath tExt                            := Eval cbn in (getChildSendPathTree tExt "lineWriteRq").

  Definition externalMemRegionIssueReadRq (isFetch : bool) (addr : ty Addr)
             : Action ty tExt (Bit 0) :=
    match hasExtraFetchPort as b return Action ty (externalMemRegionTree r b) (Bit 0) with
    | true  => if isFetch then Send pFetchLineReadRqTrue #addr Retv else Send pLineReadRqTrue #addr Retv
    | false => Send pLineReadRqFalse #addr Retv
    end.

  Definition externalMemRegionGetReadRp (isFetch : bool)
             : Action ty tExt (LineReadRp false r.(regionLineCfg)) :=
    match hasExtraFetchPort as b return Action ty (externalMemRegionTree r b) (LineReadRp false r.(regionLineCfg)) with
    | true  => if isFetch then Recv "rp" pFetchLineReadRpTrue (fun rp => Return #rp) else Recv "rp" pLineReadRpTrue (fun rp => Return #rp)
    | false => Recv "rp" pLineReadRpFalse (fun rp => Return #rp)
    end.

  Definition externalMemRegionLineRead (isFetch : bool) (addr : ty Addr)
             : Action ty tExt (LineReadRp false r.(regionLineCfg)) :=
    Act (externalMemRegionIssueReadRq isFetch addr) ;
    externalMemRegionGetReadRp isFetch.

  Definition externalMemRegionLineWrite
             (rq : ty (LineWriteRq false r.(regionLineCfg)))
             : Action ty tExt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Send pLineWriteRq #rq Retv
    ).

End ExternalMemRegionActions.

Arguments externalMemRegionIssueReadRq r hasExtraFetchPort [ty] isFetch addr.
Arguments externalMemRegionGetReadRp r hasExtraFetchPort {ty} isFetch.
Arguments externalMemRegionLineRead r hasExtraFetchPort [ty] isFetch addr.
Arguments externalMemRegionLineWrite r hasExtraFetchPort [ty] rq.

Section CustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree DomainElem).
  Variable hasExtraFetchPort : bool.
  Variable readAction : forall ty, ReadPortSel hasExtraFetchPort -> ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp false r.(regionLineCfg)).
  Variable writeAction : forall ty, ty (LineWriteRq false r.(regionLineCfg)) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tCust := customMemRegionTree r children.

  Definition customMemRegionLineRead (isFetch : bool) (addr : ty Addr)
             : Action ty tCust (LineReadRp false r.(regionLineCfg)) :=
    readAction (selectReadPortSel hasExtraFetchPort isFetch) addr.

  Definition customMemRegionLineWrite
             (rq : ty (LineWriteRq false r.(regionLineCfg)))
             : Action ty tCust (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      writeAction rq
    ).

End CustomMemRegionActions.

Arguments customMemRegionLineRead r children hasExtraFetchPort readAction [ty] isFetch addr.
Arguments customMemRegionLineWrite r children writeAction [ty] rq.

Definition memRegionLineRead
           {ty : Kind -> Type}
           (r : MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           : Action ty (memRegionTree r) (LineReadRp (isInternalMem r) r.(regionLineCfg)) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                              | ExternalMem => externalMemRegionTree r r.(hasExtraFetchPort)
                                              | CustomMem children _ _ _ => customMemRegionTree r children
                                              end) (LineReadRp (isInternalRegionKind k) r.(regionLineCfg)) with
  | InternalMem isAccessible _ _ => internalMemRegionLineRead r isAccessible isFetch addr
  | ExternalMem => externalMemRegionLineRead r r.(hasExtraFetchPort) isFetch addr
  | CustomMem children readAct writeAct _ => customMemRegionLineRead r children r.(hasExtraFetchPort) readAct isFetch addr
  end.

Definition memRegionLineWrite
           {ty : Kind -> Type}
           (r : MemRegion)
           (rq : ty (LineWriteRq (isInternalMem r) r.(regionLineCfg)))
           : Action ty (memRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return ty (LineWriteRq (isInternalRegionKind k) r.(regionLineCfg)) ->
                                   Action ty (match k with
                                              | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                              | ExternalMem => externalMemRegionTree r r.(hasExtraFetchPort)
                                              | CustomMem children _ _ _ => customMemRegionTree r children
                                              end) (Bit 0) with
  | InternalMem isAccessible _ _ => fun rq' => internalMemRegionLineWrite r isAccessible rq'
  | ExternalMem => fun rq' => externalMemRegionLineWrite r r.(hasExtraFetchPort) rq'
  | CustomMem children readAct writeAct _ => fun rq' => customMemRegionLineWrite r children writeAct rq'
  end rq.

Arguments memRegionLineRead [ty] r isFetch addr.
Arguments memRegionLineWrite [ty] r rq.

(* ===========================================================================
 * Universal CHERI Capability Multi-Byte Read & Write for a MemRegion (Spec)
 * =========================================================================== *)

Section MemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tR := memRegionTree r.
  Let isInt := isInternalMem r.

  Definition memRegionRead
             (isFetch : bool)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR FullCapWithTag :=
    if isInt then (
      LetA rp : LineReadRp isInt r.(regionLineCfg) <- memRegionLineRead r isFetch addr ;
      Return (memExtractReadCap isInt r #addr #memSize #rp)
    ) else (
      Let  addr0   : Addr                               <- memLineAddr r #addr ;
      LetA rp0     : LineReadRp isInt r.(regionLineCfg) <- memRegionLineRead r isFetch addr0 ;
      Let  crosses : Bool                               <- memCrossesLine r #addr #memSize ;
      LetIf rp1 : LineReadRp isInt r.(regionLineCfg) <-
        If #crosses Then (
          Let addr1 : Addr <- memNextLineAddr r #addr ;
          memRegionLineRead r isFetch addr1
        ) Else (
          Return ConstDef
        ) ;
      Let  rp      : LineReadRp isInt r.(regionLineCfg) <- memMergeLineReadRp isInt r #addr #rp0 #rp1 ;
      Return (memExtractReadCap isInt r #addr #memSize #rp)
    ).

  Definition memRegionWrite
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let rq : LineWriteRq isInt r.(regionLineCfg) <- memBuildLineWriteRq isInt r #addr #stVal #memSize ;
      if isInt then (
        memRegionLineWrite r rq
      ) else (
        Let rq0     : LineWriteRq isInt r.(regionLineCfg) <- memLineWriteRq0 isInt r #rq #memSize ;
        Act (memRegionLineWrite r rq0) ;
        Let crosses : Bool                                <- memCrossesLine r #addr #memSize ;
        If #crosses Then (
          Let rq1 : LineWriteRq isInt r.(regionLineCfg) <- memLineWriteRq1 isInt r #rq #memSize ;
          memRegionLineWrite r rq1
        ) ;
        Retv
      )
    ).

End MemRegionActions.

Arguments memRegionRead r [ty] isFetch addr memSize.
Arguments memRegionWrite r [ty] addr stVal memSize.

(* ===========================================================================
 * Composite Memory Tree & System Routing
 * =========================================================================== *)

Fixpoint specMemChildren (regions : list MemRegion) : list (Tree DomainElem) :=
  match regions with
  | [] => []
  | r :: rs => [ memRegionTree r ; Node "mem" (specMemChildren rs) ]
  end.

Definition specMemTree (regions : list MemRegion) : Tree DomainElem :=
  Node "mem" (specMemChildren regions).

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

Section SpecMemRouter.
  Variable ty : Kind -> Type.

  Fixpoint specMemRead
           (regions : list MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (specMemTree regions) FullCapWithTag :=
    match regions return Action ty (specMemTree regions) FullCapWithTag with
    | [] => Return ConstDef
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf devVal : FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (memRegionRead r isFetch addr memSize)
          ) Else (
            Return ConstDef
          ) ;
        LetA restVal : FullCapWithTag <-
          liftAction child1Path (specMemRead rs isFetch addr memSize) ;
        Return (Or [ #devVal ; #restVal ])
    end.

  Fixpoint specMemWrite
           (regions : list MemRegion)
           (addr : ty Addr)
           (stVal : ty FullCapWithTag)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (specMemTree regions) (Bit 0) :=
    match regions return Action ty (specMemTree regions) (Bit 0) with
    | [] => Retv
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        If #isMatch Then (
          liftAction child0Path (memRegionWrite r addr stVal memSize)
        ) ;
        liftAction child1Path (specMemWrite rs addr stVal memSize)
    end.

End SpecMemRouter.

Section RevBitHelper.
  Variable ty : Kind -> Type.
  Variable config : RevConfig.
  Variable regions : list MemRegion.

  Definition readRevBit (base : ty (Bit (AddrSz + 1))) : Action ty (specMemTree regions) Bool :=
    LetL lookup      : RevBitLookup               <- computeRevBitAddr config base ;
    Let  revByteAddr : Addr                       <- ##lookup`"revByteAddr" ;
    Let  sz0         : Bit LgLgNumBytesFullCapSz  <- $0 ;
    LetA revCap      : FullCapWithTag             <- specMemRead regions false revByteAddr sz0 ;
    Let  revByte     : Bit 8                      <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
    Let  revBit      : Bool                       <- extractRevBit lookup #revByte ;
    Return #revBit.
End RevBitHelper.

Definition memRegionIrqAction
           (r : MemRegion)
           : option (forall ty, Action ty (memRegionTree r) Bool) :=
  match r.(regionKind) as k return option (forall ty, Action ty (match k with
                                                                | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                                                | ExternalMem => externalMemRegionTree r r.(hasExtraFetchPort)
                                                                | CustomMem children _ _ _ => customMemRegionTree r children
                                                                end) Bool) with
  | CustomMem children _ _ (Some act) => Some act
  | _ => None
  end.

Section IrqCollector.
  Fixpoint collectIrqActions
           (regions : list MemRegion)
           : list (forall ty, Action ty (specMemTree regions) Bool) :=
    match regions return list (forall ty, Action ty (specMemTree regions) Bool) with
    | [] => []
    | r :: rs =>
        let rest := map (fun act ty => liftAction child1Path (act ty))
                        (collectIrqActions rs) in
        match memRegionIrqAction r with
        | Some act =>
            (fun ty => liftAction child0Path (act ty)) :: rest
        | None => rest
        end
    end.
End IrqCollector.

Definition memRegionTargetPortActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (memRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                                                         | ExternalMem => externalMemRegionTree r r.(hasExtraFetchPort)
                                                                         | CustomMem children _ _ _ => customMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem true _ _ =>
      [ (r.(regionDom), fun ty => @internalMemRegionTargetPortWrite r ty) ;
        (r.(regionDom), fun ty => @internalMemRegionTargetPortRead r ty) ]
  | _ => []
  end.

Section TargetPortCollector.
  Fixpoint collectTargetPortActions
           (regions : list MemRegion)
           : list (string * (forall ty, Action ty (specMemTree regions) (Bit 0))) :=
    match regions return list (string * (forall ty, Action ty (specMemTree regions) (Bit 0))) with
    | [] => []
    | r :: rs =>
        let curr := map (fun '(dom, act) => (dom, fun ty => liftAction child0Path (act ty)))
                        (memRegionTargetPortActions r) in
        let rest := map (fun '(dom, act) => (dom, fun ty => liftAction child1Path (act ty)))
                        (collectTargetPortActions rs) in
        (curr ++ rest)%list
    end.
End TargetPortCollector.
