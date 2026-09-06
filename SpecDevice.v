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
 * MemRegion Definition & Disjointness Checking
 * =========================================================================== *)

Inductive LineConfig :=
| TaggedLine (lgLineBytes : nat) (pf : Is_true (Z.to_nat LgNumBytesFullCapSz <=? lgLineBytes)%nat)
| RawLine    (lgLineBytes : nat).

Definition cfgHasTags (cfg : LineConfig) : bool :=
  match cfg with
  | TaggedLine _ _ => true
  | RawLine _ => false
  end.

Definition cfgLgLineBytes (cfg : LineConfig) : nat :=
  match cfg with
  | TaggedLine lgBytes _ => lgBytes
  | RawLine lgBytes => lgBytes
  end.

Definition cfgLineBytes (cfg : LineConfig) : nat :=
  Nat.pow 2 (cfgLgLineBytes cfg).

Definition cfgNumLineTags (cfg : LineConfig) : nat :=
  match cfg with
  | TaggedLine lgBytes _ => Nat.pow 2 (lgBytes - Z.to_nat LgNumBytesFullCapSz)
  | RawLine _ => 0%nat
  end.

Definition cfgRegionTagSize (regionSize : Z) (cfg : LineConfig) : nat :=
  if cfgHasTags cfg then Z.to_nat (regionSize / NumBytesFullCapSz) else 0%nat.

Definition defaultTagsInit (regionSize : Z) (cfg : LineConfig)
  : option (option (type (Array (cfgRegionTagSize regionSize cfg) Bool))) :=
  Some (Some (Build_SameTuple (tupleElems := List.repeat false (cfgRegionTagSize regionSize cfg))
                              (Is_true_Nat_eq_implies (repeat_length _ _)))).

Notation LineReadRp cfg := (STRUCT_TYPE {
  "data" :: Array (cfgLineBytes cfg) (Bit 8) ;
  "tag"  :: Array (cfgNumLineTags cfg) Bool
}).

Notation LineWriteRq cfg := (STRUCT_TYPE {
  "addr"     :: Addr ;
  "data"     :: Array (cfgLineBytes cfg) (Bit 8) ;
  "dataMask" :: Array (cfgLineBytes cfg) Bool ;
  "tag"      :: Array (cfgNumLineTags cfg) Bool ;
  "tagMask"  :: Array (cfgNumLineTags cfg) Bool
}).

Inductive RegionKind (regionName : string) (regionSize : Z) (cfg : LineConfig) :=
| InternalMem (initData : option (option (type (Array (Z.to_nat regionSize) (Bit 8)))))
              (initTags : option (option (type (Array (cfgRegionTagSize regionSize cfg) Bool))))
| ExternalMem
| CustomMem (children : list (Tree Elem))
            (readAction : forall ty, Expr ty Addr ->
                          Action ty (Node regionName children) (LineReadRp cfg))
            (writeAction : forall ty, Expr ty (LineWriteRq cfg) ->
                           Action ty (Node regionName children) (Bit 0))
            (irqAction : option (forall ty, Action ty (Node regionName children) Bool)).

Arguments InternalMem {regionName regionSize cfg} initData initTags.
Arguments ExternalMem {regionName regionSize cfg}.
Arguments CustomMem {regionName regionSize cfg} children readAction writeAction irqAction.

Record MemRegion := {
  regionName        : string ;
  regionBase        : Z ;
  regionSize        : Z ;
  regionLineCfg     : LineConfig ;
  isReadOnly        : bool ;
  regionKind        : RegionKind regionName regionSize regionLineCfg ;
  regionInMemory    : Is_true ((0 <=? regionBase) && (regionBase + regionSize <=? Z.shiftl 1 AddrSz))%Z ;
  regionBaseAligned : Is_true (regionBase mod (2 ^ Z.of_nat (cfgLgLineBytes regionLineCfg)) =? 0)%Z ;
  regionSizeAligned : Is_true (regionSize mod (2 ^ Z.of_nat (cfgLgLineBytes regionLineCfg)) =? 0)%Z
}.

Definition hasTags (r : MemRegion) : bool :=
  cfgHasTags r.(regionLineCfg).

Definition lgLineBytes (r : MemRegion) : nat :=
  cfgLgLineBytes r.(regionLineCfg).

Definition lineBytes (r : MemRegion) : nat :=
  cfgLineBytes r.(regionLineCfg).

Definition numLineTags (r : MemRegion) : nat :=
  cfgNumLineTags r.(regionLineCfg).

Definition disjointBool (r1 r2 : MemRegion) : bool :=
  (r1.(regionBase) + r1.(regionSize) <=? r2.(regionBase))%Z ||
  (r2.(regionBase) + r2.(regionSize) <=? r1.(regionBase))%Z.

Fixpoint pairwiseDisjoint (l : list MemRegion) : bool :=
  match l with
  | [] => true
  | r :: rs => forallb (disjointBool r) rs && pairwiseDisjoint rs
  end.

Definition isRegionAddr {ty : Kind -> Type} (r : MemRegion) (addr : Expr ty Addr) : Expr ty Bool :=
  And [ Sge addr $(r.(regionBase)) ; Slt addr $(r.(regionBase) + r.(regionSize)) ].

Definition regionTagSize (r : MemRegion) : nat :=
  cfgRegionTagSize r.(regionSize) r.(regionLineCfg).

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

(* ===========================================================================
 * Converting a MemRegion into a Tree
 * =========================================================================== *)

Definition internalMemRegionChildren
           (r : MemRegion)
           (initData : option (option (type (Array (Z.to_nat r.(regionSize)) (Bit 8)))))
           (initTags : option (option (type (Array (regionTagSize r) Bool))))
           : list (Tree Elem) :=
  [ Leaf "mainMem" (EMem {| memSize := Z.to_nat r.(regionSize);
                            memKind := Bit 8;
                            memPort := 1;
                            memInit := initData |}) ;
    Leaf "tags" (EMem {| memSize := regionTagSize r;
                         memKind := Bool;
                         memPort := 1;
                         memInit := initTags |})
  ].

Definition externalMemRegionChildren (r : MemRegion) : list (Tree Elem) :=
  [ Leaf "lineReadRq" (ESend Addr) ;
    Leaf "lineReadRp" (ERecv (LineReadRp r.(regionLineCfg))) ;
    Leaf "lineWriteRq" (ESend (LineWriteRq r.(regionLineCfg)))
  ].

Arguments internalMemRegionChildren r initData initTags : clear implicits.
Arguments externalMemRegionChildren r : clear implicits.

Definition internalMemRegionTree
           (r : MemRegion)
           (initData : option (option (type (Array (Z.to_nat r.(regionSize)) (Bit 8)))))
           (initTags : option (option (type (Array (regionTagSize r) Bool))))
           : Tree Elem :=
  Node r.(regionName) (internalMemRegionChildren r initData initTags).

Definition externalMemRegionTree (r : MemRegion) : Tree Elem :=
  Node r.(regionName) (externalMemRegionChildren r).

Definition customMemRegionTree (r : MemRegion) (children : list (Tree Elem)) : Tree Elem :=
  Node r.(regionName) children.

Arguments internalMemRegionTree r initData initTags : clear implicits.
Arguments externalMemRegionTree r : clear implicits.
Arguments customMemRegionTree r children : clear implicits.

Definition memRegionTree (r : MemRegion) : Tree Elem :=
  match r.(regionKind) with
  | InternalMem initData initTags => internalMemRegionTree r initData initTags
  | ExternalMem => externalMemRegionTree r
  | CustomMem children _ _ _ => customMemRegionTree r children
  end.

(* ===========================================================================
 * Line-Level Actions for Each Region Kind
 * =========================================================================== *)

Section InternalMemRegionActions.
  Variable r : MemRegion.
  Variable initData : option (option (type (Array (Z.to_nat r.(regionSize)) (Bit 8)))).
  Variable initTags : option (option (type (Array (regionTagSize r) Bool))).
  Variable ty : Kind -> Type.

  Local Definition tInt := internalMemRegionTree r initData initTags.
  Local Definition mainMemPath : MemPath tInt := getChildMemPathTree tInt "mainMem".
  Local Definition tagsPath : MemPath tInt := getChildMemPathTree tInt "tags".

  Definition internalMemRegionLineRead (addr : Expr ty Addr)
             : Action ty tInt (LineReadRp r.(regionLineCfg)) :=
    Let offset <- getMemOffset r.(regionBase) (Z.of_nat (Z.to_nat r.(regionSize))) addr ;
    LetA dataBytes : Array (lineBytes r) (Bit 8) <-
      sliceMem mainMemPath I (lineBytes r) #offset ;
    LetA tagArr : Array (numLineTags r) Bool <-
      if hasTags r then (
        Let tagAddr : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
        Let tagOffset <- getMemOffset (Z.shiftr r.(regionBase) LgNumBytesFullCapSz) (Z.of_nat (regionTagSize r)) #tagAddr ;
        sliceMem tagsPath I (numLineTags r) #tagOffset
      ) else (
        Return ConstDef
      ) ;
    @Return ty tInt (LineReadRp r.(regionLineCfg)) (STRUCT {
      "data" ::= #dataBytes ;
      "tag"  ::= #tagArr
    }).

  Definition internalMemRegionLineWrite
             (rq : Expr ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tInt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let offset <- getMemOffset r.(regionBase) (Z.of_nat (Z.to_nat r.(regionSize))) (rq`"addr") ;
      Act (updSliceMem mainMemPath (lineBytes r) #offset (rq`"data") (rq`"dataMask")) ;
      if hasTags r then (
        Let tagAddr : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz (rq`"addr") ;
        Let tagOffset <- getMemOffset (Z.shiftr r.(regionBase) LgNumBytesFullCapSz) (Z.of_nat (regionTagSize r)) #tagAddr ;
        Act (updSliceMem tagsPath (numLineTags r) #tagOffset (rq`"tag") (rq`"tagMask")) ;
        Retv
      ) else (
        Retv
      )
    ).

End InternalMemRegionActions.

Arguments internalMemRegionLineRead r initData initTags [ty] addr.
Arguments internalMemRegionLineWrite r initData initTags [ty] rq.

Section ExternalMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tExt := externalMemRegionTree r.
  Local Definition pLineReadRq : SendPath tExt := getChildSendPathTree tExt "lineReadRq".
  Local Definition pLineReadRp : RecvPath tExt := getChildRecvPathTree tExt "lineReadRp".
  Local Definition pLineWriteRq : SendPath tExt := getChildSendPathTree tExt "lineWriteRq".

  Definition externalMemRegionLineRead (addr : Expr ty Addr)
             : Action ty tExt (LineReadRp r.(regionLineCfg)) :=
    Send pLineReadRq addr (
    Recv "rp" pLineReadRp (fun rp =>
    Return #rp)).

  Definition externalMemRegionLineWrite
             (rq : Expr ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tExt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Send pLineWriteRq rq Retv
    ).

End ExternalMemRegionActions.

Arguments externalMemRegionLineRead r [ty] addr.
Arguments externalMemRegionLineWrite r [ty] rq.

Section CustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree Elem).
  Variable readAction : forall ty, Expr ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp r.(regionLineCfg)).
  Variable writeAction : forall ty, Expr ty (LineWriteRq r.(regionLineCfg)) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tCust := customMemRegionTree r children.

  Definition customMemRegionLineRead (addr : Expr ty Addr)
             : Action ty tCust (LineReadRp r.(regionLineCfg)) :=
    readAction addr.

  Definition customMemRegionLineWrite
             (rq : Expr ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tCust (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      writeAction rq
    ).

End CustomMemRegionActions.

Arguments customMemRegionLineRead r children readAction [ty] addr.
Arguments customMemRegionLineWrite r children writeAction [ty] rq.

Definition memRegionLineRead
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : Expr ty Addr)
           : Action ty (memRegionTree r) (LineReadRp r.(regionLineCfg)) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem initData initTags => internalMemRegionTree r initData initTags
                                              | ExternalMem => externalMemRegionTree r
                                              | CustomMem children _ _ _ => customMemRegionTree r children
                                              end) (LineReadRp r.(regionLineCfg)) with
  | InternalMem initData initTags => internalMemRegionLineRead r initData initTags addr
  | ExternalMem => externalMemRegionLineRead r addr
  | CustomMem children readAct writeAct _ => customMemRegionLineRead r children readAct addr
  end.

Definition memRegionLineWrite
           {ty : Kind -> Type}
           (r : MemRegion)
           (rq : Expr ty (LineWriteRq r.(regionLineCfg)))
           : Action ty (memRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem initData initTags => internalMemRegionTree r initData initTags
                                              | ExternalMem => externalMemRegionTree r
                                              | CustomMem children _ _ _ => customMemRegionTree r children
                                              end) (Bit 0) with
  | InternalMem initData initTags => internalMemRegionLineWrite r initData initTags rq
  | ExternalMem => externalMemRegionLineWrite r rq
  | CustomMem children readAct writeAct _ => customMemRegionLineWrite r children writeAct rq
  end.

Arguments memRegionLineRead [ty] r addr.
Arguments memRegionLineWrite [ty] r rq.

(* ===========================================================================
 * Universal CHERI Capability Multi-Byte Read & Write for a MemRegion
 * =========================================================================== *)

Section MemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tR := memRegionTree r.
  Local Definition lBytes := lineBytes r.
  Local Definition nTags := numLineTags r.
  Local Definition lgLineBytesZ := Z.of_nat (lgLineBytes r).

  Local Definition castAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

  Local Definition lineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytesZ) :=
    TruncLsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Local Definition lineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgLineBytesZ)%Z) :=
    TruncMsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Local Definition lineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< lineIndex addr, Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Local Definition nextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< Add [ lineIndex addr ; $1 ], Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Local Definition add1 (addr : Expr ty Addr) : Expr ty (Array lBytes Bool) :=
    FromBit (Array lBytes Bool)
      (Not (Sll (ConstBit (InvDefault _)) (lineOffset addr))).

  Local Definition lgNumDXlenZ : Z := (lgLineBytesZ - LgNumBytesFullCapSz)%Z.

  Local Definition castLineOffsetForTag (offset : Expr ty (Bit lgLineBytesZ))
    : Expr ty (Bit (LgNumBytesFullCapSz + lgNumDXlenZ)%Z) :=
    castBits (eq_sym (add_sub_cancel lgLineBytesZ LgNumBytesFullCapSz)) offset.

  Local Definition tagSlot (addr : Expr ty Addr) : Expr ty (Bit lgNumDXlenZ) :=
    TruncMsb lgNumDXlenZ LgNumBytesFullCapSz (castLineOffsetForTag (lineOffset addr)).

  Definition memRegionRead
             (addr : Expr ty Addr)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR FullCapWithTag :=
    Let capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz addr ;
    Let isCapAligned : Bool <- isZero #capOffset ;
    Let isCap : Bool <- And [Eq memSize $LgNumBytesFullCapSz ; #isCapAligned] ;
    Let numBytesActive : Bit (lgLineBytesZ + 1)%Z <-
                           Sll $1
                             (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
    Let endOffset : Bit (lgLineBytesZ + 1)%Z <-
      Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
    Let crossesLine : Bool <- FromBit Bool (TruncMsb 1 lgLineBytesZ #endOffset) ;
    LetA rp1 : LineReadRp r.(regionLineCfg) <- memRegionLineRead r (lineAddr addr) ;
    LetIf lineDataMerged : Array lBytes (Bit 8) <-
      If #crossesLine Then (
        LetA rp2 : LineReadRp r.(regionLineCfg) <- memRegionLineRead r (nextLineAddr addr) ;
        Return (ArrayBuilder (fun (i : FinType lBytes) =>
          ITE (ReadArrayConst (add1 addr) i)
              (ReadArrayConst (##rp2`"data") i)
              (ReadArrayConst (##rp1`"data") i)))
      ) Else (
        Return (##rp1`"data")
      ) ;
    Let rotData : Array lBytes (Bit 8) <- ArrayRotr 8 #lineDataMerged (lineOffset addr) ;
    Let dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      slice #rotData (Const ty (Bit 0) Zmod.zero) (Z.to_nat NumBytesFullCapSz) ;
    Let rawData : Bit FullCapSz <- ToBit #dataBytes ;
    LetA rawTag : Bool <-
      if hasTags r then (
        Return (ReadArray (##rp1`"tag") (tagSlot addr))
      ) else (
        Return (ConstBool false)
      ) ;
    Let res : FullCapWithTag <- STRUCT {
      "tag"  ::= And [ #isCap ; #rawTag ] ;
      "cap"  ::= FromBit Cap (TruncMsb CapSz AddrSz #rawData) ;
      "addr" ::= TruncLsb CapSz AddrSz #rawData
    } ;
    Return #res.

  Definition memRegionWrite
             (addr : Expr ty Addr)
             (stVal : Expr ty FullCapWithTag)
             (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz addr ;
      Let isCapAligned : Bool <- isZero #capOffset ;
      Let isCap : Bool <- And [Eq memSize $LgNumBytesFullCapSz ; #isCapAligned] ;
      Let rawData : Bit FullCapSz <-
        ITE #isCap
            {< ToBit (stVal`"cap"), stVal`"addr" >}
            (ZeroExtendTo FullCapSz (stVal`"addr")) ;
      Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData ;
      Let baseData : Array lBytes (Bit 8) <- embedCapBytes lBytes #capBytes ;
      Let rotData : Array lBytes (Bit 8) <- ArrayRotl 8 #baseData (lineOffset addr) ;
      Let numBytesActive : Bit (lgLineBytesZ + 1)%Z <-
                             Sll $1
                               (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      Let endOffset : Bit (lgLineBytesZ + 1)%Z <-
        Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
      Let crossesLine : Bool <- FromBit Bool (TruncMsb 1 lgLineBytesZ #endOffset) ;
      Let numBytesActiveDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
                             Sll $1
                               (ZeroExtend (LgNumBytesFullCapSz + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      Let endOffsetDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
        Add [ ZeroExtend 1 #capOffset ; #numBytesActiveDXlen ] ;
      Let crossesDXlen : Bool <- FromBit Bool (TruncMsb 1 LgNumBytesFullCapSz #endOffsetDXlen) ;
      Let isWrites : Array lBytes Bool <-
        FromBit (Array lBytes Bool)
          (rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (lineOffset addr)) ;
      Let mask1 : Array lBytes Bool <-
        ArrayBuilder (fun (i : FinType lBytes) =>
          And [ ReadArrayConst #isWrites i ; Not (ReadArrayConst (add1 addr) i) ]) ;
      Let tagData1 : Array nTags Bool <-
        if hasTags r then (
          UpdateArray ConstDef (tagSlot addr) (And [ #isCap ; stVal`"tag" ])
        ) else (
          ConstDef
        ) ;
      Let crossWithinLine : Bool <- And [ #crossesDXlen ; Not #crossesLine ] ;
      Let nextTagSlot : Bit lgNumDXlenZ <- Add [ tagSlot addr ; $1 ] ;
      Let tagMask1 : Array nTags Bool <-
        if hasTags r then (
          UpdateArray
            (UpdateArray ConstDef (tagSlot addr) (ConstBool true))
            #nextTagSlot
            #crossWithinLine
        ) else (
          ConstDef
        ) ;
      Act (memRegionLineWrite r (STRUCT {
        "addr"     ::= lineAddr addr ;
        "data"     ::= #rotData ;
        "dataMask" ::= #mask1 ;
        "tag"      ::= #tagData1 ;
        "tagMask"  ::= #tagMask1
      })) ;
      If #crossesLine Then (
        Let mask2 : Array lBytes Bool <-
          ArrayBuilder (fun (i : FinType lBytes) =>
            And [ ReadArrayConst #isWrites i ; ReadArrayConst (add1 addr) i ]) ;
        Let tagData2 : Array nTags Bool <- ConstDef ;
        Let tagMask2 : Array nTags Bool <-
          if hasTags r then (
            UpdateArray ConstDef (Const ty (Bit lgNumDXlenZ) Zmod.zero) (ConstBool true)
          ) else (
            ConstDef
          ) ;
        Act (memRegionLineWrite r (STRUCT {
          "addr"     ::= nextLineAddr addr ;
          "data"     ::= #rotData ;
          "dataMask" ::= #mask2 ;
          "tag"      ::= #tagData2 ;
          "tagMask"  ::= #tagMask2
        })) ;
        Retv
      ) ;
      Retv
    ).

End MemRegionActions.

Arguments memRegionRead r [ty] addr memSize.
Arguments memRegionWrite r [ty] addr stVal memSize.

(* ===========================================================================
 * Composite Memory Tree & System Routing
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

Section RevBitHelper.
  Variable ty : Kind -> Type.
  Variable config : RevConfig.
  Variable regions : list MemRegion.

  Definition readRevBit (base : Expr ty (Bit (AddrSz + 1))) : Action ty (specMemTree regions) Bool :=
    LetL lookup  : RevBitLookup   <- computeRevBitAddr config base ;
    LetA revCap  : FullCapWithTag <- specMemRead regions (##lookup`"revByteAddr") $0 ;
    Let  revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
    Let  revBit  : Bool           <- extractRevBit lookup #revByte ;
    Return #revBit.
End RevBitHelper.

Definition memRegionIrqAction
           (r : MemRegion)
           : option (forall ty, Action ty (memRegionTree r) Bool) :=
  match r.(regionKind) as k return option (forall ty, Action ty (match k with
                                                                | InternalMem initData initTags => internalMemRegionTree r initData initTags
                                                                | ExternalMem => externalMemRegionTree r
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
