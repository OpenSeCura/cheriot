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

Definition LgDXlenBytes : nat := Eval compute in Z.to_nat LgNumBytesFullCapSz.

Inductive LineConfig :=
| TaggedLine (lgLineBytes : nat) (pf : Is_true (LgDXlenBytes <=? lgLineBytes)%nat)
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
  | TaggedLine lgBytes _ => Nat.pow 2 (lgBytes - LgDXlenBytes)
  | RawLine _ => 0%nat
  end.

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

Inductive RegionKind (regionName : string) (regionSize : nat) (cfg : LineConfig) :=
| InternalMem (init : option (option (type (Array regionSize (Bit 8)))))
| ExternalMem
| CustomMem (children : list (Tree Elem))
            (readAction : forall ty, Expr ty Addr ->
                          Action ty (Node regionName children) (LineReadRp cfg))
            (writeAction : forall ty, Expr ty (LineWriteRq cfg) ->
                           Action ty (Node regionName children) (Bit 0)).

Arguments InternalMem {regionName regionSize cfg} init.
Arguments ExternalMem {regionName regionSize cfg}.
Arguments CustomMem {regionName regionSize cfg} children readAction writeAction.

Record MemRegion := {
  regionName        : string ;
  regionBase        : Z ;
  regionSize        : nat ;
  regionLineCfg     : LineConfig ;
  isReadOnly        : bool ;
  regionKind        : RegionKind regionName regionSize regionLineCfg ;
  regionInMemory    : Is_true ((0 <=? regionBase) && (regionBase + Z.of_nat regionSize <=? Z.shiftl 1 AddrSz))%Z ;
  regionBaseAligned : Is_true (regionBase mod (2 ^ Z.of_nat (cfgLgLineBytes regionLineCfg)) =? 0)%Z ;
  regionSizeAligned : Is_true (Z.of_nat regionSize mod (2 ^ Z.of_nat (cfgLgLineBytes regionLineCfg)) =? 0)%Z
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
  if hasTags r then (r.(regionSize) / DXlenBytes)%nat else 0%nat.

(* ===========================================================================
 * 2. Payload Utilities
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
 * 3. Converting a MemRegion into a Tree
 * =========================================================================== *)

Definition internalMemRegionChildren
           (r : MemRegion)
           (init : option (option (type (Array r.(regionSize) (Bit 8)))))
           : list (Tree Elem) :=
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

Definition externalMemRegionChildren (r : MemRegion) : list (Tree Elem) :=
  [ Leaf "lineReadRq" (ESend Addr) ;
    Leaf "lineReadRp" (ERecv (LineReadRp r.(regionLineCfg))) ;
    Leaf "lineWriteRq" (ESend (LineWriteRq r.(regionLineCfg)))
  ].

Arguments internalMemRegionChildren r init : clear implicits.
Arguments externalMemRegionChildren r : clear implicits.

Definition internalMemRegionTree (r : MemRegion) (init : option (option (type (Array r.(regionSize) (Bit 8))))) : Tree Elem :=
  Node r.(regionName) (internalMemRegionChildren r init).

Definition externalMemRegionTree (r : MemRegion) : Tree Elem :=
  Node r.(regionName) (externalMemRegionChildren r).

Definition customMemRegionTree (r : MemRegion) (children : list (Tree Elem)) : Tree Elem :=
  Node r.(regionName) children.

Arguments internalMemRegionTree r init : clear implicits.
Arguments externalMemRegionTree r : clear implicits.
Arguments customMemRegionTree r children : clear implicits.

Definition memRegionTree (r : MemRegion) : Tree Elem :=
  match r.(regionKind) with
  | InternalMem init => internalMemRegionTree r init
  | ExternalMem => externalMemRegionTree r
  | CustomMem children _ _ => customMemRegionTree r children
  end.

(* ===========================================================================
 * 4. Line-Level Actions for Each Region Kind
 * =========================================================================== *)

Section InternalMemRegionActions.
  Variable r : MemRegion.
  Variable init : option (option (type (Array r.(regionSize) (Bit 8)))).
  Variable ty : Kind -> Type.

  Local Definition tInt := internalMemRegionTree r init.
  Local Definition mainMemPath : MemPath tInt := getChildMemPathTree tInt "mainMem".
  Local Definition tagsPath : MemPath tInt := getChildMemPathTree tInt "tags".

  Definition internalMemRegionLineRead (addr : Expr ty Addr)
             : Action ty tInt (LineReadRp r.(regionLineCfg)) :=
    Let offset <- getMemOffset r.(regionBase) (Z.of_nat r.(regionSize)) addr ;
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
      Let offset <- getMemOffset r.(regionBase) (Z.of_nat r.(regionSize)) (rq`"addr") ;
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

Arguments internalMemRegionLineRead r init [ty] addr.
Arguments internalMemRegionLineWrite r init [ty] rq.

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
                                              | InternalMem init => internalMemRegionTree r init
                                              | ExternalMem => externalMemRegionTree r
                                              | CustomMem children _ _ => customMemRegionTree r children
                                              end) (LineReadRp r.(regionLineCfg)) with
  | InternalMem init => internalMemRegionLineRead r init addr
  | ExternalMem => externalMemRegionLineRead r addr
  | CustomMem children readAct writeAct => customMemRegionLineRead r children readAct addr
  end.

Definition memRegionLineWrite
           {ty : Kind -> Type}
           (r : MemRegion)
           (rq : Expr ty (LineWriteRq r.(regionLineCfg)))
           : Action ty (memRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem init => internalMemRegionTree r init
                                              | ExternalMem => externalMemRegionTree r
                                              | CustomMem children _ _ => customMemRegionTree r children
                                              end) (Bit 0) with
  | InternalMem init => internalMemRegionLineWrite r init rq
  | ExternalMem => externalMemRegionLineWrite r rq
  | CustomMem children readAct writeAct => customMemRegionLineWrite r children writeAct rq
  end.

Arguments memRegionLineRead [ty] r addr.
Arguments memRegionLineWrite [ty] r rq.

(* ===========================================================================
 * 5. Universal CHERI Capability Multi-Byte Read & Write for a MemRegion
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
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< Add [ lineIndex addr ; Const ty (Bit (AddrSz - lgLineBytesZ)%Z) (Zmod.of_Z _ 1) ], Const ty (Bit lgLineBytesZ) Zmod.zero >}.

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
                           Sll (Const ty (Bit (lgLineBytesZ + 1)%Z) (bits.of_Z _ 1))
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
      "cap"  ::= FromBit Cap (TruncMsb Xlen Xlen #rawData) ;
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
                             Sll (Const ty (Bit (lgLineBytesZ + 1)%Z) (bits.of_Z _ 1))
                               (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      Let endOffset : Bit (lgLineBytesZ + 1)%Z <-
        Add [ ZeroExtend 1 (lineOffset addr) ; #numBytesActive ] ;
      Let crossesLine : Bool <- FromBit Bool (TruncMsb 1 lgLineBytesZ #endOffset) ;
      Let numBytesActiveDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
                             Sll (Const ty (Bit (LgNumBytesFullCapSz + 1)%Z) (bits.of_Z _ 1))
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
      Let nextTagSlot : Bit lgNumDXlenZ <- Add [ tagSlot addr ; Const ty (Bit lgNumDXlenZ) (bits.of_Z _ 1) ] ;
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
