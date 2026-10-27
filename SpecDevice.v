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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Helper Combinators
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
 * Memory Region Definitions & Line Geometry
 * =========================================================================== *)

Record LineConfig := {
  cfgLgLineBytes : nat ;
  cfgHasTags     : bool ;
  cfgLinePf      : Is_true (Z.to_nat LgNumBytesFullCapSz <=? cfgLgLineBytes)%nat
}.

Definition cfgLineBytes (cfg : LineConfig) : nat :=
  Nat.pow 2 cfg.(cfgLgLineBytes).

Definition cfgLgNumLineTags (cfg : LineConfig) : nat :=
  (cfg.(cfgLgLineBytes) - Z.to_nat LgNumBytesFullCapSz)%nat.

Definition cfgLinePackets (cfg : LineConfig) : nat :=
  Nat.pow 2 (cfgLgNumLineTags cfg).

Definition cfgNumLineTags (cfg : LineConfig) : nat :=
  if cfg.(cfgHasTags)
  then cfgLinePackets cfg
  else 0%nat.

Definition LineReadRp (cfg : LineConfig) : Kind :=
  STRUCT_TYPE {
    "data" :: Array (cfgLineBytes cfg) (Bit 8) ;
    "tag"  :: Array (cfgNumLineTags cfg) Bool
  }.

Definition LineWriteRq (cfg : LineConfig) : Kind :=
  STRUCT_TYPE {
    "addr"     :: Addr ;
    "data"     :: Array (cfgLineBytes cfg) (Bit 8) ;
    "dataMask" :: Array (cfgLineBytes cfg) Bool ;
    "tag"      :: Array (cfgNumLineTags cfg) Bool ;
    "tagMask"  :: Array (cfgNumLineTags cfg) Bool
  }.

Inductive RegionKind (regionName : string) (cfg : LineConfig) :=
| ExternalMem
| CustomMem (children : list (Tree DomainElem))
            (readAction : forall ty, ty Addr ->
                          ty (Array (cfgLineBytes cfg) Bool) ->
                          Action ty (Node regionName children) (LineReadRp cfg))
            (writeAction : forall ty, ty (LineWriteRq cfg) ->
                           Action ty (Node regionName children) (Bit 0))
            (irqAction : option (forall ty, Action ty (Node regionName children) Bool)).

Arguments ExternalMem {regionName cfg}.
Arguments CustomMem {regionName cfg} children readAction writeAction irqAction.

Record MemRegion := {
  regionName        : string ;
  regionBase        : Z ;
  regionSize        : Z ;
  regionLineCfg     : LineConfig ;
  regionKind        : RegionKind regionName regionLineCfg ;
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

  Definition linePackets (r : MemRegion) : nat :=
    cfgLinePackets r.(regionLineCfg).

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
    And [ Uge addr $(r.(regionBase)) ; Ult addr $(r.(regionBase) + r.(regionSize)) ].

  Definition memLgLineBytesZ (r : MemRegion) : Z :=
    Z.of_nat (lgLineBytes r).

  Definition memLgNumLineTagsZ (r : MemRegion) : Z :=
    Z.of_nat (cfgLgNumLineTags r.(regionLineCfg)).

  Lemma region_lgLineBytes_ge_cap (r : MemRegion) :
    (Z.to_nat LgNumBytesFullCapSz <= lgLineBytes r)%nat.
  Proof.
    unfold lgLineBytes.
    apply Nat.leb_le, Is_true_eq_true, (cfgLinePf (regionLineCfg r)).
  Qed.

  Lemma lgLineBytes_split (r : MemRegion) :
    memLgLineBytesZ r = (LgNumBytesFullCapSz + memLgNumLineTagsZ r)%Z.
  Proof.
    pose proof (region_lgLineBytes_ge_cap r) as Hpf.
    unfold memLgLineBytesZ, memLgNumLineTagsZ, cfgLgNumLineTags, lgLineBytes, LgNumBytesFullCapSz in *.
    lia.
  Qed.

  Definition CapPacket : Kind :=
    STRUCT_TYPE {
      "data" :: Array (Z.to_nat NumBytesFullCapSz) (Bit 8) ;
      "tag"  :: Bool
    }.

  Definition memMergeCapPacket {ty : Kind -> Type}
    (addr : Expr ty Addr)
    (pkt0 pkt1 : Expr ty CapPacket)
    : Expr ty CapPacket :=
    let capOffset := TruncLsb TagAddrWidth LgNumBytesFullCapSz addr in
    let add1 := FromBit (Array (Z.to_nat NumBytesFullCapSz) Bool)
                  (Not (Srl (ConstBit (InvDefault _)) capOffset)) in
    STRUCT {
      "data" ::= ArrayBuilder (fun i =>
                   ITE (ReadArrayConst add1 i)
                       (ReadArrayConst (pkt1`"data") i)
                       (ReadArrayConst (pkt0`"data") i)) ;
      "tag"  ::= pkt0`"tag"
    }.

  Definition memAssembleCapRead {ty : Kind -> Type}
    (addr : Expr ty Addr)
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    (pkt : Expr ty CapPacket)
    : LetExpr ty FullCapWithTag :=
    LetE capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz addr ;
    LetE isCapAligned : Bool <- isZero #capOffset ;
    LetE isCap : Bool <- And [ Eq memSize $LgNumBytesFullCapSz ; #isCapAligned ] ;
    LetE rawData : Bit FullCapSz <- ToBit (pkt`"data") ;
    @RetE ty FullCapWithTag (STRUCT {
      "tag"  ::= And [ #isCap ; pkt`"tag" ] ;
      "cap"  ::= FromBit Cap (TruncMsb CapSz AddrSz #rawData) ;
      "addr" ::= TruncLsb CapSz AddrSz #rawData
    }).

  Definition memDisassembleCapWrite {ty : Kind -> Type}
    (addr : Expr ty Addr)
    (stVal : Expr ty FullCapWithTag)
    (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
    : LetExpr ty CapPacket :=
    LetE capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz addr ;
    LetE isCapAligned : Bool <- isZero #capOffset ;
    LetE isCap : Bool <- And [ Eq memSize $LgNumBytesFullCapSz ; #isCapAligned ] ;
    LetE rawData : Bit FullCapSz <-
      ITE #isCap
          {< ToBit (stVal`"cap"), stVal`"addr" >}
          (ZeroExtendTo FullCapSz (stVal`"addr")) ;
    LetE capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData ;
    @RetE ty CapPacket (STRUCT {
      "data" ::= #capBytes ;
      "tag"  ::= And [ #isCap ; stVal`"tag" ]
    }).

  Section MemAddrHelpers.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Let lBytes := lineBytes r.
    Let nTags := numLineTags r.
    Let lgLineBytesZ := memLgLineBytesZ r.
    Let lgNumLineTagsZ := memLgNumLineTagsZ r.

    Definition memCastAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
      castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

    Definition memLineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytesZ) :=
      TruncLsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (memCastAddr addr).

    Definition memLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
      castBits (add_sub_cancel AddrSz lgLineBytesZ)
        {< TruncMsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (memCastAddr addr),
           Const ty (Bit lgLineBytesZ) Zmod.zero >}.

    Definition memNextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
      Add [ memLineAddr addr ; $(Z.of_nat lBytes) ].

    Definition memAdd1 (addr : Expr ty Addr) : Expr ty (Array lBytes Bool) :=
      FromBit (Array lBytes Bool)
        (Not (Sll (ConstBit (InvDefault _)) (memLineOffset addr))).

    Definition memTagSlot (addr : Expr ty Addr) : Expr ty (Bit lgNumLineTagsZ) :=
      TruncMsb lgNumLineTagsZ LgNumBytesFullCapSz
        (castBits (lgLineBytes_split r) (memLineOffset addr)).

    Definition memAdd1Tag (addr : Expr ty Addr) : Expr ty (Array nTags Bool) :=
      FromBit (Array nTags Bool)
        (Not (Sll (ConstBit (InvDefault _)) (memTagSlot addr))).

    Definition memTagMask
      (isSecond : Expr ty Bool)
      (addr : Expr ty Addr)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : LetExpr ty (Array nTags Bool) :=
      if hasTags r then
        let wTagCnt := (lgNumLineTagsZ + 2)%Z in
        let w := kindSize (Array nTags Bool) in
        LetE capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz addr ;
        LetE numBytesActiveTag : Bit (LgNumBytesFullCapSz + wTagCnt)%Z <-
          Sll $1 (ZeroExtend (LgNumBytesFullCapSz + wTagCnt - LgLgNumBytesFullCapSz)%Z memSize) ;
        LetE endByteOffset : Bit (LgNumBytesFullCapSz + wTagCnt)%Z <-
          Sub (Add [ ZeroExtend wTagCnt #capOffset ; #numBytesActiveTag ]) $1 ;
        LetE numTagsActive : Bit wTagCnt <-
          Add [ TruncMsb wTagCnt LgNumBytesFullCapSz #endByteOffset ; $1 ] ;
        LetE baseMask : Bit (w + w)%Z <-
          Not (Sll (ConstBit (InvDefault (Bit (w + w)%Z))) #numTagsActive) ;
        LetE shiftedMask : Bit (w + w)%Z <- Sll #baseMask (memTagSlot addr) ;
        LetE maskBits : Bit w <-
          ITE isSecond (TruncMsb w w #shiftedMask) (TruncLsb w w #shiftedMask) ;
        RetE (FromBit (Array nTags Bool) #maskBits)
      else
        RetE ConstDef.

    Definition memExtractCapPacket
      (addr : Expr ty Addr)
      (rp : Expr ty (LineReadRp r.(regionLineCfg)))
      : LetExpr ty CapPacket :=
      LetE dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        slice (rp`"data") (memLineOffset addr) (Z.to_nat NumBytesFullCapSz) ;
      LetE rawTag : Bool <-
        if hasTags r then
          ReadArray (rp`"tag") (memTagSlot addr)
        else
          ConstBool false ;
      @RetE ty CapPacket (STRUCT {
        "data" ::= #dataBytes ;
        "tag"  ::= #rawTag
      }).

    Definition memDataMask
      (isSecond : Expr ty Bool)
      (addr : Expr ty Addr)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : LetExpr ty (Array lBytes Bool) :=
      LetE numBytesActive : Bit (lgLineBytesZ + 1)%Z <-
        Sll $1 (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      LetE fullMask : Bit (kindSize (Array lBytes Bool)) <-
        rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (memLineOffset addr) ;
      LetE add1Bits : Bit (kindSize (Array lBytes Bool)) <-
        ToBit (memAdd1 addr) ;
      LetE lineSelMask : Bit (kindSize (Array lBytes Bool)) <-
        ITE isSecond #add1Bits (Not #add1Bits) ;
      RetE (FromBit (Array lBytes Bool) (And [ #fullMask ; #lineSelMask ])).

    Definition memBuildLineWriteRq
      (isSecond : Expr ty Bool)
      (addr : Expr ty Addr)
      (capPkt : Expr ty CapPacket)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : LetExpr ty (LineWriteRq r.(regionLineCfg)) :=
      LetE baseData : Array lBytes (Bit 8) <- embedCapBytes lBytes (capPkt`"data") ;
      LETE rotData : Array lBytes (Bit 8) <- ArrayRotl #baseData (memLineOffset addr) ;
      LETE dataMask : Array lBytes Bool <- memDataMask isSecond addr memSize ;
      LetE tagData : Array nTags Bool <-
        if hasTags r then
          UpdateArray ConstDef (memTagSlot addr) (capPkt`"tag")
        else
          ConstDef ;
      LETE tagMask : Array nTags Bool <- memTagMask isSecond addr memSize ;
      @RetE ty (LineWriteRq r.(regionLineCfg)) (STRUCT {
        "addr"     ::= ITE isSecond (memNextLineAddr addr) (memLineAddr addr) ;
        "data"     ::= #rotData ;
        "dataMask" ::= #dataMask ;
        "tag"      ::= #tagData ;
        "tagMask"  ::= #tagMask
      }).

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

  Arguments memLineOffset r [ty] addr.
  Arguments memLineAddr r [ty] addr.
  Arguments memNextLineAddr r [ty] addr.
  Arguments memTagSlot r [ty] addr.
  Arguments memDataMask r [ty] isSecond addr memSize.
  Arguments memExtractCapPacket r [ty] addr rp.
  Arguments memBuildLineWriteRq r [ty] isSecond addr capPkt memSize.
  Arguments memCrossesLine r [ty] addr memSize.

  (* ===========================================================================
   * Generic Memory Tree & Routing
   * =========================================================================== *)

  Section GenRegionTree.
    Variable regionTree : MemRegion -> Tree DomainElem.

    Fixpoint regionsTreeChildren (regions : list MemRegion) : list (Tree DomainElem) :=
      match regions with
      | [] => []
      | r :: rs => [ regionTree r ; Node "" (regionsTreeChildren rs) ]
      end.

    Definition regionsTree (regions : list MemRegion) : Tree DomainElem :=
      Node "" (regionsTreeChildren regions).

    Fixpoint genNthRegionAction
               {ty : Kind -> Type}
               (idx : nat)
               (regions : list MemRegion)
               (r0 : MemRegion)
               (pf : nth_error regions idx = Some r0)
               {k : Kind}
               (act : Action ty (regionTree r0) k)
               {struct regions}
               : Action ty (regionsTree regions) k :=
      match regions as rs, idx as i
        return nth_error rs i = Some r0 -> Action ty (regionsTree rs) k
      with
      | [], 0%nat | [], S _ => fun pf =>
          match pf in (_ = o) return if o is Some _ then _ else True with
          | eq_refl => I
          end
      | r :: _, 0%nat => fun pf =>
          let eq_r0_r : r0 = r :=
            match pf in (_ = o) return if o is Some r0' then r0' = r else False with
            | eq_refl => eq_refl
            end in
          liftAction child0Path
            (match eq_r0_r in (_ = y) return Action ty (regionTree y) k with
             | eq_refl => act
             end)
      | _ :: rs, S idx' => fun pf =>
          liftAction child1Path (@genNthRegionAction ty idx' rs r0 pf k act)
      end pf.

    Fixpoint genCollectRegionActions
             {k : Kind}
             (getActions : forall r : MemRegion, list (forall ty, Action ty (regionTree r) k))
             (regions : list MemRegion)
             : list (forall ty, Action ty (regionsTree regions) k) :=
      match regions return list (forall ty, Action ty (regionsTree regions) k) with
      | [] => []
      | r :: rs =>
          let curr := map (fun act ty => liftAction child0Path (act ty))
                          (getActions r) in
          let rest := map (fun act ty => liftAction child1Path (act ty))
                          (genCollectRegionActions getActions rs) in
          (curr ++ rest)%list
      end.

    Fixpoint genRouteRegionActionAux
             {ty : Kind -> Type} {k : Kind}
             (getAction : forall r : MemRegion, Action ty (regionTree r) k)
             (combine : list (Expr ty k) -> Expr ty k)
             (addr : ty Addr)
             (acc : list (Expr ty k))
             (regions : list MemRegion)
             : Action ty (regionsTree regions) k :=
      match regions return Action ty (regionsTree regions) k with
      | [] => Return (combine (rev_tail acc []))
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          LetIf devVal : k <-
            If #isMatch Then (
              liftAction child0Path (getAction r)
            ) ;
          liftAction child1Path (genRouteRegionActionAux getAction combine addr (#devVal :: acc) rs)
      end.

    Definition genRouteRegionAction
               {ty : Kind -> Type} {k : Kind}
               (getAction : forall r : MemRegion, Action ty (regionTree r) k)
               (combine : list (Expr ty k) -> Expr ty k)
               (addr : ty Addr)
               (regions : list MemRegion)
               : Action ty (regionsTree regions) k :=
      genRouteRegionActionAux getAction combine addr [] regions.

    Definition genRouteRegionUnitAction
               {ty : Kind -> Type}
               (getAction : forall r : MemRegion, Action ty (regionTree r) (Bit 0))
               (addr : ty Addr)
               (regions : list MemRegion)
               : Action ty (regionsTree regions) (Bit 0) :=
      genRouteRegionAction getAction (fun _ => $0) addr regions.

    Fixpoint genFoldRegionActionsAux
             {ty : Kind -> Type} {k : Kind}
             (getAction : forall r : MemRegion, Action ty (regionTree r) k)
             (combine : list (Expr ty k) -> Expr ty k)
             (acc : list (Expr ty k))
             (regions : list MemRegion)
             : Action ty (regionsTree regions) k :=
      match regions return Action ty (regionsTree regions) k with
      | [] => Return (combine (rev_tail acc []))
      | r :: rs =>
          LetA devVal : k <- liftAction child0Path (getAction r) ;
          liftAction child1Path (genFoldRegionActionsAux getAction combine (#devVal :: acc) rs)
      end.

    Definition genFoldRegionActions
               {ty : Kind -> Type} {k : Kind}
               (getAction : forall r : MemRegion, Action ty (regionTree r) k)
               (combine : list (Expr ty k) -> Expr ty k)
               (regions : list MemRegion)
               : Action ty (regionsTree regions) k :=
      genFoldRegionActionsAux getAction combine [] regions.

    Definition genFoldRegionUnitActions
               {ty : Kind -> Type}
               (getAction : forall r : MemRegion, Action ty (regionTree r) (Bit 0))
               (regions : list MemRegion)
               : Action ty (regionsTree regions) (Bit 0) :=
      genFoldRegionActions getAction (fun _ => $0) regions.

  End GenRegionTree.

  Arguments genNthRegionAction regionTree {ty} idx regions r0 pf {k} act.
  Arguments genCollectRegionActions regionTree {k} getActions regions.
  Arguments genRouteRegionActionAux regionTree {ty k} getAction combine addr acc regions.
  Arguments genRouteRegionAction regionTree {ty k} getAction combine addr regions.
  Arguments genRouteRegionUnitAction regionTree {ty} getAction addr regions.
  Arguments genFoldRegionActionsAux regionTree {ty k} getAction combine acc regions.
  Arguments genFoldRegionActions regionTree {ty k} getAction combine regions.
  Arguments genFoldRegionUnitActions regionTree {ty} getAction regions.

  (* ===========================================================================
   * Converting a MemRegion into a Tree
   * =========================================================================== *)

Section SpecDevice.
  Variable dom : string.

  Definition externalMemFetchTree (r : MemRegion) : Tree DomainElem :=
    Node "fetch"
      [ Leaf "lineReadRq" (dom, ESend Addr) ;
        Leaf "lineReadRp" (dom, ERecv (LineReadRp r.(regionLineCfg))) ;
        Leaf "fenceIWait" (dom, EReg (Build_Reg Bool (Some false) false)) ;
        Leaf "fenceIRq"   (dom, ESend (Bit 0)) ;
        Leaf "fenceIAck"  (dom, ERecv Bool) ].

  Definition externalMemRegionTree (r : MemRegion) : Tree DomainElem :=
    Node r.(regionName)
      [ externalMemFetchTree r ;
        Leaf "lineReadRq"  (dom, ESend Addr) ;
        Leaf "lineReadRp"  (dom, ERecv (LineReadRp r.(regionLineCfg))) ;
        Leaf "lineWriteRq" (dom, ESend (LineWriteRq r.(regionLineCfg))) ].

  Definition customMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
    Node r.(regionName) children.

  Definition memRegionKindTree (r : MemRegion) (k : RegionKind r.(regionName) r.(regionLineCfg)) : Tree DomainElem :=
    match k with
    | ExternalMem => externalMemRegionTree r
    | CustomMem children _ _ _ => customMemRegionTree r children
    end.

  Arguments memRegionKindTree r k : clear implicits.

  Definition memRegionTree (r : MemRegion) : Tree DomainElem :=
    memRegionKindTree r r.(regionKind).

  (* ===========================================================================
   * Line-Level Actions for Each Region Kind
   * =========================================================================== *)

  Section ExternalMemRegionActions.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Local Definition tExtFetch := externalMemFetchTree r.
    Local Definition tExt      := externalMemRegionTree r.

    Local Definition pFetchLineReadRq : SendPath tExtFetch := Eval cbn in (getChildSendPathTree tExtFetch "lineReadRq").
    Local Definition pFetchLineReadRp : RecvPath tExtFetch := Eval cbn in (getChildRecvPathTree tExtFetch "lineReadRp").
    Local Definition pExtFenceIWait   : RegPath  tExtFetch := Eval cbn in (getChildRegPathTree  tExtFetch "fenceIWait").
    Local Definition pExtFenceIRq     : SendPath tExtFetch := Eval cbn in (getChildSendPathTree tExtFetch "fenceIRq").
    Local Definition pExtFenceIAck    : RecvPath tExtFetch := Eval cbn in (getChildRecvPathTree tExtFetch "fenceIAck").

    Local Definition pLineReadRq  : SendPath tExt := Eval cbn in (getChildSendPathTree tExt "lineReadRq").
    Local Definition pLineReadRp  : RecvPath tExt := Eval cbn in (getChildRecvPathTree tExt "lineReadRp").
    Local Definition pLineWriteRq : SendPath tExt := Eval cbn in (getChildSendPathTree tExt "lineWriteRq").

    Definition externalFetchLineReadRq (addr : ty Addr)
               : Action ty tExt (Bit 0) :=
      liftAction child0Path (Send pFetchLineReadRq #addr Retv).

    Definition externalFetchLineReadRp
               : Action ty tExt (LineReadRp r.(regionLineCfg)) :=
      liftAction child0Path (Recv "rp" pFetchLineReadRp (fun rp => Return #rp)).

    Definition externalFetchLineRead (addr : ty Addr)
               : Action ty tExt (LineReadRp r.(regionLineCfg)) :=
      Act (externalFetchLineReadRq addr) ;
      externalFetchLineReadRp.

    Definition externalLineReadRq (addr : ty Addr)
               : Action ty tExt (Bit 0) :=
      Send pLineReadRq #addr Retv.

    Definition externalLineReadRp
               : Action ty tExt (LineReadRp r.(regionLineCfg)) :=
      Recv "rp" pLineReadRp (fun rp => Return #rp).

    Definition externalLineRead (addr : ty Addr)
               : Action ty tExt (LineReadRp r.(regionLineCfg)) :=
      Act (externalLineReadRq addr) ;
      externalLineReadRp.

    Definition externalLineWrite
               (rq : ty (LineWriteRq r.(regionLineCfg)))
               : Action ty tExt (Bit 0) :=
      Send pLineWriteRq #rq Retv.

    Definition externalReadFenceIWait : Action ty tExt Bool :=
      liftAction child0Path (ReadReg "fenceIWait" pExtFenceIWait (fun v => Return #v)).

    Definition externalSendFenceIRq : Action ty tExt (Bit 0) :=
      liftAction child0Path (
        Act (WriteReg pExtFenceIWait (ConstBool true) Retv) ;
        Send pExtFenceIRq ($0 : Expr ty (Bit 0)) Retv).

    Definition externalFenceIAckStep : Action ty tExt (Bit 0) :=
      liftAction child0Path (
        ReadReg "fenceIWait" pExtFenceIWait (fun wait =>
        If #wait Then (
          Recv "ack" pExtFenceIAck (fun ack =>
          If #ack Then (
            WriteReg pExtFenceIWait (ConstBool false) Retv
          ) ;
          Retv)
        ) ;
        Retv)).

  End ExternalMemRegionActions.

  Arguments externalFetchLineReadRq r [ty] addr.
  Arguments externalFetchLineReadRp r {ty}.
  Arguments externalFetchLineRead r [ty] addr.
  Arguments externalLineReadRq r [ty] addr.
  Arguments externalLineReadRp r {ty}.
  Arguments externalLineRead r [ty] addr.
  Arguments externalLineWrite r [ty] rq.
  Arguments externalReadFenceIWait r {ty}.
  Arguments externalSendFenceIRq r {ty}.
  Arguments externalFenceIAckStep r {ty}.

  Definition memRegionLineRead
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             (dataMask : ty (Array (cfgLineBytes r.(regionLineCfg)) Bool))
             : Action ty (memRegionTree r) (LineReadRp r.(regionLineCfg)) :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) (LineReadRp r.(regionLineCfg)) with
    | ExternalMem => externalLineRead r addr
    | CustomMem _ readAct _ _ => readAct ty addr dataMask
    end.

  Definition memRegionLineWrite
             (r : MemRegion)
             {ty : Kind -> Type}
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty (memRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) (Bit 0) with
    | ExternalMem => externalLineWrite r rq
    | CustomMem _ _ writeAct _ => writeAct ty rq
    end.

  Arguments memRegionLineRead r [ty] addr dataMask.
  Arguments memRegionLineWrite r [ty] rq.

  Definition memRegionReadFenceIWait
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (memRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) Bool with
    | ExternalMem => @externalReadFenceIWait r ty
    | CustomMem _ _ _ _ => Return (ConstBool false)
    end.

  Definition memRegionSendFenceIRq
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (memRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) (Bit 0) with
    | ExternalMem => @externalSendFenceIRq r ty
    | CustomMem _ _ _ _ => Retv
    end.

  Arguments memRegionReadFenceIWait r {ty}.
  Arguments memRegionSendFenceIRq r {ty}.

  (* ===========================================================================
   * Universal CHERI Capability Multi-Byte Read & Write for a MemRegion (Spec)
   * =========================================================================== *)

  Section MemRegionActions.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Local Definition tR := memRegionTree r.

    Definition memRegionFetchRead
               (addr : ty Addr)
               : Action ty tR FullCapWithTag :=
      match r.(regionKind) as k return Action ty (memRegionKindTree r k) FullCapWithTag with
      | ExternalMem =>
          Let  addr0   : Addr                        <- memLineAddr r #addr ;
          LetA rp0     : LineReadRp r.(regionLineCfg) <- externalFetchLineRead r addr0 ;
          LetL pkt0    : CapPacket                   <- memExtractCapPacket r #addr #rp0 ;
          Let  crosses : Bool                        <- memCrossesLine r #addr ($LgNumBytesInstSz : Expr ty (Bit LgLgNumBytesFullCapSz)) ;
          LetIf pkt1 : CapPacket <-
            If #crosses Then (
              Let  addr1 : Addr                        <- memNextLineAddr r #addr ;
              LetA rp1   : LineReadRp r.(regionLineCfg) <- externalFetchLineRead r addr1 ;
              LetL pkt1  : CapPacket                   <- memExtractCapPacket r #addr #rp1 ;
              Return #pkt1
            ) Else (
              Return ConstDef
            ) ;
          Let  pkt : CapPacket      <- ITE #crosses (memMergeCapPacket #addr #pkt0 #pkt1) #pkt0 ;
          LetL res : FullCapWithTag <- memAssembleCapRead #addr ($LgNumBytesInstSz : Expr ty (Bit LgLgNumBytesFullCapSz)) #pkt ;
          Return #res
      | CustomMem _ _ _ _ =>
          Random res : FullCapWithTag ;
          Return #res
      end.

    Definition memRegionRead
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tR CapPacket :=
      Let  addr0     : Addr                        <- memLineAddr r #addr ;
      LetL dataMask0 : Array (lineBytes r) Bool    <- memDataMask r (ConstBool false) #addr #memSize ;
      LetA rp0       : LineReadRp r.(regionLineCfg) <- memRegionLineRead r addr0 dataMask0 ;
      LetL pkt0      : CapPacket                   <- memExtractCapPacket r #addr #rp0 ;
      Let  crosses   : Bool                        <- memCrossesLine r #addr #memSize ;
      LetIf pkt1 : CapPacket <-
        If #crosses Then (
          Let  addr1     : Addr                        <- memNextLineAddr r #addr ;
          LetL dataMask1 : Array (lineBytes r) Bool    <- memDataMask r (ConstBool true) #addr #memSize ;
          LetA rp1       : LineReadRp r.(regionLineCfg) <- memRegionLineRead r addr1 dataMask1 ;
          LetL pkt1      : CapPacket                   <- memExtractCapPacket r #addr #rp1 ;
          Return #pkt1
        ) Else (
          Return ConstDef
        ) ;
      Let  pkt : CapPacket <- ITE #crosses (memMergeCapPacket #addr #pkt0 #pkt1) #pkt0 ;
      Return #pkt.

    Definition memRegionWrite
               (addr : ty Addr)
               (capPkt : ty CapPacket)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tR (Bit 0) :=
      LetL rq0     : LineWriteRq r.(regionLineCfg) <-
        memBuildLineWriteRq r (ConstBool false) #addr #capPkt #memSize ;
      Act (memRegionLineWrite r rq0) ;
      Let  crosses : Bool                          <- memCrossesLine r #addr #memSize ;
      If #crosses Then (
        LetL rq1 : LineWriteRq r.(regionLineCfg) <-
          memBuildLineWriteRq r (ConstBool true) #addr #capPkt #memSize ;
        memRegionLineWrite r rq1
      ) ;
      Retv.

  End MemRegionActions.

  Arguments memRegionFetchRead r [ty] addr.
  Arguments memRegionRead r [ty] addr memSize.
  Arguments memRegionWrite r [ty] addr capPkt memSize.

  (* ===========================================================================
   * Composite Memory Tree & System Routing
   * =========================================================================== *)

  Definition specMemChildren := regionsTreeChildren memRegionTree.
  Definition specMemTree     := regionsTree memRegionTree.
  Definition nthRegionAction {ty : Kind -> Type} := @genNthRegionAction memRegionTree ty.
  Arguments nthRegionAction {ty} idx regions r0 pf {k} act.

  Section SpecMemRouter.
    Variable ty : Kind -> Type.

    Definition specMemFetchRead
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (specMemTree regions) FullCapWithTag :=
      genRouteRegionAction memRegionTree (fun r => memRegionFetchRead r addr)
        (@Or _ _) addr regions.

    Definition specMemRead
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (specMemTree regions) FullCapWithTag :=
      LetA pkt : CapPacket <-
        genRouteRegionAction memRegionTree (fun r => memRegionRead r addr memSize)
          (@Or _ _) addr regions ;
      LetL res : FullCapWithTag <- memAssembleCapRead #addr #memSize #pkt ;
      Return #res.

    Definition specMemWrite
               (regions : list MemRegion)
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (specMemTree regions) (Bit 0) :=
      LetL capPkt : CapPacket <- memDisassembleCapWrite #addr #stVal #memSize ;
      genRouteRegionUnitAction memRegionTree (fun r => memRegionWrite r addr capPkt memSize)
        addr regions.

    Definition specMemReadFenceIWait
               (regions : list MemRegion)
               : Action ty (specMemTree regions) Bool :=
      genFoldRegionActions memRegionTree (fun r => @memRegionReadFenceIWait r ty)
        (@Or _ _) regions.

    Definition specMemSendFenceIRq
               (regions : list MemRegion)
               : Action ty (specMemTree regions) (Bit 0) :=
      genFoldRegionUnitActions memRegionTree (fun r => @memRegionSendFenceIRq r ty)
        regions.

  End SpecMemRouter.

  Arguments specMemFetchRead {ty} regions addr.
  Arguments specMemRead {ty} regions addr memSize.
  Arguments specMemWrite {ty} regions addr stVal memSize.
  Arguments specMemReadFenceIWait {ty} regions.
  Arguments specMemSendFenceIRq {ty} regions.

  Section RevBitHelper.
    Variable ty : Kind -> Type.
    Variable config : RevConfig.
    Variable regions : list MemRegion.

    Definition readRevBit (base : ty (Bit (AddrSz + 1))) : Action ty (specMemTree regions) Bool :=
      LetL lookup      : RevBitLookup              <- computeRevBitAddr config base ;
      Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
      Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
      LetA revCap      : FullCapWithTag            <- specMemRead regions revByteAddr sz0 ;
      Let  revByte     : Bit 8                     <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
      Let  revBit      : Bool                      <- extractRevBit lookup #revByte ;
      Return #revBit.
  End RevBitHelper.

  Definition memRegionIrqAction
             (r : MemRegion)
             : option (forall ty, Action ty (memRegionTree r) Bool) :=
    match r.(regionKind) as k return option (forall ty, Action ty (memRegionKindTree r k) Bool) with
    | CustomMem _ _ _ (Some act) => Some act
    | _ => None
    end.

  Definition memRegionIrqActions
             (r : MemRegion)
             : list (forall ty, Action ty (memRegionTree r) Bool) :=
    match memRegionIrqAction r with
    | Some act => [act]
    | None => []
    end.

  Definition collectIrqActions :=
    genCollectRegionActions memRegionTree memRegionIrqActions.

  Definition memRegionFenceIAckActions
             (r : MemRegion)
             : list (forall ty, Action ty (memRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (memRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @externalFenceIAckStep r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition collectFenceIAckActions :=
    genCollectRegionActions memRegionTree memRegionFenceIAckActions.

End SpecDevice.

Arguments memRegionKindTree dom r k : clear implicits.
Arguments memRegionTree dom r : clear implicits.
Arguments specMemChildren dom regions : clear implicits.
Arguments specMemTree dom regions : clear implicits.

Arguments externalFetchLineReadRq {dom} r [ty] addr.
Arguments externalFetchLineReadRp {dom} r {ty}.
Arguments externalFetchLineRead {dom} r [ty] addr.
Arguments externalLineReadRq {dom} r [ty] addr.
Arguments externalLineReadRp {dom} r {ty}.
Arguments externalLineRead {dom} r [ty] addr.
Arguments externalLineWrite {dom} r [ty] rq.
Arguments externalReadFenceIWait {dom} r {ty}.
Arguments externalSendFenceIRq {dom} r {ty}.
Arguments externalFenceIAckStep {dom} r {ty}.

Arguments memRegionLineRead {dom} r [ty] addr dataMask.
Arguments memRegionLineWrite {dom} r [ty] rq.
Arguments memRegionReadFenceIWait {dom} r {ty}.
Arguments memRegionSendFenceIRq {dom} r {ty}.

Arguments memRegionFetchRead {dom} r [ty] addr.
Arguments memRegionRead {dom} r [ty] addr memSize.
Arguments memRegionWrite {dom} r [ty] addr capPkt memSize.

Arguments nthRegionAction {dom ty} idx regions r0 pf {k} act.
Arguments specMemFetchRead {dom} [ty] regions addr.
Arguments specMemRead {dom} [ty] regions addr memSize.
Arguments specMemWrite {dom} [ty] regions addr stVal memSize.
Arguments specMemReadFenceIWait {dom ty} regions.
Arguments specMemSendFenceIRq {dom ty} regions.
Arguments readRevBit {dom} [ty] config regions base.

Arguments collectIrqActions dom regions : clear implicits.
Arguments collectFenceIAckActions dom regions : clear implicits.

