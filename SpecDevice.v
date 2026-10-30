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
From Cheriot Require Import SpecDefines FunctionalUnits.

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
 * Memory Lines & Region Definitions
 *
 * Every region uses the global line geometry of SpecDefines (LgLineBytes, LineBytes,
 * NumLineTags), so line requests and responses have the same kinds everywhere.
 * =========================================================================== *)

Definition LineReadRp : Kind :=
  STRUCT_TYPE {
    "data" :: Array LineBytes (Bit 8) ;
    "tag"  :: Array NumLineTags Bool
  }.

Definition LineWriteRq : Kind :=
  STRUCT_TYPE {
    "addr"     :: Addr ;
    "data"     :: Array LineBytes (Bit 8) ;
    "dataMask" :: Array LineBytes Bool ;
    "tag"      :: Array NumLineTags Bool ;
    "tagMask"  :: Array NumLineTags Bool
  }.

(* Result of an instruction fetch: the raw instruction word and whether the instruction
 * fails the top bounds check *)
Definition FetchReadRes : Kind :=
  STRUCT_TYPE {
    "inst"   :: Inst ;
    "topExc" :: Bool
  }.

Inductive RegionKind (regionName : string) :=
| ExternalMem
(* A device has no tags: its read action returns the data bytes of the line, and its write
 * action gets the address, the data bytes and their byte mask *)
| CustomMem (children : list (Tree DomainElem))
            (readAction : forall ty, ty Addr ->
                          ty (Array LineBytes Bool) ->
                          Action ty (Node regionName children) (Array LineBytes (Bit 8)))
            (writeAction : forall ty, ty Addr ->
                           ty (Array LineBytes (Bit 8)) ->
                           ty (Array LineBytes Bool) ->
                           Action ty (Node regionName children) (Bit 0))
            (irqAction : option (forall ty, Action ty (Node regionName children) Bool)).

Arguments ExternalMem {regionName}.
Arguments CustomMem {regionName} children readAction writeAction irqAction.

Record MemRegion := {
  regionName        : string ;
  regionBase        : Z ;
  regionSize        : Z ;
  regionKind        : RegionKind regionName ;
  regionInMemory    : Is_true ((0 <=? regionBase) && (regionBase + regionSize <=? Z.shiftl 1 AddrSz))%Z ;
  regionBaseAligned : Is_true (regionBase mod (2 ^ LgLineBytes) =? 0)%Z ;
  regionSizeAligned : Is_true (regionSize mod (2 ^ LgLineBytes) =? 0)%Z
}.

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

  (* ===========================================================================
   * Memory-Level Line Helpers
   *
   * A data access of 2^memSize bytes at addr touches the line holding addr and, only when it
   * spills past the end of that line (memCrossesLine), the next line. Each line is accessed
   * separately and routed to the region that owns it.
   * =========================================================================== *)

  Section MemAddrHelpers.
    Variable ty : Kind -> Type.

    Definition memLineOffset (addr : Expr ty Addr) : Expr ty (Bit LgLineBytes) :=
      TruncLsb (AddrSz - LgLineBytes) LgLineBytes addr.

    Definition memLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
      {< TruncMsb (AddrSz - LgLineBytes) LgLineBytes addr,
         Const ty (Bit LgLineBytes) Zmod.zero >}.

    Definition memNextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
      Add [ memLineAddr addr ; $(Z.of_nat LineBytes) ].

    Definition memAdd1 (addr : Expr ty Addr) : Expr ty (Array LineBytes Bool) :=
      FromBit (Array LineBytes Bool)
        (Not (Sll (ConstBit (InvDefault _)) (memLineOffset addr))).

    Definition memTagSlot (addr : Expr ty Addr) : Expr ty (Bit LgNumLineTags) :=
      TruncMsb LgNumLineTags LgNumBytesFullCapSz (memLineOffset addr).

    Definition memTagMask
      (isSecond : Expr ty Bool)
      (addr : Expr ty Addr)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : LetExpr ty (Array NumLineTags Bool) :=
      let wTagCnt := (LgNumLineTags + 2)%Z in
      let w := kindSize (Array NumLineTags Bool) in
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
      RetE (FromBit (Array NumLineTags Bool) #maskBits).

    Definition memExtractCapPacket
      (addr : Expr ty Addr)
      (rp : Expr ty LineReadRp)
      : LetExpr ty CapPacket :=
      LetE dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        slice (rp`"data") (memLineOffset addr) (Z.to_nat NumBytesFullCapSz) ;
      LetE rawTag : Bool <- ReadArray (rp`"tag") (memTagSlot addr) ;
      @RetE ty CapPacket (STRUCT {
        "data" ::= #dataBytes ;
        "tag"  ::= #rawTag
      }).

    Definition memDataMask
      (isSecond : Expr ty Bool)
      (addr : Expr ty Addr)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : LetExpr ty (Array LineBytes Bool) :=
      LetE numBytesActive : Bit (LgLineBytes + 1)%Z <-
        Sll $1 (ZeroExtend (LgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) ;
      LetE fullMask : Bit (kindSize (Array LineBytes Bool)) <-
        rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (memLineOffset addr) ;
      LetE add1Bits : Bit (kindSize (Array LineBytes Bool)) <-
        ToBit (memAdd1 addr) ;
      LetE lineSelMask : Bit (kindSize (Array LineBytes Bool)) <-
        ITE isSecond #add1Bits (Not #add1Bits) ;
      RetE (FromBit (Array LineBytes Bool) (And [ #fullMask ; #lineSelMask ])).

    Definition memBuildLineWriteRq
      (isSecond : Expr ty Bool)
      (addr : Expr ty Addr)
      (capPkt : Expr ty CapPacket)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : LetExpr ty LineWriteRq :=
      LetE baseData : Array LineBytes (Bit 8) <- embedCapBytes LineBytes (capPkt`"data") ;
      LETE rotData : Array LineBytes (Bit 8) <- ArrayRotl #baseData (memLineOffset addr) ;
      LETE dataMask : Array LineBytes Bool <- memDataMask isSecond addr memSize ;
      LetE tagData : Array NumLineTags Bool <- UpdateArray ConstDef (memTagSlot addr) (capPkt`"tag") ;
      LETE tagMask : Array NumLineTags Bool <- memTagMask isSecond addr memSize ;
      @RetE ty LineWriteRq (STRUCT {
        "addr"     ::= ITE isSecond (memNextLineAddr addr) (memLineAddr addr) ;
        "data"     ::= #rotData ;
        "dataMask" ::= #dataMask ;
        "tag"      ::= #tagData ;
        "tagMask"  ::= #tagMask
      }).

    (* Whether an access of 2^memSize bytes at addr spills into the next line *)
    Definition memCrossesLine
      (addr : Expr ty Addr)
      (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
      : Expr ty Bool :=
      let lineOffset := memLineOffset addr in
      let numBytesActive : Expr ty (Bit (LgLineBytes + 1)%Z) :=
        Sll $1 (ZeroExtend (LgLineBytes + 1 - LgLgNumBytesFullCapSz)%Z memSize) in
      let endOffset : Expr ty (Bit (LgLineBytes + 1)%Z) :=
        Add [ ZeroExtend 1 lineOffset ; numBytesActive ] in
      FromBit Bool (TruncMsb 1 LgLineBytes (Sub endOffset $1)).

  End MemAddrHelpers.

  Arguments memLineOffset [ty] addr.
  Arguments memLineAddr [ty] addr.
  Arguments memNextLineAddr [ty] addr.
  Arguments memAdd1 [ty] addr.
  Arguments memTagSlot [ty] addr.
  Arguments memTagMask [ty] isSecond addr memSize.
  Arguments memExtractCapPacket [ty] addr rp.
  Arguments memDataMask [ty] isSecond addr memSize.
  Arguments memBuildLineWriteRq [ty] isSecond addr capPkt memSize.
  Arguments memCrossesLine [ty] addr memSize.

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

  Definition externalMemFetchTree : Tree DomainElem :=
    Node "fetch"
      [ Leaf "lineReadRq" (dom, ESend Addr) ;
        Leaf "lineReadRp" (dom, ERecv LineReadRp) ;
        Leaf "fenceIWait" (dom, EReg (Build_Reg Bool (Some false) false)) ;
        Leaf "fenceIRq"   (dom, ESend (Bit 0)) ;
        Leaf "fenceIAck"  (dom, ERecv Bool) ].

  Definition externalMemRegionTree (r : MemRegion) : Tree DomainElem :=
    Node r.(regionName)
      [ externalMemFetchTree ;
        Leaf "lineReadRq"  (dom, ESend Addr) ;
        Leaf "lineReadRp"  (dom, ERecv LineReadRp) ;
        Leaf "lineWriteRq" (dom, ESend LineWriteRq) ].

  Definition customMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
    Node r.(regionName) children.

  Definition memRegionKindTree (r : MemRegion) (k : RegionKind r.(regionName)) : Tree DomainElem :=
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

    Local Definition tExtFetch := externalMemFetchTree.
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
               : Action ty tExt LineReadRp :=
      liftAction child0Path (Recv "rp" pFetchLineReadRp (fun rp => Return #rp)).

    Definition externalFetchLineRead (addr : ty Addr)
               : Action ty tExt LineReadRp :=
      Act (externalFetchLineReadRq addr) ;
      externalFetchLineReadRp.

    Definition externalLineReadRq (addr : ty Addr)
               : Action ty tExt (Bit 0) :=
      Send pLineReadRq #addr Retv.

    Definition externalLineReadRp
               : Action ty tExt LineReadRp :=
      Recv "rp" pLineReadRp (fun rp => Return #rp).

    Definition externalLineRead (addr : ty Addr)
               : Action ty tExt LineReadRp :=
      Act (externalLineReadRq addr) ;
      externalLineReadRp.

    Definition externalLineWrite
               (rq : ty LineWriteRq)
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

  (* Single-line accesses of a region; the line address is routed to the region that owns it *)
  Definition memRegionFetchLineRead
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             : Action ty (memRegionTree r) LineReadRp :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) LineReadRp with
    | ExternalMem => externalFetchLineRead r addr
    | CustomMem _ _ _ _ =>
        Random rp : LineReadRp ;
        Return #rp
    end.

  Definition memRegionLineRead
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             (dataMask : ty (Array LineBytes Bool))
             : Action ty (memRegionTree r) LineReadRp :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) LineReadRp with
    | ExternalMem => externalLineRead r addr
    | CustomMem _ readAct _ _ =>
        LetA data : Array LineBytes (Bit 8) <- readAct ty addr dataMask ;
        @Return _ _ LineReadRp (STRUCT {
          "data" ::= #data ;
          "tag"  ::= Const ty (Array NumLineTags Bool) (getDefault _)
        })
    end.

  Definition memRegionLineWrite
             (r : MemRegion)
             {ty : Kind -> Type}
             (rq : ty LineWriteRq)
             : Action ty (memRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (memRegionKindTree r k) (Bit 0) with
    | ExternalMem => externalLineWrite r rq
    | CustomMem _ _ writeAct _ =>
        Let addr     : Addr                    <- ##rq`"addr" ;
        Let data     : Array LineBytes (Bit 8) <- ##rq`"data" ;
        Let dataMask : Array LineBytes Bool    <- ##rq`"dataMask" ;
        writeAct ty addr data dataMask
    end.

  Arguments memRegionFetchLineRead r [ty] addr.
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
   * Composite Memory Tree & System Routing
   * =========================================================================== *)

  Definition specMemChildren := regionsTreeChildren memRegionTree.
  Definition specMemTree     := regionsTree memRegionTree.
  Definition nthRegionAction {ty : Kind -> Type} := @genNthRegionAction memRegionTree ty.
  Arguments nthRegionAction {ty} idx regions r0 pf {k} act.

  Section SpecMemRouter.
    Variable ty : Kind -> Type.

    (* 1. Single-line accesses, each routed by its line address *)
    Definition specMemFetchLineRead
               (regions : list MemRegion)
               (lineAddr : ty Addr)
               : Action ty (specMemTree regions) LineReadRp :=
      genRouteRegionAction memRegionTree (fun r => memRegionFetchLineRead r lineAddr)
        (@Or _ _) lineAddr regions.

    Definition specMemLineRead
               (regions : list MemRegion)
               (lineAddr : ty Addr)
               (dataMask : ty (Array LineBytes Bool))
               : Action ty (specMemTree regions) LineReadRp :=
      genRouteRegionAction memRegionTree (fun r => memRegionLineRead r lineAddr dataMask)
        (@Or _ _) lineAddr regions.

    Definition specMemLineWrite
               (regions : list MemRegion)
               (rq : ty LineWriteRq)
               : Action ty (specMemTree regions) (Bit 0) :=
      Let lineAddr : Addr <- ##rq`"addr" ;
      genRouteRegionUnitAction memRegionTree (fun r => memRegionLineWrite r rq)
        lineAddr regions.

    (* 2. Instruction fetch: the line holding addr and, if a 4-byte instruction spills into it,
     *    the next line; the two lines may belong to different regions. The low parcel tells
     *    whether the instruction is compressed (2 bytes) or not (4 bytes). The top bounds
     *    check (instEnd > top) is done here: a 4-byte instruction that spills into the next
     *    line but fails it does not fetch that line, and its upper parcel reads as 0. *)
    Definition specMemFetchRead
               (regions : list MemRegion)
               (addr : ty Addr)
               (top : ty (Bit (AddrSz + 2)))
               : Action ty (specMemTree regions) FetchReadRes :=
      Let  addr0       : Addr                      <- memLineAddr #addr ;
      LetA rp0         : LineReadRp                <- specMemFetchLineRead regions addr0 ;
      LetL pkt0        : CapPacket                 <- memExtractCapPacket #addr #rp0 ;
      LetL word0       : FullCapWithTag            <- memAssembleCapRead #addr ($LgNumBytesInstSz : Expr ty (Bit LgLgNumBytesFullCapSz)) #pkt0 ;
      Let  raw0        : Inst                      <- ##word0`"addr" ;
      Let  isComp      : Bool                      <- isCompressed raw0 ;
      Let  instLgBytes : Bit LgLgNumBytesFullCapSz <-
        ITE #isComp $(Z.log2 (CompInstSz / 8)) $(Z.log2 (InstSz / 8)) ;
      LetL instEnd     : Bit (AddrSz + 2)          <- AdderAccessEnd addr instLgBytes ;
      Let  topExc      : Bool                      <- Ugt #instEnd #top ;
      Let  crosses     : Bool                      <-
        And [ Not #isComp ; memCrossesLine #addr ($LgNumBytesInstSz : Expr ty (Bit LgLgNumBytesFullCapSz)) ] ;
      LetIf pkt1 : CapPacket <-
        If (And [ #crosses ; Not #topExc ]) Then (
          Let  addr1 : Addr       <- memNextLineAddr #addr ;
          LetA rp1   : LineReadRp <- specMemFetchLineRead regions addr1 ;
          LetL pkt1  : CapPacket  <- memExtractCapPacket #addr #rp1 ;
          Return #pkt1
        ) Else (
          Return ConstDef
        ) ;
      Let  pkt : CapPacket      <- ITE #crosses (memMergeCapPacket #addr #pkt0 #pkt1) #pkt0 ;
      LetL res : FullCapWithTag <- memAssembleCapRead #addr ($LgNumBytesInstSz : Expr ty (Bit LgLgNumBytesFullCapSz)) #pkt ;
      @Return _ _ FetchReadRes (STRUCT {
        "inst"   ::= ##res`"addr" ;
        "topExc" ::= #topExc
      }).

    (* 3. The two line reads of a data access: the line holding addr, and the next line, which
     *    must only be read when the access spills into it (memCrossesLine) *)
    Definition specMemReadFirstLine
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (specMemTree regions) LineReadRp :=
      Let  lineAddr : Addr                     <- memLineAddr #addr ;
      LetL dataMask : Array LineBytes Bool     <- memDataMask (ConstBool false) #addr #memSize ;
      specMemLineRead regions lineAddr dataMask.

    Definition specMemReadSecondLine
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (specMemTree regions) LineReadRp :=
      Let  lineAddr : Addr                     <- memNextLineAddr #addr ;
      LetL dataMask : Array LineBytes Bool     <- memDataMask (ConstBool true) #addr #memSize ;
      specMemLineRead regions lineAddr dataMask.

    (* 4. Data accesses that stay within one line (capability-aligned or single-byte accesses,
     *    e.g. revoker sweeps and revocation bit lookups). specMemWrite writes the line holding
     *    addr; an access spilling into the next line must also write its second line. *)
    Definition specMemRead
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (specMemTree regions) FullCapWithTag :=
      LetA rp  : LineReadRp     <- specMemReadFirstLine regions addr memSize ;
      LetL pkt : CapPacket      <- memExtractCapPacket #addr #rp ;
      LetL res : FullCapWithTag <- memAssembleCapRead #addr #memSize #pkt ;
      Return #res.

    Definition specMemWrite
               (regions : list MemRegion)
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (specMemTree regions) (Bit 0) :=
      LetL capPkt : CapPacket   <- memDisassembleCapWrite #addr #stVal #memSize ;
      LetL rq     : LineWriteRq <- memBuildLineWriteRq (ConstBool false) #addr #capPkt #memSize ;
      specMemLineWrite regions rq.

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

  Arguments specMemFetchLineRead {ty} regions lineAddr.
  Arguments specMemLineRead {ty} regions lineAddr dataMask.
  Arguments specMemLineWrite {ty} regions rq.
  Arguments specMemFetchRead {ty} regions addr top.
  Arguments specMemReadFirstLine {ty} regions addr memSize.
  Arguments specMemReadSecondLine {ty} regions addr memSize.
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

Arguments externalMemFetchTree dom : clear implicits.
Arguments externalMemRegionTree dom r : clear implicits.
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

Arguments memRegionFetchLineRead {dom} r [ty] addr.
Arguments memRegionLineRead {dom} r [ty] addr dataMask.
Arguments memRegionLineWrite {dom} r [ty] rq.
Arguments memRegionReadFenceIWait {dom} r {ty}.
Arguments memRegionSendFenceIRq {dom} r {ty}.

Arguments nthRegionAction {dom ty} idx regions r0 pf {k} act.
Arguments specMemFetchLineRead {dom} [ty] regions lineAddr.
Arguments specMemLineRead {dom} [ty] regions lineAddr dataMask.
Arguments specMemLineWrite {dom} [ty] regions rq.
Arguments specMemFetchRead {dom} [ty] regions addr top.
Arguments specMemReadFirstLine {dom} [ty] regions addr memSize.
Arguments specMemReadSecondLine {dom} [ty] regions addr memSize.
Arguments specMemRead {dom} [ty] regions addr memSize.
Arguments specMemWrite {dom} [ty] regions addr stVal memSize.
Arguments specMemReadFenceIWait {dom ty} regions.
Arguments specMemSendFenceIRq {dom ty} regions.
Arguments readRevBit {dom} [ty] config regions base.

Arguments collectIrqActions dom regions : clear implicits.
Arguments collectFenceIAckActions dom regions : clear implicits.

