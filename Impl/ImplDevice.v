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
From Cheriot Require Import SpecDefines SpecDevice FunctionalUnits SpecRevoker ImplRevoker ImplCommon.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Split-Phase Implementation Memory Interface (MemIfc)
 * =========================================================================== *)

Record MemIfc {ty : Kind -> Type} := {
  memTree : Tree DomainElem ;

  (* 1. Instruction Memory Channel *)
  mem_readInstRq   : ty Addr -> Action ty memTree Bool ;
  mem_getInstRp    : ty Addr -> Action ty memTree (Option FetchPacket) ;
  mem_deqInstRp    : ty Addr -> Action ty memTree (Bit 0) ;

  (* 2. Data Load Channel *)
  mem_readMemRq    : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;
  mem_getMemRp     : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree (Option FullCapWithTag) ;
  mem_deqMemRp     : ty Addr -> Action ty memTree (Bit 0) ;

  (* 3. Revocation Bit Memory Channel *)
  mem_readRevBitRq   : ty (Bit (AddrSz + 1)) -> Action ty memTree Bool ;
  mem_getDeqRevBitRp : ty (Bit (AddrSz + 1)) -> Action ty memTree (Option Bool) ;

  (* 4. Memory Write Channel *)
  mem_writeMem     : ty Addr -> ty FullCapWithTag -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;

  (* 5. FENCE & FENCE.I Synchronization Channels *)
  mem_fence_req      : ty FenceOp -> Action ty memTree Bool ;
  mem_readFenceIWait : Action ty memTree Bool ;
  mem_fenceI_req     : Action ty memTree Bool
}.

(* ===========================================================================
 * Implementation Region Trees (Wrapping Spec memRegionTree)
 * =========================================================================== *)

Inductive MemRequester :=
| ReqDataMem
| ReqRevoker.

Definition RequesterList : list (string * Kind) :=
  [ ("DataMem", Bit 0) ;
    ("Revoker", Bit 0) ].

Definition Requester : Kind :=
  TaggedUnion RequesterList.

Definition mkRequester {ty : Kind -> Type} (req : MemRequester) : Expr ty Requester :=
  match req with
  | ReqDataMem => UNION (RequesterList, "DataMem" ::= ($0 : Expr ty (Bit 0)))
  | ReqRevoker => UNION (RequesterList, "Revoker" ::= ($0 : Expr ty (Bit 0)))
  end.

Definition isRequesterMatch {ty : Kind -> Type} (r : ty Requester) (req : MemRequester) : Expr ty Bool :=
  match req with
  | ReqDataMem => #r `? "DataMem"
  | ReqRevoker => #r `? "Revoker"
  end.

Definition MemReadRq0 : Kind :=
  STRUCT_TYPE {
    "crosses" :: Bool ;
    "addr"    :: Addr ;
    "memSize" :: Bit LgLgNumBytesFullCapSz
  }.

Definition MemReadRp0 : Kind :=
  STRUCT_TYPE {
    "addr"    :: Addr ;
    "memSize" :: Bit LgLgNumBytesFullCapSz
  }.

Definition MemWrite0 : Kind :=
  STRUCT_TYPE {
    "addr"    :: Addr ;
    "stVal"   :: FullCapWithTag ;
    "memSize" :: Bit LgLgNumBytesFullCapSz
  }.

Definition MemStateList : list (string * Kind) :=
  [ ("Idle",        Bit 0) ;
    ("ReadRq0Sent", MemReadRq0) ;
    ("ReadRp0Recv", MemReadRp0) ;
    ("ReadRq1Sent", Addr) ;
    ("ReadRp1Recv", Bit 0) ;
    ("Write0Sent",  MemWrite0) ].

Definition MemState : Kind :=
  TaggedUnion MemStateList.

Definition PortRqList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Read",  Addr) ;
    ("Write", LineWriteRq cfg) ].

Definition PortRq (cfg : LineConfig) : Kind :=
  TaggedUnion (PortRqList cfg).

Lemma pow2_sub3 (n : nat) :
  (3 <= n)%nat -> (Nat.pow 2 n = 8 * Nat.pow 2 (n - 3))%nat.
Proof.
  intros H.
  assert (Heq : n = (3 + (n - 3))%nat) by lia.
  rewrite Heq at 1.
  change (Nat.pow 2 (3 + (n - 3))) with (2 * (2 * (2 * Nat.pow 2 (n - 3))))%nat.
  lia.
Qed.

Section ImplDevice.
  Variable dom : string.

  Lemma lineBytes_eq_linePackets (r : MemRegion) :
    kindSize (Array (lineBytes r) (Bit 8)) = kindSize (Array (linePackets r) FetchPacket).
  Proof.
    pose proof (region_lgLineBytes_ge_cap r) as Hpf.
    unfold FetchPacket, NumFetchParcels, CompInstSz, lineBytes, cfgLineBytes, linePackets, cfgLinePackets, cfgLgNumLineTags, lgLineBytes in *.
    cbn [kindSize].
    rewrite !NatZ_mul_mult.
    change (Z.to_nat LgNumBytesFullCapSz) with 3%nat in *.
    rewrite (pow2_sub3 Hpf), Nat2Z.inj_mul.
    lia.
  Qed.

  Definition memExtractFetchPacket
    (r : MemRegion) {ty : Kind -> Type}
    (addr : ty Addr)
    (rp : ty (LineReadRp r.(regionLineCfg)))
    : Expr ty FetchPacket :=
    let pkts := FromBit (Array (linePackets r) FetchPacket)
                        (castBits (lineBytes_eq_linePackets r) (ToBit (##rp`"data"))) in
    ReadArray pkts (memTagSlot r #addr).

  Arguments memExtractFetchPacket r [ty] addr rp.

  Definition implExternalMemFetchTree (r : MemRegion) : Tree DomainElem :=
    Node "fetch"
      [ Leaf "lineReadRqReady" (dom, ERecv Bool) ;
        Leaf "lineReadRpValid" (dom, ERecv Bool) ;
        Leaf "lineReadRpReady" (dom, ESend (Bit 0)) ;
        Leaf "readRp"          (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg))) (Some (getDefault _)) false)) ].

  Definition implExternalMemExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ implExternalMemFetchTree r ;
      Leaf "lineReadRqReady"  (dom, ERecv Bool) ;
      Leaf "lineWriteRqReady" (dom, ERecv Bool) ;
      Leaf "lineReadRpValid"  (dom, ERecv Bool) ;
      Leaf "lineReadRpReady"  (dom, ESend (Bit 0)) ;
      Leaf "portRq"           (dom, EReg (Build_Reg (Option (PortRq r.(regionLineCfg))) (Some (getDefault _)) false)) ;
      Leaf "readRp"           (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg))) (Some (getDefault _)) false)) ;
      Leaf "savedRp"          (dom, EReg (Build_Reg (LineReadRp r.(regionLineCfg)) (Some (getDefault _)) false)) ].

  Definition implCustomMemExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "readRp"           (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg))) (Some (getDefault _)) false)) ;
      Leaf "savedRp"          (dom, EReg (Build_Reg (LineReadRp r.(regionLineCfg)) (Some (getDefault _)) false)) ].

  Definition implMemRegionExtraChildren (r : MemRegion) (k : RegionKind r.(regionName) r.(regionLineCfg)) : list (Tree DomainElem) :=
    match k with
    | ExternalMem => implExternalMemExtraChildren r
    | CustomMem _ _ _ _ => implCustomMemExtraChildren r
    end.

  Arguments implMemRegionExtraChildren r k : clear implicits.

  Definition implMemRegionKindTree (r : MemRegion) (k : RegionKind r.(regionName) r.(regionLineCfg)) : Tree DomainElem :=
    Node r.(regionName) (memRegionKindTree dom r k :: implMemRegionExtraChildren r k).

  Arguments implMemRegionKindTree r k : clear implicits.

  Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
    implMemRegionKindTree r ExternalMem.

  Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
    Node r.(regionName) (customMemRegionTree r children :: implCustomMemExtraChildren r).

  Definition implMemRegionTree (r : MemRegion) : Tree DomainElem :=
    implMemRegionKindTree r r.(regionKind).

  Definition liftToImplRegion {ty : Kind -> Type} (r : MemRegion) {k : Kind}
    (act : Action ty (memRegionTree dom r) k) : Action ty (implMemRegionTree r) k :=
    liftAction child0Path act.

  Arguments liftToImplRegion {ty r k} act.

  (* ===========================================================================
   * Single-Line & Port Implementation Actions for ExternalMem
   * =========================================================================== *)

  Section ImplExternalMemRegionActions.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Local Definition tImplExt      := implExternalMemRegionTree r.
    Local Definition tImplExtFetch := implExternalMemFetchTree r.

    Local Definition fetchPath             : NodePath tImplExt      := child1Path.
    Local Definition pLineWriteRqReady     : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineWriteRqReady").
    Local Definition pLineReadRqReady      : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRqReady").
    Local Definition pLineReadRpValid      : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRpValid").
    Local Definition pLineReadRpReady      : SendPath tImplExt      := Eval cbn in (getChildSendPathTree tImplExt "lineReadRpReady").
    Local Definition pExtPortRq            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "portRq").
    Local Definition pExtReadRp            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "readRp").
    Local Definition pExtSavedRp           : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "savedRp").

    Local Definition pFetchLineReadRqReady : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRqReady").
    Local Definition pFetchLineReadRpValid : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRpValid").
    Local Definition pFetchLineReadRpReady : SendPath tImplExtFetch := Eval cbn in (getChildSendPathTree tImplExtFetch "lineReadRpReady").
    Local Definition pExtFetchReadRp       : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "readRp").

    (* 1. Dedicated Fetch Port Actions *)

    Definition implExternalFetchLineReadRq
               (addr : ty Addr)
               : Action ty tImplExt Bool :=
      Let lineAddr : Addr <- memLineAddr r #addr ;
      Act (liftAction child0Path (externalFetchLineReadRq r lineAddr)) ;
      liftAction fetchPath (Recv "rdy" pFetchLineReadRqReady (fun rdy => Return #rdy)).

    Definition implExternalFetchLineReadRp
               : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg))) :=
      liftAction fetchPath (ReadReg "readRp" pExtFetchReadRp (fun v => Return #v)).

    Definition implExternalFetchLineDeqRp
               : Action ty tImplExt (Bit 0) :=
      liftAction fetchPath (WriteReg pExtFetchReadRp ConstDef Retv).

    Definition implExternalRpPort
               (readRpAct : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg))))
               (validAct : Action ty tImplExt Bool)
               (getRpAct : Action ty tImplExt (LineReadRp r.(regionLineCfg)))
               (ackAndStoreAct : ty (LineReadRp r.(regionLineCfg)) -> Action ty tImplExt (Bit 0))
               : Action ty tImplExt (Bit 0) :=
      LetA readRp : Option (LineReadRp r.(regionLineCfg)) <- readRpAct ;
      If (Not (##readRp`"valid")) Then (
        LetA valid : Bool <- validAct ;
        If #valid Then (
          LetA rp : LineReadRp r.(regionLineCfg) <- getRpAct ;
          ackAndStoreAct rp
        ) ;
        Retv
      ) ;
      Retv.

    Definition implExternalFetchLineRpPort
               : Action ty tImplExt (Bit 0) :=
      implExternalRpPort
        implExternalFetchLineReadRp
        (liftAction fetchPath (Recv "valid" pFetchLineReadRpValid (fun v => Return #v)))
        (liftAction child0Path (@externalFetchLineReadRp dom r ty))
        (fun rp => liftAction fetchPath (
          Act (Send pFetchLineReadRpReady ($0 : Expr ty (Bit 0)) Retv) ;
          WriteReg pExtFetchReadRp (mkSome #rp) Retv)).

    (* 2. Data Port Low-Level & Single-Line Actions *)

    Definition implExternalLineReadRq
               (addr : ty Addr)
               : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      LetIf extRdy <- If (Not (##portRq`"valid")) Then (
        WriteReg pExtPortRq (mkSome (UNION (PortRqList r.(regionLineCfg), "Read" ::= #addr))) (
        Recv "extRdy" pLineReadRqReady (fun extRdy => Return #extRdy)
      )) ;
      Return (And [ #extRdy ; Not (##portRq`"valid") ])).

    Definition implExternalLineReadRp
               : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg))) :=
      ReadReg "readRp" pExtReadRp (fun v => Return #v).

    Definition implExternalLineDeqRp
               : Action ty tImplExt (Bit 0) :=
      WriteReg pExtReadRp ConstDef Retv.

    Definition implExternalReadSavedRp
               : Action ty tImplExt (LineReadRp r.(regionLineCfg)) :=
      ReadReg "savedRp" pExtSavedRp (fun v => Return #v).

    Definition implExternalWriteSavedRp
               (rp : ty (LineReadRp r.(regionLineCfg)))
               : Action ty tImplExt (Bit 0) :=
      WriteReg pExtSavedRp #rp Retv.

    Definition implExternalLineWriteRq
               (rq : ty (LineWriteRq r.(regionLineCfg)))
               : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      LetIf extRdy <- If (Not (##portRq`"valid")) Then (
        WriteReg pExtPortRq (mkSome (UNION (PortRqList r.(regionLineCfg), "Write" ::= #rq))) (
        Recv "extRdy" pLineWriteRqReady (fun extRdy => Return #extRdy)
      )) ;
      Return (And [ #extRdy ; Not (##portRq`"valid") ])).

    Definition implExternalLineRpPort
               : Action ty tImplExt (Bit 0) :=
      implExternalRpPort
        implExternalLineReadRp
        (Recv "valid" pLineReadRpValid (fun valid => Return #valid))
        (liftAction child0Path (@externalLineReadRp dom r ty))
        (fun rp =>
          Act (Send pLineReadRpReady ($0 : Expr ty (Bit 0)) Retv) ;
          WriteReg pExtReadRp (mkSome #rp) Retv).

    Definition implExternalLineReadRqPort
               : Action ty tImplExt (Bit 0) :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Read" ]) Then (
        Let addr : Addr <- (##portRq`"data") `! "Read" ;
        Act (liftAction child0Path (externalLineReadRq r addr)) ;
        WriteReg pExtPortRq ConstDef Retv
      ) ;
      Retv).

    Definition implExternalLineWriteRqPort
               : Action ty tImplExt (Bit 0) :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Write" ]) Then (
        Let rq : LineWriteRq r.(regionLineCfg) <- (##portRq`"data") `! "Write" ;
        Act (liftAction child0Path (externalLineWrite r rq)) ;
        WriteReg pExtPortRq ConstDef Retv
      ) ;
      Retv).

    Definition implExternalIsIdle : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      Return (Not (##portRq`"valid"))).

  End ImplExternalMemRegionActions.

  Arguments implExternalFetchLineReadRq r [ty] addr.
  Arguments implExternalFetchLineReadRp r {ty}.
  Arguments implExternalFetchLineDeqRp r {ty}.
  Arguments implExternalFetchLineRpPort r {ty}.
  Arguments implExternalLineReadRq r [ty] addr.
  Arguments implExternalLineReadRp r {ty}.
  Arguments implExternalLineDeqRp r {ty}.
  Arguments implExternalReadSavedRp r {ty}.
  Arguments implExternalWriteSavedRp r [ty] rp.
  Arguments implExternalLineWriteRq r [ty] rq.
  Arguments implExternalLineRpPort r {ty}.
  Arguments implExternalLineReadRqPort r {ty}.
  Arguments implExternalLineWriteRqPort r {ty}.
  Arguments implExternalIsIdle r {ty}.

  (* ===========================================================================
   * Single-Line Implementation Actions for CustomMem
   * =========================================================================== *)

  Section ImplCustomMemRegionActions.
    Variable r : MemRegion.
    Variable children : list (Tree DomainElem).
    Variable readAction : forall ty, ty Addr ->
                          ty (Array (cfgLineBytes r.(regionLineCfg)) Bool) ->
                          Action ty (customMemRegionTree r children) (LineReadRp r.(regionLineCfg)).
    Variable writeAction : forall ty, ty (LineWriteRq r.(regionLineCfg)) ->
                           Action ty (customMemRegionTree r children) (Bit 0).
    Variable ty : Kind -> Type.

    Local Definition tImplCust : Tree DomainElem :=
      implCustomMemRegionTree r children.

    Local Definition pCustReadRp  : RegPath tImplCust := Eval cbn in (getChildRegPathTree tImplCust "readRp").
    Local Definition pCustSavedRp : RegPath tImplCust := Eval cbn in (getChildRegPathTree tImplCust "savedRp").

    Definition implCustomLineReadRq
               (addr : ty Addr)
               (dataMask : ty (Array (cfgLineBytes r.(regionLineCfg)) Bool))
               : Action ty tImplCust Bool :=
      ReadReg "readRp" pCustReadRp (fun readRp =>
      Let rdy : Bool <- Not (##readRp`"valid") ;
      If #rdy Then (
        LetA rp : LineReadRp r.(regionLineCfg) <-
          liftAction child0Path (readAction addr dataMask) ;
        WriteReg pCustReadRp (mkSome #rp) Retv
      ) ;
      Return #rdy).

    Definition implCustomLineReadRp
               : Action ty tImplCust (Option (LineReadRp r.(regionLineCfg))) :=
      ReadReg "readRp" pCustReadRp (fun v => Return #v).

    Definition implCustomLineDeqRp
               : Action ty tImplCust (Bit 0) :=
      WriteReg pCustReadRp ConstDef Retv.

    Definition implCustomReadSavedRp
               : Action ty tImplCust (LineReadRp r.(regionLineCfg)) :=
      ReadReg "savedRp" pCustSavedRp (fun v => Return #v).

    Definition implCustomWriteSavedRp
               (rp : ty (LineReadRp r.(regionLineCfg)))
               : Action ty tImplCust (Bit 0) :=
      WriteReg pCustSavedRp #rp Retv.

    Definition implCustomLineWriteRq
               (rq : ty (LineWriteRq r.(regionLineCfg)))
               : Action ty tImplCust Bool :=
      Act (liftAction child0Path (writeAction rq)) ;
      Return (ConstBool true).

  End ImplCustomMemRegionActions.

  Arguments implCustomLineReadRq r children readAction [ty] addr dataMask.
  Arguments implCustomLineReadRp r children {ty}.
  Arguments implCustomLineDeqRp r children {ty}.
  Arguments implCustomReadSavedRp r children {ty}.
  Arguments implCustomWriteSavedRp r children [ty] rp.
  Arguments implCustomLineWriteRq r children writeAction [ty] rq.

  (* ===========================================================================
   * Unified Single-Line & Region Helper Dispatch
   * =========================================================================== *)

  Definition implMemRegionFetchRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => implExternalFetchLineReadRq r addr
    | CustomMem _ _ _ _ => Return (ConstBool true)
    end.

  Definition implMemRegionFetchRp
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             : Action ty (implMemRegionTree r) (Option FetchPacket) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (Option FetchPacket) with
    | ExternalMem =>
        LetA rpOpt : Option (LineReadRp r.(regionLineCfg)) <- @implExternalFetchLineReadRp r ty ;
        LetIf resOpt : Option FetchPacket <-
          If (##rpOpt`"valid") Then (
            Let rp  : LineReadRp r.(regionLineCfg) <- ##rpOpt`"data" ;
            Let pkt : FetchPacket                  <- memExtractFetchPacket r addr rp ;
            Return (mkSome #pkt)
          ) ;
        Return #resOpt
    | CustomMem _ _ _ _ =>
        Return (mkSome (ConstDef : Expr ty FetchPacket))
    end.

  Definition implMemRegionFetchDeqRp
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (Bit 0) with
    | ExternalMem => @implExternalFetchLineDeqRp r ty
    | CustomMem _ _ _ _ => Retv
    end.

  Definition implMemRegionLineReadRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             (dataMask : ty (Array (lineBytes r) Bool))
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => implExternalLineReadRq r addr
    | CustomMem children readAct _ _ => implCustomLineReadRq r children readAct addr dataMask
    end.

  Definition implMemRegionLineReadRp
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) (Option (LineReadRp r.(regionLineCfg))) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (Option (LineReadRp r.(regionLineCfg))) with
    | ExternalMem => @implExternalLineReadRp r ty
    | CustomMem children _ _ _ => @implCustomLineReadRp r children ty
    end.

  Definition implMemRegionLineDeqRp
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (Bit 0) with
    | ExternalMem => @implExternalLineDeqRp r ty
    | CustomMem children _ _ _ => @implCustomLineDeqRp r children ty
    end.

  Definition implMemRegionReadSavedRp
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) (LineReadRp r.(regionLineCfg)) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (LineReadRp r.(regionLineCfg)) with
    | ExternalMem => @implExternalReadSavedRp r ty
    | CustomMem children _ _ _ => @implCustomReadSavedRp r children ty
    end.

  Definition implMemRegionWriteSavedRp
             (r : MemRegion)
             {ty : Kind -> Type}
             (rp : ty (LineReadRp r.(regionLineCfg)))
             : Action ty (implMemRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (Bit 0) with
    | ExternalMem => implExternalWriteSavedRp r rp
    | CustomMem children _ _ _ => implCustomWriteSavedRp r children rp
    end.

  Definition implMemRegionLineWriteRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => implExternalLineWriteRq r rq
    | CustomMem children _ writeAct _ => implCustomLineWriteRq r children writeAct rq
    end.

  Definition implMemRegionIsIdle
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => @implExternalIsIdle r ty
    | CustomMem _ _ _ _ => Return (ConstBool true)
    end.

  Arguments implMemRegionFetchRq r [ty] addr.
  Arguments implMemRegionFetchRp r [ty] addr.
  Arguments implMemRegionFetchDeqRp r {ty}.
  Arguments implMemRegionLineReadRq r [ty] addr dataMask.
  Arguments implMemRegionLineReadRp r {ty}.
  Arguments implMemRegionLineDeqRp r {ty}.
  Arguments implMemRegionReadSavedRp r {ty}.
  Arguments implMemRegionWriteSavedRp r [ty] rp.
  Arguments implMemRegionLineWriteRq r [ty] rq.
  Arguments implMemRegionIsIdle r {ty}.

  Section ImplMemRegionHelpers.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Local Definition tImplReg : Tree DomainElem := implMemRegionTree r.

    Definition implMemRegionReadRq0
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplReg (Pair Bool Bool) :=
      LetL dataMasks : Pair (Array (lineBytes r) Bool) (Array (lineBytes r) Bool) <- memDataMasks r #addr #memSize ;
      Let  addr0     : Addr                     <- memLineAddr r #addr ;
      Let  dataMask0 : Array (lineBytes r) Bool <- ##dataMasks`"fst" ;
      Let  crosses   : Bool                     <- memCrossesLine r #addr #memSize ;
      LetA rdy0      : Bool                     <- implMemRegionLineReadRq r addr0 dataMask0 ;
      @Return _ _ (Pair Bool Bool) (STRUCT { "fst" ::= #rdy0 ; "snd" ::= #crosses }).

    Definition implMemRegionReadRp0 : Action ty tImplReg Bool :=
      LetA rp0Opt : Option (LineReadRp r.(regionLineCfg)) <- implMemRegionLineReadRp r ;
      If (##rp0Opt`"valid") Then (
        Let rp0 : LineReadRp r.(regionLineCfg) <- ##rp0Opt`"data" ;
        Act (implMemRegionLineDeqRp r) ;
        implMemRegionWriteSavedRp r rp0
      ) ;
      Return (##rp0Opt`"valid").

    Definition implMemRegionReadRq1
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplReg Bool :=
      LetL dataMasks : Pair (Array (lineBytes r) Bool) (Array (lineBytes r) Bool) <- memDataMasks r #addr #memSize ;
      Let  addr1     : Addr                     <- memNextLineAddr r #addr ;
      Let  dataMask1 : Array (lineBytes r) Bool <- ##dataMasks`"snd" ;
      implMemRegionLineReadRq r addr1 dataMask1.

    Definition implMemRegionReadRp1
               (is2Line : ty Bool)
               (addr : ty Addr)
               : Action ty tImplReg Bool :=
      LetA lastRpOpt : Option (LineReadRp r.(regionLineCfg)) <- implMemRegionLineReadRp r ;
      If (##lastRpOpt`"valid") Then (
        LetA rp0    : LineReadRp r.(regionLineCfg) <- implMemRegionReadSavedRp r ;
        Let  lastRp : LineReadRp r.(regionLineCfg) <- ##lastRpOpt`"data" ;
        Let  rp     : LineReadRp r.(regionLineCfg) <-
          ITE #is2Line
              (memMergeLineReadRp r #addr #rp0 #lastRp)
              #lastRp ;
        Act (implMemRegionLineDeqRp r) ;
        implMemRegionWriteSavedRp r rp
      ) ;
      Return (##lastRpOpt`"valid").

    Definition implMemRegionReadRp
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplReg FullCapWithTag :=
      LetA rp  : LineReadRp r.(regionLineCfg) <- implMemRegionReadSavedRp r ;
      LetL res : FullCapWithTag               <- memExtractReadCap r #addr #memSize #rp ;
      Return #res.

    Definition implMemRegionWriteRq0
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplReg (Pair Bool Bool) :=
      LetL rqs     : Pair (LineWriteRq r.(regionLineCfg)) (LineWriteRq r.(regionLineCfg)) <-
        memBuildLineWriteRqs r #addr #stVal #memSize ;
      Let  rq0     : LineWriteRq r.(regionLineCfg) <- ##rqs`"fst" ;
      Let  crosses : Bool                          <- memCrossesLine r #addr #memSize ;
      LetA rdy0    : Bool                          <- implMemRegionLineWriteRq r rq0 ;
      @Return _ _ (Pair Bool Bool) (STRUCT { "fst" ::= #rdy0 ; "snd" ::= #crosses }).

    Definition implMemRegionWriteRq1
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplReg Bool :=
      LetL rqs : Pair (LineWriteRq r.(regionLineCfg)) (LineWriteRq r.(regionLineCfg)) <-
        memBuildLineWriteRqs r #addr #stVal #memSize ;
      Let  rq1 : LineWriteRq r.(regionLineCfg) <- ##rqs`"snd" ;
      implMemRegionLineWriteRq r rq1.

  End ImplMemRegionHelpers.

  Arguments implMemRegionReadRq0 r [ty] addr memSize.
  Arguments implMemRegionReadRp0 r {ty}.
  Arguments implMemRegionReadRq1 r [ty] addr memSize.
  Arguments implMemRegionReadRp1 r [ty] is2Line addr.
  Arguments implMemRegionReadRp r [ty] addr memSize.
  Arguments implMemRegionWriteRq0 r [ty] addr stVal memSize.
  Arguments implMemRegionWriteRq1 r [ty] addr stVal memSize.

  Definition implMemRegionFetchRpActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @implExternalFetchLineRpPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionDataReadRpActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @implExternalLineRpPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionDataReadRqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @implExternalLineReadRqPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionDataWriteRqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @implExternalLineWriteRqPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionIrqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) Bool) :=
    map (fun act ty => liftToImplRegion (act ty))
        (memRegionIrqActions dom r).

  Definition implMemRegionFenceIAckActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    map (fun act ty => liftToImplRegion (act ty))
        (memRegionFenceIAckActions dom r).

  (* ===========================================================================
   * Composite Implementation Memory Tree & System Routing
   * =========================================================================== *)

  Definition implRegionsChildren := regionsTreeChildren implMemRegionTree.
  Definition implRegionsTree     := regionsTree implMemRegionTree.

  Definition implRegionsNthRegionAction
    {ty : Kind -> Type}
    (idx : nat)
    (regions : list MemRegion)
    (r0 : MemRegion)
    (pf : nth_error regions idx = Some r0)
    {k : Kind}
    (act : Action ty (memRegionTree dom r0) k)
    : Action ty (implRegionsTree regions) k :=
    genNthRegionAction implMemRegionTree idx regions r0 pf (liftToImplRegion act).

  Arguments implRegionsNthRegionAction {ty} idx regions r0 pf {k} act.

  Definition implCollectRegionActions {k : Kind} :=
    @genCollectRegionActions implMemRegionTree k.

  Definition implCollectIrqActions         := implCollectRegionActions implMemRegionIrqActions.
  Definition implCollectFetchRpActions     := implCollectRegionActions implMemRegionFetchRpActions.
  Definition implCollectDataReadRpActions  := implCollectRegionActions implMemRegionDataReadRpActions.
  Definition implCollectDataReadRqActions  := implCollectRegionActions implMemRegionDataReadRqActions.
  Definition implCollectDataWriteRqActions := implCollectRegionActions implMemRegionDataWriteRqActions.
  Definition implCollectFenceIAckActions   := implCollectRegionActions implMemRegionFenceIAckActions.

  Section ImplRegionsRouter.
    Variable ty : Kind -> Type.

    Definition implRegionsFetchRq
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) Bool :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionFetchRq r addr)
        (@Or _ _) addr regions.

    Definition implRegionsFetchRp
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) (Option FetchPacket) :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionFetchRp r addr)
        (@Or _ _) addr regions.

    Definition implRegionsFetchDeqRp
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) (Bit 0) :=
      genRouteRegionUnitAction implMemRegionTree (fun r => @implMemRegionFetchDeqRp r ty)
        addr regions.

    Definition implRegionsReadRq0
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (implRegionsTree regions) (Pair Bool Bool) :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionReadRq0 r addr memSize)
        (@Or _ _) addr regions.

    Definition implRegionsReadRp0
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) Bool :=
      genRouteRegionAction implMemRegionTree (fun r => @implMemRegionReadRp0 r ty)
        (@Or _ _) addr regions.

    Definition implRegionsReadRq1
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (implRegionsTree regions) Bool :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionReadRq1 r addr memSize)
        (@Or _ _) addr regions.

    Definition implRegionsReadRp1
               (regions : list MemRegion)
               (is2Line : ty Bool)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) Bool :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionReadRp1 r is2Line addr)
        (@Or _ _) addr regions.

    Definition implRegionsReadRp
               (regions : list MemRegion)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (implRegionsTree regions) FullCapWithTag :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionReadRp r addr memSize)
        (@Or _ _) addr regions.

    Definition implRegionsWriteRq0
               (regions : list MemRegion)
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (implRegionsTree regions) (Pair Bool Bool) :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionWriteRq0 r addr stVal memSize)
        (@Or _ _) addr regions.

    Definition implRegionsWriteRq1
               (regions : list MemRegion)
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty (implRegionsTree regions) Bool :=
      genRouteRegionAction implMemRegionTree (fun r => implMemRegionWriteRq1 r addr stVal memSize)
        (@Or _ _) addr regions.

    Definition implRegionsIsIdle
               (regions : list MemRegion)
               : Action ty (implRegionsTree regions) Bool :=
      genFoldRegionActions implMemRegionTree (fun r => @implMemRegionIsIdle r ty)
        (@And _ _) regions.

    Definition implRegionsReadFenceIWait
               (regions : list MemRegion)
               : Action ty (implRegionsTree regions) Bool :=
      genFoldRegionActions implMemRegionTree (fun r => liftToImplRegion (memRegionReadFenceIWait r))
        (@Or _ _) regions.

    Definition implRegionsSendFenceIRq
               (regions : list MemRegion)
               : Action ty (implRegionsTree regions) (Bit 0) :=
      genFoldRegionUnitActions implMemRegionTree (fun r => liftToImplRegion (memRegionSendFenceIRq r))
        regions.

  End ImplRegionsRouter.

  Arguments implRegionsIsIdle {ty} regions.
  Arguments implRegionsReadFenceIWait {ty} regions.
  Arguments implRegionsSendFenceIRq {ty} regions.

  Definition implMemTree (regions : list MemRegion) : Tree DomainElem :=
    Node ""
      [ implRegionsTree regions ;
        Leaf "state"     (dom, EReg (Build_Reg MemState (Some (getDefault _)) false)) ;
        Leaf "requester" (dom, EReg (Build_Reg Requester (Some (getDefault _)) false)) ].

  Definition implNthRegionAction
    {ty : Kind -> Type}
    (idx : nat)
    (regions : list MemRegion)
    (r0 : MemRegion)
    (pf : nth_error regions idx = Some r0)
    {k : Kind}
    (act : Action ty (memRegionTree dom r0) k)
    : Action ty (implMemTree regions) k :=
    liftAction child0Path (implRegionsNthRegionAction idx regions r0 pf act).

  Arguments implNthRegionAction {ty} idx regions r0 pf {k} act.

  Section ImplMemModel.
    Variable revConfig : RevConfig.
    Variable regions : list MemRegion.

    Local Abbreviation implMemTree := (implMemTree regions).

    Local Definition pMemState     : RegPath implMemTree := Eval cbn in (getChildRegPathTree implMemTree "state").
    Local Definition pMemRequester : RegPath implMemTree := Eval cbn in (getChildRegPathTree implMemTree "requester").

    Section Ty.
      Variable ty : Kind -> Type.

      Local Definition liftRevoker
        (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions)
        (k : Kind)
        (a : Action ty (memRegionTree dom (@revokerRegion dom (implRevokerExtraChildren dom) regions rev)) k)
        : Action ty implMemTree k :=
        implNthRegionAction rev.(revokerIdx) regions (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a.

      Arguments liftRevoker rev k a : clear implicits.

      (* Universal 6-State Memory Pipeline Actions on implMemTree *)

      Definition implMemReadRq
                 (req : MemRequester)
                 (addr : ty Addr)
                 (memSize : ty (Bit LgLgNumBytesFullCapSz))
                 : Action ty implMemTree Bool :=
        ReadReg "state" pMemState (fun state =>
        LetIf rdy : Bool <-
          If (##state `? "Idle") Then (
            LetA res     : Pair Bool Bool <- liftAction child0Path (implRegionsReadRq0 regions addr memSize) ;
            Let  rdy0    : Bool           <- ##res`"fst" ;
            Let  crosses : Bool           <- ##res`"snd" ;
            If #rdy0 Then (
              Act (WriteReg pMemState (UNION (MemStateList, "ReadRq0Sent" ::= STRUCT {
                "crosses" ::= #crosses ;
                "addr"    ::= #addr ;
                "memSize" ::= #memSize
              })) Retv) ;
              WriteReg pMemRequester (mkRequester req) Retv
            ) ;
            Return #rdy0
          ) ;
        Return #rdy).

      Definition implMemReadRp0 : Action ty implMemTree (Bit 0) :=
        ReadReg "state" pMemState (fun state =>
        Let rq0Info : MemReadRq0 <- ##state `! "ReadRq0Sent" ;
        If (And [ ##state `? "ReadRq0Sent" ; ##rq0Info`"crosses" ]) Then (
          Let  addr : Addr <- ##rq0Info`"addr" ;
          LetA ok   : Bool <- liftAction child0Path (implRegionsReadRp0 regions addr) ;
          If #ok Then (
            WriteReg pMemState (UNION (MemStateList, "ReadRp0Recv" ::= STRUCT {
              "addr"    ::= #addr ;
              "memSize" ::= ##rq0Info`"memSize"
            })) Retv
          ) ;
          Retv
        ) ;
        Retv).

      Definition implMemReadRq1 : Action ty implMemTree (Bit 0) :=
        ReadReg "state" pMemState (fun state =>
        If (##state `? "ReadRp0Recv") Then (
          Let  rp0Info : MemReadRp0                <- ##state `! "ReadRp0Recv" ;
          Let  addr    : Addr                      <- ##rp0Info`"addr" ;
          Let  memSize : Bit LgLgNumBytesFullCapSz <- ##rp0Info`"memSize" ;
          LetA rdy1    : Bool                      <- liftAction child0Path (implRegionsReadRq1 regions addr memSize) ;
          If #rdy1 Then (
            WriteReg pMemState (UNION (MemStateList, "ReadRq1Sent" ::= #addr)) Retv
          ) ;
          Retv
        ) ;
        Retv).

      Definition implMemReadRp1 : Action ty implMemTree (Bit 0) :=
        ReadReg "state" pMemState (fun state =>
        Let rq0Info : MemReadRq0 <- ##state `! "ReadRq0Sent" ;
        Let is1Line : Bool       <- And [ ##state `? "ReadRq0Sent" ; Not (##rq0Info`"crosses") ] ;
        Let is2Line : Bool       <- ##state `? "ReadRq1Sent" ;
        If (Or [ #is1Line ; #is2Line ]) Then (
          Let  addr : Addr <- ITE #is2Line (##state `! "ReadRq1Sent") (##rq0Info`"addr") ;
          LetA ok   : Bool <- liftAction child0Path (implRegionsReadRp1 regions is2Line addr) ;
          If #ok Then (
            WriteReg pMemState (UNION (MemStateList, "ReadRp1Recv" ::= ($0 : Expr ty (Bit 0)))) Retv
          ) ;
          Retv
        ) ;
        Retv).

      Definition implMemReadRp
                 (req : MemRequester)
                 (addr : ty Addr)
                 (memSize : ty (Bit LgLgNumBytesFullCapSz))
                 : Action ty implMemTree (Option FullCapWithTag) :=
        ReadReg "state" pMemState (fun state =>
        ReadReg "requester" pMemRequester (fun requester =>
        LetIf resOpt : Option FullCapWithTag <-
          If (And [ ##state `? "ReadRp1Recv" ; isRequesterMatch requester req ]) Then (
            LetA res : FullCapWithTag <- liftAction child0Path (implRegionsReadRp regions addr memSize) ;
            Return (mkSome #res)
          ) ;
        Return #resOpt)).

      Definition implMemDeqRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
        WriteReg pMemState (UNION (MemStateList, "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

      Definition implMemWrite
                 (addr : ty Addr)
                 (stVal : ty FullCapWithTag)
                 (memSize : ty (Bit LgLgNumBytesFullCapSz))
                 : Action ty implMemTree Bool :=
        ReadReg "state" pMemState (fun state =>
        LetIf rdy : Bool <-
          If (##state `? "Idle") Then (
            LetA res     : Pair Bool Bool <- liftAction child0Path (implRegionsWriteRq0 regions addr stVal memSize) ;
            Let  rdy0    : Bool           <- ##res`"fst" ;
            Let  crosses : Bool           <- ##res`"snd" ;
            If (And [ #rdy0 ; #crosses ]) Then (
              WriteReg pMemState (UNION (MemStateList, "Write0Sent" ::= STRUCT {
                "addr"    ::= #addr ;
                "stVal"   ::= #stVal ;
                "memSize" ::= #memSize
              })) Retv
            ) ;
            Return #rdy0
          ) ;
        Return #rdy).

      Definition implMemWriteRq1 : Action ty implMemTree (Bit 0) :=
        ReadReg "state" pMemState (fun state =>
        If (##state `? "Write0Sent") Then (
          Let  w0      : MemWrite0                 <- ##state `! "Write0Sent" ;
          Let  addr    : Addr                      <- ##w0`"addr" ;
          Let  stVal   : FullCapWithTag            <- ##w0`"stVal" ;
          Let  memSize : Bit LgLgNumBytesFullCapSz <- ##w0`"memSize" ;
          LetA rdy1    : Bool                      <- liftAction child0Path (implRegionsWriteRq1 regions addr stVal memSize) ;
          If #rdy1 Then (
            WriteReg pMemState (UNION (MemStateList, "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
          ) ;
          Retv
        ) ;
        Retv).

      Definition implMemIsIdle : Action ty implMemTree Bool :=
        ReadReg "state" pMemState (fun state =>
        LetA regionsIdle : Bool <- liftAction child0Path (implRegionsIsIdle regions) ;
        Return (And [ ##state `? "Idle" ; #regionsIdle ])).

      Definition implMemCollectIrqActions : list (Action ty implMemTree Bool) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectIrqActions regions).

      Definition implMemCollectFetchRpActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectFetchRpActions regions).

      Definition implMemCollectDataReadRpActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectDataReadRpActions regions) ++
        [ (Act implMemReadRp0 ; implMemReadRp1) ].

      Definition implMemCollectDataReadRqActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectDataReadRqActions regions).

      Definition implMemCollectDataWriteRqActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectDataWriteRqActions regions).

      Definition implMemCollectDataCrossLineActions : list (Action ty implMemTree (Bit 0)) :=
        [ implMemWriteRq1 ; implMemReadRq1 ].

      Definition implMemCollectFenceIAckActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectFenceIAckActions regions).

      (* 1. Revocation Bit Memory Channel *)
      Definition implReadRevBitRqFor (req : MemRequester) (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
        LetL lookup      : RevBitLookup              <- computeRevBitAddr revConfig base ;
        Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
        Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
        implMemReadRq req revByteAddr sz0.

      Definition implGetDeqRevBitRpFor (req : MemRequester) (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
        LetL lookup      : RevBitLookup              <- computeRevBitAddr revConfig base ;
        Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
        Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
        LetA rpOpt       : Option FullCapWithTag     <- implMemReadRp req revByteAddr sz0 ;
        LetIf rOpt : Option Bool <-
          If (##rpOpt`"valid") Then (
            Act (implMemDeqRp revByteAddr) ;
            Let revCap  : FullCapWithTag <- ##rpOpt`"data" ;
            Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
            Let revBit  : Bool           <- extractRevBit lookup #revByte ;
            Return (mkSome #revBit)
          ) Else (
            Return ConstDef
          ) ;
        Return #rOpt.

      (* 2. Memory Write Channel (with store-address snooping for split-phase revoker) *)
      Definition implWriteMem (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions)
                              (addr : ty Addr) (stVal : ty FullCapWithTag)
                              (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
        LetA rdy : Bool <- implMemWrite addr stVal memSize ;
        If #rdy Then (
          liftRevoker rev _ (implRevokerSnoopStore dom addr memSize)
        ) ;
        Return #rdy.

      (* 3. FENCE.I Synchronization Channel *)
      Definition implFenceIReq : Action ty implMemTree Bool :=
        LetA allIdle : Bool <- implMemIsIdle ;
        If #allIdle Then (
          liftAction child0Path (implRegionsSendFenceIRq regions)
        ) ;
        Return #allIdle.

      (* 4. Split-Phase Autonomous Revoker Steps *)
      Definition implRevokerIdleStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        @implRevokerIdle
          dom
          ty
          implMemTree
          (liftRevoker rev)
          (implMemReadRq ReqRevoker).

      Definition implRevokerCapRpRevBitRqStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        Act (@implRevokerWaitCapRp
               dom
               ty
               revConfig
               implMemTree
               (liftRevoker rev)
               (implMemReadRp ReqRevoker)
               implMemDeqRp) ;
        @implRevokerWaitRevBitRq
          dom
          ty
          implMemTree
          (liftRevoker rev)
          (implReadRevBitRqFor ReqRevoker).

      Definition implRevokerRevBitRpWriteCapStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        Act (@implRevokerWaitRevBitRp
               dom
               ty
               implMemTree
               (liftRevoker rev)
               (implGetDeqRevBitRpFor ReqRevoker)) ;
        @implRevokerWriteCap
          dom
          ty
          implMemTree
          (liftRevoker rev)
          (fun addr stVal sz => implMemWrite addr stVal sz).

      (* 5. Top-level MemIfc Instance *)
      Definition implMemIfc (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : @MemIfc ty := {|
        memTree            := implMemTree ;
        mem_readInstRq     := fun addr => liftAction child0Path (implRegionsFetchRq regions addr) ;
        mem_getInstRp      := fun addr => liftAction child0Path (implRegionsFetchRp regions addr) ;
        mem_deqInstRp      := fun addr => liftAction child0Path (implRegionsFetchDeqRp regions addr) ;
        mem_readMemRq      := implMemReadRq ReqDataMem ;
        mem_getMemRp       := implMemReadRp ReqDataMem ;
        mem_deqMemRp       := implMemDeqRp ;
        mem_readRevBitRq   := implReadRevBitRqFor ReqDataMem ;
        mem_getDeqRevBitRp := implGetDeqRevBitRpFor ReqDataMem ;
        mem_writeMem       := implWriteMem rev ;
        mem_fence_req      := fun _ => Return (ConstBool true) ;
        mem_readFenceIWait := liftAction child0Path (implRegionsReadFenceIWait regions) ;
        mem_fenceI_req     := implFenceIReq
      |}.

    End Ty.

  End ImplMemModel.

End ImplDevice.

Arguments implMemRegionExtraChildren dom r k : clear implicits.
Arguments implMemRegionKindTree dom r k : clear implicits.
Arguments implMemRegionTree dom r : clear implicits.
Arguments implRegionsChildren dom regions : clear implicits.
Arguments implRegionsTree dom regions : clear implicits.
Arguments implMemTree dom regions : clear implicits.
Arguments implRegionsNthRegionAction {dom ty} idx regions r0 pf {k} act.
Arguments implNthRegionAction {dom ty} idx regions r0 pf {k} act.
Arguments implMemIfc dom revConfig regions [ty] rev.
Arguments liftToImplRegion {dom ty r k} act.


