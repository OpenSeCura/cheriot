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
  mem_getMemRp     : Action ty memTree (Option FullCapWithTag) ;
  mem_deqMemRp     : Action ty memTree (Bit 0) ;

  (* 3. Revocation Bit Memory Channel *)
  mem_readRevBitRq   : ty (Bit (AddrSz + 1)) -> Action ty memTree Bool ;
  mem_getDeqRevBitRp : ty (Bit (AddrSz + 1)) -> Action ty memTree (Option Bool) ;

  (* 4. Memory Write Channel *)
  mem_writeMem     : ty Addr -> ty FullCapWithTag -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;
  (* No accepted store is still waiting, neither in `state` nor in a region's `portRq`: every
   * store has been accepted by its region's memory or written to its device *)
  mem_noWriteRq    : Action ty memTree Bool ;

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

Definition MemPendingOp : Kind :=
  STRUCT_TYPE {
    "addr"    :: Addr ;
    "memSize" :: Bit LgLgNumBytesFullCapSz ;
    "pkt"     :: CapPacket
  }.

Definition MemStepOp : Kind :=
  STRUCT_TYPE {
    "isSecond" :: Bool ;
    "op"       :: MemPendingOp
  }.

Definition MemReadRqSent : Kind :=
  STRUCT_TYPE {
    "crosses" :: Bool ;
    "step"    :: MemStepOp
  }.

Definition MemStateList : list (string * Kind) :=
  [ ("Idle",        Bit 0) ;
    ("ReadRq",      MemStepOp) ;
    ("ReadRqSent",  MemReadRqSent) ;
    ("ReadRpReady", FullCapWithTag) ;
    ("WriteRq",     MemStepOp) ].

Definition MemState : Kind :=
  TaggedUnion MemStateList.

Definition PortRqList : list (string * Kind) :=
  [ ("Read",  Addr) ;
    ("Write", LineWriteRq) ].

Definition PortRq : Kind :=
  TaggedUnion PortRqList.

(* Result of handing a line read request to a region: whether the region accepted it, and the
 * response if the region answers at once (CustomMem device reads) *)
Definition LineReadRqRes : Kind :=
  STRUCT_TYPE {
    "rdy" :: Bool ;
    "rp"  :: Option LineReadRp
  }.

(* A fetch packet is a whole line *)
Definition memExtractFetchPacket {ty : Kind -> Type} (rp : ty LineReadRp) : Expr ty FetchPacket :=
  FromBit FetchPacket (ToBit (##rp`"data")).

Section ImplDevice.
  Variable dom : string.

  Definition implExternalMemFetchTree : Tree DomainElem :=
    Node "fetch"
      [ Leaf "lineReadRqReady" (dom, ERecv Bool) ;
        Leaf "lineReadRpValid" (dom, ERecv Bool) ;
        Leaf "lineReadRpReady" (dom, ESend (Bit 0)) ;
        Leaf "readRp"          (dom, EReg (Build_Reg (Option LineReadRp) (Some (getDefault _)) false)) ].

  Definition implExternalMemExtraChildren : list (Tree DomainElem) :=
    [ implExternalMemFetchTree ;
      Leaf "lineReadRqReady"  (dom, ERecv Bool) ;
      Leaf "lineWriteRqReady" (dom, ERecv Bool) ;
      Leaf "lineReadRpValid"  (dom, ERecv Bool) ;
      Leaf "lineReadRpReady"  (dom, ESend (Bit 0)) ;
      Leaf "portRq"           (dom, EReg (Build_Reg (Option PortRq) (Some (getDefault _)) false)) ].

  Definition implMemRegionExtraChildren (r : MemRegion) (k : RegionKind r.(regionName)) : list (Tree DomainElem) :=
    match k with
    | ExternalMem => implExternalMemExtraChildren
    | CustomMem _ _ _ _ => []
    end.

  Arguments implMemRegionExtraChildren r k : clear implicits.

  Definition implMemRegionKindTree (r : MemRegion) (k : RegionKind r.(regionName)) : Tree DomainElem :=
    Node r.(regionName) (memRegionKindTree dom r k :: implMemRegionExtraChildren r k).

  Arguments implMemRegionKindTree r k : clear implicits.

  Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
    implMemRegionKindTree r ExternalMem.

  Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
    Node r.(regionName) [ customMemRegionTree r children ].

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
    Local Definition tImplExtFetch := implExternalMemFetchTree.

    Local Definition fetchPath             : NodePath tImplExt      := child1Path.
    Local Definition pLineWriteRqReady     : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineWriteRqReady").
    Local Definition pLineReadRqReady      : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRqReady").
    Local Definition pLineReadRpValid      : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRpValid").
    Local Definition pLineReadRpReady      : SendPath tImplExt      := Eval cbn in (getChildSendPathTree tImplExt "lineReadRpReady").
    Local Definition pExtPortRq            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "portRq").

    Local Definition pFetchLineReadRqReady : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRqReady").
    Local Definition pFetchLineReadRpValid : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRpValid").
    Local Definition pFetchLineReadRpReady : SendPath tImplExtFetch := Eval cbn in (getChildSendPathTree tImplExtFetch "lineReadRpReady").
    Local Definition pExtFetchReadRp       : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "readRp").

    (* 1. Dedicated Fetch Port Actions *)

    Definition implExternalFetchLineReadRq
               (addr : ty Addr)
               : Action ty tImplExt Bool :=
      Let lineAddr : Addr <- memLineAddr #addr ;
      Act (liftAction child0Path (externalFetchLineReadRq r lineAddr)) ;
      liftAction fetchPath (Recv "rdy" pFetchLineReadRqReady (fun rdy => Return #rdy)).

    Definition implExternalFetchLineReadRp
               : Action ty tImplExt (Option LineReadRp) :=
      liftAction fetchPath (ReadReg "readRp" pExtFetchReadRp (fun v => Return #v)).

    Definition implExternalFetchLineDeqRp
               : Action ty tImplExt (Bit 0) :=
      liftAction fetchPath (WriteReg pExtFetchReadRp ConstDef Retv).

    Definition implExternalFetchLineRpPort
               : Action ty tImplExt (Bit 0) :=
      LetA readRp : Option LineReadRp <- implExternalFetchLineReadRp ;
      If (Not (##readRp`"valid")) Then (
        LetA valid : Bool <- liftAction fetchPath (Recv "valid" pFetchLineReadRpValid (fun v => Return #v)) ;
        If #valid Then (
          LetA rp : LineReadRp <- liftAction child0Path (@externalFetchLineReadRp dom r ty) ;
          liftAction fetchPath (
            Act (Send pFetchLineReadRpReady ($0 : Expr ty (Bit 0)) Retv) ;
            WriteReg pExtFetchReadRp (mkSome #rp) Retv)
        ) ;
        Retv
      ) ;
      Retv.

    (* 2. Data Port Actions *)

    (* Staging into `portRq` only checks `portRq`'s own valid bit; the external ready
     * is checked by the port action (`implExternalLineReadRqPort`). *)
    Definition implExternalLineReadRq
               (lineAddr : ty Addr)
               : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (Not (##portRq`"valid")) Then (
        WriteReg pExtPortRq (mkSome (UNION (PortRqList, "Read" ::= #lineAddr))) Retv
      ) ;
      Return (Not (##portRq`"valid"))).

    Definition implExternalLineWriteRq
               (rq : ty LineWriteRq)
               : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (Not (##portRq`"valid")) Then (
        WriteReg pExtPortRq (mkSome (UNION (PortRqList, "Write" ::= maskRegionWriteRq r #rq))) Retv
      ) ;
      Return (Not (##portRq`"valid"))).

    (* Receives the response of the outstanding line read, if it has arrived. The memory calls
     * it only while its data response buffer is empty. *)
    Definition implExternalLineRpPort
               : Action ty tImplExt (Option LineReadRp) :=
      Recv "valid" pLineReadRpValid (fun valid =>
      LetIf rpOpt : Option LineReadRp <-
        If #valid Then (
          LetA rp : LineReadRp <- liftAction child0Path (@externalLineReadRp dom r ty) ;
          Act (Send pLineReadRpReady ($0 : Expr ty (Bit 0)) Retv) ;
          Return (mkSome (maskRegionReadRp r #rp))
        ) ;
      Return #rpOpt).

    (* The port actions send the staged request and read the external ready in the same
     * action; the request leaves `portRq` only once it is accepted (ready = true). *)
    Definition implExternalLineReadRqPort
               : Action ty tImplExt (Bit 0) :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Read" ]) Then (
        Let addr : Addr <- (##portRq`"data") `! "Read" ;
        Act (liftAction child0Path (externalLineReadRq r addr)) ;
        Recv "extRdy" pLineReadRqReady (fun extRdy =>
        If #extRdy Then (
          WriteReg pExtPortRq ConstDef Retv
        ) ;
        Retv)
      ) ;
      Retv).

    Definition implExternalLineWriteRqPort
               : Action ty tImplExt (Bit 0) :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Write" ]) Then (
        Let rq : LineWriteRq <- (##portRq`"data") `! "Write" ;
        Act (liftAction child0Path (externalLineWrite r rq)) ;
        Recv "extRdy" pLineWriteRqReady (fun extRdy =>
        If #extRdy Then (
          WriteReg pExtPortRq ConstDef Retv
        ) ;
        Retv)
      ) ;
      Retv).

    Definition implExternalNoPortWriteRq : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      Return (Not (And [ ##portRq`"valid" ; (##portRq`"data") `? "Write" ]))).

  End ImplExternalMemRegionActions.

  Arguments implExternalFetchLineReadRq r [ty] addr.
  Arguments implExternalFetchLineReadRp r {ty}.
  Arguments implExternalFetchLineDeqRp r {ty}.
  Arguments implExternalFetchLineRpPort r {ty}.
  Arguments implExternalLineReadRq r [ty] lineAddr.
  Arguments implExternalLineWriteRq r [ty] rq.
  Arguments implExternalLineRpPort r {ty}.
  Arguments implExternalLineReadRqPort r {ty}.
  Arguments implExternalLineWriteRqPort r {ty}.
  Arguments implExternalNoPortWriteRq r {ty}.

  (* ===========================================================================
   * Single-Line Implementation Actions for CustomMem
   * =========================================================================== *)

  Section ImplCustomMemRegionActions.
    Variable r : MemRegion.
    Variable children : list (Tree DomainElem).
    Variable readAction : forall ty, ty Addr ->
                          ty (Array LineBytes Bool) ->
                          Action ty (customMemRegionTree r children) LineReadRp.
    Variable writeAction : forall ty, ty LineWriteRq ->
                           Action ty (customMemRegionTree r children) (Bit 0).
    Variable ty : Kind -> Type.

    Local Definition tImplCust : Tree DomainElem :=
      implCustomMemRegionTree r children.

    (* The device read happens at once; its response goes to the memory's data response buffer *)
    Definition implCustomLineReadRq
               (lineAddr : ty Addr)
               (dataMask : ty (Array LineBytes Bool))
               : Action ty tImplCust LineReadRqRes :=
      LetA rp    : LineReadRp        <- liftAction child0Path (readAction lineAddr dataMask) ;
      Let  rpOpt : Option LineReadRp <- mkSome (maskRegionReadRp r #rp) ;
      @Return _ _ LineReadRqRes (STRUCT {
        "rdy" ::= Const ty Bool true ;
        "rp"  ::= #rpOpt
      }).

    Definition implCustomLineWriteRq
               (rq : ty LineWriteRq)
               : Action ty tImplCust Bool :=
      Let rqM : LineWriteRq <- maskRegionWriteRq r #rq ;
      Act (liftAction child0Path (writeAction rqM)) ;
      Return (ConstBool true).

  End ImplCustomMemRegionActions.

  Arguments implCustomLineReadRq r children readAction [ty] lineAddr dataMask.
  Arguments implCustomLineWriteRq r children writeAction [ty] rq.

  (* ===========================================================================
   * Unified Single-Line & Region Helper Dispatch
   * =========================================================================== *)

  Definition implMemRegionFetchLineReadRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => implExternalFetchLineReadRq r addr
    | CustomMem _ _ _ _ => Return (ConstBool true)
    end.

  Definition implMemRegionFetchLineReadRp
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) (Option FetchPacket) :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) (Option FetchPacket) with
    | ExternalMem =>
        LetA rpOpt : Option LineReadRp <- @implExternalFetchLineReadRp r ty ;
        LetIf resOpt : Option FetchPacket <-
          If (##rpOpt`"valid") Then (
            Let rp  : LineReadRp  <- ##rpOpt`"data" ;
            Let pkt : FetchPacket <- memExtractFetchPacket rp ;
            Return (mkSome #pkt)
          ) ;
        Return #resOpt
    | CustomMem _ _ _ _ =>
        Return (mkSome (ConstDef : Expr ty FetchPacket))
    end.

  Definition implMemRegionFetchLineDeqRp
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
             (lineAddr : ty Addr)
             (dataMask : ty (Array LineBytes Bool))
             : Action ty (implMemRegionTree r) LineReadRqRes :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) LineReadRqRes with
    | ExternalMem =>
        LetA rdy : Bool <- implExternalLineReadRq r lineAddr ;
        @Return _ _ LineReadRqRes (STRUCT {
          "rdy" ::= #rdy ;
          "rp"  ::= Const ty (Option LineReadRp) (getDefault _)
        })
    | CustomMem children readAct _ _ => implCustomLineReadRq r children readAct lineAddr dataMask
    end.

  Definition implMemRegionLineWriteRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (rq : ty LineWriteRq)
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => implExternalLineWriteRq r rq
    | CustomMem children _ writeAct _ => implCustomLineWriteRq r children writeAct rq
    end.

  Definition implMemRegionNoPortWriteRq
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (implMemRegionKindTree r k) Bool with
    | ExternalMem => @implExternalNoPortWriteRq r ty
    | CustomMem _ _ _ _ => Return (ConstBool true)
    end.

  Arguments implMemRegionFetchLineReadRq r [ty] addr.
  Arguments implMemRegionFetchLineReadRp r {ty}.
  Arguments implMemRegionFetchLineDeqRp r {ty}.
  Arguments implMemRegionLineReadRq r [ty] lineAddr dataMask.
  Arguments implMemRegionLineWriteRq r [ty] rq.
  Arguments implMemRegionNoPortWriteRq r {ty}.

  Definition implMemRegionFetchLineRpPorts
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @implExternalFetchLineRpPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionLineRpPorts
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Option LineReadRp)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Option LineReadRp)) with
    | ExternalMem => [ (fun ty => @implExternalLineRpPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionLineReadRqPorts
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (implMemRegionKindTree r k) (Bit 0)) with
    | ExternalMem => [ (fun ty => @implExternalLineReadRqPort r ty) ]
    | CustomMem _ _ _ _ => []
    end.

  Definition implMemRegionLineWriteRqPorts
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

  Definition implCollectIrqActions       := implCollectRegionActions implMemRegionIrqActions.
  Definition implCollectFetchLineRpPorts := implCollectRegionActions implMemRegionFetchLineRpPorts.
  Definition implCollectLineRpPorts      := implCollectRegionActions implMemRegionLineRpPorts.
  Definition implCollectLineReadRqPorts  := implCollectRegionActions implMemRegionLineReadRqPorts.
  Definition implCollectLineWriteRqPorts := implCollectRegionActions implMemRegionLineWriteRqPorts.
  Definition implCollectFenceIAckActions := implCollectRegionActions implMemRegionFenceIAckActions.

  Section ImplRegionsRouter.
    Variable ty : Kind -> Type.

    (* Whether some region owns the line at `addr`. An unmapped line behaves like a region
     * that answers at once, as in the spec: a fetch or data read returns zeros and a write
     * is dropped, so an access to it never stalls. *)
    Definition isMappedAddr (regions : list MemRegion) (addr : Expr ty Addr) : Expr ty Bool :=
      Or (map (fun r => isRegionAddr r addr) regions).

    Definition implRegionsFetchLineReadRq
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) Bool :=
      LetA rdy : Bool <- genRouteRegionAction implMemRegionTree (fun r => implMemRegionFetchLineReadRq r addr)
                           (@Or _ _) addr regions ;
      Return (Or [ #rdy ; Not (isMappedAddr regions #addr) ]).

    Definition implRegionsFetchLineReadRp
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) (Option FetchPacket) :=
      LetA rpOpt : Option FetchPacket <- genRouteRegionAction implMemRegionTree (fun r => @implMemRegionFetchLineReadRp r ty)
                                           (@Or _ _) addr regions ;
      Return (ITE (isMappedAddr regions #addr) #rpOpt (mkSome (ConstDef : Expr ty FetchPacket))).

    Definition implRegionsFetchLineDeqRp
               (regions : list MemRegion)
               (addr : ty Addr)
               : Action ty (implRegionsTree regions) (Bit 0) :=
      genRouteRegionUnitAction implMemRegionTree (fun r => @implMemRegionFetchLineDeqRp r ty)
        addr regions.

    (* Single-line data requests, each routed by its line address *)
    Definition implRegionsLineReadRq
               (regions : list MemRegion)
               (lineAddr : ty Addr)
               (dataMask : ty (Array LineBytes Bool))
               : Action ty (implRegionsTree regions) LineReadRqRes :=
      LetA res : LineReadRqRes <- genRouteRegionAction implMemRegionTree (fun r => implMemRegionLineReadRq r lineAddr dataMask)
                                    (@Or _ _) lineAddr regions ;
      Let  zeroRp      : Option LineReadRp <- mkSome (ConstDef : Expr ty LineReadRp) ;
      Let  unmappedRes : LineReadRqRes     <- STRUCT {
        "rdy" ::= Const ty Bool true ;
        "rp"  ::= #zeroRp
      } ;
      Return (ITE (isMappedAddr regions #lineAddr) #res #unmappedRes).

    Definition implRegionsLineWriteRq
               (regions : list MemRegion)
               (rq : ty LineWriteRq)
               : Action ty (implRegionsTree regions) Bool :=
      Let lineAddr : Addr <- ##rq`"addr" ;
      LetA rdy : Bool <- genRouteRegionAction implMemRegionTree (fun r => implMemRegionLineWriteRq r rq)
                           (@Or _ _) lineAddr regions ;
      Return (Or [ #rdy ; Not (isMappedAddr regions #lineAddr) ]).

    Definition implRegionsNoPortWriteRq
               (regions : list MemRegion)
               : Action ty (implRegionsTree regions) Bool :=
      genFoldRegionActions implMemRegionTree (fun r => @implMemRegionNoPortWriteRq r ty)
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

  Arguments implRegionsNoPortWriteRq {ty} regions.
  Arguments implRegionsReadFenceIWait {ty} regions.
  Arguments implRegionsSendFenceIRq {ty} regions.

  (* The memory: the regions, the `state` machine that serves one data request at a time (its
   * requester), and the single data response buffer `readRp` *)
  Definition implMemTree (regions : list MemRegion) : Tree DomainElem :=
    Node ""
      [ implRegionsTree regions ;
        Leaf "state"     (dom, EReg (Build_Reg MemState (Some (getDefault _)) false)) ;
        Leaf "requester" (dom, EReg (Build_Reg Requester (Some (getDefault _)) false)) ;
        Leaf "readRp"    (dom, EReg (Build_Reg (Option LineReadRp) (Some (getDefault _)) false)) ].

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
    Local Definition pMemReadRp    : RegPath implMemTree := Eval cbn in (getChildRegPathTree implMemTree "readRp").

    Section Ty.
      Variable ty : Kind -> Type.

      Local Definition liftRevoker
        (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions)
        (k : Kind)
        (a : Action ty (memRegionTree dom (@revokerRegion dom (implRevokerExtraChildren dom) regions rev)) k)
        : Action ty implMemTree k :=
        implNthRegionAction rev.(revokerIdx) regions (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a.

      Arguments liftRevoker rev k a : clear implicits.

      (* Universal 5-State Memory Pipeline Actions on implMemTree. A data access touches the line
       * holding its address and, only if it spills into it (memCrossesLine), the next line; each
       * line request is routed to the region that owns that line.
       * Requests reach the memories in program order: a new access is handed to `state`, and a
       * store's next line is handed to its region, only once no region's `portRq` still holds a
       * Write, i.e. once every earlier store line has been accepted. A read keeps `state` busy
       * until its response arrives, so only Writes can be left in a `portRq`. *)

      Definition implMemNoPortWriteRq : Action ty implMemTree Bool :=
        liftAction child0Path (implRegionsNoPortWriteRq regions).

      Definition implMemNoWriteRq : Action ty implMemTree Bool :=
        ReadReg "state" pMemState (fun state =>
        Return (Not (##state `? "WriteRq"))).

      (* Every accepted store has reached its region: none waits in `state` or in a `portRq` *)
      Definition implMemNoPendingWrite : Action ty implMemTree Bool :=
        LetA noWriteRq      : Bool <- implMemNoWriteRq ;
        LetA noPortWriteRqs : Bool <- implMemNoPortWriteRq ;
        Return (And [ #noWriteRq ; #noPortWriteRqs ]).

      Definition implMemReadRq
                 (req : MemRequester)
                 (addr : ty Addr)
                 (memSize : ty (Bit LgLgNumBytesFullCapSz))
                 : Action ty implMemTree Bool :=
        LetA noPortWriteRqs : Bool <- implMemNoPortWriteRq ;
        ReadReg "state" pMemState (fun state =>
        Let rdy : Bool <- And [ ##state `? "Idle" ; #noPortWriteRqs ] ;
        If #rdy Then (
          Let isSecond : Bool      <- ConstBool false ;
          Let emptyPkt : CapPacket <- ConstDef ;
          Act (WriteReg pMemState (UNION (MemStateList, "ReadRq" ::= STRUCT {
            "isSecond" ::= #isSecond ;
            "op"       ::= STRUCT {
              "addr"    ::= #addr ;
              "memSize" ::= #memSize ;
              "pkt"     ::= #emptyPkt
            }
          })) Retv) ;
          WriteReg pMemRequester (mkRequester req) Retv
        ) ;
        Return #rdy).

      Definition implMemReadRqStep : Action ty implMemTree (Bit 0) :=
        ReadReg "state" pMemState (fun state =>
        ReadReg "readRp" pMemReadRp (fun readRp =>
        If (And [ ##state `? "ReadRq" ; Not (##readRp`"valid") ]) Then (
          Let  step     : MemStepOp                 <- ##state `! "ReadRq" ;
          Let  isSecond : Bool                      <- ##step`"isSecond" ;
          Let  op       : MemPendingOp              <- ##step`"op" ;
          Let  addr     : Addr                      <- ##op`"addr" ;
          Let  memSize  : Bit LgLgNumBytesFullCapSz <- ##op`"memSize" ;
          Let  lineAddr : Addr                      <- ITE #isSecond (memNextLineAddr #addr) (memLineAddr #addr) ;
          LetL dataMask : Array LineBytes Bool      <- memDataMask #isSecond #addr #memSize ;
          LetA res      : LineReadRqRes             <- liftAction child0Path (implRegionsLineReadRq regions lineAddr dataMask) ;
          If (##res`"rdy") Then (
            Let crosses : Bool <- memCrossesLine #addr #memSize ;
            Act (WriteReg pMemState (UNION (MemStateList, "ReadRqSent" ::= STRUCT {
              "crosses" ::= #crosses ;
              "step"    ::= #step
            })) Retv) ;
            If (##res`"rp"`"valid") Then (
              WriteReg pMemReadRp (##res`"rp") Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv)).

      Definition implMemReadRpStep : Action ty implMemTree (Bit 0) :=
        ReadReg "state" pMemState (fun state =>
        ReadReg "readRp" pMemReadRp (fun readRp =>
        If (And [ ##state `? "ReadRqSent" ; ##readRp`"valid" ]) Then (
          Let  rqInfo   : MemReadRqSent             <- ##state `! "ReadRqSent" ;
          Let  crosses  : Bool                      <- ##rqInfo`"crosses" ;
          Let  step     : MemStepOp                 <- ##rqInfo`"step" ;
          Let  isSecond : Bool                      <- ##step`"isSecond" ;
          Let  op       : MemPendingOp              <- ##step`"op" ;
          Let  addr     : Addr                      <- ##op`"addr" ;
          Let  memSize  : Bit LgLgNumBytesFullCapSz <- ##op`"memSize" ;
          Let  savedPkt : CapPacket                 <- ##op`"pkt" ;
          Let  rp       : LineReadRp                <- ##readRp`"data" ;
          LetL pkt      : CapPacket                 <- memExtractCapPacket #addr #rp ;
          Act (WriteReg pMemReadRp ConstDef Retv) ;
          If (And [ Not #isSecond ; #crosses ]) Then (
            Let isSecond1 : Bool <- ConstBool true ;
            WriteReg pMemState (UNION (MemStateList, "ReadRq" ::= STRUCT {
              "isSecond" ::= #isSecond1 ;
              "op"       ::= STRUCT {
                "addr"    ::= #addr ;
                "memSize" ::= #memSize ;
                "pkt"     ::= #pkt
              }
            })) Retv
          ) Else (
            Let  mergedPkt : CapPacket      <- ITE #isSecond (memMergeCapPacket #addr #savedPkt #pkt) #pkt ;
            LetL res       : FullCapWithTag <- memAssembleCapRead #addr #memSize #mergedPkt ;
            WriteReg pMemState (UNION (MemStateList, "ReadRpReady" ::= #res)) Retv
          ) ;
          Retv
        ) ;
        Retv)).

      (* Port of an ExternalMem region delivering a line read response into the data response
       * buffer, if the buffer is empty *)
      Definition implMemLineRpPort (port : Action ty (implRegionsTree regions) (Option LineReadRp))
        : Action ty implMemTree (Bit 0) :=
        ReadReg "readRp" pMemReadRp (fun readRp =>
        If (Not (##readRp`"valid")) Then (
          LetA rpOpt : Option LineReadRp <- liftAction child0Path port ;
          If (##rpOpt`"valid") Then (
            WriteReg pMemReadRp #rpOpt Retv
          ) ;
          Retv
        ) ;
        Retv).

      Definition implMemReadRp
                 (req : MemRequester)
                 : Action ty implMemTree (Option FullCapWithTag) :=
        ReadReg "state" pMemState (fun state =>
        ReadReg "requester" pMemRequester (fun requester =>
        LetIf resOpt : Option FullCapWithTag <-
          If (And [ ##state `? "ReadRpReady" ; isRequesterMatch requester req ]) Then (
            Let res : FullCapWithTag <- ##state `! "ReadRpReady" ;
            Return (mkSome #res)
          ) ;
        Return #resOpt)).

      Definition implMemDeqRp : Action ty implMemTree (Bit 0) :=
        WriteReg pMemState (UNION (MemStateList, "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

      Definition implMemWrite
                 (addr : ty Addr)
                 (stVal : ty FullCapWithTag)
                 (memSize : ty (Bit LgLgNumBytesFullCapSz))
                 : Action ty implMemTree Bool :=
        LetA noPortWriteRqs : Bool <- implMemNoPortWriteRq ;
        ReadReg "state" pMemState (fun state =>
        Let rdy : Bool <- And [ ##state `? "Idle" ; #noPortWriteRqs ] ;
        If #rdy Then (
          Let  isSecond : Bool      <- ConstBool false ;
          LetL capPkt   : CapPacket <- memDisassembleCapWrite #addr #stVal #memSize ;
          WriteReg pMemState (UNION (MemStateList, "WriteRq" ::= STRUCT {
            "isSecond" ::= #isSecond ;
            "op"       ::= STRUCT {
              "addr"    ::= #addr ;
              "memSize" ::= #memSize ;
              "pkt"     ::= #capPkt
            }
          })) Retv
        ) ;
        Return #rdy).

      (* A line is handed to its region only once every earlier line has been accepted, so the
       * two lines of a crossing store reach their memories in order. *)
      Definition implMemWriteRqStep : Action ty implMemTree (Bit 0) :=
        LetA noPortWriteRqs : Bool <- implMemNoPortWriteRq ;
        ReadReg "state" pMemState (fun state =>
        If (And [ ##state `? "WriteRq" ; #noPortWriteRqs ]) Then (
          Let  step     : MemStepOp                 <- ##state `! "WriteRq" ;
          Let  isSecond : Bool                      <- ##step`"isSecond" ;
          Let  op       : MemPendingOp              <- ##step`"op" ;
          Let  addr     : Addr                      <- ##op`"addr" ;
          Let  memSize  : Bit LgLgNumBytesFullCapSz <- ##op`"memSize" ;
          Let  capPkt   : CapPacket                 <- ##op`"pkt" ;
          LetL rq       : LineWriteRq               <- memBuildLineWriteRq #isSecond #addr #capPkt #memSize ;
          LetA rdy      : Bool                      <- liftAction child0Path (implRegionsLineWriteRq regions rq) ;
          If #rdy Then (
            If (And [ Not #isSecond ; memCrossesLine #addr #memSize ]) Then (
              Let isSecond1 : Bool <- ConstBool true ;
              WriteReg pMemState (UNION (MemStateList, "WriteRq" ::= STRUCT {
                "isSecond" ::= #isSecond1 ;
                "op"       ::= #op
              })) Retv
            ) Else (
              WriteReg pMemState (UNION (MemStateList, "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv).

      Definition implMemCollectIrqActions : list (Action ty implMemTree Bool) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectIrqActions regions).

      Definition implMemCollectFetchLineRpPorts : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectFetchLineRpPorts regions).

      Definition implMemCollectLineReadRpPorts : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => implMemLineRpPort (f ty)) (implCollectLineRpPorts regions).

      Definition implMemCollectLineReadRqPorts : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectLineReadRqPorts regions).

      Definition implMemCollectLineWriteRqPorts : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => liftAction child0Path (f ty)) (implCollectLineWriteRqPorts regions).

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
        LetA rpOpt       : Option FullCapWithTag     <- implMemReadRp req ;
        LetIf rOpt : Option Bool <-
          If (##rpOpt`"valid") Then (
            Act implMemDeqRp ;
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

      (* 3. FENCE.I Synchronization Channel: every accepted store must have reached its
       *    region's memory, i.e. no store waits in `state` or in a region's `portRq` *)
      Definition implFenceIReq : Action ty implMemTree Bool :=
        LetA allWritten : Bool <- implMemNoPendingWrite ;
        If #allWritten Then (
          liftAction child0Path (implRegionsSendFenceIRq regions)
        ) ;
        Return #allWritten.

      (* 4. Split-Phase Autonomous Revoker Steps. The Idle step waits until no store is pending,
       *    so the revoker moves on (to its next read, or to the epoch bump when the sweep is
       *    done) only after its last write has been accepted. *)
      Definition implRevokerIdleStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        LetA noPendingWrite : Bool <- implMemNoPendingWrite ;
        If #noPendingWrite Then (
          @implRevokerIdle
            dom
            ty
            implMemTree
            (liftRevoker rev)
            (implMemReadRq ReqRevoker)
        ) ;
        Retv.

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
        mem_readInstRq     := fun addr => liftAction child0Path (implRegionsFetchLineReadRq regions addr) ;
        mem_getInstRp      := fun addr => liftAction child0Path (implRegionsFetchLineReadRp regions addr) ;
        mem_deqInstRp      := fun addr => liftAction child0Path (implRegionsFetchLineDeqRp regions addr) ;
        mem_readMemRq      := implMemReadRq ReqDataMem ;
        mem_getMemRp       := implMemReadRp ReqDataMem ;
        mem_deqMemRp       := implMemDeqRp ;
        mem_readRevBitRq   := implReadRevBitRqFor ReqDataMem ;
        mem_getDeqRevBitRp := implGetDeqRevBitRpFor ReqDataMem ;
        mem_writeMem       := implWriteMem rev ;
        mem_noWriteRq      := implMemNoPendingWrite ;
        mem_fence_req      := fun _ => Return (ConstBool true) ;
        mem_readFenceIWait := liftAction child0Path (implRegionsReadFenceIWait regions) ;
        mem_fenceI_req     := implFenceIReq
      |}.

    End Ty.

  End ImplMemModel.

End ImplDevice.

Arguments implExternalMemFetchTree dom : clear implicits.
Arguments implExternalMemExtraChildren dom : clear implicits.
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


