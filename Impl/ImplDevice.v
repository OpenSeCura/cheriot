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
From Cheriot Require Import SpecDefines Decoder SpecDevice FunctionalUnits SpecRevoker ImplRevoker ImplCommon.

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
| ReqRevoker
| ReqFetch
| ReqTarget.

Definition isFetchRequester (req : MemRequester) : bool :=
  match req with
  | ReqFetch => true
  | _        => false
  end.

Definition RequesterList : list (string * Kind) :=
  [ ("DataMem", Bit 0) ;
    ("Revoker", Bit 0) ;
    ("Fetch",   Bit 0) ;
    ("Target",  Bit 0) ].

Definition Requester : Kind :=
  TaggedUnion RequesterList.

Definition mkRequester {ty : Kind -> Type} (req : MemRequester) : Expr ty Requester :=
  match req with
  | ReqDataMem => UNION (RequesterList, "DataMem" ::= ($0 : Expr ty (Bit 0)))
  | ReqRevoker => UNION (RequesterList, "Revoker" ::= ($0 : Expr ty (Bit 0)))
  | ReqFetch   => UNION (RequesterList, "Fetch"   ::= ($0 : Expr ty (Bit 0)))
  | ReqTarget  => UNION (RequesterList, "Target"  ::= ($0 : Expr ty (Bit 0)))
  end.

Definition mkRequesterOpt {ty : Kind -> Type} (req : MemRequester) : Expr ty (Option Requester) :=
  mkSome (mkRequester req).

Definition isRequesterMatch {ty : Kind -> Type} (r : ty Requester) (req : MemRequester) : Expr ty Bool :=
  match req with
  | ReqDataMem => #r `? "DataMem"
  | ReqRevoker => #r `? "Revoker"
  | ReqFetch   => #r `? "Fetch"
  | ReqTarget  => #r `? "Target"
  end.

Definition IntRegionStateList : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadWait", Bit 0) ].

Definition IntRegionState : Kind :=
  TaggedUnion IntRegionStateList.

Definition ExtRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadWait", Bit 0) ;
    ("ReadRp0",  LineReadRp cfg false) ;
    ("WriteRq1", LineWriteRq cfg false) ].

Definition ExtRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (ExtRegionStateList cfg).

Definition PortRqList (cfg : LineConfig) (isInternal : bool) : list (string * Kind) :=
  [ ("Read",  Addr) ;
    ("Write", LineWriteRq cfg isInternal) ].

Definition PortRq (cfg : LineConfig) (isInternal : bool) : Kind :=
  TaggedUnion (PortRqList cfg isInternal).

Definition CustomRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadRp",   LineReadRp cfg false) ;
    ("WriteRq1", LineWriteRq cfg false) ].

Definition CustomRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (CustomRegionStateList cfg).

Definition CustomLineReadRq (cfg : LineConfig) : Kind :=
  STRUCT_TYPE {
    "addr"     :: Addr ;
    "dataMask" :: Array (cfgLineBytes cfg) Bool
  }.

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

  Local Abbreviation MemRegion := (MemRegion dom).
  Local Abbreviation customMemChildren := (customMemChildren dom).

  Definition lgLinePackets (r : MemRegion) : nat :=
    (lgLineBytes r - Z.to_nat LgNumBytesFullCapSz)%nat.

  Definition linePackets (r : MemRegion) : nat :=
    Nat.pow 2 (lgLinePackets r).

  Definition memLgLinePacketsZ (r : MemRegion) : Z :=
    Z.of_nat (lgLinePackets r).

  Lemma region_lgLineBytes_ge_cap (r : MemRegion) :
    (Z.to_nat LgNumBytesFullCapSz <= lgLineBytes r)%nat.
  Proof.
    unfold lgLineBytes.
    apply Nat.leb_le, Is_true_eq_true, (cfgLinePf (regionLineCfg r)).
  Qed.

  Lemma lgLineBytes_split (r : MemRegion) :
    memLgLineBytesZ r = (LgNumBytesFullCapSz + memLgLinePacketsZ r)%Z.
  Proof.
    pose proof (region_lgLineBytes_ge_cap r) as Hpf.
    unfold memLgLineBytesZ, memLgLinePacketsZ, lgLinePackets.
    unfold LgNumBytesFullCapSz in *.
    lia.
  Qed.

  Lemma lineBytes_eq_linePackets (r : MemRegion) :
    kindSize (Array (lineBytes r) (Bit 8)) = kindSize (Array (linePackets r) FetchPacket).
  Proof.
    pose proof (region_lgLineBytes_ge_cap r) as Hpf.
    unfold FetchPacket, NumFetchParcels, CompInstSz, lineBytes, cfgLineBytes, linePackets, lgLinePackets, lgLineBytes in *.
    cbn [kindSize].
    rewrite !NatZ_mul_mult.
    change (Z.to_nat LgNumBytesFullCapSz) with 3%nat in *.
    rewrite (pow2_sub3 Hpf), Nat2Z.inj_mul.
    lia.
  Qed.

  Definition memLinePacketIdx (r : MemRegion) {ty : Kind -> Type} (addr : ty Addr)
    : Expr ty (Bit (memLgLinePacketsZ r)) :=
    TruncMsb (memLgLinePacketsZ r) LgNumBytesFullCapSz
      (castBits (lgLineBytes_split r) (memLineOffset r #addr)).

  Definition memExtractFetchPacket
    (r : MemRegion) (isInternal : bool) {ty : Kind -> Type}
    (addr : ty Addr)
    (rp : ty (LineReadRp r.(regionLineCfg) isInternal))
    : Expr ty FetchPacket :=
    let pkts := FromBit (Array (linePackets r) FetchPacket)
                        (castBits (lineBytes_eq_linePackets r) (ToBit (##rp`"data"))) in
    ReadArray pkts (memLinePacketIdx r addr).

  Arguments memLinePacketIdx r [ty] addr.
  Arguments memExtractFetchPacket r isInternal [ty] addr rp.

  Definition implInternalMemFetchChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "rpValid" (dom, EReg (Build_Reg Bool (Some false) false)) ;
      Leaf "readRp"  (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) true)) (Some (getDefault _)) false)) ].

  Definition implInternalMemFetchTree (r : MemRegion) : Tree DomainElem :=
    Node "fetch" (implInternalMemFetchChildren r).

  Definition implInternalMemTargetPortExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "lineReadRqReady"  (dom, ESend (Bit 0)) ;
      Leaf "lineWriteRqReady" (dom, ESend (Bit 0)) ;
      Leaf "lineReadRpReady"  (dom, ERecv Bool) ].

  Definition implInternalMemTargetPortExtraTree (r : MemRegion) : Tree DomainElem :=
    Node "target" (implInternalMemTargetPortExtraChildren r).

  Definition implInternalMemRegionBaseExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "rpValid"   (dom, EReg (Build_Reg Bool (Some false) false)) ;
      Leaf "state"     (dom, EReg (Build_Reg IntRegionState (Some (getDefault _)) false)) ;
      Leaf "requester" (dom, EReg (Build_Reg Requester (Some (getDefault _)) false)) ;
      Leaf "portRq"    (dom, EReg (Build_Reg (Option (PortRq r.(regionLineCfg) true)) (Some (getDefault _)) false)) ;
      Leaf "readRp"    (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) true)) (Some (getDefault _)) false)) ].

  Definition implInternalMemRegionExtraChildren (r : MemRegion) (isAccessible : bool) : list (Tree DomainElem) :=
    optNode "fetch" (hasFetchPort r.(hasExtraFetchPort)) (implInternalMemFetchChildren r) ::
    optNode "target" isAccessible (implInternalMemTargetPortExtraChildren r) ::
    implInternalMemRegionBaseExtraChildren r.

  Definition implExternalMemFetchChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "lineReadRqReady" (dom, ERecv Bool) ;
      Leaf "lineReadRpValid" (dom, ERecv Bool) ;
      Leaf "lineReadRpReady" (dom, ESend (Bit 0)) ;
      Leaf "readRp"          (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) false)) (Some (getDefault _)) false)) ].

  Definition implExternalMemFetchTree (r : MemRegion) : Tree DomainElem :=
    Node "fetch" (implExternalMemFetchChildren r).

  Definition implExternalMemRegionBaseExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "lineReadRqReady"  (dom, ERecv Bool) ;
      Leaf "lineWriteRqReady" (dom, ERecv Bool) ;
      Leaf "lineReadRpValid"  (dom, ERecv Bool) ;
      Leaf "lineReadRpReady"  (dom, ESend (Bit 0)) ;
      Leaf "state"            (dom, EReg (Build_Reg (ExtRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
      Leaf "nextLineAddr"     (dom, EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
      Leaf "requester"        (dom, EReg (Build_Reg Requester (Some (getDefault _)) false)) ;
      Leaf "portRq"           (dom, EReg (Build_Reg (Option (PortRq r.(regionLineCfg) false)) (Some (getDefault _)) false)) ;
      Leaf "readRp"           (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) false)) (Some (getDefault _)) false)) ].

  Definition implExternalMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    optNode "fetch" (hasFetchPort r.(hasExtraFetchPort)) (implExternalMemFetchChildren r) ::
    implExternalMemRegionBaseExtraChildren r.

  Definition implCustomMemFetchChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "readRp" (dom, EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) false)) (Some (getDefault _)) false)) ].

  Definition implCustomMemFetchTree (r : MemRegion) : Tree DomainElem :=
    Node "fetch" (implCustomMemFetchChildren r).

  Definition implCustomMemRegionBaseExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    [ Leaf "state"      (dom, EReg (Build_Reg (CustomRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
      Leaf "nextLineRq" (dom, EReg (Build_Reg (Option (CustomLineReadRq r.(regionLineCfg))) (Some (getDefault _)) false)) ;
      Leaf "requester"  (dom, EReg (Build_Reg Requester (Some (getDefault _)) false)) ].

  Definition implCustomMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    optNode "fetch" (hasFetchPort r.(hasExtraFetchPort)) (implCustomMemFetchChildren r) ::
    implCustomMemRegionBaseExtraChildren r.

  Definition implInternalMemRegionTree (r : MemRegion) (isAccessible : bool) : Tree DomainElem :=
    Node r.(regionName) (internalMemRegionTree r isAccessible :: implInternalMemRegionExtraChildren r isAccessible).

  Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
    Node r.(regionName) (externalMemRegionTree r :: implExternalMemRegionExtraChildren r).

  Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
    Node r.(regionName) (customMemRegionTree r children :: implCustomMemRegionExtraChildren r).

  Definition implMemRegionTree (r : MemRegion) : Tree DomainElem :=
    match r.(regionKind) with
    | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
    | ExternalMem => implExternalMemRegionTree r
    | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
    end.

  Definition liftToImplRegion {ty : Kind -> Type} (r : MemRegion) {k : Kind}
    (act : Action ty (memRegionTree r) k) : Action ty (implMemRegionTree r) k :=
    match r.(regionKind) as rk
      return Action ty (match rk with
                        | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                        | ExternalMem => externalMemRegionTree r
                        | CustomMem children _ _ _ _ => customMemRegionTree r children
                        end) k ->
             Action ty (match rk with
                        | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                        | ExternalMem => implExternalMemRegionTree r
                        | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                        end) k
    with
    | InternalMem isAccessible _ _ => fun a => liftAction child0Path a
    | ExternalMem => fun a => liftAction child0Path a
    | CustomMem children _ _ _ _ => fun a => liftAction child0Path a
    end act.

  Arguments liftToImplRegion {ty} r {k} act.

  (* ===========================================================================
   * Split-Phase Implementation Actions for InternalMem
   * =========================================================================== *)

  Section ImplInternalMemRegionActions.
    Variable r : MemRegion.
    Variable isAccessible : bool.
    Variable ty : Kind -> Type.

    Local Definition tImplInt      := implInternalMemRegionTree r isAccessible.
    Local Definition tImplIntFetch := implInternalMemFetchTree r.

    Local Definition pIntRpValid     : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "rpValid").
    Local Definition pIntState       : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "state").
    Local Definition pIntRequester   : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "requester").
    Local Definition pIntPortRq      : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "portRq").
    Local Definition pIntReadRp      : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "readRp").

    Local Definition pIntFetchRpValid : RegPath tImplIntFetch := Eval cbn in (getChildRegPathTree tImplIntFetch "rpValid").
    Local Definition pIntFetchReadRp  : RegPath tImplIntFetch := Eval cbn in (getChildRegPathTree tImplIntFetch "readRp").

    Let tInt := internalMemRegionTree r isAccessible.
    Let numLines := regionNumLines r.
    Let lBytes := lineBytes r.
    Let nTags := numLineTags r true.

    Definition internalMemRegionIssueFetchRq (addr : ty Addr)
               : Action ty tInt (Bit 0) :=
      let port := selectReadPort r true in
      Let lineIdx : Bit (Z.log2_up (Z.of_nat numLines)) <- memLineOffsetIdx r #addr ;
      fold_right (fun memIdx acc =>
                    ReadRqMem (memBankPath isAccessible memIdx)
                              (memSizeCast isAccessible memIdx #lineIdx)
                              (memPortCast isAccessible memIdx port) acc)
                 Retv (genFinType lBytes).

    Definition internalMemRegionGetFetchRp
               : Action ty tInt (LineReadRp r.(regionLineCfg) true) :=
      let port := selectReadPort r true in
      LetA dataBytes : Array lBytes (Bit 8) <-
        ArrayBuilderAction (fun memIdx cont =>
          ReadRpMem "readByteRp" (memBankPath isAccessible memIdx)
                    (memPortCast isAccessible memIdx port)
            (fun val => cont (memKindCastInv #val))) ;
      @Return ty tInt (LineReadRp r.(regionLineCfg) true) (STRUCT {
        "data" ::= #dataBytes ;
        "tag"  ::= (ConstDef : Expr ty (Array nTags Bool))
      }).

    (* 1. Dedicated Fetch Port Actions (useFetch = true) *)

    Definition implInternalMemRegionFetchLineReadRq (addr : ty Addr)
               : Action ty tImplInt Bool :=
      LetA rpValid : Bool <-
        liftChild1OptAction (ReadReg "rpValid" pIntFetchRpValid (fun v => Return #v)) ;
      Let rdy : Bool <- Not #rpValid ;
      If #rdy Then (
        Act (liftAction child0Path (internalMemRegionIssueFetchRq addr)) ;
        liftChild1OptAction (WriteReg pIntFetchRpValid (ConstBool true) Retv)
      ) ;
      Return #rdy.

    Definition implInternalMemRegionFetchLineReadRp
               : Action ty tImplInt (Option (LineReadRp r.(regionLineCfg) true)) :=
      liftChild1OptAction (ReadReg "readRp" pIntFetchReadRp (fun v => Return #v)).

    Definition implInternalMemRegionFetchDeqRp
               : Action ty tImplInt (Bit 0) :=
      liftChild1OptAction (WriteReg pIntFetchReadRp ConstDef Retv).

    Definition implInternalMemRegionFetchResponsePort
               : Action ty tImplInt (Bit 0) :=
      LetA readRp : Option (LineReadRp r.(regionLineCfg) true) <-
        liftChild1OptAction (ReadReg "readRp" pIntFetchReadRp (fun v => Return #v)) ;
      If (Not (##readRp`"valid")) Then (
        LetA rpValid : Bool <-
          liftChild1OptAction (ReadReg "rpValid" pIntFetchRpValid (fun v => Return #v)) ;
        If #rpValid Then (
          LetA rp : LineReadRp r.(regionLineCfg) true <-
            liftAction child0Path internalMemRegionGetFetchRp ;
          Act (liftChild1OptAction (WriteReg pIntFetchRpValid (ConstBool false) Retv)) ;
          liftChild1OptAction (WriteReg pIntFetchReadRp (mkSome #rp) Retv)
        ) ;
        Retv
      ) ;
      Retv.

    (* 2. Non-Fetch Port Actions (useFetch = false) *)

    Definition implInternalMemRegionPortReadRq (addr : ty Addr)
               : Action ty tImplInt Bool :=
      ReadReg "portRq" pIntPortRq (fun portRq =>
      ReadReg "rpValid" pIntRpValid (fun rpValid =>
      If (Not (##portRq`"valid")) Then (
        WriteReg pIntPortRq (mkSome (UNION (PortRqList r.(regionLineCfg) true, "Read" ::= #addr))) Retv
      ) ;
      Return (And [ Not #rpValid ; Not (##portRq`"valid") ]))).

    Definition implInternalMemRegionPortReadRp
               : Action ty tImplInt (Option (LineReadRp r.(regionLineCfg) true)) :=
      ReadReg "readRp" pIntReadRp (fun v => Return #v).

    Definition implInternalMemRegionPortDeqRp
               : Action ty tImplInt (Bit 0) :=
      WriteReg pIntReadRp ConstDef Retv.

    Definition implInternalMemRegionPortWriteRq
               (rq : ty (LineWriteRq r.(regionLineCfg) true))
               : Action ty tImplInt Bool :=
      if r.(isReadOnly) then (
        Return (ConstBool true)
      ) else (
        ReadReg "portRq" pIntPortRq (fun portRq =>
        If (Not (##portRq`"valid")) Then (
          WriteReg pIntPortRq (mkSome (UNION (PortRqList r.(regionLineCfg) true, "Write" ::= #rq))) Retv
        ) ;
        Return (Not (##portRq`"valid")))
      ).

    Definition implInternalMemRegionResponsePort
               : Action ty tImplInt (Bit 0) :=
      ReadReg "readRp" pIntReadRp (fun readRp =>
      If (Not (##readRp`"valid")) Then (
        ReadReg "rpValid" pIntRpValid (fun rpValid =>
        If #rpValid Then (
          LetA rp : LineReadRp r.(regionLineCfg) true <-
            liftAction child0Path (internalMemRegionGetReadRp r isAccessible false) ;
          Act (WriteReg pIntRpValid (ConstBool false) Retv) ;
          WriteReg pIntReadRp (mkSome #rp) Retv
        ) ;
        Retv)
      ) ;
      Retv).

    Definition implInternalMemRegionReadRequestPort
               : Action ty tImplInt (Bit 0) :=
      ReadReg "portRq" pIntPortRq (fun portRq =>
      If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Read" ]) Then (
        Let addr : Addr <- (##portRq`"data") `! "Read" ;
        Act (liftAction child0Path (internalMemRegionIssueReadRq r isAccessible false addr)) ;
        Act (WriteReg pIntRpValid (ConstBool true) Retv) ;
        WriteReg pIntPortRq ConstDef Retv
      ) ;
      Retv).

    Definition implInternalMemRegionWriteRequestPort
               : Action ty tImplInt (Bit 0) :=
      if r.(isReadOnly) then (
        Retv
      ) else (
        ReadReg "portRq" pIntPortRq (fun portRq =>
        If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Write" ]) Then (
          Let rq : LineWriteRq r.(regionLineCfg) true <- (##portRq`"data") `! "Write" ;
          Act (liftAction child0Path (internalMemRegionLineWrite r isAccessible rq)) ;
          WriteReg pIntPortRq ConstDef Retv
        ) ;
        Retv)
      ).

    Definition implInternalMemRegionDataLineReadRq
               (req : MemRequester)
               (addr : ty Addr)
               : Action ty tImplInt Bool :=
      ReadReg "state" pIntState (fun state =>
      LetIf rdy : Bool <-
        If (##state `? "Idle") Then (
          LetA rdy0 : Bool <- implInternalMemRegionPortReadRq addr ;
          If #rdy0 Then (
            Act (WriteReg pIntState (UNION (IntRegionStateList, "ReadWait" ::= ($0 : Expr ty (Bit 0)))) Retv) ;
            WriteReg pIntRequester (mkRequester req) Retv
          ) ;
          Return #rdy0
        ) ;
      Return #rdy).

    Definition implInternalMemRegionDataLineReadRp
               (req : MemRequester)
               : Action ty tImplInt (Option (LineReadRp r.(regionLineCfg) true)) :=
      ReadReg "state" pIntState (fun state =>
      ReadReg "requester" pIntRequester (fun requester =>
      LetIf rpOpt : Option (LineReadRp r.(regionLineCfg) true) <-
        If (And [ isRequesterMatch requester req ; ##state `? "ReadWait" ]) Then (
          implInternalMemRegionPortReadRp
        ) ;
      Return #rpOpt)).

    Definition implInternalMemRegionDataDeqRp : Action ty tImplInt (Bit 0) :=
      Act implInternalMemRegionPortDeqRp ;
      WriteReg pIntState (UNION (IntRegionStateList, "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

    (* 3. Unified Single-Line & Sub-Line Actions (dispatching on useFetch) *)

    Definition implInternalMemRegionLineReadRq
               (req : MemRequester)
               (addr : ty Addr)
               : Action ty tImplInt Bool :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implInternalMemRegionFetchLineReadRq addr
      else implInternalMemRegionDataLineReadRq req addr.

    Definition implInternalMemRegionLineReadRp
               (req : MemRequester)
               : Action ty tImplInt (Option (LineReadRp r.(regionLineCfg) true)) :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implInternalMemRegionFetchLineReadRp
      else implInternalMemRegionDataLineReadRp req.

    Definition implInternalMemRegionDeqRp
               (req : MemRequester)
               : Action ty tImplInt (Bit 0) :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implInternalMemRegionFetchDeqRp
      else implInternalMemRegionDataDeqRp.

    Definition implInternalMemRegionReadRq
               (req : MemRequester)
               (addr : ty Addr)
               (_ : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplInt Bool :=
      implInternalMemRegionDataLineReadRq req addr.

    Definition implInternalMemRegionReadRp
               (req : MemRequester)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplInt (Option FullCapWithTag) :=
      LetA rpOpt : Option (LineReadRp r.(regionLineCfg) true) <- implInternalMemRegionDataLineReadRp req ;
      LetIf resOpt : Option FullCapWithTag <-
        If (##rpOpt`"valid") Then (
          Let  rp  : LineReadRp r.(regionLineCfg) true <- ##rpOpt`"data" ;
          LetL res : FullCapWithTag                    <- memExtractReadCap r true #addr #memSize #rp ;
          Return (mkSome #res)
        ) ;
      Return #resOpt.

    Definition implInternalMemRegionWriteRq
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplInt Bool :=
      if r.(isReadOnly) then (
        Return (ConstBool true)
      ) else (
        ReadReg "state" pIntState (fun state =>
        LetIf rdy : Bool <-
          If (##state `? "Idle") Then (
            LetL rq : LineWriteRq r.(regionLineCfg) true <- memBuildLineWriteRq r true #addr #stVal #memSize ;
            implInternalMemRegionPortWriteRq rq
          ) ;
        Return #rdy)
      ).

  End ImplInternalMemRegionActions.

  Arguments internalMemRegionIssueFetchRq r isAccessible [ty] addr.
  Arguments internalMemRegionGetFetchRp r isAccessible {ty}.
  Arguments implInternalMemRegionFetchLineReadRq r isAccessible [ty] addr.
  Arguments implInternalMemRegionFetchLineReadRp r isAccessible {ty}.
  Arguments implInternalMemRegionFetchDeqRp r isAccessible {ty}.
  Arguments implInternalMemRegionFetchResponsePort r isAccessible {ty}.
  Arguments implInternalMemRegionPortReadRq r isAccessible [ty] addr.
  Arguments implInternalMemRegionPortReadRp r isAccessible {ty}.
  Arguments implInternalMemRegionPortDeqRp r isAccessible {ty}.
  Arguments implInternalMemRegionPortWriteRq r isAccessible [ty] rq.
  Arguments implInternalMemRegionResponsePort r isAccessible {ty}.
  Arguments implInternalMemRegionReadRequestPort r isAccessible {ty}.
  Arguments implInternalMemRegionWriteRequestPort r isAccessible {ty}.
  Arguments implInternalMemRegionDataLineReadRq r isAccessible [ty] req addr.
  Arguments implInternalMemRegionDataLineReadRp r isAccessible {ty} req.
  Arguments implInternalMemRegionDataDeqRp r isAccessible {ty}.
  Arguments implInternalMemRegionLineReadRq r isAccessible [ty] req addr.
  Arguments implInternalMemRegionLineReadRp r isAccessible {ty} req.
  Arguments implInternalMemRegionDeqRp r isAccessible {ty} req.
  Arguments implInternalMemRegionReadRq r isAccessible [ty] req addr memSize.
  Arguments implInternalMemRegionReadRp r isAccessible [ty] req addr memSize.
  Arguments implInternalMemRegionWriteRq r isAccessible [ty] addr stVal memSize.

  Section ImplInternalMemTargetPortActions.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Local Definition tTargetSpec        := internalMemTargetPortTree r.
    Local Definition tImplIntTargetPort := implInternalMemRegionTree r true.
    Local Definition tImplTargetExtra   := implInternalMemTargetPortExtraTree r.
    Local Definition pTargetPortLineReadRqReady  : SendPath tImplTargetExtra := Eval cbn in (getChildSendPathTree tImplTargetExtra "lineReadRqReady").
    Local Definition pTargetPortLineWriteRqReady : SendPath tImplTargetExtra := Eval cbn in (getChildSendPathTree tImplTargetExtra "lineWriteRqReady").
    Local Definition pTargetPortLineReadRpReady  : RecvPath tImplTargetExtra := Eval cbn in (getChildRecvPathTree tImplTargetExtra "lineReadRpReady").

    Local Definition pTargetPortLineReadRqValid  : RecvPath tTargetSpec := Eval cbn in (getChildRecvPathTree tTargetSpec "lineReadRqValid").
    Local Definition pTargetPortLineReadRq       : RecvPath tTargetSpec := Eval cbn in (getChildRecvPathTree tTargetSpec "lineReadRq").
    Local Definition pTargetPortLineReadRp       : SendPath tTargetSpec := Eval cbn in (getChildSendPathTree tTargetSpec "lineReadRp").
    Local Definition pTargetPortLineWriteRqValid : RecvPath tTargetSpec := Eval cbn in (getChildRecvPathTree tTargetSpec "lineWriteRqValid").
    Local Definition pTargetPortLineWriteRq      : RecvPath tTargetSpec := Eval cbn in (getChildRecvPathTree tTargetSpec "lineWriteRq").

    Definition implInternalMemRegionTargetPortReadRq : Action ty tImplIntTargetPort (Bit 0) :=
      ReadReg "state" (@pIntState r true) (fun state =>
      ReadReg "portRq" (@pIntPortRq r true) (fun portRq =>
      ReadReg "rpValid" (@pIntRpValid r true) (fun rpValid =>
      Let rdy : Bool <- And [ ##state `? "Idle" ; Not #rpValid ; Not (##portRq`"valid") ] ;
      If #rdy Then (
        LetA valid : Bool <- liftAction child0Path (liftAction child2Path (Recv "valid" pTargetPortLineReadRqValid (fun valid => Return #valid))) ;
        If #valid Then (
          LetA addr : Addr <- liftAction child0Path (liftAction child2Path (Recv "addr" pTargetPortLineReadRq (fun addr => Return #addr))) ;
          Act (liftAction child2Path (Send pTargetPortLineReadRqReady ($0 : Expr ty (Bit 0)) Retv)) ;
          Act (implInternalMemRegionDataLineReadRq r true ReqTarget addr) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv))).

    Definition implInternalMemRegionTargetPortReadRp : Action ty tImplIntTargetPort (Bit 0) :=
      LetA rpOpt : Option (LineReadRp r.(regionLineCfg) true) <- @implInternalMemRegionDataLineReadRp r true ty ReqTarget ;
      If (##rpOpt`"valid") Then (
        Let rp : LineReadRp r.(regionLineCfg) true <- ##rpOpt`"data" ;
        Act (liftAction child0Path (liftAction child2Path (Send pTargetPortLineReadRp #rp Retv))) ;
        LetA rpReady : Bool <- liftAction child2Path (Recv "rpReady" pTargetPortLineReadRpReady (fun rpReady => Return #rpReady)) ;
        If #rpReady Then (
          @implInternalMemRegionDataDeqRp r true ty
        ) ;
        Retv
      ) ;
      Retv.

    Definition implInternalMemRegionTargetPortWrite : Action ty tImplIntTargetPort (Bit 0) :=
      ReadReg "state" (@pIntState r true) (fun state =>
      ReadReg "portRq" (@pIntPortRq r true) (fun portRq =>
      Let rdy : Bool <-
        if r.(isReadOnly) then
          ConstBool true
        else
          And [ ##state `? "Idle" ; Not (##portRq`"valid") ] ;
      If #rdy Then (
        LetA valid : Bool <- liftAction child0Path (liftAction child2Path (Recv "valid" pTargetPortLineWriteRqValid (fun valid => Return #valid))) ;
        If #valid Then (
          LetA rq : LineWriteRq r.(regionLineCfg) true <- liftAction child0Path (liftAction child2Path (Recv "rq" pTargetPortLineWriteRq (fun rq => Return #rq))) ;
          Act (liftAction child2Path (Send pTargetPortLineWriteRqReady ($0 : Expr ty (Bit 0)) Retv)) ;
          Act (implInternalMemRegionPortWriteRq r true rq) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv)).

  End ImplInternalMemTargetPortActions.

  Arguments implInternalMemRegionTargetPortReadRq r {ty}.
  Arguments implInternalMemRegionTargetPortReadRp r {ty}.
  Arguments implInternalMemRegionTargetPortWrite r {ty}.

  (* ===========================================================================
   * Split-Phase Implementation Actions for ExternalMem
   * =========================================================================== *)

  Section ImplExternalMemRegionActions.
    Variable r : MemRegion.
    Variable ty : Kind -> Type.

    Local Definition tImplExt      := implExternalMemRegionTree r.
    Local Definition tImplExtFetch := implExternalMemFetchTree r.

    Local Definition pLineWriteRqReady     : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineWriteRqReady").
    Local Definition pLineReadRqReady      : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRqReady").
    Local Definition pLineReadRpValid      : RecvPath tImplExt      := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRpValid").
    Local Definition pLineReadRpReady      : SendPath tImplExt      := Eval cbn in (getChildSendPathTree tImplExt "lineReadRpReady").
    Local Definition pState                : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "state").
    Local Definition pNextLineAddr         : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "nextLineAddr").
    Local Definition pExtRequester         : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "requester").
    Local Definition pExtPortRq            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "portRq").
    Local Definition pExtReadRp            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "readRp").

    Local Definition pFetchLineReadRqReady : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRqReady").
    Local Definition pFetchLineReadRpValid : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRpValid").
    Local Definition pFetchLineReadRpReady : SendPath tImplExtFetch := Eval cbn in (getChildSendPathTree tImplExtFetch "lineReadRpReady").
    Local Definition pExtFetchReadRp       : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "readRp").

    (* 1. Dedicated Fetch Port Actions (useFetch = true) *)

    Definition implExternalMemRegionFetchLineReadRq (addr : ty Addr)
               : Action ty tImplExt Bool :=
      Act (liftAction child0Path (externalMemRegionIssueReadRq r true addr)) ;
      liftChild1OptAction (Recv "rdy" pFetchLineReadRqReady (fun rdy => Return #rdy)).

    Definition implExternalMemRegionFetchLineReadRp
               : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg) false)) :=
      liftChild1OptAction (ReadReg "readRp" pExtFetchReadRp (fun v => Return #v)).

    Definition implExternalMemRegionFetchDeqRp
               : Action ty tImplExt (Bit 0) :=
      liftChild1OptAction (WriteReg pExtFetchReadRp ConstDef Retv).

    Definition implExternalMemRegionFetchResponsePort
               : Action ty tImplExt (Bit 0) :=
      LetA readRp : Option (LineReadRp r.(regionLineCfg) false) <-
        liftChild1OptAction (ReadReg "readRp" pExtFetchReadRp (fun v => Return #v)) ;
      If (Not (##readRp`"valid")) Then (
        LetA valid : Bool <-
          liftChild1OptAction (Recv "valid" pFetchLineReadRpValid (fun v => Return #v)) ;
        If #valid Then (
          LetA rp : LineReadRp r.(regionLineCfg) false <-
            liftAction child0Path (externalMemRegionGetReadRp r true) ;
          Act (liftChild1OptAction (Send pFetchLineReadRpReady ($0 : Expr ty (Bit 0)) Retv)) ;
          liftChild1OptAction (WriteReg pExtFetchReadRp (mkSome #rp) Retv)
        ) ;
        Retv
      ) ;
      Retv.

    (* 2. Non-Fetch Port Actions (useFetch = false) *)

    Definition implExternalMemRegionPortReadRq (addr : ty Addr)
               : Action ty tImplExt Bool :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      LetIf extRdy <- If (Not (##portRq`"valid")) Then (
        WriteReg pExtPortRq (mkSome (UNION (PortRqList r.(regionLineCfg) false, "Read" ::= #addr))) (
        Recv "extRdy" pLineReadRqReady (fun extRdy => Return #extRdy )
      )) ;
      Return (And [ #extRdy ; Not (##portRq`"valid") ])).

    Definition implExternalMemRegionPortReadRp
               : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg) false)) :=
      ReadReg "readRp" pExtReadRp (fun v => Return #v).

    Definition implExternalMemRegionPortDeqRp
               : Action ty tImplExt (Bit 0) :=
      WriteReg pExtReadRp ConstDef Retv.

    Definition implExternalMemRegionPortWriteRq
               (rq : ty (LineWriteRq r.(regionLineCfg) false))
               : Action ty tImplExt Bool :=
      if r.(isReadOnly) then (
        Return (ConstBool true)
      ) else (
        ReadReg "portRq" pExtPortRq (fun portRq =>
        LetIf extRdy <- If (Not (##portRq`"valid")) Then (
          WriteReg pExtPortRq (mkSome (UNION (PortRqList r.(regionLineCfg) false, "Write" ::= #rq))) (
          Recv "extRdy" pLineWriteRqReady (fun extRdy => Return #extRdy)
        )) ;
        Return (And [ #extRdy ; Not (##portRq`"valid") ]))
      ).

    Definition implExternalMemRegionResponsePort
               : Action ty tImplExt (Bit 0) :=
      ReadReg "readRp" pExtReadRp (fun readRp =>
      If (Not (##readRp`"valid")) Then (
        Recv "valid" pLineReadRpValid (fun valid =>
        If #valid Then (
          LetA rp : LineReadRp r.(regionLineCfg) false <-
            liftAction child0Path (externalMemRegionGetReadRp r false) ;
          Act (Send pLineReadRpReady ($0 : Expr ty (Bit 0)) Retv) ;
          WriteReg pExtReadRp (mkSome #rp) Retv
        ) ;
        Retv)
      ) ;
      Retv).

    Definition implExternalMemRegionReadRequestPort
               : Action ty tImplExt (Bit 0) :=
      ReadReg "portRq" pExtPortRq (fun portRq =>
      If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Read" ]) Then (
        Let addr : Addr <- (##portRq`"data") `! "Read" ;
        Act (liftAction child0Path (externalMemRegionIssueReadRq r false addr)) ;
        WriteReg pExtPortRq ConstDef Retv
      ) ;
      Retv).

    Definition implExternalMemRegionWriteRequestPort
               : Action ty tImplExt (Bit 0) :=
      if r.(isReadOnly) then (
        Retv
      ) else (
        ReadReg "portRq" pExtPortRq (fun portRq =>
        If (And [ ##portRq`"valid" ; (##portRq`"data") `? "Write" ]) Then (
          Let rq : LineWriteRq r.(regionLineCfg) false <- (##portRq`"data") `! "Write" ;
          Act (liftAction child0Path (externalMemRegionLineWrite r rq)) ;
          WriteReg pExtPortRq ConstDef Retv
        ) ;
        Retv)
      ).

    Definition implExternalMemRegionDataLineReadRq
               (req : MemRequester)
               (addr : ty Addr)
               : Action ty tImplExt Bool :=
      ReadReg "state" pState (fun state =>
      LetIf rdy : Bool <-
        If (##state `? "Idle") Then (
          LetA rdy0 : Bool <- implExternalMemRegionPortReadRq addr ;
          If #rdy0 Then (
            Act (WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "ReadWait" ::= ($0 : Expr ty (Bit 0)))) Retv) ;
            WriteReg pExtRequester (mkRequester req) Retv
          ) ;
          Return #rdy0
        ) ;
      Return #rdy).

    Definition implExternalMemRegionDataLineReadRp
               (req : MemRequester)
               : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg) false)) :=
      ReadReg "state" pState (fun state =>
      ReadReg "requester" pExtRequester (fun requester =>
      LetIf rpOpt : Option (LineReadRp r.(regionLineCfg) false) <-
        If (And [ isRequesterMatch requester req ; ##state `? "ReadWait" ]) Then (
          implExternalMemRegionPortReadRp
        ) ;
      Return #rpOpt)).

    Definition implExternalMemRegionDataDeqRp : Action ty tImplExt (Bit 0) :=
      Act implExternalMemRegionPortDeqRp ;
      WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

    (* 3. Unified Single-Line & Multi-Line Actions (dispatching on useFetch) *)

    Definition implExternalMemRegionLineReadRq
               (req : MemRequester)
               (addr : ty Addr)
               : Action ty tImplExt Bool :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implExternalMemRegionFetchLineReadRq addr
      else implExternalMemRegionDataLineReadRq req addr.

    Definition implExternalMemRegionLineReadRp
               (req : MemRequester)
               : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg) false)) :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implExternalMemRegionFetchLineReadRp
      else implExternalMemRegionDataLineReadRp req.

    Definition implExternalMemRegionDeqRp
               (req : MemRequester)
               : Action ty tImplExt (Bit 0) :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implExternalMemRegionFetchDeqRp
      else implExternalMemRegionDataDeqRp.

    Definition implExternalMemRegionReadRq
               (req : MemRequester)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplExt Bool :=
      Let  addr0 : Addr <- memLineAddr r #addr ;
      LetA rdy0  : Bool <- implExternalMemRegionDataLineReadRq req addr0 ;
      If #rdy0 Then (
        Let crosses : Bool <- memCrossesLine r #addr #memSize ;
        If #crosses Then (
          Let addr1 : Addr <- memNextLineAddr r #addr ;
          WriteReg pNextLineAddr (mkSome #addr1) Retv
        ) ;
        Retv
      ) ;
      Return #rdy0.

    Definition implExternalMemRegionReadRp0 : Action ty tImplExt (Bit 0) :=
      ReadReg "state" pState (fun state =>
      ReadReg "nextLineAddr" pNextLineAddr (fun nextLineAddr =>
      If (And [ ##state `? "ReadWait" ; ##nextLineAddr`"valid" ]) Then (
        LetA rp0Opt : Option (LineReadRp r.(regionLineCfg) false) <- implExternalMemRegionPortReadRp ;
        If (##rp0Opt`"valid") Then (
          Let rp0 : LineReadRp r.(regionLineCfg) false <- ##rp0Opt`"data" ;
          Act implExternalMemRegionPortDeqRp ;
          WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "ReadRp0" ::= #rp0)) Retv
        ) ;
        Retv
      ) ;
      Retv)).

    Definition implExternalMemRegionReadRq1 : Action ty tImplExt (Bit 0) :=
      ReadReg "state" pState (fun state =>
      ReadReg "nextLineAddr" pNextLineAddr (fun nextLineAddr =>
      If (And [ ##state `? "ReadRp0" ; ##nextLineAddr`"valid" ]) Then (
        Let  addr1 : Addr <- ##nextLineAddr`"data" ;
        LetA rdy1  : Bool <- implExternalMemRegionPortReadRq addr1 ;
        If #rdy1 Then (
          WriteReg pNextLineAddr ConstDef Retv
        ) ;
        Retv
      ) ;
      Retv)).

    Definition implExternalMemRegionReadRp
               (req : MemRequester)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplExt (Option FullCapWithTag) :=
      ReadReg "state" pState (fun state =>
      ReadReg "nextLineAddr" pNextLineAddr (fun nextLineAddr =>
      ReadReg "requester" pExtRequester (fun requester =>
      Let isMatch : Bool <- isRequesterMatch requester req ;
      LetIf resOpt : Option FullCapWithTag <-
        If (And [ #isMatch ;
                  Or [ ##state `? "ReadWait" ; ##state `? "ReadRp0" ] ;
                  Not (##nextLineAddr`"valid") ]) Then (
          LetA lastRpOpt : Option (LineReadRp r.(regionLineCfg) false) <- implExternalMemRegionPortReadRp ;
          LetIf rOpt : Option FullCapWithTag <-
            If (##lastRpOpt`"valid") Then (
              Let lastRp : LineReadRp r.(regionLineCfg) false <- ##lastRpOpt`"data" ;
              Let rp0    : LineReadRp r.(regionLineCfg) false <-
                ITE (##state `? "ReadRp0") (##state `! "ReadRp0") #lastRp ;
              Let rp1    : LineReadRp r.(regionLineCfg) false <-
                ITE (##state `? "ReadRp0") #lastRp ConstDef ;
              Let rp     : LineReadRp r.(regionLineCfg) false <- memMergeLineReadRp r false #addr #rp0 #rp1 ;
              LetL res   : FullCapWithTag                     <- memExtractReadCap r false #addr #memSize #rp ;
              Return (mkSome #res)
            ) ;
          Return #rOpt
        ) ;
      Return #resOpt))).

    Definition implExternalMemRegionWriteRq
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplExt Bool :=
      if r.(isReadOnly) then (
        Return (ConstBool true)
      ) else (
        ReadReg "state" pState (fun state =>
        LetIf rdy : Bool <-
          If (##state `? "Idle") Then (
            LetL rq   : LineWriteRq r.(regionLineCfg) false <- memBuildLineWriteRq r false #addr #stVal #memSize ;
            Let  rq0  : LineWriteRq r.(regionLineCfg) false <- memLineWriteRq0 r false #rq #memSize ;
            LetA rdy0 : Bool                                <- implExternalMemRegionPortWriteRq rq0 ;
            If #rdy0 Then (
              Let crosses : Bool <- memCrossesLine r #addr #memSize ;
              If #crosses Then (
                Let rq1 : LineWriteRq r.(regionLineCfg) false <- memLineWriteRq1 r false #rq #memSize ;
                WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "WriteRq1" ::= #rq1)) Retv
              ) ;
              Retv
            ) ;
            Return #rdy0
          ) ;
        Return #rdy)
      ).

    Definition implExternalMemRegionWrite1 : Action ty tImplExt (Bit 0) :=
      if r.(isReadOnly) then (
        Retv
      ) else (
        ReadReg "state" pState (fun state =>
        If (##state `? "WriteRq1") Then (
          Let  rq1  : LineWriteRq r.(regionLineCfg) false <- ##state `! "WriteRq1" ;
          LetA rdy1 : Bool                                <- implExternalMemRegionPortWriteRq rq1 ;
          If #rdy1 Then (
            WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
          ) ;
          Retv
        ) ;
        Retv)
      ).

    Definition implExternalMemRegionIsIdle : Action ty tImplExt Bool :=
      ReadReg "state" pState (fun state =>
      ReadReg "portRq" pExtPortRq (fun portRq =>
      Return (And [ ##state `? "Idle" ; Not (##portRq`"valid") ]))).

  End ImplExternalMemRegionActions.

  Arguments implExternalMemRegionFetchLineReadRq r [ty] addr.
  Arguments implExternalMemRegionFetchLineReadRp r {ty}.
  Arguments implExternalMemRegionFetchDeqRp r {ty}.
  Arguments implExternalMemRegionFetchResponsePort r {ty}.
  Arguments implExternalMemRegionPortReadRq r [ty] addr.
  Arguments implExternalMemRegionPortReadRp r {ty}.
  Arguments implExternalMemRegionPortDeqRp r {ty}.
  Arguments implExternalMemRegionPortWriteRq r [ty] rq.
  Arguments implExternalMemRegionResponsePort r {ty}.
  Arguments implExternalMemRegionReadRequestPort r {ty}.
  Arguments implExternalMemRegionWriteRequestPort r {ty}.
  Arguments implExternalMemRegionDataLineReadRq r [ty] req addr.
  Arguments implExternalMemRegionDataLineReadRp r {ty} req.
  Arguments implExternalMemRegionDataDeqRp r {ty}.
  Arguments implExternalMemRegionLineReadRq r [ty] req addr.
  Arguments implExternalMemRegionLineReadRp r {ty} req.
  Arguments implExternalMemRegionDeqRp r {ty} req.
  Arguments implExternalMemRegionReadRq r [ty] req addr memSize.
  Arguments implExternalMemRegionReadRp0 r {ty}.
  Arguments implExternalMemRegionReadRq1 r {ty}.
  Arguments implExternalMemRegionReadRp r [ty] req addr memSize.
  Arguments implExternalMemRegionWriteRq r [ty] addr stVal memSize.
  Arguments implExternalMemRegionWrite1 r {ty}.
  Arguments implExternalMemRegionIsIdle r {ty}.

  (* ===========================================================================
   * Split-Phase Implementation Actions for CustomMem
   * =========================================================================== *)

  Section ImplCustomMemRegionActions.
    Variable r : MemRegion.
    Variable children : list (Tree DomainElem).
    Variable readAction : forall ty, ReadPortSel r.(hasExtraFetchPort) -> ty Addr ->
                          ty (Array (cfgLineBytes r.(regionLineCfg)) Bool) ->
                          Action ty (Node r.(regionName) (customMemChildren r.(hasExtraFetchPort) children))
                                 (LineReadRp r.(regionLineCfg) false).
    Variable writeAction : forall ty, ty (LineWriteRq r.(regionLineCfg) false) ->
                           Action ty (Node r.(regionName) (customMemChildren r.(hasExtraFetchPort) children)) (Bit 0).
    Variable ty : Kind -> Type.

    Local Definition tImplCust      := implCustomMemRegionTree r children.
    Local Definition tImplCustFetch := implCustomMemFetchTree r.

    Local Definition pCustState       : RegPath tImplCust      := Eval cbn in (getChildRegPathTree tImplCust "state").
    Local Definition pCustNextLineRq  : RegPath tImplCust      := Eval cbn in (getChildRegPathTree tImplCust "nextLineRq").
    Local Definition pCustRequester   : RegPath tImplCust      := Eval cbn in (getChildRegPathTree tImplCust "requester").
    Local Definition pCustFetchReadRp : RegPath tImplCustFetch := Eval cbn in (getChildRegPathTree tImplCustFetch "readRp").

    (* 1. Dedicated Fetch Port Actions (useFetch = true) *)

    Definition implCustomMemRegionFetchLineReadRq (addr : ty Addr)
               : Action ty tImplCust Bool :=
      LetA readRp : Option (LineReadRp r.(regionLineCfg) false) <-
        liftChild1OptAction (ReadReg "readRp" pCustFetchReadRp (fun v => Return #v)) ;
      Let rdy : Bool <- Not (##readRp`"valid") ;
      If #rdy Then (
        Let dataMask : Array (lineBytes r) Bool <- Const ty (Array (lineBytes r) Bool) (InvDefault _) ;
        LetA rp : LineReadRp r.(regionLineCfg) false <-
          liftAction child0Path (customMemRegionLineRead r children readAction true addr dataMask) ;
        liftChild1OptAction (WriteReg pCustFetchReadRp (mkSome #rp) Retv)
      ) ;
      Return #rdy.

    Definition implCustomMemRegionFetchLineReadRp
               : Action ty tImplCust (Option (LineReadRp r.(regionLineCfg) false)) :=
      liftChild1OptAction (ReadReg "readRp" pCustFetchReadRp (fun v => Return #v)).

    Definition implCustomMemRegionFetchDeqRp
               : Action ty tImplCust (Bit 0) :=
      liftChild1OptAction (WriteReg pCustFetchReadRp ConstDef Retv).

    (* 2. Non-Fetch Port Actions (useFetch = false) *)

    Definition implCustomMemRegionDataLineReadRq
               (req : MemRequester)
               (addr : ty Addr)
               (dataMask : ty (Array (lineBytes r) Bool))
               : Action ty tImplCust Bool :=
      ReadReg "state" pCustState (fun state =>
      Let isIdle : Bool <- ##state `? "Idle" ;
      If #isIdle Then (
        LetA rp0 : LineReadRp r.(regionLineCfg) false <-
          liftAction child0Path (customMemRegionLineRead r children readAction false addr dataMask) ;
        Act (WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "ReadRp" ::= #rp0)) Retv) ;
        WriteReg pCustRequester (mkRequester req) Retv
      ) ;
      Return #isIdle).

    Definition implCustomMemRegionDataLineReadRp
               (req : MemRequester)
               : Action ty tImplCust (Option (LineReadRp r.(regionLineCfg) false)) :=
      ReadReg "state" pCustState (fun state =>
      ReadReg "nextLineRq" pCustNextLineRq (fun nextLineRq =>
      ReadReg "requester" pCustRequester (fun requester =>
      LetIf rpOpt : Option (LineReadRp r.(regionLineCfg) false) <-
        If (And [ ##state `? "ReadRp" ; Not (##nextLineRq`"valid") ; isRequesterMatch requester req ]) Then (
          Let rp : LineReadRp r.(regionLineCfg) false <- ##state `! "ReadRp" ;
          Return (mkSome #rp)
        ) ;
      Return #rpOpt))).

    Definition implCustomMemRegionDataDeqRp : Action ty tImplCust (Bit 0) :=
      WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

    (* 3. Unified Single-Line & Multi-Line Actions (dispatching on useFetch) *)

    Definition implCustomMemRegionLineReadRq
               (req : MemRequester)
               (addr : ty Addr)
               : Action ty tImplCust Bool :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch then
        implCustomMemRegionFetchLineReadRq addr
      else (
        Let dataMask : Array (lineBytes r) Bool <- Const ty (Array (lineBytes r) Bool) (InvDefault _) ;
        implCustomMemRegionDataLineReadRq req addr dataMask
      ).

    Definition implCustomMemRegionLineReadRp
               (req : MemRequester)
               : Action ty tImplCust (Option (LineReadRp r.(regionLineCfg) false)) :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implCustomMemRegionFetchLineReadRp
      else implCustomMemRegionDataLineReadRp req.

    Definition implCustomMemRegionDeqRp
               (req : MemRequester)
               : Action ty tImplCust (Bit 0) :=
      let useFetch := isFetchRequester req && hasFetchPort r.(hasExtraFetchPort) in
      if useFetch
      then implCustomMemRegionFetchDeqRp
      else implCustomMemRegionDataDeqRp.

    Definition implCustomMemRegionReadRq
               (req : MemRequester)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplCust Bool :=
      let '(dataMask0Expr, dataMask1Expr) := memDataMasks r #addr #memSize in
      Let  addr0     : Addr                     <- memLineAddr r #addr ;
      Let  dataMask0 : Array (lineBytes r) Bool <- dataMask0Expr ;
      LetA rdy0      : Bool                     <- implCustomMemRegionDataLineReadRq req addr0 dataMask0 ;
      If #rdy0 Then (
        Let crosses : Bool <- memCrossesLine r #addr #memSize ;
        If #crosses Then (
          Let rq1 : CustomLineReadRq r.(regionLineCfg) <- STRUCT {
            "addr"     ::= #addr ;
            "dataMask" ::= dataMask1Expr
          } ;
          WriteReg pCustNextLineRq (mkSome #rq1) Retv
        ) ;
        Retv
      ) ;
      Return #rdy0.

    Definition implCustomMemRegionReadRq1 : Action ty tImplCust (Bit 0) :=
      ReadReg "state" pCustState (fun state =>
      ReadReg "nextLineRq" pCustNextLineRq (fun nextLineRq =>
      If (And [ ##state `? "ReadRp" ; ##nextLineRq`"valid" ]) Then (
        Let  rp0       : LineReadRp r.(regionLineCfg) false       <- ##state `! "ReadRp" ;
        Let  rq1       : CustomLineReadRq r.(regionLineCfg)       <- ##nextLineRq`"data" ;
        Let  addr1     : Addr                                     <- memNextLineAddr r (##rq1`"addr") ;
        Let  dataMask1 : Array (lineBytes r) Bool                 <- ##rq1`"dataMask" ;
        LetA rp1       : LineReadRp r.(regionLineCfg) false       <-
          liftAction child0Path (customMemRegionLineRead r children readAction false addr1 dataMask1) ;
        Let  rp        : LineReadRp r.(regionLineCfg) false       <- memMergeLineReadRp r false (##rq1`"addr") #rp0 #rp1 ;
        Act (WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "ReadRp" ::= #rp)) Retv) ;
        WriteReg pCustNextLineRq ConstDef Retv
      ) ;
      Retv)).

    Definition implCustomMemRegionReadRp
               (req : MemRequester)
               (addr : ty Addr)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplCust (Option FullCapWithTag) :=
      LetA rpOpt : Option (LineReadRp r.(regionLineCfg) false) <- implCustomMemRegionDataLineReadRp req ;
      LetIf resOpt : Option FullCapWithTag <-
        If (##rpOpt`"valid") Then (
          Let  rp  : LineReadRp r.(regionLineCfg) false <- ##rpOpt`"data" ;
          LetL res : FullCapWithTag                     <- memExtractReadCap r false #addr #memSize #rp ;
          Return (mkSome #res)
        ) ;
      Return #resOpt.

    Definition implCustomMemRegionWriteRq
               (addr : ty Addr)
               (stVal : ty FullCapWithTag)
               (memSize : ty (Bit LgLgNumBytesFullCapSz))
               : Action ty tImplCust Bool :=
      if r.(isReadOnly) then (
        Return (ConstBool true)
      ) else (
        ReadReg "state" pCustState (fun state =>
        Let isIdle : Bool <- ##state `? "Idle" ;
        If #isIdle Then (
          LetL rq     : LineWriteRq r.(regionLineCfg) false <- memBuildLineWriteRq r false #addr #stVal #memSize ;
          Let rq0     : LineWriteRq r.(regionLineCfg) false <- memLineWriteRq0 r false #rq #memSize ;
          Act (liftAction child0Path (customMemRegionLineWrite r children writeAction rq0)) ;
          Let crosses : Bool                                <- memCrossesLine r #addr #memSize ;
          If #crosses Then (
            Let rq1 : LineWriteRq r.(regionLineCfg) false <- memLineWriteRq1 r false #rq #memSize ;
            WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "WriteRq1" ::= #rq1)) Retv
          ) ;
          Retv
        ) ;
        Return #isIdle)
      ).

    Definition implCustomMemRegionWrite1 : Action ty tImplCust (Bit 0) :=
      if r.(isReadOnly) then (
        Retv
      ) else (
        ReadReg "state" pCustState (fun state =>
        If (##state `? "WriteRq1") Then (
          Let rq1 : LineWriteRq r.(regionLineCfg) false <- ##state `! "WriteRq1" ;
          Act (liftAction child0Path (customMemRegionLineWrite r children writeAction rq1)) ;
          WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
        ) ;
        Retv)
      ).

    Definition implCustomMemRegionIsIdle : Action ty tImplCust Bool :=
      ReadReg "state" pCustState (fun state =>
      Return (##state `? "Idle")).

  End ImplCustomMemRegionActions.

  Arguments implCustomMemRegionFetchLineReadRq r children readAction [ty] addr.
  Arguments implCustomMemRegionFetchLineReadRp r children {ty}.
  Arguments implCustomMemRegionFetchDeqRp r children {ty}.
  Arguments implCustomMemRegionDataLineReadRq r children readAction [ty] req addr dataMask.
  Arguments implCustomMemRegionDataLineReadRp r children {ty} req.
  Arguments implCustomMemRegionDataDeqRp r children {ty}.
  Arguments implCustomMemRegionLineReadRq r children readAction [ty] req addr.
  Arguments implCustomMemRegionLineReadRp r children {ty} req.
  Arguments implCustomMemRegionDeqRp r children {ty} req.
  Arguments implCustomMemRegionReadRq r children readAction [ty] req addr memSize.
  Arguments implCustomMemRegionReadRq1 r children readAction {ty}.
  Arguments implCustomMemRegionReadRp r children {ty} req addr memSize.
  Arguments implCustomMemRegionWriteRq r children writeAction [ty] addr stVal memSize.
  Arguments implCustomMemRegionWrite1 r children writeAction {ty}.
  Arguments implCustomMemRegionIsIdle r children {ty}.

  (* ===========================================================================
   * Unified Per-Region Implementation Dispatch
   * =========================================================================== *)

  Definition implMemRegionLineReadRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (req : MemRequester)
             (addr : ty Addr)
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) Bool with
    | InternalMem isAccessible _ _ => implInternalMemRegionLineReadRq r isAccessible req addr
    | ExternalMem => implExternalMemRegionLineReadRq r req addr
    | CustomMem children readAct _ _ _ => implCustomMemRegionLineReadRq r children readAct req addr
    end.

  Definition implMemRegionLineReadRp
             (r : MemRegion)
             {ty : Kind -> Type}
             (req : MemRequester)
             : Action ty (implMemRegionTree r) (Option (LineReadRp r.(regionLineCfg) (isInternalMem r))) :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) (Option (LineReadRp r.(regionLineCfg) (isInternalRegionKind k))) with
    | InternalMem isAccessible _ _ => @implInternalMemRegionLineReadRp r isAccessible ty req
    | ExternalMem => @implExternalMemRegionLineReadRp r ty req
    | CustomMem children _ _ _ _ => @implCustomMemRegionLineReadRp r children ty req
    end.

  Definition implMemRegionFetchRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             : Action ty (implMemRegionTree r) Bool :=
    Let lineAddr : Addr <- memLineAddr r #addr ;
    implMemRegionLineReadRq r ReqFetch lineAddr.

  Definition implMemRegionFetchRp
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             : Action ty (implMemRegionTree r) (Option FetchPacket) :=
    LetA rpOpt : Option (LineReadRp r.(regionLineCfg) (isInternalMem r)) <- implMemRegionLineReadRp r ReqFetch ;
    LetIf resOpt : Option FetchPacket <-
      If (##rpOpt`"valid") Then (
        Let rp  : LineReadRp r.(regionLineCfg) (isInternalMem r) <- ##rpOpt`"data" ;
        Let pkt : FetchPacket                                    <- memExtractFetchPacket r (isInternalMem r) addr rp ;
        Return (mkSome #pkt)
      ) ;
    Return #resOpt.

  Definition implMemRegionReadRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) Bool with
    | InternalMem isAccessible _ _ => implInternalMemRegionReadRq r isAccessible req addr memSize
    | ExternalMem => implExternalMemRegionReadRq r req addr memSize
    | CustomMem children readAct _ _ _ => implCustomMemRegionReadRq r children readAct req addr memSize
    end.

  Definition implMemRegionReadRp
             (r : MemRegion)
             {ty : Kind -> Type}
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty (implMemRegionTree r) (Option FullCapWithTag) :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) (Option FullCapWithTag) with
    | InternalMem isAccessible _ _ => implInternalMemRegionReadRp r isAccessible req addr memSize
    | ExternalMem => implExternalMemRegionReadRp r req addr memSize
    | CustomMem children _ _ _ _ => implCustomMemRegionReadRp r children req addr memSize
    end.

  Definition implMemRegionDeqRp
             (r : MemRegion)
             {ty : Kind -> Type}
             (req : MemRequester)
             : Action ty (implMemRegionTree r) (Bit 0) :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) (Bit 0) with
    | InternalMem isAccessible _ _ => @implInternalMemRegionDeqRp r isAccessible ty req
    | ExternalMem => @implExternalMemRegionDeqRp r ty req
    | CustomMem children _ _ _ _ => @implCustomMemRegionDeqRp r children ty req
    end.

  Definition implMemRegionWriteRq
             (r : MemRegion)
             {ty : Kind -> Type}
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) Bool with
    | InternalMem isAccessible _ _ => implInternalMemRegionWriteRq r isAccessible addr stVal memSize
    | ExternalMem => implExternalMemRegionWriteRq r addr stVal memSize
    | CustomMem children _ writeAct _ _ => implCustomMemRegionWriteRq r children writeAct addr stVal memSize
    end.

  Definition implMemRegionIsIdle
             (r : MemRegion)
             {ty : Kind -> Type}
             : Action ty (implMemRegionTree r) Bool :=
    match r.(regionKind) as k return Action ty (match k with
                                                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                | ExternalMem => implExternalMemRegionTree r
                                                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                end) Bool with
    | InternalMem _ _ _ => Return (ConstBool true)
    | ExternalMem =>
        if hasFenceIPort r.(hasExtraFetchPort) then @implExternalMemRegionIsIdle r ty
        else Return (ConstBool true)
    | CustomMem children _ _ _ _ =>
        if hasFenceIPort r.(hasExtraFetchPort) then @implCustomMemRegionIsIdle r children ty
        else Return (ConstBool true)
    end.

  Arguments implMemRegionLineReadRq r [ty] req addr.
  Arguments implMemRegionLineReadRp r {ty} req.
  Arguments implMemRegionFetchRq r [ty] addr.
  Arguments implMemRegionFetchRp r [ty] addr.
  Arguments implMemRegionReadRq r [ty] req addr memSize.
  Arguments implMemRegionReadRp r [ty] req addr memSize.
  Arguments implMemRegionDeqRp r {ty} req.
  Arguments implMemRegionWriteRq r [ty] addr stVal memSize.
  Arguments implMemRegionIsIdle r {ty}.

  Definition implMemRegionFetchRpActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem isAccessible _ _ =>
        if hasFetchPort r.(hasExtraFetchPort) then
          [ (fun ty => @implInternalMemRegionFetchResponsePort r isAccessible ty) ]
        else []
    | ExternalMem =>
        if hasFetchPort r.(hasExtraFetchPort) then
          [ (fun ty => @implExternalMemRegionFetchResponsePort r ty) ]
        else []
    | CustomMem _ _ _ _ _ => []
    end.

  Definition implMemRegionFetchRqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem _ _ _ => []
    | ExternalMem => []
    | CustomMem _ _ _ _ _ => []
    end.

  Definition implMemRegionDataReadRpActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem isAccessible _ _ =>
        [ (fun ty => @implInternalMemRegionResponsePort r isAccessible ty) ]
    | ExternalMem =>
        [ (fun ty => @implExternalMemRegionResponsePort r ty) ]
    | CustomMem _ _ _ _ _ => []
    end.

  Definition implMemRegionDataReadRqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem isAccessible _ _ =>
        [ (fun ty => @implInternalMemRegionReadRequestPort r isAccessible ty) ]
    | ExternalMem =>
        [ (fun ty => @implExternalMemRegionReadRequestPort r ty) ]
    | CustomMem _ _ _ _ _ => []
    end.

  Definition implMemRegionDataWriteRqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem isAccessible _ _ =>
        [ (fun ty => @implInternalMemRegionWriteRequestPort r isAccessible ty) ]
    | ExternalMem =>
        [ (fun ty => @implExternalMemRegionWriteRequestPort r ty) ]
    | CustomMem _ _ _ _ _ => []
    end.

  Definition implMemRegionDataCrossLineActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem _ _ _ => []
    | ExternalMem =>
        [ (fun ty => @implExternalMemRegionWrite1 r ty) ;
          (fun ty => (Act (@implExternalMemRegionReadRp0 r ty) ; @implExternalMemRegionReadRq1 r ty)) ]
    | CustomMem children readAct writeAct _ _ =>
        [ (fun ty => @implCustomMemRegionWrite1 r children writeAct ty) ;
          (fun ty => @implCustomMemRegionReadRq1 r children readAct ty) ]
    end.

  Definition implMemRegionTargetPortRqActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem true _ _ =>
        [ (fun ty => @implInternalMemRegionTargetPortWrite r ty) ;
          (fun ty => @implInternalMemRegionTargetPortReadRq r ty) ]
    | _ => []
    end.

  Definition implMemRegionTargetPortRpActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    match r.(regionKind) as k return list (forall ty, Action ty (match k with
                                                                 | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                 | ExternalMem => implExternalMemRegionTree r
                                                                 | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                                                                 end) (Bit 0)) with
    | InternalMem true _ _ =>
        [ (fun ty => @implInternalMemRegionTargetPortReadRp r ty) ]
    | _ => []
    end.

  Definition implMemRegionFenceIAckActions
             (r : MemRegion)
             : list (forall ty, Action ty (implMemRegionTree r) (Bit 0)) :=
    map (fun act ty => liftToImplRegion r (act ty))
        (memRegionFenceIAckActions r).

  (* ===========================================================================
   * Multi-Region Composite Implementation Tree, Router & Collectors
   * =========================================================================== *)

  Fixpoint implRegionsChildren (regions : list MemRegion) : list (Tree DomainElem) :=
    match regions with
    | [] => []
    | r :: rs => [ implMemRegionTree r ; Node "" (implRegionsChildren rs) ]
    end.

  Definition implRegionsTree (regions : list MemRegion) : Tree DomainElem :=
    Node "" (implRegionsChildren regions).

  Section ImplNthRegionAction.
    Variable ty : Kind -> Type.

    Fixpoint implNthRegionAction
               (idx : nat)
               {struct idx}
               : forall (regions : list MemRegion) (r0 : MemRegion),
                 nth_error regions idx = Some r0 ->
                 forall k, Action ty (memRegionTree r0) k -> Action ty (implRegionsTree regions) k :=
      match idx with
      | 0%nat =>
          fun regions =>
            match regions return forall r0, nth_error regions 0 = Some r0 ->
                                  forall k, Action ty (memRegionTree r0) k -> Action ty (implRegionsTree regions) k with
            | nil => fun r0 pf => False_rect _ (none_neq_some pf)
            | cons r rs => fun r0 pf k act =>
                let eq_r0_r : r0 = r :=
                  match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end with
                  | eq_refl => eq_refl
                  end in
                liftAction child0Path
                  (liftToImplRegion r
                    (match eq_r0_r in (_ = y) return Action ty (memRegionTree y) k with
                     | eq_refl => act
                     end))
            end
      | S idx' =>
          fun regions =>
            match regions return forall r0, nth_error regions (S idx') = Some r0 ->
                                  forall k, Action ty (memRegionTree r0) k -> Action ty (implRegionsTree regions) k with
            | nil => fun r0 pf => False_rect _ (none_neq_some pf)
            | cons r rs => fun r0 pf k act =>
                liftAction child1Path (@implNthRegionAction idx' rs r0 pf k act)
            end
      end.

  End ImplNthRegionAction.

  Arguments implNthRegionAction {ty} idx regions r0 pf {k} act.

  Section ImplCollectors.
    Fixpoint implCollectIrqActions
             (regions : list MemRegion)
             : list (forall ty, Action ty (implRegionsTree regions) Bool) :=
      match regions return list (forall ty, Action ty (implRegionsTree regions) Bool) with
      | [] => []
      | r :: rs =>
          let rest := map (fun act ty => liftAction child1Path (act ty))
                          (implCollectIrqActions rs) in
          match memRegionIrqAction r with
          | Some act =>
              (fun ty => liftAction child0Path (liftToImplRegion r (act ty))) :: rest
          | None => rest
          end
      end.

    Fixpoint implCollectRegionActions
             (getActions : forall r : MemRegion, list (forall ty, Action ty (implMemRegionTree r) (Bit 0)))
             (regions : list MemRegion)
             : list (forall ty, Action ty (implRegionsTree regions) (Bit 0)) :=
      match regions return list (forall ty, Action ty (implRegionsTree regions) (Bit 0)) with
      | [] => []
      | r :: rs =>
          let curr := map (fun act ty => liftAction child0Path (act ty))
                          (getActions r) in
          let rest := map (fun act ty => liftAction child1Path (act ty))
                          (implCollectRegionActions getActions rs) in
          (curr ++ rest)%list
      end.

    Definition implCollectFetchRpActions := implCollectRegionActions implMemRegionFetchRpActions.
    Definition implCollectFetchRqActions := implCollectRegionActions implMemRegionFetchRqActions.
    Definition implCollectDataReadRpActions := implCollectRegionActions implMemRegionDataReadRpActions.
    Definition implCollectDataReadRqActions := implCollectRegionActions implMemRegionDataReadRqActions.
    Definition implCollectDataWriteRqActions := implCollectRegionActions implMemRegionDataWriteRqActions.
    Definition implCollectDataCrossLineActions := implCollectRegionActions implMemRegionDataCrossLineActions.
    Definition implCollectTargetPortRqActions := implCollectRegionActions implMemRegionTargetPortRqActions.
    Definition implCollectTargetPortRpActions := implCollectRegionActions implMemRegionTargetPortRpActions.
    Definition implCollectFenceIAckActions := implCollectRegionActions implMemRegionFenceIAckActions.
  End ImplCollectors.

  Section ImplRegionsRouter.
    Variable ty : Kind -> Type.

    Fixpoint implRegionsFetchRq
             (regions : list MemRegion)
             (addr : ty Addr)
             : Action ty (implRegionsTree regions) Bool :=
      match regions return Action ty (implRegionsTree regions) Bool with
      | [] => Return (ConstBool true)
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          LetIf devRdy : Bool <-
            If #isMatch Then (
              liftAction child0Path (implMemRegionFetchRq r addr)
            ) Else (
              Return (ConstBool true)
            ) ;
          LetA restRdy : Bool <-
            liftAction child1Path (implRegionsFetchRq rs addr) ;
          Return (And [ #devRdy ; #restRdy ])
      end.

    Fixpoint implRegionsFetchRp
             (regions : list MemRegion)
             (addr : ty Addr)
             : Action ty (implRegionsTree regions) (Option FetchPacket) :=
      match regions return Action ty (implRegionsTree regions) (Option FetchPacket) with
      | [] => Return (mkSome ConstDef)
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          LetIf devRp : Option FetchPacket <-
            If #isMatch Then (
              liftAction child0Path (implMemRegionFetchRp r addr)
            ) Else (
              Return (mkSome ConstDef)
            ) ;
          LetA restRp : Option FetchPacket <-
            liftAction child1Path (implRegionsFetchRp rs addr) ;
          @Return ty _ (Option FetchPacket) (STRUCT {
            "data"  ::= Or [ ##devRp`"data" ; ##restRp`"data" ] ;
            "valid" ::= And [ ##devRp`"valid" ; ##restRp`"valid" ]
          })
      end.

    Fixpoint implRegionsReadRq
             (regions : list MemRegion)
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty (implRegionsTree regions) Bool :=
      match regions return Action ty (implRegionsTree regions) Bool with
      | [] => Return (ConstBool true)
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          LetIf devRdy : Bool <-
            If #isMatch Then (
              liftAction child0Path (implMemRegionReadRq r req addr memSize)
            ) Else (
              Return (ConstBool true)
            ) ;
          LetA restRdy : Bool <-
            liftAction child1Path (implRegionsReadRq rs req addr memSize) ;
          Return (And [ #devRdy ; #restRdy ])
      end.

    Fixpoint implRegionsReadRp
             (regions : list MemRegion)
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty (implRegionsTree regions) (Option FullCapWithTag) :=
      match regions return Action ty (implRegionsTree regions) (Option FullCapWithTag) with
      | [] => Return (mkSome ConstDef)
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          LetIf devRp : Option FullCapWithTag <-
            If #isMatch Then (
              liftAction child0Path (implMemRegionReadRp r req addr memSize)
            ) Else (
              Return (mkSome ConstDef)
            ) ;
          LetA restRp : Option FullCapWithTag <-
            liftAction child1Path (implRegionsReadRp rs req addr memSize) ;
          @Return ty _ (Option FullCapWithTag) (STRUCT {
            "data"  ::= Or [ ##devRp`"data" ; ##restRp`"data" ] ;
            "valid" ::= And [ ##devRp`"valid" ; ##restRp`"valid" ]
          })
      end.

    Fixpoint implRegionsDeqRp
             (regions : list MemRegion)
             (req : MemRequester)
             (addr : ty Addr)
             : Action ty (implRegionsTree regions) (Bit 0) :=
      match regions return Action ty (implRegionsTree regions) (Bit 0) with
      | [] => Retv
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          If #isMatch Then (
            liftAction child0Path (@implMemRegionDeqRp r ty req)
          ) ;
          liftAction child1Path (implRegionsDeqRp rs req addr)
      end.

    Fixpoint implRegionsWrite
             (regions : list MemRegion)
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty (implRegionsTree regions) Bool :=
      match regions return Action ty (implRegionsTree regions) Bool with
      | [] => Return (ConstBool true)
      | r :: rs =>
          Let isMatch : Bool <- isRegionAddr r #addr ;
          LetIf devRdy : Bool <-
            If #isMatch Then (
              liftAction child0Path (implMemRegionWriteRq r addr stVal memSize)
            ) Else (
              Return (ConstBool true)
            ) ;
          LetA restRdy : Bool <-
            liftAction child1Path (implRegionsWrite rs addr stVal memSize) ;
          Return (And [ #devRdy ; #restRdy ])
      end.

    Fixpoint implRegionsIsIdle
             (regions : list MemRegion)
             : Action ty (implRegionsTree regions) Bool :=
      match regions return Action ty (implRegionsTree regions) Bool with
      | [] => Return (ConstBool true)
      | r :: rs =>
          LetA devIdle  : Bool <- liftAction child0Path (@implMemRegionIsIdle r ty) ;
          LetA restIdle : Bool <- liftAction child1Path (implRegionsIsIdle rs) ;
          Return (And [ #devIdle ; #restIdle ])
      end.

    Fixpoint implRegionsReadFenceIWait
             (regions : list MemRegion)
             : Action ty (implRegionsTree regions) Bool :=
      match regions return Action ty (implRegionsTree regions) Bool with
      | [] => Return (ConstBool false)
      | r :: rs =>
          LetA devWait  : Bool <- liftAction child0Path (liftToImplRegion r (memRegionReadFenceIWait r)) ;
          LetA restWait : Bool <- liftAction child1Path (implRegionsReadFenceIWait rs) ;
          Return (Or [ #devWait ; #restWait ])
      end.

    Fixpoint implRegionsSendFenceIRq
             (regions : list MemRegion)
             : Action ty (implRegionsTree regions) (Bit 0) :=
      match regions return Action ty (implRegionsTree regions) (Bit 0) with
      | [] => Retv
      | r :: rs =>
          Act (liftAction child0Path (liftToImplRegion r (memRegionSendFenceIRq r))) ;
          liftAction child1Path (implRegionsSendFenceIRq rs)
      end.

  End ImplRegionsRouter.

  Arguments implRegionsIsIdle {ty} regions.
  Arguments implRegionsReadFenceIWait {ty} regions.
  Arguments implRegionsSendFenceIRq {ty} regions.

  Section ImplMemModel.
    Variable revConfig : RevConfig.
    Variable regions : list MemRegion.

    Definition implMemTree : Tree DomainElem :=
      implRegionsTree regions.

    Section Ty.
      Variable ty : Kind -> Type.

      Definition implMemNthRegionAction
        (idx : nat)
        (r0 : MemRegion)
        (pf : nth_error regions idx = Some r0)
        {k : Kind}
        (act : Action ty (memRegionTree r0) k)
        : Action ty implMemTree k :=
        implNthRegionAction idx regions r0 pf act.

      Arguments implMemNthRegionAction idx r0 pf {k} act.

      Definition implMemCollectIrqActions : list (Action ty implMemTree Bool) :=
        map (fun f => f ty) (implCollectIrqActions regions).

      Definition implMemCollectFetchRpActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectFetchRpActions regions).

      Definition implMemCollectFetchRqActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectFetchRqActions regions).

      Definition implMemCollectDataReadRpActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectDataReadRpActions regions).

      Definition implMemCollectDataReadRqActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectDataReadRqActions regions).

      Definition implMemCollectDataWriteRqActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectDataWriteRqActions regions).

      Definition implMemCollectDataCrossLineActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectDataCrossLineActions regions).

      Definition implMemCollectTargetPortRqActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectTargetPortRqActions regions).

      Definition implMemCollectTargetPortRpActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectTargetPortRpActions regions).

      Definition implMemCollectFenceIAckActions : list (Action ty implMemTree (Bit 0)) :=
        map (fun f => f ty) (implCollectFenceIAckActions regions).

      (* 1. Instruction Memory Channel *)
      Definition implReadInstRq (addr : ty Addr) : Action ty implMemTree Bool :=
        implRegionsFetchRq regions addr.

      Definition implGetInstRp (addr : ty Addr) : Action ty implMemTree (Option FetchPacket) :=
        implRegionsFetchRp regions addr.

      Definition implDeqInstRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
        implRegionsDeqRp regions ReqFetch addr.

      (* 2. Data Load Channel *)
      Definition implReadMemRq (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
        implRegionsReadRq regions ReqDataMem addr memSize.

      Definition implGetMemRp (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree (Option FullCapWithTag) :=
        implRegionsReadRp regions ReqDataMem addr memSize.

      Definition implDeqMemRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
        implRegionsDeqRp regions ReqDataMem addr.

      (* 3. Revocation Bit Memory Channel *)
      Definition implReadRevBitRqFor (req : MemRequester) (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
        LetL lookup      : RevBitLookup              <- computeRevBitAddr revConfig base ;
        Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
        Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
        implRegionsReadRq regions req revByteAddr sz0.

      Definition implGetDeqRevBitRpFor (req : MemRequester) (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
        LetL lookup      : RevBitLookup              <- computeRevBitAddr revConfig base ;
        Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
        Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
        LetA rpOpt       : Option FullCapWithTag     <- implRegionsReadRp regions req revByteAddr sz0 ;
        LetIf rOpt : Option Bool <-
          If (##rpOpt`"valid") Then (
            Act (implRegionsDeqRp regions req revByteAddr) ;
            Let revCap  : FullCapWithTag <- ##rpOpt`"data" ;
            Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
            Let revBit  : Bool           <- extractRevBit lookup #revByte ;
            Return (mkSome #revBit)
          ) Else (
            Return ConstDef
          ) ;
        Return #rOpt.

      Definition implReadRevBitRq (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
        implReadRevBitRqFor ReqDataMem base.

      Definition implGetDeqRevBitRp (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
        implGetDeqRevBitRpFor ReqDataMem base.

      (* 4. Memory Write Channel (with store-address snooping for split-phase revoker) *)
      Definition implWriteMem (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions)
                              (addr : ty Addr) (stVal : ty FullCapWithTag)
                              (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
        LetA rdy : Bool <- implRegionsWrite regions addr stVal memSize ;
        If #rdy Then (
          implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker)
            (implRevokerSnoopStore dom addr memSize)
        ) ;
        Return #rdy.

      (* 5. FENCE & FENCE.I Synchronization Channels *)
      Definition implFenceReq (_ : ty FenceOp) : Action ty implMemTree Bool :=
        Return (ConstBool true).

      Definition implReadFenceIWait : Action ty implMemTree Bool :=
        implRegionsReadFenceIWait regions.

      Definition implFenceIReq : Action ty implMemTree Bool :=
        LetA allIdle : Bool <- implRegionsIsIdle regions ;
        If #allIdle Then (
          implRegionsSendFenceIRq regions
        ) ;
        Return #allIdle.

      (* 6. Split-Phase Autonomous Revoker Steps *)
      Definition implRevokerIdleStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        @implRevokerIdle
          dom
          ty
          implMemTree
          (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a)
          (implRegionsReadRq regions ReqRevoker).

      Definition implRevokerCapRpRevBitRqStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        Act (@implRevokerWaitCapRp
               dom
               ty
               revConfig
               implMemTree
               (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a)
               (implRegionsReadRp regions ReqRevoker)
               (implRegionsDeqRp regions ReqRevoker)) ;
        @implRevokerWaitRevBitRq
          dom
          ty
          implMemTree
          (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a)
          (implReadRevBitRqFor ReqRevoker).

      Definition implRevokerRevBitRpWriteCapStep (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : Action ty implMemTree (Bit 0) :=
        Act (@implRevokerWaitRevBitRp
               dom
               ty
               implMemTree
               (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a)
               (implGetDeqRevBitRpFor ReqRevoker)) ;
        @implRevokerWriteCap
          dom
          ty
          implMemTree
          (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a)
          (fun addr stVal sz => implRegionsWrite regions addr stVal sz).

      (* 7. Top-level MemIfc Instance *)
      Definition implMemIfc (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : @MemIfc ty := {|
        memTree            := implMemTree ;
        mem_readInstRq     := implReadInstRq ;
        mem_getInstRp      := implGetInstRp ;
        mem_deqInstRp      := implDeqInstRp ;
        mem_readMemRq      := implReadMemRq ;
        mem_getMemRp       := implGetMemRp ;
        mem_deqMemRp       := implDeqMemRp ;
        mem_readRevBitRq   := implReadRevBitRq ;
        mem_getDeqRevBitRp := implGetDeqRevBitRp ;
        mem_writeMem       := implWriteMem rev ;
        mem_fence_req      := implFenceReq ;
        mem_readFenceIWait := implReadFenceIWait ;
        mem_fenceI_req     := implFenceIReq
      |}.

    End Ty.

  End ImplMemModel.

End ImplDevice.

