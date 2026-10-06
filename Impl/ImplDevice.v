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
From Cheriot Require Import SpecDefines Decoder SpecDevice FunctionalUnits SpecRevoker ImplRevoker.

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
  mem_getInstRp    : ty Addr -> Action ty memTree (Option Inst) ;
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
  mem_fence_req    : ty FenceOp -> Action ty memTree Bool ;
  mem_fenceI_req   : Action ty memTree Bool ;
  mem_fenceI_ack   : Action ty memTree Bool
}.

(* ===========================================================================
 * Implementation Region Trees (Wrapping Spec memRegionTree)
 * =========================================================================== *)

Inductive MemRequester :=
| ReqDeferred
| ReqRevoker
| ReqFetch
| ReqTarget.

Definition isFetchRequester (req : MemRequester) : bool :=
  match req with
  | ReqFetch => true
  | _        => false
  end.

Definition RequesterList : list (string * Kind) :=
  [ ("Deferred", Bit 0) ;
    ("Revoker",  Bit 0) ;
    ("Fetch",    Bit 0) ;
    ("Target",   Bit 0) ].

Definition Requester : Kind :=
  TaggedUnion RequesterList.

Definition mkRequester {ty : Kind -> Type} (req : MemRequester) : Expr ty Requester :=
  match req with
  | ReqDeferred => UNION (RequesterList, "Deferred" ::= ($0 : Expr ty (Bit 0)))
  | ReqRevoker  => UNION (RequesterList, "Revoker"  ::= ($0 : Expr ty (Bit 0)))
  | ReqFetch    => UNION (RequesterList, "Fetch"    ::= ($0 : Expr ty (Bit 0)))
  | ReqTarget   => UNION (RequesterList, "Target"   ::= ($0 : Expr ty (Bit 0)))
  end.

Definition mkRequesterOpt {ty : Kind -> Type} (req : MemRequester) : Expr ty (Option Requester) :=
  mkSome (mkRequester req).

Definition isRequesterMatch {ty : Kind -> Type} (opt : Expr ty (Option Requester)) (req : MemRequester) : Expr ty Bool :=
  let tag := opt`"data" in
  let isTag :=
    match req with
    | ReqDeferred => tag `? "Deferred"
    | ReqRevoker  => tag `? "Revoker"
    | ReqFetch    => tag `? "Fetch"
    | ReqTarget   => tag `? "Target"
    end in
  And [ opt`"valid" ; isTag ].

Definition ExtRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadWait", Bit 0) ;
    ("ReadRp0",  LineReadRp cfg false) ;
    ("WriteRq1", LineWriteRq cfg false) ].

Definition ExtRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (ExtRegionStateList cfg).

Definition CustomRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadRp0",  LineReadRp cfg false) ;
    ("WriteRq1", LineWriteRq cfg false) ].

Definition CustomRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (CustomRegionStateList cfg).

Definition implInternalMemFetchChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "rpValid" (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ;
    Leaf "readRq"  (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
    Leaf "readRp"  (r.(regionDom), EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) true)) (Some (getDefault _)) false)) ].

Definition implInternalMemFetchTree (r : MemRegion) : Tree DomainElem :=
  Node "fetch" (implInternalMemFetchChildren r).

Definition implInternalMemRegionBaseExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "requester"        (r.(regionDom), EReg (Build_Reg (Option Requester) (Some (getDefault _)) false)) ;
    Leaf "writeBusy"        (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ;
    Leaf "readRq"           (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
    Leaf "readRp"           (r.(regionDom), EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) true)) (Some (getDefault _)) false)) ;
    Leaf "writeRq"          (r.(regionDom), EReg (Build_Reg (Option (LineWriteRq r.(regionLineCfg) true)) (Some (getDefault _)) false)) ;
    Leaf "lineReadRqReady"  (r.(regionDom), ESend Bool) ;
    Leaf "lineWriteRqReady" (r.(regionDom), ESend Bool) ;
    Leaf "lineReadRpReady"  (r.(regionDom), ERecv Bool) ].

Definition implInternalMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  optNode "fetch" r.(hasExtraFetchPort) (implInternalMemFetchChildren r) ::
  implInternalMemRegionBaseExtraChildren r.

Definition implExternalMemFetchChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "lineReadRqReady" (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRpValid" (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRpReady" (r.(regionDom), ESend (Bit 0)) ;
    Leaf "state"           (r.(regionDom), EReg (Build_Reg (ExtRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
    Leaf "nextLineAddr"    (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
    Leaf "readRq"          (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
    Leaf "readRp"          (r.(regionDom), EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) false)) (Some (getDefault _)) false)) ].

Definition implExternalMemFetchTree (r : MemRegion) : Tree DomainElem :=
  Node "fetch" (implExternalMemFetchChildren r).

Definition implExternalMemRegionBaseExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "lineReadRqReady"  (r.(regionDom), ERecv Bool) ;
    Leaf "lineWriteRqReady" (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRpValid"  (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRpReady"  (r.(regionDom), ESend (Bit 0)) ;
    Leaf "state"            (r.(regionDom), EReg (Build_Reg (ExtRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
    Leaf "nextLineAddr"     (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
    Leaf "requester"        (r.(regionDom), EReg (Build_Reg (Option Requester) (Some (getDefault _)) false)) ;
    Leaf "readRq"           (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
    Leaf "readRp"           (r.(regionDom), EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg) false)) (Some (getDefault _)) false)) ;
    Leaf "writeRq"          (r.(regionDom), EReg (Build_Reg (Option (LineWriteRq r.(regionLineCfg) false)) (Some (getDefault _)) false)) ].

Definition implExternalMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  optNode "fetch" r.(hasExtraFetchPort) (implExternalMemFetchChildren r) ::
  implExternalMemRegionBaseExtraChildren r.

Definition implCustomMemFetchChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "state" (r.(regionDom), EReg (Build_Reg (CustomRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ].

Definition implCustomMemFetchTree (r : MemRegion) : Tree DomainElem :=
  Node "fetch" (implCustomMemFetchChildren r).

Definition implCustomMemRegionBaseExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "state"     (r.(regionDom), EReg (Build_Reg (CustomRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
    Leaf "requester" (r.(regionDom), EReg (Build_Reg (Option Requester) (Some (getDefault _)) false)) ].

Definition implCustomMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  optNode "fetch" r.(hasExtraFetchPort) (implCustomMemFetchChildren r) ::
  implCustomMemRegionBaseExtraChildren r.

Definition implInternalMemRegionTree (r : MemRegion) (isAccessible : bool) : Tree DomainElem :=
  Node r.(regionName) (internalMemRegionTree r isAccessible :: implInternalMemRegionExtraChildren r).

Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
  Node r.(regionName) (externalMemRegionTree r :: implExternalMemRegionExtraChildren r).

Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
  Node r.(regionName) (customMemRegionTree r children :: implCustomMemRegionExtraChildren r).

Definition implMemRegionTree (r : MemRegion) : Tree DomainElem :=
  match r.(regionKind) with
  | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
  | ExternalMem => implExternalMemRegionTree r
  | CustomMem children _ _ _ => implCustomMemRegionTree r children
  end.

Definition liftToImplRegion {ty : Kind -> Type} (r : MemRegion) {k : Kind}
  (act : Action ty (memRegionTree r) k) : Action ty (implMemRegionTree r) k :=
  match r.(regionKind) as rk
    return Action ty (match rk with
                      | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                      | ExternalMem => externalMemRegionTree r
                      | CustomMem children _ _ _ => customMemRegionTree r children
                      end) k ->
           Action ty (match rk with
                      | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                      | ExternalMem => implExternalMemRegionTree r
                      | CustomMem children _ _ _ => implCustomMemRegionTree r children
                      end) k
  with
  | InternalMem isAccessible _ _ => fun a => liftAction child0Path a
  | ExternalMem => fun a => liftAction child0Path a
  | CustomMem children _ _ _ => fun a => liftAction child0Path a
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

  Local Definition pIntRequester : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "requester").
  Local Definition pWriteBusy    : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "writeBusy").
  Local Definition pReadRq       : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "readRq").
  Local Definition pReadRp       : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "readRp").
  Local Definition pWriteRq      : RegPath tImplInt      := Eval cbn in (getChildRegPathTree tImplInt "writeRq").
  Local Definition pFetchRpValid : RegPath tImplIntFetch := Eval cbn in (getChildRegPathTree tImplIntFetch "rpValid").
  Local Definition pFetchReadRq  : RegPath tImplIntFetch := Eval cbn in (getChildRegPathTree tImplIntFetch "readRq").
  Local Definition pFetchReadRp  : RegPath tImplIntFetch := Eval cbn in (getChildRegPathTree tImplIntFetch "readRp").

  Definition implInternalMemRegionLineReadRdy (isFetch : bool)
             : Action ty tImplInt Bool :=
    if isFetch && r.(hasExtraFetchPort) then
      liftChild1OptAction (ReadReg "rpValid" pFetchRpValid (fun rpValid =>
      Return (Not #rpValid)))
    else
      ReadReg "requester" pIntRequester (fun requester =>
      Return (Not (##requester`"valid"))).

  Definition implInternalMemRegionLineWriteRdy
             : Action ty tImplInt Bool :=
    ReadReg "writeBusy" pWriteBusy (fun writeBusy =>
    Return (Not #writeBusy)).

  Definition implInternalMemRegionLineReadRq (req : MemRequester) (addr : ty Addr)
             : Action ty tImplInt Bool :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA rdy : Bool <- implInternalMemRegionLineReadRdy isFetch ;
    If #rdy Then (
      Act (if useFetch
           then liftChild1OptAction (WriteReg pFetchReadRq (mkSome #addr) Retv)
           else WriteReg pReadRq (mkSome #addr) Retv) ;
      if useFetch
      then liftChild1OptAction (WriteReg pFetchRpValid (ConstBool true) Retv)
      else WriteReg pIntRequester (mkRequesterOpt req) Retv
    ) ;
    Return #rdy.

  Definition implInternalMemRegionLineReadRp (req : MemRequester)
             : Action ty tImplInt (Option (LineReadRp r.(regionLineCfg) true)) :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA isValid : Bool <-
      if useFetch then
        liftChild1OptAction (ReadReg "rpValid" pFetchRpValid (fun rpValid =>
        Return #rpValid))
      else
        ReadReg "requester" pIntRequester (fun requester =>
        Return (isRequesterMatch #requester req)) ;
    LetIf rpOpt : Option (LineReadRp r.(regionLineCfg) true) <-
      If #isValid Then (
        if useFetch
        then liftChild1OptAction (ReadReg "readRp" pFetchReadRp (fun readRp => Return #readRp))
        else ReadReg "readRp" pReadRp (fun readRp => Return #readRp)
      ) ;
    Return #rpOpt.

  Definition implInternalMemRegionLineDeqRp (req : MemRequester)
             : Action ty tImplInt (Bit 0) :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    Act (if useFetch
         then liftChild1OptAction (WriteReg pFetchReadRp ConstDef Retv)
         else WriteReg pReadRp ConstDef Retv) ;
    if useFetch
    then liftChild1OptAction (WriteReg pFetchRpValid (ConstBool false) Retv)
    else WriteReg pIntRequester ConstDef Retv.

  Definition implInternalMemRegionLineWriteRq
             (rq : ty (LineWriteRq r.(regionLineCfg) true))
             : Action ty tImplInt Bool :=
    LetA rdy : Bool <- implInternalMemRegionLineWriteRdy ;
    If #rdy Then (
      Act (WriteReg pWriteRq (mkSome #rq) Retv) ;
      WriteReg pWriteBusy (ConstBool true) Retv
    ) ;
    Return #rdy.

  Definition implInternalMemRegionResponsePort (isFetch : bool)
             : Action ty tImplInt (Bit 0) :=
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA isInFlight : Bool <-
      if useFetch then
        liftChild1OptAction (ReadReg "rpValid" pFetchRpValid (fun rpValid => Return #rpValid))
      else
        ReadReg "requester" pIntRequester (fun requester => Return (##requester`"valid")) ;
    LetA readRq : Option Addr <-
      if useFetch then
        liftChild1OptAction (ReadReg "readRq" pFetchReadRq (fun v => Return #v))
      else
        ReadReg "readRq" pReadRq (fun v => Return #v) ;
    LetA readRp : Option (LineReadRp r.(regionLineCfg) true) <-
      if useFetch then
        liftChild1OptAction (ReadReg "readRp" pFetchReadRp (fun v => Return #v))
      else
        ReadReg "readRp" pReadRp (fun v => Return #v) ;
    If (And [ #isInFlight ; Not (##readRq`"valid") ; Not (##readRp`"valid") ]) Then (
      LetA rp : LineReadRp r.(regionLineCfg) true <-
        liftAction child0Path (@internalMemRegionGetReadRp r isAccessible ty useFetch) ;
      if useFetch
      then liftChild1OptAction (WriteReg pFetchReadRp (mkSome #rp) Retv)
      else WriteReg pReadRp (mkSome #rp) Retv
    ) ;
    Retv.

  Definition implInternalMemRegionReadRequestPort (isFetch : bool)
             : Action ty tImplInt (Bit 0) :=
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA readRq : Option Addr <-
      if useFetch then
        liftChild1OptAction (ReadReg "readRq" pFetchReadRq (fun v => Return #v))
      else
        ReadReg "readRq" pReadRq (fun v => Return #v) ;
    If (##readRq`"valid") Then (
      Let addr : Addr <- ##readRq`"data" ;
      Act (liftAction child0Path (internalMemRegionIssueReadRq r isAccessible useFetch addr)) ;
      if useFetch
      then liftChild1OptAction (WriteReg pFetchReadRq ConstDef Retv)
      else WriteReg pReadRq ConstDef Retv
    ) ;
    Retv.

  Definition implInternalMemRegionWriteRequestPort
             : Action ty tImplInt (Bit 0) :=
    ReadReg "writeRq" pWriteRq (fun writeRq =>
    If (##writeRq`"valid") Then (
      Let rq : LineWriteRq r.(regionLineCfg) true <- ##writeRq`"data" ;
      Act (liftAction child0Path (internalMemRegionLineWrite r isAccessible rq)) ;
      Act (WriteReg pWriteRq ConstDef Retv) ;
      WriteReg pWriteBusy (ConstBool false) Retv
    ) ;
    Retv).

  Definition implInternalMemRegionReadRp
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplInt (Option FullCapWithTag) :=
    LetA rpOpt : Option (LineReadRp r.(regionLineCfg) true) <- implInternalMemRegionLineReadRp req ;
    LetIf resOpt : Option FullCapWithTag <-
      If (##rpOpt`"valid") Then (
        Let  rp  : LineReadRp r.(regionLineCfg) true <- ##rpOpt`"data" ;
        LetL res : FullCapWithTag                    <- memExtractReadCap r true #addr #memSize #rp ;
        Return (mkSome #res)
      )  ;
    Return #resOpt.

  Definition implInternalMemRegionWriteRq
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplInt Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      LetL rq : LineWriteRq r.(regionLineCfg) true <- memBuildLineWriteRq r true #addr #stVal #memSize ;
      implInternalMemRegionLineWriteRq rq
    ).

End ImplInternalMemRegionActions.

Arguments implInternalMemRegionLineReadRdy r isAccessible {ty} isFetch.
Arguments implInternalMemRegionLineWriteRdy r isAccessible {ty}.
Arguments implInternalMemRegionLineReadRq r isAccessible [ty] req addr.
Arguments implInternalMemRegionLineReadRp r isAccessible {ty} req.
Arguments implInternalMemRegionLineDeqRp r isAccessible {ty} req.
Arguments implInternalMemRegionLineWriteRq r isAccessible [ty] rq.
Arguments implInternalMemRegionResponsePort r isAccessible {ty} isFetch.
Arguments implInternalMemRegionReadRequestPort r isAccessible {ty} isFetch.
Arguments implInternalMemRegionWriteRequestPort r isAccessible {ty}.
Arguments implInternalMemRegionReadRp r isAccessible [ty] req addr memSize.
Arguments implInternalMemRegionWriteRq r isAccessible [ty] addr stVal memSize.

Section ImplInternalMemTargetPortActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tIntSpec := internalMemRegionTree r true.
  Local Definition tImplIntTargetPort := implInternalMemRegionTree r true.
  Local Definition pTargetPortLineReadRqReady  : SendPath tImplIntTargetPort := Eval cbn in (getChildSendPathTree tImplIntTargetPort "lineReadRqReady").
  Local Definition pTargetPortLineWriteRqReady : SendPath tImplIntTargetPort := Eval cbn in (getChildSendPathTree tImplIntTargetPort "lineWriteRqReady").
  Local Definition pTargetPortLineReadRpReady  : RecvPath tImplIntTargetPort := Eval cbn in (getChildRecvPathTree tImplIntTargetPort "lineReadRpReady").

  Local Definition pTargetPortLineReadRqValid  : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineReadRqValid").
  Local Definition pTargetPortLineReadRq       : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineReadRq").
  Local Definition pTargetPortLineReadRp       : SendPath tIntSpec := Eval cbn in (getChildSendPathTree tIntSpec "lineReadRp").
  Local Definition pTargetPortLineWriteRqValid : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineWriteRqValid").
  Local Definition pTargetPortLineWriteRq      : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineWriteRq").

  Definition implInternalMemRegionTargetPortReadRq : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rdy : Bool <- @implInternalMemRegionLineReadRdy r true ty false ;
    Act (Send pTargetPortLineReadRqReady #rdy Retv) ;
    If #rdy Then (
      LetA valid : Bool <- liftAction child0Path (Recv "valid" pTargetPortLineReadRqValid (fun valid => Return #valid)) ;
      If #valid Then (
        LetA addr : Addr <- liftAction child0Path (Recv "addr" pTargetPortLineReadRq (fun addr => Return #addr)) ;
        Act (implInternalMemRegionLineReadRq r true ReqTarget addr) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  Definition implInternalMemRegionTargetPortReadRp : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rpOpt : Option (LineReadRp r.(regionLineCfg) true) <- @implInternalMemRegionLineReadRp r true ty ReqTarget ;
    If (##rpOpt`"valid") Then (
      Recv "rpReady" pTargetPortLineReadRpReady (fun rpReady =>
      If #rpReady Then (
        Let rp : LineReadRp r.(regionLineCfg) true <- ##rpOpt`"data" ;
        Act (@implInternalMemRegionLineDeqRp r true ty ReqTarget) ;
        liftAction child0Path (Send pTargetPortLineReadRp #rp Retv)
      ) ;
      Retv)
    ) ;
    Retv.

  Definition implInternalMemRegionTargetPortWrite : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rdy : Bool <- @implInternalMemRegionLineWriteRdy r true ty ;
    Act (Send pTargetPortLineWriteRqReady #rdy Retv) ;
    If #rdy Then (
      LetA valid : Bool <- liftAction child0Path (Recv "valid" pTargetPortLineWriteRqValid (fun valid => Return #valid)) ;
      If #valid Then (
        LetA rq : LineWriteRq r.(regionLineCfg) true <- liftAction child0Path (Recv "rq" pTargetPortLineWriteRq (fun rq => Return #rq)) ;
        Act (implInternalMemRegionLineWriteRq r true rq) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

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
  Local Definition pExtReadRq            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "readRq").
  Local Definition pExtReadRp            : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "readRp").
  Local Definition pExtWriteRq           : RegPath  tImplExt      := Eval cbn in (getChildRegPathTree tImplExt "writeRq").

  Local Definition pFetchLineReadRqReady : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRqReady").
  Local Definition pFetchLineReadRpValid : RecvPath tImplExtFetch := Eval cbn in (getChildRecvPathTree tImplExtFetch "lineReadRpValid").
  Local Definition pFetchLineReadRpReady : SendPath tImplExtFetch := Eval cbn in (getChildSendPathTree tImplExtFetch "lineReadRpReady").
  Local Definition pFetchState           : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "state").
  Local Definition pFetchNextLineAddr    : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "nextLineAddr").
  Local Definition pExtFetchReadRq       : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "readRq").
  Local Definition pExtFetchReadRp       : RegPath  tImplExtFetch := Eval cbn in (getChildRegPathTree tImplExtFetch "readRp").

  Local Definition recvLineReadRqReady {k : Kind} (isFetch : bool)
    (cont : ty Bool -> Action ty tImplExt k) : Action ty tImplExt k :=
    LetA rdy : Bool <-
      if isFetch && r.(hasExtraFetchPort)
      then liftChild1OptAction (Recv "rdy" pFetchLineReadRqReady (fun v => Return #v))
      else Recv "rdy" pLineReadRqReady (fun v => Return #v) ;
    cont rdy.

  Local Definition recvLineReadRpValid {k : Kind} (isFetch : bool)
    (cont : ty Bool -> Action ty tImplExt k) : Action ty tImplExt k :=
    LetA rpValid : Bool <-
      if isFetch && r.(hasExtraFetchPort)
      then liftChild1OptAction (Recv "rpValid" pFetchLineReadRpValid (fun v => Return #v))
      else Recv "rpValid" pLineReadRpValid (fun v => Return #v) ;
    cont rpValid.

  Local Definition readExtState {k : Kind} (isFetch : bool)
    (cont : ty (ExtRegionState r.(regionLineCfg)) -> Action ty tImplExt k) : Action ty tImplExt k :=
    LetA state : ExtRegionState r.(regionLineCfg) <-
      if isFetch && r.(hasExtraFetchPort)
      then liftChild1OptAction (ReadReg "state" pFetchState (fun v => Return #v))
      else ReadReg "state" pState (fun v => Return #v) ;
    cont state.

  Local Definition writeExtState {k : Kind} (isFetch : bool)
    (v : Expr ty (ExtRegionState r.(regionLineCfg))) (cont : Action ty tImplExt k) : Action ty tImplExt k :=
    Act (if isFetch && r.(hasExtraFetchPort)
         then liftChild1OptAction (WriteReg pFetchState v Retv)
         else WriteReg pState v Retv) ;
    cont.

  Local Definition readExtNextLineAddr {k : Kind} (isFetch : bool)
    (cont : ty (Option Addr) -> Action ty tImplExt k) : Action ty tImplExt k :=
    LetA nextLineAddr : Option Addr <-
      if isFetch && r.(hasExtraFetchPort)
      then liftChild1OptAction (ReadReg "nextLineAddr" pFetchNextLineAddr (fun v => Return #v))
      else ReadReg "nextLineAddr" pNextLineAddr (fun v => Return #v) ;
    cont nextLineAddr.

  Local Definition writeExtNextLineAddr {k : Kind} (isFetch : bool)
    (v : Expr ty (Option Addr)) (cont : Action ty tImplExt k) : Action ty tImplExt k :=
    Act (if isFetch && r.(hasExtraFetchPort)
         then liftChild1OptAction (WriteReg pFetchNextLineAddr v Retv)
         else WriteReg pNextLineAddr v Retv) ;
    cont.

  Definition implExternalMemRegionLineReadRq (isFetch : bool) (addr : ty Addr)
             : Action ty tImplExt Bool :=
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA readRq : Option Addr <-
      if useFetch
      then liftChild1OptAction (ReadReg "readRq" pExtFetchReadRq (fun v => Return #v))
      else ReadReg "readRq" pExtReadRq (fun v => Return #v) ;
    Let rdy : Bool <- Not (##readRq`"valid") ;
    If #rdy Then (
      if useFetch
      then liftChild1OptAction (WriteReg pExtFetchReadRq (mkSome #addr) Retv)
      else WriteReg pExtReadRq (mkSome #addr) Retv
    ) ;
    Return #rdy.

  Definition implExternalMemRegionLineReadRp (isFetch : bool)
             : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg) false)) :=
    if isFetch && r.(hasExtraFetchPort)
    then liftChild1OptAction (ReadReg "readRp" pExtFetchReadRp (fun v => Return #v))
    else ReadReg "readRp" pExtReadRp (fun v => Return #v).

  Definition implExternalMemRegionLineDeqRp (isFetch : bool)
             : Action ty tImplExt (Bit 0) :=
    if isFetch && r.(hasExtraFetchPort)
    then liftChild1OptAction (WriteReg pExtFetchReadRp ConstDef Retv)
    else WriteReg pExtReadRp ConstDef Retv.

  Definition implExternalMemRegionLineWriteRq
             (rq : ty (LineWriteRq r.(regionLineCfg) false))
             : Action ty tImplExt Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      ReadReg "writeRq" pExtWriteRq (fun writeRq =>
      Let rdy : Bool <- Not (##writeRq`"valid") ;
      If #rdy Then (
        WriteReg pExtWriteRq (mkSome #rq) Retv
      ) ;
      Return #rdy)
    ).

  Definition implExternalMemRegionResponsePort (isFetch : bool)
             : Action ty tImplExt (Bit 0) :=
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA readRp : Option (LineReadRp r.(regionLineCfg) false) <-
      if useFetch
      then liftChild1OptAction (ReadReg "readRp" pExtFetchReadRp (fun v => Return #v))
      else ReadReg "readRp" pExtReadRp (fun v => Return #v) ;
    If (Not (##readRp`"valid")) Then (
      recvLineReadRpValid isFetch (fun rpValid =>
      If #rpValid Then (
        LetA rp : LineReadRp r.(regionLineCfg) false <-
          liftAction child0Path (@externalMemRegionGetReadRp r ty isFetch) ;
        Act (if useFetch
             then liftChild1OptAction (Send pFetchLineReadRpReady ($0 : Expr ty (Bit 0)) Retv)
             else Send pLineReadRpReady ($0 : Expr ty (Bit 0)) Retv) ;
        if useFetch
        then liftChild1OptAction (WriteReg pExtFetchReadRp (mkSome #rp) Retv)
        else WriteReg pExtReadRp (mkSome #rp) Retv
      ) ;
      Retv)
    ) ;
    Retv.

  Definition implExternalMemRegionReadRequestPort (isFetch : bool)
             : Action ty tImplExt (Bit 0) :=
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    LetA readRq : Option Addr <-
      if useFetch
      then liftChild1OptAction (ReadReg "readRq" pExtFetchReadRq (fun v => Return #v))
      else ReadReg "readRq" pExtReadRq (fun v => Return #v) ;
    If (##readRq`"valid") Then (
      recvLineReadRqReady isFetch (fun rdy =>
      If #rdy Then (
        Let addr : Addr <- ##readRq`"data" ;
        Act (liftAction child0Path (externalMemRegionIssueReadRq r isFetch addr)) ;
        if useFetch
        then liftChild1OptAction (WriteReg pExtFetchReadRq ConstDef Retv)
        else WriteReg pExtReadRq ConstDef Retv
      ) ;
      Retv)
    ) ;
    Retv.

  Definition implExternalMemRegionWriteRequestPort
             : Action ty tImplExt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      ReadReg "writeRq" pExtWriteRq (fun writeRq =>
      If (##writeRq`"valid") Then (
        Recv "rdy" pLineWriteRqReady (fun rdy =>
        If #rdy Then (
          Let rq : LineWriteRq r.(regionLineCfg) false <- ##writeRq`"data" ;
          Act (liftAction child0Path (externalMemRegionLineWrite r rq)) ;
          WriteReg pExtWriteRq ConstDef Retv
        ) ;
        Retv)
      ) ;
      Retv)
    ).

  Definition implExternalMemRegionReadRq
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt Bool :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    readExtState isFetch (fun state =>
    LetIf rdy : Bool <-
      If (##state `? "Idle") Then (
        Let  addr0 : Addr <- memLineAddr r #addr ;
        LetA rdy0  : Bool <- implExternalMemRegionLineReadRq isFetch addr0 ;
        If #rdy0 Then (
          Act (writeExtState isFetch (UNION (ExtRegionStateList r.(regionLineCfg), "ReadWait" ::= ($0 : Expr ty (Bit 0)))) Retv) ;
          Act (if useFetch then Retv else WriteReg pExtRequester (mkRequesterOpt req) Retv) ;
          Let crosses : Bool <- memCrossesLine r #addr #memSize ;
          If #crosses Then (
            Let addr1 : Addr <- memNextLineAddr r #addr ;
            writeExtNextLineAddr isFetch (mkSome #addr1) Retv
          ) ;
          Retv
        ) ;
        Return #rdy0
      ) ;
    Return #rdy).

  Definition implExternalMemRegionReadRp0 (isFetch : bool) : Action ty tImplExt (Bit 0) :=
    readExtState isFetch (fun state =>
    readExtNextLineAddr isFetch (fun nextLineAddr =>
    If (And [ ##state `? "ReadWait" ; ##nextLineAddr`"valid" ]) Then (
      LetA rp0Opt : Option (LineReadRp r.(regionLineCfg) false) <- implExternalMemRegionLineReadRp isFetch ;
      If (##rp0Opt`"valid") Then (
        Let rp0 : LineReadRp r.(regionLineCfg) false <- ##rp0Opt`"data" ;
        Act (implExternalMemRegionLineDeqRp isFetch) ;
        writeExtState isFetch (UNION (ExtRegionStateList r.(regionLineCfg), "ReadRp0" ::= #rp0)) Retv
      ) ;
      Retv
    ) ;
    Retv)).

  Definition implExternalMemRegionReadRq1 (isFetch : bool) : Action ty tImplExt (Bit 0) :=
    readExtState isFetch (fun state =>
    readExtNextLineAddr isFetch (fun nextLineAddr =>
    If (And [ ##state `? "ReadRp0" ; ##nextLineAddr`"valid" ]) Then (
      Let  addr1 : Addr <- ##nextLineAddr`"data" ;
      LetA rdy1  : Bool <- implExternalMemRegionLineReadRq isFetch addr1 ;
      If #rdy1 Then (
        writeExtNextLineAddr isFetch ConstDef Retv
      ) ;
      Retv
    ) ;
    Retv)).

  Definition implExternalMemRegionReadRp
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt (Option FullCapWithTag) :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    readExtState isFetch (fun state =>
    readExtNextLineAddr isFetch (fun nextLineAddr =>
    LetA isMatch : Bool <-
      if useFetch then
        Return (ConstBool true)
      else
        ReadReg "requester" pExtRequester (fun requester =>
        Return (isRequesterMatch #requester req)) ;
    LetIf resOpt : Option FullCapWithTag <-
      If (And [ #isMatch ;
                Or [ ##state `? "ReadWait" ; ##state `? "ReadRp0" ] ;
                Not (##nextLineAddr`"valid") ]) Then (
        LetA lastRpOpt : Option (LineReadRp r.(regionLineCfg) false) <- implExternalMemRegionLineReadRp isFetch ;
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
    Return #resOpt)).

  Definition implExternalMemRegionDeqRp (req : MemRequester) : Action ty tImplExt (Bit 0) :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    Act (implExternalMemRegionLineDeqRp isFetch) ;
    writeExtState isFetch (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) (
    if useFetch then Retv else WriteReg pExtRequester ConstDef Retv).

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
          LetA rdy0 : Bool                                <- implExternalMemRegionLineWriteRq rq0 ;
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

  Definition implExternalMemRegionWriteStep : Action ty tImplExt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      ReadReg "state" pState (fun state =>
      If (##state `? "WriteRq1") Then (
        Let  rq1  : LineWriteRq r.(regionLineCfg) false <- ##state `! "WriteRq1" ;
        LetA rdy1 : Bool                                <- implExternalMemRegionLineWriteRq rq1 ;
        If #rdy1 Then (
          WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
        ) ;
        Retv
      ) ;
      Retv)
    ).

End ImplExternalMemRegionActions.

Arguments implExternalMemRegionLineReadRq r [ty] isFetch addr.
Arguments implExternalMemRegionLineReadRp r {ty} isFetch.
Arguments implExternalMemRegionLineDeqRp r {ty} isFetch.
Arguments implExternalMemRegionLineWriteRq r [ty] rq.
Arguments implExternalMemRegionResponsePort r {ty} isFetch.
Arguments implExternalMemRegionReadRequestPort r {ty} isFetch.
Arguments implExternalMemRegionWriteRequestPort r {ty}.
Arguments implExternalMemRegionReadRq r [ty] req addr memSize.
Arguments implExternalMemRegionReadRp0 r {ty} isFetch.
Arguments implExternalMemRegionReadRq1 r {ty} isFetch.
Arguments implExternalMemRegionReadRp r [ty] req addr memSize.
Arguments implExternalMemRegionDeqRp r {ty} req.
Arguments implExternalMemRegionWriteRq r [ty] addr stVal memSize.
Arguments implExternalMemRegionWriteStep r {ty}.

(* ===========================================================================
 * Split-Phase Implementation Actions for CustomMem
 * =========================================================================== *)

Section ImplCustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree DomainElem).
  Variable readAction : forall ty, ReadPortSel r.(hasExtraFetchPort) -> ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp r.(regionLineCfg) false).
  Variable writeAction : forall ty, ty (LineWriteRq r.(regionLineCfg) false) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tImplCust      := implCustomMemRegionTree r children.
  Local Definition tImplCustFetch := implCustomMemFetchTree r.

  Local Definition pCustState      : RegPath tImplCust      := Eval cbn in (getChildRegPathTree tImplCust "state").
  Local Definition pCustRequester  : RegPath tImplCust      := Eval cbn in (getChildRegPathTree tImplCust "requester").
  Local Definition pCustFetchState : RegPath tImplCustFetch := Eval cbn in (getChildRegPathTree tImplCustFetch "state").

  Local Definition readCustState {k : Kind} (isFetch : bool)
    (cont : ty (CustomRegionState r.(regionLineCfg)) -> Action ty tImplCust k) : Action ty tImplCust k :=
    LetA state : CustomRegionState r.(regionLineCfg) <-
      if isFetch && r.(hasExtraFetchPort)
      then liftChild1OptAction (ReadReg "state" pCustFetchState (fun v => Return #v))
      else ReadReg "state" pCustState (fun v => Return #v) ;
    cont state.

  Local Definition writeCustState {k : Kind} (isFetch : bool)
    (v : Expr ty (CustomRegionState r.(regionLineCfg))) (cont : Action ty tImplCust k) : Action ty tImplCust k :=
    Act (if isFetch && r.(hasExtraFetchPort)
         then liftChild1OptAction (WriteReg pCustFetchState v Retv)
         else WriteReg pCustState v Retv) ;
    cont.

  Definition implCustomMemRegionReadRq (req : MemRequester) (addr : ty Addr)
             : Action ty tImplCust Bool :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    readCustState isFetch (fun state =>
    Let isIdle : Bool <- ##state `? "Idle" ;
    If #isIdle Then (
      Let  addr0 : Addr                               <- memLineAddr r #addr ;
      LetA rp0   : LineReadRp r.(regionLineCfg) false <- liftAction child0Path (customMemRegionLineRead r children readAction isFetch addr0) ;
      writeCustState isFetch (UNION (CustomRegionStateList r.(regionLineCfg), "ReadRp0" ::= #rp0)) (
      if useFetch then Retv else WriteReg pCustRequester (mkRequesterOpt req) Retv)
    ) ;
    Return #isIdle).

  Definition implCustomMemRegionReadRp
             (req : MemRequester)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplCust (Option FullCapWithTag) :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    readCustState isFetch (fun state =>
    LetA isMatch : Bool <-
      if useFetch then
        Return (ConstBool true)
      else
        ReadReg "requester" pCustRequester (fun requester =>
        Return (isRequesterMatch #requester req)) ;
    LetIf resOpt : Option FullCapWithTag <-
      If (And [ ##state `? "ReadRp0" ; #isMatch ]) Then (
        Let  rp0     : LineReadRp r.(regionLineCfg) false <- ##state `! "ReadRp0" ;
        Let  crosses : Bool                               <- memCrossesLine r #addr #memSize ;
        LetIf rp1 : LineReadRp r.(regionLineCfg) false <-
          If #crosses Then (
            Let addr1 : Addr <- memNextLineAddr r #addr ;
            liftAction child0Path (customMemRegionLineRead r children readAction isFetch addr1)
          ) Else (
            Return ConstDef
          ) ;
        Let  rp      : LineReadRp r.(regionLineCfg) false <- memMergeLineReadRp r false #addr #rp0 #rp1 ;
        LetL res     : FullCapWithTag                     <- memExtractReadCap r false #addr #memSize #rp ;
        Return (mkSome #res)
      ) ;
    Return #resOpt).

  Definition implCustomMemRegionDeqRp (req : MemRequester) : Action ty tImplCust (Bit 0) :=
    let isFetch := isFetchRequester req in
    let useFetch := isFetch && r.(hasExtraFetchPort) in
    writeCustState isFetch (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) (
    if useFetch then Retv else WriteReg pCustRequester ConstDef Retv).

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

  Definition implCustomMemRegionWriteStep : Action ty tImplCust (Bit 0) :=
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

End ImplCustomMemRegionActions.

Arguments implCustomMemRegionReadRq r children readAction [ty] req addr.
Arguments implCustomMemRegionReadRp r children readAction [ty] req addr memSize.
Arguments implCustomMemRegionDeqRp r children {ty} req.
Arguments implCustomMemRegionWriteRq r children writeAction [ty] addr stVal memSize.
Arguments implCustomMemRegionWriteStep r children writeAction {ty}.

(* ===========================================================================
 * Unified Per-Region Implementation Dispatch
 * =========================================================================== *)

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
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem isAccessible _ _ => implInternalMemRegionLineReadRq r isAccessible req addr
  | ExternalMem => implExternalMemRegionReadRq r req addr memSize
  | CustomMem children readAct _ _ => implCustomMemRegionReadRq r children readAct req addr
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
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) (Option FullCapWithTag) with
  | InternalMem isAccessible _ _ => implInternalMemRegionReadRp r isAccessible req addr memSize
  | ExternalMem => implExternalMemRegionReadRp r req addr memSize
  | CustomMem children readAct _ _ => implCustomMemRegionReadRp r children readAct req addr memSize
  end.

Definition implMemRegionDeqRp
           (r : MemRegion)
           {ty : Kind -> Type}
           (req : MemRequester)
           : Action ty (implMemRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) (Bit 0) with
  | InternalMem isAccessible _ _ => @implInternalMemRegionLineDeqRp r isAccessible ty req
  | ExternalMem => @implExternalMemRegionDeqRp r ty req
  | CustomMem children _ _ _ => @implCustomMemRegionDeqRp r children ty req
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
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem isAccessible _ _ => implInternalMemRegionWriteRq r isAccessible addr stVal memSize
  | ExternalMem => implExternalMemRegionWriteRq r addr stVal memSize
  | CustomMem children _ writeAct _ => implCustomMemRegionWriteRq r children writeAct addr stVal memSize
  end.

Arguments implMemRegionReadRq r [ty] req addr memSize.
Arguments implMemRegionReadRp r [ty] req addr memSize.
Arguments implMemRegionDeqRp r {ty} req.
Arguments implMemRegionWriteRq r [ty] addr stVal memSize.

Definition implMemRegionFetchRpActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem isAccessible _ _ =>
      if r.(hasExtraFetchPort) then
        [ (r.(regionDom), fun ty => @implInternalMemRegionResponsePort r isAccessible ty true) ]
      else []
  | ExternalMem =>
      if r.(hasExtraFetchPort) then
        [ (r.(regionDom), fun ty => @implExternalMemRegionResponsePort r ty true) ]
      else []
  | CustomMem _ _ _ _ => []
  end.

Definition implMemRegionFetchRqActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem isAccessible _ _ =>
      if r.(hasExtraFetchPort) then
        [ (r.(regionDom), fun ty => @implInternalMemRegionReadRequestPort r isAccessible ty true) ]
      else []
  | ExternalMem =>
      if r.(hasExtraFetchPort) then
        [ (r.(regionDom), fun ty => @implExternalMemRegionReadRequestPort r ty true) ]
      else []
  | CustomMem _ _ _ _ => []
  end.

Definition implMemRegionDataReadRpActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem isAccessible _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionResponsePort r isAccessible ty false) ]
  | ExternalMem =>
      [ (r.(regionDom), fun ty => @implExternalMemRegionResponsePort r ty false) ]
  | CustomMem _ _ _ _ => []
  end.

Definition implMemRegionDataReadRqActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem isAccessible _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionReadRequestPort r isAccessible ty false) ]
  | ExternalMem =>
      [ (r.(regionDom), fun ty => @implExternalMemRegionReadRequestPort r ty false) ]
  | CustomMem _ _ _ _ => []
  end.

Definition implMemRegionDataWriteRqActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem isAccessible _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionWriteRequestPort r isAccessible ty) ]
  | ExternalMem =>
      [ (r.(regionDom), fun ty => @implExternalMemRegionWriteRequestPort r ty) ]
  | CustomMem _ _ _ _ => []
  end.

Definition implMemRegionFetchCrossLineActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem _ _ _ => []
  | ExternalMem =>
      if r.(hasExtraFetchPort) then
        [ (r.(regionDom), fun ty => (Act (@implExternalMemRegionReadRp0 r ty true) ; @implExternalMemRegionReadRq1 r ty true)) ]
      else []
  | CustomMem _ _ _ _ => []
  end.

Definition implMemRegionDataCrossLineActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem _ _ _ => []
  | ExternalMem =>
      [ (r.(regionDom), fun ty => @implExternalMemRegionWriteStep r ty) ;
        (r.(regionDom), fun ty => (Act (@implExternalMemRegionReadRp0 r ty false) ; @implExternalMemRegionReadRq1 r ty false)) ]
  | CustomMem children _ writeAct _ =>
      [ (r.(regionDom), fun ty => @implCustomMemRegionWriteStep r children writeAct ty) ]
  end.

Definition implMemRegionTargetPortRqActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem true _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionTargetPortWrite r ty) ;
        (r.(regionDom), fun ty => @implInternalMemRegionTargetPortReadRq r ty) ]
  | _ => []
  end.

Definition implMemRegionTargetPortRpActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem true _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionTargetPortReadRp r ty) ]
  | _ => []
  end.

(* ===========================================================================
 * Multi-Region Composite Implementation Tree, Router & Collectors
 * =========================================================================== *)

Fixpoint implRegionsChildren (regions : list MemRegion) : list (Tree DomainElem) :=
  match regions with
  | [] => []
  | r :: rs => [ implMemRegionTree r ; Node "mem" (implRegionsChildren rs) ]
  end.

Definition implRegionsTree (regions : list MemRegion) : Tree DomainElem :=
  Node "mem" (implRegionsChildren regions).

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
           (getActions : forall r : MemRegion, list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))))
           (regions : list MemRegion)
           : list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) :=
    match regions return list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) with
    | [] => []
    | r :: rs =>
        let curr := map (fun '(dom, act) => (dom, fun ty => liftAction child0Path (act ty)))
                        (getActions r) in
        let rest := map (fun '(dom, act) => (dom, fun ty => liftAction child1Path (act ty)))
                        (implCollectRegionActions getActions rs) in
        (curr ++ rest)%list
    end.

  Definition implCollectFetchRpActions := implCollectRegionActions implMemRegionFetchRpActions.
  Definition implCollectFetchRqActions := implCollectRegionActions implMemRegionFetchRqActions.
  Definition implCollectDataReadRpActions := implCollectRegionActions implMemRegionDataReadRpActions.
  Definition implCollectDataReadRqActions := implCollectRegionActions implMemRegionDataReadRqActions.
  Definition implCollectDataWriteRqActions := implCollectRegionActions implMemRegionDataWriteRqActions.
  Definition implCollectFetchCrossLineActions := implCollectRegionActions implMemRegionFetchCrossLineActions.
  Definition implCollectDataCrossLineActions := implCollectRegionActions implMemRegionDataCrossLineActions.
  Definition implCollectTargetPortRqActions := implCollectRegionActions implMemRegionTargetPortRqActions.
  Definition implCollectTargetPortRpActions := implCollectRegionActions implMemRegionTargetPortRpActions.
End ImplCollectors.

Section ImplRegionsRouter.
  Variable ty : Kind -> Type.

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

End ImplRegionsRouter.

Section ImplMemModel.
  Variable dom : string.
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

    Definition implMemCollectFetchRpActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectFetchRpActions regions).

    Definition implMemCollectFetchRqActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectFetchRqActions regions).

    Definition implMemCollectDataReadRpActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectDataReadRpActions regions).

    Definition implMemCollectDataReadRqActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectDataReadRqActions regions).

    Definition implMemCollectDataWriteRqActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectDataWriteRqActions regions).

    Definition implMemCollectFetchCrossLineActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectFetchCrossLineActions regions).

    Definition implMemCollectDataCrossLineActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectDataCrossLineActions regions).

    Definition implMemCollectTargetPortRqActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectTargetPortRqActions regions).

    Definition implMemCollectTargetPortRpActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectTargetPortRpActions regions).

    (* 1. Instruction Memory Channel *)
    Definition implReadInstRq (addr : ty Addr) : Action ty implMemTree Bool :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      implRegionsReadRq regions ReqFetch addr instSz.

    Definition implGetInstRp (addr : ty Addr) : Action ty implMemTree (Option Inst) :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      LetA rpOpt : Option FullCapWithTag <- implRegionsReadRp regions ReqFetch addr instSz ;
      LetIf instOpt : Option Inst <-
        If (##rpOpt`"valid") Then (
          Let  fullVal : FullCapWithTag <- ##rpOpt`"data" ;
          Let  rawInst : Inst           <- ##fullVal`"addr" ;
          LetL expInst : Inst           <- preDecode rawInst ;
          Return (mkSome #expInst)
        ) Else (
          Return ConstDef
        ) ;
      Return #instOpt.

    Definition implDeqInstRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
      implRegionsDeqRp regions ReqFetch addr.

    (* 2. Data Load Channel *)
    Definition implReadMemRq (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
      implRegionsReadRq regions ReqDeferred addr memSize.

    Definition implGetMemRp (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree (Option FullCapWithTag) :=
      implRegionsReadRp regions ReqDeferred addr memSize.

    Definition implDeqMemRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
      implRegionsDeqRp regions ReqDeferred addr.

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
      implReadRevBitRqFor ReqDeferred base.

    Definition implGetDeqRevBitRp (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
      implGetDeqRevBitRpFor ReqDeferred base.

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

    Definition implFenceIReq : Action ty implMemTree Bool :=
      Return (ConstBool true).

    Definition implFenceIAck : Action ty implMemTree Bool :=
      Return (ConstBool true).

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
      mem_fenceI_req     := implFenceIReq ;
      mem_fenceI_ack     := implFenceIAck
    |}.

  End Ty.

End ImplMemModel.
