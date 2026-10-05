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

Definition ExtRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadWait", Bit 0) ;
    ("ReadRp0",  LineReadRp false cfg) ;
    ("WriteRq1", LineWriteRq false cfg) ].

Definition ExtRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (ExtRegionStateList cfg).

Definition CustomRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadRp0",  LineReadRp false cfg) ;
    ("WriteRq1", LineWriteRq false cfg) ].

Definition CustomRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (CustomRegionStateList cfg).

Definition implInternalMemRegionExtraChildren (r : MemRegion) (hasExtraFetchPort : bool) : list (Tree DomainElem) :=
  ([ Leaf "rpValid"          (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ;
     Leaf "targetRpPending"  (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ;
     Leaf "writeBusy"        (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ;
     Leaf "lineReadRqReady"  (r.(regionDom), ESend Bool) ;
     Leaf "lineWriteRqReady" (r.(regionDom), ESend Bool) ;
     Leaf "lineReadRpReady"  (r.(regionDom), ERecv Bool) ] ++
   if hasExtraFetchPort then
     [ Leaf "fetchRpValid"   (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ]
   else [])%list.

Definition implExternalMemRegionExtraChildren (r : MemRegion) (hasExtraFetchPort : bool) : list (Tree DomainElem) :=
  ([ Leaf "lineReadRqReady"  (r.(regionDom), ERecv Bool) ;
     Leaf "lineWriteRqReady" (r.(regionDom), ERecv Bool) ;
     Leaf "lineReadRpValid"  (r.(regionDom), ERecv Bool) ;
     Leaf "lineReadRpReady"  (r.(regionDom), ESend (Bit 0)) ;
     Leaf "state"            (r.(regionDom), EReg (Build_Reg (ExtRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
     Leaf "nextLineAddr"     (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ] ++
   if hasExtraFetchPort then
     [ Leaf "fetchLineReadRqReady" (r.(regionDom), ERecv Bool) ;
       Leaf "fetchLineReadRpValid" (r.(regionDom), ERecv Bool) ;
       Leaf "fetchLineReadRpReady" (r.(regionDom), ESend (Bit 0)) ;
       Leaf "fetchState"           (r.(regionDom), EReg (Build_Reg (ExtRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
       Leaf "fetchNextLineAddr"    (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ]
   else [])%list.

Definition implCustomMemRegionExtraChildren (r : MemRegion) (hasExtraFetchPort : bool) : list (Tree DomainElem) :=
  ([ Leaf "state" (r.(regionDom), EReg (Build_Reg (CustomRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ] ++
   if hasExtraFetchPort then
     [ Leaf "fetchState" (r.(regionDom), EReg (Build_Reg (CustomRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ]
   else [])%list.

Definition implInternalMemRegionTree (r : MemRegion) (isAccessible hasExtraFetchPort : bool) : Tree DomainElem :=
  Node r.(regionName) (internalMemRegionTree r isAccessible :: implInternalMemRegionExtraChildren r hasExtraFetchPort).

Definition implExternalMemRegionTree (r : MemRegion) (hasExtraFetchPort : bool) : Tree DomainElem :=
  Node r.(regionName) (externalMemRegionTree r hasExtraFetchPort :: implExternalMemRegionExtraChildren r hasExtraFetchPort).

Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) (hasExtraFetchPort : bool) : Tree DomainElem :=
  Node r.(regionName) (customMemRegionTree r children :: implCustomMemRegionExtraChildren r hasExtraFetchPort).

Definition implMemRegionTree (r : MemRegion) : Tree DomainElem :=
  match r.(regionKind) with
  | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
  | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
  | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
  end.

Definition liftToImplRegion {ty : Kind -> Type} (r : MemRegion) {k : Kind}
  (act : Action ty (memRegionTree r) k) : Action ty (implMemRegionTree r) k :=
  match r.(regionKind) as rk
    return Action ty (match rk with
                      | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                      | ExternalMem => externalMemRegionTree r r.(hasExtraFetchPort)
                      | CustomMem children _ _ _ => customMemRegionTree r children
                      end) k ->
           Action ty (match rk with
                      | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                      | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                      | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
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
  Variable hasExtraFetchPort : bool.
  Variable ty : Kind -> Type.

  Local Definition tImplInt := implInternalMemRegionTree r isAccessible hasExtraFetchPort.
  Local Definition pTargetRpPending  : RegPath tImplInt := Eval cbn in (getChildRegPathTree tImplInt "targetRpPending").
  Local Definition pWriteBusy        : RegPath tImplInt := Eval cbn in (getChildRegPathTree tImplInt "writeBusy").
  Local Definition pRpValidTrue      : RegPath (implInternalMemRegionTree r isAccessible true)  := Eval cbn in (getChildRegPathTree (implInternalMemRegionTree r isAccessible true) "rpValid").
  Local Definition pFetchRpValidTrue : RegPath (implInternalMemRegionTree r isAccessible true)  := Eval cbn in (getChildRegPathTree (implInternalMemRegionTree r isAccessible true) "fetchRpValid").
  Local Definition pRpValidFalse     : RegPath (implInternalMemRegionTree r isAccessible false) := Eval cbn in (getChildRegPathTree (implInternalMemRegionTree r isAccessible false) "rpValid").

  Local Definition readRpValid {k : Kind} (isFetch : bool)
    (cont : ty Bool -> Action ty tImplInt k) : Action ty tImplInt k :=
    match hasExtraFetchPort as b
      return (ty Bool -> Action ty (implInternalMemRegionTree r isAccessible b) k) ->
             Action ty (implInternalMemRegionTree r isAccessible b) k with
    | true  => fun c => if isFetch then ReadReg "rpValid" pFetchRpValidTrue c else ReadReg "rpValid" pRpValidTrue c
    | false => fun c => ReadReg "rpValid" pRpValidFalse c
    end cont.

  Local Definition writeRpValid {k : Kind} (isFetch : bool)
    (v : Expr ty Bool) (cont : Action ty tImplInt k) : Action ty tImplInt k :=
    match hasExtraFetchPort as b
      return Action ty (implInternalMemRegionTree r isAccessible b) k ->
             Action ty (implInternalMemRegionTree r isAccessible b) k with
    | true  => fun c => if isFetch then WriteReg pFetchRpValidTrue v c else WriteReg pRpValidTrue v c
    | false => fun c => WriteReg pRpValidFalse v c
    end cont.

  Definition implInternalMemRegionLineReadRdy (isFetch : bool)
             : Action ty tImplInt Bool :=
    readRpValid isFetch (fun rpValid =>
    Return (Not #rpValid)).

  Definition implInternalMemRegionLineWriteRdy
             : Action ty tImplInt Bool :=
    ReadReg "writeBusy" pWriteBusy (fun writeBusy =>
    Return (Not #writeBusy)).

  Definition implInternalMemRegionLineReadRq (isFetch isTarget : bool) (addr : ty Addr)
             : Action ty tImplInt Bool :=
    let useFetch := isFetch && hasExtraFetchPort in
    LetA rdy : Bool <- implInternalMemRegionLineReadRdy isFetch ;
    If #rdy Then (
      Act (liftAction child0Path (internalMemRegionIssueReadRq r isAccessible useFetch addr)) ;
      writeRpValid isFetch (ConstBool true) (
      if useFetch then Retv else WriteReg pTargetRpPending (ConstBool isTarget) Retv)
    ) ;
    Return #rdy.

  Definition implInternalMemRegionLineReadRp (isFetch isTarget : bool)
             : Action ty tImplInt (Option (LineReadRp true r.(regionLineCfg))) :=
    let useFetch := isFetch && hasExtraFetchPort in
    readRpValid isFetch (fun rpValid =>
    LetA isMatch : Bool <-
      if useFetch then
        Return (ConstBool true)
      else
        ReadReg "targetRpPending" pTargetRpPending (fun targetRpPending =>
        Return (if isTarget then #targetRpPending else Not #targetRpPending)) ;
    LetIf rpOpt : Option (LineReadRp true r.(regionLineCfg)) <-
      If (And [ #rpValid ; #isMatch ]) Then (
        LetA rp : LineReadRp true r.(regionLineCfg) <-
          liftAction child0Path (@internalMemRegionGetReadRp r isAccessible ty useFetch) ;
        Return (mkSome #rp)
      ) ;
    Return #rpOpt).

  Definition implInternalMemRegionLineDeqRp (isFetch : bool)
             : Action ty tImplInt (Bit 0) :=
    let useFetch := isFetch && hasExtraFetchPort in
    writeRpValid isFetch (ConstBool false) (
    if useFetch then Retv else WriteReg pTargetRpPending (ConstBool false) Retv).

  Definition implInternalMemRegionLineWriteRq
             (rq : ty (LineWriteRq true r.(regionLineCfg)))
             : Action ty tImplInt Bool :=
    LetA rdy : Bool <- implInternalMemRegionLineWriteRdy ;
    If #rdy Then (
      Act (liftAction child0Path (internalMemRegionLineWrite r isAccessible rq)) ;
      WriteReg pWriteBusy (ConstBool true) Retv
    ) ;
    Return #rdy.

  Definition implInternalMemRegionClearWriteBusy
             : Action ty tImplInt (Bit 0) :=
    WriteReg pWriteBusy (ConstBool false) Retv.

  Definition implInternalMemRegionReadRp
             (isFetch : bool)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplInt (Option FullCapWithTag) :=
    LetA rpOpt : Option (LineReadRp true r.(regionLineCfg)) <- implInternalMemRegionLineReadRp isFetch false ;
    LetIf resOpt : Option FullCapWithTag <-
      If (##rpOpt`"valid") Then (
        Let rp : LineReadRp true r.(regionLineCfg) <- ##rpOpt`"data" ;
        Return (mkSome (memExtractReadCap true r #addr #memSize #rp))
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
      Let rq : LineWriteRq true r.(regionLineCfg) <- memBuildLineWriteRq true r #addr #stVal #memSize ;
      implInternalMemRegionLineWriteRq rq
    ).

End ImplInternalMemRegionActions.

Arguments implInternalMemRegionLineReadRdy r isAccessible hasExtraFetchPort {ty} isFetch.
Arguments implInternalMemRegionLineWriteRdy r isAccessible hasExtraFetchPort {ty}.
Arguments implInternalMemRegionLineReadRq r isAccessible hasExtraFetchPort [ty] isFetch isTarget addr.
Arguments implInternalMemRegionLineReadRp r isAccessible hasExtraFetchPort {ty} isFetch isTarget.
Arguments implInternalMemRegionLineDeqRp r isAccessible hasExtraFetchPort {ty} isFetch.
Arguments implInternalMemRegionLineWriteRq r isAccessible hasExtraFetchPort [ty] rq.
Arguments implInternalMemRegionClearWriteBusy r isAccessible hasExtraFetchPort {ty}.
Arguments implInternalMemRegionReadRp r isAccessible hasExtraFetchPort [ty] isFetch addr memSize.
Arguments implInternalMemRegionWriteRq r isAccessible hasExtraFetchPort [ty] addr stVal memSize.

Section ImplInternalMemTargetPortActions.
  Variable r : MemRegion.
  Variable hasExtraFetchPort : bool.
  Variable ty : Kind -> Type.

  Local Definition tIntSpec := internalMemRegionTree r true.
  Local Definition tImplIntTargetPort := implInternalMemRegionTree r true hasExtraFetchPort.
  Local Definition pTargetPortLineReadRqReady  : SendPath tImplIntTargetPort := Eval cbn in (getChildSendPathTree tImplIntTargetPort "lineReadRqReady").
  Local Definition pTargetPortLineWriteRqReady : SendPath tImplIntTargetPort := Eval cbn in (getChildSendPathTree tImplIntTargetPort "lineWriteRqReady").
  Local Definition pTargetPortLineReadRpReady  : RecvPath tImplIntTargetPort := Eval cbn in (getChildRecvPathTree tImplIntTargetPort "lineReadRpReady").

  Local Definition pTargetPortLineReadRqValid  : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineReadRqValid").
  Local Definition pTargetPortLineReadRq       : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineReadRq").
  Local Definition pTargetPortLineReadRp       : SendPath tIntSpec := Eval cbn in (getChildSendPathTree tIntSpec "lineReadRp").
  Local Definition pTargetPortLineWriteRqValid : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineWriteRqValid").
  Local Definition pTargetPortLineWriteRq      : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineWriteRq").

  Definition implInternalMemRegionTargetPortReadRq : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rdy : Bool <- @implInternalMemRegionLineReadRdy r true hasExtraFetchPort ty false ;
    Act (Send pTargetPortLineReadRqReady #rdy Retv) ;
    If #rdy Then (
      LetA valid : Bool <- liftAction child0Path (Recv "valid" pTargetPortLineReadRqValid (fun valid => Return #valid)) ;
      If #valid Then (
        LetA addr : Addr <- liftAction child0Path (Recv "addr" pTargetPortLineReadRq (fun addr => Return #addr)) ;
        Act (implInternalMemRegionLineReadRq r true hasExtraFetchPort false true addr) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  Definition implInternalMemRegionTargetPortReadRp : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rpOpt : Option (LineReadRp true r.(regionLineCfg)) <- @implInternalMemRegionLineReadRp r true hasExtraFetchPort ty false true ;
    If (##rpOpt`"valid") Then (
      Recv "rpReady" pTargetPortLineReadRpReady (fun rpReady =>
      If #rpReady Then (
        Let rp : LineReadRp true r.(regionLineCfg) <- ##rpOpt`"data" ;
        Act (@implInternalMemRegionLineDeqRp r true hasExtraFetchPort ty false) ;
        liftAction child0Path (Send pTargetPortLineReadRp #rp Retv)
      ) ;
      Retv)
    ) ;
    Retv.

  Definition implInternalMemRegionTargetPortWrite : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rdy : Bool <- @implInternalMemRegionLineWriteRdy r true hasExtraFetchPort ty ;
    Act (Send pTargetPortLineWriteRqReady #rdy Retv) ;
    If #rdy Then (
      LetA valid : Bool <- liftAction child0Path (Recv "valid" pTargetPortLineWriteRqValid (fun valid => Return #valid)) ;
      If #valid Then (
        LetA rq : LineWriteRq true r.(regionLineCfg) <- liftAction child0Path (Recv "rq" pTargetPortLineWriteRq (fun rq => Return #rq)) ;
        Act (implInternalMemRegionLineWriteRq r true hasExtraFetchPort rq) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End ImplInternalMemTargetPortActions.

Arguments implInternalMemRegionTargetPortReadRq r hasExtraFetchPort {ty}.
Arguments implInternalMemRegionTargetPortReadRp r hasExtraFetchPort {ty}.
Arguments implInternalMemRegionTargetPortWrite r hasExtraFetchPort {ty}.

(* ===========================================================================
 * Split-Phase Implementation Actions for ExternalMem
 * =========================================================================== *)

Section ImplExternalMemRegionActions.
  Variable r : MemRegion.
  Variable hasExtraFetchPort : bool.
  Variable ty : Kind -> Type.

  Local Definition tExtSpec := externalMemRegionTree r hasExtraFetchPort.
  Local Definition tImplExt := implExternalMemRegionTree r hasExtraFetchPort.

  Local Definition pLineWriteRqReady         : RecvPath tImplExt                          := Eval cbn in (getChildRecvPathTree tImplExt "lineWriteRqReady").
  Local Definition pState                    : RegPath  tImplExt                          := Eval cbn in (getChildRegPathTree tImplExt "state").
  Local Definition pLineReadRqReadyTrue      : RecvPath (implExternalMemRegionTree r true)  := Eval cbn in (getChildRecvPathTree (implExternalMemRegionTree r true) "lineReadRqReady").
  Local Definition pFetchLineReadRqReadyTrue : RecvPath (implExternalMemRegionTree r true)  := Eval cbn in (getChildRecvPathTree (implExternalMemRegionTree r true) "fetchLineReadRqReady").
  Local Definition pLineReadRqReadyFalse     : RecvPath (implExternalMemRegionTree r false) := Eval cbn in (getChildRecvPathTree (implExternalMemRegionTree r false) "lineReadRqReady").
  Local Definition pLineReadRpValidTrue      : RecvPath (implExternalMemRegionTree r true)  := Eval cbn in (getChildRecvPathTree (implExternalMemRegionTree r true) "lineReadRpValid").
  Local Definition pFetchLineReadRpValidTrue : RecvPath (implExternalMemRegionTree r true)  := Eval cbn in (getChildRecvPathTree (implExternalMemRegionTree r true) "fetchLineReadRpValid").
  Local Definition pLineReadRpValidFalse     : RecvPath (implExternalMemRegionTree r false) := Eval cbn in (getChildRecvPathTree (implExternalMemRegionTree r false) "lineReadRpValid").
  Local Definition pLineReadRpReadyTrue      : SendPath (implExternalMemRegionTree r true)  := Eval cbn in (getChildSendPathTree (implExternalMemRegionTree r true) "lineReadRpReady").
  Local Definition pFetchLineReadRpReadyTrue : SendPath (implExternalMemRegionTree r true)  := Eval cbn in (getChildSendPathTree (implExternalMemRegionTree r true) "fetchLineReadRpReady").
  Local Definition pLineReadRpReadyFalse     : SendPath (implExternalMemRegionTree r false) := Eval cbn in (getChildSendPathTree (implExternalMemRegionTree r false) "lineReadRpReady").
  Local Definition pStateTrue                : RegPath  (implExternalMemRegionTree r true)  := Eval cbn in (getChildRegPathTree (implExternalMemRegionTree r true) "state").
  Local Definition pFetchStateTrue           : RegPath  (implExternalMemRegionTree r true)  := Eval cbn in (getChildRegPathTree (implExternalMemRegionTree r true) "fetchState").
  Local Definition pStateFalse               : RegPath  (implExternalMemRegionTree r false) := Eval cbn in (getChildRegPathTree (implExternalMemRegionTree r false) "state").
  Local Definition pNextLineAddrTrue         : RegPath  (implExternalMemRegionTree r true)  := Eval cbn in (getChildRegPathTree (implExternalMemRegionTree r true) "nextLineAddr").
  Local Definition pFetchNextLineAddrTrue    : RegPath  (implExternalMemRegionTree r true)  := Eval cbn in (getChildRegPathTree (implExternalMemRegionTree r true) "fetchNextLineAddr").
  Local Definition pNextLineAddrFalse        : RegPath  (implExternalMemRegionTree r false) := Eval cbn in (getChildRegPathTree (implExternalMemRegionTree r false) "nextLineAddr").

  Local Definition recvLineReadRqReady {k : Kind} (isFetch : bool)
    (cont : ty Bool -> Action ty tImplExt k) : Action ty tImplExt k :=
    match hasExtraFetchPort as b
      return (ty Bool -> Action ty (implExternalMemRegionTree r b) k) ->
             Action ty (implExternalMemRegionTree r b) k with
    | true  => fun c => if isFetch then Recv "rdy" pFetchLineReadRqReadyTrue c else Recv "rdy" pLineReadRqReadyTrue c
    | false => fun c => Recv "rdy" pLineReadRqReadyFalse c
    end cont.

  Local Definition recvLineReadRpValid {k : Kind} (isFetch : bool)
    (cont : ty Bool -> Action ty tImplExt k) : Action ty tImplExt k :=
    match hasExtraFetchPort as b
      return (ty Bool -> Action ty (implExternalMemRegionTree r b) k) ->
             Action ty (implExternalMemRegionTree r b) k with
    | true  => fun c => if isFetch then Recv "rpValid" pFetchLineReadRpValidTrue c else Recv "rpValid" pLineReadRpValidTrue c
    | false => fun c => Recv "rpValid" pLineReadRpValidFalse c
    end cont.

  Local Definition readExtState {k : Kind} (isFetch : bool)
    (cont : ty (ExtRegionState r.(regionLineCfg)) -> Action ty tImplExt k) : Action ty tImplExt k :=
    match hasExtraFetchPort as b
      return (ty (ExtRegionState r.(regionLineCfg)) -> Action ty (implExternalMemRegionTree r b) k) ->
             Action ty (implExternalMemRegionTree r b) k with
    | true  => fun c => if isFetch then ReadReg "state" pFetchStateTrue c else ReadReg "state" pStateTrue c
    | false => fun c => ReadReg "state" pStateFalse c
    end cont.

  Local Definition writeExtState {k : Kind} (isFetch : bool)
    (v : Expr ty (ExtRegionState r.(regionLineCfg))) (cont : Action ty tImplExt k) : Action ty tImplExt k :=
    match hasExtraFetchPort as b
      return Action ty (implExternalMemRegionTree r b) k ->
             Action ty (implExternalMemRegionTree r b) k with
    | true  => fun c => if isFetch then WriteReg pFetchStateTrue v c else WriteReg pStateTrue v c
    | false => fun c => WriteReg pStateFalse v c
    end cont.

  Local Definition readExtNextLineAddr {k : Kind} (isFetch : bool)
    (cont : ty (Option Addr) -> Action ty tImplExt k) : Action ty tImplExt k :=
    match hasExtraFetchPort as b
      return (ty (Option Addr) -> Action ty (implExternalMemRegionTree r b) k) ->
             Action ty (implExternalMemRegionTree r b) k with
    | true  => fun c => if isFetch then ReadReg "nextLineAddr" pFetchNextLineAddrTrue c else ReadReg "nextLineAddr" pNextLineAddrTrue c
    | false => fun c => ReadReg "nextLineAddr" pNextLineAddrFalse c
    end cont.

  Local Definition writeExtNextLineAddr {k : Kind} (isFetch : bool)
    (v : Expr ty (Option Addr)) (cont : Action ty tImplExt k) : Action ty tImplExt k :=
    match hasExtraFetchPort as b
      return Action ty (implExternalMemRegionTree r b) k ->
             Action ty (implExternalMemRegionTree r b) k with
    | true  => fun c => if isFetch then WriteReg pFetchNextLineAddrTrue v c else WriteReg pNextLineAddrTrue v c
    | false => fun c => WriteReg pNextLineAddrFalse v c
    end cont.

  Definition implExternalMemRegionLineReadRq (isFetch : bool) (addr : ty Addr)
             : Action ty tImplExt Bool :=
    recvLineReadRqReady isFetch (fun rdy =>
    If #rdy Then (
      liftAction child0Path (externalMemRegionIssueReadRq r hasExtraFetchPort isFetch addr)
    ) ;
    Return #rdy).

  Definition implExternalMemRegionLineReadRp (isFetch : bool)
             : Action ty tImplExt (Option (LineReadRp false r.(regionLineCfg))) :=
    recvLineReadRpValid isFetch (fun rpValid =>
    LetIf rpOpt : Option (LineReadRp false r.(regionLineCfg)) <-
      If #rpValid Then (
        LetA rp : LineReadRp false r.(regionLineCfg) <-
          liftAction child0Path (@externalMemRegionGetReadRp r hasExtraFetchPort ty isFetch) ;
        Return (mkSome #rp)
      ) ;
    Return #rpOpt).

  Definition implExternalMemRegionLineDeqRp (isFetch : bool)
             : Action ty tImplExt (Bit 0) :=
    match hasExtraFetchPort as b return Action ty (implExternalMemRegionTree r b) (Bit 0) with
    | true  => if isFetch then Send pFetchLineReadRpReadyTrue ($0 : Expr ty (Bit 0)) Retv else Send pLineReadRpReadyTrue ($0 : Expr ty (Bit 0)) Retv
    | false => Send pLineReadRpReadyFalse ($0 : Expr ty (Bit 0)) Retv
    end.

  Definition implExternalMemRegionLineWriteRq
             (rq : ty (LineWriteRq false r.(regionLineCfg)))
             : Action ty tImplExt Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      Recv "rdy" pLineWriteRqReady (fun rdy =>
      If #rdy Then (
        liftAction child0Path (externalMemRegionLineWrite r hasExtraFetchPort rq)
      ) ;
      Return #rdy)
    ).

  Definition implExternalMemRegionReadRq
             (isFetch : bool)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt Bool :=
    readExtState isFetch (fun state =>
    LetIf rdy : Bool <-
      If (##state `? "Idle") Then (
        Let  addr0 : Addr <- memLineAddr r #addr ;
        LetA rdy0  : Bool <- implExternalMemRegionLineReadRq isFetch addr0 ;
        If #rdy0 Then (
          Act (writeExtState isFetch (UNION (ExtRegionStateList r.(regionLineCfg), "ReadWait" ::= ($0 : Expr ty (Bit 0)))) Retv) ;
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
      LetA rp0Opt : Option (LineReadRp false r.(regionLineCfg)) <- implExternalMemRegionLineReadRp isFetch ;
      If (##rp0Opt`"valid") Then (
        Let rp0 : LineReadRp false r.(regionLineCfg) <- ##rp0Opt`"data" ;
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
             (isFetch : bool)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt (Option FullCapWithTag) :=
    readExtState isFetch (fun state =>
    readExtNextLineAddr isFetch (fun nextLineAddr =>
    LetIf resOpt : Option FullCapWithTag <-
      If (And [ Or [ ##state `? "ReadWait" ; ##state `? "ReadRp0" ] ;
                Not (##nextLineAddr`"valid") ]) Then (
        LetA lastRpOpt : Option (LineReadRp false r.(regionLineCfg)) <- implExternalMemRegionLineReadRp isFetch ;
        LetIf rOpt : Option FullCapWithTag <-
          If (##lastRpOpt`"valid") Then (
            Let lastRp : LineReadRp false r.(regionLineCfg) <- ##lastRpOpt`"data" ;
            Let rp0    : LineReadRp false r.(regionLineCfg) <-
              ITE (##state `? "ReadRp0") (##state `! "ReadRp0") #lastRp ;
            Let rp1    : LineReadRp false r.(regionLineCfg) <-
              ITE (##state `? "ReadRp0") #lastRp ConstDef ;
            Let rp     : LineReadRp false r.(regionLineCfg) <- memMergeLineReadRp false r #addr #rp0 #rp1 ;
            Let res    : FullCapWithTag                     <- memExtractReadCap false r #addr #memSize #rp ;
            Return (mkSome #res)
          ) ;
        Return #rOpt
      ) ;
    Return #resOpt)).

  Definition implExternalMemRegionDeqRp (isFetch : bool) : Action ty tImplExt (Bit 0) :=
    Act (implExternalMemRegionLineDeqRp isFetch) ;
    writeExtState isFetch (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

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
          Let  rq   : LineWriteRq false r.(regionLineCfg) <- memBuildLineWriteRq false r #addr #stVal #memSize ;
          Let  rq0  : LineWriteRq false r.(regionLineCfg) <- memLineWriteRq0 false r #rq #memSize ;
          LetA rdy0 : Bool                                <- implExternalMemRegionLineWriteRq rq0 ;
          If #rdy0 Then (
            Let crosses : Bool <- memCrossesLine r #addr #memSize ;
            If #crosses Then (
              Let rq1 : LineWriteRq false r.(regionLineCfg) <- memLineWriteRq1 false r #rq #memSize ;
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
        Let  rq1  : LineWriteRq false r.(regionLineCfg) <- ##state `! "WriteRq1" ;
        LetA rdy1 : Bool                                <- implExternalMemRegionLineWriteRq rq1 ;
        If #rdy1 Then (
          WriteReg pState (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
        ) ;
        Retv
      ) ;
      Retv)
    ).

End ImplExternalMemRegionActions.

Arguments implExternalMemRegionLineReadRq r hasExtraFetchPort [ty] isFetch addr.
Arguments implExternalMemRegionLineReadRp r hasExtraFetchPort {ty} isFetch.
Arguments implExternalMemRegionLineDeqRp r hasExtraFetchPort {ty} isFetch.
Arguments implExternalMemRegionLineWriteRq r hasExtraFetchPort [ty] rq.
Arguments implExternalMemRegionReadRq r hasExtraFetchPort [ty] isFetch addr memSize.
Arguments implExternalMemRegionReadRp0 r hasExtraFetchPort {ty} isFetch.
Arguments implExternalMemRegionReadRq1 r hasExtraFetchPort {ty} isFetch.
Arguments implExternalMemRegionReadRp r hasExtraFetchPort [ty] isFetch addr memSize.
Arguments implExternalMemRegionDeqRp r hasExtraFetchPort {ty} isFetch.
Arguments implExternalMemRegionWriteRq r hasExtraFetchPort [ty] addr stVal memSize.
Arguments implExternalMemRegionWriteStep r hasExtraFetchPort {ty}.

(* ===========================================================================
 * Split-Phase Implementation Actions for CustomMem
 * =========================================================================== *)

Section ImplCustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree DomainElem).
  Variable hasExtraFetchPort : bool.
  Variable readAction : forall ty, ReadPortSel hasExtraFetchPort -> ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp false r.(regionLineCfg)).
  Variable writeAction : forall ty, ty (LineWriteRq false r.(regionLineCfg)) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tImplCust := implCustomMemRegionTree r children hasExtraFetchPort.
  Local Definition pCustState          : RegPath tImplCust := Eval cbn in (getChildRegPathTree tImplCust "state").
  Local Definition pCustStateTrue      : RegPath (implCustomMemRegionTree r children true)  := Eval cbn in (getChildRegPathTree (implCustomMemRegionTree r children true) "state").
  Local Definition pCustFetchStateTrue : RegPath (implCustomMemRegionTree r children true)  := Eval cbn in (getChildRegPathTree (implCustomMemRegionTree r children true) "fetchState").
  Local Definition pCustStateFalse     : RegPath (implCustomMemRegionTree r children false) := Eval cbn in (getChildRegPathTree (implCustomMemRegionTree r children false) "state").

  Local Definition readCustState {k : Kind} (isFetch : bool)
    (cont : ty (CustomRegionState r.(regionLineCfg)) -> Action ty tImplCust k) : Action ty tImplCust k :=
    match hasExtraFetchPort as b
      return (ty (CustomRegionState r.(regionLineCfg)) -> Action ty (implCustomMemRegionTree r children b) k) ->
             Action ty (implCustomMemRegionTree r children b) k with
    | true  => fun c => if isFetch then ReadReg "state" pCustFetchStateTrue c else ReadReg "state" pCustStateTrue c
    | false => fun c => ReadReg "state" pCustStateFalse c
    end cont.

  Local Definition writeCustState {k : Kind} (isFetch : bool)
    (v : Expr ty (CustomRegionState r.(regionLineCfg))) (cont : Action ty tImplCust k) : Action ty tImplCust k :=
    match hasExtraFetchPort as b
      return Action ty (implCustomMemRegionTree r children b) k ->
             Action ty (implCustomMemRegionTree r children b) k with
    | true  => fun c => if isFetch then WriteReg pCustFetchStateTrue v c else WriteReg pCustStateTrue v c
    | false => fun c => WriteReg pCustStateFalse v c
    end cont.

  Definition implCustomMemRegionReadRq (isFetch : bool) (addr : ty Addr)
             : Action ty tImplCust Bool :=
    readCustState isFetch (fun state =>
    Let isIdle : Bool <- ##state `? "Idle" ;
    If #isIdle Then (
      Let  addr0 : Addr                               <- memLineAddr r #addr ;
      LetA rp0   : LineReadRp false r.(regionLineCfg) <- liftAction child0Path (customMemRegionLineRead r children hasExtraFetchPort readAction isFetch addr0) ;
      writeCustState isFetch (UNION (CustomRegionStateList r.(regionLineCfg), "ReadRp0" ::= #rp0)) Retv
    ) ;
    Return #isIdle).

  Definition implCustomMemRegionReadRp
             (isFetch : bool)
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplCust (Option FullCapWithTag) :=
    readCustState isFetch (fun state =>
    LetIf resOpt : Option FullCapWithTag <-
      If (##state `? "ReadRp0") Then (
        Let  rp0     : LineReadRp false r.(regionLineCfg) <- ##state `! "ReadRp0" ;
        Let  crosses : Bool                               <- memCrossesLine r #addr #memSize ;
        LetIf rp1 : LineReadRp false r.(regionLineCfg) <-
          If #crosses Then (
            Let addr1 : Addr <- memNextLineAddr r #addr ;
            liftAction child0Path (customMemRegionLineRead r children hasExtraFetchPort readAction isFetch addr1)
          ) Else (
            Return ConstDef
          ) ;
        Let  rp      : LineReadRp false r.(regionLineCfg) <- memMergeLineReadRp false r #addr #rp0 #rp1 ;
        Let  res     : FullCapWithTag                     <- memExtractReadCap false r #addr #memSize #rp ;
        Return (mkSome #res)
      ) ;
    Return #resOpt).

  Definition implCustomMemRegionDeqRp (isFetch : bool) : Action ty tImplCust (Bit 0) :=
    writeCustState isFetch (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

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
        Let rq      : LineWriteRq false r.(regionLineCfg) <- memBuildLineWriteRq false r #addr #stVal #memSize ;
        Let rq0     : LineWriteRq false r.(regionLineCfg) <- memLineWriteRq0 false r #rq #memSize ;
        Act (liftAction child0Path (customMemRegionLineWrite r children writeAction rq0)) ;
        Let crosses : Bool                                <- memCrossesLine r #addr #memSize ;
        If #crosses Then (
          Let rq1 : LineWriteRq false r.(regionLineCfg) <- memLineWriteRq1 false r #rq #memSize ;
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
        Let rq1 : LineWriteRq false r.(regionLineCfg) <- ##state `! "WriteRq1" ;
        Act (liftAction child0Path (customMemRegionLineWrite r children writeAction rq1)) ;
        WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
      ) ;
      Retv)
    ).

End ImplCustomMemRegionActions.

Arguments implCustomMemRegionReadRq r children hasExtraFetchPort readAction [ty] isFetch addr.
Arguments implCustomMemRegionReadRp r children hasExtraFetchPort readAction [ty] isFetch addr memSize.
Arguments implCustomMemRegionDeqRp r children hasExtraFetchPort {ty} isFetch.
Arguments implCustomMemRegionWriteRq r children hasExtraFetchPort writeAction [ty] addr stVal memSize.
Arguments implCustomMemRegionWriteStep r children hasExtraFetchPort writeAction {ty}.

(* ===========================================================================
 * Unified Per-Region Implementation Dispatch
 * =========================================================================== *)

Definition implMemRegionReadRq
           {ty : Kind -> Type}
           (r : MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implMemRegionTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                              | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                              end) Bool with
  | InternalMem isAccessible _ _ => implInternalMemRegionLineReadRq r isAccessible r.(hasExtraFetchPort) isFetch false addr
  | ExternalMem => implExternalMemRegionReadRq r r.(hasExtraFetchPort) isFetch addr memSize
  | CustomMem children readAct _ _ => implCustomMemRegionReadRq r children r.(hasExtraFetchPort) readAct isFetch addr
  end.

Definition implMemRegionReadRp
           {ty : Kind -> Type}
           (r : MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implMemRegionTree r) (Option FullCapWithTag) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                              | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                              end) (Option FullCapWithTag) with
  | InternalMem isAccessible _ _ => implInternalMemRegionReadRp r isAccessible r.(hasExtraFetchPort) isFetch addr memSize
  | ExternalMem => implExternalMemRegionReadRp r r.(hasExtraFetchPort) isFetch addr memSize
  | CustomMem children readAct _ _ => implCustomMemRegionReadRp r children r.(hasExtraFetchPort) readAct isFetch addr memSize
  end.

Definition implMemRegionDeqRp
           {ty : Kind -> Type}
           (r : MemRegion)
           (isFetch : bool)
           : Action ty (implMemRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                              | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                              end) (Bit 0) with
  | InternalMem isAccessible _ _ => @implInternalMemRegionLineDeqRp r isAccessible r.(hasExtraFetchPort) ty isFetch
  | ExternalMem => @implExternalMemRegionDeqRp r r.(hasExtraFetchPort) ty isFetch
  | CustomMem children _ _ _ => @implCustomMemRegionDeqRp r children r.(hasExtraFetchPort) ty isFetch
  end.

Definition implMemRegionWriteRq
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : ty Addr)
           (stVal : ty FullCapWithTag)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implMemRegionTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                              | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                              end) Bool with
  | InternalMem isAccessible _ _ => implInternalMemRegionWriteRq r isAccessible r.(hasExtraFetchPort) addr stVal memSize
  | ExternalMem => implExternalMemRegionWriteRq r r.(hasExtraFetchPort) addr stVal memSize
  | CustomMem children _ writeAct _ => implCustomMemRegionWriteRq r children r.(hasExtraFetchPort) writeAct addr stVal memSize
  end.

Arguments implMemRegionReadRq [ty] r isFetch addr memSize.
Arguments implMemRegionReadRp [ty] r isFetch addr memSize.
Arguments implMemRegionDeqRp {ty} r isFetch.
Arguments implMemRegionWriteRq [ty] r addr stVal memSize.

Definition implMemRegionStepActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                                                         | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                                                         end) (Bit 0))) with
  | InternalMem _ _ _ => []
  | ExternalMem =>
      ([ (r.(regionDom), fun ty => (Act (@implExternalMemRegionReadRp0 r r.(hasExtraFetchPort) ty false) ; @implExternalMemRegionReadRq1 r r.(hasExtraFetchPort) ty false)) ] ++
       (if r.(hasExtraFetchPort) then
          [ (r.(regionDom), fun ty => (Act (@implExternalMemRegionReadRp0 r r.(hasExtraFetchPort) ty true) ; @implExternalMemRegionReadRq1 r r.(hasExtraFetchPort) ty true)) ]
        else []) ++
       [ (r.(regionDom), fun ty => @implExternalMemRegionWriteStep r r.(hasExtraFetchPort) ty) ])%list
  | CustomMem children _ writeAct _ =>
      [ (r.(regionDom), fun ty => @implCustomMemRegionWriteStep r children r.(hasExtraFetchPort) writeAct ty) ]
  end.

Definition implMemRegionTargetPortActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                                                         | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                                                         end) (Bit 0))) with
  | InternalMem true _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionTargetPortWrite r r.(hasExtraFetchPort) ty) ;
        (r.(regionDom), fun ty => @implInternalMemRegionTargetPortReadRq r r.(hasExtraFetchPort) ty) ;
        (r.(regionDom), fun ty => @implInternalMemRegionTargetPortReadRp r r.(hasExtraFetchPort) ty) ]
  | _ => []
  end.

Definition implMemRegionClearWriteBusyActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible r.(hasExtraFetchPort)
                                                                         | ExternalMem => implExternalMemRegionTree r r.(hasExtraFetchPort)
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children r.(hasExtraFetchPort)
                                                                         end) (Bit 0))) with
  | InternalMem isAccessible _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionClearWriteBusy r isAccessible r.(hasExtraFetchPort) ty) ]
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

  Fixpoint implCollectTargetPortActions
           (regions : list MemRegion)
           : list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) :=
    match regions return list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) with
    | [] => []
    | r :: rs =>
        let curr := map (fun '(dom, act) => (dom, fun ty => liftAction child0Path (act ty)))
                        (implMemRegionTargetPortActions r) in
        let rest := map (fun '(dom, act) => (dom, fun ty => liftAction child1Path (act ty)))
                        (implCollectTargetPortActions rs) in
        (curr ++ rest)%list
    end.

  Fixpoint implCollectClearWriteBusyActions
           (regions : list MemRegion)
           : list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) :=
    match regions return list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) with
    | [] => []
    | r :: rs =>
        let curr := map (fun '(dom, act) => (dom, fun ty => liftAction child0Path (act ty)))
                        (implMemRegionClearWriteBusyActions r) in
        let rest := map (fun '(dom, act) => (dom, fun ty => liftAction child1Path (act ty)))
                        (implCollectClearWriteBusyActions rs) in
        (curr ++ rest)%list
    end.

  Fixpoint implCollectRegionStepActions
           (regions : list MemRegion)
           : list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) :=
    match regions return list (string * (forall ty, Action ty (implRegionsTree regions) (Bit 0))) with
    | [] => []
    | r :: rs =>
        let curr := map (fun '(dom, act) => (dom, fun ty => liftAction child0Path (act ty)))
                        (implMemRegionStepActions r) in
        let rest := map (fun '(dom, act) => (dom, fun ty => liftAction child1Path (act ty)))
                        (implCollectRegionStepActions rs) in
        (curr ++ rest)%list
    end.
End ImplCollectors.

Section ImplRegionsRouter.
  Variable ty : Kind -> Type.

  Fixpoint implRegionsReadRq
           (regions : list MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) Bool :=
    match regions return Action ty (implRegionsTree regions) Bool with
    | [] => Return (ConstBool true)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf devRdy : Bool <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRq r isFetch addr memSize)
          ) Else (
            Return (ConstBool true)
          ) ;
        LetA restRdy : Bool <-
          liftAction child1Path (implRegionsReadRq rs isFetch addr memSize) ;
        Return (And [ #devRdy ; #restRdy ])
    end.

  Fixpoint implRegionsReadRp
           (regions : list MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) (Option FullCapWithTag) :=
    match regions return Action ty (implRegionsTree regions) (Option FullCapWithTag) with
    | [] => Return (mkSome ConstDef)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf devRp : Option FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRp r isFetch addr memSize)
          ) Else (
            Return (mkSome ConstDef)
          ) ;
        LetA restRp : Option FullCapWithTag <-
          liftAction child1Path (implRegionsReadRp rs isFetch addr memSize) ;
        @Return ty _ (Option FullCapWithTag) (STRUCT {
          "data"  ::= Or [ ##devRp`"data" ; ##restRp`"data" ] ;
          "valid" ::= And [ ##devRp`"valid" ; ##restRp`"valid" ]
        })
    end.

  Fixpoint implRegionsDeqRp
           (regions : list MemRegion)
           (isFetch : bool)
           (addr : ty Addr)
           : Action ty (implRegionsTree regions) (Bit 0) :=
    match regions return Action ty (implRegionsTree regions) (Bit 0) with
    | [] => Retv
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        If #isMatch Then (
          liftAction child0Path (@implMemRegionDeqRp ty r isFetch)
        ) ;
        liftAction child1Path (implRegionsDeqRp rs isFetch addr)
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

    Definition implMemCollectTargetPortActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectTargetPortActions regions).

    Definition implMemCollectClearWriteBusyActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectClearWriteBusyActions regions).

    Definition implMemCollectRegionStepActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectRegionStepActions regions).

    (* 1. Instruction Memory Channel *)
    Definition implReadInstRq (addr : ty Addr) : Action ty implMemTree Bool :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      implRegionsReadRq regions true addr instSz.

    Definition implGetInstRp (addr : ty Addr) : Action ty implMemTree (Option Inst) :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      LetA rpOpt : Option FullCapWithTag <- implRegionsReadRp regions true addr instSz ;
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
      implRegionsDeqRp regions true addr.

    (* 2. Data Load Channel *)
    Definition implReadMemRq (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
      implRegionsReadRq regions false addr memSize.

    Definition implGetMemRp (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree (Option FullCapWithTag) :=
      implRegionsReadRp regions false addr memSize.

    Definition implDeqMemRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
      implRegionsDeqRp regions false addr.

    (* 3. Revocation Bit Memory Channel *)
    Definition implReadRevBitRq (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
      LetL lookup      : RevBitLookup              <- computeRevBitAddr revConfig base ;
      Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
      Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
      implRegionsReadRq regions false revByteAddr sz0.

    Definition implGetDeqRevBitRp (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
      LetL lookup      : RevBitLookup              <- computeRevBitAddr revConfig base ;
      Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
      Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
      LetA rpOpt       : Option FullCapWithTag     <- implRegionsReadRp regions false revByteAddr sz0 ;
      LetIf rOpt : Option Bool <-
        If (##rpOpt`"valid") Then (
          Act (implRegionsDeqRp regions false revByteAddr) ;
          Let revCap  : FullCapWithTag <- ##rpOpt`"data" ;
          Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
          Let revBit  : Bool           <- extractRevBit lookup #revByte ;
          Return (mkSome #revBit)
        ) Else (
          Return ConstDef
        ) ;
      Return #rOpt.

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
    Definition implRevokerSteps (rev : @RevokerInstance dom (implRevokerExtraChildren dom) regions) : list (Action ty implMemTree (Bit 0)) :=
      @implRevokerStepsFsm
        dom
        ty
        revConfig
        implMemTree
        (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom (implRevokerExtraChildren dom) regions rev) rev.(pfRevoker) a)
        implReadMemRq
        implGetMemRp
        implDeqMemRp
        implReadRevBitRq
        implGetDeqRevBitRp
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
