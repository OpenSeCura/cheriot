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
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines SpecDevice FunctionalUnits SpecRevoker ImplRevoker.

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
    ("ReadRp0",  LineReadRp cfg) ;
    ("WriteRq1", LineWriteRq cfg) ].

Definition ExtRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (ExtRegionStateList cfg).

Definition CustomRegionStateList (cfg : LineConfig) : list (string * Kind) :=
  [ ("Idle",     Bit 0) ;
    ("ReadRp0",  LineReadRp cfg) ;
    ("WriteRq1", LineWriteRq cfg) ].

Definition CustomRegionState (cfg : LineConfig) : Kind :=
  TaggedUnion (CustomRegionStateList cfg).

Definition implInternalMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "rpValid" (r.(regionDom), EReg (Build_Reg Bool (Some false) false)) ].

Definition implExternalMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "lineReadRqReady"  (r.(regionDom), ERecv Bool) ;
    Leaf "lineWriteRqReady" (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRpValid"  (r.(regionDom), ERecv Bool) ;
    Leaf "lineReadRpReady"  (r.(regionDom), ESend (Bit 0)) ;
    Leaf "state"            (r.(regionDom), EReg (Build_Reg (ExtRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ;
    Leaf "nextLineAddr"     (r.(regionDom), EReg (Build_Reg (Option Addr) (Some (getDefault _)) false))
  ].

Definition implCustomMemRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "state" (r.(regionDom), EReg (Build_Reg (CustomRegionState r.(regionLineCfg)) (Some (getDefault _)) false)) ].

Definition implInternalMemRegionTree (r : MemRegion) (isAccessible : bool) : Tree DomainElem :=
  Node r.(regionName) (internalMemRegionTree r isAccessible :: implInternalMemRegionExtraChildren r).

Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
  Node r.(regionName) (externalMemRegionTree r :: implExternalMemRegionExtraChildren r).

Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
  Node r.(regionName) (customMemRegionTree r children :: implCustomMemRegionExtraChildren r).

Arguments implInternalMemRegionTree r isAccessible : clear implicits.
Arguments implExternalMemRegionTree r : clear implicits.
Arguments implCustomMemRegionTree r children : clear implicits.

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

  Local Definition tImplInt := implInternalMemRegionTree r isAccessible.
  Local Definition pRpValid : RegPath tImplInt := Eval cbn in (getChildRegPathTree tImplInt "rpValid").

  Definition implInternalMemRegionLineReadRq (addr : ty Addr)
             : Action ty tImplInt Bool :=
    ReadReg "rpValid" pRpValid (fun rpValid =>
    If (Not #rpValid) Then (
      Act (liftAction child0Path (internalMemRegionIssueReadRq r isAccessible addr)) ;
      WriteReg pRpValid (ConstBool true) Retv
    ) ;
    Return (Not #rpValid)).

  Definition implInternalMemRegionLineReadRp
             : Action ty tImplInt (Option (LineReadRp r.(regionLineCfg))) :=
    ReadReg "rpValid" pRpValid (fun rpValid =>
    LetIf rpOpt : Option (LineReadRp r.(regionLineCfg)) <-
      If #rpValid Then (
        LetA rp : LineReadRp r.(regionLineCfg) <-
          liftAction child0Path (@internalMemRegionGetReadRp r isAccessible ty) ;
        Return (mkSome #rp)
      ) ;
    Return #rpOpt).

  Definition implInternalMemRegionLineDeqRp
             : Action ty tImplInt (Bit 0) :=
    WriteReg pRpValid (ConstBool false) Retv.

  Definition implInternalMemRegionLineWriteRq
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tImplInt Bool :=
    Act (liftAction child0Path (internalMemRegionLineWrite r isAccessible rq)) ;
    Return (ConstBool true).

  Definition implInternalMemRegionReadRp
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplInt (Option FullCapWithTag) :=
    LetA rpOpt : Option (LineReadRp r.(regionLineCfg)) <- implInternalMemRegionLineReadRp ;
    LetIf resOpt : Option FullCapWithTag <-
      If (##rpOpt `? "Some") Then (
        Let rp : LineReadRp r.(regionLineCfg) <- ##rpOpt `! "Some" ;
        Return (mkSome (memExtractReadCap r #addr #memSize #rp))
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
      Let rq : LineWriteRq r.(regionLineCfg) <- memBuildLineWriteRq r #addr #stVal #memSize ;
      implInternalMemRegionLineWriteRq rq
    ).

End ImplInternalMemRegionActions.

Arguments implInternalMemRegionLineReadRq r isAccessible [ty] addr.
Arguments implInternalMemRegionLineReadRp r isAccessible {ty}.
Arguments implInternalMemRegionLineDeqRp r isAccessible {ty}.
Arguments implInternalMemRegionLineWriteRq r isAccessible [ty] rq.
Arguments implInternalMemRegionReadRp r isAccessible [ty] addr memSize.
Arguments implInternalMemRegionWriteRq r isAccessible [ty] addr stVal memSize.

Section ImplInternalMemTargetPortActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tIntSpec := internalMemRegionTree r true.
  Local Definition tImplIntTargetPort := implInternalMemRegionTree r true.
  Local Definition pTargetPortLineReadRq : RecvPath tIntSpec := Eval cbn in (getChildRecvPathTree tIntSpec "lineReadRq").
  Local Definition pTargetPortLineReadRp : SendPath tIntSpec := Eval cbn in (getChildSendPathTree tIntSpec "lineReadRp").

  Definition implInternalMemRegionTargetPortReadRq : Action ty tImplIntTargetPort (Bit 0) :=
    LetA addr : Addr <- liftAction child0Path (Recv "addr" pTargetPortLineReadRq (fun addr => Return #addr)) ;
    Act (implInternalMemRegionLineReadRq r true addr) ;
    Retv.

  Definition implInternalMemRegionTargetPortReadRp : Action ty tImplIntTargetPort (Bit 0) :=
    LetA rpOpt : Option (LineReadRp r.(regionLineCfg)) <- @implInternalMemRegionLineReadRp r true ty ;
    If (##rpOpt `? "Some") Then (
      Let rp : LineReadRp r.(regionLineCfg) <- ##rpOpt `! "Some" ;
      Act (@implInternalMemRegionLineDeqRp r true ty) ;
      liftAction child0Path (Send pTargetPortLineReadRp #rp Retv)
    ) ;
    Retv.

  Definition implInternalMemRegionTargetPortWrite : Action ty tImplIntTargetPort (Bit 0) :=
    liftAction child0Path (@internalMemRegionTargetPortWrite r ty).

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

  Local Definition tExtSpec := externalMemRegionTree r.
  Local Definition tImplExt := implExternalMemRegionTree r.

  Local Definition pExtSpecLineReadRq : SendPath tExtSpec := Eval cbn in (getChildSendPathTree tExtSpec "lineReadRq").
  Local Definition pExtSpecLineReadRp : RecvPath tExtSpec := Eval cbn in (getChildRecvPathTree tExtSpec "lineReadRp").

  Local Definition pLineReadRqReady  : RecvPath tImplExt := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRqReady").
  Local Definition pLineWriteRqReady : RecvPath tImplExt := Eval cbn in (getChildRecvPathTree tImplExt "lineWriteRqReady").
  Local Definition pLineReadRpValid  : RecvPath tImplExt := Eval cbn in (getChildRecvPathTree tImplExt "lineReadRpValid").
  Local Definition pLineReadRpReady  : SendPath tImplExt := Eval cbn in (getChildSendPathTree tImplExt "lineReadRpReady").
  Local Definition pExtState         : RegPath  tImplExt := Eval cbn in (getChildRegPathTree  tImplExt "state").
  Local Definition pExtNextLineAddr  : RegPath  tImplExt := Eval cbn in (getChildRegPathTree  tImplExt "nextLineAddr").

  Definition implExternalMemRegionLineReadRq (addr : ty Addr)
             : Action ty tImplExt Bool :=
    Recv "rdy" pLineReadRqReady (fun rdy =>
    If #rdy Then (
      liftAction child0Path (Send pExtSpecLineReadRq #addr Retv)
    ) ;
    Return #rdy).

  Definition implExternalMemRegionLineReadRp
             : Action ty tImplExt (Option (LineReadRp r.(regionLineCfg))) :=
    Recv "rpValid" pLineReadRpValid (fun rpValid =>
    LetIf rpOpt : Option (LineReadRp r.(regionLineCfg)) <-
      If #rpValid Then (
        LetA rp : LineReadRp r.(regionLineCfg) <-
          liftAction child0Path (Recv "rp" pExtSpecLineReadRp (fun rp => Return #rp)) ;
        Return (mkSome #rp)
      ) ;
    Return #rpOpt).

  Definition implExternalMemRegionLineDeqRp
             : Action ty tImplExt (Bit 0) :=
    Send pLineReadRpReady ($0 : Expr ty (Bit 0)) Retv.

  Definition implExternalMemRegionLineWriteRq
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tImplExt Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      Recv "rdy" pLineWriteRqReady (fun rdy =>
      If #rdy Then (
        liftAction child0Path (externalMemRegionLineWrite r rq)
      ) ;
      Return #rdy)
    ).

  Definition implExternalMemRegionReadRq
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt Bool :=
    ReadReg "state" pExtState (fun state =>
    LetIf rdy : Bool <-
      If (##state `? "Idle") Then (
        Let  addr0 : Addr <- memLineAddr r #addr ;
        LetA rdy0  : Bool <- implExternalMemRegionLineReadRq addr0 ;
        If #rdy0 Then (
          Act (WriteReg pExtState (UNION (ExtRegionStateList r.(regionLineCfg), "ReadWait" ::= ($0 : Expr ty (Bit 0)))) Retv) ;
          Let crosses : Bool <- memCrossesLine r #addr #memSize ;
          If #crosses Then (
            Let addr1 : Addr <- memNextLineAddr r #addr ;
            WriteReg pExtNextLineAddr (mkSome #addr1) Retv
          ) ;
          Retv
        ) ;
        Return #rdy0
      ) ;
    Return #rdy).

  Definition implExternalMemRegionReadRp0 : Action ty tImplExt (Bit 0) :=
    ReadReg "state" pExtState (fun state =>
    ReadReg "nextLineAddr" pExtNextLineAddr (fun nextLineAddr =>
    If (And [ ##state `? "ReadWait" ; ##nextLineAddr `? "Some" ]) Then (
      LetA rp0Opt : Option (LineReadRp r.(regionLineCfg)) <- implExternalMemRegionLineReadRp ;
      If (##rp0Opt `? "Some") Then (
        Let rp0 : LineReadRp r.(regionLineCfg) <- ##rp0Opt `! "Some" ;
        Act implExternalMemRegionLineDeqRp ;
        WriteReg pExtState (UNION (ExtRegionStateList r.(regionLineCfg), "ReadRp0" ::= #rp0)) Retv
      ) ;
      Retv
    ) ;
    Retv)).

  Definition implExternalMemRegionReadRq1 : Action ty tImplExt (Bit 0) :=
    ReadReg "state" pExtState (fun state =>
    ReadReg "nextLineAddr" pExtNextLineAddr (fun nextLineAddr =>
    If (And [ ##state `? "ReadRp0" ; ##nextLineAddr `? "Some" ]) Then (
      Let  addr1 : Addr <- ##nextLineAddr `! "Some" ;
      LetA rdy1  : Bool <- implExternalMemRegionLineReadRq addr1 ;
      If #rdy1 Then (
        WriteReg pExtNextLineAddr ConstDef Retv
      ) ;
      Retv
    ) ;
    Retv)).

  Definition implExternalMemRegionReadRp
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt (Option FullCapWithTag) :=
    ReadReg "state" pExtState (fun state =>
    ReadReg "nextLineAddr" pExtNextLineAddr (fun nextLineAddr =>
    LetIf resOpt : Option FullCapWithTag <-
      If (And [ Or [ ##state `? "ReadWait" ; ##state `? "ReadRp0" ] ;
                Not (##nextLineAddr `? "Some") ]) Then (
        LetA lastRpOpt : Option (LineReadRp r.(regionLineCfg)) <- implExternalMemRegionLineReadRp ;
        LetIf rOpt : Option FullCapWithTag <-
          If (##lastRpOpt `? "Some") Then (
            Let lastRp : LineReadRp r.(regionLineCfg) <- ##lastRpOpt `! "Some" ;
            Let rp0    : LineReadRp r.(regionLineCfg) <-
              ITE (##state `? "ReadRp0") (##state `! "ReadRp0") #lastRp ;
            Let rp1    : LineReadRp r.(regionLineCfg) <-
              ITE (##state `? "ReadRp0") #lastRp ConstDef ;
            Let rp     : LineReadRp r.(regionLineCfg) <- memMergeLineReadRp r #addr #rp0 #rp1 ;
            Let res    : FullCapWithTag               <- memExtractReadCap r #addr #memSize #rp ;
            Return (mkSome #res)
          ) ;
        Return #rOpt
      ) ;
    Return #resOpt)).

  Definition implExternalMemRegionDeqRp : Action ty tImplExt (Bit 0) :=
    Act implExternalMemRegionLineDeqRp ;
    WriteReg pExtState (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

  Definition implExternalMemRegionWriteRq
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplExt Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      ReadReg "state" pExtState (fun state =>
      LetIf rdy : Bool <-
        If (##state `? "Idle") Then (
          Let  rq   : LineWriteRq r.(regionLineCfg) <- memBuildLineWriteRq r #addr #stVal #memSize ;
          Let  rq0  : LineWriteRq r.(regionLineCfg) <- memLineWriteRq0 r #rq ;
          LetA rdy0 : Bool                          <- implExternalMemRegionLineWriteRq rq0 ;
          If #rdy0 Then (
            Let crosses : Bool <- memCrossesLine r #addr #memSize ;
            If #crosses Then (
              Let rq1 : LineWriteRq r.(regionLineCfg) <- memLineWriteRq1 r #rq ;
              WriteReg pExtState (UNION (ExtRegionStateList r.(regionLineCfg), "WriteRq1" ::= #rq1)) Retv
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
      ReadReg "state" pExtState (fun state =>
      If (##state `? "WriteRq1") Then (
        Let  rq1  : LineWriteRq r.(regionLineCfg) <- ##state `! "WriteRq1" ;
        LetA rdy1 : Bool                          <- implExternalMemRegionLineWriteRq rq1 ;
        If #rdy1 Then (
          WriteReg pExtState (UNION (ExtRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
        ) ;
        Retv
      ) ;
      Retv)
    ).

End ImplExternalMemRegionActions.

Arguments implExternalMemRegionLineReadRq r [ty] addr.
Arguments implExternalMemRegionLineReadRp r {ty}.
Arguments implExternalMemRegionLineDeqRp r {ty}.
Arguments implExternalMemRegionLineWriteRq r [ty] rq.
Arguments implExternalMemRegionReadRq r [ty] addr memSize.
Arguments implExternalMemRegionReadRp0 r {ty}.
Arguments implExternalMemRegionReadRq1 r {ty}.
Arguments implExternalMemRegionReadRp r [ty] addr memSize.
Arguments implExternalMemRegionDeqRp r {ty}.
Arguments implExternalMemRegionWriteRq r [ty] addr stVal memSize.
Arguments implExternalMemRegionWriteStep r {ty}.

(* ===========================================================================
 * Split-Phase Implementation Actions for CustomMem
 * =========================================================================== *)

Section ImplCustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree DomainElem).
  Variable readAction : forall ty, ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp r.(regionLineCfg)).
  Variable writeAction : forall ty, ty (LineWriteRq r.(regionLineCfg)) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tImplCust := implCustomMemRegionTree r children.
  Local Definition pCustState : RegPath tImplCust := Eval cbn in (getChildRegPathTree tImplCust "state").

  Definition implCustomMemRegionReadRq (addr : ty Addr)
             : Action ty tImplCust Bool :=
    ReadReg "state" pCustState (fun state =>
    Let isIdle : Bool <- ##state `? "Idle" ;
    If #isIdle Then (
      Let  addr0 : Addr                         <- memLineAddr r #addr ;
      LetA rp0   : LineReadRp r.(regionLineCfg) <- liftAction child0Path (customMemRegionLineRead r children readAction addr0) ;
      WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "ReadRp0" ::= #rp0)) Retv
    ) ;
    Return #isIdle).

  Definition implCustomMemRegionReadRp
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tImplCust (Option FullCapWithTag) :=
    ReadReg "state" pCustState (fun state =>
    LetIf resOpt : Option FullCapWithTag <-
      If (##state `? "ReadRp0") Then (
        Let  rp0     : LineReadRp r.(regionLineCfg) <- ##state `! "ReadRp0" ;
        Let  crosses : Bool                         <- memCrossesLine r #addr #memSize ;
        LetIf rp1 : LineReadRp r.(regionLineCfg) <-
          If #crosses Then (
            Let addr1 : Addr <- memNextLineAddr r #addr ;
            liftAction child0Path (customMemRegionLineRead r children readAction addr1)
          ) Else (
            Return ConstDef
          ) ;
        Let  rp      : LineReadRp r.(regionLineCfg) <- memMergeLineReadRp r #addr #rp0 #rp1 ;
        Let  res     : FullCapWithTag               <- memExtractReadCap r #addr #memSize #rp ;
        Return (mkSome #res)
      ) ;
    Return #resOpt).

  Definition implCustomMemRegionDeqRp : Action ty tImplCust (Bit 0) :=
    WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv.

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
        Let rq      : LineWriteRq r.(regionLineCfg) <- memBuildLineWriteRq r #addr #stVal #memSize ;
        Let rq0     : LineWriteRq r.(regionLineCfg) <- memLineWriteRq0 r #rq ;
        Act (liftAction child0Path (customMemRegionLineWrite r children writeAction rq0)) ;
        Let crosses : Bool                          <- memCrossesLine r #addr #memSize ;
        If #crosses Then (
          Let rq1 : LineWriteRq r.(regionLineCfg) <- memLineWriteRq1 r #rq ;
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
        Let rq1 : LineWriteRq r.(regionLineCfg) <- ##state `! "WriteRq1" ;
        Act (liftAction child0Path (customMemRegionLineWrite r children writeAction rq1)) ;
        WriteReg pCustState (UNION (CustomRegionStateList r.(regionLineCfg), "Idle" ::= ($0 : Expr ty (Bit 0)))) Retv
      ) ;
      Retv)
    ).

End ImplCustomMemRegionActions.

Arguments implCustomMemRegionReadRq r children readAction [ty] addr.
Arguments implCustomMemRegionReadRp r children readAction [ty] addr memSize.
Arguments implCustomMemRegionDeqRp r children {ty}.
Arguments implCustomMemRegionWriteRq r children writeAction [ty] addr stVal memSize.
Arguments implCustomMemRegionWriteStep r children writeAction {ty}.

(* ===========================================================================
 * Unified Per-Region Implementation Dispatch
 * =========================================================================== *)

Definition implMemRegionReadRq
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implMemRegionTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem isAccessible _ _ => implInternalMemRegionLineReadRq r isAccessible addr
  | ExternalMem => implExternalMemRegionReadRq r addr memSize
  | CustomMem children readAct _ _ => implCustomMemRegionReadRq r children readAct addr
  end.

Definition implMemRegionReadRp
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implMemRegionTree r) (Option FullCapWithTag) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) (Option FullCapWithTag) with
  | InternalMem isAccessible _ _ => implInternalMemRegionReadRp r isAccessible addr memSize
  | ExternalMem => implExternalMemRegionReadRp r addr memSize
  | CustomMem children readAct _ _ => implCustomMemRegionReadRp r children readAct addr memSize
  end.

Definition implMemRegionDeqRp
           {ty : Kind -> Type}
           (r : MemRegion)
           : Action ty (implMemRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) (Bit 0) with
  | InternalMem isAccessible _ _ => @implInternalMemRegionLineDeqRp r isAccessible ty
  | ExternalMem => @implExternalMemRegionDeqRp r ty
  | CustomMem children _ _ _ => @implCustomMemRegionDeqRp r children ty
  end.

Definition implMemRegionWriteRq
           {ty : Kind -> Type}
           (r : MemRegion)
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

Arguments implMemRegionReadRq [ty] r addr memSize.
Arguments implMemRegionReadRp [ty] r addr memSize.
Arguments implMemRegionDeqRp {ty} r.
Arguments implMemRegionWriteRq [ty] r addr stVal memSize.

Definition implMemRegionStepActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem _ _ _ => []
  | ExternalMem =>
      [ (r.(regionDom), fun ty => (Act (@implExternalMemRegionReadRp0 r ty) ; @implExternalMemRegionReadRq1 r ty)) ;
        (r.(regionDom), fun ty => @implExternalMemRegionWriteStep r ty) ]
  | CustomMem children _ writeAct _ =>
      [ (r.(regionDom), fun ty => @implCustomMemRegionWriteStep r children writeAct ty) ]
  end.

Definition implMemRegionTargetPortActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (implMemRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                                                         | ExternalMem => implExternalMemRegionTree r
                                                                         | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem true _ _ =>
      [ (r.(regionDom), fun ty => @implInternalMemRegionTargetPortReadRq r ty) ;
        (r.(regionDom), fun ty => @implInternalMemRegionTargetPortReadRp r ty) ;
        (r.(regionDom), fun ty => @implInternalMemRegionTargetPortWrite r ty) ]
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
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) Bool :=
    match regions return Action ty (implRegionsTree regions) Bool with
    | [] => Return (ConstBool true)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rdy : Bool <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRq r addr memSize)
          ) Else (
            liftAction child1Path (implRegionsReadRq rs addr memSize)
          ) ;
        Return #rdy
    end.

  Fixpoint implRegionsReadRp
           (regions : list MemRegion)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) (Option FullCapWithTag) :=
    match regions return Action ty (implRegionsTree regions) (Option FullCapWithTag) with
    | [] => Return (mkSome ConstDef)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rpOpt : Option FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRp r addr memSize)
          ) Else (
            liftAction child1Path (implRegionsReadRp rs addr memSize)
          ) ;
        Return #rpOpt
    end.

  Fixpoint implRegionsDeqRp
           (regions : list MemRegion)
           (addr : ty Addr)
           : Action ty (implRegionsTree regions) (Bit 0) :=
    match regions return Action ty (implRegionsTree regions) (Bit 0) with
    | [] => Retv
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        If #isMatch Then (
          liftAction child0Path (@implMemRegionDeqRp ty r)
        ) Else (
          liftAction child1Path (implRegionsDeqRp rs addr)
        ) ;
        Retv
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
        LetIf rdy : Bool <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionWriteRq r addr stVal memSize)
          ) Else (
            liftAction child1Path (implRegionsWrite rs addr stVal memSize)
          ) ;
        Return #rdy
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

    Definition implMemCollectRegionStepActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, f ty)) (implCollectRegionStepActions regions).

    (* 1. Instruction Memory Channel *)
    Definition implReadInstRq (addr : ty Addr) : Action ty implMemTree Bool :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      implRegionsReadRq regions addr instSz.

    Definition implGetInstRp (addr : ty Addr) : Action ty implMemTree (Option Inst) :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      LetA rpOpt : Option FullCapWithTag <- implRegionsReadRp regions addr instSz ;
      LetIf instOpt : Option Inst <-
        If (##rpOpt `? "Some") Then (
          Let fullVal : FullCapWithTag <- ##rpOpt `! "Some" ;
          Return (mkSome (##fullVal`"addr"))
        ) Else (
          Return ConstDef
        ) ;
      Return #instOpt.

    Definition implDeqInstRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
      implRegionsDeqRp regions addr.

    (* 2. Data Load Channel *)
    Definition implReadMemRq (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
      implRegionsReadRq regions addr memSize.

    Definition implGetMemRp (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree (Option FullCapWithTag) :=
      implRegionsReadRp regions addr memSize.

    Definition implDeqMemRp (addr : ty Addr) : Action ty implMemTree (Bit 0) :=
      implRegionsDeqRp regions addr.

    (* 3. Revocation Bit Memory Channel *)
    Definition implReadRevBitRq (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
      LetL lookup : RevBitLookup <- computeRevBitAddr revConfig base ;
      LetIf rdy : Bool <-
        If (##lookup`"isRevokable") Then (
          Let revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
          Let sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
          implRegionsReadRq regions revByteAddr sz0
        ) Else (
          Return (ConstBool true)
        ) ;
      Return #rdy.

    Definition implGetDeqRevBitRp (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
      LetL lookup : RevBitLookup <- computeRevBitAddr revConfig base ;
      LetIf revOpt : Option Bool <-
        If (##lookup`"isRevokable") Then (
          Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
          Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
          LetA rpOpt       : Option FullCapWithTag     <- implRegionsReadRp regions revByteAddr sz0 ;
          LetIf rOpt : Option Bool <-
            If (##rpOpt `? "Some") Then (
              Act (implRegionsDeqRp regions revByteAddr) ;
              Let revCap  : FullCapWithTag <- ##rpOpt `! "Some" ;
              Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
              Let revBit  : Bool           <- extractRevBit lookup #revByte ;
              Return (mkSome #revBit)
            ) Else (
              Return ConstDef
            ) ;
          Return #rOpt
        ) Else (
          Return (mkSome (ConstBool false))
        ) ;
      Return #revOpt.

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
