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

From Stdlib Require Import String List ZArith.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines FunctionalUnits ImplCommon ImplDevice SpecFetchDeferred ShiftFifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Definition MemFenceReq : Kind := STRUCT_TYPE {
  "dstIdx" :: Bit RegIdxSzReal ;
  "addr"   :: Addr ;
  "op"     :: MemFenceUnion
}.

Definition DataMemStateList : list (string * Kind) :=
  [ ("LoadRq", Bit 0) ;
    ("LoadRp", LoadCmd) ;
    ("RevRq",  RevCmd) ;
    ("RevRp",  RevCmd) ].

Definition DataMemState : Kind := TaggedUnion DataMemStateList.

Section DataMemStages.
  Variable dom : string.
  Variable capacity : nat.

  Definition implDataMemTree : Tree DomainElem :=
    Node "" [
      Node "inputBuf" [ fifoTree dom capacity MemFenceReq ] ;
      Leaf "state"    (dom, EReg (Build_Reg DataMemState (Some (getDefault _)) false))
    ].

  Definition pState : RegPath implDataMemTree :=
    Eval cbn in (getChildRegPathTree implDataMemTree "state").

  Definition readState (ty : Kind -> Type) : Action ty implDataMemTree DataMemState :=
    ReadReg "state" pState (fun v => Return #v).

  Definition writeState (ty : Kind -> Type) (val : ty DataMemState) : Action ty implDataMemTree (Bit 0) :=
    WriteReg pState #val Retv.

  Definition np_dmInputFifo : NodePath implDataMemTree :=
    Eval cbn in (getNodePath implDataMemTree ".inputBuf.fifo").

  Definition dataMemIsEmpty (ty : Kind -> Type) : Action ty implDataMemTree Bool :=
    LetA inEmpty : Bool         <- liftAction np_dmInputFifo (@isEmpty dom capacity MemFenceReq ty) ;
    LetA state   : DataMemState <- @readState ty ;
    Return (And [ #inEmpty ; #state `? "LoadRq" ]).

  Definition dataMemIsFull (ty : Kind -> Type) : Action ty implDataMemTree Bool :=
    liftAction np_dmInputFifo (@isFull dom capacity MemFenceReq ty).

  Definition dataMemEnq (ty : Kind -> Type)
    (dstIdx : ty (Bit RegIdxSzReal)) (addr : ty Addr) (op : ty MemFenceUnion) :
    Action ty implDataMemTree (Bit 0) :=
    Let req : MemFenceReq <- STRUCT {
      "dstIdx" ::= #dstIdx ;
      "addr"   ::= #addr ;
      "op"     ::= #op
    } ;
    liftAction np_dmInputFifo (@enq dom capacity MemFenceReq ty req).

  Definition implDataMemIfc (ty : Kind -> Type) : @DataMemIfc ty := {|
    dataMemTree     := implDataMemTree ;
    dataMem_isEmpty := @dataMemIsEmpty ty ;
    dataMem_isFull  := @dataMemIsFull ty ;
    dataMem_enq     := @dataMemEnq ty
  |}.

  Variable pcAddrInit : Z.
  Variable bpTree fetchTree decodeTree mulDivTree : Tree DomainElem.
  Variable executeIfc : forall ty, @ExecuteIfc ty.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation executeTree := (executeIfc ty).(executeTree).
  Local Abbreviation coreTree := (coreTree dom rfTree bpTree memTree fetchTree decodeTree executeTree implDataMemTree mulDivTree).
  Local Abbreviation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf.").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits.").

  Definition np_mem : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_execute : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.execute") singletonChildPath).

  Definition np_dataMem : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.dataMem.").

  Definition np_inputFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.dataMem..inputBuf.fifo").

  Local Definition commitWb (dstIdx : ty (Bit RegIdxSzReal)) (dstVal : ty FullECapWithTag) : Action ty coreTree (Bit 0) :=
    If (isNotZero #dstIdx) Then (
      Let waitFalse : Bool <- ConstBool false ;
      Act (liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #dstVal)) ;
      liftAction np_waitBits (@writeGprWaitBit dom ty dstIdx waitFalse)
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 1: loadRqOrStoreOrFence
   *
   * - Active when state is "LoadRq". Dispatches head of inputFifo via
   *   dispatchMemFence:
   *   - Store:  issues mem_writeMem and dequeues inputFifo.
   *   - Load:   issues mem_readMemRq, transitions state to "LoadRp", and
   *             dequeues inputFifo.
   *   - Fence:  issues mem_fenceI_req / mem_fence_req and dequeues
   *             inputFifo.
   * ========================================================================= *)
  Definition loadRqOrStoreOrFence : Action ty coreTree (Bit 0) :=
    LetA state     : DataMemState       <- liftAction np_dataMem (@readState ty) ;
    LetA inputHead : Option MemFenceReq <- liftAction np_inputFifo (@first dom capacity MemFenceReq ty) ;

    If (And [ #state `? "LoadRq" ; #inputHead`"valid" ]) Then (
      Let  req    : MemFenceReq      <- #inputHead`"data" ;
      Let  dstIdx : Bit RegIdxSzReal <- ##req`"dstIdx" ;
      Let  addr   : Addr             <- ##req`"addr" ;
      Let  op     : MemFenceUnion    <- ##req`"op" ;
      LetL mfAct  : MemFenceAction   <- dispatchMemFence dstIdx addr op ;

      If (##mfAct `? "Mem") Then (
        Let memAct : MemAction <- ##mfAct `! "Mem" ;

        If (##memAct `? "Store") Then (
          Let st        : StoreCmd                  <- ##memAct `! "Store" ;
          Let stAddr    : Addr                      <- ##st`"addr" ;
          Let stVal     : FullCapWithTag            <- ##st`"stVal" ;
          Let memSize   : Bit LgLgNumBytesFullCapSz <- ##st`"memSize" ;
          LetA accepted : Bool                      <- liftAction np_mem ((memIfc ty).(mem_writeMem) stAddr stVal memSize) ;
          If #accepted Then (
            liftAction np_inputFifo (@deq dom capacity MemFenceReq ty)
          ) ;
          Retv
        ) Else (
          Let  ld        : LoadCmd                   <- ##memAct `! "Load" ;
          Let  ldAddr    : Addr                      <- ##ld`"addr" ;
          Let  pending   : PendingLoad               <- ##ld`"pending" ;
          Let  memSize   : Bit LgLgNumBytesFullCapSz <- ##pending`"memSize" ;
          LetA accepted  : Bool                      <- liftAction np_mem ((memIfc ty).(mem_readMemRq) ldAddr memSize) ;
          If #accepted Then (
            Let nextState : DataMemState <- UNION (DataMemStateList, "LoadRp" ::= #ld) ;
            Act (liftAction np_dataMem (@writeState ty nextState)) ;
            liftAction np_inputFifo (@deq dom capacity MemFenceReq ty)
          ) ;
          Retv
        ) ;
        Retv
      ) Else (
        Let fenceVal : FenceOp <- ##mfAct `! "Fence" ;
        Let isFenceI : Bool    <- ##fenceVal`"FenceI" ;
        LetIf accepted : Bool <-
          If #isFenceI Then (
            liftAction np_mem ((memIfc ty).(mem_fenceI_req))
          ) Else (
            liftAction np_mem ((memIfc ty).(mem_fence_req) fenceVal)
          ) ;
        If #accepted Then (
          Act (If #isFenceI Then (
            liftAction np_execute (executeIfc ty).(execute_clearFenceIPend)
          ) ; Retv) ;
          liftAction np_inputFifo (@deq dom capacity MemFenceReq ty)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2a: loadRpAndWriteback
   *
   * - Active when state is "LoadRp". Peeks load response via mem_getMemRp.
   * - Unconditionally dequeues mem_deqMemRp when valid, and uses
   *   dispatchLoadResponse:
   *   - RevLookup: transitions state to "RevRq".
   *   - Writeback: writes back to RF, clears waitBit[dstIdx], and transitions
   *                state to "LoadRq".
   * ========================================================================= *)
  Definition loadRpAndWriteback (config : RevConfig) : Action ty coreTree (Bit 0) :=
    LetA state : DataMemState <- liftAction np_dataMem (@readState ty) ;

    If (#state `? "LoadRp") Then (
      Let  ld        : LoadCmd                   <- #state `! "LoadRp" ;
      Let  ldAddr    : Addr                      <- ##ld`"addr" ;
      Let  pl        : PendingLoad               <- ##ld`"pending" ;
      Let  memSize   : Bit LgLgNumBytesFullCapSz <- ##pl`"memSize" ;
      LetA memValOpt : Option FullCapWithTag     <- liftAction np_mem ((memIfc ty).(mem_getMemRp) ldAddr memSize) ;

      If (##memValOpt`"valid") Then (
        Act (liftAction np_mem ((memIfc ty).(mem_deqMemRp) ldAddr)) ;
        Let  memVal  : FullCapWithTag <- ##memValOpt`"data" ;
        LetL outcome : LoadOutcome    <- dispatchLoadResponse config pl memVal ;

        If (#outcome `? "RevLookup") Then (
          Let revInfo   : RevCmd       <- #outcome `! "RevLookup" ;
          Let nextState : DataMemState <- UNION (DataMemStateList, "RevRq" ::= #revInfo) ;
          liftAction np_dataMem (@writeState ty nextState)
        ) Else (
          Let wbInfo    : WbCmd            <- #outcome `! "Writeback" ;
          Let dstIdxV   : Bit RegIdxSzReal <- ##wbInfo`"dstIdx" ;
          Let dstValV   : FullECapWithTag  <- ##wbInfo`"dstVal" ;
          Let nextState : DataMemState     <- UNION (DataMemStateList, "LoadRq" ::= ($0 : Expr ty (Bit 0))) ;
          Act (commitWb dstIdxV dstValV) ;
          liftAction np_dataMem (@writeState ty nextState)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2b: issueRevRq
   *
   * - Active when state is "RevRq". Issues mem_readRevBitRq; when accepted,
   *   transitions state to "RevRp".
   * ========================================================================= *)
  Definition issueRevRq : Action ty coreTree (Bit 0) :=
    LetA state : DataMemState <- liftAction np_dataMem (@readState ty) ;

    If (#state `? "RevRq") Then (
      Let  revInfo  : RevCmd           <- #state `! "RevRq" ;
      Let  revBase  : Bit (AddrSz + 1) <- ##revInfo`"base" ;
      LetA accepted : Bool             <- liftAction np_mem ((memIfc ty).(mem_readRevBitRq) revBase) ;
      If #accepted Then (
        Let nextState : DataMemState <- UNION (DataMemStateList, "RevRp" ::= #revInfo) ;
        liftAction np_dataMem (@writeState ty nextState)
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: loadRpAndIssueRevRq
   *
   * - Linearly combines loadRpAndWriteback and issueRevRq.
   * ========================================================================= *)
  Definition loadRpAndIssueRevRq (config : RevConfig) : Action ty coreTree (Bit 0) :=
    Act (loadRpAndWriteback config) ;
    issueRevRq.

  (* =========================================================================
   * STAGE 3: revRpAndWriteBack
   *
   * - Active when state is "RevRp". Consumes revocation bit response via
   *   mem_getDeqRevBitRp, writes back final capability to RF, clears
   *   waitBit[dstIdx], and transitions state to "LoadRq".
   * ========================================================================= *)
  Definition revRpAndWriteBack : Action ty coreTree (Bit 0) :=
    LetA state : DataMemState <- liftAction np_dataMem (@readState ty) ;

    If (#state `? "RevRp") Then (
      Let  revInfo   : RevCmd           <- #state `! "RevRp" ;
      Let  revBase   : Bit (AddrSz + 1) <- ##revInfo`"base" ;
      Let  pr        : PendingRev       <- ##revInfo`"pendingRev" ;
      LetA revBitOpt : Option Bool      <- liftAction np_mem ((memIfc ty).(mem_getDeqRevBitRp) revBase) ;

      If (##revBitOpt`"valid") Then (
        Let  revBit    : Bool             <- ##revBitOpt`"data" ;
        LetL wbInfo    : WbCmd            <- dispatchRevResponse pr revBit ;
        Let  dstIdxV   : Bit RegIdxSzReal <- ##wbInfo`"dstIdx" ;
        Let  dstValV   : FullECapWithTag  <- ##wbInfo`"dstVal" ;
        Let  nextState : DataMemState     <- UNION (DataMemStateList, "LoadRq" ::= ($0 : Expr ty (Bit 0))) ;
        Act (commitWb dstIdxV dstValV) ;
        liftAction np_dataMem (@writeState ty nextState)
      ) ;
      Retv
    ) ;
    Retv.

End DataMemStages.
