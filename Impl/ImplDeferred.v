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
From Cheriot Require Import SpecDefines FunctionalUnits ImplCommon ImplDevice Fifo SpecFetchDeferred SpecMulDiv ImplStaged ImplMulDiv.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Definition ImplMulStages  : nat := 1%nat.
Definition ImplDivStages  : nat := 1%nat.
Definition ImplMulDivMode : MulDivMode := IterMul_SharedIterDiv.

Definition DeferredStateList : list (string * Kind) :=
  [ ("LoadRq", Bit 0) ;
    ("LoadRp", LoadCmd) ;
    ("RevRp",  RevCmd) ].

Definition DeferredState : Kind := TaggedUnion DeferredStateList.

Section DeferredStages.
  Variable dom : string.
  Variable capacity : nat.

  Definition deferredTree : Tree DomainElem :=
    Node "deferred" [
      Node "inputBuf" [ fifoTree dom capacity DeferredReq ] ;
      Leaf "state"    (dom, EReg (Build_Reg DeferredState (Some (getDefault _)) false)) ;
      mulDivTree dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode
    ].

  Definition pState : RegPath deferredTree :=
    Eval cbn in (getChildRegPathTree deferredTree "state").

  Definition readState (ty : Kind -> Type) : Action ty deferredTree DeferredState :=
    ReadReg "state" pState (fun v => Return #v).

  Definition writeState (ty : Kind -> Type) (val : Expr ty DeferredState) : Action ty deferredTree (Bit 0) :=
    WriteReg pState val Retv.

  Definition np_defInputFifo : NodePath deferredTree :=
    Eval cbn in (getNodePath deferredTree "deferred.inputBuf.fifo").

  Definition np_defMulDiv : NodePath deferredTree :=
    Eval cbn in (getNodePath deferredTree "deferred.mulDiv").

  Definition deferredIsEmpty (ty : Kind -> Type) : Action ty deferredTree Bool :=
    LetA inEmpty : Bool          <- liftAction np_defInputFifo (@isEmpty dom capacity DeferredReq ty) ;
    LetA state   : DeferredState <- @readState ty ;
    LetA mdEmpty : Bool          <-
      liftAction np_defMulDiv
        (@mulDivIsEmpty dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode ty) ;
    Return (And [ #inEmpty ; #state `? "LoadRq" ; #mdEmpty ]).

  Variable pcAddrInit : Z.
  Variable bpTree fetchTree decodeTree : Tree DomainElem.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation coreTree := (coreTree dom pcAddrInit bpTree memTree fetchTree decodeTree deferredTree).
  Local Notation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits").

  Definition np_mem : NodePath coreTree :=
    Eval cbn in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_deferred : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.deferred").

  Definition np_inputFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.deferred.inputBuf.fifo").

  Definition np_mulDiv : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.deferred.deferred.mulDiv").

  Local Definition commitWb (dstIdx : ty (Bit RegIdxSzReal)) (dstVal : ty FullECapWithTag) : Action ty coreTree (Bit 0) :=
    If (isNotZero #dstIdx) Then (
      Act (liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #dstVal)) ;
      liftAction np_waitBits (@writeGprWaitBit dom ty #dstIdx (ConstBool false))
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 1: loadRqOrStoreOrFence
   *
   * - Active when state is "LoadRq". Dispatches head of inputFifo via
   *   dispatchDeferredReq:
   *   - Store:  issues mem_writeMem and dequeues inputFifo.
   *   - Load:   issues mem_readMemRq, transitions state to "LoadRp", and
   *             dequeues inputFifo.
   *   - Fence:  no-op (only one memory request is ever in flight); dequeues
   *             inputFifo.
   *   - MulDiv: enqueues into MulDiv subsystem when ready.
   * ========================================================================= *)
  Definition loadRqOrStoreOrFence : Action ty coreTree (Bit 0) :=
    LetA state     : DeferredState      <- liftAction np_deferred (@readState ty) ;
    LetA inputHead : Option DeferredReq <- liftAction np_inputFifo (@first dom capacity DeferredReq ty) ;

    If (And [ #state `? "LoadRq" ; #inputHead`"valid" ]) Then (
      Let  req    : DeferredReq    <- #inputHead`"data" ;
      LetL action : DeferredAction <- dispatchDeferredReq req ;

      If (##action `? "MemFence") Then (
        Let mfAct : MemFenceAction <- ##action `! "MemFence" ;

        If (##mfAct `? "Mem") Then (
          Let memAct : MemAction <- ##mfAct `! "Mem" ;

          If (##memAct `? "Store") Then (
            Let st        : StoreCmd                  <- ##memAct `! "Store" ;
            Let stAddr    : Addr                      <- ##st`"addr" ;
            Let stVal     : FullCapWithTag            <- ##st`"stVal" ;
            Let memSize   : Bit LgLgNumBytesFullCapSz <- ##st`"memSize" ;
            LetA accepted : Bool                      <- liftAction np_mem ((memIfc ty).(mem_writeMem) stAddr stVal memSize) ;
            If #accepted Then (
              liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
            ) ;
            Retv
          ) Else (
            Let  ld       : LoadCmd                   <- ##memAct `! "Load" ;
            Let  ldAddr   : Addr                      <- ##ld`"addr" ;
            Let  pending  : PendingLoad               <- ##ld`"pending" ;
            Let  memSize  : Bit LgLgNumBytesFullCapSz <- ##pending`"memSize" ;
            LetA accepted : Bool                      <- liftAction np_mem ((memIfc ty).(mem_readMemRq) ldAddr memSize) ;
            If #accepted Then (
              Act (liftAction np_deferred (@writeState ty (UNION (DeferredStateList, "LoadRp" ::= #ld)))) ;
              liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
        ) ;
        Retv
      ) Else (
        Let  md       : MulDivCmd        <- ##action `! "MulDiv" ;
        Let  op1      : Addr             <- ##md`"op1" ;
        Let  mulDivOp : MulDivUnion      <- ##md`"mulDivOp" ;
        Let  dstIdx   : Bit RegIdxSzReal <- ##md`"dstIdx" ;
        Let  isMul    : Bool             <- #mulDivOp `? "Mul" ;
        LetA canEnq   : Bool             <-
          liftAction np_mulDiv
            (@mulDivCanEnq dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode ty isMul) ;
        If #canEnq Then (
          Act (liftAction np_mulDiv
                 (@mulDivEnqReq dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode ty dstIdx op1 mulDivOp)) ;
          liftAction np_inputFifo (@deq dom capacity DeferredReq ty)
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: loadRpAndWritebackOrIssueRevRq
   *
   * - Active when state is "LoadRp". Peeks load response via mem_getMemRp.
   * - Uses dispatchLoadResponse:
   *   - RevLookup: when mem_readRevBitRq is accepted, dequeues mem_deqMemRp
   *                and transitions state to "RevRp".
   *   - Writeback: dequeues mem_deqMemRp, writes back to RF, clears
   *                waitBit[dstIdx], and transitions state to "LoadRq".
   * ========================================================================= *)
  Definition loadRpAndWritebackOrIssueRevRq (config : RevConfig) : Action ty coreTree (Bit 0) :=
    LetA state : DeferredState <- liftAction np_deferred (@readState ty) ;

    If (#state `? "LoadRp") Then (
      Let  ld        : LoadCmd                   <- #state `! "LoadRp" ;
      Let  ldAddr    : Addr                      <- ##ld`"addr" ;
      Let  pl        : PendingLoad               <- ##ld`"pending" ;
      Let  memSize   : Bit LgLgNumBytesFullCapSz <- ##pl`"memSize" ;
      LetA memValOpt : Option FullCapWithTag     <- liftAction np_mem ((memIfc ty).(mem_getMemRp) ldAddr memSize) ;

      If (##memValOpt`"valid") Then (
        Let  memVal  : FullCapWithTag <- ##memValOpt`"data" ;
        LetL outcome : LoadOutcome    <- dispatchLoadResponse config pl memVal ;

        If (#outcome `? "RevLookup") Then (
          Let  revInfo  : RevCmd           <- #outcome `! "RevLookup" ;
          Let  revBase  : Bit (AddrSz + 1) <- ##revInfo`"base" ;
          LetA accepted : Bool             <- liftAction np_mem ((memIfc ty).(mem_readRevBitRq) revBase) ;
          If #accepted Then (
            Act (liftAction np_mem ((memIfc ty).(mem_deqMemRp) ldAddr)) ;
            liftAction np_deferred (@writeState ty (UNION (DeferredStateList, "RevRp" ::= #revInfo)))
          ) ;
          Retv
        ) Else (
          Let wbInfo  : WbCmd            <- #outcome `! "Writeback" ;
          Let dstIdxV : Bit RegIdxSzReal <- ##wbInfo`"dstIdx" ;
          Let dstValV : FullECapWithTag  <- ##wbInfo`"dstVal" ;
          Act (liftAction np_mem ((memIfc ty).(mem_deqMemRp) ldAddr)) ;
          Act (commitWb dstIdxV dstValV) ;
          liftAction np_deferred (@writeState ty (UNION (DeferredStateList, "LoadRq" ::= ($0 : Expr ty (Bit 0)))))
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 3: revRpAndWriteBack
   *
   * - Active when state is "RevRp". Consumes revocation bit response via
   *   mem_getDeqRevBitRp, writes back final capability to RF, clears
   *   waitBit[dstIdx], and transitions state to "LoadRq".
   * ========================================================================= *)
  Definition revRpAndWriteBack : Action ty coreTree (Bit 0) :=
    LetA state : DeferredState <- liftAction np_deferred (@readState ty) ;

    If (#state `? "RevRp") Then (
      Let  revInfo   : RevCmd           <- #state `! "RevRp" ;
      Let  revBase   : Bit (AddrSz + 1) <- ##revInfo`"base" ;
      Let  pr        : PendingRev       <- ##revInfo`"pendingRev" ;
      LetA revBitOpt : Option Bool      <- liftAction np_mem ((memIfc ty).(mem_getDeqRevBitRp) revBase) ;

      If (##revBitOpt`"valid") Then (
        Let  revBit  : Bool             <- ##revBitOpt`"data" ;
        LetL wbInfo  : WbCmd            <- dispatchRevResponse pr revBit ;
        Let  dstIdxV : Bit RegIdxSzReal <- ##wbInfo`"dstIdx" ;
        Let  dstValV : FullECapWithTag  <- ##wbInfo`"dstVal" ;
        Act (commitWb dstIdxV dstValV) ;
        liftAction np_deferred (@writeState ty (UNION (DeferredStateList, "LoadRq" ::= ($0 : Expr ty (Bit 0)))))
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * MULDIV SUBSYSTEM STAGES & WRITEBACK
   * ========================================================================= *)

  Definition mulDivStageRules : list (Action ty coreTree (Bit 0)) :=
    map (fun a => liftAction np_mulDiv a)
        (@mulDivAllStageRules dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode ty).

  Local Definition mulDivWriteBack
    (popResp : Action ty (mulDivTree dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode) (Option (MulDivWbResp (Z.to_nat Xlen))))
    : Action ty coreTree (Bit 0) :=
    LetA wbOpt : Option (MulDivWbResp (Z.to_nat Xlen)) <- liftAction np_mulDiv popResp ;
    If (#wbOpt`"valid") Then (
      Let wb      : MulDivWbResp (Z.to_nat Xlen) <- #wbOpt`"data" ;
      Let dstIdx  : Bit RegIdxSzReal             <- ##wb`"dst" ;
      Let resAddr : Addr                         <- ##wb`"res" ;
      Let wbVal   : FullECapWithTag              <- STRUCT {
        "tag"  ::= Const ty Bool false ;
        "ecap" ::= Const ty ECap (getDefault _) ;
        "addr" ::= #resAddr
      } ;
      commitWb dstIdx wbVal
    ) ;
    Retv.

  Definition mulWriteBack : Action ty coreTree (Bit 0) :=
    mulDivWriteBack (@mulDivPopMulResp dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode ty).

  Definition divWriteBack : Action ty coreTree (Bit 0) :=
    mulDivWriteBack (@mulDivPopDivResp dom (Z.to_nat Xlen) ImplMulStages ImplDivStages ImplMulDivMode ty).

  Definition mulDivWriteBackRules : list (Action ty coreTree (Bit 0)) :=
    [mulWriteBack ; divWriteBack].

  Definition mulDivRules : list (Action ty coreTree (Bit 0)) :=
    mulDivStageRules ++ mulDivWriteBackRules.

End DeferredStages.
