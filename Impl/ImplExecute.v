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

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu ImplCommon ImplBranchPredictor ImplDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section ExecuteStage.

  (* What the sequential commit of one execute slot leaves for the next slot of the same cycle, so
   * that the next slot does not re-read state through this slot's other writes: the head of
   * decodeToAluBuf after the dequeue, the PCC it wrote, and the checks it leaves unchanged.
   * The dataMem-empty and no-write checks are not handed off: a later slot treats them as false,
   * so an op that needs them (a virtual CSR read) waits for the first slot of the next cycle.
   * It is cleared when a slot starts and at the end of every cycle, so it holds a constant at
   * the clock edge, like `canProceed`. *)
  Definition ExecHandoff := STRUCT_TYPE {
    "head"             :: Option DecodeToAluEntry ;
    "pcc"              :: FullECapWithTag ;
    "redirPending"     :: Bool ;
    "dataMemIn_isFull" :: Bool
  }.

  Definition implExecuteTree : Tree Elem :=
    Node "" [
      Leaf "execEpoch"     (EReg (Build_Reg Epoch (Some Zmod.zero))) ;
      Leaf "fenceIPending" (EReg (Build_Reg Bool (Some false))) ;
      Leaf "canProceed"    (EReg (Build_Reg Bool (Some true))) ;
      (* true for the first execute slot of a cycle, which reads the registers itself; every slot
       * clears it, and the end of the cycle sets it again *)
      Leaf "firstSlot"     (EReg (Build_Reg Bool (Some true))) ;
      Leaf "handoff"       (EReg (Build_Reg ExecHandoff (Some (getDefault _)))) ;
      (* this stage's redirect: the new PCC (its `addr` is the next fetch PC), applied at the start
       * of the next cycle (`applyRedirect`) *)
      Leaf "redirect"      (EReg (Build_Reg (Option FullECapWithTag) (Some (getDefault _))))
    ].

  Definition pExecEpoch : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "execEpoch").

  Definition readExecEpoch (ty : Kind -> Type) : Action ty implExecuteTree Epoch :=
    ReadReg "execEpoch" pExecEpoch (fun v => Return #v).

  Definition writeExecEpoch (ty : Kind -> Type) (val : ty Epoch) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecEpoch #val Retv.

  Definition pFenceIPending : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "fenceIPending").

  Definition readFenceIPending (ty : Kind -> Type) : Action ty implExecuteTree Bool :=
    ReadReg "fenceIPending" pFenceIPending (fun v => Return #v).

  Definition setFenceIPending (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pFenceIPending (ConstBool true) Retv.

  Definition clearFenceIPending (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pFenceIPending (ConstBool false) Retv.

  Definition pExecuteCanProceed : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "canProceed").

  Definition readExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree Bool :=
    ReadReg "canProceed" pExecuteCanProceed (fun v => Return #v).

  Definition setExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecuteCanProceed (ConstBool true) Retv.

  Definition clearExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecuteCanProceed (ConstBool false) Retv.

  Definition pFirstSlot : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "firstSlot").

  Definition readFirstSlot (ty : Kind -> Type) : Action ty implExecuteTree Bool :=
    ReadReg "firstSlot" pFirstSlot (fun v => Return #v).

  Definition clearFirstSlot (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pFirstSlot (ConstBool false) Retv.

  Definition pHandoff : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "handoff").

  Definition readHandoff (ty : Kind -> Type) : Action ty implExecuteTree ExecHandoff :=
    ReadReg "handoff" pHandoff (fun v => Return #v).

  Definition writeHandoff (ty : Kind -> Type) (val : ty ExecHandoff) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pHandoff #val Retv.

  Definition clearHandoff (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pHandoff ConstDef Retv.

  (* End of cycle: the first slot of the next cycle may proceed, and reads the registers itself. *)
  Definition resetExecuteCanProceed (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pExecuteCanProceed (ConstBool true)
      (WriteReg pFirstSlot (ConstBool true)
         (WriteReg pHandoff ConstDef Retv)).

  Definition pRedirect : RegPath implExecuteTree :=
    Eval cbn in (getChildRegPathTree implExecuteTree "redirect").

  Definition readRedirect (ty : Kind -> Type) : Action ty implExecuteTree (Option FullECapWithTag) :=
    ReadReg "redirect" pRedirect (fun v => Return #v).

  Definition redirectPending (ty : Kind -> Type) : Action ty implExecuteTree Bool :=
    ReadReg "redirect" pRedirect (fun v => Return (##v`"valid")).

  Definition setRedirect (ty : Kind -> Type) (pcc : ty FullECapWithTag) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pRedirect (mkSome #pcc) Retv.

  Definition clearRedirect (ty : Kind -> Type) : Action ty implExecuteTree (Bit 0) :=
    WriteReg pRedirect ConstDef Retv.

  Definition implExecuteIfc (ty : Kind -> Type) : @ExecuteIfc ty := {|
    executeTree             := implExecuteTree ;
    execute_readExecEpoch   := @readExecEpoch ty ;
    execute_readFenceIPend  := @readFenceIPending ty ;
    execute_clearFenceIPend := @clearFenceIPending ty ;
    execute_writeExecEpoch  := @writeExecEpoch ty ;
    execute_readRedirect    := @readRedirect ty ;
    execute_clearRedirect   := @clearRedirect ty
  |}.

  Variable pcAddrInit : Z.
  Variable withInstIfc : WithInstPredIfc.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable fetchIfc : forall ty, @FetchIfc ty.
  Variable decodeIfc : forall ty, @DecodeIfc ty.
  Variable dataMemIfc : forall ty, @DataMemIfc ty.
  Variable mulDivIfc : forall ty, @MulDivIfc ty.
  Variable ty : Kind -> Type.
  Variable meipAct mtipAct : Action ty (memIfc ty).(memTree) Bool.

  Local Abbreviation rfTree := (rfTree pcAddrInit).
  Local Abbreviation bpTree := withInstIfc.(withInst_BpTree).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation fetchTree := (fetchIfc ty).(fetchTree).
  Local Abbreviation decodeTree := (decodeIfc ty).(decodeTree).
  Local Abbreviation dataMemTree := (dataMemIfc ty).(dataMemTree).
  Local Abbreviation mulDivTree := (mulDivIfc ty).(mulDivTree).
  Local Abbreviation coreTree := (coreTree rfTree bpTree memTree fetchTree decodeTree implExecuteTree dataMemTree mulDivTree).
  Local Abbreviation gprPathsWithKind := (gprPathsWithKind pcAddrInit).
  Local Abbreviation isInterruptPending := (isInterruptPending pcAddrInit).
  Local Abbreviation executeInterrupt := (executeInterrupt pcAddrInit).
  Local Abbreviation executeSequential := (executeSequential pcAddrInit).
  Local Abbreviation executeNonSequential := (executeNonSequential pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf.").

  Definition np_waitBits : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.waitBits.").

  Definition np_bp : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.bp") singletonChildPath).

  Definition np_mem : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_fetch : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.fetch") singletonChildPath).

  Definition np_decode : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.decode") singletonChildPath).

  Definition np_execute : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.execute.").

  Definition np_dataMem : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.dataMem") singletonChildPath).

  Definition np_mulDiv : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.mulDiv") singletonChildPath).

  (* =========================================================================
   * STAGE 4: aluAndExecuteNonDeferred
   *
   * - Precondition: decodeToAluBuf is non-empty, the target input FIFO
   *                 (dataMem / mul / div) is not full when applicable, and
   *                 if an enabled interrupt is pending (or a virtual CSR is
   *                 read), the dataMem (Mem/Fence) pipeline is empty and no
   *                 accepted store is still waiting in the memory.
   * - Action:       Dequeue d2aEntry { aluIn, predPc, execEpoch } from
   *                 decodeToAluBuf.
   *                 - If execEpoch != currExecEpoch + redirectPending: drop entry
   *                   and clear its destination GPR wait bit.
   *                 - Otherwise: run AluRouting, Alu, and
   *                   dispatch to executeInterrupt, executeSequential, or
   *                   executeNonSequential; update branch predictor; on
   *                   ControlFlowAddrECap or committedNextPc != predPc,
   *                   set `redirect` (the new PCC); `applyRedirect`
   *                   applies it at the start of the next cycle (fetchPcc,
   *                   whose addr is the fetch PC; execEpoch + 1; no
   *                   straddle); clear
   *                   destination GPR wait bit when not
   *                   deferred, or enqueue MemFence into dataMemIfc and
   *                   Mul/Div into mulDivIfc.
   * ========================================================================= *)
  Definition aluAndExecuteNonDeferred : Action ty coreTree (Bit 0) :=
    LetA canProceed       : Bool                    <- liftAction np_execute (@readExecuteCanProceed ty) ;
    (* `firstSlot` and the hand-off are read and then cleared outside every branch, so a later
     * slot of the cycle reads a constant-false `firstSlot`, and a hand-off that is either the
     * previous slot's sequential commit or empty. *)
    LetA firstSlot        : Bool                    <- liftAction np_execute (@readFirstSlot ty) ;
    LetA handoff          : ExecHandoff             <- liftAction np_execute (@readHandoff ty) ;
    Act (liftAction np_execute (@clearFirstSlot ty)) ;
    Act (liftAction np_execute (@clearHandoff ty)) ;

    If #canProceed Then (
      Act (liftAction np_execute (@clearExecuteCanProceed ty)) ;

      (* This slot's own reads of state that an earlier slot of the same cycle may have written.
       * Only the first slot of a cycle uses them. A later slot takes them from the hand-off, so
       * that it does not read through the earlier slot's other writes. *)
      LetA headReg             : Option DecodeToAluEntry <- liftAction np_decode (decodeIfc ty).(decode_first) ;
      LetA dataMemIn_isFullReg : Bool                    <- liftAction np_dataMem (dataMemIfc ty).(dataMem_isFull) ;
      LetA dataMem_isEmptyReg  : Bool                    <- liftAction np_dataMem (dataMemIfc ty).(dataMem_isEmpty) ;
      LetA mem_noWriteRqReg    : Bool                    <- liftAction np_mem (memIfc ty).(mem_noWriteRq) ;
      (* A redirect of this stage not applied yet (`applyRedirect`) already counts: its entries are
       * stale. In the pipeline `applyRedirect` runs first in the cycle, so this is never set here. *)
      LetA redirPendingReg     : Bool                    <- liftAction np_execute (@redirectPending ty) ;
      LetA pccReg              : FullECapWithTag         <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
      LetA meip                : Bool                    <- liftAction np_mem meipAct ;
      LetA mtip                : Bool                    <- liftAction np_mem mtipAct ;
      LetA isInterruptReg      : Bool                    <- liftAction np_rf (isInterruptPending meip mtip) ;
      (* Read directly in every slot: an earlier slot writes these only in its sequential commit
       * (mul/div enqueue), or not at all (execEpoch). *)
      LetA mulIn_isFull        : Bool                    <- liftAction np_mulDiv (mulDivIfc ty).(mulDiv_isFullMul) ;
      LetA divIn_isFull        : Bool                    <- liftAction np_mulDiv (mulDivIfc ty).(mulDiv_isFullDiv) ;
      LetA currExecEpoch       : Epoch                   <- liftAction np_execute (@readExecEpoch ty) ;

      (* A later slot does nothing while an interrupt line is raised: it treats its hand-off head
       * as empty, and the first slot of the next cycle handles the interrupt. Otherwise no
       * interrupt is pending, whatever mstatus and mie hold. meip and mtip are read directly:
       * execute never writes them. *)
      Let  laterHead        : Option DecodeToAluEntry <- ##handoff`"head" ;
      Let  laterHeadOk      : Option DecodeToAluEntry <- STRUCT {
        "data"  ::= #laterHead`"data" ;
        "valid" ::= And [ #laterHead`"valid" ; Not (Or [ #meip ; #mtip ]) ]
      } ;
      Let  d2aHead          : Option DecodeToAluEntry <- ITE #firstSlot #headReg             #laterHeadOk ;
      Let  pcc              : FullECapWithTag         <- ITE #firstSlot #pccReg              (##handoff`"pcc") ;
      Let  redirPending     : Bool                    <- ITE #firstSlot #redirPendingReg     (##handoff`"redirPending") ;
      Let  dataMemIn_isFull : Bool                    <- ITE #firstSlot #dataMemIn_isFullReg (##handoff`"dataMemIn_isFull") ;
      Let  dataMem_isEmpty  : Bool                    <- And [ #firstSlot ; #dataMem_isEmptyReg ] ;
      Let  mem_noWriteRq    : Bool                    <- And [ #firstSlot ; #mem_noWriteRqReg ] ;
      Let  isInterrupt      : Bool                    <- And [ #firstSlot ; #isInterruptReg ] ;

      Let  d2aEntry       : DecodeToAluEntry <- ##d2aHead`"data" ;
      Let  pkg            : AluInInstGroup   <- ##d2aEntry`"aluIn" ;
      Let  predPc         : Addr             <- ##d2aEntry`"predPc" ;
      Let  entryExecEpoch : Epoch            <- ##d2aEntry`"execEpoch" ;
      Let  pendingEpoch   : Epoch            <- FromBit Epoch (ToBit (k := Bool) #redirPending) ;
      Let  effExecEpoch   : Epoch            <- Add [ #currExecEpoch ; #pendingEpoch ] ;

      Let  instBits        : Inst             <- ##pkg`"inst" ;
      Let  writesCd        : Bool             <- ##pkg`"writesCd" ;
      Let  dstIdxReal      : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd instBits) ;

      Let  pcAddr          : Addr               <- ##pcc`"addr" ;
      LetL aluOut          : AluOutUnion        <- wrappedAlu pcc pkg ;

      Let  aluOp           : AluOpUnion         <- ##aluOut`"Op" ;
      Let  isSeq           : Bool               <- #aluOp `? "Sequential" ;
      Let  seqOp           : SequentialUnion    <- #aluOp `! "Sequential" ;
      Let  isMulDiv        : Bool               <- And [ #isSeq ; #seqOp `? "MulDiv" ] ;
      Let  mulDivOp        : MulDivUnion        <- #seqOp `! "MulDiv" ;
      Let  isMul           : Bool               <- And [ #isMulDiv ; #mulDivOp `? "Mul" ] ;
      Let  isDiv           : Bool               <- And [ #isMulDiv ; #mulDivOp `? "Div" ] ;

      Let  nonSeqOp        : NonSequentialUnion <- #aluOp `! "NonSequential" ;
      Let  isNonSeq        : Bool               <- #aluOp `? "NonSequential" ;
      Let  isExc           : Bool               <- And [ #isNonSeq ; #nonSeqOp `? "Exception" ] ;
      Let  isNoExc         : Bool               <- And [ #isNonSeq ; #nonSeqOp `? "NoException" ] ;
      Let  noExc           : NoExceptionUnion   <- #nonSeqOp `! "NoException" ;
      Let  isMemOrFence    : Bool               <- And [ #isNoExc ; #noExc `? "DataMem" ] ;
      Let  isCfScrCsr      : Bool               <- And [ #isNoExc ; #noExc `? "CfScrCsr" ] ;
      Let  cfScrCsr        : CfScrCsrUnion      <- #noExc `! "CfScrCsr" ;
      Let  isScrCsr        : Bool               <- And [ #isCfScrCsr ; #cfScrCsr `? "ScrCsr" ] ;
      Let  scrCsr          : ScrCsrPayload      <- #cfScrCsr `! "ScrCsr" ;
      Let  sDest           : TaggedUnion ScrCsrIdx <- ##scrCsr`"SpecialDest" ;
      Let  isCsr           : Bool               <- And [ #isScrCsr ; #sDest `? "Csr" ] ;
      Let  csrIdx          : Bit CsrIdxSz       <- #sDest `! "Csr" ;
      Let  isVirtCsr       : Bool               <- And [ #isCsr ; csrIdxIsVirtual csrIdx ] ;

      Let  dstVal          : FullECapWithTag    <- ##aluOut`"dstValue" ;
      Let  reqDst          : Bit RegIdxSzReal   <- ##aluOut`"dstIdx" ;
      Let  reqAddr         : Addr               <- ##dstVal`"addr" ;

      Let  waitFalse : Bool <- ConstBool false ;

      If (##d2aHead`"valid") Then (
        If (Not (Eq #entryExecEpoch #effExecEpoch)) Then (
          Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
          liftAction np_waitBits
            (@setDstWaitBits ty
               writesCd dstIdxReal
               waitFalse)
        ) Else (
          If #isInterrupt Then (
            If (And [ #dataMem_isEmpty ; #mem_noWriteRq ]) Then (
              Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
              LetA execOut         : ExecuteOut      <- liftAction np_rf (executeInterrupt pcc meip mtip) ;
              Let  nextPcc         : FullECapWithTag <- ##execOut`"nextPcc" ;
              Act (liftAction np_rf (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc)) ;

              (* the redirect takes effect in the next cycle (`applyRedirect`) *)
              Act (liftAction np_execute (@setRedirect ty nextPcc)) ;

              liftAction np_waitBits
                (@setDstWaitBits ty
                   writesCd dstIdxReal
                   waitFalse)
            ) ;
            Retv
          ) Else (
            If #isSeq Then (
              If (And [ Or [ Not #isMul ; Not #mulIn_isFull ] ;
                        Or [ Not #isDiv ; Not #divIn_isFull ] ]) Then (
                Act (liftAction np_execute (@setExecuteCanProceed ty)) ;
                Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
                LetA mulDivOpt : Option MulDivUnion <- liftAction np_rf (executeSequential pcc aluOut) ;
                Let  nextPcc   : FullECapWithTag    <- #pcc `{ "addr" <- #predPc } ;
                Act (liftAction np_rf (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc)) ;

                (* Hand-off to the next slot of this cycle: the head after the dequeue above, the
                 * PCC just written, and the checks that a sequential commit leaves unchanged.
                 * This is the only place the hand-off is written with data. *)
                LetA nextHead    : Option DecodeToAluEntry <- liftAction np_decode (decodeIfc ty).(decode_first) ;
                Let  nextHandoff : ExecHandoff             <- STRUCT {
                  "head"             ::= #nextHead ;
                  "pcc"              ::= #nextPcc ;
                  "redirPending"     ::= #redirPending ;
                  "dataMemIn_isFull" ::= #dataMemIn_isFull
                } ;
                Act (liftAction np_execute (@writeHandoff ty nextHandoff)) ;

                If (#mulDivOpt`"valid") Then (
                  Let mdOp : MulDivUnion <- #mulDivOpt`"data" ;
                  If (#mdOp `? "Mul") Then (
                    Let mOp : MulOp <- #mdOp `! "Mul" ;
                    liftAction np_mulDiv ((mulDivIfc ty).(mulDiv_enqMul) reqDst reqAddr mOp)
                  ) Else (
                    Let dOp : DivOp <- #mdOp `! "Div" ;
                    liftAction np_mulDiv ((mulDivIfc ty).(mulDiv_enqDiv) reqDst reqAddr dOp)
                  ) ;
                  Retv
                ) Else (
                  liftAction np_waitBits
                    (@setDstWaitBits ty
                       writesCd dstIdxReal
                       waitFalse)
                ) ;
                Retv
              ) ;
              Retv
            ) Else (
              If (And [ Or [ Not #isMemOrFence ; Not #dataMemIn_isFull ] ;
                        Or [ Not #isVirtCsr ; And [ #dataMem_isEmpty ; #mem_noWriteRq ] ] ]) Then (
                Act (liftAction np_decode (decodeIfc ty).(decode_deq)) ;
                LetA execOut         : ExecuteOut      <- liftAction np_rf (executeNonSequential pcc meip mtip aluOut) ;
                Let  nextPcc         : FullECapWithTag <- ##execOut`"nextPcc" ;
                Act (liftAction np_rf (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc)) ;

                Let  cfOpt           : Option CfPayload <- ##execOut`"cf" ;
                Let  hasCf           : Bool             <- #cfOpt`"valid" ;
                Let  cf              : CfPayload        <- #cfOpt`"data" ;
                Let  committedNextPc : Addr             <- ##nextPcc`"addr" ;
                Let  capChanged      : Bool             <- And [ #hasCf ; ##cf`"capChanged" ] ;

                If #hasCf Then (
                  liftAction np_bp (withInstIfc.(withInst_updCf) pcAddr cf)
                ) ;

                If #isExc Then (
                  liftAction np_bp (withInstIfc.(withInst_updException) pcAddr)
                ) ;

                (* the redirect takes effect in the next cycle (`applyRedirect`) *)
                If (Or [ #isExc ; #capChanged ; ##execOut`"isFenceIRq" ; Not (Eq #committedNextPc #predPc) ]) Then (
                  liftAction np_execute (@setRedirect ty nextPcc)
                ) ;

                If (##execOut`"isFenceIRq") Then (
                  liftAction np_execute (@setFenceIPending ty)
                ) ;

                Let dataMemOpt : Option MemFenceUnion <- ##execOut`"dataMem" ;
                If (#dataMemOpt`"valid") Then (
                  Let mfOp : MemFenceUnion <- #dataMemOpt`"data" ;
                  liftAction np_dataMem ((dataMemIfc ty).(dataMem_enq) reqDst reqAddr mfOp)
                ) Else (
                  liftAction np_waitBits
                    (@setDstWaitBits ty
                       writesCd dstIdxReal
                       waitFalse)
                ) ;
                Retv
              ) ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End ExecuteStage.
