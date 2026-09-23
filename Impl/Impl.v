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

From Stdlib Require Import String List ZArith Zmod Psatz Bool.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic Fifo ImplRevoker ImplDevice ImplDefines ImplFetch ImplDeferred.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Pipelined System Tree and Implementation Module
 * =========================================================================== *)

Section ImplDom.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable tohostAddr : Z.
  Variable fetchCapacity deferredCapacity : nat.

  Definition implSysTree (config : RevConfig) (regions : list MemRegion) : Tree DomainElem :=
    Node "sys" [
      coreTree core pcAddrInit (implMemTree core regions) fetchCapacity deferredCapacity
    ].

  Section Impl.
    Variable config : RevConfig.
    Variable regions : list MemRegion.
    Variable clint : @ClintInstance core regions.
    Variable rev : @RevokerInstance core regions.
    Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

    Local Notation memTree := (implMemTree core regions).
    Local Notation memIfc := (@implMemIfc core config regions).
    Local Notation cTree := (coreTree core pcAddrInit memTree fetchCapacity deferredCapacity).
    Local Notation sysTree := (implSysTree config regions).
    Local Notation gprPathsWithKind := (gprPathsWithKind core pcAddrInit).
    Local Notation scrPathsWithKind := (scrPathsWithKind core pcAddrInit).
    Local Notation csrPathsWithKind := (csrPathsWithKind core pcAddrInit).
    Local Notation incrementMcycle := (incrementMcycle core pcAddrInit).
    Local Notation incrementMinstret := (incrementMinstret core pcAddrInit).
    Local Notation regRead := (regRead core pcAddrInit).
    Local Notation executeNonDeferred := (executeNonDeferred core pcAddrInit).

    Section Ty.
      Variable ty : Kind -> Type.

      Definition np_core : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core").

      Definition np_rf : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.rf").

      Definition np_waitBits : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.waitBits").

      Definition np_mem : NodePath sysTree :=
        Eval cbn in (embedNodeIntoPath (getNodePath sysTree "sys.core.mem") singletonChildPath).

      Definition np_fetchOutFifo : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.fetch.fetchOutBuf.fifo").

      Definition np_decodeToAluFifo : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.decodeToAluBuf.fifo").

      Definition np_aluToExecFifo : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.aluToExecBuf.fifo").

      Definition np_deferredInFifo : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.deferred.inputBuf.fifo").

      (* =====================================================================
       * Peripheral Background Rules & Interrupt Polling on implMemTree
       * ===================================================================== *)

      Local Definition implClintAction {k : Kind} (act : Action ty (Node "clint" (clintChildren core)) k)
        : Action ty memTree k :=
        @implMemNthRegionAction core regions ty clint.(clintIdx) (@clintRegion core regions clint) clint.(pfClint) k act.

      Local Notation nIrq := (S (S (length (collectIrqActions regions)))).

      Local Definition implPlicAction {k : Kind} (act : Action ty (plicTree core nIrq) k)
        : Action ty memTree k :=
        @implMemNthRegionAction core regions ty plic.(plicIdx) (@plicRegion core nIrq regions plic) plic.(pfPlic) k act.

      Definition implTickCycle : Action ty sysTree (Bit 0) :=
        liftAction np_rf incrementMcycle.

      Definition implTickTimer : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintTick core ty)).

      Definition implMemStepSecondLineSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implMemStepSecondLine core regions ty).

      Definition implRevokerStepsSys : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act) (@implRevokerSteps core config regions ty rev).

      Definition implPlicClaimStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implPlicAction (@updateClaim core nIrq ty)).

      Local Definition implPlicUartIrqAction : Action ty memTree Bool :=
        implPlicAction (Recv "uartIrq" (plicUartIrqPath core nIrq) (fun v => Return #v)).

      Local Fixpoint implPlicPendingStepsHelper
        (acts : list (Action ty memTree Bool))
        (pends : list (RegOfKind (t := plicTree core nIrq) Bool))
        (insvs : list (RegOfKind (t := plicTree core nIrq) Bool))
        : list (Action ty memTree (Bit 0)) :=
        match acts, pends, insvs with
        | act :: restActs, pendRk :: restPends, insvRk :: restInsvs =>
            (LetA irqVal : Bool <- act ;
             implPlicAction (@updatePendingLeaf core nIrq ty pendRk insvRk irqVal))
            :: implPlicPendingStepsHelper restActs restPends restInsvs
        | _, _, _ => []
        end.

      Definition implPlicPendingsSteps : list (Action ty sysTree (Bit 0)) :=
        let memSteps :=
          match pendingPathsWithKind core nIrq, inServicePathsWithKind core nIrq with
          | _ :: devPends, _ :: devInsvs =>
              implPlicPendingStepsHelper
                (@implMemCollectIrqActions core regions ty ++ [implPlicUartIrqAction])
                devPends
                devInsvs
          | _, _ => []
          end in
        map (fun act => liftAction np_mem act) memSteps.

      (* =====================================================================
       * STAGE 1 & 2: Fetch Request & Fetch Response
       * ===================================================================== *)

      Definition fetchRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@fetchRq core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition fetchCrossLineStage : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implMemStepSecondLine core regions ty).

      Definition fetchRpStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@fetchRp core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      (* =====================================================================
       * STAGE 3: Decode & Register Read with Scoreboard (waitBits)
       * ===================================================================== *)

      Definition decodeAndRegRead : Action ty sysTree (Bit 0) :=
        LetA fetchHead          : Option FetchOut <- liftAction np_fetchOutFifo (@first core fetchCapacity FetchOut ty) ;
        LetA decodeToAlu_isFull : Bool            <- liftAction np_decodeToAluFifo (@isFull core fetchCapacity AluInInstGroup ty) ;

        If (And [ ##fetchHead `? "Some" ; Not #decodeToAlu_isFull ]) Then (
          Let  fetchOut  : FetchOut  <- ##fetchHead `! "Some" ;
          LetL regReadIn : RegReadIn <- wrappedDecode fetchOut ;
          Let  decodeOut : DecodeOut <- ##regReadIn`"decodeOut" ;

          Let  cs1Idx    : Bit RegIdxSzReal      <- ##decodeOut`"cs1Idx" ;
          Let  cs2Source : TaggedUnion Cs2Source <- ##decodeOut`"cs2Idx" ;
          Let  cs2IsReg  : Bool                  <- #cs2Source `? "Reg" ;
          Let  cs2Idx    : Bit RegIdxSzReal      <- #cs2Source `! "Reg" ;
          Let  writesCd  : Bool                  <- ##decodeOut`"writesCd" ;
          Let  instBits  : Inst                  <- ##decodeOut`"instBits" ;
          Let  cdIdx     : Bit RegIdxSzReal      <- TruncLsb 1 RegIdxSzReal (getCd instBits) ;

          LetA cs1Wait   : Bool <- liftAction np_waitBits (@readWaitBit core ty #cs1Idx) ;
          LetA cs2Wait   : Bool <- liftAction np_waitBits (@readWaitBit core ty #cs2Idx) ;
          LetA cdWait    : Bool <- liftAction np_waitBits (@readWaitBit core ty #cdIdx) ;

          Let  cs1Stall  : Bool <- And [ isNotZero #cs1Idx ; #cs1Wait ] ;
          Let  cs2Stall  : Bool <- And [ #cs2IsReg ; isNotZero #cs2Idx ; #cs2Wait ] ;
          Let  cdStall   : Bool <- And [ #writesCd ; isNotZero #cdIdx ; #cdWait ] ;
          Let  canIssue  : Bool <- Not (Or [ #cs1Stall ; #cs2Stall ; #cdStall ]) ;

          If #canIssue Then (
            LetA meip : Bool <- liftAction np_mem (implPlicAction (@plicMeip core nIrq ty)) ;
            LetA mtip : Bool <- liftAction np_mem (implClintAction (readClintMtip core ty)) ;
            LetA aluInInstGroup : AluInInstGroup <- liftAction np_rf (regRead meip mtip regReadIn) ;

            Act (liftAction np_fetchOutFifo (@deq core fetchCapacity FetchOut ty)) ;
            Act (liftAction np_decodeToAluFifo (@enq core fetchCapacity AluInInstGroup ty aluInInstGroup)) ;
            If (And [ #writesCd ; isNotZero #cdIdx ]) Then (
              liftAction np_waitBits (@writeWaitBit core ty #cdIdx (ConstBool true))
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv.

      (* =====================================================================
       * STAGE 4: ALU Stage
       * ===================================================================== *)

      Definition aluStage : Action ty sysTree (Bit 0) :=
        LetA aluInHead        : Option AluInInstGroup <- liftAction np_decodeToAluFifo (@first core fetchCapacity AluInInstGroup ty) ;
        LetA aluToExec_isFull : Bool                  <- liftAction np_aluToExecFifo (@isFull core fetchCapacity AluOutUnion ty) ;

        If (And [ ##aluInHead `? "Some" ; Not #aluToExec_isFull ]) Then (
          Let  aluInInstGroup : AluInInstGroup <- ##aluInHead `! "Some" ;
          Let  instGroup      : InstGroup      <- ##aluInInstGroup`"instGroup" ;
          Let  instBits       : Inst           <- ##aluInInstGroup`"inst" ;
          LetL aluCtrl        : AluControl     <- decodeInstGroup instGroup ;
          Let  aluIn          : AluIn          <- STRUCT {
            "cs2Idx"              ::= ##aluInInstGroup`"cs2Idx" ;
            "writesCd"            ::= ##aluInInstGroup`"writesCd" ;
            "inst"                ::= #instBits ;
            "decodeExc"           ::= ##aluInInstGroup`"decodeExc" ;
            "fetchExc"            ::= ##aluInInstGroup`"fetchExc" ;
            "pcc"                 ::= ##aluInInstGroup`"pcc" ;
            "cs1"                 ::= ##aluInInstGroup`"cs1" ;
            "cs2"                 ::= ##aluInInstGroup`"cs2" ;
            "currInterruptStatus" ::= ##aluInInstGroup`"currInterruptStatus" ;
            "aluControl"          ::= #aluCtrl
          } ;
          LetL routingOut     : AluOut         <- AluRouting aluIn ;
          LetL aluOut         : AluOutUnion    <- Alu routingOut ;
          Let  rawDstIdx      : Bit RegIdxSz   <- ITE0 (##aluInInstGroup`"writesCd") (getCd instBits) ;
          Let  aluOutWithDst  : AluOutUnion    <- #aluOut `{ "dstIdx" <- #rawDstIdx } ;

          Act (liftAction np_decodeToAluFifo (@deq core fetchCapacity AluInInstGroup ty)) ;
          liftAction np_aluToExecFifo (@enq core fetchCapacity AluOutUnion ty aluOutWithDst)
        ) ;
        Retv.

      (* =====================================================================
       * STAGE 5: Execute Non-Deferred Stage
       * ===================================================================== *)

      Definition executeNonDeferredStage : Action ty sysTree (Bit 0) :=
        LetA execInHead        : Option AluOutUnion <- liftAction np_aluToExecFifo (@first core fetchCapacity AluOutUnion ty) ;
        LetA deferredIn_isFull : Bool               <- liftAction np_deferredInFifo (@isFull core deferredCapacity DeferredReq ty) ;

        If (And [ ##execInHead `? "Some" ; Not #deferredIn_isFull ]) Then (
          Let  aluOut : AluOutUnion <- ##execInHead `! "Some" ;
          LetA meip   : Bool        <- liftAction np_mem (implPlicAction (@plicMeip core nIrq ty)) ;
          LetA mtip   : Bool        <- liftAction np_mem (implClintAction (readClintMtip core ty)) ;

          LetA execOut : ExecuteOut <- liftAction np_rf (executeNonDeferred meip mtip aluOut) ;

          If (##execOut`"isFenceIRq") Then (
            Act (liftAction np_mem ((memIfc ty).(mem_fenceI_req))) ;
            Retv
          ) ;

          Act (liftAction np_aluToExecFifo (@deq core fetchCapacity AluOutUnion ty)) ;

          Let reqOpt      : Option DeferredReq <- ##execOut`"deferredReq" ;
          Let hasDeferred : Bool               <- #reqOpt `? "Some" ;
          Let dstIdxReal  : Bit RegIdxSzReal   <- TruncLsb 1 RegIdxSzReal (##aluOut`"dstIdx") ;
          Let clearPcc    : Bool               <- Not #hasDeferred ;
          Let clearDst    : Bool               <- And [ Not #hasDeferred ; isNotZero #dstIdxReal ] ;

          Act (liftAction np_waitBits (@clearWaitBits2 core ty ($0 : Expr ty (Bit RegIdxSzReal)) #clearPcc #dstIdxReal #clearDst)) ;

          If #hasDeferred Then (
            Let req : DeferredReq <- #reqOpt `! "Some" ;
            liftAction np_deferredInFifo (@enq core deferredCapacity DeferredReq ty req)
          ) ;
          Retv
        ) ;
        Retv.

      (* =====================================================================
       * STAGE 6: Execute Deferred Stages (Load / Store / Fence / MulDiv / Rev)
       * ===================================================================== *)

      Definition loadRqOrStoreOrFenceStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRqOrStoreOrFence core pcAddrInit tohostAddr fetchCapacity deferredCapacity memIfc ty).

      Definition dataCrossLineStage : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implMemStepSecondLine core regions ty).

      Definition loadRpAndWritebackOrEnqueueRevRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRpAndWritebackOrEnqueueRevRq core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition revRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@revRq core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition revRpAndWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@revRpAndWriteBack core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition mulStageActions : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_core act) (@mulStageRules core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition mulWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@mulWriteBack core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition divStageActions : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_core act) (@divStageRules core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

      Definition divWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@divWriteBack core pcAddrInit fetchCapacity deferredCapacity memIfc ty).

    End Ty.

    (* =======================================================================
     * Top-Level Implementation Module (impl)
     * ======================================================================= *)

    Definition impl : Mod sysTree :=
      fun ty => ([
        (core, fetchRqStage ty) ;
        (core, fetchCrossLineStage ty) ;
        (core, fetchRpStage ty) ;
        (core, decodeAndRegRead ty) ;
        (core, aluStage ty) ;
        (core, executeNonDeferredStage ty) ;
        (core, loadRqOrStoreOrFenceStage ty) ;
        (core, dataCrossLineStage ty) ;
        (core, loadRpAndWritebackOrEnqueueRevRqStage ty) ;
        (core, revRqStage ty) ;
        (core, revRpAndWriteBackStage ty)
      ] ++ map (fun a => (core, a)) (mulStageActions ty)
        ++ [ (core, mulWriteBackStage ty) ]
        ++ map (fun a => (core, a)) (divStageActions ty)
        ++ [ (core, divWriteBackStage ty) ;
             (core, implTickCycle ty) ;
             (core, implTickTimer ty) ;
             (core, implPlicClaimStep ty) ]
        ++ map (fun a => (core, a)) (implRevokerStepsSys ty)
        ++ map (fun a => (core, a)) (implPlicPendingsSteps ty))%list.

  End Impl.

End ImplDom.
