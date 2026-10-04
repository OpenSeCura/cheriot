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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic Fifo ImplRevoker ImplDevice ImplCommon ImplBranchPredictor ImplFetch ImplDecode ImplExecute ImplDeferred.

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
  Variable fetchCapacity decodeCapacity deferredCapacity : nat.

  Local Notation fTree := (fetchTree core pcAddrInit fetchCapacity).
  Local Notation decTree := (decodeTree core pcAddrInit decodeCapacity).
  Local Notation dTree := (deferredTree core deferredCapacity).

  Definition implSysTree (config : RevConfig) (regions : list MemRegion) : Tree DomainElem :=
    Node "sys" [
      coreTree core pcAddrInit implBpTree (implMemTree regions) fTree decTree dTree
    ].

  Section Impl.
    Variable config : RevConfig.
    Variable regions : list MemRegion.
    Variable clint : @ClintInstance core regions.
    Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
    Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

    Local Notation bpTree := implBpTree.
    Local Notation noInstIfc := (fun ty => @implNoInstIfc ty).
    Local Notation withInstIfc := (fun ty => @implWithInstIfc noInstIfc ty).
    Local Notation memTree := (implMemTree regions).
    Local Notation memIfc := (fun ty => @implMemIfc core config regions ty rev).
    Local Notation sysTree := (implSysTree config regions).
    Local Notation incrementMcycle := (incrementMcycle core pcAddrInit).

    Section Ty.
      Variable ty : Kind -> Type.

      Definition np_core : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core").

      Definition np_rf : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.rf").

      Definition np_mem : NodePath sysTree :=
        Eval cbn in (embedNodeIntoPath (getNodePath sysTree "sys.core.mem") singletonChildPath).

      (* =====================================================================
       * Peripheral Background Rules & Interrupt Polling on implMemTree
       * ===================================================================== *)

      Local Definition implClintAction {k : Kind} (act : Action ty (Node "clint" (clintChildren core)) k)
        : Action ty memTree k :=
        @implMemNthRegionAction regions ty clint.(clintIdx) (@clintRegion core regions clint) clint.(pfClint) k act.

      Local Notation nIrq := (S (S (length (collectIrqActions regions)))).

      Local Definition implPlicAction {k : Kind} (act : Action ty (plicTree core nIrq) k)
        : Action ty memTree k :=
        @implMemNthRegionAction regions ty plic.(plicIdx) (@plicRegion core nIrq regions plic) plic.(pfPlic) k act.

      Definition implTickCycle : Action ty sysTree (Bit 0) :=
        liftAction np_rf incrementMcycle.

      Definition implTickTimer : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintTick core ty)).

      Definition implSampleMtipStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintSampleMtip core ty)).

      Definition implRevokerStepsSys : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act) (@implRevokerSteps core config regions ty rev).

      Definition implPlicClaimStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implPlicAction (@updateClaim core nIrq ty)).

      Definition implPlicSampleMeipStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implPlicAction (@plicSampleMeip core nIrq ty)).

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
                (@implMemCollectIrqActions regions ty ++ [implPlicUartIrqAction])
                devPends
                devInsvs
          | _, _ => []
          end in
        map (fun act => liftAction np_mem act) memSteps.

      (* =====================================================================
       * STAGE 1: Fetch Request
       * ===================================================================== *)

      Definition fetchRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@fetchRq core pcAddrInit fetchCapacity noInstIfc implWithInstTree memIfc decTree dTree ty).

      (* =====================================================================
       * STAGE 2: Decode & Register Read with Two-Level Predictor & Scoreboard
       * ===================================================================== *)

      Definition decodeAndRegReadStage : Action ty sysTree (Bit 0) :=
        liftAction np_core
          (@decodeAndRegRead core pcAddrInit decodeCapacity fetchCapacity deferredCapacity
                             implNoInstTree withInstIfc memIfc ty
                             (implPlicAction (@plicMeip core nIrq ty))
                             (implClintAction (readClintMtip core ty))).

      (* =====================================================================
       * STAGE 3: Combined ALU + Execute Non-Deferred Stage
       * ===================================================================== *)

      Definition aluAndExecuteNonDeferredStage : Action ty sysTree (Bit 0) :=
        liftAction np_core
          (@aluAndExecuteNonDeferred core pcAddrInit fetchCapacity decodeCapacity deferredCapacity
                                     implNoInstTree withInstIfc memIfc ty
                                     (implPlicAction (@plicMeip core nIrq ty))
                                     (implClintAction (readClintMtip core ty))).

      (* =====================================================================
       * STAGE 4: Execute Deferred Stages (Load / Store / Fence / MulDiv / Rev)
       * ===================================================================== *)

      Definition loadRqOrStoreOrFenceStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRqOrStoreOrFence core deferredCapacity pcAddrInit tohostAddr bpTree fTree decTree memIfc ty).

      Definition loadRpAndWritebackOrIssueRevRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRpAndWritebackOrIssueRevRq core deferredCapacity pcAddrInit bpTree fTree decTree memIfc ty config).

      Definition revRpAndWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@revRpAndWriteBack core deferredCapacity pcAddrInit bpTree fTree decTree memIfc ty).

      Definition mulDivStageActions : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_core act) (@mulDivStageRules core deferredCapacity pcAddrInit bpTree fTree decTree memIfc ty).

      Definition mulWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@mulWriteBack core deferredCapacity pcAddrInit bpTree fTree decTree memIfc ty).

      Definition divWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@divWriteBack core deferredCapacity pcAddrInit bpTree fTree decTree memIfc ty).

      Definition implRegionStepsSys : list (string * Action ty sysTree (Bit 0)) :=
        map (fun '(dom, act) => (dom, liftAction np_mem act))
            (@implMemCollectRegionStepActions regions ty).

      Definition implClearWriteBusySteps : list (string * Action ty sysTree (Bit 0)) :=
        map (fun '(dom, act) => (dom, liftAction np_mem act))
            (@implMemCollectClearWriteBusyActions regions ty).

      Definition implInternalMemTargetPortSteps : list (string * Action ty sysTree (Bit 0)) :=
        map (fun '(dom, act) => (dom, liftAction np_mem act))
            (@implMemCollectTargetPortActions regions ty).

    End Ty.

    (* =======================================================================
     * Top-Level Implementation Module (impl)
     * ======================================================================= *)

    Definition impl : Mod sysTree :=
      fun ty => (
        implClearWriteBusySteps ty
        ++ map (fun a => (core, a)) (implRevokerStepsSys ty)
        ++ map (fun a => (core, a)) (implPlicPendingsSteps ty)
        ++ [ (core, implPlicClaimStep ty) ;
             (core, implPlicSampleMeipStep ty) ;
             (core, implTickCycle ty) ;
             (core, implTickTimer ty) ;
             (core, implSampleMtipStep ty) ;
             (core, fetchRqStage ty) ;
             (core, decodeAndRegReadStage ty) ;
             (core, aluAndExecuteNonDeferredStage ty) ;
             (core, loadRqOrStoreOrFenceStage ty) ]
        ++ implRegionStepsSys ty
        ++ [
          (core, loadRpAndWritebackOrIssueRevRqStage ty) ;
          (core, revRpAndWriteBackStage ty)
        ]
        ++ map (fun a => (core, a)) (mulDivStageActions ty)
        ++ [ (core, mulWriteBackStage ty) ;
             (core, divWriteBackStage ty) ]
        ++ implInternalMemTargetPortSteps ty)%list.

  End Impl.

End ImplDom.
