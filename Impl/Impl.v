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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic ImplRevoker ImplDevice ImplMulDiv ImplCommon ImplBranchPredictor ImplFetch ImplDecode ImplExecute ImplDeferred ShiftFifo.

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
  Variable fetchCapacity decodeCapacity deferredCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.

  Local Abbreviation rTree := (rfTree core pcAddrInit).
  Local Abbreviation fTree := (implFetchTree core pcAddrInit fetchCapacity).
  Local Abbreviation decTree := (implDecodeTree core decodeCapacity).
  Local Abbreviation eTree := (implExecuteTree core).
  Local Abbreviation dTree := (implDeferredTree core deferredCapacity mulStages divStages mulDivMode).

  Definition implSysTree (config : RevConfig) (regions : list (MemRegion core)) : Tree DomainElem :=
    Node "sys" [
      coreTree core rTree implBpTree (implMemTree regions) fTree decTree eTree dTree
    ].

  Section Impl.
    Variable config : RevConfig.
    Variable regions : list (MemRegion core).
    Variable clint : @ClintInstance core regions.
    Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
    Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

    Local Abbreviation bpTree := implBpTree.
    Local Abbreviation noInstIfc := (fun ty => @implNoInstIfc ty).
    Local Abbreviation withInstIfc := (fun ty => @implWithInstIfc noInstIfc ty).
    Local Abbreviation memTree := (implMemTree regions).
    Local Abbreviation memIfc := (fun ty => @implMemIfc core config regions ty rev).
    Local Abbreviation fetchIfc := (fun ty => @implFetchIfc core pcAddrInit fetchCapacity ty).
    Local Abbreviation decodeIfc := (fun ty => @implDecodeIfc core decodeCapacity ty).
    Local Abbreviation executeIfc := (fun ty => @implExecuteIfc core ty).
    Local Abbreviation deferredIfc := (fun ty => @implDeferredIfc core deferredCapacity mulStages divStages mulDivMode ty).
    Local Abbreviation sysTree := (implSysTree config regions).
    Local Abbreviation incrementMcycle := (incrementMcycle core pcAddrInit).

    Section Ty.
      Variable ty : Kind -> Type.

      Definition np_core : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core").

      Definition np_rf : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.rf.").

      Definition np_mem : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.mem.").

      (* =====================================================================
       * Peripheral Background Rules & Interrupt Polling on implMemTree
       * ===================================================================== *)

      Local Definition implClintAction {k : Kind} (act : Action ty (Node "clint" (clintChildren core)) k)
        : Action ty memTree k :=
        @implMemNthRegionAction core regions ty clint.(clintIdx) (@clintRegion core regions clint) clint.(pfClint) k act.

      Local Abbreviation nIrq := (S (S (length (collectIrqActions regions)))).

      Local Definition implPlicAction {k : Kind} (act : Action ty (plicTree core nIrq) k)
        : Action ty memTree k :=
        @implMemNthRegionAction core regions ty plic.(plicIdx) (@plicRegion core nIrq regions plic) plic.(pfPlic) k act.

      Definition implTickCycle : Action ty sysTree (Bit 0) :=
        liftAction np_rf incrementMcycle.

      Definition implTickTimer : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintTick core ty)).

      Definition implSampleMtipStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintSampleMtip core ty)).

      Definition implRevokerIdleStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerIdleStep core regions ty rev).

      Definition implRevokerCapRpRevBitRqStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerCapRpRevBitRqStep core config regions ty rev).

      Definition implRevokerRevBitRpWriteCapStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerRevBitRpWriteCapStep core config regions ty rev).

      Definition implRevokerStepsSys : list (Action ty sysTree (Bit 0)) :=
        [ implRevokerIdleStepSys ;
          implRevokerCapRpRevBitRqStepSys ;
          implRevokerRevBitRpWriteCapStepSys ].

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
                (implMemCollectIrqActions regions ty ++ [implPlicUartIrqAction])
                devPends
                devInsvs
          | _, _ => []
          end in
        map (fun act => liftAction np_mem act) memSteps.

      Definition implPlicSteps : list (Action ty sysTree (Bit 0)) :=
        implPlicPendingsSteps ++ [implPlicClaimStep ; implPlicSampleMeipStep].

      Definition implTimerSteps : list (Action ty sysTree (Bit 0)) :=
        [implTickCycle ; implTickTimer ; implSampleMtipStep].

      Definition implPeripheralSteps : list (Action ty sysTree (Bit 0)) :=
        implPlicSteps ++ implTimerSteps.

      (* =====================================================================
       * STAGE 1: Fetch Request
       * ===================================================================== *)

      Definition fetchRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@fetchRq core pcAddrInit fetchCapacity noInstIfc withInstIfc memIfc executeIfc decTree dTree ty).

      (* =====================================================================
       * STAGE 2: Fetch Assemble, Pre-Decode & Level-2 Branch Prediction
       * ===================================================================== *)

      Definition fetchAssembleStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@fetchAssemble core pcAddrInit fetchCapacity noInstIfc withInstIfc memIfc executeIfc decTree dTree ty).

      (* =====================================================================
       * STAGE 3: Decode & Register Read with Scoreboard
       * ===================================================================== *)

      Definition decodeAndRegReadStage : Action ty sysTree (Bit 0) :=
        liftAction np_core
          (@decodeAndRegRead core decodeCapacity pcAddrInit
                             bpTree fetchIfc executeIfc deferredIfc memIfc ty
                             (implPlicAction (@plicMeip core nIrq ty))
                             (implClintAction (readClintMtip core ty))).

      (* =====================================================================
       * STAGE 4: Combined ALU + Execute Non-Deferred Stage
       * ===================================================================== *)

      Definition aluAndExecuteNonDeferredStage : Action ty sysTree (Bit 0) :=
        liftAction np_core
          (@aluAndExecuteNonDeferred core pcAddrInit
                                     implNoInstTree withInstIfc memIfc
                                     fetchIfc decodeIfc deferredIfc ty
                                     (implPlicAction (@plicMeip core nIrq ty))
                                     (implClintAction (readClintMtip core ty))).

      (* =====================================================================
       * STAGE 5: Execute Deferred Stages (Load / Store / Fence / MulDiv / Rev)
       * ===================================================================== *)

      Definition loadRqOrStoreOrFenceStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRqOrStoreOrFence core deferredCapacity mulStages divStages mulDivMode pcAddrInit bpTree fTree decTree executeIfc memIfc ty).

      Definition loadRpAndWritebackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRpAndWriteback core deferredCapacity mulStages divStages mulDivMode pcAddrInit bpTree fTree decTree executeIfc memIfc ty config).

      Definition issueRevRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@issueRevRq core deferredCapacity mulStages divStages mulDivMode pcAddrInit bpTree fTree decTree executeIfc memIfc ty).

      Definition loadRpAndIssueRevRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRpAndIssueRevRq core deferredCapacity mulStages divStages mulDivMode pcAddrInit bpTree fTree decTree executeIfc memIfc ty config).

      Definition revRpAndWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@revRpAndWriteBack core deferredCapacity mulStages divStages mulDivMode pcAddrInit bpTree fTree decTree executeIfc memIfc ty).

      Definition mulDivStageActions : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_core act)
            (@mulDivRules core deferredCapacity mulStages divStages mulDivMode pcAddrInit bpTree fTree decTree executeIfc memIfc ty).

      Definition fetchRps : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectFetchRpActions regions ty).

      Definition fetchRqs : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectFetchRqActions regions ty).

      Definition dataReadRps : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectDataReadRpActions regions ty).

      Definition dataReadRqs : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectDataReadRqActions regions ty).

      Definition dataWriteRqs : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectDataWriteRqActions regions ty).

      Definition targetPortRqs : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectTargetPortRqActions regions ty).

      Definition targetPortRps : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectTargetPortRpActions regions ty).

      Definition dataCrossLineSteps : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectDataCrossLineActions regions ty).

      Definition fenceIAcks : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectFenceIAckActions regions ty).

    End Ty.

    (* =======================================================================
     * Top-Level Implementation Modules (singleCycleMod / pipelinedMod)
     * ======================================================================= *)

    Definition forwardDatapathList (ty : Kind -> Type) : list (string * Action ty sysTree (Bit 0)) :=
      map (fun a => (core, a)) (
        implPeripheralSteps ty
        ++ [ fetchRqStage ty ]
        ++ fetchRqs ty ++ fetchRps ty
        ++ [ fetchAssembleStage ty ;
             decodeAndRegReadStage ty ;
             aluAndExecuteNonDeferredStage ty ;
             loadRqOrStoreOrFenceStage ty ]
        ++ dataWriteRqs ty ++ dataReadRqs ty ++ dataReadRps ty
        ++ dataCrossLineSteps ty
        ++ dataWriteRqs ty ++ dataReadRqs ty ++ dataReadRps ty
        ++ [ loadRpAndIssueRevRqStage ty ]
        ++ dataReadRqs ty ++ dataReadRps ty
        ++ [ revRpAndWriteBackStage ty ]
        ++ mulDivStageActions ty
        ++ [ implRevokerIdleStepSys ty ]
        ++ dataReadRqs ty ++ dataReadRps ty
        ++ [ implRevokerCapRpRevBitRqStepSys ty ]
        ++ dataReadRqs ty ++ dataReadRps ty
        ++ [ implRevokerRevBitRpWriteCapStepSys ty ]
        ++ dataWriteRqs ty
        ++ fenceIAcks ty
        ++ targetPortRqs ty
        ++ dataWriteRqs ty ++ dataReadRqs ty ++ dataReadRps ty
        ++ targetPortRps ty)%list.

    Definition forwardDatapathMod : Mod sysTree :=
      fun ty => forwardDatapathList ty.

    Definition pipelinedList (ty : Kind -> Type) : list (string * Action ty sysTree (Bit 0)) :=
      map (fun a => (core, a)) (
        fetchRps ty ++ dataReadRps ty
        ++ targetPortRps ty
        ++ List.rev (
             [ fetchRqStage ty ;
               fetchAssembleStage ty ;
               decodeAndRegReadStage ty ;
               aluAndExecuteNonDeferredStage ty ;
               loadRqOrStoreOrFenceStage ty ]
             ++ dataCrossLineSteps ty
             ++ [ loadRpAndIssueRevRqStage ty ;
                  revRpAndWriteBackStage ty ]
             ++ mulDivStageActions ty
           )
        ++ List.rev (implPeripheralSteps ty)
        ++ List.rev (implRevokerStepsSys ty)
        ++ fenceIAcks ty
        ++ targetPortRqs ty
        ++ fetchRqs ty ++ dataReadRqs ty ++ dataWriteRqs ty)%list.

    Definition pipelinedMod : Mod sysTree :=
      fun ty => pipelinedList ty.

  End Impl.

End ImplDom.
