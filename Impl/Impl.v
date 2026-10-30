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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic ImplRevoker ImplDevice ImplMulDiv ImplCommon ImplBranchPredictor ImplFetch ImplDecode ImplExecute ImplDataMem ShiftFifo.

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
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.

  Local Abbreviation rTree := (rfTree core pcAddrInit).
  Local Abbreviation fTree := (implFetchTree core pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (implDecodeTree core decodeCapacity).
  Local Abbreviation eTree := (implExecuteTree core).
  Local Abbreviation dmTree := (implDataMemTree core dataMemCapacity).
  Local Abbreviation mdTree := (implMulDivTree core mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).

  Definition implSysTree (config : RevConfig) (regions : list MemRegion) : Tree DomainElem :=
    Node "sys" [
      coreTree core rTree implBpTree (implMemTree core regions) fTree decTree eTree dmTree mdTree
    ].

  Section Impl.
    Variable config : RevConfig.
    Variable regions : list MemRegion.
    Variable clint : @ClintInstance core regions.
    Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
    Variable plic : @PlicInstance core (S (S (length (collectIrqActions core regions)))) regions.

    Local Abbreviation bpTree := implBpTree.
    Local Abbreviation noInstIfc := (fun ty => @implNoInstIfc ty).
    Local Abbreviation withInstIfc := (fun ty => @implWithInstIfc noInstIfc ty).
    Local Abbreviation memTree := (implMemTree core regions).
    Local Abbreviation memIfc := (fun ty => @implMemIfc core config regions ty rev).
    Local Abbreviation fetchIfc := (fun ty => @implFetchIfc core pcAddrInit fetchCapacity instCapacity ty).
    Local Abbreviation decodeIfc := (fun ty => @implDecodeIfc core decodeCapacity ty).
    Local Abbreviation executeIfc := (fun ty => @implExecuteIfc core ty).
    Local Abbreviation dataMemIfc := (fun ty => @implDataMemIfc core dataMemCapacity ty).
    Local Abbreviation mulDivIfc := (fun ty => @implMulDivIfc core mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode ty).
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

      Definition np_fetch : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.fetch.").

      Definition np_decode : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.decode.").

      Definition np_execute : NodePath sysTree :=
        Eval cbn in (getNodePath sysTree "sys.core.execute.").

      (* =====================================================================
       * Peripheral Background Rules & Interrupt Polling on implMemTree
       * ===================================================================== *)

      Local Definition implClintAction {k : Kind} (act : Action ty (Node "clint" (clintChildren core)) k)
        : Action ty memTree k :=
        @implNthRegionAction core ty clint.(clintIdx) regions (clintRegion clint) clint.(pfClint) k act.

      Local Abbreviation nIrq := (S (S (length (collectIrqActions core regions)))).

      Local Definition implPlicAction {k : Kind} (act : Action ty (plicTree core nIrq) k)
        : Action ty memTree k :=
        @implNthRegionAction core ty plic.(plicIdx) regions (plicRegion plic) plic.(pfPlic) k act.

      Definition implTickCycle : Action ty sysTree (Bit 0) :=
        liftAction np_rf incrementMcycle.

      Definition implTickTimer : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintTick core ty)).

      Definition implSampleMtipStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implClintAction (clintSampleMtip core ty)).

      (* One rule per revoker phase (`implRevokerSteps`), in phase order *)
      Definition implRevokerStepsSys : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act) (@implRevokerSteps core config regions ty rev).

      Definition implRevokerIdleStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerIdleStep core regions ty rev).

      Definition implRevokerWaitCapRpStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerWaitCapRpStep core config regions ty rev).

      Definition implRevokerWaitRevBitRqStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerWaitRevBitRqStep core config regions ty rev).

      Definition implRevokerWaitRevBitRpStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerWaitRevBitRpStep core config regions ty rev).

      Definition implRevokerWriteCapStepSys : Action ty sysTree (Bit 0) :=
        liftAction np_mem (@implRevokerWriteCapStep core regions ty rev).

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
                (implMemCollectIrqActions core regions ty ++ [implPlicUartIrqAction])
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
        liftAction np_core (@fetchRq core pcAddrInit fetchCapacity instCapacity noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree ty).

      (* =====================================================================
       * STAGE 2: Fetch Assemble, Pre-Decode & Level-2 Branch Prediction
       * ===================================================================== *)

      Definition fetchAssembleStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@fetchAssemble core pcAddrInit fetchCapacity instCapacity noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree ty).

      Definition setFetchCanProceedStage : Action ty sysTree (Bit 0) :=
        liftAction np_fetch (@setFetchCanProceed core pcAddrInit fetchCapacity instCapacity ty).

      (* =====================================================================
       * STAGE 3: Decode & Register Read with Scoreboard
       * ===================================================================== *)

      Definition decodeAndRegReadStage : Action ty sysTree (Bit 0) :=
        liftAction np_core
          (@decodeAndRegRead core decodeCapacity pcAddrInit
                             bpTree mdTree fetchIfc executeIfc dataMemIfc memIfc ty).

      Definition setDecodeCanProceedStage : Action ty sysTree (Bit 0) :=
        liftAction np_decode (@setDecodeCanProceed core decodeCapacity ty).

      (* =====================================================================
       * STAGE 4: Combined ALU + Execute Non-Deferred Stage
       * ===================================================================== *)

      Definition aluAndExecuteNonDeferredStage : Action ty sysTree (Bit 0) :=
        liftAction np_core
          (@aluAndExecuteNonDeferred core pcAddrInit
                                     implNoInstTree withInstIfc memIfc
                                     fetchIfc decodeIfc dataMemIfc mulDivIfc ty
                                     (implPlicAction (@plicMeip core nIrq ty))
                                     (implClintAction (readClintMtip core ty))).

      Definition setExecuteCanProceedStage : Action ty sysTree (Bit 0) :=
        liftAction np_execute (@setExecuteCanProceed core ty).

      Definition setCanProceedSteps : list (Action ty sysTree (Bit 0)) :=
        [ setFetchCanProceedStage ;
          setDecodeCanProceedStage ;
          setExecuteCanProceedStage ].

      (* =====================================================================
       * STAGE 5: Execute DataMem Stages (Load / Store / Fence / Rev) & MulDiv
       * ===================================================================== *)

      Definition loadRqOrStoreOrFenceStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRqOrStoreOrFence core dataMemCapacity pcAddrInit bpTree fTree decTree mdTree executeIfc memIfc ty).

      Definition loadRpAndWritebackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRpAndWriteback core dataMemCapacity pcAddrInit bpTree fTree decTree mdTree executeIfc memIfc ty config).

      Definition issueRevRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@issueRevRq core dataMemCapacity pcAddrInit bpTree fTree decTree mdTree executeIfc memIfc ty).

      Definition loadRpAndIssueRevRqStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@loadRpAndIssueRevRq core dataMemCapacity pcAddrInit bpTree fTree decTree mdTree executeIfc memIfc ty config).

      Definition revRpAndWriteBackStage : Action ty sysTree (Bit 0) :=
        liftAction np_core (@revRpAndWriteBack core dataMemCapacity pcAddrInit bpTree fTree decTree mdTree executeIfc memIfc ty).

      Definition mulDivStageActions : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_core act)
            (@mulDivRules core mulCapacity divCapacity mulStages divStages mulDivMode pcAddrInit bpTree memTree fTree decTree eTree dmTree ty).

      Definition fetchLineRpPorts : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectFetchLineRpPorts core regions ty).

      Definition readRpPorts : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectLineReadRpPorts core regions ty).

      Definition readRpStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implMemReadRpStep core regions ty).

      Definition readRqPorts : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectLineReadRqPorts core regions ty).

      Definition readRqStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implMemReadRqStep core regions ty).

      Definition writeRqPorts : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectLineWriteRqPorts core regions ty).

      Definition writeRqStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (implMemWriteRqStep core regions ty).

      Definition fetchRps : list (Action ty sysTree (Bit 0)) :=
        fetchLineRpPorts.

      Definition dataReadRps : list (Action ty sysTree (Bit 0)) :=
        readRpPorts ++ [ readRpStep ].

      Definition dataReadRqs : list (Action ty sysTree (Bit 0)) :=
        readRqStep :: readRqPorts.

      Definition dataWriteRqs : list (Action ty sysTree (Bit 0)) :=
        writeRqStep :: writeRqPorts.

      Definition fenceIAcks : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act)
            (implMemCollectFenceIAckActions core regions ty).

    End Ty.

    (* =======================================================================
     * Top-Level Implementation Modules (singleCycleMod / pipelinedMod)
     * ======================================================================= *)

    Definition forwardDatapathList (ty : Kind -> Type) : list (string * Action ty sysTree (Bit 0)) :=
      map (fun a => (core, a)) (
        implPeripheralSteps ty
        ++ [ fetchRqStage ty ]
        ++ fetchLineRpPorts ty
        ++ [ fetchAssembleStage ty ;
             decodeAndRegReadStage ty ;
             aluAndExecuteNonDeferredStage ty ;
             loadRqOrStoreOrFenceStage ty ]
        ++ [ writeRqStep ty ] ++ writeRqPorts ty
        ++ [ writeRqStep ty ] ++ writeRqPorts ty
        ++ [ readRqStep ty ] ++ readRqPorts ty ++ readRpPorts ty ++ [ readRpStep ty ]
        ++ [ readRqStep ty ] ++ readRqPorts ty ++ readRpPorts ty ++ [ readRpStep ty ]
        ++ [ loadRpAndIssueRevRqStage ty ]
        ++ [ readRqStep ty ] ++ readRqPorts ty ++ readRpPorts ty ++ [ readRpStep ty ]
        ++ [ revRpAndWriteBackStage ty ]
        ++ mulDivStageActions ty
        ++ [ implRevokerIdleStepSys ty ]
        ++ [ readRqStep ty ] ++ readRqPorts ty ++ readRpPorts ty ++ [ readRpStep ty ]
        ++ [ implRevokerWaitCapRpStepSys ty ; implRevokerWaitRevBitRqStepSys ty ]
        ++ [ readRqStep ty ] ++ readRqPorts ty ++ readRpPorts ty ++ [ readRpStep ty ]
        ++ [ implRevokerWaitRevBitRpStepSys ty ; implRevokerWriteCapStepSys ty ]
        ++ [ writeRqStep ty ] ++ writeRqPorts ty
        ++ fenceIAcks ty
        ++ setCanProceedSteps ty)%list.

    Definition forwardDatapathMod : Mod sysTree :=
      fun ty => forwardDatapathList ty.

    Definition pipelinedList (ty : Kind -> Type) : list (string * Action ty sysTree (Bit 0)) :=
      map (fun a => (core, a)) (
        fetchLineRpPorts ty ++ readRpPorts ty ++ [ readRpStep ty ]
        ++ List.rev (
             [ fetchRqStage ty ]
             ++ repeat (fetchAssembleStage ty) issueWidth
             ++ repeat (decodeAndRegReadStage ty) issueWidth
             ++ repeat (aluAndExecuteNonDeferredStage ty) issueWidth
             ++ [ loadRqOrStoreOrFenceStage ty ;
                  loadRpAndIssueRevRqStage ty ;
                  revRpAndWriteBackStage ty ]
             ++ mulDivStageActions ty
           )
        ++ List.rev (implPeripheralSteps ty)
        ++ List.rev (implRevokerStepsSys ty)
        ++ fenceIAcks ty
        ++ [ readRqStep ty ; writeRqStep ty ]
        ++ readRqPorts ty ++ writeRqPorts ty
        ++ setCanProceedSteps ty)%list.

    Definition pipelinedMod : Mod sysTree :=
      fun ty => pipelinedList ty.

  End Impl.

End ImplDom.
