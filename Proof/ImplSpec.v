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

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Export SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Export Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Export TreeLemmas StateRel SimDevices SimFetchDecode SimExecute SimDataMem.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * ACTION MEMBERSHIP DECOMPOSITION FOR `pipelinedMod`
 * =========================================================================== *)

Section ModuleActionDecomposition.
  Variable pcAddrInit : Z.
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : @ClintInstance regions.
  Variable rev : @RevokerInstance implRevokerExtraChildren regions.
  Variable revSpec : @RevokerInstance [] regions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode bp config regions).

  Local Abbreviation pipeMod :=
    (@pipelinedMod pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
       config regions clint rev plic).

  (* --- 2A. Unfolding `pipelinedMod` --- *)

  Lemma map_snd_pipelinedMod :
    forall (ty : Kind -> Type),
      pipeMod ty =
      ([ @applyRedirectStage pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
           config regions rev ty ]
       ++ @fetchRps pcAddrInit fetchCapacity instCapacity decodeCapacity
          dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
          config regions ty
       ++ @dataReadRps pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
             config regions ty
       ++ List.rev (
            [ @fetchRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                 config regions rev ty ]
            ++ repeat (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                         config regions rev ty) issueWidth
            ++ repeat (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                         config regions rev ty) issueWidth
            ++ repeat (@aluAndExecuteNonDeferredStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                         config regions clint rev plic ty) issueWidth
            ++ [ @loadRqOrStoreOrFenceStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                    config regions rev ty ;
                 @loadRpAndWritebackStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                    config regions rev ty ;
                 @checkRevocationStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                    config regions rev ty ;
                 @issueRevRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                    config regions rev ty ;
                 @revRpAndWriteBackStage pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                    config regions rev ty ]
            ++ @mulDivStageActions pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                  config regions ty
          )
       ++ List.rev (@implPeripheralSteps pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                      config regions clint plic ty)
       ++ List.rev (@implRevokerStepsSys pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                      config regions rev ty)
       ++ @fenceIAcks pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
             config regions ty
       ++ [ @readRqStep pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
               config regions ty ;
            @writeRqStep pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
               config regions ty ]
       ++ @readRqPorts pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
             config regions ty
       ++ @writeRqPorts pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
             config regions ty
       ++ @setCanProceedSteps pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
             config regions rev ty)%list.
  Proof.
    intros ty; unfold pipelinedMod, pipelinedList.
    unfold fetchRps, dataReadRps.
    rewrite <- !app_assoc; reflexivity.
  Qed.

  (* --- 2B. Top-Level Action Classification (`ImplActionKind`) --- *)

  Inductive ImplActionKind (ty : Kind -> Type) (act : Action ty iTree (Bit 0)) : Prop :=
  | IA_Peripheral :
      In act (@implPeripheralSteps pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions clint plic ty) ->
      ImplActionKind ty act
  | IA_ApplyRedirect :
      act = @applyRedirectStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_FetchRqStage :
      act = @fetchRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_FetchRps :
      In act (@fetchRps pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions ty) ->
      ImplActionKind ty act
  | IA_FetchAssembleStage :
      act = @fetchAssembleStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_DecodeAndRegReadStage :
      act = @decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_AluAndExecuteStage :
      act = @aluAndExecuteNonDeferredStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions clint rev plic ty ->
      ImplActionKind ty act
  | IA_LoadRqOrStoreOrFenceStage :
      act = @loadRqOrStoreOrFenceStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_DataWriteRqs :
      In act (@dataWriteRqs pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions ty) ->
      ImplActionKind ty act
  | IA_DataReadRqs :
      In act (@dataReadRqs pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions ty) ->
      ImplActionKind ty act
  | IA_DataReadRps :
      In act (@dataReadRps pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions ty) ->
      ImplActionKind ty act
  | IA_LoadRpAndWritebackStage :
      act = @loadRpAndWritebackStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_CheckRevocationStage :
      act = @checkRevocationStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_IssueRevRqStage :
      act = @issueRevRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_RevRpAndWriteBackStage :
      act = @revRpAndWriteBackStage pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty ->
      ImplActionKind ty act
  | IA_MulDivStageActions :
      In act (@mulDivStageActions pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions ty) ->
      ImplActionKind ty act
  | IA_RevokerStepsSys :
      In act (@implRevokerStepsSys pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions rev ty) ->
      ImplActionKind ty act
  | IA_FenceIAcks :
      In act (@fenceIAcks pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions ty) ->
      ImplActionKind ty act
  | IA_SetCanProceedSteps :
      In act (@setCanProceedSteps pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions rev ty) ->
      ImplActionKind ty act.

  (* --- 2C. Sub-Group Decompositions (`implPeripheralSteps`, `implRevokerStepsSys`, `setCanProceedSteps`) --- *)

  Lemma In_implRevokerStepsSys_decomp :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (@implRevokerStepsSys pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                config regions rev ty) <->
      act = @implRevokerIdleStepSys pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty \/
      act = @implRevokerWaitCapRpStepSys pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty \/
      act = @implRevokerWaitRevBitRqStepSys pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty \/
      act = @implRevokerWaitRevBitRpStepSys pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty \/
      act = @implRevokerWriteCapStepSys pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
              config regions rev ty.
  Proof.
    intros ty act.
    unfold implRevokerStepsSys, implRevokerSteps, implRevokerIdleStepSys, implRevokerWaitCapRpStepSys,
      implRevokerWaitRevBitRqStepSys, implRevokerWaitRevBitRpStepSys, implRevokerWriteCapStepSys.
    cbn [map In]; intuition congruence.
  Qed.

  (* --- 2D. Membership Decomposition for `pipelinedMod` --- *)

  Lemma in_singleton_iff :
    forall (A : Type) (x y : A), In x [y] <-> x = y.
  Proof.
    intros A x y; cbn [In]; intuition congruence.
  Qed.

  Lemma in_two_iff :
    forall (A : Type) (x y1 y2 : A),
      In x [y1; y2] <-> x = y1 \/ x = y2.
  Proof.
    intros A x y1 y2; cbn [In]; intuition congruence.
  Qed.

  Lemma in_three_iff :
    forall (A : Type) (x y1 y2 y3 : A),
      In x [y1; y2; y3] <-> x = y1 \/ x = y2 \/ x = y3.
  Proof.
    intros A x y1 y2 y3; cbn [In]; intuition congruence.
  Qed.

  Lemma in_five_iff :
    forall (A : Type) (x y1 y2 y3 y4 y5 : A),
      In x [y1; y2; y3; y4; y5] <-> x = y1 \/ x = y2 \/ x = y3 \/ x = y4 \/ x = y5.
  Proof.
    intros A x y1 y2 y3 y4 y5; cbn [In]; intuition congruence.
  Qed.

  Theorem In_pipelinedMod_ImplActionKind :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (pipeMod ty) ->
      ImplActionKind ty act.
  Proof.
    intros ty act Hin.
    rewrite map_snd_pipelinedMod in Hin.
    rewrite !in_app_iff in Hin.
    repeat rewrite <- in_rev in Hin.
    rewrite !in_app_iff, ?in_five_iff, ?in_three_iff, ?in_two_iff, ?in_singleton_iff in Hin.
    repeat lazymatch type of Hin with
    | _ \/ _ => destruct Hin as [Hin | Hin]
    end;
      try (apply repeat_spec in Hin);
      try (apply IA_ApplyRedirect; exact Hin);
      try (apply IA_FetchRqStage; exact Hin);
      try (apply IA_FetchAssembleStage; exact Hin);
      try (apply IA_DecodeAndRegReadStage; exact Hin);
      try (apply IA_AluAndExecuteStage; exact Hin);
      try (apply IA_LoadRqOrStoreOrFenceStage; exact Hin);
      try (apply IA_LoadRpAndWritebackStage; exact Hin);
      try (apply IA_CheckRevocationStage; exact Hin);
      try (apply IA_IssueRevRqStage; exact Hin);
      try (apply IA_RevRpAndWriteBackStage; exact Hin);
      try (apply IA_Peripheral; exact Hin);
      try (apply IA_FetchRps; exact Hin);
      try (apply IA_DataWriteRqs; left; exact (eq_sym Hin));
      try (apply IA_DataWriteRqs; right; exact Hin);
      try (apply IA_DataReadRqs; left; exact (eq_sym Hin));
      try (apply IA_DataReadRqs; right; exact Hin);
      try (apply IA_DataReadRps; exact Hin);
      try (apply IA_MulDivStageActions; exact Hin);
      try (apply IA_RevokerStepsSys; exact Hin);
      try (apply IA_FenceIAcks; exact Hin);
      try (apply IA_SetCanProceedSteps; exact Hin).
  Qed.

End ModuleActionDecomposition.
