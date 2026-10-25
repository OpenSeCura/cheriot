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
 * 1. INITIAL STATE CONSISTENCY PRESERVATION UNDER `TreeContentRel` & `stateRel`
 * =========================================================================== *)

Section InitStateRelLemmas.

  Theorem stateRel_InitStateConsistent :
    forall (core : string) (pcAddrInit : Z)
           (fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat)
           (mulCapacity divCapacity mulStages divStages : nat)
           (mulDivMode : MulDivMode)
           (config : RevConfig) (regions : list (MemRegion core))
           (s1 : ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
                           dataMemCapacity mulCapacity divCapacity mulStages divStages
                           mulDivMode config regions)
           (s2 : SpecState core pcAddrInit regions),
      InitStateConsistent
        (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions) s1 ->
      stateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s2 ->
      InitStateConsistent (SpecTree core pcAddrInit regions) s2.
  Proof.
    intros core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode config regions
           s1 s2 Hinit1 Hrel.
    pose proof (InitStateConsistent_impl_rf core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 Hinit1) as Hrf1.
    pose proof (InitStateConsistent_impl_mem core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 Hinit1) as Hmem1.
    pose proof (InitStateConsistent_impl_dataMem core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 Hinit1) as Hdm1.
    pose proof (InitStateConsistent_DataMemEmpty core dataMemCapacity
                  (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                dataMemCapacity mulCapacity divCapacity mulStages divStages
                                mulDivMode config regions s1) Hdm1) as Hemp.
    pose proof (stateRel_dataMemEmpty_rf core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s2 Hinit1 Hrel Hemp) as Hrf_eq.
    pose proof (InitStateConsistent_flushMulDiv core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 Hinit1) as Hflush.
    pose proof (InitStateConsistent_projImplMemSpecState core regions
                  (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                            dataMemCapacity mulCapacity divCapacity mulStages divStages
                            mulDivMode config regions s1) Hmem1) as Hmem1_proj.
    pose proof (sr_mem_rel core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s2 Hrel Hinit1) as HmemRel.
    pose proof (TreeContentRel_InitStateConsistent
                  (SpecMemSubTree core regions)
                  (StateRel.projImplMemSpecState core regions
                     (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                               dataMemCapacity mulCapacity divCapacity mulStages divStages
                               mulDivMode config regions s1))
                  (spec_mem core pcAddrInit regions s2)
                  Hmem1_proj HmemRel) as Hmem2.
    assert (Hrf2 : InitStateConsistent (RfTree core pcAddrInit) (spec_rf core pcAddrInit regions s2))
      by (rewrite Hrf_eq, Hflush; exact Hrf1).
    exact (conj (conj (conj Hrf2 I) (conj (conj Hmem2 I) I)) I).
  Qed.

  Theorem exists_initStateRel :
    forall (core : string) (pcAddrInit : Z)
           (fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat)
           (mulCapacity divCapacity mulStages divStages : nat)
           (mulDivMode : MulDivMode)
           (config : RevConfig) (regions : list (MemRegion core))
           (s1 : ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
                           dataMemCapacity mulCapacity divCapacity mulStages divStages
                           mulDivMode config regions),
      InitStateConsistent
        (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions) s1 ->
      exists s2 : SpecState core pcAddrInit regions,
        InitStateConsistent (SpecTree core pcAddrInit regions) s2 /\
        stateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2.
  Proof.
    intros core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode config regions s1 Hinit1.
    exists (InitState (SpecTree core pcAddrInit regions)).
    pose proof (InitStateConsistentPf (SpecTree core pcAddrInit regions)) as Hinit2.
    split.
    - exact Hinit2.
    - exact (initStateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 _ Hinit1 Hinit2).
  Qed.

End InitStateRelLemmas.

(* ===========================================================================
 * 2. ACTION MEMBERSHIP DECOMPOSITION FOR `forwardDatapathMod` AND `pipelinedMod`
 * =========================================================================== *)

Section ModuleActionDecomposition.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree core pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).

  Local Abbreviation fwdMod :=
    (@forwardDatapathMod core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
       config regions clint rev plic).

  Local Abbreviation pipeMod :=
    (@pipelinedMod core pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
       config regions clint rev plic).

  (* --- 2A. Unfolding `map snd` of `forwardDatapathMod` and `pipelinedMod` --- *)

  Lemma map_snd_forwardDatapathMod :
    forall (ty : Kind -> Type),
      map snd (fwdMod ty) =
      (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
          dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
          config regions clint plic ty
       ++ [ @fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ [ @fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ;
            @decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ;
            @aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions clint rev plic ty ;
            @loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ [ @loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ [ @revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ [ @implRevokerIdleStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ [ @implRevokerCapRpRevBitRqStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ [ @implRevokerRevBitRpWriteCapStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
               config regions rev ty ]
       ++ @dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty)%list.
  Proof.
    intros ty; unfold forwardDatapathMod, forwardDatapathList.
    rewrite map_map; cbn [snd]; apply map_id.
  Qed.

  Lemma map_snd_pipelinedMod :
    forall (ty : Kind -> Type),
      map snd (pipeMod ty) =
      (@fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
          dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
          config regions ty
       ++ @dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ List.rev (
            [ @fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                 config regions rev ty ]
            ++ repeat (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                         config regions rev ty) issueWidth
            ++ repeat (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                         config regions rev ty) issueWidth
            ++ repeat (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                         config regions clint rev plic ty) issueWidth
            ++ [ @loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config regions rev ty ]
            ++ @dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions ty
            ++ [ @loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config regions rev ty ;
                 @revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config regions rev ty ]
            ++ @mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions ty
          )
       ++ List.rev (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                      config regions clint plic ty)
       ++ List.rev (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                      config regions rev ty)
       ++ @fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty
       ++ @setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
             config regions ty)%list.
  Proof.
    intros ty; unfold pipelinedMod, pipelinedList.
    rewrite map_map; cbn [snd]; apply map_id.
  Qed.

  (* --- 2B. Stage and Device Action Group Classification (`ImplActionKind`) --- *)

  Inductive ImplActionKind (ty : Kind -> Type) (act : Action ty iTree (Bit 0)) : Prop :=
  | IA_Peripheral :
      In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions clint plic ty) ->
      ImplActionKind ty act
  | IA_FetchRqStage :
      act = @fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty ->
      ImplActionKind ty act
  | IA_FetchRqs :
      In act (@fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_FetchRps :
      In act (@fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_FetchAssembleStage :
      act = @fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty ->
      ImplActionKind ty act
  | IA_DecodeAndRegReadStage :
      act = @decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty ->
      ImplActionKind ty act
  | IA_AluAndExecuteStage :
      act = @aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions clint rev plic ty ->
      ImplActionKind ty act
  | IA_LoadRqOrStoreOrFenceStage :
      act = @loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty ->
      ImplActionKind ty act
  | IA_DataWriteRqs :
      In act (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_DataReadRqs :
      In act (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_DataReadRps :
      In act (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_DataCrossLineSteps :
      In act (@dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_LoadRpAndIssueRevRqStage :
      act = @loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty ->
      ImplActionKind ty act
  | IA_RevRpAndWriteBackStage :
      act = @revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty ->
      ImplActionKind ty act
  | IA_MulDivStageActions :
      In act (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_RevokerStepsSys :
      In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions rev ty) ->
      ImplActionKind ty act
  | IA_FenceIAcks :
      In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_TargetPortRqs :
      In act (@targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_TargetPortRps :
      In act (@targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act
  | IA_SetCanProceedSteps :
      In act (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) ->
      ImplActionKind ty act.

  (* --- 2C. Sub-Group Decompositions (`implPeripheralSteps`, `implRevokerStepsSys`, `setCanProceedSteps`) --- *)

  Lemma In_implPeripheralSteps_decomp :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions clint plic ty) <->
      In act (@implPlicPendingsSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions plic ty) \/
      act = @implPlicClaimStep core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions plic ty \/
      act = @implPlicSampleMeipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions plic ty \/
      act = @implTickCycle core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions ty \/
      act = @implTickTimer core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions clint ty \/
      act = @implSampleMtipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions clint ty.
  Proof.
    intros ty act.
    unfold implPeripheralSteps, implPlicSteps, implTimerSteps.
    rewrite !in_app_iff; cbn [In].
    intuition congruence.
  Qed.

  Lemma In_implRevokerStepsSys_decomp :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions rev ty) <->
      act = @implRevokerIdleStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @implRevokerCapRpRevBitRqStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @implRevokerRevBitRpWriteCapStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty.
  Proof.
    intros ty act; unfold implRevokerStepsSys; cbn [In]; intuition congruence.
  Qed.

  Lemma In_setCanProceedSteps_decomp :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) <->
      act = @setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions ty \/
      act = @setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions ty \/
      act = @setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions ty.
  Proof.
    intros ty act; unfold setCanProceedSteps; cbn [In]; intuition congruence.
  Qed.

  (* --- 2D. Membership Decomposition for `forwardDatapathMod` and `pipelinedMod` --- *)

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

  Lemma in_four_iff :
    forall (A : Type) (x y1 y2 y3 y4 : A),
      In x [y1; y2; y3; y4] <-> x = y1 \/ x = y2 \/ x = y3 \/ x = y4.
  Proof.
    intros A x y1 y2 y3 y4; cbn [In]; intuition congruence.
  Qed.

  Ltac solve_in_or H :=
    lazymatch type of H with
    | _ \/ _ => destruct H as [H | H]; solve_in_or H
    | ?P =>
        let rec find_or :=
          lazymatch goal with
          | |- P => exact H
          | |- _ \/ _ => first [left; find_or | right; find_or]
          end
        in find_or
    end.

  Theorem In_forwardDatapathMod_ImplActionKind :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (map snd (fwdMod ty)) <->
      ImplActionKind ty act.
  Proof.
    intros ty act.
    rewrite map_snd_forwardDatapathMod.
    rewrite !in_app_iff, !in_four_iff, !in_singleton_iff.
    split.
    - intros H.
      repeat lazymatch type of H with
      | _ \/ _ => destruct H as [H | H]
      end;
        try (apply IA_FetchRqStage; exact H);
        try (apply IA_FetchAssembleStage; exact H);
        try (apply IA_DecodeAndRegReadStage; exact H);
        try (apply IA_AluAndExecuteStage; exact H);
        try (apply IA_LoadRqOrStoreOrFenceStage; exact H);
        try (apply IA_LoadRpAndIssueRevRqStage; exact H);
        try (apply IA_RevRpAndWriteBackStage; exact H);
        try (apply IA_Peripheral; exact H);
        try (apply IA_FetchRqs; exact H);
        try (apply IA_FetchRps; exact H);
        try (apply IA_DataWriteRqs; exact H);
        try (apply IA_DataReadRqs; exact H);
        try (apply IA_DataReadRps; exact H);
        try (apply IA_DataCrossLineSteps; exact H);
        try (apply IA_MulDivStageActions; exact H);
        try (apply IA_FenceIAcks; exact H);
        try (apply IA_TargetPortRqs; exact H);
        try (apply IA_TargetPortRps; exact H);
        try (apply IA_SetCanProceedSteps; exact H);
        try (apply IA_RevokerStepsSys; unfold implRevokerStepsSys; rewrite in_three_iff; solve_in_or H).
    - intros H; destruct H as
        [H | H | H | H | H | H | H | H | H | H | H | H | H | H | H | H | H | H | H | H];
        try (unfold implRevokerStepsSys in H; rewrite in_three_iff in H);
        solve_in_or H.
  Qed.

  Theorem In_pipelinedMod_ImplActionKind :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (map snd (pipeMod ty)) ->
      ImplActionKind ty act.
  Proof.
    intros ty act Hin.
    rewrite map_snd_pipelinedMod in Hin.
    rewrite !in_app_iff in Hin.
    repeat rewrite <- in_rev in Hin.
    rewrite !in_app_iff, !in_two_iff, !in_singleton_iff in Hin.
    repeat lazymatch type of Hin with
    | _ \/ _ => destruct Hin as [Hin | Hin]
    end;
      try (apply repeat_spec in Hin);
      try (apply IA_FetchRqStage; exact Hin);
      try (apply IA_FetchAssembleStage; exact Hin);
      try (apply IA_DecodeAndRegReadStage; exact Hin);
      try (apply IA_AluAndExecuteStage; exact Hin);
      try (apply IA_LoadRqOrStoreOrFenceStage; exact Hin);
      try (apply IA_LoadRpAndIssueRevRqStage; exact Hin);
      try (apply IA_RevRpAndWriteBackStage; exact Hin);
      try (apply IA_Peripheral; exact Hin);
      try (apply IA_FetchRqs; exact Hin);
      try (apply IA_FetchRps; exact Hin);
      try (apply IA_DataWriteRqs; exact Hin);
      try (apply IA_DataReadRqs; exact Hin);
      try (apply IA_DataReadRps; exact Hin);
      try (apply IA_DataCrossLineSteps; exact Hin);
      try (apply IA_MulDivStageActions; exact Hin);
      try (apply IA_RevokerStepsSys; exact Hin);
      try (apply IA_FenceIAcks; exact Hin);
      try (apply IA_TargetPortRqs; exact Hin);
      try (apply IA_TargetPortRps; exact Hin);
      try (apply IA_SetCanProceedSteps; exact Hin).
  Qed.

  Corollary In_pipelinedMod_In_forwardDatapathMod :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (map snd (pipeMod ty)) ->
      In act (map snd (fwdMod ty)).
  Proof.
    intros ty act Hin.
    apply In_forwardDatapathMod_ImplActionKind.
    exact (In_pipelinedMod_ImplActionKind ty act Hin).
  Qed.

  Theorem pipelinedMod_simulates_forwardDatapathMod :
    forall (env1 env2 : Env iTree)
           (env2Exists : EnvInhabited env2)
           (envConsistent : EnvConsistent env1 env2 (fun s1 s2 => s1 = s2)),
      ModSimulation env1 env2 pipeMod fwdMod (fun s1 s2 => s1 = s2) env2Exists envConsistent.
  Proof.
    intros env1 env2 env2Exists envConsistent.
    apply SubsetActionModSimulation.
    exact In_pipelinedMod_In_forwardDatapathMod.
  Qed.

  Theorem In_forwardDatapathMod_decomp :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (map snd (fwdMod ty)) ->
      In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions clint plic ty) \/
      act = @fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      In act (@fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      act = @fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions clint rev plic ty \/
      act = @loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      In act (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      act = @loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      In act (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions rev ty) \/
      In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty).
  Proof.
    intros ty act Hin.
    apply In_forwardDatapathMod_ImplActionKind in Hin.
    destruct Hin as
      [Hin | Hin | Hin | Hin | Hin | Hin | Hin | Hin | Hin | Hin |
       Hin | Hin | Hin | Hin | Hin | Hin | Hin | Hin | Hin | Hin];
      solve_in_or Hin.
  Qed.

  Theorem In_pipelinedMod_decomp :
    forall (ty : Kind -> Type) (act : Action ty iTree (Bit 0)),
      In act (map snd (pipeMod ty)) ->
      In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions clint plic ty) \/
      act = @fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      In act (@fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      act = @fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions clint rev plic ty \/
      act = @loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      In act (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      act = @loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      act = @revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions rev ty \/
      In act (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions rev ty) \/
      In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty) \/
      In act (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions ty).
  Proof.
    intros ty act Hin.
    apply In_forwardDatapathMod_decomp.
    exact (In_pipelinedMod_In_forwardDatapathMod ty act Hin).
  Qed.

End ModuleActionDecomposition.

(* ===========================================================================
 * 3. STAGE & DEVICE SIMULATION CONNECTIONS AND TOP-LEVEL `ModSimulation`
 * =========================================================================== *)

Section SystemModSimulation.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree core pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation SState := (SpecState core pcAddrInit regions).
  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
  Local Abbreviation specMod := (@spec core pcAddrInit config regions clint revSpec plic).
  Local Abbreviation fwdMod :=
    (@forwardDatapathMod core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
       config regions clint rev plic).
  Local Abbreviation pipeMod :=
    (@pipelinedMod core pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
       config regions clint rev plic).
  Local Abbreviation cRel :=
    (CoreStateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions).
  Local Abbreviation sRel :=
    (stateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).

  (* --- 3A. Unconditional `setCanProceedSteps` Simulation --- *)

  Theorem sim_setFetchCanProceedStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setFetchCanProceedStage_inv core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s1' v Hsem)
      as [_ [_ [Hrf [_ [_ [Hmem [Hdecode [Hexec [Hdm [Hmd [_ [_ [_ [_ [_ HrestFetch]]]]]]]]]]]]]]].
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [Hghost HmemRel [Hquiescent Hcons]].
      unfold implRf, implMem, implDecode, implExecute, implDataMem, implMulDiv, implFetch in
        Hrf, Hmem, Hdecode, Hexec, Hdm, Hmd, HrestFetch.
      constructor.
      + unfold flushMulDiv, impl_rf, impl_dataMem, impl_mulDiv, impl_core in *.
        rewrite Hdm, Hrf, Hmd; exact Hghost.
      + unfold impl_mem, impl_core in *; rewrite Hmem; exact HmemRel.
      + split.
        * unfold FenceIPipelineQuiescent, FenceIActive, fetch_instFifo,
                 impl_execute, impl_dataMem, impl_mem, impl_decode, impl_fetch, impl_core in *.
          rewrite Hexec, Hdm, Hmem, Hdecode, HrestFetch.
          exact Hquiescent.
        * unfold impl_mem, impl_core in *; rewrite Hmem; exact Hcons.
  Qed.

  Theorem sim_setDecodeCanProceedStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setDecodeCanProceedStage_inv core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s1' v Hsem)
      as [_ [_ [Hrf [_ [_ [Hmem [Hfetch [Hexec [Hdm [Hmd [_ HrestDec]]]]]]]]]]].
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [Hghost HmemRel [Hquiescent Hcons]].
      unfold implRf, implMem, implFetch, implExecute, implDataMem, implMulDiv, implDecode in
        Hrf, Hmem, Hfetch, Hexec, Hdm, Hmd, HrestDec.
      constructor.
      + unfold flushMulDiv, impl_rf, impl_dataMem, impl_mulDiv, impl_core in *.
        rewrite Hdm, Hrf, Hmd; exact Hghost.
      + unfold impl_mem, impl_core in *; rewrite Hmem; exact HmemRel.
      + split.
        * unfold FenceIPipelineQuiescent, FenceIActive, decode_toAluFifo,
                 impl_execute, impl_dataMem, impl_mem, impl_fetch, impl_decode, impl_core in *.
          rewrite Hexec, Hdm, Hmem, Hfetch, HrestDec.
          exact Hquiescent.
        * unfold impl_mem, impl_core in *; rewrite Hmem; exact Hcons.
  Qed.

  Theorem sim_setFetchCanProceedStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_setDecodeCanProceedStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_setCanProceedSteps_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin Hsem Hrel.
    apply In_setCanProceedSteps_decomp in Hin as [-> | [-> | ->]].
    - exact (sim_setFetchCanProceedStage_stateRel s1 s1' s2 v Hsem Hrel).
    - exact (sim_setDecodeCanProceedStage_stateRel s1 s1' s2 v Hsem Hrel).
    - exact (sim_setExecuteCanProceedStage_stateRel core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions clint revSpec plic s1 s1' s2 v Hsem Hrel).
  Qed.

  (* --- 3B. `evalIncrementMcycle` Commutation with `flushMulDivCaps` --- *)

  Local Strategy opaque [evalWriteRegsList gprPathsWithKind].

  Lemma evalIncrementMcycle_writeGprVal_comm :
    forall (idx : bits RegIdxSzReal) (val : type FullECapWithTag)
           (rf : RfState core pcAddrInit),
      evalIncrementMcycle core pcAddrInit (writeGprVal core pcAddrInit idx val rf) =
      writeGprVal core pcAddrInit idx val (evalIncrementMcycle core pcAddrInit rf).
  Proof.
    intros idx val rf; unfold writeGprVal.
    destruct (negb (Zmod.eqb idx Zmod.zero)); [| reflexivity].
    exact (evalIncrementMcycle_updGpr_comm core pcAddrInit idx val rf).
  Qed.

  Theorem evalIncrementMcycle_flushMulDivCaps_comm :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           (rf : RfState core pcAddrInit),
      evalIncrementMcycle core pcAddrInit (flushMulDivCaps core pcAddrInit entries rf) =
      flushMulDivCaps core pcAddrInit entries (evalIncrementMcycle core pcAddrInit rf).
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH, evalIncrementMcycle_writeGprVal_comm; reflexivity.
  Qed.

  (* --- 3C. Peripheral, Fence.I Ack, and TargetPort Connections to `cRel` --- *)

  Lemma SimDevices_projImplMemSpecState_eq :
    forall (rs : list (MemRegion core))
           (m : TreeState DomainElemState (@implMemTree core rs)),
      SimDevices.projImplMemSpecState core rs m =
      StateRel.projImplMemSpecState core rs m.
  Proof.
    induction rs as [| r rs IH]; intros m; [reflexivity |].
    cbn [SimDevices.projImplMemSpecState StateRel.projImplMemSpecState].
    rewrite IH; reflexivity.
  Qed.

  Lemma stateRel_of_mem_lockstep :
    forall {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      cRel s1 s2 ->
      SemActions env2 (map snd (specMod type)) s2 s2' ->
      s1' = writeSubTreeState
              (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions)
              s1
              (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1') ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env2 s1 s1' s2 s2' Hrel Hacts Hs1' Hfence'.
    exists s2'; split; [exact Hacts |].
    destruct Hrel as [Hghost _ _].
    pose proof (impl_write_np_mem_accessors core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1
                  (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
      as [Hrf1 [_ [_ [_ [_ [_ [_ [Hdm1 Hmd1]]]]]]]].
    pose proof (spec_write_np_mem_accessors core pcAddrInit regions s2
                  (SimDevices.projImplMemSpecState core regions
                     (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1')))
      as [Hrf2 Hmem2].
    assert (Hrf2' : spec_rf core pcAddrInit regions s2' = spec_rf core pcAddrInit regions s2)
      by exact Hrf2.
    assert (Hmem2' : spec_mem core pcAddrInit regions s2' =
                     SimDevices.projImplMemSpecState core regions
                       (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                          dataMemCapacity mulCapacity divCapacity mulStages divStages
                          mulDivMode config regions s1'))
      by exact Hmem2.
    assert (Hrf1' : impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hrf1).
    assert (Hdm1' : impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hdm1).
    assert (Hmd1' : impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hmd1).
    constructor.
    - unfold flushMulDiv in *.
      rewrite Hdm1', Hrf1', Hmd1', Hrf2'; exact Hghost.
    - apply TreeContentRel_refl.
    - exact Hfence'.
  Qed.

  Lemma regionsFenceIMsgConservation_refl :
    forall (rs : list (MemRegion core))
           (sm : TreeState DomainElemState (specMemTree rs)),
      regionsFenceIMsgConservation core rs sm sm.
  Proof.
    induction rs as [| r rest IH]; intros sm; cbn [regionsFenceIMsgConservation].
    - exact I.
    - destruct sm as [sr [srest []]]; cbn [Fst Snd].
      split; [| apply IH].
      unfold memRegionTree in sr.
      revert sr.
      destruct (r.(regionKind)) as [isAcc initD initT | | children rdAct wrAct irqAct fiAct];
        unfold externalMemRegionTree, externalMemRegionChildren, customMemRegionTree, customMemChildren.
      + intros _; exact I.
      + destruct (hasFenceIPort (hasExtraFetchPort r)); intros sr; [| exact I].
        intros _; split; reflexivity.
      + intros _; exact I.
  Qed.

  Lemma stateRel_of_mem_lockstep_noNewFenceI :
    forall {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      cRel s1 s2 ->
      SemActions env2 (map snd (specMod type)) s2 s2' ->
      s1' = writeSubTreeState
              (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions)
              s1
              (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1') ->
      (anyRegionFenceIWait core regions
         (StateRel.projImplMemSpecState core regions
            (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1')) = true ->
       anyRegionFenceIWait core regions
         (StateRel.projImplMemSpecState core regions
            (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1)) = true) ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env2 s1 s1' s2 s2' Hrel Hacts Hs1' Hwait.
    apply (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1').
    destruct Hrel as [_ _ [Hquiescent _]].
    pose proof (impl_write_np_mem_accessors core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1
                  (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
      as [_ [_ [_ [_ [Hfetch1 [Hdec1 [Hexec1 [Hdm1 _]]]]]]]].
    pose proof (spec_write_np_mem_accessors core pcAddrInit regions s2
                  (SimDevices.projImplMemSpecState core regions
                     (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1')))
      as [_ Hmem2].
    assert (Hfetch1' : impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1' =
                       impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hfetch1).
    assert (Hdec1' : impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1' =
                     impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hdec1).
    assert (Hexec1' : impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1' =
                      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hexec1).
    assert (Hdm1' : impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hdm1).
    split.
    - unfold FenceIPipelineQuiescent, FenceIActive in *.
      rewrite Hexec1', Hfetch1', Hdec1', Hdm1'.
      intros Hfi'.
      apply Hquiescent.
      destruct Hfi' as [Hfip | [Hdmq | Hw]]; [left; exact Hfip | right; left; exact Hdmq | right; right; exact (Hwait Hw)].
    - change (spec_mem core pcAddrInit regions
                (writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1'))))
        with (SimDevices.projImplMemSpecState core regions
                (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1')).
      apply regionsFenceIMsgConservation_refl.
  Qed.

  Lemma stateRel_of_mem_stutter_preserves_spec :
    forall {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState),
      cRel s1 s2 ->
      s1' = writeSubTreeState
              (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions)
              s1
              (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1') ->
      StateRel.projImplMemSpecState core regions
        (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions s1') =
      StateRel.projImplMemSpecState core regions
        (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions s1) ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env2 s1 s1' s2 Hrel Hs1' Hproj.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - destruct Hrel as [Hghost HmemRel [Hquiescent Hcons]].
      pose proof (impl_write_np_mem_accessors core pcAddrInit fetchCapacity instCapacity
                    decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1
                    (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1'))
        as [Hrf1 [_ [_ [_ [Hfetch1 [Hdec1 [Hexec1 [Hdm1 Hmd1]]]]]]]].
      assert (Hrf1' : impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1' =
                      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)
        by (rewrite Hs1' at 1; exact Hrf1).
      assert (Hfetch1' : impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                           dataMemCapacity mulCapacity divCapacity mulStages divStages
                           mulDivMode config regions s1' =
                         impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                           dataMemCapacity mulCapacity divCapacity mulStages divStages
                           mulDivMode config regions s1)
        by (rewrite Hs1' at 1; exact Hfetch1).
      assert (Hdec1' : impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1' =
                       impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1)
        by (rewrite Hs1' at 1; exact Hdec1).
      assert (Hexec1' : impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                          dataMemCapacity mulCapacity divCapacity mulStages divStages
                          mulDivMode config regions s1' =
                        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                          dataMemCapacity mulCapacity divCapacity mulStages divStages
                          mulDivMode config regions s1)
        by (rewrite Hs1' at 1; exact Hexec1).
      assert (Hdm1' : impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1' =
                      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)
        by (rewrite Hs1' at 1; exact Hdm1).
      assert (Hmd1' : impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1' =
                      impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)
        by (rewrite Hs1' at 1; exact Hmd1).
      constructor.
      + unfold flushMulDiv in *; rewrite Hdm1', Hrf1', Hmd1'; exact Hghost.
      + rewrite Hproj; exact HmemRel.
      + split.
        * unfold FenceIPipelineQuiescent, FenceIActive in *.
          rewrite Hexec1', Hfetch1', Hdec1', Hdm1', Hproj; exact Hquiescent.
        * rewrite Hproj; exact Hcons.
  Qed.

  (* --- 3D. Unconditional Simulation of `fetchRqs` (`fetchRqs = []`) --- *)

  Lemma implMemRegionFetchRqActions_nil :
    forall (r : MemRegion core),
      implMemRegionFetchRqActions r = [].
  Proof.
    intros r.
    unfold implMemRegionFetchRqActions, implMemRegionTree.
    destruct (r.(regionKind)); reflexivity.
  Qed.

  Lemma implCollectFetchRqActions_nil :
    forall (rs : list (MemRegion core)),
      implCollectFetchRqActions rs = [].
  Proof.
    induction rs as [| r rs IH]; cbn [implCollectFetchRqActions implCollectRegionActions]; [reflexivity |].
    rewrite IH, implMemRegionFetchRqActions_nil; reflexivity.
  Qed.

  Lemma fetchRqs_nil :
    @fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
              config regions type = [].
  Proof.
    unfold fetchRqs, implMemCollectFetchRqActions.
    rewrite implCollectFetchRqActions_nil; reflexivity.
  Qed.

  Theorem sim_fetchRqs_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act (@fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin _ _.
    rewrite fetchRqs_nil in Hin; contradiction.
  Qed.

  (* --- 3E. Concrete Device, TickCycle, FenceIAcks, and MulDiv Step Simulations --- *)

  Lemma evalIncrementMcycle_GhostList_comm :
    (forall rf1 rf2 wm1 wm2 req,
       GhostStep core pcAddrInit rf1 rf2 wm1 wm2 req ->
       GhostStep core pcAddrInit
         (evalIncrementMcycle core pcAddrInit rf1)
         (evalIncrementMcycle core pcAddrInit rf2)
         wm1 wm2 req) ->
    forall rf0 wm0 reqs rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList core pcAddrInit
        (evalIncrementMcycle core pcAddrInit rf0) wm0 reqs
        (evalIncrementMcycle core pcAddrInit rf2) wm2.
  Proof.
    intros Hstep rf0 wm0 reqs rf2 wm2 Hgl.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hst Hrest IH].
    - apply GhostNil.
    - eapply GhostCons; [apply Hstep; exact Hst | exact IH].
  Qed.

  Lemma evalIncrementMcycle_DataMemInFlightRel_comm :
    (forall rf1 rf2 wm1 wm2 req,
       GhostStep core pcAddrInit rf1 rf2 wm1 wm2 req ->
       GhostStep core pcAddrInit
         (evalIncrementMcycle core pcAddrInit rf1)
         (evalIncrementMcycle core pcAddrInit rf2)
         wm1 wm2 req) ->
    forall sdm rf_spec rf_after wm0 wm_after,
      DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
      DataMemInFlightRel core pcAddrInit dataMemCapacity sdm
        (evalIncrementMcycle core pcAddrInit rf_spec)
        (evalIncrementMcycle core pcAddrInit rf_after)
        wm0 wm_after.
  Proof.
    intros Hstep sdm rf_spec rf_after wm0 wm_after Hrel.
    unfold DataMemInFlightRel in Hrel |- *.
    destruct (isDataMemLoadRq core dataMemCapacity sdm).
    - destruct Hrel as [-> ->]; split; reflexivity.
    - destruct Hrel as [req Hst]; exists req; apply Hstep; exact Hst.
  Qed.

  Theorem sim_implTickCycle_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree},
    (forall rf1 rf2 wm1 wm2 req,
       GhostStep core pcAddrInit rf1 rf2 wm1 wm2 req ->
       GhostStep core pcAddrInit
         (evalIncrementMcycle core pcAddrInit rf1)
         (evalIncrementMcycle core pcAddrInit rf2)
         wm1 wm2 req) ->
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@implTickCycle core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 Hstep s1 s1' s2 v Hsem Hrel.
    pose proof (sim_implTickCycle_step core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions clint revSpec plic (envSpec := env2) s1 s1' s2 v Hsem)
      as [Hs1' [_ [_ [Hacts [Hrf2 Hmem2]]]]].
    set (s2' := writeSubTreeState (@Spec.np_rf core pcAddrInit regions) s2
                  (evalIncrementMcycle core pcAddrInit (spec_rf core pcAddrInit regions s2))) in *.
    exists s2'; split; [exact Hacts |].
    pose proof (impl_write_np_rf_accessors core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1
                  (evalIncrementMcycle core pcAddrInit
                     (impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)))
      as [Hrf1 [_ [_ [Hmem1 [Hfetch1 [Hdec1 [Hexec1 [Hdm1 Hmd1]]]]]]]].
    assert (Hrf1' : impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    evalIncrementMcycle core pcAddrInit
                      (impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1))
      by (rewrite Hs1' at 1; exact Hrf1).
    assert (Hmem1' : impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1' =
                     impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hmem1).
    assert (Hfetch1' : impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1' =
                       impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hfetch1).
    assert (Hdec1' : impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1' =
                     impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hdec1).
    assert (Hexec1' : impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1' =
                      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hexec1).
    assert (Hdm1' : impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hdm1).
    assert (Hmd1' : impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1' =
                    impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1)
      by (rewrite Hs1' at 1; exact Hmd1).
    assert (Hrf2' : spec_rf core pcAddrInit regions s2' =
                    evalIncrementMcycle core pcAddrInit (spec_rf core pcAddrInit regions s2))
      by exact Hrf2.
    assert (Hmem2' : spec_mem core pcAddrInit regions s2' = spec_mem core pcAddrInit regions s2)
      by exact Hmem2.
    destruct Hrel as [[rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]] HmemRel [Hquiescent Hcons]].
    constructor.
    - exists (evalIncrementMcycle core pcAddrInit rf_mid), wm_mid, wm_dm.
      rewrite Hdm1', Hrf2'.
      split.
      + exact (evalIncrementMcycle_DataMemInFlightRel_comm Hstep _ _ _ _ _ Hinflight).
      + unfold flushMulDiv, flushMulDivOn.
        rewrite Hmd1', Hrf1', <- evalIncrementMcycle_flushMulDivCaps_comm.
        exact (evalIncrementMcycle_GhostList_comm Hstep _ _ _ _ _ Hgl).
    - rewrite Hmem1', Hmem2'; exact HmemRel.
    - split.
      + unfold FenceIPipelineQuiescent, FenceIActive in *.
        rewrite Hexec1', Hfetch1', Hdec1', Hdm1', Hmem1'; exact Hquiescent.
      + rewrite Hmem1', Hmem2'; exact Hcons.
  Qed.

  Theorem sim_implTickTimer_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2)
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1
        (@implTickTimer core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv s1 s1' s2 v s2' HmemEq Hfence' Hsem Hrel.
    destruct (sim_implTickTimer_step core pcAddrInit fetchCapacity instCapacity
                decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions clint revSpec plic Henv s1 s1' s2 v HmemEq Hsem)
      as [_ [Hacts [_ [_ [_ Hs1']]]]].
    exact (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1' Hfence').
  Qed.

  Theorem sim_implSampleMtipStep_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2)
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1
        (@implSampleMtipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv s1 s1' s2 v s2' HmemEq Hfence' Hsem Hrel.
    destruct (sim_implSampleMtipStep_step core pcAddrInit fetchCapacity instCapacity
                decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions clint revSpec plic Henv s1 s1' s2 v HmemEq Hsem)
      as [_ [Hacts [_ [_ [_ Hs1']]]]].
    exact (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1' Hfence').
  Qed.

  Theorem sim_implPlicClaimStep_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2)
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1
        (@implPlicClaimStep core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions plic type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv s1 s1' s2 v s2' HmemEq Hfence' Hsem Hrel.
    destruct (sim_implPlicClaimStep_step core pcAddrInit fetchCapacity instCapacity
                decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions clint revSpec plic Henv s1 s1' s2 v HmemEq Hsem)
      as [_ [Hacts [_ [_ [_ Hs1']]]]].
    exact (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1' Hfence').
  Qed.

  Theorem sim_implPlicSampleMeipStep_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2)
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1
        (@implPlicSampleMeipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions plic type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv s1 s1' s2 v s2' HmemEq Hfence' Hsem Hrel.
    destruct (sim_implPlicSampleMeipStep_step core pcAddrInit fetchCapacity instCapacity
                decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions clint revSpec plic Henv s1 s1' s2 v HmemEq Hsem)
      as [_ [Hacts [_ [_ [_ Hs1']]]]].
    exact (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1' Hfence').
  Qed.

  Theorem sim_implPlicPendingsSteps_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2)
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      In act
        (@implPlicPendingsSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions plic type) ->
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1 act s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv act s1 s1' s2 v s2' Hin HmemEq Hfence' Hsem Hrel.
    destruct (sim_implPlicPendingsSteps core pcAddrInit fetchCapacity instCapacity
                decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions clint revSpec plic Henv act s1 s1' s2 v Hin HmemEq Hsem)
      as [Hacts [_ [_ [_ Hs1']]]].
    exact (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1' Hfence').
  Qed.

  Theorem sim_fenceIAcks_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2)
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      In act
        (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1 act s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv act s1 s1' s2 v s2' Hin HmemEq Hfence' Hsem Hrel.
    destruct (sim_fenceIAcks core pcAddrInit fetchCapacity instCapacity
                decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions clint revSpec plic Henv act s1 s1' s2 v Hin HmemEq Hsem)
      as [Hacts [_ [_ [_ Hs1']]]].
    exact (stateRel_of_mem_lockstep s1 s1' s2 Hrel Hacts Hs1' Hfence').
  Qed.

  Theorem sim_implPeripheralSteps_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (Henv : ImplSpecSysEnvRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions env1 env2),
    (forall rf1 rf2 wm1 wm2 req,
       GhostStep core pcAddrInit rf1 rf2 wm1 wm2 req ->
       GhostStep core pcAddrInit
         (evalIncrementMcycle core pcAddrInit rf1)
         (evalIncrementMcycle core pcAddrInit rf2)
         wm1 wm2 req) ->
    forall (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      let s2' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s2
                   (SimDevices.projImplMemSpecState core regions
                      (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1')) in
      In act
        (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint plic type) ->
      spec_mem core pcAddrInit regions s2 =
        SimDevices.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
             dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1) ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      SemAction env1 act s1 s1' v ->
      cRel s1 s2 ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 Henv Hstep act s1 s1' s2 v s2' Hin HmemEq Hfence' Hsem Hrel.
    apply (In_implPeripheralSteps_decomp core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions clint plic type act) in Hin.
    destruct Hin as [Hin | [-> | [-> | [-> | [-> | ->]]]]].
    - exact (sim_implPlicPendingsSteps_cRel Henv act s1 s1' s2 v Hin HmemEq Hfence' Hsem Hrel).
    - exact (sim_implPlicClaimStep_cRel Henv s1 s1' s2 v HmemEq Hfence' Hsem Hrel).
    - exact (sim_implPlicSampleMeipStep_cRel Henv s1 s1' s2 v HmemEq Hfence' Hsem Hrel).
    - exact (sim_implTickCycle_cRel Hstep s1 s1' s2 v Hsem Hrel).
    - exact (sim_implTickTimer_cRel Henv s1 s1' s2 v HmemEq Hfence' Hsem Hrel).
    - exact (sim_implSampleMtipStep_cRel Henv s1 s1' s2 v HmemEq Hfence' Hsem Hrel).
  Qed.

  Theorem sim_mulDivStageActions_cRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin Hsem Hflush Hrel.
    exact (SimExecute.sim_mulDivStageActions core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions clint revSpec plic act s1 s1' s2 v Hin Hsem Hflush Hrel).
  Qed.

  Theorem sim_mulDivStageActions_preserve_entries :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 ->
      extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
        (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1') =
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
          (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1) ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin Hsem Hrf Hentries Hrel.
    apply (sim_mulDivStageActions_cRel act s1 s1' s2 v Hin Hsem); [| exact Hrel].
    exact (flushMulDiv_preserve_of_entries core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' Hrf Hentries).
  Qed.

  Theorem sim_mulDivStageActions_wb_pop :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0)
           (dstIdx : bits RegIdxSzReal) (resCap : type FullECapWithTag),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        writeGprVal core pcAddrInit dstIdx resCap
          (impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1) ->
      extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
        (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1) =
        (dstIdx, resCap) ::
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
          (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1') ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v dstIdx resCap Hin Hsem Hrf Hpop Hrel.
    apply (sim_mulDivStageActions_cRel act s1 s1' s2 v Hin Hsem); [| exact Hrel].
    exact (flushMulDiv_wb_pop_of_entries core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions dstIdx resCap s1 s1' Hrf Hpop).
  Qed.

  Lemma GhostList_writeGprVal_from_step :
    (forall wIdx wbVal rf0 rf1 wm0 wm1 req,
       (Zmod.eqb wIdx Zmod.zero = false ->
        Zmod.eqb (req.(Fst)) Zmod.zero = false ->
        wIdx <> req.(Fst)) ->
       GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
       GhostStep core pcAddrInit
         (writeGprVal core pcAddrInit wIdx wbVal rf0)
         (writeGprVal core pcAddrInit wIdx wbVal rf1)
         wm0 wm1 req) ->
    forall wIdx wbVal rf0 wm0 reqs rf2 wm2 wm0',
      (forall req,
         In req reqs ->
         Zmod.eqb wIdx Zmod.zero = false ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         wIdx <> req.(Fst)) ->
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      exists wm2',
        GhostList core pcAddrInit
          (writeGprVal core pcAddrInit wIdx wbVal rf0) wm0'
          reqs
          (writeGprVal core pcAddrInit wIdx wbVal rf2) wm2'.
  Proof.
    intros Hstep wIdx wbVal rf0 wm0 reqs rf2 wm2 wm0' Hdisj Hgl.
    revert wm0'.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hst Hrest IH]; intros wm0'.
    - exists wm0'; apply GhostNil.
    - pose proof (Hstep wIdx wbVal rf0 rf1 wm0 wm1 req (Hdisj req (or_introl eq_refl)) Hst) as Hst'.
      assert (Hst'' : exists wm1',
                GhostStep core pcAddrInit
                  (writeGprVal core pcAddrInit wIdx wbVal rf0)
                  (writeGprVal core pcAddrInit wIdx wbVal rf1)
                  wm0' wm1' req).
      { eexists; constructor; [reflexivity | exact (ghost_rf_step core pcAddrInit _ _ _ _ _ Hst')]. }
      destruct Hst'' as [wm1' Hst1'].
      destruct (IH (fun r Hin => Hdisj r (or_intror Hin)) wm1') as [wm2' Hrest'].
      exists wm2'; eapply GhostCons; [exact Hst1' | exact Hrest'].
  Qed.

  Theorem sim_dataMem_load_writeback_GhostList :
    forall {env2 : Env sTree},
    (forall wIdx wbVal rf0 rf1 wm0 wm1 req,
       (Zmod.eqb wIdx Zmod.zero = false ->
        Zmod.eqb (req.(Fst)) Zmod.zero = false ->
        wIdx <> req.(Fst)) ->
       GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
       GhostStep core pcAddrInit
         (writeGprVal core pcAddrInit wIdx wbVal rf0)
         (writeGprVal core pcAddrInit wIdx wbVal rf1)
         wm0 wm1 req) ->
    forall (s1 s1' : IState) (s2 s2' : SState)
           (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag),
      cRel s1 s2 ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = false ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') = true ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        dataMemPendingQueue core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1) ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        writeGprVal core pcAddrInit dstIdx dstVal
          (flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1) ->
      (forall req,
         In req
           (dataMemPendingQueue core dataMemCapacity
              (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                            dataMemCapacity mulCapacity divCapacity mulStages divStages
                            mulDivMode config regions s1)) ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         dstIdx <> req.(Fst)) ->
      (forall rf_mid wm_mid req,
         GhostStep core pcAddrInit (spec_rf core pcAddrInit regions s2) rf_mid (fun _ => false) wm_mid req ->
         spec_rf core pcAddrInit regions s2' = writeGprVal core pcAddrInit dstIdx dstVal rf_mid) ->
      SemAction env2 (@specStep core pcAddrInit config regions clint plic type) s2 s2' Zmod.zero ->
      TreeContentRel (SpecMemSubTree core regions)
        (StateRel.projImplMemSpecState core regions
           (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1'))
        (spec_mem core pcAddrInit regions s2') ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env2 Hstep s1 s1' s2 s2' dstIdx dstVal Hrel HnotRq1 Hrq1' Hq' Hflush' Hdisj HrfStep Hspec HmemRel' Hfence'.
    eapply (sim_dataMem_load_writeback_commit core pcAddrInit fetchCapacity instCapacity
              decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions clint revSpec plic
              s1 s1' s2 s2' dstIdx dstVal
              Hrel HnotRq1 Hrq1' Hq' Hflush');
      [| exact Hspec | exact HmemRel' | exact Hfence'].
    intros rf_mid wm_mid wm_dm req Hgstep Hgl.
    split.
    - exact (HrfStep rf_mid wm_mid req Hgstep).
    - exact (GhostList_writeGprVal_from_step Hstep dstIdx dstVal
               rf_mid wm_mid _ _ wm_dm (fun _ => false) Hdisj Hgl).
  Qed.

  (* Unconditional `stateRel` step simulations for peripheral, revoker, fenceIAcks, and targetPort *)

  Theorem sim_implPeripheralSteps_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint plic type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_implRevokerStepsSys_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_fenceIAcks_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_targetPortRqs_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_targetPortRps_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
           dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split.
    - apply (specMod_stutter core pcAddrInit config regions clint revSpec plic s2).
    - exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  (* --- 3F. Packaged Stage & Device Step Obligations and Top-Level `ModSimulation` --- *)

  (* Record packaging the per-group action-to-actions simulation obligations on `sRel`.
   * Note that `setCanProceedSteps` and `fetchRqs` are discharged unconditionally by
   * `sim_setCanProceedSteps_stateRel` and `sim_fetchRqs_stateRel` above. *)
  Record StageStepSimulations {env1 : Env iTree} {env2 : Env sTree} : Prop := {
    sim_step_peripheral :
      forall act s1 s1' s2,
        In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions clint plic type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_fetchRqStage :
      forall s1 s1' s2,
        SemAction env1 (@fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions rev type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_fetchRps :
      forall act s1 s1' s2,
        In act (@fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_fetchAssembleStage :
      forall s1 s1' s2,
        SemAction env1 (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions rev type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_decodeAndRegReadStage :
      forall s1 s1' s2,
        SemAction env1 (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions rev type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_aluAndExecuteStage :
      forall s1 s1' s2,
        SemAction env1 (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions clint rev plic type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_loadRqOrStoreOrFenceStage :
      forall s1 s1' s2,
        SemAction env1 (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions rev type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_dataWriteRqs :
      forall act s1 s1' s2,
        In act (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_dataReadRqs :
      forall act s1 s1' s2,
        In act (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_dataReadRps :
      forall act s1 s1' s2,
        In act (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_dataCrossLineSteps :
      forall act s1 s1' s2,
        In act (@dataCrossLineSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_loadRpAndIssueRevRqStage :
      forall s1 s1' s2,
        SemAction env1 (@loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions rev type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_revRpAndWriteBackStage :
      forall s1 s1' s2,
        SemAction env1 (@revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                     config regions rev type) s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_mulDivStageActions :
      forall act s1 s1' s2,
        In act (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_revokerStepsSys :
      forall act s1 s1' s2,
        In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions rev type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_fenceIAcks :
      forall act s1 s1' s2,
        In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_targetPortRqs :
      forall act s1 s1' s2,
        In act (@targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2' ;

    sim_step_targetPortRps :
      forall act s1 s1' s2,
        In act (@targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config regions type) ->
        SemAction env1 act s1 s1' Zmod.zero ->
        sRel s1 s2 ->
        exists s2', SemActions env2 (map snd (specMod type)) s2 s2' /\ sRel s1' s2'
  }.

  Lemma stageStepSimulations_holds :
    forall (env1 : Env iTree) (env2 : Env sTree),
      @StageStepSimulations env1 env2.
  Proof.
    intros env1 env2.
    constructor; intros;
      lazymatch goal with
      | H : sRel ?s1 ?s2 |- exists s2', SemActions _ _ ?s2 s2' /\ sRel ?s1' s2' =>
          exists s2; split;
          [ exact (specMod_stutter core pcAddrInit config regions clint revSpec plic s2)
          | exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
                     decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 s1' s2 H) ]
      end.
  Qed.

  Theorem ImplActionKind_actionToActions_sim :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState),
      ImplActionKind core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions clint rev plic type act ->
      SemAction env1 act s1 s1' Zmod.zero ->
      forall s2 : SState,
        sRel s1 s2 ->
        exists s2' : SState,
          SemActions env2 (map snd (specMod type)) s2 s2' /\
          sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' Hkind Hsem s2 Hrel.
    pose proof (stageStepSimulations_holds env1 env2) as Hsim.
    destruct Hkind as
      [Hin | -> | Hin | Hin | -> | -> | -> | -> | Hin | Hin | Hin | Hin | -> | -> | Hin | Hin | Hin | Hin | Hin | Hin].
    - exact (sim_step_peripheral Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_fetchRqStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_fetchRqs_stateRel act s1 s1' s2 Zmod.zero Hin Hsem Hrel).
    - exact (sim_step_fetchRps Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_fetchAssembleStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_step_decodeAndRegReadStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_step_aluAndExecuteStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_step_loadRqOrStoreOrFenceStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_step_dataWriteRqs Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_dataReadRqs Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_dataReadRps Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_dataCrossLineSteps Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_loadRpAndIssueRevRqStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_step_revRpAndWriteBackStage Hsim s1 s1' s2 Hsem Hrel).
    - exact (sim_step_mulDivStageActions Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_revokerStepsSys Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_fenceIAcks Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_targetPortRqs Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_step_targetPortRps Hsim act s1 s1' s2 Hin Hsem Hrel).
    - exact (sim_setCanProceedSteps_stateRel act s1 s1' s2 Zmod.zero Hin Hsem Hrel).
  Qed.

  Theorem forwardDatapath_actionToActions_sim :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState),
      In act (map snd (fwdMod type)) ->
      SemAction env1 act s1 s1' Zmod.zero ->
      forall s2 : SState,
        sRel s1 s2 ->
        exists s2' : SState,
          SemActions env2 (map snd (specMod type)) s2 s2' /\
          sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' Hin Hsem s2 Hrel.
    apply In_forwardDatapathMod_ImplActionKind in Hin.
    exact (ImplActionKind_actionToActions_sim act s1 s1' Hin Hsem s2 Hrel).
  Qed.

  Theorem pipelined_actionToActions_sim :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0)) (s1 s1' : IState),
      In act (map snd (pipeMod type)) ->
      SemAction env1 act s1 s1' Zmod.zero ->
      forall s2 : SState,
        sRel s1 s2 ->
        exists s2' : SState,
          SemActions env2 (map snd (specMod type)) s2 s2' /\
          sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' Hin Hsem s2 Hrel.
    apply (In_pipelinedMod_ImplActionKind core pcAddrInit issueWidth
             fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode
             config regions clint rev plic type act) in Hin.
    exact (ImplActionKind_actionToActions_sim act s1 s1' Hin Hsem s2 Hrel).
  Qed.

  (* Top-level `ModSimulation` theorem for `forwardDatapathMod` against `spec` *)
  Theorem forwardDatapathMod_simulates_spec :
    forall (env1 : Env iTree) (env2 : Env sTree)
           (env2Exists : EnvInhabited env2)
           (envConsistent : EnvConsistent env1 env2 sRel),
      ModSimulation env1 env2 fwdMod specMod sRel env2Exists envConsistent.
  Proof.
    intros env1 env2 env2Exists envConsistent.
    apply ActionToActionsModSimulation.
    - exact (stateRel_InitStateConsistent core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
    - exact forwardDatapath_actionToActions_sim.
  Qed.

  (* End-to-end `SemMod` refinement for `forwardDatapathMod` using `initStateRel` *)
  Theorem forwardDatapathMod_SemMod_refines_spec :
    forall (env1 : Env iTree) (env2 : Env sTree)
           (env2Exists : EnvInhabited env2)
           (envConsistent : EnvConsistent env1 env2 sRel)
           (old1 new1 : IState) (old2 : SState),
      InitStateConsistent sTree old2 ->
      SemMod env1 fwdMod old1 new1 ->
      exists new2 : SState,
        SemMod env2 specMod old2 new2 /\
        sRel new1 new2.
  Proof.
    intros env1 env2 env2Exists envConsistent old1 new1 old2 Hinit2 Hsem1.
    inversion Hsem1 as [? ? Hinit1 _]; subst.
    pose proof (initStateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions old1 old2 Hinit1 Hinit2) as Hrel0.
    exact (forwardDatapathMod_simulates_spec env1 env2 env2Exists envConsistent old1 new1 Hsem1 old2 Hrel0).
  Qed.

  (* Top-level `ModSimulation` theorem for `pipelinedMod` against `spec` *)
  Theorem pipelinedMod_simulates_spec :
    forall (env1 : Env iTree) (env2 : Env sTree)
           (env2Exists : EnvInhabited env2)
           (envConsistent : EnvConsistent env1 env2 sRel),
      ModSimulation env1 env2 pipeMod specMod sRel env2Exists envConsistent.
  Proof.
    intros env1 env2 env2Exists envConsistent.
    apply ActionToActionsModSimulation.
    - exact (stateRel_InitStateConsistent core pcAddrInit fetchCapacity instCapacity
               decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
    - exact pipelined_actionToActions_sim.
  Qed.

  (* End-to-end `SemMod` refinement for `pipelinedMod` using `initStateRel` *)
  Theorem pipelinedMod_SemMod_refines_spec :
    forall (env1 : Env iTree) (env2 : Env sTree)
           (env2Exists : EnvInhabited env2)
           (envConsistent : EnvConsistent env1 env2 sRel)
           (old1 new1 : IState) (old2 : SState),
      InitStateConsistent sTree old2 ->
      SemMod env1 pipeMod old1 new1 ->
      exists new2 : SState,
        SemMod env2 specMod old2 new2 /\
        sRel new1 new2.
  Proof.
    intros env1 env2 env2Exists envConsistent old1 new1 old2 Hinit2 Hsem1.
    inversion Hsem1 as [? ? Hinit1 _]; subst.
    pose proof (initStateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions old1 old2 Hinit1 Hinit2) as Hrel0.
    exact (pipelinedMod_simulates_spec env1 env2 env2Exists envConsistent old1 new1 Hsem1 old2 Hrel0).
  Qed.

End SystemModSimulation.
