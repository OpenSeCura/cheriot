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

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot.Proof Require Import ImplSpec RunSim.

Unset Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * TOP-LEVEL REFINEMENT GLUE FOR `pipelinedMod`
 * ===========================================================================
 * `run_sim` (RunSim.v) turns one step obligation into a run-level result, with
 * the spec env chosen per run (`env2 : O -> Env sTree`, oracle prefixes `P`)
 * and every impl step assumed to obey `Rule`. This section splits that step
 * obligation into one obligation per action group of `pipelinedMod`
 * (`ImplActionKind`) and derives the top-level statement for any relation `R`
 * that meets them. The envs, `Rule` and `R` stay abstract here. *)

Section TopLevelGlue.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  (* Spec and impl region lists. They are meant to differ only at the revoker index
   * (the impl revoker region has extra leaves); the glue does not need that link. *)
  Variable specRegions : list MemRegion.
  Variable clintS : @ClintInstance core specRegions.
  Variable revSpec : @RevokerInstance core [] specRegions.
  Variable plicS : @PlicInstance core (S (S (length (collectIrqActions core specRegions)))) specRegions.
  Variable implRegions : list MemRegion.
  Variable clint : @ClintInstance core implRegions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) implRegions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions core implRegions)))) implRegions.

  Local Abbreviation sTree := (SpecTree core pcAddrInit specRegions).
  Local Abbreviation iTree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config implRegions).
  Local Abbreviation SState := (SpecState core pcAddrInit specRegions).
  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config implRegions).
  Local Abbreviation specMod := (@spec core pcAddrInit config specRegions clintS revSpec plicS).
  Local Abbreviation pipeMod :=
    (@pipelinedMod core pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
       config implRegions clint rev plic).

  (* Impl env, family of spec envs indexed by an oracle, and oracle prefixes. *)
  Variable env1 : Env iTree.
  Variables O P : Type.
  Variable env2 : O -> Env sTree.
  Variable Agrees : P -> O -> Prop.
  Variable Ext : P -> P -> Prop.

  Hypothesis Ext_refl : forall p, Ext p p.
  Hypothesis Ext_trans : forall p1 p2 p3, Ext p1 p2 -> Ext p2 p3 -> Ext p1 p3.
  Hypothesis Agrees_Ext : forall p p' o, Ext p p' -> Agrees p' o -> Agrees p o.
  Hypothesis Agrees_inhabited : forall p, exists o, Agrees p o.

  (* Assumed property of every impl step (the software rule), and the relation. *)
  Variable Rule : IState -> IState -> Prop.
  Variable R : P -> IState -> SState -> Prop.

  (* --- Per-Action Obligation (`ActStepSim`) --- *)

  (* One impl action, taken from a related state and obeying `Rule`, is matched by
   * spec steps that are valid for every oracle agreeing with the new prefix. *)
  Definition ActStepSim (act : Action type iTree (Bit 0)) : Prop :=
    forall p s1 s1' s2,
      SemAction env1 act s1 s1' Zmod.zero ->
      Rule s1 s1' ->
      R p s1 s2 ->
      exists p' s2',
        Ext p p' /\
        (forall o, Agrees p' o -> SemActions (env2 o) (map snd (specMod type)) s2 s2') /\
        R p' s1' s2'.

  (* One obligation per `ImplActionKind` group of `pipelinedMod`. *)
  Record RefinementObligations : Prop := {
    ob_peripheral :
      forall act,
        In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions clint plic type) ->
        ActStepSim act ;
    ob_fetchRqStage :
      ActStepSim (@fetchRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions rev type) ;
    ob_fetchRps :
      forall act,
        In act (@fetchRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act ;
    ob_fetchAssembleStage :
      ActStepSim (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions rev type) ;
    ob_decodeAndRegReadStage :
      ActStepSim (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions rev type) ;
    ob_aluAndExecuteStage :
      ActStepSim (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions clint rev plic type) ;
    ob_loadRqOrStoreOrFenceStage :
      ActStepSim (@loadRqOrStoreOrFenceStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions rev type) ;
    ob_dataWriteRqs :
      forall act,
        In act (@dataWriteRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act ;
    ob_dataReadRqs :
      forall act,
        In act (@dataReadRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act ;
    ob_dataReadRps :
      forall act,
        In act (@dataReadRps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act ;
    ob_loadRpAndIssueRevRqStage :
      ActStepSim (@loadRpAndIssueRevRqStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions rev type) ;
    ob_revRpAndWriteBackStage :
      ActStepSim (@revRpAndWriteBackStage core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                    config implRegions rev type) ;
    ob_mulDivStageActions :
      forall act,
        In act (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act ;
    ob_revokerStepsSys :
      forall act,
        In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions rev type) ->
        ActStepSim act ;
    ob_fenceIAcks :
      forall act,
        In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act ;
    ob_setCanProceedSteps :
      forall act,
        In act (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions type) ->
        ActStepSim act
  }.

  (* --- From Per-Group Obligations to `run_sim`'s Step Obligation --- *)

  Lemma obligations_StepSim :
    RefinementObligations ->
    StepSim iTree sTree env1 O P env2 Agrees Ext
      (map snd (pipeMod type)) (map snd (specMod type)) R Rule.
  Proof.
    intros Hob p s1 s1' s2 a Hin Ha Hrule Hr.
    pose proof (In_pipelinedMod_ImplActionKind core pcAddrInit issueWidth
                  fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode
                  config implRegions clint rev plic type a Hin) as Hkind.
    destruct Hkind as
      [Hin' | -> | Hin' | -> | -> | -> | -> | Hin' | Hin' | Hin' | -> | -> | Hin' | Hin' | Hin' | Hin'].
    - exact (ob_peripheral Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_fetchRqStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_fetchRps Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_fetchAssembleStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_decodeAndRegReadStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_aluAndExecuteStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_loadRqOrStoreOrFenceStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_dataWriteRqs Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_dataReadRqs Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_dataReadRps Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_loadRpAndIssueRevRqStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_revRpAndWriteBackStage Hob p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_mulDivStageActions Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_revokerStepsSys Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_fenceIAcks Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
    - exact (ob_setCanProceedSteps Hob a Hin' p s1 s1' s2 Ha Hrule Hr).
  Qed.

  (* --- Top-Level Statement from the Obligations --- *)

  (* For any relation meeting the per-group obligations and holding on initial
   * states (for some starting prefix `p0`): every impl run whose steps obey
   * `Rule` is matched by a spec run under some oracle, ending in related states. *)
  Theorem refinement_of_obligations :
    RefinementObligations ->
    forall p0 : P,
      (forall old1 old2,
         InitStateConsistent iTree old1 ->
         InitStateConsistent sTree old2 ->
         R p0 old1 old2) ->
      forall old1 new1,
        SemMod env1 pipeMod old1 new1 ->
        (forall s s' a,
           SemActions env1 (map snd (pipeMod type)) old1 s ->
           In a (map snd (pipeMod type)) ->
           SemAction env1 a s s' Zmod.zero ->
           Rule s s') ->
        forall old2,
          InitStateConsistent sTree old2 ->
          exists (o : O) (new2 : SState),
            SemMod (env2 o) specMod old2 new2 /\
            exists p, R p new1 new2.
  Proof.
    intros Hob p0 Hinit old1 new1 Hsem Hrule old2 Hinit2.
    destruct Hsem as [old1 new1 Hinit1 Hrun].
    destruct (run_sim iTree sTree env1 O P env2 Agrees Ext Ext_refl Ext_trans Agrees_Ext
                (map snd (pipeMod type)) (map snd (specMod type)) R Rule
                (obligations_StepSim Hob) old1 new1 Hrun Hrule p0 old2
                (Hinit old1 old2 Hinit1 Hinit2))
      as [p' [new2 [_ [Hval Hr]]]].
    destruct (Agrees_inhabited p') as [o Ho].
    exists o, new2; split.
    - constructor; [exact Hinit2 | exact (Hval o Ho)].
    - exists p'; exact Hr.
  Qed.

End TopLevelGlue.
