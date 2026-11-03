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
From Cheriot Require Import SpecDefines Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplMulDiv ImplInst.
From Cheriot.Proof Require Import ImplSpec Refinement SimDevices.
From Cheriot.Proof Require Import RefRel RefCoreRel RefPcEven RefInit RefPeriph RefRevBitRule.
From Cheriot.Proof Require Import RefRevokerStep RefMemStep RefReadRp RefFetchRp RefLoadCommitStep RefRevWriteCommit.
From Cheriot.Proof Require Import RefWriteRqStep RefReadRqStep RefDmStep RefMdStep RefLsfFenceI RefDecodeStep.
From Cheriot.Proof Require Import RefFetchRqStep RefFetchAsmStep RefExecMain.

Unset Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * MILESTONE 8: `pipelinedMod` REFINES `spec`
 * ===========================================================================
 * `refinement_of_obligations` (Refinement.v) instantiated with the real relation
 * `RefRel` (RefCoreRel.v), one StepOK theorem per obligation group, `RefRel_init`
 * for the initial states, and the fence.i write-count oracle kept unchanged
 * (`fwc' := fwc`: O := `nat -> nat -> nat`, P := unit, `Agrees tt o := o = fwc`).
 * - `actStepSim_of`: a `StepOKR` rule meets `ActStepSim`.
 * - `pipelinedMod_obligations`: all obligation groups.
 * - `pipelinedMod_refines_spec`: the top-level theorem. Its static mulDiv hypothesis
 *   `Hmd` holds for the instantiated stage counts (`implMulDivStagesDivideXlen`,
 *   ImplInst.v). *)

Section Top.
  Variable pcAddrInit : Z.
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  (* Spec and impl region lists: equal except at the revoker position. *)
  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation rev := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.

  (* Static hypotheses (CHERIOT_STATUS.md, "Static hypotheses"). *)
  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HrevTab : Is_true (revTableInExternalMem config specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.
  Hypothesis Hmd : Is_true (mulDivStagesDivideXlen mulStages divStages).
  Hypothesis HdetPre : Forall (fun r => allTreeInitDet (memRegionTree r) = true) pre.
  Hypothesis HdetPost : Forall (fun r => allTreeInitDet (memRegionTree r) = true) post.
  Hypothesis HpcEven : pcAligned (Zmod.of_Z _ pcAddrInit).

  Local Abbreviation sTree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation iTree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation specMod := (@spec pcAddrInit config specRegions clintS revSpec plicS).
  Local Abbreviation pipeMod :=
    (@pipelinedMod pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
       config implRegions clint rev plic).
  Local Abbreviation implEnvL initLine fwc :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwc).
  Local Abbreviation specEnvL initLine fwc := (specEnv pcAddrInit specRegions initLine fwc).
  Local Abbreviation RuleL initLine :=
    (RevBitRuleStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post
                    revBase revPfB revPfA initLine).
  Local Abbreviation RelL initLine fwc :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwc).
  (* A section lemma of the StepOK files applied to the common section variables. *)
  Local Abbreviation SEC f initLine fwc :=
    (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
       clintS clint plicS plic initLine fwc).

  Section Oracle.
    Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
    Variable fwc : nat -> nat -> nat.

    Local Abbreviation ACTSTEP :=
      (ActStepSim pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config specRegions clintS revSpec plicS
         implRegions (implEnvL initLine fwc) (nat -> nat -> nat) unit (fun o => specEnvL initLine o)
         (fun _ o => o = fwc) (fun _ _ => True) (RuleL initLine) (fun _ => RelL initLine fwc)).
    Local Abbreviation STEPOKR := (SEC StepOKR initLine fwc).

    Lemma actStepSim_of : forall act, STEPOKR act -> ACTSTEP act.
    Proof.
      intros act H p s1 s1' s2 Ha Hr Hrel.
      destruct (H s1 s1' s2 Ha Hr Hrel) as [s2' [Hs Hrel']].
      exists tt, s2'; split; [exact I | split; [intros o -> | ]; assumption].
    Qed.

    Local Abbreviation OF := (SEC StepOKR_of initLine fwc).

    Lemma pipelinedMod_obligations :
      RefinementObligations pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config specRegions clintS revSpec plicS
        implRegions clint rev plic (implEnvL initLine fwc) (nat -> nat -> nat) unit
        (fun o => specEnvL initLine o) (fun _ o => o = fwc) (fun _ _ => True)
        (RuleL initLine) (fun _ => RelL initLine fwc).
    Proof.
      constructor;
        lazymatch goal with |- forall _, In _ _ -> _ => intros act Hin | _ => idtac end;
        apply actStepSim_of.
      - exact (OF _ (SEC stepOK_implPeripheralSteps initLine fwc HclintIdx HplicIdx act Hin)).
      - exact (OF _ (SEC stepOK_fetchRqStage initLine fwc Hdisj)).
      - exact (OF _ (SEC stepOK_fetchLineRpPorts initLine fwc Hdisj act Hin)).
      - exact (OF _ (SEC stepOK_fetchAssembleStage initLine fwc Hdisj)).
      - exact (OF _ (SEC stepOK_decodeAndRegReadStage initLine fwc)).
      - exact (OF _ (SEC stepOK_aluAndExecuteNonDeferredStage initLine fwc Hdisj HclintIdx HplicIdx)).
      - exact (OF _ (SEC stepOK_loadRqOrStoreOrFenceStage initLine fwc Hdisj)).
      - destruct Hin as [<- | Hin].
        + exact (OF _ (SEC stepOK_writeRqStep initLine fwc Hdisj HclintIdx HplicIdx)).
        + exact (SEC stepOK_writeRqPorts initLine fwc Hdisj HrevTab act Hin).
      - destruct Hin as [<- | Hin].
        + exact (OF _ (SEC stepOK_readRqStep initLine fwc Hdisj HrevTab HclintIdx HplicIdx)).
        + exact (OF _ (SEC stepOK_readRqPorts initLine fwc Hdisj act Hin)).
      - apply in_app_or in Hin as [Hin | [<- | []]].
        + exact (OF _ (SEC stepOK_readRpPorts initLine fwc Hdisj HrevTab act Hin)).
        + exact (OF _ (SEC stepOK_readRpStep initLine fwc)).
      - exact (OF _ (SEC stepOK_loadRpAndIssueRevRqStage initLine fwc)).
      - exact (OF _ (SEC stepOK_revRpAndWriteBackStage initLine fwc)).
      - exact (OF _ (SEC stepOK_mulDivStageActions initLine fwc Hmd act Hin)).
      - exact (OF _ (SEC stepOK_implRevokerStepsSys initLine fwc Hdisj HrevTab act Hin)).
      - exact (OF _ (SEC stepOK_fenceIAcks initLine fwc act Hin)).
      - exact (OF _ (SEC stepOK_setCanProceedSteps initLine fwc act Hin)).
    Qed.
  End Oracle.

  (* The top-level theorem: every impl run whose steps obey the software rule
   * `RevBitRuleStep` is matched, from any consistent initial spec state, by a spec
   * run under the same fence.i write-count oracle, ending in `RefRel`-related states. *)
  Theorem pipelinedMod_refines_spec :
    forall initLine fwc old1 new1,
      SemMod (implEnvL initLine fwc) pipeMod old1 new1 ->
      (forall s s' a,
         SemActions (implEnvL initLine fwc) (pipeMod type) old1 s ->
         In a (pipeMod type) ->
         SemAction (implEnvL initLine fwc) a s s' Zmod.zero ->
         RuleL initLine s s') ->
      forall old2, InitStateConsistent sTree old2 ->
      exists fwc' new2, SemMod (specEnvL initLine fwc') specMod old2 new2 /\ RelL initLine fwc new1 new2.
  Proof.
    intros initLine fwc old1 new1 Hsem Hrule old2 Hinit2.
    destruct (refinement_of_obligations pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config
                specRegions clintS revSpec plicS implRegions clint rev plic (implEnvL initLine fwc)
                (nat -> nat -> nat) unit (fun o => specEnvL initLine o) (fun _ o => o = fwc)
                (fun _ _ => True)
                (fun _ => I) (fun _ _ _ _ _ => I) (fun _ _ _ _ H => H) (fun _ => ex_intro _ fwc eq_refl)
                (RuleL initLine) (fun _ => RelL initLine fwc)
                (pipelinedMod_obligations initLine fwc) tt
                (fun o1 o2 H1 H2 =>
                   SEC RefRel_init initLine fwc HdetPre HdetPost HpcEven o1 o2 H1 H2)
                old1 new1 Hsem Hrule old2 Hinit2)
      as [o [new2 [Hspec [_ Hrel]]]].
    exists o, new2; split; assumption.
  Qed.
End Top.
