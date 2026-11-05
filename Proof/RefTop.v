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
From Cheriot.Proof Require Import RefRedirect RefRedirStep RefRedirFront RefRedirAsm RefRedirDec RefRedirCore.
From Cheriot.Proof Require Import RefGhost RefFetch RefMemRel.

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

(* --- Observables: region-list pieces --- *)

Local Abbreviation TS t := (TreeState ElemState t).

(* An ExternalMem region: the spec's write trace equals the writes the impl region accepted *)
Definition ExtWritesAt (r : MemRegion) : TS (memRegionTree r) -> TS (implMemRegionTree r) -> Prop :=
  match r.(regionKind) as k
    return TS (memRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> Prop
  with
  | ExternalMem => fun x y => x.(Snd).(Snd).(Snd).(Fst) = implAccWrites r y
  | CustomMem _ _ _ _ => fun _ _ => True
  end.

Fixpoint ExtWritesPost (l : list MemRegion) : TS (specMemTree l) -> TS (implRegionsTree l) -> Prop :=
  match l as l0 return TS (specMemTree l0) -> TS (implRegionsTree l0) -> Prop with
  | [] => fun _ _ => True
  | r :: l' => fun ms mi => ExtWritesAt r ms.(Fst) mi.(Fst) /\ ExtWritesPost l' ms.(Snd).(Fst) mi.(Snd).(Fst)
  end.

(* The revoker position (a CustomMem region) is skipped *)
Fixpoint ExtWritesPre (l : list MemRegion) (sRev iRev : MemRegion) (post : list MemRegion)
  : TS (specMemTree (l ++ sRev :: post)) -> TS (implRegionsTree (l ++ iRev :: post)) -> Prop :=
  match l as l0
    return TS (specMemTree (l0 ++ sRev :: post)) -> TS (implRegionsTree (l0 ++ iRev :: post)) -> Prop
  with
  | [] => fun ms mi => ExtWritesPost post ms.(Snd).(Fst) mi.(Snd).(Fst)
  | r :: l' => fun ms mi => ExtWritesAt r ms.(Fst) mi.(Fst) /\ ExtWritesPre l' sRev iRev post ms.(Snd).(Fst) mi.(Snd).(Fst)
  end.

Lemma ExtWritesAt_of : forall cp pp i r x y, RegionRelAt cp pp i r x y -> ExtWritesAt r x y.
Proof.
  intros cp pp i r; unfold RegionRelAt, ExtWritesAt, memRegionTree, implMemRegionTree.
  destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros x y H;
    [exact (proj1 H) | exact I].
Qed.

Lemma ExtWritesPost_of : forall cp pp l i ms mi, MemRelPost cp pp i l ms mi -> ExtWritesPost l ms mi.
Proof.
  intros cp pp l; induction l as [| r l IH]; intros i ms mi H; cbn [MemRelPost ExtWritesPost] in *; [exact I |].
  destruct H as [H0 H1]; exact (conj (ExtWritesAt_of _ _ _ _ _ _ H0) (IH _ _ _ H1)).
Qed.

Lemma ExtWritesPre_of :
  forall cp pp sRev iRev post l i ms mi, MemRelPre cp pp i l sRev iRev post ms mi -> ExtWritesPre l sRev iRev post ms mi.
Proof.
  intros cp pp sRev iRev post l; induction l as [| r l IH]; intros i ms mi H; cbn [MemRelPre ExtWritesPre] in *.
  - exact (ExtWritesPost_of _ _ _ _ _ _ H).
  - destruct H as [H0 H1]; exact (conj (ExtWritesAt_of _ _ _ _ _ _ H0) (IH _ _ _ H1)).
Qed.

(* The trace of the PLIC's `UartIrq` receive: [ priorities; pending; enables; threshold; claim;
 * meip; in_service; UartIrq ] *)
Definition plicUartOf {n} (x : TS (plicTree n)) := x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

Lemma plicUartOf_rel : forall n1 n2 xs xi, PlicRel n1 n2 xs xi -> plicUartOf xs = plicUartOf xi.
Proof.
  intros n1 n2 xs xi [e [H _]]; subst n2; cbn [eq_rect] in H.
  rewrite H at 1; reflexivity.
Qed.

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
  Local Abbreviation SRuleL initLine :=
    (SpecRevBitRule pcAddrInit config pre post revBase revPfB revPfA initLine).
  Local Abbreviation RelL initLine fwc :=
    (RefRelR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
         (fun _ o => o = fwc) (fun _ _ => True) (SRuleL initLine) (fun _ => RelL initLine fwc)).
    Local Abbreviation STEPOKRR := (SEC StepOKRR initLine fwc).

    Lemma actStepSim_of : forall act, STEPOKRR act -> ACTSTEP act.
    Proof.
      intros act H p s1 s1' s2 Ha Hr Hrel.
      destruct (H s1 s1' s2 Ha (Hr fwc eq_refl) Hrel) as [s2' [Hs Hrel']].
      exists tt, s2'; split; [exact I | split; [intros o -> | ]; assumption].
    Qed.

    Local Abbreviation OF := (SEC StepOKR_of initLine fwc).
    Local Abbreviation NPM := (SEC lift_np_mem initLine fwc).
    Local Abbreviation NPMS := (SEC lift_np_mem_map initLine fwc).

    Lemma lift_peripheral :
      forall act,
        In act (@implPeripheralSteps pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                  config implRegions clint plic type) -> STEPOKRR act.
    Proof.
      intros act Hin.
      pose proof (OF _ (SEC stepOK_implPeripheralSteps initLine fwc HclintIdx HplicIdx act Hin)) as H.
      unfold implPeripheralSteps, implPlicSteps, implTimerSteps in Hin.
      apply in_app_or in Hin as [Hin | Hin]; [apply in_app_or in Hin as [Hin | Hin] |].
      - unfold implPlicPendingsSteps in Hin; cbv zeta in Hin.
        exact (NPMS _ act Hin H).
      - destruct Hin as [<- | [<- | []]]; exact (NPM _ H).
      - destruct Hin as [<- | [<- | [<- | []]]]; [exact (SEC lift_tick initLine fwc H) | exact (NPM _ H) | exact (NPM _ H)].
    Qed.

    Lemma lift_setCp :
      forall act,
        In act (@setCanProceedSteps pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
                  config implRegions rev type) -> STEPOKRR act.
    Proof.
      intros act Hin.
      pose proof (OF _ (SEC stepOK_setCanProceedSteps initLine fwc act Hin)) as H.
      destruct Hin as [<- | [<- | [<- | [<- | []]]]].
      - exact (SEC lift_setFetchCp initLine fwc H).
      - exact (SEC lift_setDecodeCp initLine fwc H).
      - exact (SEC lift_setExecCp initLine fwc H).
      - exact (NPM _ H).
    Qed.

    Lemma pipelinedMod_obligations :
      RefinementObligations pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config specRegions clintS revSpec plicS
        implRegions clint rev plic (implEnvL initLine fwc) (nat -> nat -> nat) unit
        (fun o => specEnvL initLine o) (fun _ o => o = fwc) (fun _ _ => True)
        (SRuleL initLine) (fun _ => RelL initLine fwc).
    Proof.
      constructor;
        lazymatch goal with |- forall _, In _ _ -> _ => intros act Hin | _ => idtac end;
        apply actStepSim_of.
      - exact (lift_peripheral act Hin).
      - exact (SEC stepOK_applyRedirect initLine fwc).
      - exact (SEC stepOK_fetchRq initLine fwc Hdisj).
      - exact (NPMS _ act Hin (OF _ (SEC stepOK_fetchLineRpPorts initLine fwc Hdisj act Hin))).
      - exact (SEC stepOK_fetchAsm initLine fwc Hdisj).
      - exact (SEC stepOK_decode initLine fwc).
      - exact (SEC stepOK_exec initLine fwc Hdisj HclintIdx HplicIdx).
      - exact (SEC stepOK_lsf initLine fwc Hdisj).
      - pose proof Hin as Hin0; destruct Hin0 as [<- | Hin0].
        + exact (NPM _ (OF _ (SEC stepOK_writeRqStep initLine fwc Hdisj HclintIdx HplicIdx))).
        + exact (NPMS _ act Hin0 (SEC stepOK_writeRqPorts initLine fwc Hdisj HrevTab act Hin0)).
      - pose proof Hin as Hin0; destruct Hin0 as [<- | Hin0].
        + exact (NPM _ (OF _ (SEC stepOK_readRqStep initLine fwc Hdisj HrevTab HclintIdx HplicIdx))).
        + exact (NPMS _ act Hin0 (OF _ (SEC stepOK_readRqPorts initLine fwc Hdisj act Hin0))).
      - apply in_app_or in Hin as [Hin | [<- | []]].
        + exact (NPMS _ act Hin (OF _ (SEC stepOK_readRpPorts initLine fwc Hdisj HrevTab act Hin))).
        + exact (NPM _ (OF _ (SEC stepOK_readRpStep initLine fwc))).
      - exact (SEC stepOK_loadRp initLine fwc).
      - exact (SEC stepOK_checkRev initLine fwc).
      - exact (SEC stepOK_issue initLine fwc).
      - exact (SEC stepOK_revRp initLine fwc).
      - exact (SEC stepOK_md initLine fwc Hmd act Hin).
      - exact (NPMS _ act Hin (OF _ (SEC stepOK_implRevokerStepsSys initLine fwc Hdisj HrevTab act Hin))).
      - exact (NPMS _ act Hin (OF _ (SEC stepOK_fenceIAcks initLine fwc act Hin))).
      - exact (lift_setCp act Hin).
    Qed.
  End Oracle.

  (* The software rule on revocation bits: every spec step reachable from the initial spec
   * state `old2` obeys `SpecRevBitRule` (it clears rev bit `b` only if spec memory before it
   * holds no tagged capability with base `b` that needs a revocation check). *)
  Definition SoftwareRevBitsRule initLine fwc (old2 : TreeState ElemState sTree) : Prop :=
    forall s2 s2' a,
      SemActions (specEnvL initLine fwc) (specMod type) old2 s2 ->
      In a (specMod type) ->
      SemAction (specEnvL initLine fwc) a s2 s2' Zmod.zero ->
      SRuleL initLine s2 s2'.

  (* The top-level theorem: if every spec run from the initial spec state `old2` obeys the
   * software rule (`SoftwareRevBitsRule`), every impl run is matched, from `old2`, by a spec run
   * under the same fence.i write-count oracle, ending in `RefRel`-related states. *)
  Theorem pipelinedMod_refines_spec :
    forall initLine fwc old1 new1,
      SemMod (implEnvL initLine fwc) pipeMod old1 new1 ->
      forall old2, InitStateConsistent sTree old2 ->
      SoftwareRevBitsRule initLine fwc old2 ->
      exists fwc' new2, SemMod (specEnvL initLine fwc') specMod old2 new2 /\ RelL initLine fwc new1 new2.
  Proof.
    intros initLine fwc old1 new1 Hsem old2 Hinit2 Hrule.
    destruct (refinement_of_obligations pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config
                specRegions clintS revSpec plicS implRegions clint rev plic (implEnvL initLine fwc)
                (nat -> nat -> nat) unit (fun o => specEnvL initLine o) (fun _ o => o = fwc)
                (fun _ _ => True)
                (fun _ => I) (fun _ _ _ _ _ => I) (fun _ _ _ _ H => H) (fun _ => ex_intro _ fwc eq_refl)
                (SRuleL initLine) (fun _ => RelL initLine fwc)
                (pipelinedMod_obligations initLine fwc) tt
                (fun o1 o2 H1 H2 =>
                   SEC RefRelR_init initLine fwc HdetPre HdetPost HpcEven o1 o2 H1 H2)
                old1 new1 Hsem old2 Hinit2 (fun o Ho => ltac:(cbv beta in Ho; subst o; exact Hrule)))
      as [o [new2 [Hspec [_ Hrel]]]].
    exists o, new2; split; assumption.
  Qed.

  (* --- Observables --- *)

  Local Abbreviation IStateT :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SStateT := (SpecState pcAddrInit specRegions).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA :=
    (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA :=
    (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* Registers: the impl register file (pending mulDiv results written in) is the spec register
   * file (`rf0` plus at most one committed load the impl has not written back, `c`) advanced by a
   * sequence `G` of spec instruction steps (and mcycle ticks), where each instruction is one the
   * spec can fetch from its memory at the PCC the sequence has reached. *)
  Definition ObsRegs initLine fwc (s1 : IStateT) (s2 : SStateT) : Prop :=
    exists rf0 c G,
      sRfA s2 = cnwbApply pcAddrInit c rf0 /\
      GChain pcAddrInit rf0 G (iFlushA s1) /\
      (forall G1 e G2 rfe,
         G = (G1 ++ GInst e :: G2)%list ->
         GChain pcAddrInit rf0 G1 rfe ->
         FetchAllowedInst initLine fwc specRegions (sMemA s2) (readPcc pcAddrInit rfe) (ge_fetchOut e)).

  (* External behavior: every ExternalMem region received the same writes from the spec as it
   * accepted from the impl, and the PLIC's `UartIrq` input delivered the same values to both. *)
  Definition ObsExt (s1 : IStateT) (s2 : SStateT) : Prop :=
    ExtWritesPre pre (specRevRegion revBase revPfB revPfA) (implRevRegion revBase revPfB revPfA) post
      (sMemA s2) (iRegionsA s1) /\
    plicUartOf (specPlicState pre post revBase revPfB revPfA plicS (sMemA s2)) =
      plicUartOf (implPlicState pre post revBase revPfB revPfA plic (iRegionsA s1)).

  Lemma ObsRegs_of : forall initLine fwc s1 s2, RelL initLine fwc s1 s2 -> ObsRegs initLine fwc s1 s2.
  Proof.
    intros initLine fwc s1 s2 [_ [g Hg]].
    unfold effS in Hg; destruct (iRedirValid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1);
    destruct Hg as [Hrf _ _ Hrp _ _ _ _ _ _ _ _ _];
    destruct Hrf as [Hs [Hch _]];
    exists (g_rf0 pcAddrInit g), (g_cnwb pcAddrInit g), (g_chain pcAddrInit g);
    exact (conj Hs (conj Hch Hrp)).
  Qed.

  Lemma ObsExt_of : forall initLine fwc s1 s2, RelL initLine fwc s1 s2 -> ObsExt s1 s2.
  Proof.
    intros initLine fwc s1 s2 [_ [g Hg]].
    unfold effS in Hg; destruct (iRedirValid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1);
    destruct Hg as [_ Hm _ _ _ _ _ _ _ _ _ _ _];
    destruct Hm as [[Hpre [_ [Hpl _]]] _];
    exact (conj (ExtWritesPre_of _ _ _ _ _ _ _ _ _ Hpre) (plicUartOf_rel _ _ _ _ Hpl)).
  Qed.

  (* The top-level theorem stated with the observables *)
  Theorem pipelinedMod_refines_spec_obs :
    forall initLine fwc old1 new1,
      SemMod (implEnvL initLine fwc) pipeMod old1 new1 ->
      forall old2, InitStateConsistent sTree old2 ->
      SoftwareRevBitsRule initLine fwc old2 ->
      exists fwc' new2, SemMod (specEnvL initLine fwc') specMod old2 new2 /\
                        ObsRegs initLine fwc new1 new2 /\ ObsExt new1 new2.
  Proof.
    intros initLine fwc old1 new1 Hsem old2 Hinit2 Hrule.
    destruct (pipelinedMod_refines_spec initLine fwc old1 new1 Hsem old2 Hinit2 Hrule)
      as [o [new2 [Hspec Hrel]]].
    exists o, new2; split; [exact Hspec |].
    exact (conj (ObsRegs_of _ _ _ _ Hrel) (ObsExt_of _ _ _ _ Hrel)).
  Qed.
End Top.
