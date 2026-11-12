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
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplMulDiv.
From Cheriot.Proof Require Import ImplSpec SimDevices SimExecute SimFetchDecode.
From Cheriot.Proof Require Import RefRel RefCoreRel RefRevoker RefPeriph RefRevBitRule RefRedirect RefExecImpl RefExecFrame.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* ===========================================================================
 * THE STEP OBLIGATION FOR `RefRelR` (item 3.4)
 * ===========================================================================
 * `StepOKRR`: `StepOKR` with the relation `RefRelR` (the state with a pending redirect applied,
 * plus `RedirInv`). Actions on the memory subtree commute with applying the redirect, so their
 * `StepOKR` lifts (`lift_np_mem`). *)

Section RedirStep.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation RRA :=
    (RefRelR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation SRF :=
    (SpecRuleFrom pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwcs).
  Local Abbreviation STEPOKR :=
    (StepOKR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation ACC f :=
    (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation applyPA := (ACC applyP).
  Local Abbreviation effSA := (ACC effS).
  Local Abbreviation validA := (ACC iRedirValid).
  Local Abbreviation InvA := (ACC RedirInv).
  Local Abbreviation NPMEM :=
    (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Definition StepOKRR (act : Action type ITree (Bit 0)) : Prop :=
    forall (s1 s1' : TS ITree) (s2 : TS STree),
      SemAction envI act s1 s1' Zmod.zero ->
      SRF s2 ->
      RRA s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ RRA s1' s2'.

  (* --- 1. Actions on the Memory Subtree --- *)

  Lemma np_mem_applyP_write :
    forall (s : IState) m, writeSubTreeState NPMEM (applyPA s) m = applyPA (writeSubTreeState NPMEM s m).
  Proof. reflexivity. Qed.

  Lemma envI_applyP : forall (s : IState) x v, envI (applyPA s) x v <-> envI s x v.
  Proof. intros s x v; reflexivity. Qed.

  Lemma lift_np_mem :
    forall (a : Action type (getNode NPMEM) (Bit 0)), STEPOKR (liftAction NPMEM a) ->
      StepOKRR (liftAction NPMEM a).
  Proof.
    intros a H s1 s1' s2 Hs Hr [Hinv [Hh [g Hg]]].
    pose proof Hs as Hs0; apply SemAction_liftAction_iff in Hs0 as [m' [Hm Es]].
    assert (Hinv' : InvA s1') by (subst s1'; exact Hinv).
    assert (Hh' : ACC HandInv s1').
    { revert Hh; subst s1'; apply (ACC HandInv_frame);
        [reflexivity | reflexivity | reflexivity | intros _; reflexivity | reflexivity | intros h; exact h
        | intros h; exact h]. }
    assert (Ev : validA s1' = validA s1) by (subst s1'; reflexivity).
    destruct (validA s1) eqn:Hv.
    - erewrite effS_true in Hg by exact Hv.
      assert (Hs' : SemAction envI (liftAction NPMEM a) (applyPA s1) (applyPA s1') Zmod.zero).
      { apply SemAction_liftAction_iff; exists m'; split.
        - rewrite SemAction_iff_evalActionPropGen in Hm |- *.
          refine (proj2 (evalActionPropGen_env_ext _ _ _ _ _ _) Hm).
          intros sub x v; unfold subEnv; split; intros Hx; exact Hx.
        - subst s1'; symmetry; apply np_mem_applyP_write. }
      destruct (H _ _ _ Hs' Hr (ex_intro _ g Hg)) as [s2' [Hss [g' Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact Hinv' |]; split; [exact Hh' |]; exists g'.
      erewrite effS_true by exact Ev; exact Hg'.
    - erewrite effS_false in Hg by exact Hv.
      destruct (H _ _ _ Hs Hr (ex_intro _ g Hg)) as [s2' [Hss [g' Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact Hinv' |]; split; [exact Hh' |]; exists g'.
      erewrite effS_false by exact Ev; exact Hg'.
  Qed.

  (* --- 2. Deterministic Actions That Commute With the Redirect --- *)

  Lemma lift_det :
    forall (act : Action type ITree (Bit 0)) (F : IState -> IState),
      (forall s s', SemAction envI act s s' Zmod.zero -> s' = F s) ->
      (forall s, SemAction envI act s (F s) Zmod.zero) ->
      (forall s, F (applyPA s) = applyPA (F s)) ->
      (forall s, validA (F s) = validA s) ->
      (forall s, InvA s -> InvA (F s)) ->
      (forall s, ACC HandInv s -> ACC HandInv (F s)) ->
      STEPOKR act -> StepOKRR act.
  Proof.
    intros act F Hsem Hsem' Hcomm Hval Hinv Hhand H s1 s1' s2 Hs Hr [Hi [Hh [g Hg]]].
    rewrite (Hsem _ _ Hs) in Hs |- *.
    pose proof (Hval s1) as Ev.
    destruct (validA s1) eqn:Hv.
    - erewrite effS_true in Hg by exact Hv.
      pose proof (Hsem' (applyPA s1)) as Hs'; rewrite Hcomm in Hs'.
      destruct (H _ _ _ Hs' Hr (ex_intro _ g Hg)) as [s2' [Hss [g' Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact (Hinv _ Hi) |]; split; [exact (Hhand _ Hh) |]; exists g'.
      erewrite effS_true by exact Ev; exact Hg'.
    - erewrite effS_false in Hg by exact Hv.
      destruct (H _ _ _ Hs Hr (ex_intro _ g Hg)) as [s2' [Hss [g' Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact (Hinv _ Hi) |]; split; [exact (Hhand _ Hh) |]; exists g'.
      erewrite effS_false by exact Ev; exact Hg'.
  Qed.

  Local Abbreviation NPRF :=
    (Impl.np_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPFETCH :=
    (Impl.np_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPDEC :=
    (Impl.np_decode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPEXEC :=
    (Impl.np_execute pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Lemma lift_tick :
    STEPOKR (@implTickCycle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
    StepOKRR (@implTickCycle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    apply (lift_det _ (fun s => writeSubTreeState NPRF s (evalIncrementMcycle pcAddrInit (readSubTreeState NPRF s)))).
    - intros s s' Hs; unfold implTickCycle in Hs.
      apply SemAction_liftAction_iff in Hs as [rf' [Hrf ->]].
      apply SemAction_incrementMcycle_iff in Hrf as [-> _]; reflexivity.
    - intros s; unfold implTickCycle; apply SemAction_liftAction_iff; eexists; split; [| reflexivity].
      apply SemAction_incrementMcycle_iff; split; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros s H.
      refine (RedirInv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ eq_refl eq_refl eq_refl eq_refl eq_refl _
                eq_refl eq_refl eq_refl eq_refl H).
      exact (f_equal tagEcap (readPcc_incr pcAddrInit (ACC iRf s))).
    - intros s; apply (ACC HandInv_frame);
        [reflexivity | reflexivity | reflexivity | intros _; reflexivity | exact (readPcc_incr pcAddrInit (ACC iRf s))
        | intros h; exact h | intros h; exact h].
  Qed.

  Ltac det_sem lem :=
    intros s s' Hs; apply SemAction_liftAction_iff in Hs as [sub [Hs ->]];
    rewrite SemAction_iff_evalActionPropGen in Hs; apply (proj1 (lem _ _ _)) in Hs;
    destruct Hs as [-> _]; reflexivity.
  Ltac det_sem' lem :=
    intros s; apply SemAction_liftAction_iff; eexists; split; [| reflexivity];
    rewrite SemAction_iff_evalActionPropGen; apply (proj2 (lem _ _ _)); split; reflexivity.

  Lemma lift_setFetchCp :
    STEPOKR (@setFetchCanProceedStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
    StepOKRR (@setFetchCanProceedStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    intros Hok; apply (lift_det _ (fun s => writeSubTreeState NPFETCH s
                                  (fetch_withCanProceed pcAddrInit fetchCapacity instCapacity
                                     (readSubTreeState NPFETCH s) true)));
      [det_sem (@evalActionPropGen_setFetchCanProceed pcAddrInit fetchCapacity instCapacity) | det_sem' (@evalActionPropGen_setFetchCanProceed pcAddrInit fetchCapacity instCapacity) | reflexivity | reflexivity | intros s H; exact H
       | intros s; apply (ACC HandInv_eq); reflexivity | exact Hok].
  Qed.

  Lemma lift_setDecodeCp :
    STEPOKR (@setDecodeCanProceedStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
    StepOKRR (@setDecodeCanProceedStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    intros Hok; apply (lift_det _ (fun s => writeSubTreeState NPDEC s
                                  (decode_withCanProceed decodeCapacity (readSubTreeState NPDEC s) true)));
      [det_sem (@evalActionPropGen_setDecodeCanProceed decodeCapacity) | det_sem' (@evalActionPropGen_setDecodeCanProceed decodeCapacity) | reflexivity | reflexivity | intros s H; exact H
       | intros s; apply (ACC HandInv_frame);
         [reflexivity | reflexivity | reflexivity | intros _; reflexivity | reflexivity
         | intros h; exact h | intros h; exact h] | exact Hok].
  Qed.

  Lemma lift_setExecCp :
    STEPOKR (@setExecuteCanProceedStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
    StepOKRR (@setExecuteCanProceedStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    intros Hok; apply (lift_det _ (fun s => writeSubTreeState NPEXEC s
                                  (ex_withHandoff (ex_withFirstSlot (ex_withCanProceed (readSubTreeState NPEXEC s) true) true)
                                     (getDefault ExecHandoff))));
      [det_sem (@evalActionPropGen_resetExecuteCanProceed) | det_sem' (@evalActionPropGen_resetExecuteCanProceed)
       | reflexivity | reflexivity | intros s H; exact H
       | intros s _; apply (ACC HandInv_first); reflexivity | exact Hok].
  Qed.

  (* --- 3. `applyRedirect` --- *)

  Local Abbreviation ARSTAGE :=
    (@applyRedirectStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions
       (revImplOf pre post revBase revPfB revPfA) type).

  Ltac ar_ret H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (Return _) _ _ => apply fw_return in H
            | evalActionPropGen _ (LetAction _ _ _) _ _ => apply fw_letAction in H
            end; cbv beta in H).

  Lemma applyRedirect_char :
    forall (s1 s1' : IState),
      SemAction envI ARSTAGE s1 s1' Zmod.zero ->
      ACC iRf s1' = ACC iRf s1 /\ ACC iWb s1' = ACC iWb s1 /\ ACC iMem s1' = ACC iMem s1 /\
      ACC iDecode s1' = ACC iDecode s1 /\ ACC iDm s1' = ACC iDm s1 /\
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1' =
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1 /\
      (if validA s1
       then ACC iFetch s1' =
              fetch_withPccCopy pcAddrInit fetchCapacity instCapacity
                (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity
                   (fetch_withFipCopy pcAddrInit fetchCapacity instCapacity (ACC iFetch s1) (ACC iFenceIPending s1))
                   (getDefault (Option StraddleHalf)))
                (ACC redirPcc s1) /\
            ACC iExec s1' = ex_withRedirect (ex_withExecEpoch (ACC iExec s1) (nextEpoch (ACC iExecEpoch s1)))
                              (getDefault (Option FullECapWithTag))
       else ACC iFetch s1' =
              fetch_withFipCopy pcAddrInit fetchCapacity instCapacity (ACC iFetch s1) (ACC iFenceIPending s1) /\
            ACC iExec s1' = ACC iExec s1).
  Proof.
    intros s1 s1' H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold applyRedirectStage in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    unfold applyRedirect in H.
    cbn [execute_readRedirect execute_readExecEpoch execute_readFenceIPend execute_writeExecEpoch
         execute_clearRedirect implExecuteIfc] in H.
    eapply fw_liftRead in H;
      [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readRedirect _ _) HQ_)]; cbv beta in H.
    eapply fw_liftRead in H;
      [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecEpoch _ _) HQ_)]; cbv beta in H.
    eapply fw_liftRead in H;
      [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readFenceIPending _ _) HQ_)]; cbv beta in H.
    eapply fw_liftUpd in H;
      [| intros env_ sub_ Q_ HQ_;
         exact (proj1 (evalActionPropGen_writeFetchFenceIPending pcAddrInit fetchCapacity instCapacity _ _ _) HQ_)];
      cbv beta in H.
    apply fw_ifTF in H as [[Hv H] | [Hv H]].
    - repeat (apply fw_letExp in H; cbv beta in H).
      eapply fw_liftUpd in H;
        [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_writeExecEpoch _ _ _) HQ_)]; cbv beta in H.
      eapply fw_liftUpd in H;
        [| intros env_ sub_ Q_ HQ_;
           exact (proj1 (evalActionPropGen_clearStraddle pcAddrInit fetchCapacity instCapacity _ _) HQ_)];
        cbv beta in H.
      eapply fw_liftUpd in H;
        [| intros env_ sub_ Q_ HQ_;
           exact (proj1 (evalActionPropGen_writeFetchPcc pcAddrInit fetchCapacity instCapacity _ _ _) HQ_)];
        cbv beta in H.
      eapply fw_liftUpdLast in H;
        [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_clearRedirect _ _) HQ_)]; cbv beta in H.
      ar_ret H; destruct H as [<- _].
      assert (E : validA s1 = true) by exact Hv; rewrite E.
      repeat split; reflexivity.
    - ar_ret H; destruct H as [<- _].
      assert (E : validA s1 = false) by exact Hv; rewrite E.
      repeat split; reflexivity.
  Qed.

  Local Abbreviation FEXT :=
    (RefRelG_fetch_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
       clintS clint plicS plic initLine fwcs).

  Theorem stepOK_applyRedirect : StepOKRR ARSTAGE.
  Proof.
    intros s1 s1' s2 Hs _ [Hinv [Hh [g Hg]]].
    exists s2; split; [apply NilAction; reflexivity |].
    destruct (applyRedirect_char s1 s1' Hs) as [Erf [Ewb [Emem [Ede [Edm [Emd Hif]]]]]].
    destruct (validA s1) eqn:Hv; destruct Hif as [Efe Eex].
    - erewrite effS_true in Hg by exact Hv.
      assert (Hv' : validA s1' = false)
        by (unfold iRedirValid, ex_redirValid, ex_redirect; rewrite Eex; reflexivity).
      (* a later slot never waits with a redirect pending: the hand-off is not in use *)
      assert (Hh' : ACC HandInv s1').
      { intros Hcp Hfs.
        rewrite Eex in Hcp, Hfs; cbn [ex_canProceed ex_firstSlot ex_withRedirect ex_withExecEpoch Fst Snd] in Hcp, Hfs.
        destruct (Hh Hcp Hfs) as [_ [_ [_ [C _]]]]; rewrite Hv in C; discriminate C. }
      destruct Hinv as [_ [_ I3]]; destruct (I3 Hv) as [Ip _].
      split; [| split; [exact Hh' |]].
      + split; [intros _ | split; [intros _ Hfip | intros C; rewrite Hv' in C; discriminate C]].
        * unfold iFetchPcc, iPcc; rewrite Efe, Erf; exact Ip.
        * unfold iFetchFip; rewrite Efe.
          unfold iFenceIPending in Hfip; rewrite Eex in Hfip; exact Hfip.
      + exists g; erewrite effS_false by exact Hv'.
        apply (FEXT g (applyPA s1) s1' s2); try assumption.
        * rewrite Efe; reflexivity.
        * unfold iExecEpoch; rewrite Eex; reflexivity.
        * unfold iFenceIPending; rewrite Eex; reflexivity.
    - erewrite effS_false in Hg by exact Hv.
      assert (Hv' : validA s1' = false) by (unfold iRedirValid; rewrite Eex; exact Hv).
      assert (Hh' : ACC HandInv s1') by exact (ACC HandInv_eq s1 s1' Eex Ede Erf Edm Emem Hh).
      destruct Hinv as [I1 [I2 _]].
      split; [| split; [exact Hh' |]].
      + split; [intros _ | split; [intros _ Hfip | intros C; rewrite Hv' in C; discriminate C]].
        * unfold iFetchPcc, iPcc; rewrite Efe, Erf; exact (I1 Hv).
        * unfold iFetchFip; rewrite Efe.
          unfold iFenceIPending in Hfip; rewrite Eex in Hfip; exact Hfip.
      + exists g; erewrite effS_false by exact Hv'.
        apply (FEXT g s1 s1' s2); try assumption.
        * rewrite Efe; reflexivity.
        * unfold iExecEpoch; rewrite Eex; reflexivity.
        * unfold iFenceIPending; rewrite Eex; reflexivity.
  Qed.

End RedirStep.
