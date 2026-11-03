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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute SimDataMem GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker.
From Cheriot.Proof Require Import RefExecAux RefExecLive RefLoadCommit RefDmImpl RefDmStep ImplStagedProof ImplMulDivProof RefMdEngine RefMdRules.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.


(* ===========================================================================
 * MILESTONE 5: THE MULDIV RULES (RELATION SIDE)
 * ===========================================================================
 * - `RefRelG_mdFrame`: a step that only changes the mulDiv subtree, keeps its flush entries and
 *   its well-formedness.
 * - `RefRelG_mdWb`: a write-back of the flush entry `(d, v)`: `d` gets `v`, its wait bit is
 *   cleared and the entry leaves the flush. The spec stutters in both. *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma flushMulDivCaps_app :
  forall pcAddrInit l1 l2 (rf : RfState pcAddrInit),
    flushMulDivCaps pcAddrInit (l1 ++ l2) rf = flushMulDivCaps pcAddrInit l2 (flushMulDivCaps pcAddrInit l1 rf).
Proof.
  intros pcAddrInit l1; induction l1 as [| [m c] l1 IH]; intros l2 rf; [reflexivity |].
  cbn [app flushMulDivCaps]; apply IH.
Qed.

Definition nzB (d : bits RegIdxSzReal) : bool := negb (Zmod.eqb d Zmod.zero).

Lemma wbClr_iff :
  forall (d : bits RegIdxSzReal) (X Y : list (bits RegIdxSzReal)) wb,
    NoDup (X ++ (if nzB d then [d] else []) ++ Y)%list ->
    (forall r, evalReadWaitBit r wb = true <-> In r (X ++ (if nzB d then [d] else []) ++ Y)%list) ->
    forall r, evalReadWaitBit r (wbClr d wb) = true <-> In r (X ++ Y)%list.
Proof.
  intros d X Y wb Hnd Hwb r; unfold wbClr; fold (nzB d).
  destruct (nzB d) eqn:Ez; cbn [app] in Hnd, Hwb; [| exact (Hwb r)].
  assert (Hdz : Zmod.eqb d Zmod.zero = false) by (unfold nzB in Ez; apply negb_true_iff; exact Ez).
  destruct (Zmod.eqb r d) eqn:Er.
  - apply Zmod.eqb_eq in Er; subst r.
    rewrite (evalReadWaitBit_write_same d false _ Hdz).
    split; [discriminate | intros Hin; exfalso].
    exact (NoDup_remove_2 _ _ _ Hnd Hin).
  - assert (Hne : r <> d) by (intros E; subst r; rewrite Zmod.eqb_refl in Er; discriminate Er).
    rewrite (evalReadWaitBit_write_other r d false _ Hne), Hwb.
    rewrite !in_app_iff; cbn [In].
    split; [intros [H | [E | H]]; [left; exact H | exfalso; exact (Hne (eq_sym E)) | right; exact H] |].
    intros [H | H]; [left; exact H | right; right; exact H].
Qed.

Lemma filter_split :
  forall {B : Type} (A : list (bits RegIdxSzReal)) (l1 l2 : list (bits RegIdxSzReal * B)) d v,
    filter nzB (A ++ map fst (l1 ++ (d, v) :: l2))%list =
    (filter nzB (A ++ map fst l1) ++ (if nzB d then [d] else []) ++ filter nzB (map fst l2))%list.
Proof.
  intros B A l1 l2 d v; rewrite map_app, app_assoc, filter_app; cbn [map fst filter].
  destruct (nzB d); reflexivity.
Qed.

Lemma filter_split' :
  forall {B : Type} (A : list (bits RegIdxSzReal)) (l1 l2 : list (bits RegIdxSzReal * B)),
    filter nzB (A ++ map fst (l1 ++ l2))%list = (filter nzB (A ++ map fst l1) ++ filter nzB (map fst l2))%list.
Proof. intros B A l1 l2; rewrite map_app, app_assoc, filter_app; reflexivity. Qed.

Lemma In_drop_mid2 :
  forall (d x : bits RegIdxSzReal) (X Y Z : list (bits RegIdxSzReal)),
    In x ((X ++ Y) ++ Z)%list -> In x ((X ++ (if nzB d then [d] else []) ++ Y) ++ Z)%list.
Proof.
  intros d x X Y Z H; rewrite !in_app_iff in H |- *; destruct (nzB d); cbn [app In]; tauto.
Qed.

Lemma NoDup_drop_mid :
  forall (d : bits RegIdxSzReal) (X Y : list (bits RegIdxSzReal)),
    NoDup (X ++ (if nzB d then [d] else []) ++ Y)%list -> NoDup (X ++ Y)%list.
Proof.
  intros d X Y H; destruct (nzB d); cbn [app] in H; [exact (NoDup_remove_1 _ _ _ H) | exact H].
Qed.

Lemma In_drop_mid :
  forall (d x : bits RegIdxSzReal) (X Y : list (bits RegIdxSzReal)),
    In x (X ++ Y)%list -> In x (X ++ (if nzB d then [d] else []) ++ Y)%list.
Proof.
  intros d x X Y H; rewrite in_app_iff in H |- *; rewrite in_app_iff.
  destruct H as [H | H]; [left; exact H | right; right; exact H].
Qed.

Section MdStep.
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
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation GhostT := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation DWS :=
    (DmWbStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA := (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA := (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA := (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmBufA := (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA := (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iPccA := (iPcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA := (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iD2aA := (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecEpochA := (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA := (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation olderWritersA := (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation dmInFlightDstA := (dmInFlightDst pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PortsQuietA := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation revNotReadingA := (revNotReading pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation EXTA md := (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode md).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind.

  Local Abbreviation MDWF := (MulDivWf mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation MDT := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation CORE s1 := (impl_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1).

  (* The state with the mulDiv subtree replaced *)
  Definition mdSet (s1 : IState) (smd : TS MDT) : IState :=
    (core_withMulDiv _ _ _ _ _ _ _ _ (CORE s1) smd ,, s1.(Snd)).

  (* The state after a mulDiv write-back of `v` to `d` *)
  Definition mdWbSet (s1 : IState) (smd : TS MDT) (d : bits RegIdxSzReal) (v : type FullECapWithTag) : IState :=
    (core_withWaitBits _ _ _ _ _ _ _ _
       (core_withRf _ _ _ _ _ _ _ _ (core_withMulDiv _ _ _ _ _ _ _ _ (CORE s1) smd) (writeGprVal pcAddrInit d v (iRfA s1)))
       (wbClr d (iWbA s1)) ,, s1.(Snd)).

  Lemma RefRelG_mdFrame :
    forall (g : GhostT) (s1 : IState) (s2 : SState) smd,
      RELG g s1 s2 -> MDWF smd -> EXTA smd = EXTA (iMdA s1) ->
      RELG g (mdSet s1 smd) s2.
  Proof.
    intros g s1 s2 smd Hg Hwf Hex.
    assert (Emd : iMdA (mdSet s1 smd) = smd) by reflexivity.
    assert (Eflush : iFlushA (mdSet s1 smd) = iFlushA s1).
    { unfold iFlush, flushMulDiv, flushMulDivOn; rewrite Emd, Hex; reflexivity. }
    assert (Eow : olderWritersA (mdSet s1 smd) = olderWritersA s1).
    { unfold olderWriters; rewrite Emd, Hex; reflexivity. }
    destruct Hg as [Hrf Hm Hl Hrpl He Ha Hc Hd Hf Hs Hfr Hwf0 Hrk].
    constructor.
    - unfold RfRel in *; rewrite Eflush; exact Hrf.
    - exact Hm.
    - exact Hl.
    - exact Hrpl.
    - exact He.
    - exact Ha.
    - exact Hc.
    - exact Hd.
    - exact Hf.
    - unfold ScoreRel in *; rewrite Eow, Eflush; exact Hs.
    - exact Hfr.
    - destruct Hwf0 as [W1 [W2 [W3 [W4 [_ W6]]]]].
      exact (conj W1 (conj W2 (conj W3 (conj W4 (conj Hwf W6))))).
    - exact Hrk.
  Qed.

  Lemma RefRelG_mdWb :
    forall (g : GhostT) (s1 : IState) (s2 : SState) smd l1 l2 d v,
      RELG g s1 s2 -> MDWF smd ->
      EXTA (iMdA s1) = (l1 ++ (d, v) :: l2)%list -> EXTA smd = (l1 ++ l2)%list ->
      RELG g (mdWbSet s1 smd d v) s2.
  Proof.
    intros g s1 s2 smd l1 l2 d v Hg Hwf Hex1 Hex2.
    set (s1' := mdWbSet s1 smd d v).
    assert (Emd : iMdA s1' = smd) by reflexivity.
    assert (Erf : iRfA s1' = writeGprVal pcAddrInit d v (iRfA s1)) by reflexivity.
    assert (Ewb : iWbA s1' = wbClr d (iWbA s1)) by reflexivity.
    assert (Epcc : iPccA s1' = iPccA s1) by exact (readPcc_writeGprVal pcAddrInit d v (iRfA s1)).
    set (A := (dmInFlightDstA s1 ++ map mrDst (filter (fun q => opIsLoad (mrOp q)) (iDmBufA s1)))%list).
    set (X := filter nzB (A ++ map fst l1)).
    set (Y := filter nzB (map fst l2)).
    assert (Eow : olderWritersA s1 = (X ++ (if nzB d then [d] else []) ++ Y)%list).
    { unfold olderWriters; rewrite Hex1, app_assoc; exact (filter_split A l1 l2 d v). }
    assert (Eow' : olderWritersA s1' = (X ++ Y)%list).
    { unfold olderWriters; rewrite Emd, Hex2, app_assoc; exact (filter_split' A l1 l2). }
    destruct Hg as [Hrf Hm Hl Hrpl He Ha Hc Hd Hf Hs Hfr Hwf0 Hrk].
    unfold ScoreRel in Hs; cbv zeta in Hs; rewrite Eow in Hs.
    destruct Hs as [S1 [S2 [S3 S4]]].
    rewrite <- !app_assoc in S1.
    assert (Hdist : forall m c, In (m, c) l1 -> Zmod.eqb d Zmod.zero = false -> Zmod.eqb m Zmod.zero = false -> m <> d).
    { intros m c Hmc Hdz Hmz E; subst m.
      assert (Ez : nzB d = true) by (unfold nzB; rewrite Hdz; reflexivity).
      rewrite Ez in S1; cbn [app] in S1.
      apply (NoDup_remove_2 _ _ _ S1); apply in_or_app; left.
      apply filter_In; split; [| exact Ez].
      apply in_or_app; right; apply in_map_iff; exists (d, c); split; [reflexivity | exact Hmc]. }
    assert (Eflush : iFlushA s1' = iFlushA s1).
    { unfold iFlush, flushMulDiv, flushMulDivOn.
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1') with (iRfA s1').
      change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1) with (iRfA s1).
      rewrite Erf, Emd, Hex1, Hex2, !flushMulDivCaps_app; cbn [flushMulDivCaps].
      rewrite flushMulDivCaps_writeGprVal; [reflexivity |].
      intros m c Hmc Hdz Hmz; exact (Hdist m c Hmc Hdz Hmz). }
    constructor.
    - unfold RfRel in *; rewrite Eflush; exact Hrf.
    - exact Hm.
    - exact Hl.
    - exact Hrpl.
    - exact He.
    - exact Ha.
    - exact Hc.
    - exact Hd.
    - exact Hf.
    - unfold ScoreRel; cbv zeta; rewrite Eow', Ewb, Eflush, <- !app_assoc.
      split; [exact (NoDup_drop_mid d X _ S1) |].
      split.
      + change (forall r, evalReadWaitBit r (wbClr d (iWbA s1)) = true <->
                          In r (X ++ Y ++ d2aWriters (iD2aA s1))%list).
        apply wbClr_iff; [exact S1 |].
        intros r; rewrite <- !app_assoc in S2; exact (S2 r).
      + split; [exact S3 |].
        intros k1 j k2 fo Hk Hn Hlv.
        destruct (S4 k1 j k2 fo Hk Hn Hlv) as [T1 [T2 T3]].
        split; [exact T1 |].
        split; intros x Hx; [apply T2 | apply T3]; apply In_drop_mid2; exact Hx.
    - unfold FrontRel, LiveChain, FrontierRel in *; rewrite !Epcc; exact Hfr.
    - unfold WfRel in *; rewrite Epcc.
      destruct Hwf0 as [W1 [W2 [W3 [W4 [_ W6]]]]].
      exact (conj W1 (conj W2 (conj W3 (conj W4 (conj Hwf W6))))).
    - exact Hrk.
  Qed.

  Hypothesis Hmd : Is_true (mulDivStagesDivideXlen mulStages divStages).

  Local Abbreviation NPCORE :=
    (Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation MDACTS :=
    (@mulDivStageActions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).

  (* Milestone 5: every mulDiv rule (issue, engine step, write-back); the spec stutters *)
  Theorem stepOK_mulDivStageActions :
    forall a, In a MDACTS ->
      StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs a.
  Proof.
    intros a Hin s1 s1' s2 Hsem [g Hg].
    exists s2; split; [apply NilAction; reflexivity |].
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [_ [Hwf _]]]]] _].
    unfold mulDivStageActions in Hin; apply in_map_iff in Hin as [cAct [<- Hc]].
    apply liftSem in Hsem; destruct Hsem as [c' [Hc' ->]].
    unfold mulDivRules in Hc; apply in_app_or in Hc as [Hc | Hc]; [| apply in_app_or in Hc as [Hc | Hc]].
    - unfold mulDivIssueCoreRules in Hc; apply in_map_iff in Hc as [r [<- Hr]].
      apply liftSem in Hc'; destruct Hc' as [smd' [Hr' ->]].
      destruct (md_rule_ok mulCapacity divCapacity mulStages divStages Hmd mulDivMode r
                  (in_or_app _ _ _ (or_introl Hr)) _ _ _ _ Hwf Hr') as [Hwf' Hex].
      exists g; exact (RefRelG_mdFrame g s1 s2 smd' Hg Hwf' Hex).
    - unfold mulDivStageRules in Hc; apply in_map_iff in Hc as [r [<- Hr]].
      apply liftSem in Hc'; destruct Hc' as [smd' [Hr' ->]].
      destruct (md_rule_ok mulCapacity divCapacity mulStages divStages Hmd mulDivMode r
                  (in_or_app _ _ _ (or_intror Hr)) _ _ _ _ Hwf Hr') as [Hwf' Hex].
      exists g; exact (RefRelG_mdFrame g s1 s2 smd' Hg Hwf' Hex).
    - assert (Hwb : forall popResp,
                 (forall env smd smd' r, MDWF smd -> SemAction env popResp smd smd' r ->
                    PopOK mulCapacity divCapacity mulStages divStages mulDivMode smd smd' r) ->
                 forall env, SemAction env
                   (@ImplMulDiv.mulDivWriteBack mulCapacity divCapacity mulStages divStages mulDivMode pcAddrInit
                      (withInst_BpTree bp) (implMemTree implRegions) (implFetchTree pcAddrInit fetchCapacity instCapacity)
                      (implDecodeTree decodeCapacity) implExecuteTree (implDataMemTree dataMemCapacity) type popResp)
                   (readSubTreeState NPCORE s1) c' Zmod.zero ->
                 RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                   clintS clint plicS plic initLine fwcs (writeSubTreeState NPCORE s1 c') s2).
      { intros popResp Hok env Hs.
        destruct (wb_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs) as [env' [smd' [res [Hp ->]]]].
        pose proof (Hok _ _ _ _ Hwf Hp) as Hpop; unfold PopOK in Hpop.
        destruct (res.(Snd).(Fst)).
        - destruct Hpop as [l1 [l2 [E1 [E2 Hwf']]]]; exists g.
          pose proof (RefRelG_mdWb g s1 s2 smd' l1 l2 _ _ Hg Hwf' E1 E2) as R.
          match goal with |- _ (writeSubTreeState ?p ?s ?x) _ =>
            assert (Es : writeSubTreeState p s x = mdWbSet s1 smd' res.(Fst).(Fst) (mkMulDivCap res.(Fst).(Snd).(Fst)))
          end.
          { unfold mdWbSet, evalCommitMulDivWb, writeGprVal, wbClr.
            destruct (negb (Zmod.eqb res.(Fst).(Fst) Zmod.zero)); reflexivity. }
          rewrite Es; exact R.
        - subst smd'; exists g; exact (RefRelG_mdFrame g s1 s2 _ Hg Hwf eq_refl). }
      unfold mulDivWriteBackRules in Hc; destruct Hc as [<- | Hc].
      + exact (Hwb _ (popMul_ok mulCapacity divCapacity mulStages divStages mulDivMode) _ Hc').
      + assert (cAct = @divWriteBack mulCapacity divCapacity mulStages divStages mulDivMode pcAddrInit
                         (withInst_BpTree bp) (implMemTree implRegions) (implFetchTree pcAddrInit fetchCapacity instCapacity)
                         (implDecodeTree decodeCapacity) implExecuteTree (implDataMemTree dataMemCapacity) type) as ->.
        { clear - Hc; destruct mulDivMode; [destruct Hc as [<- | []]; reflexivity | destruct Hc as [<- | []]; reflexivity | destruct Hc]. }
        exact (Hwb _ (popDiv_ok mulCapacity divCapacity mulStages divStages mulDivMode) _ Hc').
  Qed.

End MdStep.
