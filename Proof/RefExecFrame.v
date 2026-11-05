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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel DecodeFacts SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead RefSpecFetch RefReplay.
From Cheriot.Proof Require Import RefExecAux.
From Stdlib Require Import Permutation.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7 FRAME & INVARIANT LEMMAS (`RefExecFrame.v`)
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Device Sample Intro Lemmas --- *)

Lemma clintSample_intro :
  forall env (xs : TS (Node "clint" clintChildren)),
    SemAction env (clintSampleMtip type) xs
      (clintWithSampled (orb (clintSampled xs) (clintMtip xs)) xs) Zmod.zero.
Proof.
  intros env xs; rewrite SemAction_iff_evalActionPropGen.
  destruct xs as [a [b [c [d []]]]].
  unfold clintSampleMtip, clintWithSampled, clintMtip, clintSampled; cbn.
  destruct c, d; split; reflexivity.
Qed.

Lemma plicSample_intro :
  forall n env (xs : TS (plicTree n)),
    SemAction env (@plicSampleMeip n type) xs
      (plicWithMeip (orb (plicMeipOf xs) (evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf xs))))) xs) Zmod.zero.
Proof.
  intros n env xs; rewrite SemAction_iff_evalActionPropGen.
  destruct xs as [pr [pe [en [th [cl [me [insv [ua []]]]]]]]].
  unfold plicSampleMeip, plicWithMeip, plicMeipOf, plicClaimOf; cbn -[evalExpr].
  destruct (evalExpr (isNotZero (Var type (Bit Xlen) cl))), me; split; reflexivity.
Qed.

Lemma isNotZero_of_neq_zero :
  forall {sz : Z} (x : bits sz),
    x <> Zmod.zero ->
    evalExpr (isNotZero (Var type (Bit sz) x)) = true.
Proof.
  intros sz x Hneq.
  destruct (evalExpr (isNotZero (Var type (Bit sz) x))) eqn:E; [reflexivity |].
  exfalso; apply Hneq.
  change (negb (evalExpr (isZero (Var type (Bit sz) x))) = false) in E.
  apply negb_false_iff in E.
  assert (H' : Zmod.eqb x Zmod.zero = true) by (rewrite <- E; reflexivity).
  apply Zmod.eqb_eq in H'; exact H'.
Qed.

(* --- 1b. Scoreboard Writer Lists --- *)

Lemma d2aWriters_cons :
  forall j l, d2aWriters (j :: l) =
              ((if Zmod.eqb (d2aDst j) Zmod.zero then [] else [d2aDst j]) ++ d2aWriters l)%list.
Proof.
  intros j l; unfold d2aWriters; cbn [map filter].
  destruct (Zmod.eqb (d2aDst j) Zmod.zero); reflexivity.
Qed.

Lemma d2aWriters_app :
  forall l1 l2, d2aWriters (l1 ++ l2) = (d2aWriters l1 ++ d2aWriters l2)%list.
Proof. intros l1 l2; unfold d2aWriters; rewrite map_app, filter_app; reflexivity. Qed.

Lemma d2aWriters_nz : forall l d, In d (d2aWriters l) -> Zmod.eqb d Zmod.zero = false.
Proof.
  intros l d Hin; unfold d2aWriters in Hin; apply filter_In in Hin as [_ H].
  apply negb_true_iff in H; exact H.
Qed.

(* The ALU's `dstIdx` of a decode-to-ALU entry is the register the scoreboard tracks for it *)
Lemma d2aDst_aluDstIdx :
  forall pcc j, aluDstIdx (evalAluOut pcc (daAluIn j)) = d2aDst j.
Proof. intros pcc j; rewrite wrappedAlu_dstIdx; reflexivity. Qed.

(* Clearing the head entry `j`'s wait bit: a bit is then set exactly for the other pending writers *)
Lemma waitBits_clear_head :
  forall (wb : TS waitBitsTree) (ow : list (bits RegIdxSzReal)) j tail,
    (forall r, In r ow -> Zmod.eqb r Zmod.zero = false) ->
    NoDup (ow ++ d2aWriters (j :: tail))%list ->
    (forall r, readWaitBit r wb = true <-> In r (ow ++ d2aWriters (j :: tail))%list) ->
    forall r,
      readWaitBit r (evalSetDstWaitBits (aluInWritesCd (daAluIn j)) (aluInCd (daAluIn j)) false wb) = true <->
      In r (ow ++ d2aWriters tail)%list.
Proof.
  intros wb ow j tail Hnzo Hnd Hwb r.
  specialize (Hwb r).
  change (readWaitBit r) with (evalReadWaitBit r) in *.
  rewrite evalReadWaitBit_setDst_false.
  destruct (andb (aluInWritesCd (daAluIn j)) (Zmod.eqb r (aluInCd (daAluIn j)))) eqn:Ec; cbv beta iota.
  - (* the head's register: cleared, and no other pending writer has it *)
    split; [discriminate | intros Hin; exfalso].
    apply andb_prop in Ec as [Ew Eq]; apply Zmod.eqb_eq in Eq; subst r.
    assert (Ed : d2aDst j = aluInCd (daAluIn j)) by (unfold d2aDst; rewrite Ew; reflexivity).
    assert (Hnz : Zmod.eqb (aluInCd (daAluIn j)) Zmod.zero = false).
    { apply in_app_or in Hin as [H | H]; [exact (Hnzo _ H) | exact (d2aWriters_nz _ _ H)]. }
    rewrite d2aWriters_cons, Ed, Hnz in Hnd; cbn [app] in Hnd.
    exact (NoDup_remove_2 _ _ _ Hnd Hin).
  - (* another register: its bit is unchanged, and it is not the head's *)
    split; intros Hin.
    + apply Hwb in Hin; rewrite d2aWriters_cons in Hin.
      apply in_app_or in Hin as [H | H]; apply in_or_app; [left; exact H |].
      apply in_app_or in H as [H | H]; [exfalso | right; exact H].
      destruct (Zmod.eqb (d2aDst j) Zmod.zero) eqn:Ez; [destruct H |].
      destruct H as [<- | []].
      unfold d2aDst in Ec, Ez; destruct (aluInWritesCd (daAluIn j)); cbv beta iota in Ec, Ez.
      * rewrite Zmod.eqb_refl in Ec; discriminate Ec.
      * rewrite Zmod.eqb_refl in Ez; discriminate Ez.
    + apply Hwb; rewrite d2aWriters_cons.
      apply in_app_or in Hin as [H | H]; apply in_or_app; [left; exact H | right].
      apply in_or_app; right; exact H.
Qed.

Section ExecFrame.
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

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation IState := (TS ITree).
  Local Abbreviation SState := (TS STree).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).

  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELNE :=
    (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs).

  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA :=
    (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA :=
    (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemA :=
    (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA :=
    (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchA :=
    (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA :=
    (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecA :=
    (iExec pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA :=
    (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iExecEpochA :=
    (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA :=
    (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iD2aA :=
    (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmBufA :=
    (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA :=
    (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sClintA := (sClint pcAddrInit pre post revBase revPfB revPfA clintS).
  Local Abbreviation sPlicA := (sPlic pcAddrInit pre post revBase revPfB revPfA plicS).
  Local Abbreviation iClintA :=
    (iClint pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clint).
  Local Abbreviation iPlicA :=
    (iPlic pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA plic).
  Local Abbreviation olderWritersA :=
    (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Local Abbreviation sRevR := (specRevRegion revBase revPfB revPfA).
  Local Abbreviation iRevR := (implRevRegion revBase revPfB revPfA).
  Local Abbreviation NPMS := (Spec.np_mem pcAddrInit specRegions).

  Lemma nth_spec_rev : nth_error specRegions (length pre) = Some sRevR.
  Proof. exact (nth_error_app_cons_len pre sRevR post). Qed.

  Lemma clintS_ne_rev : clintIdx clintS <> length pre.
  Proof.
    intros E; pose proof (pfClint clintS) as H; rewrite E, nth_spec_rev in H.
    discriminate H.
  Qed.

  Lemma plicS_ne_rev : plicIdx plicS <> length pre.
  Proof.
    intros E; pose proof (pfPlic plicS) as H; rewrite E, nth_spec_rev in H.
    discriminate H.
  Qed.

  Lemma clintS_ne_plicS : clintIdx clintS <> plicIdx plicS.
  Proof.
    intros E; pose proof (pfClint clintS) as H1; pose proof (pfPlic plicS) as H2.
    rewrite E, H2 in H1; discriminate H1.
  Qed.

  (* --- 2. 9-Subtree Impl State Extensionality for `RefRelG` and `RefRelNE` --- *)

  Lemma iFlush_ext :
    forall (s1 s1' : IState),
      iRfA s1' = iRfA s1 ->
      iMdA s1' = iMdA s1 ->
      iFlushA s1' = iFlushA s1.
  Proof.
    intros s1 s1' Erf Emd.
    unfold iFlush, flushMulDiv, flushMulDivOn.
    change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1')
      with (iRfA s1').
    change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1)
      with (iRfA s1).
    rewrite Erf, Emd; reflexivity.
  Qed.

  Lemma olderWriters_ext :
    forall (s1 s1' : IState),
      iDmA s1' = iDmA s1 ->
      iMdA s1' = iMdA s1 ->
      olderWritersA s1' = olderWritersA s1.
  Proof.
    intros s1 s1' Edm Emd.
    unfold olderWriters, dmInFlightDst, iDmBuf, iDmSt.
    change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1')
      with (iDmA s1').
    change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1)
      with (iDmA s1).
    rewrite Edm, Emd; reflexivity.
  Qed.

  (* The relation reads the fetch subtree only through these projections (not fetch's PCC and
   * fence.i copies, item 3.4) *)
  Local Abbreviation FPROJ s1 :=
    (fetch_pc pcAddrInit fetchCapacity instCapacity (iFetchA s1),
     fetch_predEpoch pcAddrInit fetchCapacity instCapacity (iFetchA s1),
     fetch_curParcelOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1),
     fetch_straddleOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1),
     fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1),
     fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).

  (* The equalities `RefRelNE_fetch_ext` assumes; one lemma per relation part below keeps each
   * kernel check small *)
  Local Abbreviation CR L := (L pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post
                                revBase revPfB revPfA).
  Local Abbreviation FEXT s1 s1' :=
    (iRfA s1' = iRfA s1 /\ iWbA s1' = iWbA s1 /\ iMemA s1' = iMemA s1 /\ FPROJ s1' = FPROJ s1 /\
     iDecodeA s1' = iDecodeA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1 /\
     iExecEpochA s1' = iExecEpochA s1 /\ iFenceIPendingA s1' = iFenceIPendingA s1).

  Ltac fext_intro s1 s1' :=
    intros [Erf [Ewb [Emem [Efp [Ede [Edm [Emd [Eep Efip]]]]]]]];
    injection Efp as Epc Epe Ecp Estr Efb Eib;
    pose proof (iFlush_ext s1 s1' Erf Emd) as Efl;
    pose proof (olderWriters_ext s1 s1' Edm Emd) as Eow;
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity);
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite Ede; reflexivity).

  Lemma fext_fence :
    forall g (s1 s1' : IState), FEXT s1 s1' -> CR FenceRel g s1 -> CR FenceRel g s1'.
  Proof.
    intros g s1 s1'; fext_intro s1 s1'; intros Hf.
    unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
           iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *;
      rewrite Ereg, Estr, Eib, Efb, Epe, Ed2a, Eep, Efip; exact Hf.
  Qed.

  Lemma fext_score :
    forall g (s1 s1' : IState), FEXT s1 s1' -> CR ScoreRel g s1 -> CR ScoreRel g s1'.
  Proof.
    intros g s1 s1'; fext_intro s1 s1'; intros Hs.
    unfold ScoreRel, daLive in *;
      rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
  Qed.

  Lemma fext_front :
    forall g (s1 s1' : IState) (s2 : SState), FEXT s1 s1' ->
      CR FrontRel initLine fwcs g s1 s2 -> CR FrontRel initLine fwcs g s1' s2.
  Proof.
    intros g s1 s1' s2; fext_intro s1 s1'; intros Hfr.
    (* rewrite each conjunct on its own: the motive of every rewrite is then that conjunct only *)
    unfold FrontRel in Hfr |- *; destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]];
      [ revert F1 | revert F2 | revert F3 | revert F4 | revert F5 | revert F6 | revert F7 ];
      unfold LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iPcc, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf;
      rewrite ?Erf, ?Ereg, ?Epc, ?Epe, ?Ecp, ?Estr, ?Efb, ?Eib, ?Ed2a, ?Eep; exact (fun H => H).
  Qed.

  Lemma fext_wf :
    forall g (s1 s1' : IState) (s2 : SState), FEXT s1 s1' -> CR WfRel g s1 s2 -> CR WfRel g s1' s2.
  Proof.
    intros g s1 s1' s2; fext_intro s1 s1'; intros Hw.
    unfold WfRel, iCurParcel, iFetchBuf, iPcc, liveInsts, daLive, aiLive, iInstBuf in *;
      rewrite ?Erf, ?Ed2a, ?Eep, ?Ecp, ?Efb, ?Eib, ?Ede, ?Edm, ?Emd, ?Ereg; exact Hw.
  Qed.

  Lemma RefRelNE_fetch_ext :
    forall g (s1 s1' : IState) (s2 : SState),
      iRfA s1' = iRfA s1 -> iWbA s1' = iWbA s1 -> iMemA s1' = iMemA s1 -> FPROJ s1' = FPROJ s1 ->
      iDecodeA s1' = iDecodeA s1 -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      iExecEpochA s1' = iExecEpochA s1 -> iFenceIPendingA s1' = iFenceIPendingA s1 ->
      RELNE g s1 s2 -> RELNE g s1' s2.
  Proof.
    intros g s1 s1' s2 Erf Ewb Emem Efp Ede Edm Emd Eep Efip H.
    pose proof (conj Erf (conj Ewb (conj Emem (conj Efp (conj Ede (conj Edm (conj Emd (conj Eep Efip))))))))
      as HX.
    pose proof (iFlush_ext s1 s1' Erf Emd) as Efl.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    destruct H as [Hrf Hm Hl Hrp Ha Hc Hd Hf Hs Hfr Hw Hrk].
    constructor.
    - unfold RfRel in *; rewrite Efl; exact Hrf.
    - unfold MemRelC in *; rewrite Ereg; exact Hm.
    - exact Hl.
    - exact Hrp.
    - eapply AccessRel_frame with (s1 := s1) (s2 := s2);
        try reflexivity;
        try (unfold iMemSt, iRequester, iReadRp, iRdBufs, iDmSt, iRevPhase, iRev, iRegions; rewrite ?Emem, ?Edm; reflexivity);
        exact Ha.
    - unfold CnwbRel in *; unfold iDmSt in *; rewrite Edm; exact Hc.
    - unfold DmQueueRel, iDmBuf in *; rewrite Edm; exact Hd.
    - exact (fext_fence g s1 s1' HX Hf).
    - exact (fext_score g s1 s1' HX Hs).
    - exact (fext_front g s1 s1' s2 HX Hfr).
    - exact (fext_wf g s1 s1' s2 HX Hw).
    - eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2);
        try reflexivity;
        try (unfold iRev, iRegions; rewrite Emem; reflexivity);
        exact Hrk.
  Qed.

  Lemma RefRelNE_impl_ext :
    forall g (s1 s1' : IState) (s2 : SState),
      iRfA s1' = iRfA s1 ->
      iWbA s1' = iWbA s1 ->
      iMemA s1' = iMemA s1 ->
      iFetchA s1' = iFetchA s1 ->
      iDecodeA s1' = iDecodeA s1 ->
      iDmA s1' = iDmA s1 ->
      iMdA s1' = iMdA s1 ->
      iExecEpochA s1' = iExecEpochA s1 ->
      iFenceIPendingA s1' = iFenceIPendingA s1 ->
      RELNE g s1 s2 ->
      RELNE g s1' s2.
  Proof.
    intros g s1 s1' s2 Erf Ewb Emem Efe Ede Edm Emd Eep Efip H.
    apply (RefRelNE_fetch_ext g s1 s1' s2 Erf Ewb Emem); try assumption.
    rewrite Efe; reflexivity.
  Qed.

  Lemma RefRelG_impl_ext :
    forall g (s1 s1' : IState) (s2 : SState),
      iRfA s1' = iRfA s1 ->
      iWbA s1' = iWbA s1 ->
      iMemA s1' = iMemA s1 ->
      iFetchA s1' = iFetchA s1 ->
      iDecodeA s1' = iDecodeA s1 ->
      iDmA s1' = iDmA s1 ->
      iMdA s1' = iMdA s1 ->
      iExecEpochA s1' = iExecEpochA s1 ->
      iFenceIPendingA s1' = iFenceIPendingA s1 ->
      RELG g s1 s2 ->
      RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 Erf Ewb Emem Efe Ede Edm Emd Eep Efip Hg.
    apply RefRelG_of_NE.
    - refine (RefRelNE_impl_ext g s1 s1' s2 Erf Ewb Emem Efe Ede Edm Emd Eep Efip _).
      eapply RefRelNE_of_G; exact Hg.
    - pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ He _ _ _ _ _ _ _ _]; exact He.
  Qed.

  Lemma RefRelG_fetch_ext :
    forall g (s1 s1' : IState) (s2 : SState),
      iRfA s1' = iRfA s1 -> iWbA s1' = iWbA s1 -> iMemA s1' = iMemA s1 -> FPROJ s1' = FPROJ s1 ->
      iDecodeA s1' = iDecodeA s1 -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      iExecEpochA s1' = iExecEpochA s1 -> iFenceIPendingA s1' = iFenceIPendingA s1 ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 Erf Ewb Emem Efp Ede Edm Emd Eep Efip Hg.
    apply RefRelG_of_NE.
    - refine (RefRelNE_fetch_ext g s1 s1' s2 Erf Ewb Emem Efp Ede Edm Emd Eep Efip _).
      eapply RefRelNE_of_G; exact Hg.
    - pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ He _ _ _ _ _ _ _ _]; exact He.
  Qed.

  (* --- 3. Scoreboard Writer Avoidance (`EntryAvoids_of_in_olderWriters`) --- *)

  Lemma ChainAvoids_app :
    forall (G1 G2 : list GItem) (d : bits RegIdxSzReal),
      ChainAvoids G1 d ->
      ChainAvoids G2 d ->
      ChainAvoids (G1 ++ G2)%list d.
  Proof.
    intros G1 G2 d H1 H2 e Hin.
    apply in_app_or in Hin as [Hin | Hin]; [exact (H1 e Hin) | exact (H2 e Hin)].
  Qed.

  Lemma EntryAvoids_of_in_olderWriters :
    forall g s1 j d2a_tail fo fo_tail (e : GEntry) (d : bits RegIdxSzReal),
      ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1 ->
      iD2aA s1 = j :: d2a_tail ->
      g_d2aFo pcAddrInit g = fo :: fo_tail ->
      daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 j = true ->
      ge_fetchOut e = fo ->
      aluDstIdx (ge_aluOut e) = decDst fo ->
      (Zmod.eqb d Zmod.zero = false -> In d (olderWritersA s1)) ->
      EntryAvoids e d.
  Proof.
    intros g s1 j d2a_tail fo fo_tail e d Hsc Ed2a Efo Hlive Hge Hdst Hin.
    destruct Hsc as [Hnd [_ [_ Hreg]]].
    assert (Eapp : iD2aA s1 = ([] ++ j :: d2a_tail)%list) by exact Ed2a.
    assert (Enth : nth_error (g_d2aFo pcAddrInit g) (length (@nil (type DecodeToAluEntry))) = Some fo)
      by (rewrite Efo; reflexivity).
    destruct (Hreg [] j d2a_tail fo Eapp Enth Hlive) as [Hrr [Hcs1 Hcs2]].
    unfold EntryAvoids; rewrite Hge, Hdst.
    split; [intros Hd; apply (Hcs1 d); [apply in_or_app; left; exact (Hin Hd) | exact Hd] |].
    split; [intros Hd; apply (Hcs2 d); [apply in_or_app; left; exact (Hin Hd) | exact Hd] |].
    intros Hd Hx Heq.
    pose proof (Hin Hd) as Hdin.
    unfold decDst in Heq; destruct (decWritesCd fo) eqn:Ew.
    - subst d; rewrite NoDup_app_iff in Hnd; destruct Hnd as [_ [_ Hdisj]].
      apply (Hdisj _ Hdin).
      assert (Ej : d2aDst j = instCd fo.(Snd).(Fst)).
      { unfold d2aDst; rewrite Hrr, regRead_writesCd, Ew; unfold aluInCd; rewrite regRead_inst; reflexivity. }
      rewrite Ed2a, d2aWriters_cons, Ej, Hd; left; reflexivity.
    - subst d; rewrite Zmod.eqb_refl in Hd; discriminate Hd.
  Qed.

  Local Abbreviation ScoreRelA :=
    (ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation daLiveA :=
    (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Lemma olderWriters_nz : forall (s1 : IState) d, In d (olderWritersA s1) -> Zmod.eqb d Zmod.zero = false.
  Proof.
    intros s1 d Hin; unfold olderWriters in Hin; apply filter_In in Hin as [_ H].
    apply negb_true_iff in H; exact H.
  Qed.

  (* The head `j` of the decode-to-ALU FIFO leaves it: its register is cleared (`rest` holds it)
   * or moves to the older writers; the live entries behind it read the same registers *)
  Lemma ScoreRel_pop :
    forall (g g' : Ghost) (s1 s1' : IState) (j : type DecodeToAluEntry) (tail : list (type DecodeToAluEntry))
           (fo0 : type FetchOut) (fo_tail : list (type FetchOut)) (rest : list (bits RegIdxSzReal)),
      ScoreRelA g s1 ->
      iD2aA s1 = j :: tail ->
      g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = tail ->
      g_d2aFo pcAddrInit g' = fo_tail ->
      Permutation (olderWritersA s1 ++ d2aWriters (j :: tail))%list (olderWritersA s1' ++ d2aWriters tail ++ rest)%list ->
      (forall r, readWaitBit r (iWbA s1') = true <-> In r (olderWritersA s1' ++ d2aWriters tail)%list) ->
      (forall r, In r (olderWritersA s1') -> In r (olderWritersA s1 ++ d2aWriters [j])%list) ->
      (forall x, In x tail -> daLiveA s1' x = true -> daLiveA s1 x = true) ->
      (forall l1 j2 l2 fo,
         tail = (l1 ++ j2 :: l2)%list ->
         nth_error fo_tail (length l1) = Some fo ->
         daLiveA s1' j2 = true ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs1 fo) ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs2 fo) ->
         evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) ->
      ScoreRelA g' s1'.
  Proof.
    intros g g' s1 s1' j tail fo0 fo_tail rest [Hnd [_ [Hlen Hreg]]] Ed2a Efo Ed2a' Efo' Hperm Hwb' Hold Hlv Hrr.
    unfold ScoreRel; cbv zeta; rewrite Ed2a', Efo'.
    rewrite Ed2a in Hnd, Hlen; rewrite Efo in Hlen; cbn [length] in Hlen; injection Hlen as Hlen'.
    split.
    - apply (Permutation_NoDup Hperm) in Hnd; rewrite app_assoc in Hnd; exact (NoDup_app_remove_r _ _ Hnd).
    - split; [exact Hwb' |]; split; [exact Hlen' |].
      intros l1 j2 l2 fo Hl1 Hnth Hlive.
      assert (Hl1s : iD2aA s1 = ((j :: l1) ++ j2 :: l2)%list) by (rewrite Ed2a, Hl1; reflexivity).
      assert (Hnths : nth_error (g_d2aFo pcAddrInit g) (length (j :: l1)) = Some fo) by (rewrite Efo; exact Hnth).
      assert (Hin2 : In j2 tail) by (rewrite Hl1; apply in_or_app; right; left; reflexivity).
      destruct (Hreg (j :: l1) j2 l2 fo Hl1s Hnths (Hlv j2 Hin2 Hlive)) as [Hrr0 [Hc1 Hc2]].
      split; [rewrite (Hrr l1 j2 l2 fo Hl1 Hnth Hlive Hc1 Hc2); exact Hrr0 |].
      assert (Hsub : forall d, In d (olderWritersA s1' ++ d2aWriters l1)%list ->
                               In d (olderWritersA s1 ++ d2aWriters (j :: l1))%list).
      { change (j :: l1) with ([j] ++ l1)%list; rewrite d2aWriters_app.
        intros d Hd; apply in_app_or in Hd as [Hd | Hd].
        - apply Hold in Hd; apply in_app_or in Hd as [Hd | Hd]; apply in_or_app;
            [left; exact Hd | right; apply in_or_app; left; exact Hd].
        - apply in_or_app; right; apply in_or_app; right; exact Hd. }
      split; intros d Hd; [exact (Hc1 d (Hsub d Hd)) | exact (Hc2 d (Hsub d Hd))].
  Qed.

  (* --- 4. Spec Interrupt Latch Catch-Up (`catchup_mtip`, `catchup_meip`, `catchup_latches`) --- *)

  Lemma SemAction_specDevStep_intro_local :
    forall env idx r0 (pf : nth_error specRegions idx = Some r0) (act : Action type (memRegionTree r0) (Bit 0))
           (s2 : SState) x' v,
      (forall envR, SemAction envR act (regionStateAt memRegionTree idx specRegions r0 pf (sMemA s2)) x' v) ->
      SemAction env (liftAction NPMS (@nthRegionAction type idx specRegions r0 pf (Bit 0) act)) s2
        (writeSubTreeState NPMS s2 (updRegionStateAt memRegionTree idx specRegions r0 pf (sMemA s2) x')) v.
  Proof.
    intros env idx r0 pf act s2 x' v Hx.
    apply SemAction_liftAction_iff; eexists; split; [| reflexivity].
    unfold nthRegionAction.
    apply SemAction_genNthRegionAction_iff; eexists; split; [apply Hx | reflexivity].
  Qed.

  Lemma MemRelPre_upd_spec :
    forall cp pp sRev iRev post0 l i idxS idxI r0S r0I
           (pfS : nth_error (l ++ sRev :: post0) idxS = Some r0S)
           (pfI : nth_error (l ++ iRev :: post0) idxI = Some r0I)
           (ms : TS (specMemTree (l ++ sRev :: post0))) (mi : TS (implRegionsTree (l ++ iRev :: post0)))
           v,
      idxI = idxS ->
      idxS <> length l ->
      (forall x y, RegionRelAt cp pp (i + idxS) r0S x y) ->
      MemRelPre cp pp i l sRev iRev post0 ms mi ->
      MemRelPre cp pp i l sRev iRev post0
        (updRegionStateAt memRegionTree idxS (l ++ sRev :: post0) r0S pfS ms v) mi.
  Proof.
    intros cp pp sRev iRev post0 l i idxS idxI r0S r0I pfS pfI ms mi v E Hne Htriv H.
    pose proof (MemRelPre_upd2 cp pp sRev iRev post0 l i idxS idxI r0S r0I pfS pfI ms mi
                  v (regionStateAt implMemRegionTree idxI (l ++ iRev :: post0) r0I pfI mi) E Hne Htriv H) as H'.
    rewrite updRegionStateAt_regionStateAt in H'; exact H'.
  Qed.

  Lemma catchup_mtip :
    forall g (s1 : IState) (s2 : SState),
      g_chain pcAddrInit g = [] ->
      RELG g s1 s2 ->
      exists s2' : SState,
        SemActions envS specActs s2 s2' /\
        RELG g s1 s2' /\
        clintSampled (sClintA s2') = clintSampled (iClintA s1) /\
        sPlicA s2' = sPlicA s2.
  Proof.
    intros g s1 s2 Hch Hg.
    destruct (Bool.bool_dec (clintSampled (sClintA s2)) (clintSampled (iClintA s1))) as [Heq | Hneq].
    - exists s2; split; [apply NilAction; reflexivity |].
      split; [exact Hg | split; [exact Heq | reflexivity]].
    - pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ _ _ _ _ _ _ _ _].
      unfold MemRelC, MemRel, DevInv in Hm.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
      set (xs := sClintA s2) in *.
      set (xi := iClintA s1) in *.
      change (ClintRel xs xi) in Hcl.
      change (ClintInv xi) in Hci.
      assert (Hs_false : clintSampled xs = false).
      { destruct (clintSampled xs) eqn:Es; [| reflexivity].
        pose proof (proj2 Hcl Es) as Ei; rewrite Ei in Hneq; exfalso; apply Hneq; reflexivity. }
      assert (Hi_true : clintSampled xi = true).
      { destruct (clintSampled xi); [reflexivity | exfalso; apply Hneq; exact Hs_false]. }
      pose proof (Hci Hi_true) as Hmtip_i.
      assert (Hmtip_s : clintMtip xs = true).
      { destruct Hcl as [Hstruct _].
        rewrite Hstruct; exact Hmtip_i. }
      set (xs' := clintWithSampled (orb (clintSampled xs) (clintMtip xs)) xs).
      set (ms' := updRegionStateAt memRegionTree (clintIdx clintS) specRegions (clintRegion clintS)
                    (pfClint clintS) (sMemA s2) xs').
      set (s2' := writeSubTreeState NPMS s2 ms').
      assert (Es : sMemA s2' = ms') by reflexivity.
      exists s2'; split.
      + eapply ConsAction;
          [apply (In_specSampleMtipStep_spec pcAddrInit config specRegions clintS revSpec plicS) | |
           apply NilAction; reflexivity].
        unfold specSampleMtipStep, clintSampleMtipAction, clintAction.
        apply SemAction_specDevStep_intro_local.
        intros envR; apply clintSample_intro.
      + assert (Hcl' : ClintRel xs' xi).
        { split.
          - destruct Hcl as [Hstruct _].
            unfold xs'; rewrite Hstruct; reflexivity.
          - intros _; exact Hi_true. }
        assert (Hrel' : RELG g s1 s2').
        { eapply RefRelG_regions_frame with (s1 := s1) (s2 := s2) (ms' := ms');
            [reflexivity | reflexivity | | | | | | | exact Hg].
          - intros P; reflexivity.
          - reflexivity.
          - intros L; rewrite Es;
              exact (lineContent_upd initLine specRegions (clintIdx clintS) (clintRegion clintS) (pfClint clintS) (sMemA s2) xs' L I).
          - rewrite Es;
              exact (FetchViewExt_upd specRegions (clintIdx clintS) (clintRegion clintS) (pfClint clintS) (sMemA s2) xs' I).
          - unfold MemRelC, MemRel, DevInv.
            rewrite Es; unfold ms', specClintState, specPlicState, specRevState.
            rewrite regionStateAt_updRegionStateAt.
            rewrite !regionStateAt_upd_other by first [exact clintS_ne_plicS | exact clintS_ne_rev].
            refine (conj (conj _ (conj Hcl' (conj Hpl Hrv))) (conj (conj Hci Hpi) _)).
            + exact (MemRelPre_upd_spec (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                       (clintIdx clintS) (clintIdx clint) (clintRegion clintS) (clintRegion clint)
                       (pfClint clintS) (pfClint clint) _ _ _ HclintIdx clintS_ne_rev
                       (fun x y => or_introl eq_refl) Hpre).
            + exact (SnapshotOK_upd specRegions fwcs (clintIdx clintS) (clintRegion clintS) (pfClint clintS) (sMemA s2) xs' I Hsnap).
          - unfold LatchRel; rewrite Hch; intros e []. }
        split; [exact Hrel' |]; split.
        * unfold sClint; rewrite Es; unfold ms', specClintState.
          rewrite regionStateAt_updRegionStateAt.
          unfold xs'; rewrite Hmtip_s, orb_true_r, Hi_true; reflexivity.
        * unfold sPlic; rewrite Es; unfold ms', specPlicState.
          rewrite regionStateAt_upd_other by exact clintS_ne_plicS.
          reflexivity.
  Qed.

  Lemma PlicRel_catchup :
    forall n1 n2 (xs : TS (plicTree n1)) (xi : TS (plicTree n2)),
      PlicRel n1 n2 xs xi ->
      PlicInv xi ->
      plicMeipOf xs <> plicMeipOf xi ->
      evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf xs))) = true /\
      plicMeipOf xi = true /\
      PlicRel n1 n2
        (plicWithMeip (orb (plicMeipOf xs) (evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf xs))))) xs) xi.
  Proof.
    intros n1 n2 xs xi [e [H1 H2]] Hpi Hneq; subst n2; cbn [eq_rect] in *.
    assert (Hs_false : plicMeipOf xs = false).
    { destruct (plicMeipOf xs); [| reflexivity].
      pose proof (H2 eq_refl) as Ei; rewrite Ei in Hneq; exfalso; apply Hneq; reflexivity. }
    assert (Hi_true : plicMeipOf xi = true).
    { destruct (plicMeipOf xi); [reflexivity | exfalso; apply Hneq; exact Hs_false]. }
    assert (Hnz : evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf xs))) = true).
    { apply isNotZero_of_neq_zero; rewrite H1; exact (Hpi Hi_true). }
    split; [exact Hnz | split; [exact Hi_true |]].
    exists eq_refl; cbn [eq_rect]; split; [rewrite H1; reflexivity | intros _; exact Hi_true].
  Qed.

  Lemma catchup_meip :
    forall g (s1 : IState) (s2 : SState),
      g_chain pcAddrInit g = [] ->
      RELG g s1 s2 ->
      exists s2' : SState,
        SemActions envS specActs s2 s2' /\
        RELG g s1 s2' /\
        plicMeipOf (sPlicA s2') = plicMeipOf (iPlicA s1) /\
        sClintA s2' = sClintA s2.
  Proof.
    intros g s1 s2 Hch Hg.
    destruct (Bool.bool_dec (plicMeipOf (sPlicA s2)) (plicMeipOf (iPlicA s1))) as [Heq | Hneq].
    - exists s2; split; [apply NilAction; reflexivity |].
      split; [exact Hg | split; [exact Heq | reflexivity]].
    - pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ _ _ _ _ _ _ _ _].
      unfold MemRelC, MemRel, DevInv in Hm.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
      set (xs := sPlicA s2) in *.
      set (xi := iPlicA s1) in *.
      destruct (PlicRel_catchup _ _ xs xi Hpl Hpi Hneq) as [Hnz_s [Hi_true Hpl']].
      set (xs' := plicWithMeip (orb (plicMeipOf xs) (evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf xs))))) xs).
      set (ms' := updRegionStateAt memRegionTree (plicIdx plicS) specRegions (plicRegion plicS)
                    (pfPlic plicS) (sMemA s2) xs').
      set (s2' := writeSubTreeState NPMS s2 ms').
      assert (Es : sMemA s2' = ms') by reflexivity.
      exists s2'; split.
      + eapply ConsAction;
          [apply (In_specPlicSampleMeipStep_spec pcAddrInit config specRegions clintS revSpec plicS) | |
           apply NilAction; reflexivity].
        unfold specPlicSampleMeipStep, plicSampleMeipStep, plicAction.
        apply SemAction_specDevStep_intro_local.
        intros envR; apply plicSample_intro.
      + assert (Hrel' : RELG g s1 s2').
        { eapply RefRelG_regions_frame with (s1 := s1) (s2 := s2) (ms' := ms');
            [reflexivity | reflexivity | | | | | | | exact Hg].
          - intros P; reflexivity.
          - reflexivity.
          - intros L; rewrite Es;
              exact (lineContent_upd initLine specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (sMemA s2) xs' L I).
          - rewrite Es;
              exact (FetchViewExt_upd specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (sMemA s2) xs' I).
          - unfold MemRelC, MemRel, DevInv.
            rewrite Es; unfold ms', specClintState, specPlicState, specRevState.
            rewrite regionStateAt_updRegionStateAt.
            rewrite !regionStateAt_upd_other by first [exact (not_eq_sym clintS_ne_plicS) | exact plicS_ne_rev].
            refine (conj (conj _ (conj Hcl (conj Hpl' Hrv))) (conj (conj Hci Hpi) _)).
            + exact (MemRelPre_upd_spec (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                       (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
                       (pfPlic plicS) (pfPlic plic) _ _ _ HplicIdx plicS_ne_rev
                       (fun x y => or_intror (or_introl eq_refl)) Hpre).
            + exact (SnapshotOK_upd specRegions fwcs (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (sMemA s2) xs' I Hsnap).
          - unfold LatchRel; rewrite Hch; intros e []. }
        split; [exact Hrel' |]; split.
        * unfold sPlic; rewrite Es; unfold ms', specPlicState.
          rewrite regionStateAt_updRegionStateAt.
          unfold xs'; rewrite Hnz_s, orb_true_r, Hi_true; reflexivity.
        * unfold sClint; rewrite Es; unfold ms', specClintState.
          rewrite regionStateAt_upd_other by exact (not_eq_sym clintS_ne_plicS).
          reflexivity.
  Qed.

  Theorem catchup_latches :
    forall g (s1 : IState) (s2 : SState),
      g_chain pcAddrInit g = [] ->
      RELG g s1 s2 ->
      exists s2' : SState,
        SemActions envS specActs s2 s2' /\
        RELG g s1 s2' /\
        plicMeipOf (sPlicA s2') = plicMeipOf (iPlicA s1) /\
        clintSampled (sClintA s2') = clintSampled (iClintA s1).
  Proof.
    intros g s1 s2 Hch Hg.
    destruct (catchup_mtip g s1 s2 Hch Hg) as [s2m [Hsm [Hgm [Hmt _]]]].
    destruct (catchup_meip g s1 s2m Hch Hgm) as [s2' [Hse [Hg' [Hme Ecl]]]].
    exists s2'; split; [eapply SemActions_trans; [exact Hsm | exact Hse] |].
    split; [exact Hg' | split; [exact Hme | rewrite Ecl; exact Hmt]].
  Qed.

End ExecFrame.
