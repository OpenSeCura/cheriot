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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic Spec.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefPeriph RefFrame.
From Cheriot.Proof Require Import RefSpecRead RefMemStep RefExecAux RefExecFrame RefExecFlush RefDecodeStep RefPcEven.
From Cheriot.Proof Require Import RefFetchRqImpl RefFetchRqStep RefRevBitRule RefRedirect RefRedirStep.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * FRONTEND STEPS WHILE A REDIRECT IS PENDING (item 3.4)
 * ===========================================================================
 * While a redirect is pending, `RedirInv` keeps every frontend entry in the current epoch, so in
 * the applied view (`applyP`, epoch + 1) the whole frontend is dead (`NoLive`) and there is no
 * straddle. The applied view's fetchPc is the redirect target, the PCC's address. A frontend step
 * then only adds or drops dead entries; the relation's frontend part follows from these facts
 * (`FrontRel_noLive`). *)

Local Abbreviation TS t := (TreeState ElemState t).

Section RedirFront.
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
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation STAGE :=
    (@fetchRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation STEPOKRR :=
    (StepOKRR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs).

  Local Abbreviation ACC f := (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA := (ACC iRf).
  Local Abbreviation iWbA := (ACC iWb).
  Local Abbreviation iMemA := (ACC iMem).
  Local Abbreviation iFetchA := (ACC iFetch).
  Local Abbreviation iDecodeA := (ACC iDecode).
  Local Abbreviation iExecA := (ACC iExec).
  Local Abbreviation iDmA := (ACC iDm).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iRegionsA := (ACC iRegions).
  Local Abbreviation iFetchBufA := (ACC iFetchBuf).
  Local Abbreviation iInstBufA := (ACC iInstBuf).
  Local Abbreviation iD2aA := (ACC iD2a).
  Local Abbreviation iExecEpochA := (ACC iExecEpoch).
  Local Abbreviation iFenceIPendingA := (ACC iFenceIPending).
  Local Abbreviation iPccA := (ACC iPcc).
  Local Abbreviation daLiveA := (ACC daLive).
  Local Abbreviation aiLiveA := (ACC aiLive).
  Local Abbreviation fbLiveA := (ACC fbLive).
  Local Abbreviation NoLiveA := (ACC NoLive).
  Local Abbreviation applyPA := (ACC applyP).
  Local Abbreviation effSA := (ACC effS).
  Local Abbreviation validA := (ACC iRedirValid).
  Local Abbreviation InvA := (ACC RedirInv).
  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation FRREL := (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 initLine fwcs).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* --- 1. The Applied View of a Pending Redirect --- *)

  Lemma pending_noLive : forall s1, validA s1 = true -> InvA s1 -> NoLiveA (applyPA s1).
  Proof.
    intros s1 Hv [_ [_ I3]]; destruct (I3 Hv) as [_ [Hd [Ha Hf]]].
    pose proof (zmod_epoch_add1_neq (iExecEpochA s1)) as Hne.
    split; [| split].
    - change (Forall (fun j => daLiveA (applyPA s1) j = false) (iD2aA s1)).
      revert Hd; apply Forall_impl; intros j Ej; unfold daLive; rewrite applyP_epoch, Ej; exact Hne.
    - change (Forall (fun a => aiLiveA (applyPA s1) a = false) (iInstBufA s1)).
      revert Ha; apply Forall_impl; intros a Ea; unfold aiLive; rewrite applyP_epoch, Ea; exact Hne.
    - change (Forall (fun f => fbLiveA (applyPA s1) f = false) (iFetchBufA s1)).
      revert Hf; apply Forall_impl; intros f Ef; unfold fbLive; rewrite applyP_epoch, Ef.
      unfold nextEpoch; rewrite Hne; reflexivity.
  Qed.

  Lemma applyP_noStraddle : forall s1, optValid (ACC iStraddle (applyPA s1)) = false.
  Proof. intros s1; reflexivity. Qed.

  (* With no live instruction and no straddle, fetch continues at the PCC *)
  Lemma noLive_front_facts :
    forall g (X : IState) (s2 : SState),
      NoLiveA X -> optValid (ACC iStraddle X) = false ->
      FrontRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine fwcs g X s2 ->
      ACC iFetchPc X = (iPccA X).(Snd).(Snd).(Fst) /\ pcAligned (iPccA X).(Snd).(Snd).(Fst).
  Proof.
    intros g X s2 Hnl Hs [_ [_ [_ [_ [_ [F6 _]]]]]].
    unfold LiveChain in F6; erewrite liveInsts_noLive in F6 by exact Hnl.
    cbn [LiveChainG] in F6; unfold FrontierRel in F6; cbv zeta in F6.
    rewrite (filter_false_nil _ _ (proj2 (proj2 Hnl))), Hs in F6.
    destruct F6 as [_ [_ [A B]]]; exact (conj A B).
  Qed.

  Lemma FrontRel_noLive :
    forall g (X : IState) (s2 : SState),
      NoLiveA X -> optValid (ACC iStraddle X) = false ->
      ACC iFetchPc X = (iPccA X).(Snd).(Snd).(Fst) -> pcAligned (iPccA X).(Snd).(Snd).(Fst) ->
      FRREL X s2 ->
      FrontRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine fwcs g X s2.
  Proof.
    intros g X s2 Hnl Hs Hpc Hal Hfr.
    destruct Hnl as [Hd [Ha Hf]].
    unfold FrontRel.
    split; [exact (StalePrefix_all_false _ _ Hd) |].
    split; [exact (StalePrefix_all_false _ _ Ha) |].
    split; [exact (StalePrefix_all_false _ _ Hf) |].
    split; [intros Hex; exfalso; exact (Forall_false_Exists_contra _ _ Hd Hex) |].
    split; [intros [Hex | Hex]; exfalso;
             [exact (Forall_false_Exists_contra _ _ Hd Hex) | exact (Forall_false_Exists_contra _ _ Ha Hex)] |].
    split; [| exact Hfr].
    unfold LiveChain, liveInsts.
    rewrite (filter_fst_false_nil (daLiveA X) (iD2aA X) (g_d2aFo pcAddrInit g) Hd).
    rewrite (filter_false_nil (aiLiveA X) (iInstBufA X) Ha).
    cbn [map app LiveChainG].
    unfold FrontierRel; cbv zeta.
    rewrite (filter_false_nil (fbLiveA X) (iFetchBufA X) Hf), Hs.
    split; [exact I | split; [constructor | split; [exact Hpc | exact Hal]]].
  Qed.

  Lemma FenceRel_noLive :
    forall g (X X' : IState),
      FenceRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g X ->
      iFenceIPendingA X' = iFenceIPendingA X -> optValid (ACC iStraddle X') = optValid (ACC iStraddle X) ->
      NoLiveA X' -> (ACC NoFenceIWait X -> ACC NoFenceIWait X') ->
      FenceRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g X'.
  Proof.
    intros g X X' [A [B C]] E1 E2 Hnl Himp; unfold FenceRel; rewrite E1, E2.
    split; [intros h; destruct (A h) as [_ R]; exact (conj Hnl R) |].
    split; [| exact C].
    intros Hn; destruct (B (fun h => Hn (Himp h))) as [P [_ R]]; exact (conj P (conj Hnl R)).
  Qed.

  (* --- 2. A Fetch Step on a Dead Frontend --- *)

  (* fetch's PC, straddle, parcel and assembled instructions stay; dead entries `E` join fetchBuf *)
  Lemma fetch_dead :
    forall g (X X' : IState) (s2 : SState) (E : list (type FetchBufEntry)),
      iRfA X' = iRfA X -> iWbA X' = iWbA X -> iDecodeA X' = iDecodeA X -> iExecA X' = iExecA X ->
      iDmA X' = iDmA X -> iMdA X' = iMdA X ->
      ACC iFetchPc X' = ACC iFetchPc X -> ACC iStraddle X' = ACC iStraddle X ->
      ACC iPredEpoch X' = ACC iPredEpoch X -> ACC iCurParcel X' = ACC iCurParcel X ->
      fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA X') =
        fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA X) ->
      fifo_wf (FBF X') -> iFetchBufA X' = (iFetchBufA X ++ E)%list ->
      Forall (fun f => fbLiveA X f = false) E -> Forall (fun f => pcAligned (fbPredPc f)) E ->
      NoLiveA X -> optValid (ACC iStraddle X) = false ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g X' s2 ->
      MEMC g X' s2 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g X' s2 ->
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g X' s2 ->
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g X' ->
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g X' s2 ->
      (forall P, FrqInsensitive P -> AllPorts P implRegions (iRegionsA X') = AllPorts P implRegions (iRegionsA X)) ->
      FRREL X' s2 ->
      RELG g X s2 -> RELG g X' s2.
  Proof.
    intros g X X' s2 E Erf Ewb ED Eex Edm Emd Efpc Estr Epe Ecp Eif Wfb Efb HE HEal Hnl Hs
           Crf Cm Ca Cc Cd Crk HP Cfr H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  X X' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  X X' Edm Emd) as Eow.
    assert (Ed2a : iD2aA X' = iD2aA X) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA X' = iExecEpochA X) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA X' = iFenceIPendingA X) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA X' = iPccA X) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Eib : iInstBufA X' = iInstBufA X) by (unfold iInstBuf; rewrite Eif; reflexivity).
    assert (Elv : fbLiveA X' = fbLiveA X) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
    assert (Edl : daLiveA X' = daLiveA X) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA X' = aiLiveA X) by (unfold aiLive; rewrite Eep; reflexivity).
    assert (Hnl' : NoLiveA X').
    { destruct Hnl as [N1 [N2 N3]]; unfold NoLive.
      rewrite Ed2a, Eib, Efb, Edl, Eal, Elv.
      exact (conj N1 (conj N2 (proj2 (Forall_app _ _ _) (conj N3 HE)))). }
    destruct H as [_ _ Hl Hrp He' _ _ _ Hfe Hsc Hfr Hwf _].
    destruct (noLive_front_facts g X s2 Hnl Hs Hfr) as [Hpc Hal].
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - refine (FenceRel_noLive g X X' Hfe Efip (f_equal optValid Estr) Hnl' _).
      unfold NoFenceIWait; rewrite HP by (intros r y L rdy; reflexivity); exact (fun h => h).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hsc.
    - apply (FrontRel_noLive g X' s2 Hnl'); [rewrite Estr; exact Hs | rewrite Efpc, Epcc; exact Hpc |
                                             rewrite Epcc; exact Hal | exact Cfr].
    - destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
      unfold WfRel; rewrite Ecp, Efb, Epcc, Ed2a, Eib.
      rewrite HP by (intros r y L rdy; reflexivity).
      split; [split; [exact Wfb |] |].
      + split; [intros Hc C; apply app_eq_nil in C as [C _]; exact (W1b Hc C) |].
        split; [exact W1c |]; split; [exact W1d |]; split; [exact W1e |].
        apply Forall_app; split; [exact W1f | exact HEal].
      + split; [rewrite Eif; exact W2 |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
    - exact Crk.
  Qed.


  (* --- 3. `fetchRqStage` --- *)

  (* The applied view of a fetchRq step: execute stays, fetch changes as in the raw step *)
  Lemma frq_applied :
    forall (s1 s1' : IState) m f,
      ACC FrqStep s1 s1' m f ->
      iExecA (applyPA s1') = iExecA (applyPA s1) /\
      iFetchA (applyPA s1') =
        fetch_withPc pcAddrInit fetchCapacity instCapacity
          (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity f (getDefault (Option StraddleHalf)))
          (ACC redirTarget s1).
  Proof.
    intros s1 s1' m f [_ [_ [_ [Efe [_ [Eex _]]]]]].
    split.
    - rewrite !applyP_exec; unfold iExecEpoch; rewrite Eex; reflexivity.
    - rewrite applyP_fetch, Efe; unfold redirTarget, redirPcc, iRedirect; rewrite Eex; reflexivity.
  Qed.

  Lemma frEntry_dead :
    forall (s1 s1' : IState) nio, iExecEpochA s1' = iExecEpochA s1 ->
      fbLiveA (applyPA s1') (ACC frEntry s1 nio) = false.
  Proof.
    intros s1 s1' nio Eep; unfold fbLive; rewrite applyP_epoch, Eep.
    change (fbExecEpoch (ACC frEntry s1 nio)) with (iExecEpochA s1).
    unfold nextEpoch; rewrite zmod_epoch_add1_neq; reflexivity.
  Qed.

  Ltac frq_eq Efe' := rewrite Efe', applyP_fetch; reflexivity.

  Lemma fetchRq_pending :
    forall g (s1 s1' : IState) (s2 : SState),
      SemAction envI STAGE s1 s1' Zmod.zero -> validA s1 = true -> InvA s1 ->
      RELG g (applyPA s1) s2 -> RELG g (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 Hsem Hv Hi Hg.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    pose proof (pending_noLive s1 Hv Hi) as Hnl.
    pose proof (applyP_noStraddle s1) as Hs.
    pose proof Hg as [_ _ _ _ _ _ _ _ _ _ Hfr0 Hw0 _].
    assert (Wfb : fifo_wf (FBF s1)) by exact (proj1 (proj1 Hw0)).
    pose proof Hfr0 as [_ [_ [_ [_ [_ [_ F7]]]]]].
    destruct (andb (negb (ACC frFull s1)) (andb (negb (ACC frFip s1)) (negb (anyWait implRegions (iRegionsA s1)))))
      eqn:Hgo.
    2: { rewrite (ACC fetchRq_idle _ s1 s1' Hsem Hgo); exact Hg. }
    apply andb_prop in Hgo as [Hf Hgo]; apply andb_prop in Hgo as [Hfc Hw].
    apply negb_true_iff in Hf, Hfc, Hw.
    (* an enqueue: one dead entry joins fetchBuf *)
    assert (Henq : forall m nio,
               ACC FrqStep s1 s1' m (ACC frEnqF s1 (ACC frEntry s1 nio)) ->
               RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g (applyPA s1') s2 ->
               MEMC g (applyPA s1') s2 ->
               AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g (applyPA s1') s2 ->
               CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g (applyPA s1') s2 ->
               DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g (applyPA s1') ->
               RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g (applyPA s1') s2 ->
               (forall P, FrqInsensitive P ->
                  AllPorts P implRegions (iRegionsA (applyPA s1')) = AllPorts P implRegions (iRegionsA (applyPA s1))) ->
               (iFetchBufA (applyPA s1') = (iFetchBufA (applyPA s1) ++ [ACC frEntry s1 nio])%list ->
                fbLiveA (applyPA s1') = fbLiveA (applyPA s1) -> FRREL (applyPA s1') s2) ->
               RELG g (applyPA s1') s2).
    { intros m nio Hst Crf Cm Ca Cc Cd Crk HP Cfr.
      pose proof Hst as [Erf [Ewb [_ [_ [ED [_ [Edm Emd]]]]]]].
      destruct (frq_applied s1 s1' _ _ Hst) as [Eex Efe].
      assert (Eep : iExecEpochA (applyPA s1') = iExecEpochA (applyPA s1)) by (unfold iExecEpoch; rewrite Eex; reflexivity).
      assert (Epe : ACC iPredEpoch (applyPA s1') = ACC iPredEpoch (applyPA s1)) by (unfold iPredEpoch; frq_eq Efe).
      assert (Efb : iFetchBufA (applyPA s1') = (iFetchBufA (applyPA s1) ++ [ACC frEntry s1 nio])%list).
      { unfold iFetchBuf; rewrite Efe, applyP_fetch; exact (fifo_to_list_enq_nf _ _ _ _ Wfb Hf). }
      assert (Elv : fbLiveA (applyPA s1') = fbLiveA (applyPA s1)) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
      refine (fetch_dead g (applyPA s1) (applyPA s1') s2 [ACC frEntry s1 nio] Erf Ewb ED Eex Edm Emd
                _ _ Epe _ _ _ Efb _ _ Hnl Hs Crf Cm Ca Cc Cd Crk HP (Cfr Efb Elv) Hg).
      - unfold iFetchPc; frq_eq Efe.
      - unfold iStraddle; frq_eq Efe.
      - unfold iCurParcel; frq_eq Efe.
      - frq_eq Efe.
      - rewrite Efe; exact (fifo_wf_enq _ _ _ _ Wfb).
      - constructor; [| constructor].
        rewrite <- Elv; apply frEntry_dead; unfold iExecEpoch; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hst)))))).
        reflexivity.
      - constructor; [exact (pcAligned_clear _) | constructor]. }
    destruct (excAny (ACC frExc s1)) eqn:Hpre.
    - pose proof (ACC fetchRq_pre _ s1 s1' Hsem Hf Hfc Hw Hpre) as Hst.
      pose proof Hst as [Erf [_ [Emem [_ [_ [_ [Edm Emd]]]]]]].
      assert (Ereg : iRegionsA (applyPA s1') = iRegionsA (applyPA s1)) by (unfold iRegions; exact (f_equal _ Emem)).
      destruct (ACC decode_core clintS clint plicS plic initLine fwcs g (applyPA s1) (applyPA s1') s2 Erf Emem Edm Emd Hg)
        as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
      refine (Henq _ _ Hst Crf Cm Ca Cc Cd Crk _ _).
      + intros P _; rewrite Ereg; reflexivity.
      + intros Efb Elv; exact (ACC FetchRespRel_pre initLine fwcs (applyPA s1) (applyPA s1') s2 _ Ereg Efb Elv Hpre F7).
    - destruct (ACC fetchRq_noPre _ s1 s1' Hu Hsem Hf Hfc Hw Hpre) as [mr' [rdy [Hat [Hk Hst]]]].
      destruct rdy.
      + destruct Hst as [nio Hst].
        pose proof Hst as [Erf [_ [Emem [_ [_ [_ [Edm Emd]]]]]]].
        destruct (ACC core_fetchRq clintS clint plicS plic initLine fwcs g (applyPA s1) (applyPA s1') s2 mr' _ true
                    Erf Emem Edm Emd Hat Hg)
          as [Crf [Cm [Ca [Cc [Cd [Crk HP]]]]]].
        assert (Ereg : iRegionsA (applyPA s1') = mr') by (unfold iRegions; rewrite applyP_mem, Emem; reflexivity).
        refine (Henq _ _ Hst Crf Cm Ca Cc Cd Crk HP _).
        intros Efb Elv; exact (ACC FetchRespRel_acc initLine fwcs Hdisj (applyPA s1) (applyPA s1') s2 _ mr' _ Hat Ereg Efb Elv eq_refl Hpre F7).
      + pose proof Hst as [Erf [Ewb [Emem [_ [ED [_ [Edm Emd]]]]]]].
        destruct (frq_applied s1 s1' _ _ Hst) as [Eex Efe].
        destruct (ACC core_fetchRq clintS clint plicS plic initLine fwcs g (applyPA s1) (applyPA s1') s2 mr' _ false
                    Erf Emem Edm Emd Hat Hg)
          as [Crf [Cm [Ca [Cc [Cd [Crk HP]]]]]].
        assert (Ereg : iRegionsA (applyPA s1') = mr') by (unfold iRegions; rewrite applyP_mem, Emem; reflexivity).
        assert (Eep : iExecEpochA (applyPA s1') = iExecEpochA (applyPA s1)) by (unfold iExecEpoch; rewrite Eex; reflexivity).
        assert (Epe : ACC iPredEpoch (applyPA s1') = ACC iPredEpoch (applyPA s1)) by (unfold iPredEpoch; frq_eq Efe).
        assert (Efb0 : iFetchBufA (applyPA s1') = iFetchBufA (applyPA s1)) by (unfold iFetchBuf; frq_eq Efe).
        assert (Elv : fbLiveA (applyPA s1') = fbLiveA (applyPA s1)) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
        refine (fetch_dead g (applyPA s1) (applyPA s1') s2 [] Erf Ewb ED Eex Edm Emd
                  _ _ Epe _ _ _ _ (Forall_nil _) (Forall_nil _) Hnl Hs Crf Cm Ca Cc Cd Crk HP _ Hg).
        * unfold iFetchPc; frq_eq Efe.
        * unfold iStraddle; frq_eq Efe.
        * unfold iCurParcel; frq_eq Efe.
        * frq_eq Efe.
        * rewrite Efe; exact Wfb.
        * rewrite app_nil_r; exact Efb0.
        * exact (ACC FetchRespRel_rej initLine fwcs Hdisj (applyPA s1) (applyPA s1') s2 mr' _ Hat Ereg Efb0 Elv F7).
  Qed.

  (* `RedirInv` across a fetchRq step: new entries carry the current epoch *)
  Lemma inv_frq :
    forall (s1 s1' : IState) m f (E : list (type FetchBufEntry)),
      ACC FrqStep s1 s1' m f ->
      tagEcap (fetch_pccCopy pcAddrInit fetchCapacity instCapacity f) =
      tagEcap (fetch_pccCopy pcAddrInit fetchCapacity instCapacity (iFetchA s1)) ->
      fetch_fipCopy pcAddrInit fetchCapacity instCapacity f = fetch_fipCopy pcAddrInit fetchCapacity instCapacity (iFetchA s1) ->
      fetch_instFifo pcAddrInit fetchCapacity instCapacity f = fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) ->
      iFetchBufA s1' = (iFetchBufA s1 ++ E)%list ->
      Forall (fun x => fbExecEpoch x = iExecEpochA s1) E ->
      InvA s1 -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' m f E [Erf [_ [_ [Efe [ED [Eex _]]]]]] Ep Efi Eif Efb HE H.
    assert (Ev : validA s1' = validA s1) by (unfold iRedirValid; rewrite Eex; reflexivity).
    split; [| exact Ev].
    assert (E2 : tagEcap (ACC iFetchPcc s1') = tagEcap (ACC iFetchPcc s1)) by (unfold iFetchPcc; rewrite Efe; exact Ep).
    assert (E3 : ACC iFetchFip s1' = ACC iFetchFip s1) by (unfold iFetchFip; rewrite Efe; exact Efi).
    assert (E4 : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (E5 : ACC redirPcc s1' = ACC redirPcc s1) by (unfold redirPcc, iRedirect; rewrite Eex; reflexivity).
    assert (E6 : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (E7 : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (E8 : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (E9 : iInstBufA s1' = iInstBufA s1) by (unfold iInstBuf; rewrite Efe, Eif; reflexivity).
    unfold RedirInv in *; rewrite Ev, E2, E3, E4, E5, E6, E7, E8, E9, Efb.
    destruct H as [I1 [I2 I3]]; split; [exact I1 | split; [exact I2 |]].
    intros hv; destruct (I3 hv) as [A [B [C D]]].
    exact (conj A (conj B (conj C (proj2 (Forall_app _ _ _) (conj D HE))))).
  Qed.

  Lemma fetchRq_inv :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero -> fifo_wf (FBF s1) ->
      InvA s1 -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' Hsem Wfb Hi.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    destruct (andb (negb (ACC frFull s1)) (andb (negb (ACC frFip s1)) (negb (anyWait implRegions (iRegionsA s1)))))
      eqn:Hgo.
    2: { rewrite (ACC fetchRq_idle _ s1 s1' Hsem Hgo); exact (conj Hi eq_refl). }
    apply andb_prop in Hgo as [Hf Hgo]; apply andb_prop in Hgo as [Hfc Hw].
    apply negb_true_iff in Hf, Hfc, Hw.
    assert (Henq : forall m nio, ACC FrqStep s1 s1' m (ACC frEnqF s1 (ACC frEntry s1 nio)) ->
                                 InvA s1' /\ validA s1' = validA s1).
    { intros m nio Hst.
      refine (inv_frq s1 s1' m _ [ACC frEntry s1 nio] Hst eq_refl eq_refl eq_refl _ _ Hi).
      - unfold iFetchBuf; rewrite (proj1 (proj2 (proj2 (proj2 Hst)))).
        exact (fifo_to_list_enq_nf _ _ _ _ Wfb Hf).
      - constructor; [reflexivity | constructor]. }
    destruct (excAny (ACC frExc s1)) eqn:Hpre.
    - exact (Henq _ _ (ACC fetchRq_pre _ s1 s1' Hsem Hf Hfc Hw Hpre)).
    - destruct (ACC fetchRq_noPre _ s1 s1' Hu Hsem Hf Hfc Hw Hpre) as [mr' [rdy [_ [_ Hst]]]].
      destruct rdy; [destruct Hst as [nio Hst]; exact (Henq _ _ Hst) |].
      refine (inv_frq s1 s1' _ _ [] Hst eq_refl eq_refl eq_refl _ (Forall_nil _) Hi).
      rewrite app_nil_r; unfold iFetchBuf; rewrite (proj1 (proj2 (proj2 (proj2 Hst)))); reflexivity.
  Qed.

  (* The hand-off: a fetch request touches only fetch and the fetch side of the regions *)
  Lemma fetchRq_hand :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> ACC HandInv s1 -> ACC HandInv s1'.
  Proof.
    intros s1 s1' Hsem Hh.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    destruct (andb (negb (ACC frFull s1)) (andb (negb (ACC frFip s1)) (negb (anyWait implRegions (iRegionsA s1)))))
      eqn:Hgo.
    2: { rewrite (ACC fetchRq_idle _ s1 s1' Hsem Hgo); exact Hh. }
    apply andb_prop in Hgo as [Hf Hgo]; apply andb_prop in Hgo as [Hfc Hw].
    apply negb_true_iff in Hf, Hfc, Hw.
    destruct (excAny (ACC frExc s1)) eqn:Hpre.
    - destruct (ACC fetchRq_pre _ s1 s1' Hsem Hf Hfc Hw Hpre) as [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]].
      exact (ACC HandInv_eq s1 s1' Eex ED Erf Edm Emem Hh).
    - destruct (ACC fetchRq_noPre _ s1 s1' Hu Hsem Hf Hfc Hw Hpre) as [mr' [rdy [Hat [_ Hst]]]].
      assert (Hfr : forall f, ACC FrqStep s1 s1' (mr' ,, (iMemA s1).(Snd)) f -> ACC HandInv s1').
      { intros f [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]].
        exact (ACC HandInv_regions s1 s1' mr' Eex ED Erf Edm Emem Hh). }
      destruct rdy; [destruct Hst as [nio Hst] |]; exact (Hfr _ Hst).
  Qed.

  Theorem stepOK_fetchRq : STEPOKRR STAGE.
  Proof.
    intros s1 s1' s2 Hsem _ [Hi [Hh [g Hg]]].
    exists s2; split; [apply NilAction; reflexivity |].
    assert (Wfb : fifo_wf (FBF s1)).
    { pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; unfold effS in Hw.
      destruct (validA s1); exact (proj1 (proj1 Hw)). }
    destruct (fetchRq_inv s1 s1' Hsem Wfb Hi) as [Hi' Ev].
    split; [exact Hi' | split; [exact (fetchRq_hand s1 s1' Hsem Hh) | exists g]].
    destruct (validA s1) eqn:Hv.
    - erewrite effS_true in Hg by exact Hv; erewrite effS_true by exact Ev.
      exact (fetchRq_pending g s1 s1' s2 Hsem Hv Hi Hg).
    - erewrite effS_false in Hg by exact Hv; erewrite effS_false by exact Ev.
      destruct Hi as [I1 [I2 _]]; pose proof (I1 Hv) as Ht; unfold tagEcap in Ht; injection Ht as Et Ee.
      exact (ACC fetchRq_live clintS clint plicS plic initLine fwcs Hdisj g s1 s1' s2 Hsem Et Ee (I2 Hv) Hg).
  Qed.

End RedirFront.
