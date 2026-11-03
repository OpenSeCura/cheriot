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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefPeriph.
From Cheriot.Proof Require Import RefExecAux RefExecFrame RefDecodeImpl.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 6: `decodeAndRegReadStage` (the spec stutters)
 * ===========================================================================
 * Branches (RefDecodeImpl.v): no `canProceed` or no head or a stall changes nothing the relation
 * reads; a stale head leaves instBuf; a live head moves to the end of the decode-to-ALU FIFO with
 * its fetch output appended to `g_d2aFo`, so `liveInsts` is unchanged. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Stall Test and Wait Bits --- *)

Lemma isNotZero_eval : forall sz (x : bits sz), evalExpr (isNotZero (Var type (Bit sz) x)) = negb (Zmod.eqb x Zmod.zero).
Proof.
  intros sz x.
  change (negb (evalExpr (isZero (Var type (Bit sz) x))) = negb (Zmod.eqb x Zmod.zero)).
  f_equal; reflexivity.
Qed.

Definition canIssueB (full nz1 nz2 w1 w2 wcd writesCd : bool) : bool :=
  evalExpr (Not (Or [ Var type Bool full ;
                      And [ Var type Bool nz1 ; Var type Bool w1 ] ;
                      And [ Var type Bool nz2 ; Var type Bool w2 ] ;
                      And [ Var type Bool writesCd ; Var type Bool wcd ] ])).

Lemma canIssueV_B :
  forall full cs1 cs2 w1 w2 wcd writesCd,
    canIssueV full cs1 cs2 w1 w2 wcd writesCd =
    canIssueB full (negb (Zmod.eqb cs1 Zmod.zero)) (negb (Zmod.eqb cs2 Zmod.zero)) w1 w2 wcd writesCd.
Proof.
  intros; unfold canIssueV, canIssueB.
  rewrite <- (isNotZero_eval RegIdxSzReal cs1), <- (isNotZero_eval RegIdxSzReal cs2); reflexivity.
Qed.

Lemma canIssueV_true :
  forall full cs1 cs2 w1 w2 wcd writesCd,
    canIssueV full cs1 cs2 w1 w2 wcd writesCd = true ->
    full = false /\
    (Zmod.eqb cs1 Zmod.zero = false -> w1 = false) /\
    (Zmod.eqb cs2 Zmod.zero = false -> w2 = false) /\
    (writesCd = true -> wcd = false).
Proof.
  intros full cs1 cs2 w1 w2 wcd writesCd H; rewrite canIssueV_B in H.
  destruct (Zmod.eqb cs1 Zmod.zero), (Zmod.eqb cs2 Zmod.zero), full, w1, w2, wcd, writesCd;
    cbv in H; first [discriminate H | repeat split; intros; first [reflexivity | discriminate]].
Qed.

(* Setting a register's wait bit (x0 has none) *)
Lemma evalReadWaitBit_setDst_true :
  forall (w : bool) (d r : bits RegIdxSzReal) (wb : TS waitBitsTree),
    evalReadWaitBit r (evalSetDstWaitBits w d true wb) =
      if andb w (andb (negb (Zmod.eqb d Zmod.zero)) (Zmod.eqb r d)) then true else evalReadWaitBit r wb.
Proof.
  intros [|] d r wb; cbn [evalSetDstWaitBits andb]; [| reflexivity].
  destruct (Zmod.eqb r d) eqn:Erd.
  - apply Zmod.eqb_eq in Erd; subst r.
    destruct (Zmod.eqb d Zmod.zero) eqn:Ez; cbn [negb andb].
    + apply Zmod.eqb_eq in Ez; subst d; rewrite !evalReadWaitBit_zero; reflexivity.
    + apply evalReadWaitBit_write_same; exact Ez.
  - rewrite andb_false_r; apply evalReadWaitBit_write_other.
    intros Heq; subst r; rewrite Zmod.eqb_refl in Erd; discriminate Erd.
Qed.

Lemma combine_snoc :
  forall {A B : Type} (l1 : list A) (l2 : list B) x y,
    length l1 = length l2 -> combine (l1 ++ [x]) (l2 ++ [y]) = (combine l1 l2 ++ [(x, y)])%list.
Proof.
  intros A B l1; induction l1 as [| a l1 IH]; intros [| b l2] x y H; cbn in H |- *;
    [reflexivity | discriminate H | discriminate H |].
  rewrite IH by lia; reflexivity.
Qed.

(* --- 2. The Relation Across a Decode Step --- *)

Section DecodeStep.
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

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation STEPOK :=
    (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
  Local Abbreviation STAGE :=
    (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

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
  Local Abbreviation iFlushA := (ACC iFlush).
  Local Abbreviation iRegionsA := (ACC iRegions).
  Local Abbreviation iFetchBufA := (ACC iFetchBuf).
  Local Abbreviation iInstBufA := (ACC iInstBuf).
  Local Abbreviation iD2aA := (ACC iD2a).
  Local Abbreviation iExecEpochA := (ACC iExecEpoch).
  Local Abbreviation iFenceIPendingA := (ACC iFenceIPending).
  Local Abbreviation iPccA := (ACC iPcc).
  Local Abbreviation olderWritersA := (ACC olderWriters).
  Local Abbreviation daLiveA := (ACC daLive).
  Local Abbreviation aiLiveA := (ACC aiLive).
  Local Abbreviation fbLiveA := (ACC fbLive).
  Local Abbreviation liveInstsA := (ACC liveInsts).
  Local Abbreviation D2AF s1 := (decode_toAluFifo decodeCapacity (iDecodeA s1)).
  Local Abbreviation IBF s1 := (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation dHeadA := (ACC dHead).
  Local Abbreviation dAA := (ACC dA).
  Local Abbreviation dFoA := (ACC dFo).
  Local Abbreviation dEntryA := (ACC dEntry).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* The components that read neither the frontend nor the wait bits *)
  Lemma decode_core :
    forall g (s1 s1' : IState) (s2 : SState),
      iRfA s1' = iRfA s1 -> iMemA s1' = iMemA s1 -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      RELG g s1 s2 ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 /\
      MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        clintS clint plicS plic fwcs g s1' s2 /\
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' /\
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2.
  Proof.
    intros g s1 s1' s2 Erf Emem Edm Emd H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    destruct H as [Hrf Hm _ _ _ Ha Hc Hd _ _ _ _ Hrk].
    split; [unfold RfRel in *; rewrite Efl; exact Hrf |].
    split; [unfold MemRelC in *; rewrite Ereg; exact Hm |].
    split.
    { eapply AccessRel_frame with (s1 := s1) (s2 := s2);
        try reflexivity;
        try (unfold iMemSt, iRequester, iReadRp, iDmSt, iRevPhase, iRev, iRegions; rewrite ?Emem, ?Edm; reflexivity);
        exact Ha. }
    split; [unfold CnwbRel in *; unfold iDmSt in *; rewrite Edm; exact Hc |].
    split; [unfold DmQueueRel, iDmBuf in *; rewrite Edm; exact Hd |].
    eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2);
      try reflexivity; try (unfold iRev, iRegions; rewrite Emem; reflexivity); exact Hrk.
  Qed.

  (* No frontend change: decode only cleared its `canProceed` *)
  Lemma decode_stutter :
    forall g (s1 s1' : IState) (s2 : SState),
      DecStutter pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 s1' ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] H.
    destruct (decode_core g s1 s1' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    destruct H as [_ _ Hl Hrp He _ _ _ Hf Hs Hfr Hw _].
    constructor; try assumption.
    - unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *;
        rewrite Ereg, Efe, Ed2a, Eep, Efip; exact Hf.
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - unfold FrontRel, LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iPcc, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf in *;
        rewrite Erf, Ereg, Efe, Ed2a, Eep; exact Hfr.
    - unfold WfRel, iCurParcel, iFetchBuf, iInstBuf, iPcc in *;
        rewrite ?Erf, ?Ed2a, ?ED, ?Efe, ?Edm, ?Emd, ?Ereg; exact Hw.
  Qed.

  (* Facts about instBuf's head when it is valid *)
  Lemma ib_head :
    forall (s1 : IState),
      fifo_wf (IBF s1) -> (dHeadA s1).(Snd).(Fst) = true ->
      exists rest, iInstBufA s1 = dAA s1 :: rest /\ fifo_to_list (fifoDeqState (IBF s1)) = rest.
  Proof.
    intros s1 Hwf Hv.
    unfold dHead in Hv; rewrite (fifoFirstVal_valid _ _ _ Hwf) in Hv.
    unfold iInstBuf; destruct (fifo_to_list (IBF s1)) as [| a rest] eqn:El; [discriminate Hv |].
    exists rest; split.
    - f_equal; unfold dA, dHead; symmetry; exact (fifoFirstVal_data _ _ _ a rest El).
    - rewrite (fifo_to_list_deq _ _ _ Hwf), El; reflexivity.
  Qed.

  (* The frontend accessors that only instBuf's update leaves unchanged *)
  Local Ltac fetch_eqs Efe :=
    let E1 := fresh "Efb" in let E2 := fresh "Ecp" in let E3 := fresh "Estr" in
    let E4 := fresh "Efpc" in let E5 := fresh "Epe" in
    assert (E1 : iFetchBufA _ = iFetchBufA _) by (unfold iFetchBuf; rewrite Efe; reflexivity);
    assert (E2 : ACC iCurParcel _ = ACC iCurParcel _) by (unfold iCurParcel; rewrite Efe; reflexivity);
    assert (E3 : ACC iStraddle _ = ACC iStraddle _) by (unfold iStraddle; rewrite Efe; reflexivity);
    assert (E4 : ACC iFetchPc _ = ACC iFetchPc _) by (unfold iFetchPc; rewrite Efe; reflexivity);
    assert (E5 : ACC iPredEpoch _ = ACC iPredEpoch _) by (unfold iPredEpoch; rewrite Efe; reflexivity).

  Lemma FrontierRel_ib :
    forall (s1 s1' : IState) (s2 : SState) fp,
      iFetchBufA s1' = iFetchBufA s1 -> ACC iCurParcel s1' = ACC iCurParcel s1 ->
      ACC iStraddle s1' = ACC iStraddle s1 -> ACC iFetchPc s1' = ACC iFetchPc s1 ->
      ACC iPredEpoch s1' = ACC iPredEpoch s1 -> iExecEpochA s1' = iExecEpochA s1 -> iPccA s1' = iPccA s1 ->
      FrontierRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine fwcs s1 s2 fp ->
      FrontierRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine fwcs s1' s2 fp.
  Proof.
    intros s1 s1' s2 fp Efb Ecp Estr Efpc Epe Eep Epcc H.
    unfold FrontierRel, fbLive in *; rewrite Efb, Ecp, Estr, Efpc, Epe, Eep, Epcc; exact H.
  Qed.

  Lemma FetchRespRel_ib :
    forall (s1 s1' : IState) (s2 : SState),
      iFetchBufA s1' = iFetchBufA s1 -> ACC iPredEpoch s1' = ACC iPredEpoch s1 ->
      iExecEpochA s1' = iExecEpochA s1 -> iRegionsA s1' = iRegionsA s1 ->
      FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine fwcs s1 s2 ->
      FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine fwcs s1' s2.
  Proof.
    intros s1 s1' s2 Efb Epe Eep Ereg H.
    unfold FetchRespRel, fbInRegion, fbLive in *; rewrite Ereg, Efb, Epe, Eep; exact H.
  Qed.

  (* A stale instBuf head is dropped *)
  Lemma decode_stale :
    forall g (s1 s1' : IState) (s2 : SState),
      (dHeadA s1).(Snd).(Fst) = true -> aiLiveA s1 (dAA s1) = false ->
      iRfA s1' = iRfA s1 -> iWbA s1' = iWbA s1 -> iMemA s1' = iMemA s1 ->
      iFetchA s1' = fetch_withInstFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) (fifoDeqState (IBF s1)) ->
      D2AF s1' = D2AF s1 -> iExecA s1' = iExecA s1 -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 Hv Hst Erf Ewb Emem Efe ED Eex Edm Emd H.
    destruct (decode_core g s1 s1' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    fetch_eqs Efe.
    destruct H as [_ _ Hl Hrp He _ _ _ Hf Hs Hfr Hw _].
    pose proof Hw as Hw0; destruct Hw0 as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (ib_head s1 W2 Hv) as [rest [Eib0 Erest]].
    assert (Eib : iInstBufA s1' = rest) by (unfold iInstBuf; rewrite Efe; exact Erest).
    assert (Eal : forall a, aiLiveA s1' a = aiLiveA s1 a) by (intros a; unfold aiLive; rewrite Eep; reflexivity).
    assert (Edl : forall j, daLiveA s1' j = daLiveA s1 j) by (intros j; unfold daLive; rewrite Eep; reflexivity).
    assert (Elive : liveInstsA g s1' = liveInstsA g s1).
    { unfold liveInsts; rewrite Ed2a, Eib, Eib0; cbn [filter]; rewrite Hst.
      rewrite (filter_ext (fun jf => daLiveA s1' (fst jf)) (fun jf => daLiveA s1 (fst jf)) (fun jf => Edl (fst jf))).
      rewrite (filter_ext (aiLiveA s1') (aiLiveA s1) Eal); reflexivity. }
    constructor; try assumption.
    - (* FenceRel: NoLive survives dropping instBuf's head *)
      unfold FenceRel, NoFenceIWait in *; rewrite Ereg, Efip, Estr.
      assert (HNL : ACC NoLive s1 -> ACC NoLive s1').
      { intros [N1 [N2 N3]]; split; [| split].
        - rewrite Ed2a; eapply Forall_impl; [| exact N1]; intros x Hx; rewrite Edl; exact Hx.
        - rewrite Eib; rewrite Eib0 in N2; apply Forall_inv_tail in N2.
          eapply Forall_impl; [| exact N2]; intros x Hx; rewrite Eal; exact Hx.
        - rewrite Efb; eapply Forall_impl; [| exact N3]; intros x Hx; unfold fbLive in *; rewrite Eep, Epe; exact Hx. }
      destruct Hf as [Hf1 [Hf2 Hf3]]; split; [| split; [| exact Hf3]].
      + intros Hp; destruct (Hf1 Hp) as [Hn Hr]; exact (conj (HNL Hn) Hr).
      + intros Hq; destruct (Hf2 Hq) as [Hp [Hn Hr]]; exact (conj Hp (conj (HNL Hn) Hr)).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite Ed2a; destruct F1 as [la [lb [Ea [Fa Fb]]]]; exists la, lb; split; [exact Ea |];
              split; (eapply Forall_impl; [intros x Hx; rewrite Edl; exact Hx |]); assumption |].
      split; [rewrite Eib; rewrite Eib0 in F2;
              destruct (StalePrefix_tail (aiLiveA s1) (dAA s1) rest F2) as [la [lb [Ea [Fa Fb]]]];
              exists la, lb; split; [exact Ea |];
              split; (eapply Forall_impl; [intros x Hx; rewrite Eal; exact Hx |]); assumption |].
      split; [rewrite Efb; destruct F3 as [la [lb [Ea [Fa Fb]]]]; exists la, lb; split; [exact Ea |];
              split; (eapply Forall_impl; [intros x Hx; unfold fbLive in *; rewrite Eep, Epe; exact Hx |]); assumption |].
      assert (Hex_d : Exists (fun j => daLiveA s1' j = true) (iD2aA s1') -> Exists (fun j => daLiveA s1 j = true) (iD2aA s1))
        by (rewrite Ed2a; intros Hx; eapply Exists_impl; [| exact Hx]; intros x Hx'; rewrite <- Edl; exact Hx').
      split.
      { intros Hx; rewrite Eib; pose proof (F4 (Hex_d Hx)) as F4'; rewrite Eib0 in F4'; apply Forall_inv_tail in F4'.
        eapply Forall_impl; [| exact F4']; intros y Hy; rewrite Eal; exact Hy. }
      split.
      { intros Hx; rewrite Efb, Eep.
        apply F5; destruct Hx as [Hx | Hx]; [left; exact (Hex_d Hx) | right].
        rewrite Eib in Hx; rewrite Eib0; right; eapply Exists_impl; [| exact Hx]; intros x Hx'; rewrite <- Eal; exact Hx'. }
      split.
      + unfold LiveChain in *; rewrite Elive, Epcc.
        refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                  (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
        intros p Hp; exact (FrontierRel_ib s1 s1' s2 p Efb Ecp Estr Efpc Epe Eep Epcc Hp).
      + exact (FetchRespRel_ib s1 s1' s2 Efb Epe Eep Ereg F7).
    - unfold WfRel; rewrite Ecp, Efb, Epcc, Ed2a, Eib, Ereg; unfold iDecode, iFetch, iDm in *.
      split; [split; [unfold iFetch; rewrite Efe; exact W1a | split; [exact W1b | split; [exact W1c |]]] |].
      + split; [exact W1d |]; split; [rewrite Eib0 in W1e; exact (Forall_inv_tail W1e) | exact W1f].
      + split; [unfold iFetch; rewrite Efe; exact (fifo_wf_deq _ _ _ W2) |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
  Qed.

  (* The new decode-to-ALU entry's register read is the read of the flushed register file: its
   * source registers avoid every pending writer (the stall test) *)
  Lemma decode_read_flush :
    forall g (s1 : IState) (fo : type FetchOut),
      ACC ScoreRel g s1 ->
      (Zmod.eqb (decCs1 fo) Zmod.zero = false -> evalReadWaitBit (decCs1 fo) (iWbA s1) = false) ->
      (Zmod.eqb (decCs2 fo) Zmod.zero = false -> evalReadWaitBit (decCs2 fo) (iWbA s1) = false) ->
      evalRegRead pcAddrInit (evalDecode fo) (iRfA s1) = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1).
  Proof.
    intros g s1 fo [_ [Swb _]] Hc1 Hc2.
    assert (Hw : forall d c, In (d, c) (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1)) ->
                             Zmod.eqb d Zmod.zero = false -> evalReadWaitBit d (iWbA s1) = true).
    { intros d c Hin Hdz; change (readWaitBit d (iWbA s1) = true); apply Swb; apply in_or_app; left.
      unfold olderWriters; apply filter_In; split; [| rewrite Hdz; reflexivity].
      apply in_or_app; right; apply in_or_app; right; apply in_map_iff; exists (d, c); split; [reflexivity | exact Hin]. }
    unfold iFlush, flushMulDiv, flushMulDivOn; symmetry.
    apply evalRegRead_flushMulDivCaps.
    - intros d c Hin Hdz Hcz Heq.
      assert (H1 : evalReadWaitBit (decCs1 fo) (iWbA s1) = false) by exact (Hc1 Hcz).
      change (decCs1 fo = d) in Heq; rewrite Heq, (Hw d c Hin Hdz) in H1; discriminate H1.
    - intros d c Hin Hdz Hcz Heq.
      assert (H1 : evalReadWaitBit (decCs2 fo) (iWbA s1) = false) by exact (Hc2 Hcz).
      change (decCs2 fo = d) in Heq; rewrite Heq, (Hw d c Hin Hdz) in H1; discriminate H1.
  Qed.

  (* A pending writer is not a source register the stall test let through *)
  Lemma avoid_of_wait :
    forall (W : list (bits RegIdxSzReal)) wb (x : bits RegIdxSzReal),
      (forall r, readWaitBit r wb = true <-> In r W) ->
      (Zmod.eqb x Zmod.zero = false -> evalReadWaitBit x wb = false) ->
      RegAvoidAll W x.
  Proof.
    intros W wb x Hiff Hx d Hd Hdz Hxz Heq; subst x.
    pose proof (proj2 (Hiff d) Hd) as Ht; change (evalReadWaitBit d wb = true) in Ht.
    rewrite (Hx Hxz) in Ht; discriminate Ht.
  Qed.

  Lemma d2aWriters_one :
    forall j r, In r (d2aWriters [j]) -> r = d2aDst j /\ Zmod.eqb r Zmod.zero = false.
  Proof.
    intros j r H; unfold d2aWriters in H; apply filter_In in H as [[<- | []] Hz].
    apply negb_true_iff in Hz; split; [reflexivity | exact Hz].
  Qed.

  (* A live head is issued: it moves to the decode-to-ALU FIFO, its destination's wait bit is set *)
  Lemma decode_issue :
    forall g (s1 s1' : IState) (s2 : SState),
      (dHeadA s1).(Snd).(Fst) = true -> aiLiveA s1 (dAA s1) = true -> ACC dCanIssue s1 = true ->
      iRfA s1' = iRfA s1 ->
      iWbA s1' = evalSetDstWaitBits (decWritesCd (dFoA s1)) (instCd (foInst (dFoA s1))) true (iWbA s1) ->
      iMemA s1' = iMemA s1 ->
      iFetchA s1' = fetch_withInstFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) (fifoDeqState (IBF s1)) ->
      D2AF s1' = fifoEnqState (D2AF s1) (dEntryA s1) ->
      iExecA s1' = iExecA s1 -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      RELG g s1 s2 ->
      RELG (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g)
                    (g_d2aFo pcAddrInit g ++ [dFoA s1]) (g_acc pcAddrInit g)) s1' s2.
  Proof.
    intros g s1 s1' s2 Hv Hlive Hci Erf Ewb Emem Efe ED Eex Edm Emd H.
    unfold dCanIssue in Hci.
    set (fo := dFoA s1) in *; set (j := dEntryA s1) in *; set (a := dAA s1) in *.
    destruct (canIssueV_true _ _ _ _ _ _ _ Hci) as [Hfull [Hc1 [Hc2 Hcd]]].
    destruct (decode_core g s1 s1' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    fetch_eqs Efe.
    pose proof (decode_read_flush g s1 fo (rr_score _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) Hc1 Hc2) as Ernd.
    destruct H as [_ _ Hl Hrp He _ _ _ Hf Hs Hfr Hw _].
    pose proof Hw as Hw0; destruct Hw0 as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (ib_head s1 W2 Hv) as [rest [Eib0 Erest]].
    assert (Eib : iInstBufA s1' = rest) by (unfold iInstBuf; rewrite Efe; exact Erest).
    assert (Ed2a : iD2aA s1' = (iD2aA s1 ++ [j])%list).
    { unfold iD2a; rewrite ED; apply fifo_to_list_enq; [exact W3 |].
      pose proof (length_fifo_to_list _ _ _ W3) as Hlen.
      assert (Hf' : Nat.eqb (Z.to_nat (Zmod.unsigned (fifo_size (D2AF s1)))) decodeCapacity = false)
        by (rewrite <- fifo_size_eqb_cap; exact Hfull).
      apply Nat.eqb_neq in Hf'; unfold fifo_wf in W3; lia. }
    assert (Eal : forall x, aiLiveA s1' x = aiLiveA s1 x) by (intros x; unfold aiLive; rewrite Eep; reflexivity).
    assert (Edl : forall x, daLiveA s1' x = daLiveA s1 x) by (intros x; unfold daLive; rewrite Eep; reflexivity).
    assert (Ejl : daLiveA s1 j = true) by (unfold daLive; apply Zmod.eqb_refl).
    assert (Ejd : d2aDst j = if decWritesCd fo then instCd (foInst fo) else Zmod.zero)
      by (unfold d2aDst, aluInCd;
          change (daAluIn j) with (evalRegRead pcAddrInit (evalDecode fo) (iRfA s1));
          rewrite regRead_writesCd; change (instCd (aluInInst (evalRegRead pcAddrInit (evalDecode fo) (iRfA s1)))
                                             = instCd (aluInInst (evalRegRead pcAddrInit (evalDecode fo) (iRfA s1)))) || idtac;
          rewrite regRead_inst; reflexivity).
    assert (Hrest : Forall (fun x => aiLiveA s1 x = true) rest)
      by (destruct Hfr as [_ [F2 _]]; rewrite Eib0 in F2; exact (StalePrefix_live_head (aiLiveA s1) a rest F2 Hlive)).
    destruct Hs as [Snd [Swb [Slen Sreg]]].
    constructor; try assumption.
    - (* FenceRel: a pending or waiting fence.i means nothing is live *)
      assert (Hcontra : ACC NoLive s1 -> False).
      { intros [_ [N2 _]]; rewrite Eib0 in N2; apply Forall_inv in N2.
        change (aiLiveA s1 a = false) in N2; rewrite Hlive in N2; discriminate N2. }
      unfold FenceRel, NoFenceIWait in *; rewrite Ereg, Efip.
      destruct Hf as [Hf1 [Hf2 Hf3]]; split; [| split; [| exact Hf3]].
      + intros Hp; exfalso; exact (Hcontra (proj1 (Hf1 Hp))).
      + intros Hq; exfalso; exact (Hcontra (proj1 (proj2 (Hf2 Hq)))).
    - (* ScoreRel *)
      unfold ScoreRel; cbv zeta; cbn [g_d2aFo]; rewrite Eow, Ed2a, Ewb, Efl.
      rewrite d2aWriters_app, app_assoc.
      assert (Hnew : forall r, In r (d2aWriters [j]) ->
                               decWritesCd fo = true /\ r = instCd (foInst fo) /\ Zmod.eqb r Zmod.zero = false).
      { intros r Hr; destruct (d2aWriters_one j r Hr) as [Er Hz]; rewrite Ejd in Er.
        destruct (decWritesCd fo); [split; [reflexivity | split; [exact Er | exact Hz]] |].
        subst r; rewrite Zmod.eqb_refl in Hz; discriminate Hz. }
      split; [| split; [| split]].
      + apply NoDup_app_iff; split; [exact Snd |]; split.
        * unfold d2aWriters; cbn [map filter]; destruct (negb (Zmod.eqb (d2aDst j) Zmod.zero));
            repeat constructor; intros [].
        * intros x Hx Hx2; destruct (Hnew x Hx2) as [Ew [Ex _]].
          pose proof (proj2 (Swb x) Hx) as Ht; change (evalReadWaitBit x (iWbA s1) = true) in Ht.
          rewrite Ex, (Hcd Ew) in Ht; discriminate Ht.
      + intros r; change (readWaitBit r) with (evalReadWaitBit r); rewrite evalReadWaitBit_setDst_true.
        destruct (andb (decWritesCd fo) (andb (negb (Zmod.eqb (instCd (foInst fo)) Zmod.zero))
                                               (Zmod.eqb r (instCd (foInst fo))))) eqn:Ec.
        * split; [intros _ | reflexivity].
          apply andb_prop in Ec as [Ew Ec]; apply andb_prop in Ec as [Ez Er].
          apply Zmod.eqb_eq in Er; subst r; apply in_or_app; right.
          unfold d2aWriters; cbn [map filter]; rewrite Ejd, Ew, Ez; left; reflexivity.
        * change (evalReadWaitBit r (iWbA s1)) with (readWaitBit r (iWbA s1)).
          rewrite Swb; split; [intros Hr; apply in_or_app; left; exact Hr |].
          intros Hr; apply in_app_or in Hr as [Hr | Hr]; [exact Hr | exfalso].
          destruct (Hnew r Hr) as [Ew [Er Hz]]; subst r.
          rewrite Ew, Hz, Zmod.eqb_refl in Ec; discriminate Ec.
      + rewrite !length_app, Slen; reflexivity.
      + intros l1 j' l2 fo' Hl1 Hnth Hlv.
        rewrite Edl in Hlv.
        induction l2 as [| y l2 _] using rev_ind.
        * apply app_inj_tail in Hl1 as [E1 E2]; subst l1 j'.
          rewrite nth_error_app2, Slen, Nat.sub_diag in Hnth by lia; cbn in Hnth; injection Hnth as <-.
          split; [exact Ernd |].
          split; [exact (avoid_of_wait _ _ _ Swb Hc1) | exact (avoid_of_wait _ _ _ Swb Hc2)].
        * rewrite app_comm_cons, app_assoc in Hl1; apply app_inj_tail in Hl1 as [E1 _].
          assert (Hlt : (length l1 < length (g_d2aFo pcAddrInit g))%nat)
            by (rewrite Slen, E1, length_app; cbn [length]; lia).
          rewrite nth_error_app1 in Hnth by exact Hlt.
          exact (Sreg l1 j' l2 fo' E1 Hnth Hlv).
    - (* FrontRel *)
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split.
      { rewrite Ed2a; destruct F1 as [la [lb [Ea [Fa Fb]]]]; exists la, (lb ++ [j])%list.
        split; [rewrite Ea, app_assoc; reflexivity |].
        split; [eapply Forall_impl; [| exact Fa]; intros x Hx; rewrite Edl; exact Hx |].
        apply Forall_app; split; [eapply Forall_impl; [| exact Fb]; intros x Hx; rewrite Edl; exact Hx |].
        constructor; [rewrite Edl; exact Ejl | constructor]. }
      split.
      { rewrite Eib; exists [], rest; split; [reflexivity | split; [constructor |]].
        eapply Forall_impl; [| exact Hrest]; intros x Hx; rewrite Eal; exact Hx. }
      split; [rewrite Efb; destruct F3 as [la [lb [Ea [Fa Fb]]]]; exists la, lb; split; [exact Ea |];
              split; (eapply Forall_impl; [intros x Hx; unfold fbLive in *; rewrite Eep, Epe; exact Hx |]); assumption |].
      split; [intros _; rewrite Eib; eapply Forall_impl; [| exact Hrest]; intros x Hx; rewrite Eal; exact Hx |].
      split; [intros _; rewrite Efb, Eep; apply F5; right; rewrite Eib0; left; exact Hlive |].
      split.
      + assert (Elive : liveInstsA (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                                            (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g ++ [fo]) (g_acc pcAddrInit g)) s1' =
                        liveInstsA g s1).
        { unfold liveInsts; cbn [g_d2aFo]; rewrite Ed2a, Eib, Eib0, (combine_snoc _ _ j fo (eq_sym Slen)).
          rewrite (filter_ext (fun jf => daLiveA s1' (fst jf)) (fun jf => daLiveA s1 (fst jf)) (fun jf => Edl (fst jf))).
          rewrite (filter_ext (aiLiveA s1') (aiLiveA s1) Eal).
          rewrite filter_app; cbn [filter fst]; rewrite Ejl, (Hlive : aiLiveA s1 (dAA s1) = true), map_app, <- app_assoc.
          reflexivity. }
        unfold LiveChain in *; rewrite Elive, Epcc.
        refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                  (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
        intros p Hp; exact (FrontierRel_ib s1 s1' s2 p Efb Ecp Estr Efpc Epe Eep Epcc Hp).
      + exact (FetchRespRel_ib s1 s1' s2 Efb Epe Eep Ereg F7).
    - (* WfRel *)
      unfold WfRel; rewrite Ecp, Efb, Epcc, Ed2a, Eib, Ereg; unfold iDecode, iFetch, iDm in *.
      split; [split; [unfold iFetch; rewrite Efe; exact W1a | split; [exact W1b | split; [exact W1c |]]] |].
      + rewrite Eib0 in W1e.
        split; [apply Forall_app; split; [exact W1d | constructor; [exact (Forall_inv W1e) | constructor]] |].
        split; [exact (Forall_inv_tail W1e) | exact W1f].
      + split; [unfold iFetch; rewrite Efe; exact (fifo_wf_deq _ _ _ W2) |].
        split; [rewrite ED; exact (fifo_wf_enq _ _ _ _ W3) |].
        split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
  Qed.

  (* --- 3. The Theorem --- *)

  Theorem stepOK_decodeAndRegReadStage : STEPOK STAGE.
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    exists s2; split; [apply NilAction; reflexivity |].
    destruct (decode_canProceed decodeCapacity (iDecodeA s1)) eqn:Hcp.
    2: { rewrite (dec_noCanProceed pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    _ s1 s1' Hsem Hcp); exists g; exact Hg. }
    destruct ((dHeadA s1).(Snd).(Fst)) eqn:Hv.
    2: { exists g; exact (decode_stutter g s1 s1' s2
                            (dec_noHead pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               _ s1 s1' Hsem Hcp Hv) Hg). }
    destruct (aiLiveA s1 (dAA s1)) eqn:Hl.
    - destruct (ACC dCanIssue s1) eqn:Hci.
      + destruct (dec_issue pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    _ s1 s1' Hsem Hcp Hv Hl Hci) as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
        eexists; exact (decode_issue g s1 s1' s2 Hv Hl Hci Erf Ewb Emem Efe ED Eex Edm Emd Hg).
      + exists g; exact (decode_stutter g s1 s1' s2
                           (dec_stall pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                              _ s1 s1' Hsem Hcp Hv Hl Hci) Hg).
    - destruct (dec_stale pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  _ s1 s1' Hsem Hcp Hv Hl) as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
      exists g; exact (decode_stale g s1 s1' s2 Hv Hl Erf Ewb Emem Efe ED Eex Edm Emd Hg).
  Qed.

End DecodeStep.
