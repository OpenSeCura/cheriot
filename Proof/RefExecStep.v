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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker RefSpecRead RefSpecFetch RefReplay.
From Cheriot.Proof Require Import RefExecAux RefExecFrame.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.
Unset Guard Checking.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7 RELATION TRANSITION ENGINE (`RefExecStep.v`)
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma dmLoadRq_excl :
  forall st, dmLoadRq st = true ->
    dmLoadRp st = false /\ dmRevRq st = false /\ dmRevRp st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Section ExecStep.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
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
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation IState := (TS ITree).
  Local Abbreviation SState := (TS STree).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).

  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELNE :=
    (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).

  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA :=
    (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA :=
    (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iMemA :=
    (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA :=
    (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA :=
    (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchA :=
    (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA :=
    (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA :=
    (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation iExecEpochA :=
    (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA :=
    (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iD2aA :=
    (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iDmBufA :=
    (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA :=
    (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation daLiveA :=
    (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation olderWritersA :=
    (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).

  (* --- 1. Empty DataMem + No Pending Write Quiescence (`empty_dm_quiescent`) --- *)

  Lemma WrStageRel_false :
    forall addr size pkt st (s1 : IState),
      msWriteRq (iMemStA s1) = false ->
      noPortWriteB implRegions (iRegionsA s1) = true ->
      WrStageRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                 addr size pkt st s1 -> False.
  Proof.
    intros addr size pkt [b | b] s1 Hms Hnp [_ Hwr].
    - destruct Hwr as [Hw _]; rewrite Hms in Hw; discriminate Hw.
    - destruct Hwr as [_ [Hk Hp]].
      pose proof (noPortWriteB_false (lineOf b addr) (buildW b addr pkt size) implRegions (iRegionsA s1) Hk) as Hf.
      assert (Himp : AllPorts (fun r y => isRegionAddrB r (lineOf b addr) = true ->
                                          extPortRq r y = someWrite (buildW b addr pkt size))
                       implRegions (iRegionsA s1)).
      { refine (AllPorts_impl _ _ implRegions (iRegionsA s1) _ Hp).
        intros r y [_ Hy] Hr; rewrite Hr in Hy; exact Hy. }
      specialize (Hf Himp); rewrite Hnp in Hf; discriminate Hf.
  Qed.

  Lemma empty_dm_quiescent :
    forall g (s1 : IState) (s2 : SState),
      RELG g s1 s2 ->
      iDmBufA s1 = [] ->
      dmLoadRq (iDmStA s1) = true ->
      msWriteRq (iMemStA s1) = false ->
      noPortWriteB implRegions (iRegionsA s1) = true ->
      g_chain pcAddrInit g = [] /\
      g_cnwb pcAddrInit g = None /\
      optValid (sSecondA s2) = false /\
      g_rf0 pcAddrInit g = iFlushA s1 /\
      sRfA s2 = iFlushA s1.
  Proof.
    intros g s1 s2 Hg Hbuf Hlrq Hms Hnp.
    destruct (dmLoadRq_excl _ Hlrq) as [Hlrp [_ Hrrp]].
    destruct Hg as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    destruct Hc as [Hc1 _]; specialize (Hc1 Hlrq) as Hcnwb.
    assert (Hacc_facts : optValid (sSecondA s2) = false /\
                         accTakesHead (g_acc pcAddrInit g) = false).
    { unfold AccessRel in Ha.
      destruct (g_acc pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt st];
        cbn [accTakesHead] in *.
      - split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Ha)))))) | reflexivity].
      - exfalso; destruct Ha as [Hwr _]; exact (WrStageRel_false addr size pkt st s1 Hms Hnp Hwr).
      - exfalso; destruct Ha as [_ [_ [H _]]]; rewrite Hlrp in H; discriminate H.
      - exfalso; destruct Ha as [_ [_ [H _]]]; rewrite Hrrp in H; discriminate H.
      - split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Ha)))))) | reflexivity].
      - split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Ha)))))) | reflexivity].
      - exfalso; destruct Ha as [Hwr _]; exact (WrStageRel_false addr capSz pkt st s1 Hms Hnp Hwr). }
    destruct Hacc_facts as [Hsec Hntake].
    assert (Hch : g_chain pcAddrInit g = []).
    { destruct He as [Hch | [e [G' [Hch [Hsec' | Hblk]]]]]; [exact Hch | rewrite Hsec in Hsec'; discriminate Hsec' |].
      exfalso.
      unfold DmQueueRel in Hd; cbv zeta in Hd; rewrite Hbuf, Hntake, Hch in Hd; cbn [chainReqs flat_map] in Hd.
      unfold entryBlocking in Hblk.
      destruct (entryReq e) as [q |] eqn:Eq; [| discriminate Hblk].
      cbn [app filter] in Hd; rewrite Hblk in Hd; discriminate Hd. }
    destruct Hrf as [R1 [R2 _]].
    rewrite Hch in R2; inversion R2; subst.
    rewrite Hcnwb in R1; cbn [cnwbApply] in R1.
    repeat split; first [exact Hch | exact Hcnwb | exact Hsec | reflexivity | exact R1].
  Qed.

  (* --- 2. Stale Head Drop Preserves `RefRelG` (`step_stale_drop`) --- *)

  Lemma step_stale_drop :
    forall g (s1 s1' : IState) (s2 : SState) (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry)),
      RELG g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      iD2aA s1' = d2a_tail ->
      daLiveA s1 j = false ->
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn j)) (aluInCd (daAluIn j)) false (iWbA s1) ->
      fifo_wf (decode_toAluFifo decodeCapacity (iDecodeA s1')) ->
      iRfA s1' = iRfA s1 ->
      iMemA s1' = iMemA s1 ->
      iFetchA s1' = iFetchA s1 ->
      iDmA s1' = iDmA s1 ->
      iMdA s1' = iMdA s1 ->
      iExecEpochA s1' = iExecEpochA s1 ->
      iFenceIPendingA s1' = iFenceIPendingA s1 ->
      exists g', RELG g' s1' s2.
  Proof.
    intros g s1 s1' s2 j d2a_tail Hg Ed2a Ed2a' Hstale Ewb' Hwf_dec Erf Emem Efe Edm Emd Eep Efip.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Edlive : forall x, daLiveA s1' x = daLiveA s1 x)
      by (intros x; unfold daLive; rewrite Eep; reflexivity).
    destruct Hg as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    destruct Hs as [Hnd [Hwb [Hlen Hreg]]].
    rewrite Ed2a in Hlen.
    destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen; discriminate Hlen |].
    cbn [length] in Hlen; injection Hlen as Hlen'.
    set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g)
                       (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g) fo_tail (g_acc pcAddrInit g)).
    exists g'; constructor.
    - unfold RfRel in *; cbn [g_chain g_rf0 g_cnwb]; rewrite Efl; exact Hrf.
    - unfold MemRelC in *; cbn [g_revOff]; rewrite Ereg; exact Hm.
    - unfold LatchRel in *; cbn [g_chain]; exact Hl.
    - unfold ReplayRel in *; cbn [g_chain g_rf0]; exact Hrp.
    - unfold EagerRel in *; cbn [g_chain]; exact He.
    - eapply AccessRel_frame with (s1 := s1) (s2 := s2);
        try reflexivity;
        try (unfold iMemSt, iRequester, iReadRp, iDmSt, iRevPhase, iRev, iRegions; rewrite ?Emem, ?Edm; reflexivity);
        exact Ha.
    - unfold CnwbRel in *; cbn [g_cnwb g_chain g_acc]; unfold iDmSt in *; rewrite Edm; exact Hc.
    - unfold DmQueueRel, iDmBuf in *; cbn [g_chain g_acc]; rewrite Edm; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; cbn [g_chain]; rewrite Ereg, Efip.
      destruct Hf as [Hf1 Hf2]; split.
      + intros Hp; destruct (Hf1 Hp) as [[Hnl1 [Hnl2 Hnl3]] [Hst Hrest]].
        rewrite Ed2a in Hnl1; inversion Hnl1 as [| ? ? _ Hnl1'].
        split.
        * unfold NoLive in *; rewrite Ed2a'.
          split; [eapply Forall_impl; [intros y1 Hy1; rewrite Edlive; exact Hy1 | exact Hnl1'] |].
          unfold aiLive, fbLive, iInstBuf, iFetchBuf, iPredEpoch in *; rewrite Efe, Eep; split; [exact Hnl2 | exact Hnl3].
        * unfold iStraddle in *; rewrite Efe; split; [exact Hst | exact Hrest].
      + intros Hnw; destruct (Hf2 Hnw) as [Hp [[Hnl1 [Hnl2 Hnl3]] [Hst Hno]]].
        rewrite Ed2a in Hnl1; inversion Hnl1 as [| ? ? _ Hnl1'].
        split; [exact Hp | split; [| unfold iStraddle in *; rewrite Efe; split; [exact Hst | exact Hno]]].
        unfold NoLive in *; rewrite Ed2a'.
        split; [eapply Forall_impl; [intros y2 Hy2; rewrite Edlive; exact Hy2 | exact Hnl1'] |].
        unfold aiLive, fbLive, iInstBuf, iFetchBuf, iPredEpoch in *; rewrite Efe, Eep; split; [exact Hnl2 | exact Hnl3].
    - (* ScoreRel *)
      unfold ScoreRel; cbn [g_d2aFo]; rewrite Eow, Ed2a', Efl.
      rewrite Ed2a in Hnd, Hwb.
      split.
      + (* NoDup (olderWritersA s1 ++ d2aWriters d2a_tail) *)
        unfold d2aWriters in Hnd |- *; cbn [filter] in Hnd.
        destruct (aluInWritesCd (daAluIn j)) eqn:Ew; [| exact Hnd].
        cbn [map] in Hnd.
        rewrite NoDup_app_iff in Hnd; destruct Hnd as [Ho [Hdup Hdisj]].
        inversion Hdup as [| ? ? Hnin H2]; subst.
        rewrite NoDup_app_iff; split; [exact Ho | split; [exact H2 |]].
        intros u Hu Hin; exact (Hdisj u Hu (or_intror Hin)).
      + split.
        * (* Wait-bit characterization after `evalSetDstWaitBits` *)
          intros r; rewrite Ewb'.
          change (readWaitBit r) with (evalReadWaitBit r) in *.
          rewrite evalReadWaitBit_setDst_false.
          unfold d2aWriters in Hwb |- *; cbn [filter] in Hwb.
          destruct (aluInWritesCd (daAluIn j)) eqn:Ew; cbn [andb].
          -- cbn [map] in Hwb.
             destruct (Zmod.eqb r (aluInCd (daAluIn j))) eqn:Eq.
             ++ apply Zmod.eqb_eq in Eq; subst r.
                split; [intros Hfalse; discriminate Hfalse |].
                intros Hin; exfalso.
                unfold d2aWriters in Hnd; cbn [filter] in Hnd; rewrite Ew in Hnd; cbn [map] in Hnd.
                rewrite NoDup_app_iff in Hnd; destruct Hnd as [_ [Hdup Hdisj]].
                inversion Hdup as [| ? ? Hnin _]; subst.
                apply in_app_or in Hin as [Hin | Hin].
                ** exact (Hdisj _ Hin (or_introl eq_refl)).
                ** exact (Hnin Hin).
             ++ rewrite Hwb, !in_app_iff; cbn [In].
                assert (Hneq : aluInCd (daAluIn j) <> r).
                { intros Heq; subst r; rewrite Zmod.eqb_refl in Eq; discriminate Eq. }
                tauto.
          -- rewrite Hwb; reflexivity.
        * split; [exact Hlen' |].
          (* Live entries in `d2a_tail` *)
          intros l1 j2 l2 fo Hl1 Hnth Hlv2.
          rewrite Edlive in Hlv2.
          assert (Hl1_s1 : iD2aA s1 = ((j :: l1) ++ j2 :: l2)%list)
            by (rewrite Ed2a, Hl1; reflexivity).
          assert (Hnth_s1 : nth_error (fo0 :: fo_tail) (length (j :: l1)) = Some fo)
            by exact Hnth.
          destruct (Hreg (j :: l1) j2 l2 fo Hl1_s1 Hnth_s1 Hlv2) as [Hrr2 [Hcs1_2 Hcs2_2]].
          split; [exact Hrr2 |].
          assert (Hsub : forall d, In d (olderWritersA s1 ++ d2aWriters l1)%list ->
                                   In d (olderWritersA s1 ++ d2aWriters (j :: l1))%list).
          { intros d Hin; apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left; exact Hin | right].
            unfold d2aWriters in *; cbn [filter].
            destruct (aluInWritesCd (daAluIn j)); [right; exact Hin | exact Hin]. }
          split; intros d Hin; [exact (Hcs1_2 d (Hsub d Hin)) | exact (Hcs2_2 d (Hsub d Hin))].
    - (* FrontRel: `liveInsts g' s1' = liveInsts g s1` because `daLive s1 j = false`! *)
      unfold FrontRel in *; destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      rewrite Ed2a in F1, F4, F5.
      rewrite Ed2a'.
      assert (Esp1 : StalePrefix (daLiveA s1') d2a_tail).
      { assert (F1' : StalePrefix (daLiveA s1') (j :: d2a_tail)).
        { destruct F1 as [la [lb [Heq [Hfa Hfb]]]]; exists la, lb; split; [exact Heq | split];
            (eapply Forall_impl; [intros y3 Hy3; rewrite Edlive; exact Hy3 |]); [exact Hfa | exact Hfb]. }
        exact (StalePrefix_tail (daLiveA s1') j d2a_tail F1'). }
      split; [exact Esp1 |].
      unfold aiLive, fbLive, iInstBuf, iFetchBuf, iPredEpoch in *; rewrite ?Efe, ?Eep, ?Ereg.
      split; [exact F2 | split; [exact F3 |]].
      assert (Himp_ex : Exists (fun u => daLiveA s1' u = true) d2a_tail ->
                        Exists (fun u => daLiveA s1 u = true) (j :: d2a_tail)).
      { intros Hex; right; eapply Exists_impl; [intros y4 Hy4; rewrite <- Edlive; exact Hy4 | exact Hex]. }
      split; [intros Hex; exact (F4 (Himp_ex Hex)) |].
      split; [intros [Hex | Hex]; [exact (F5 (or_introl (Himp_ex Hex))) | exact (F5 (or_intror Hex))] |].
      split.
      + (* `liveInsts g' s1' = liveInsts g s1` because `daLive s1 j = false`! *)
        assert (Elive : liveInsts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA g' s1' =
                        liveInsts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA g s1).
        { unfold liveInsts; cbn [g_d2aFo]; rewrite Ed2a, Ed2a', Efo.
          unfold iInstBuf, aiLive in *; rewrite ?Efe, ?Eep.
          cbn [combine filter fst]; rewrite Hstale.
          f_equal; f_equal.
          apply filter_ext; intros y5; apply Edlive. }
        rewrite Elive.
        unfold LiveChain, FrontierRel, fbLive, iPcc, iFetchPc, iPredEpoch, iCurParcel, iStraddle, iFetchBuf in *;
          rewrite ?Erf, ?Efe, ?Eep; exact F6.
      + unfold FetchRespRel, fbInRegion, fbLive, iFetchBuf, iPredEpoch in *;
          rewrite ?Ereg, ?Efe, ?Eep; exact F7.
    - unfold WfRel in *; rewrite ?Efe, ?Edm, ?Ereg.
      destruct Hw as [W1 [W2 [_ [W4 W5]]]].
      split; [exact W1 | split; [exact W2 | split; [exact Hwf_dec | split; [exact W4 | exact W5]]]].
    - eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2);
        try reflexivity;
        try (unfold iRev, iRegions; rewrite Emem; reflexivity);
        exact Hrk.
  Qed.

End ExecStep.
