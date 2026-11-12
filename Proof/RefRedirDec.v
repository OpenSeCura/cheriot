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
From Cheriot.Proof Require Import RefExecAux RefExecFrame RefExecFlush RefDecodeImpl RefDecodeStep.
From Cheriot.Proof Require Import RefRevBitRule RefRedirect RefRedirStep RefRedirFront RefRedirAsm.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * `decodeAndRegReadStage` WITH A REDIRECT PENDING (item 3.4)
 * ===========================================================================
 * In the applied view the instBuf head is dead. Issuing it adds a dead decode-to-ALU entry: it
 * still sets its destination's wait bit and counts as a pending writer (`d2aWriters` reads every
 * entry), and its fetch output joins `g_d2aFo`. *)

Local Abbreviation TS t := (TreeState ElemState t).

Section RedirDec.
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
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation STAGE :=
    (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation iFlushA := (ACC iFlush).
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
  Local Abbreviation validA := (ACC iRedirValid).
  Local Abbreviation InvA := (ACC RedirInv).
  Local Abbreviation D2AF s1 := (decode_toAluFifo decodeCapacity (iDecodeA s1)).
  Local Abbreviation IBF s1 := (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation dHeadA := (ACC dHead).
  Local Abbreviation dAA := (ACC dA).
  Local Abbreviation dFoA := (ACC dFo).
  Local Abbreviation DECSTUTTER := (ACC DecStutter).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* --- 1. Issuing a Dead Head --- *)

  Lemma decode_issue_dead :
    forall g (X X' : IState) (s2 : SState) (j : type DecodeToAluEntry),
      (dHeadA X).(Snd).(Fst) = true -> ACC dCanIssue X = true ->
      iRfA X' = iRfA X ->
      iWbA X' = evalSetDstWaitBits (decWritesCd (dFoA X)) (instCd (foInst (dFoA X))) true (iWbA X) ->
      iMemA X' = iMemA X ->
      iFetchA X' = fetch_withInstFifo pcAddrInit fetchCapacity instCapacity (iFetchA X) (fifoDeqState (IBF X)) ->
      D2AF X' = fifoEnqState (D2AF X) j ->
      iExecA X' = iExecA X -> iDmA X' = iDmA X -> iMdA X' = iMdA X ->
      daAluIn j = ACC dAluIn X -> daPredPc j = aiPredPc (dAA X) -> daLiveA X j = false ->
      NoLiveA X -> optValid (ACC iStraddle X) = false ->
      RELG g X s2 ->
      RELG (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g)
                    (g_d2aFo pcAddrInit g ++ [dFoA X]) (g_acc pcAddrInit g)) X' s2.
  Proof.
    intros g X X' s2 j Hv Hci Erf Ewb Emem Efe ED Eex Edm Emd Hj Hjp Ejl Hnl Hs H.
    unfold dCanIssue in Hci.
    set (fo := dFoA X) in *.
    destruct (canIssueV_true _ _ _ _ _ _ _ Hci) as [Hfull [_ [_ Hcd]]].
    destruct (ACC decode_core clintS clint plicS plic initLine fwcs g X X' s2 Erf Emem Edm Emd H)
      as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  X X' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  X X' Edm Emd) as Eow.
    assert (Ereg : iRegionsA X' = iRegionsA X) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Eep : iExecEpochA X' = iExecEpochA X) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA X' = iFenceIPendingA X) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA X' = iPccA X) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Efb : iFetchBufA X' = iFetchBufA X) by (unfold iFetchBuf; rewrite Efe; reflexivity).
    assert (Ecp : ACC iCurParcel X' = ACC iCurParcel X) by (unfold iCurParcel; rewrite Efe; reflexivity).
    assert (Estr : ACC iStraddle X' = ACC iStraddle X) by (unfold iStraddle; rewrite Efe; reflexivity).
    assert (Efpc : ACC iFetchPc X' = ACC iFetchPc X) by (unfold iFetchPc; rewrite Efe; reflexivity).
    assert (Epe : ACC iPredEpoch X' = ACC iPredEpoch X) by (unfold iPredEpoch; rewrite Efe; reflexivity).
    destruct H as [_ _ Hl Hrp He _ _ _ Hf Hsc Hfr Hw _].
    destruct (noLive_front_facts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                initLine fwcs g X s2 Hnl Hs Hfr) as [Hpc Hal].
    pose proof Hw as Hw0; destruct Hw0 as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (ACC ib_head X W2 Hv) as [rest [Eib0 Erest]].
    assert (Eib : iInstBufA X' = rest) by (unfold iInstBuf; rewrite Efe; exact Erest).
    assert (Ed2a : iD2aA X' = (iD2aA X ++ [j])%list).
    { unfold iD2a; rewrite ED; apply fifo_to_list_enq; [exact W3 |].
      pose proof (length_fifo_to_list _ _ _ W3) as Hlen.
      assert (Hf' : Nat.eqb (Z.to_nat (Zmod.unsigned (fifo_size (D2AF X)))) decodeCapacity = false)
        by (rewrite <- fifo_size_eqb_cap; exact Hfull).
      apply Nat.eqb_neq in Hf'; unfold fifo_wf in W3; lia. }
    assert (Eal : forall x, aiLiveA X' x = aiLiveA X x) by (intros x; unfold aiLive; rewrite Eep; reflexivity).
    assert (Edl : forall x, daLiveA X' x = daLiveA X x) by (intros x; unfold daLive; rewrite Eep; reflexivity).
    assert (Elv : fbLiveA X' = fbLiveA X) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
    assert (Ejd : d2aDst j = if decWritesCd fo then instCd (foInst fo) else Zmod.zero)
      by (unfold d2aDst, aluInCd; rewrite Hj; unfold dAluIn;
          rewrite regRead_writesCd; rewrite regRead_inst; reflexivity).
    assert (Hnl' : NoLiveA X').
    { destruct Hnl as [N1 [N2 N3]]; split; [| split].
      - rewrite Ed2a; apply Forall_app; split.
        + revert N1; apply Forall_impl; intros x Hx; rewrite Edl; exact Hx.
        + constructor; [rewrite Edl; exact Ejl | constructor].
      - rewrite Eib; rewrite Eib0 in N2; apply Forall_inv_tail in N2.
        revert N2; apply Forall_impl; intros x Hx; rewrite Eal; exact Hx.
      - rewrite Efb, Elv; exact N3. }
    destruct Hsc as [Snd [Swb [Slen Sreg]]].
    constructor; try assumption.
    - refine (FenceRel_noLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                _ X X' Hf Efip (f_equal optValid Estr) Hnl' _).
      unfold NoFenceIWait; rewrite Ereg; exact (fun h => h).
    - (* ScoreRel: the dead entry is a pending writer *)
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
          pose proof (proj2 (Swb x) Hx) as Ht; change (evalReadWaitBit x (iWbA X) = true) in Ht.
          rewrite Ex, (Hcd Ew) in Ht; discriminate Ht.
      + intros r; change (readWaitBit r) with (evalReadWaitBit r); rewrite evalReadWaitBit_setDst_true.
        destruct (andb (decWritesCd fo) (andb (negb (Zmod.eqb (instCd (foInst fo)) Zmod.zero))
                                               (Zmod.eqb r (instCd (foInst fo))))) eqn:Ec.
        * split; [intros _ | reflexivity].
          apply andb_prop in Ec as [Ew Ec]; apply andb_prop in Ec as [Ez Er].
          apply Zmod.eqb_eq in Er; subst r; apply in_or_app; right.
          unfold d2aWriters; cbn [map filter]; rewrite Ejd, Ew, Ez; left; reflexivity.
        * change (evalReadWaitBit r (iWbA X)) with (readWaitBit r (iWbA X)).
          rewrite Swb; split; [intros Hr; apply in_or_app; left; exact Hr |].
          intros Hr; apply in_app_or in Hr as [Hr | Hr]; [exact Hr | exfalso].
          destruct (Hnew r Hr) as [Ew [Er Hz]]; subst r.
          rewrite Ew, Hz, Zmod.eqb_refl in Ec; discriminate Ec.
      + rewrite !length_app, Slen; reflexivity.
      + intros l1 j' l2 fo' Hl1 Hnth Hlv.
        rewrite Edl in Hlv.
        induction l2 as [| y l2 _] using rev_ind.
        * apply app_inj_tail in Hl1 as [E1 E2]; subst l1 j'.
          rewrite Ejl in Hlv; discriminate Hlv.
        * rewrite app_comm_cons, app_assoc in Hl1; apply app_inj_tail in Hl1 as [E1 _].
          assert (Hlt : (length l1 < length (g_d2aFo pcAddrInit g))%nat)
            by (rewrite Slen, E1, length_app; cbn [length]; lia).
          rewrite nth_error_app1 in Hnth by exact Hlt.
          exact (Sreg l1 j' l2 fo' E1 Hnth Hlv).
    - apply (FrontRel_noLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
               initLine fwcs _ X' s2 Hnl'); [rewrite Estr; exact Hs | rewrite Efpc, Epcc; exact Hpc |
                                             rewrite Epcc; exact Hal |].
      exact (ACC FetchRespRel_ib initLine fwcs X X' s2 Efb Epe Eep Ereg (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hfr))))))).
    - unfold WfRel; rewrite Ecp, Efb, Epcc, Ed2a, Eib, Ereg; unfold iDecode, iFetch, iDm in *.
      split; [split; [unfold iFetch; rewrite Efe; exact W1a | split; [exact W1b | split; [exact W1c |]]] |].
      + rewrite Eib0 in W1e.
        split; [apply Forall_app; split; [exact W1d | constructor; [rewrite Hjp; exact (Forall_inv W1e) | constructor]] |].
        split; [exact (Forall_inv_tail W1e) | exact W1f].
      + split; [unfold iFetch; rewrite Efe; exact (fifo_wf_deq _ _ _ W2) |].
        split; [rewrite ED; exact (fifo_wf_enq _ _ _ _ W3) |].
        split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
  Qed.


  (* --- 2. The Stage --- *)

  Lemma dec_applied :
    forall (s1 s1' : IState),
      iExecA s1' = iExecA s1 ->
      iExecA (applyPA s1') = iExecA (applyPA s1) /\
      iFetchA (applyPA s1') =
        fetch_withPc pcAddrInit fetchCapacity instCapacity
          (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1') (getDefault (Option StraddleHalf)))
          (ACC redirTarget s1).
  Proof.
    intros s1 s1' Eex; split.
    - rewrite !applyP_exec; unfold iExecEpoch; rewrite Eex; reflexivity.
    - rewrite applyP_fetch; unfold redirTarget, redirPcc, iRedirect; rewrite Eex; reflexivity.
  Qed.

  Lemma pend_stutterD :
    forall g (s1 s1' : IState) (s2 : SState),
      DECSTUTTER s1 s1' -> RELG g (applyPA s1) s2 -> RELG g (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] Hg.
    destruct (dec_applied s1 s1' Eex) as [Eex' Efe'].
    refine (ACC decode_stutter clintS clint plicS plic initLine fwcs g (applyPA s1) (applyPA s1') s2 _ Hg).
    unfold DecStutter; split; [exact Erf | split; [exact Ewb | split; [exact Emem | split; [| split; [exact ED | split; [exact Eex' | exact (conj Edm Emd)]]]]]].
    rewrite Efe', Efe, applyP_fetch; reflexivity.
  Qed.

  Lemma decode_pending :
    forall g (s1 s1' : IState) (s2 : SState),
      SemAction envI STAGE s1 s1' Zmod.zero -> validA s1 = true -> InvA s1 ->
      RELG g (applyPA s1) s2 -> exists g', RELG g' (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 Hsem Hv Hi Hg.
    pose proof (pending_noLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 Hv Hi) as Hnl.
    assert (Hhd : (dHeadA s1).(Snd).(Fst) = true -> aiLiveA (applyPA s1) (dAA s1) = false).
    { intros Hhv.
      assert (W2 : fifo_wf (IBF s1)) by (destruct Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; exact (proj1 (proj2 Hw))).
      destruct (ACC ib_head s1 W2 Hhv) as [rest [Eib0 _]].
      destruct Hnl as [_ [N2 _]]; change (Forall (fun a => aiLiveA (applyPA s1) a = false) (iInstBufA s1)) in N2.
      rewrite Eib0 in N2; exact (Forall_inv N2). }
    destruct (decode_canProceed decodeCapacity (iDecodeA s1)) eqn:Hcp.
    2: { rewrite (ACC dec_noCanProceed _ s1 s1' Hsem Hcp); exists g; exact Hg. }
    destruct ((dHeadA s1).(Snd).(Fst)) eqn:Hhv.
    2: { exists g; exact (pend_stutterD g s1 s1' s2 (ACC dec_noHead _ s1 s1' Hsem Hcp Hhv) Hg). }
    pose proof (Hhd eq_refl) as Hdead.
    destruct (aiLiveA s1 (dAA s1)) eqn:Hl.
    - destruct (ACC dCanIssue s1) eqn:Hci.
      + destruct (ACC dec_issue _ s1 s1' Hsem Hcp Hhv Hl Hci) as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
        destruct (dec_applied s1 s1' Eex) as [Eex' Efe'].
        eexists.
        refine (decode_issue_dead g (applyPA s1) (applyPA s1') s2 (ACC dEntry s1) Hhv Hci Erf Ewb Emem _ ED Eex' Edm Emd
                  eq_refl eq_refl _ Hnl (applyP_noStraddle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1) Hg).
        * rewrite Efe', Efe, applyP_fetch; reflexivity.
        * unfold daLive; rewrite applyP_epoch.
          change (Zmod.eqb (iExecEpochA s1) (nextEpoch (iExecEpochA s1)) = false).
          exact (zmod_epoch_add1_neq _).
      + exists g; exact (pend_stutterD g s1 s1' s2 (ACC dec_stall _ s1 s1' Hsem Hcp Hhv Hl Hci) Hg).
    - destruct (ACC dec_stale _ s1 s1' Hsem Hcp Hhv Hl) as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
      destruct (dec_applied s1 s1' Eex) as [Eex' Efe'].
      exists g; refine (ACC decode_stale clintS clint plicS plic initLine fwcs g (applyPA s1) (applyPA s1') s2
                          Hhv Hdead Erf Ewb Emem _ ED Eex' Edm Emd Hg).
      rewrite Efe', Efe, applyP_fetch; reflexivity.
  Qed.

  (* `RedirInv` across a decode step: the new entry carries the current epoch *)
  Lemma inv_dec :
    forall (s1 s1' : IState) (D : list (type DecodeToAluEntry)) q,
      iRfA s1' = iRfA s1 -> iExecA s1' = iExecA s1 ->
      iFetchA s1' = fetch_withInstFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) q ->
      (forall P : type AssembledInst -> Prop, Forall P (iInstBufA s1) -> Forall P (fifo_to_list q)) ->
      iD2aA s1' = (iD2aA s1 ++ D)%list -> Forall (fun j => daExecEpoch j = iExecEpochA s1) D ->
      InvA s1 -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' D q Erf Eex Efe Hq Ed2a HD H.
    assert (Ev : validA s1' = validA s1) by (unfold iRedirValid; rewrite Eex; reflexivity).
    split; [| exact Ev].
    assert (E2 : ACC iFetchPcc s1' = ACC iFetchPcc s1) by (unfold iFetchPcc; rewrite Efe; reflexivity).
    assert (E3 : ACC iFetchFip s1' = ACC iFetchFip s1) by (unfold iFetchFip; rewrite Efe; reflexivity).
    assert (E4 : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (E5 : ACC redirPcc s1' = ACC redirPcc s1) by (unfold redirPcc, iRedirect; rewrite Eex; reflexivity).
    assert (E6 : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (E7 : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (E9 : iFetchBufA s1' = iFetchBufA s1) by (unfold iFetchBuf; rewrite Efe; reflexivity).
    assert (E10 : forall P, Forall P (iInstBufA s1) -> Forall P (iInstBufA s1'))
      by (intros P HP; unfold iInstBuf; rewrite Efe; exact (Hq P HP)).
    unfold RedirInv in *; rewrite Ev, E2, E3, E4, E5, E6, E7, E9, Ed2a.
    destruct H as [I1 [I2 I3]]; split; [exact I1 | split; [exact I2 |]].
    intros hv; destruct (I3 hv) as [B1 [B2 [B3 B4]]].
    exact (conj B1 (conj (proj2 (Forall_app _ _ _) (conj B2 HD)) (conj (E10 _ B3) B4))).
  Qed.

  Lemma decode_inv :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero -> fifo_wf (IBF s1) -> fifo_wf (D2AF s1) ->
      InvA s1 -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' Hsem W2 W3 Hi.
    assert (Hdeq : forall P : type AssembledInst -> Prop,
                     Forall P (iInstBufA s1) -> Forall P (fifo_to_list (fifoDeqState (IBF s1)))).
    { intros P HP; rewrite (fifo_to_list_deq _ _ _ W2); exact (RefRedirAsm.Forall_tl _ _ HP). }
    assert (Hst : DECSTUTTER s1 s1' -> InvA s1' /\ validA s1' = validA s1).
    { intros [Erf [_ [_ [Efe [ED [Eex _]]]]]].
      refine (inv_dec s1 s1' [] (IBF s1) Erf Eex _ (fun P HP => HP) _ (Forall_nil _) Hi).
      - rewrite Efe; reflexivity.
      - rewrite app_nil_r; unfold iD2a; rewrite ED; reflexivity. }
    destruct (decode_canProceed decodeCapacity (iDecodeA s1)) eqn:Hcp.
    2: { rewrite (ACC dec_noCanProceed _ s1 s1' Hsem Hcp); exact (conj Hi eq_refl). }
    destruct ((dHeadA s1).(Snd).(Fst)) eqn:Hhv; [| exact (Hst (ACC dec_noHead _ s1 s1' Hsem Hcp Hhv))].
    destruct (aiLiveA s1 (dAA s1)) eqn:Hl.
    - destruct (ACC dCanIssue s1) eqn:Hci; [| exact (Hst (ACC dec_stall _ s1 s1' Hsem Hcp Hhv Hl Hci))].
      destruct (ACC dec_issue _ s1 s1' Hsem Hcp Hhv Hl Hci) as [Erf [_ [_ [Efe [ED [Eex _]]]]]].
      refine (inv_dec s1 s1' [ACC dEntry s1] _ Erf Eex Efe Hdeq _ _ Hi).
      + unfold dCanIssue in Hci; destruct (canIssueV_true _ _ _ _ _ _ _ Hci) as [Hfull _].
        unfold iD2a; rewrite ED; apply fifo_to_list_enq; [exact W3 |].
        pose proof (length_fifo_to_list _ _ _ W3) as Hlen.
        assert (Hf' : Nat.eqb (Z.to_nat (Zmod.unsigned (fifo_size (D2AF s1)))) decodeCapacity = false)
          by (rewrite <- fifo_size_eqb_cap; exact Hfull).
        apply Nat.eqb_neq in Hf'; unfold fifo_wf in W3; lia.
      + constructor; [reflexivity | constructor].
    - destruct (ACC dec_stale _ s1 s1' Hsem Hcp Hhv Hl) as [Erf [_ [_ [Efe [ED [Eex _]]]]]].
      refine (inv_dec s1 s1' [] _ Erf Eex Efe Hdeq _ (Forall_nil _) Hi).
      rewrite app_nil_r; unfold iD2a; rewrite ED; reflexivity.
  Qed.

  (* An enqueue keeps the head of a non-empty FIFO *)
  Lemma firstVal_enq :
    forall (f : TS (ShiftFifo.fifoTree decodeCapacity DecodeToAluEntry)) v,
      fifo_wf f -> (Datatypes.length (fifo_to_list f) < decodeCapacity)%nat ->
      (fifoFirstVal f).(Snd).(Fst) = true -> fifoFirstVal (fifoEnqState f v) = fifoFirstVal f.
  Proof.
    intros f v Hw Hlt Hv.
    pose proof (fifo_wf_enq _ _ f v Hw) as Hw'.
    pose proof (fifo_to_list_enq _ _ f v Hw Hlt) as Henq.
    rewrite (fifoFirstVal_valid _ _ f Hw) in Hv.
    destruct (fifo_to_list f) as [| x l] eqn:El; [discriminate Hv |].
    assert (El' : fifo_to_list (fifoEnqState f v) = x :: (l ++ [v])%list)
      by (rewrite Henq; reflexivity).
    assert (D1 : (fifoFirstVal (fifoEnqState f v)).(Fst) = (fifoFirstVal f).(Fst))
      by (rewrite (fifoFirstVal_data _ _ _ x _ El'), (fifoFirstVal_data _ _ _ x _ El); reflexivity).
    assert (D2 : (fifoFirstVal (fifoEnqState f v)).(Snd).(Fst) = (fifoFirstVal f).(Snd).(Fst))
      by (rewrite (fifoFirstVal_valid _ _ _ Hw'), (fifoFirstVal_valid _ _ _ Hw), El', El; reflexivity).
    revert D1 D2; destruct (fifoFirstVal (fifoEnqState f v)) as [a [b []]]; destruct (fifoFirstVal f) as [a' [b' []]].
    cbn [Fst Snd]; intros -> ->; reflexivity.
  Qed.

  (* The hand-off: decode keeps the head of the hand-off FIFO when it has one *)
  Lemma decode_hand :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> fifo_wf (D2AF s1) ->
      ACC HandInv s1 -> ACC HandInv s1'.
  Proof.
    intros s1 s1' Hsem W3 Hh.
    assert (Hfr : forall f, iRfA s1' = iRfA s1 -> iMemA s1' = iMemA s1 -> iExecA s1' = iExecA s1 -> iDmA s1' = iDmA s1 ->
                  D2AF s1' = f -> ((fifoFirstVal (D2AF s1)).(Snd).(Fst) = true -> fifoFirstVal f = fifoFirstVal (D2AF s1)) ->
                  ACC HandInv s1').
    { intros f Erf Emem Eex Edm ED Ehd; revert Hh; apply (ACC HandInv_frame);
        unfold hdHead, hdDmFull, iRedirValid, iPcc;
        rewrite ?Eex, ?Erf, ?Edm, ?Emem; first [reflexivity | intros h; exact h | idtac].
      rewrite ED; exact Ehd. }
    assert (Hst : DECSTUTTER s1 s1' -> ACC HandInv s1')
      by (intros [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]]; exact (Hfr _ Erf Emem Eex Edm ED (fun _ => eq_refl))).
    destruct (decode_canProceed decodeCapacity (iDecodeA s1)) eqn:Hcp.
    2: { rewrite (ACC dec_noCanProceed _ s1 s1' Hsem Hcp); exact Hh. }
    destruct ((dHeadA s1).(Snd).(Fst)) eqn:Hhv; [| exact (Hst (ACC dec_noHead _ s1 s1' Hsem Hcp Hhv))].
    destruct (aiLiveA s1 (dAA s1)) eqn:Hl.
    - destruct (ACC dCanIssue s1) eqn:Hci; [| exact (Hst (ACC dec_stall _ s1 s1' Hsem Hcp Hhv Hl Hci))].
      destruct (ACC dec_issue _ s1 s1' Hsem Hcp Hhv Hl Hci) as [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]].
      refine (Hfr _ Erf Emem Eex Edm ED _).
      unfold dCanIssue in Hci; destruct (canIssueV_true _ _ _ _ _ _ _ Hci) as [Hfull _].
      apply firstVal_enq; [exact W3 |].
      pose proof (length_fifo_to_list _ _ _ W3) as Hlen.
      assert (Hf' : Nat.eqb (Z.to_nat (Zmod.unsigned (fifo_size (D2AF s1)))) decodeCapacity = false)
        by (rewrite <- fifo_size_eqb_cap; exact Hfull).
      apply Nat.eqb_neq in Hf'; unfold fifo_wf in W3; lia.
    - destruct (ACC dec_stale _ s1 s1' Hsem Hcp Hhv Hl) as [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]].
      exact (Hfr _ Erf Emem Eex Edm ED (fun _ => eq_refl)).
  Qed.

  Theorem stepOK_decode : STEPOKRR STAGE.
  Proof.
    intros s1 s1' s2 Hsem _ [Hi [Hh [g Hg]]].
    assert (Hw : fifo_wf (IBF s1) /\ fifo_wf (D2AF s1)).
    { pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; unfold effS in Hw.
      destruct (validA s1); exact (conj (proj1 (proj2 Hw)) (proj1 (proj2 (proj2 Hw)))). }
    destruct (decode_inv s1 s1' Hsem (proj1 Hw) (proj2 Hw) Hi) as [Hi' Ev].
    pose proof (decode_hand s1 s1' Hsem (proj2 Hw) Hh) as Hh'.
    destruct (validA s1) eqn:Hv.
    - erewrite effS_true in Hg by exact Hv.
      destruct (decode_pending g s1 s1' s2 Hsem Hv Hi Hg) as [g' Hg'].
      exists s2; split; [apply NilAction; reflexivity |]; split; [exact Hi' | split; [exact Hh' | exists g']].
      erewrite effS_true by exact Ev; exact Hg'.
    - erewrite effS_false in Hg by exact Hv.
      destruct (ACC stepOK_decodeAndRegReadStage clintS clint plicS plic initLine fwcs s1 s1' s2 Hsem (ex_intro _ g Hg))
        as [s2' [Hss [g' Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact Hi' | split; [exact Hh' | exists g']].
      erewrite effS_false by exact Ev; exact Hg'.
  Qed.

End RedirDec.
