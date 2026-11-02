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
From Cheriot.Proof Require Import RefExecAux RefExecFrame RefExecStep RefExecLive.
From Stdlib Require Import Permutation.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7 FLUSH, MULDIV-LIFT, AND LOCKSTEP COMMIT ENGINE (`RefExecFlush.v`)
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Lifting `executeNonDeferred` and `GInstStep` across `flushMulDivCaps` --- *)

Lemma SemAction_executeNonDeferred_flushMulDivCaps :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)}
         (entries : list (bits RegIdxSzReal * type FullECapWithTag))
         (pcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
         (rf0 rfMid : RfState pcAddrInit) (execOut : type ExecuteOut),
    (forall d v,
       In (d, v) entries ->
       Zmod.eqb d Zmod.zero = false ->
       Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false ->
       d <> aluDstIdx aluOut) ->
    SemAction env (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut) rf0 rfMid execOut ->
    SemAction env (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut)
      (flushMulDivCaps pcAddrInit entries rf0)
      (flushMulDivCaps pcAddrInit entries rfMid)
      execOut.
Proof.
  intros pcAddrInit env entries pcc meip mtip aluOut.
  induction entries as [| [d v] rest IH]; intros rf0 rfMid execOut Hdisj Hsem; cbn [flushMulDivCaps].
  - exact Hsem.
  - apply IH.
    + intros d' v' Hin; exact (Hdisj d' v' (or_intror Hin)).
    + apply SemAction_executeNonDeferred_writeGprVal; [| exact Hsem].
      exact (Hdisj d v (or_introl eq_refl)).
Qed.

Lemma GInstStep_flushMulDivCaps :
  forall pcAddrInit (entries : list (bits RegIdxSzReal * type FullECapWithTag))
         (rf0 rf1 : RfState pcAddrInit) (e : GEntry),
    (forall d v, In (d, v) entries -> EntryAvoids e d) ->
    GInstStep pcAddrInit rf0 rf1 e ->
    GInstStep pcAddrInit
      (flushMulDivCaps pcAddrInit entries rf0)
      (flushMulDivCaps pcAddrInit entries rf1) e.
Proof.
  intros pcAddrInit entries; induction entries as [| [d v] rest IH]; intros rf0 rf1 e Hav Hstep; cbn [flushMulDivCaps].
  - exact Hstep.
  - apply IH.
    + intros d' v' Hin; exact (Hav d' v' (or_intror Hin)).
    + exact (GInstStep_writeGprVal pcAddrInit rf0 rf1 e d v (Hav d v (or_introl eq_refl)) Hstep).
Qed.

Lemma specMulDivWb_flushMulDivCaps :
  forall pcAddrInit (entries : list (bits RegIdxSzReal * type FullECapWithTag))
         (a : type AluOutUnion) (x : type ExecuteOut) (rf : RfState pcAddrInit),
    (forall d v, In (d, v) entries -> RegAvoid d (aluDstIdx a)) ->
    specMulDivWb pcAddrInit a x (flushMulDivCaps pcAddrInit entries rf) =
    flushMulDivCaps pcAddrInit entries (specMulDivWb pcAddrInit a x rf).
Proof.
  intros pcAddrInit entries; induction entries as [| [d v] rest IH]; intros a x rf Hav; cbn [flushMulDivCaps].
  - reflexivity.
  - rewrite IH.
    + rewrite (specMulDivWb_writeGprVal pcAddrInit a x d v rf (Hav d v (or_introl eq_refl))); reflexivity.
    + intros d' v' Hin; exact (Hav d' v' (or_intror Hin)).
Qed.

Lemma Forall_false_Exists_contra :
  forall {A : Type} (f : A -> bool) (l : list A),
    Forall (fun x => f x = false) l ->
    Exists (fun x => f x = true) l ->
    False.
Proof.
  intros A f l Hf Hex.
  induction Hex as [x xs Hx | x xs Hex IH]; inversion Hf as [| ? ? Hfx Hf']; subst.
  - rewrite Hfx in Hx; discriminate Hx.
  - exact (IH Hf').
Qed.

Lemma filter_false_nil :
  forall {A : Type} (f : A -> bool) (l : list A),
    Forall (fun x => f x = false) l ->
    filter f l = [].
Proof.
  intros A f l Hf; induction Hf as [| x xs Hx Hf IH]; cbn [filter].
  - reflexivity.
  - rewrite Hx; exact IH.
Qed.

Lemma filter_fst_false_nil :
  forall {A B : Type} (f : A -> bool) (l1 : list A) (l2 : list B),
    Forall (fun x => f x = false) l1 ->
    filter (fun p => f (fst p)) (combine l1 l2) = [].
Proof.
  intros A B f l1; induction l1 as [| a l1 IH]; intros [| b l2] Hf; try reflexivity.
  inversion Hf as [| ? ? Ha Hf']; subst; cbn [combine filter fst].
  rewrite Ha; exact (IH l2 Hf').
Qed.

Section ExecFlush.
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

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation IState := (TS ITree).
  Local Abbreviation SState := (TS STree).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation iMemStA :=
    (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation iInstBufA :=
    (iInstBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchBufA :=
    (iFetchBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iStraddleA :=
    (iStraddle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchPcA :=
    (iFetchPc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iPccA :=
    (iPcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation daLiveA :=
    (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation aiLiveA :=
    (aiLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation fbLiveA :=
    (fbLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation NoLiveA :=
    (NoLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation FrontRelA :=
    (FrontRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              initLine fwcs).
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

  (* --- 2. Universal Epoch-Redirect Lemma (`redirect_FrontRel_NoLive`) --- *)

  Lemma redirect_FrontRel_NoLive :
    forall (g g' : Ghost) (s1 s1' : IState) (s2 s2' : SState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry)),
      FrontRelA g s1 s2 ->
      iD2aA s1 = j :: d2a_tail ->
      daLiveA s1 j = true ->
      iD2aA s1' = d2a_tail ->
      iInstBufA s1' = iInstBufA s1 ->
      iFetchBufA s1' = iFetchBufA s1 ->
      iRegionsA s1' = iRegionsA s1 ->
      iExecEpochA s1' = evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]) ->
      optValid (iStraddleA s1') = false ->
      iFetchPcA s1' = (iPccA s1').(Snd).(Snd).(Fst) ->
      pcAligned (iPccA s1').(Snd).(Snd).(Fst) ->
      NoLiveA s1' /\ FrontRelA g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' j d2a_tail Hfr Ed2a Hlive Ed2a' Eib Efb Ereg Eep' Estr' Efpc' Hal.
    destruct Hfr as [F1 [F2 [F3 [F4 [F5 [_ F7]]]]]].
    rewrite Ed2a in F1, F4, F5.
    assert (Hex_j : Exists (fun x => daLiveA s1 x = true) (j :: d2a_tail))
      by (left; exact Hlive).
    pose proof (StalePrefix_live_head (daLiveA s1) j d2a_tail F1 Hlive) as Hd2a_ep.
    pose proof (F4 Hex_j) as Hib_ep.
    pose proof (F5 (or_introl Hex_j)) as Hfb_ep.
    pose proof (zmod_epoch_add1_neq (iExecEpochA s1)) as Hneq_ep.
    assert (Hd2a_false : Forall (fun x => daLiveA s1' x = false) (iD2aA s1')).
    { rewrite Ed2a'; eapply Forall_impl; [| exact Hd2a_ep].
      intros x Hx; unfold daLive in *; apply Zmod.eqb_eq in Hx.
      rewrite Hx, Eep'; exact Hneq_ep. }
    assert (Hib_false : Forall (fun x => aiLiveA s1' x = false) (iInstBufA s1')).
    { rewrite Eib; eapply Forall_impl; [| exact Hib_ep].
      intros x Hx; unfold aiLive in *; apply Zmod.eqb_eq in Hx.
      rewrite Hx, Eep'; exact Hneq_ep. }
    assert (Hfb_false : Forall (fun x => fbLiveA s1' x = false) (iFetchBufA s1')).
    { rewrite Efb; eapply Forall_impl; [| exact Hfb_ep].
      intros x Hx; unfold fbLive; apply Zmod.eqb_eq in Hx.
      rewrite Hx, Eep', Hneq_ep; reflexivity. }
    assert (Hnl : NoLiveA s1')
      by (split; [exact Hd2a_false | split; [exact Hib_false | exact Hfb_false]]).
    split; [exact Hnl |].
    unfold FrontRel.
    split; [exact (StalePrefix_all_false _ _ Hd2a_false) |].
    split; [exact (StalePrefix_all_false _ _ Hib_false) |].
    split; [exact (StalePrefix_all_false _ _ Hfb_false) |].
    split; [intros Hex; exfalso; exact (Forall_false_Exists_contra _ _ Hd2a_false Hex) |].
    split; [intros [Hex | Hex]; exfalso;
             [exact (Forall_false_Exists_contra _ _ Hd2a_false Hex)
             | exact (Forall_false_Exists_contra _ _ Hib_false Hex)] |].
    split.
    - (* LiveChain: `liveInsts g' s1' = []` and `filter (fbLive s1') (iFetchBuf s1') = []` *)
      unfold LiveChain, liveInsts.
      rewrite (filter_fst_false_nil (daLiveA s1') (iD2aA s1') (g_d2aFo pcAddrInit g') Hd2a_false).
      rewrite (filter_false_nil (aiLiveA s1') (iInstBufA s1') Hib_false).
      cbn [map app LiveChainG].
      unfold FrontierRel; cbv zeta.
      rewrite (filter_false_nil (fbLiveA s1') (iFetchBufA s1') Hfb_false).
      rewrite Estr', Efpc'.
      split; [exact I | split; [constructor | split; [reflexivity | exact Hal]]].
    - (* FetchRespRel: every `fbLive s1' f = true` premise is vacuous (`false = true`)! *)
      unfold FetchRespRel, fbInRegion in *.
      rewrite Efb, Ereg.
      refine (AllPorts_impl _ _ implRegions (iRegionsA s1) _ F7).
      intros r y [C [Hc1 [Hc2 Hrd]]].
      exists C; split; [exact Hc1 | split; [exact Hc2 |]].
      intros Hopt.
      destruct (Hrd Hopt) as [f [E' [EE _]]].
      exists f, E'; split; [exact EE |].
      intros Hf_live; exfalso.
      assert (Hin_f : In f (iFetchBufA s1')).
      { rewrite Efb.
        assert (Hin_E : In f (filter (fun f0 => andb (negb (excAny (fbFetchExc f0))) (isRegionAddrB r (lineAddrOf (fbPcAddr f0)))) (iFetchBufA s1)))
          by (rewrite EE; left; reflexivity).
        apply filter_In in Hin_E as [Hin_f _]; exact Hin_f. }
      rewrite Forall_forall in Hfb_false.
      pose proof (Hfb_false f Hin_f) as Hf_false.
      rewrite Hf_false in Hf_live; discriminate Hf_live.
  Qed.

  (* --- 3. Scoreboard Update When Dequeuing Head `j` and Clearing Wait Bit --- *)

  Lemma ScoreRel_deq_clear :
    forall (g g' : Ghost) (s1 s1' : IState)
           (j : type DecodeToAluEntry) (d2a_tail : list (type DecodeToAluEntry))
           (fo0 : type FetchOut) (fo_tail : list (type FetchOut)),
      ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1 ->
      iD2aA s1 = j :: d2a_tail ->
      g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = d2a_tail ->
      g_d2aFo pcAddrInit g' = fo_tail ->
      olderWritersA s1' = olderWritersA s1 ->
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn j)) (aluInCd (daAluIn j)) false (iWbA s1) ->
      (forall l1 j2 l2 fo,
         iD2aA s1' = (l1 ++ j2 :: l2)%list ->
         nth_error fo_tail (length l1) = Some fo ->
         daLiveA s1' j2 = true ->
         daAluIn j2 = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') /\
         RegAvoidAll (olderWritersA s1' ++ d2aWriters l1) (decCs1 fo) /\
         RegAvoidAll (olderWritersA s1' ++ d2aWriters l1) (decCs2 fo)) ->
      ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g' s1'.
  Proof.
    intros g g' s1 s1' j d2a_tail fo0 fo_tail [Hnd [Hwb [Hlen _]]]
           Ed2a Efo Ed2a' Efo' Eow Ewb' Hlive_tail.
    unfold ScoreRel; cbv zeta; rewrite Eow, Ed2a', Efo'.
    rewrite Ed2a in Hnd, Hwb, Hlen; rewrite Efo in Hlen; cbn [length] in Hlen; injection Hlen as Hlen'.
    split.
    - pose proof Hnd as Hnd'; rewrite d2aWriters_cons in Hnd'.
      apply (Permutation_NoDup (Permutation_app_head _ (Permutation_app_comm _ _))) in Hnd'.
      rewrite app_assoc in Hnd'; exact (NoDup_app_remove_r _ _ Hnd').
    - split.
      + rewrite Ewb'.
        exact (waitBits_clear_head (iWbA s1) (olderWritersA s1) j d2a_tail
                 (olderWriters_nz pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
                 Hnd Hwb).
      + split; [exact Hlen' | rewrite Eow, Ed2a' in Hlive_tail; exact Hlive_tail].
  Qed.

End ExecFlush.
