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
From Cheriot.Proof Require Import RefFetchWord RefFetchRqImpl RefFetchRqStep RefFetchAsmImpl RefFetchAsmStep RefRevBitRule RefRedirect RefRedirStep RefRedirFront.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * `fetchAssembleStage` WITH A REDIRECT PENDING (item 3.4)
 * ===========================================================================
 * In the applied view every fetchBuf entry is in the old epoch. A step that assembles from the
 * head (raw-live) adds a dead instruction, and at the end of a line drops the head as a stale
 * step would; its prediction changes (fetchPc, predEpoch, straddle) are hidden by the applied
 * view or touch only dead entries (`front_dead_frame`). *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma Forall_tl : forall {A : Type} (P : A -> Prop) (l : list A), Forall P l -> Forall P (tl l).
Proof. intros A P [| a l] H; [constructor | exact (Forall_inv_tail H)]. Qed.

Section RedirAsm.
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
    (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation validA := (ACC iRedirValid).
  Local Abbreviation InvA := (ACC RedirInv).
  Local Abbreviation FASM := (ACC FasmStep).
  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation IBF s1 := (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation FRREL := (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 initLine fwcs).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* --- 1. Dead Frontends --- *)

  Lemma noLive_of_epochs :
    forall (Y : IState) e,
      iExecEpochA Y = nextEpoch e ->
      Forall (fun j => daExecEpoch j = e) (iD2aA Y) ->
      Forall (fun a => aiExecEpoch a = e) (iInstBufA Y) ->
      Forall (fun f => fbExecEpoch f = e) (iFetchBufA Y) ->
      NoLiveA Y /\ Forall (fun f => Zmod.eqb (fbExecEpoch f) (iExecEpochA Y) = false) (iFetchBufA Y).
  Proof.
    intros Y e Ee Hd Ha Hf.
    pose proof (zmod_epoch_add1_neq e) as Hne; change (Zmod.eqb e (nextEpoch e) = false) in Hne.
    split; [split; [| split] |].
    - revert Hd; apply Forall_impl; intros j Ej; unfold daLive; rewrite Ee, Ej; exact Hne.
    - revert Ha; apply Forall_impl; intros a Ea; unfold aiLive; rewrite Ee, Ea; exact Hne.
    - revert Hf; apply Forall_impl; intros f Ef; unfold fbLive; rewrite Ee, Ef, Hne; reflexivity.
    - revert Hf; apply Forall_impl; intros f Ef; rewrite Ee, Ef; exact Hne.
  Qed.

  (* A frontend-only step on a dead frontend whose fetchBuf entries are all in another epoch: fetch
   * keeps its PC, straddle and fetchBuf; dead instructions `A` join instBuf; the parcel, the
   * prediction epoch and `canProceed` may change *)
  Lemma front_dead_frame :
    forall g (Y X' : IState) (s2 : SState) (A : list (type AssembledInst)),
      iRfA X' = iRfA Y -> iWbA X' = iWbA Y -> iMemA X' = iMemA Y -> iDecodeA X' = iDecodeA Y ->
      iExecA X' = iExecA Y -> iDmA X' = iDmA Y -> iMdA X' = iMdA Y ->
      ACC iFetchPc X' = ACC iFetchPc Y -> ACC iStraddle X' = ACC iStraddle Y -> FBF X' = FBF Y ->
      fifo_wf (IBF X') -> iInstBufA X' = (iInstBufA Y ++ A)%list ->
      Forall (fun a => aiLiveA Y a = false) A -> Forall (fun a => pcAligned (aiPredPc a)) A ->
      (optValid (ACC iCurParcel X') = true -> iFetchBufA Y <> []) ->
      NoLiveA Y -> optValid (ACC iStraddle Y) = false ->
      Forall (fun f => Zmod.eqb (fbExecEpoch f) (iExecEpochA Y) = false) (iFetchBufA Y) ->
      RELG g Y s2 -> RELG g X' s2.
  Proof.
    intros g Y X' s2 A Erf Ewb Emem ED Eex Edm Emd Efpc Estr Efbf Wib Eib HA HAal Hcp Hnl Hs HfbE H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  Y X' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  Y X' Edm Emd) as Eow.
    assert (Ed2a : iD2aA X' = iD2aA Y) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA X' = iExecEpochA Y) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA X' = iFenceIPendingA Y) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA X' = iPccA Y) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Efb : iFetchBufA X' = iFetchBufA Y) by (unfold iFetchBuf; rewrite Efbf; reflexivity).
    assert (Ereg : iRegionsA X' = iRegionsA Y) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Edl : daLiveA X' = daLiveA Y) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA X' = aiLiveA Y) by (unfold aiLive; rewrite Eep; reflexivity).
    assert (Hfb' : Forall (fun f => fbLiveA X' f = false) (iFetchBufA Y)).
    { revert HfbE; apply Forall_impl; intros f Hf; unfold fbLive; rewrite Eep, Hf; reflexivity. }
    assert (Hnl' : NoLiveA X').
    { destruct Hnl as [N1 [N2 _]]; unfold NoLive.
      rewrite Ed2a, Eib, Efb, Edl, Eal.
      exact (conj N1 (conj (proj2 (Forall_app _ _ _) (conj N2 HA)) Hfb')). }
    destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs g Y X' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    destruct H as [_ _ Hl Hrp He' _ _ _ Hfe Hsc Hfr Hwf _].
    destruct (noLive_front_facts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                initLine fwcs g Y s2 Hnl Hs Hfr) as [Hpc Hal].
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hfr)))))) as F7.
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - refine (FenceRel_noLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                g Y X' Hfe Efip (f_equal optValid Estr) Hnl' _).
      unfold NoFenceIWait; rewrite Ereg; exact (fun h => h).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hsc.
    - apply (FrontRel_noLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
               initLine fwcs g X' s2 Hnl'); [rewrite Estr; exact Hs | rewrite Efpc, Epcc; exact Hpc |
                                             rewrite Epcc; exact Hal |].
      unfold FetchRespRel, fbInRegion in *; rewrite Ereg, Efb.
      revert F7; apply AllPorts_impl; intros r y [C [H1 [H2 H3]]]; cbv zeta in H1, H2, H3 |- *.
      exists C; split; [exact H1 | split; [exact H2 |]].
      intros Hv; destruct (H3 Hv) as [f [E' [HE _]]].
      exists f, E'; split; [exact HE |].
      intros Hlv; exfalso.
      assert (Hin : In f (iFetchBufA Y)).
      { assert (Hin0 : In f (filter (fun f0 => andb (negb (excAny (fbFetchExc f0))) (isRegionAddrB r (lineAddrOf (fbPcAddr f0))))
                                    (iFetchBufA Y))) by (rewrite HE; left; reflexivity).
        apply filter_In in Hin0; exact (proj1 Hin0). }
      rewrite (proj1 (Forall_forall _ _) Hfb' f Hin) in Hlv; discriminate Hlv.
    - destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
      unfold WfRel; rewrite Epcc, Ed2a, Eib, Efb, Ereg.
      split; [split; [rewrite Efbf; exact W1a |] |].
      + split; [exact Hcp |].
        split; [exact W1c |]; split; [exact W1d |]; split; [| exact W1f].
        apply Forall_app; split; [exact W1e | exact HAal].
      + split; [exact Wib |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
    - exact Crk.
  Qed.

  (* --- 2. The Applied View of a fetchAssemble Step --- *)

  Lemma fasm_applied :
    forall (s1 s1' : IState) m f,
      FASM s1 s1' m f ->
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

  (* the state `s` with fetch replaced by `f` *)
  Definition withFetchS (s : IState) (f : TS (implFetchTree pcAddrInit fetchCapacity instCapacity)) : IState :=
    let c := s.(Fst) in
    ((c.(Fst) ,, (c.(Snd).(Fst) ,, (c.(Snd).(Snd).(Fst) ,, (c.(Snd).(Snd).(Snd).(Fst) ,,
      ((f ,, c.(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,, c.(Snd).(Snd).(Snd).(Snd).(Snd)))))) ,, s.(Snd)).

  Lemma withFetchS_exec : forall s f, iExecA (withFetchS s f) = iExecA s.
  Proof. reflexivity. Qed.

  (* What the pending relation knows: the frontend's entries, in the raw epoch *)
  Lemma pend_facts :
    forall g (s1 : IState) (s2 : SState),
      validA s1 = true -> InvA s1 -> RELG g (applyPA s1) s2 ->
      NoLiveA (applyPA s1) /\
      Forall (fun f => Zmod.eqb (fbExecEpoch f) (iExecEpochA (applyPA s1)) = false) (iFetchBufA (applyPA s1)) /\
      Forall (fun j => daExecEpoch j = iExecEpochA s1) (iD2aA s1) /\
      Forall (fun a => aiExecEpoch a = iExecEpochA s1) (iInstBufA s1) /\
      Forall (fun f => fbExecEpoch f = iExecEpochA s1) (iFetchBufA s1) /\
      WfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g (applyPA s1) s2.
  Proof.
    intros g s1 s2 Hv [_ [_ I3]] Hg; destruct (I3 Hv) as [_ [Hd [Ha Hf]]].
    destruct (noLive_of_epochs (applyPA s1) (iExecEpochA s1) (applyP_epoch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1)
                Hd Ha Hf) as [Hnl HfbE].
    refine (conj Hnl (conj HfbE (conj Hd (conj Ha (conj Hf _))))).
    destruct Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; exact Hw.
  Qed.

  Lemma asm_dead :
    forall (s1 : IState) pp, aiLiveA (applyPA s1) (ACC aAsm s1 pp) = false.
  Proof.
    intros s1 pp; unfold aiLive; rewrite applyP_epoch.
    change (Zmod.eqb (iExecEpochA s1) (nextEpoch (iExecEpochA s1)) = false).
    exact (zmod_epoch_add1_neq _).
  Qed.

  Ltac app_eq Efe := rewrite Efe, applyP_fetch; reflexivity.

  (* Steps that change only `canProceed` *)
  Lemma pend_stutter :
    forall g (s1 s1' : IState) (s2 : SState),
      FASM s1 s1' (iMemA s1) (ACC aF0 s1) -> validA s1 = true -> InvA s1 ->
      RELG g (applyPA s1) s2 -> RELG g (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 Hst Hv Hi Hg.
    destruct (pend_facts g s1 s2 Hv Hi Hg) as [Hnl [HfbE [_ [_ [_ Hw]]]]].
    destruct Hw as [[W1a [W1b _]] [W2 _]].
    pose proof Hst as [Erf [Ewb [Emem [_ [ED [_ [Edm Emd]]]]]]].
    destruct (fasm_applied s1 s1' _ _ Hst) as [Eex Efe].
    refine (front_dead_frame g (applyPA s1) (applyPA s1') s2 [] Erf Ewb Emem ED Eex Edm Emd
              _ _ _ _ _ (Forall_nil _) (Forall_nil _) _ Hnl (applyP_noStraddle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1) HfbE Hg).
    - unfold iFetchPc; app_eq Efe.
    - unfold iStraddle; app_eq Efe.
    - app_eq Efe.
    - rewrite Efe; exact W2.
    - rewrite app_nil_r; unfold iInstBuf; app_eq Efe.
    - assert (Ecp : ACC iCurParcel (applyPA s1') = ACC iCurParcel (applyPA s1)) by (unfold iCurParcel; app_eq Efe).
      rewrite Ecp; exact W1b.
  Qed.

  (* A parcel that stays in its line: one dead instruction joins instBuf *)
  Lemma pend_stay :
    forall g (s1 s1' : IState) (s2 : SState) cp,
      FASM s1 s1' (iMemA s1) (ACC fStay s1 cp (ACC aSeqPc s1)) ->
      (ACC aHead s1).(Snd).(Fst) = true -> ACC aIbFull s1 = false ->
      validA s1 = true -> InvA s1 ->
      RELG g (applyPA s1) s2 -> RELG g (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 cp Hst Hhv Hf Hv Hi Hg.
    destruct (pend_facts g s1 s2 Hv Hi Hg) as [Hnl [HfbE [_ [_ [_ Hw]]]]].
    destruct Hw as [[W1a _] [W2 _]].
    destruct (ACC fb_head s1 W1a Hhv) as [rest [Efb0 _]].
    pose proof Hst as [Erf [Ewb [Emem [_ [ED [_ [Edm Emd]]]]]]].
    destruct (fasm_applied s1 s1' _ _ Hst) as [Eex Efe].
    refine (front_dead_frame g (applyPA s1) (applyPA s1') s2 [ACC aAsm s1 (ACC aSeqPc s1)] Erf Ewb Emem ED Eex Edm Emd
              _ _ _ _ _ _ _ _ Hnl (applyP_noStraddle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1) HfbE Hg).
    - unfold iFetchPc; app_eq Efe.
    - unfold iStraddle; app_eq Efe.
    - app_eq Efe.
    - rewrite Efe; exact (fifo_wf_enq _ _ _ _ W2).
    - unfold iInstBuf; rewrite Efe, applyP_fetch; exact (fifo_to_list_enq_nf _ _ _ _ W2 Hf).
    - constructor; [exact (asm_dead s1 _) | constructor].
    - constructor; [exact (ACC seqPc_even s1) | constructor].
    - intros _; change (iFetchBufA s1 <> []); rewrite Efb0; discriminate.
  Qed.

  (* The end of a line: the head is dropped as by a stale step, then a dead instruction may join *)
  Lemma pend_eol :
    forall g (s1 s1' : IState) (s2 : SState) l2 mr',
      (ACC aPre s1 = true -> mr' = iRegionsA s1) ->
      (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) mr') ->
      FASM s1 s1' (mr' ,, (iMemA s1).(Snd)) (ACC fEol s1 l2) ->
      (ACC aHead s1).(Snd).(Fst) = true -> (ACC aPkt s1).(Snd).(Fst) = true -> ACC aIbFull s1 = false ->
      (andb (negb (ACC aInit s1)) (negb (ACC aFault s1)) = false -> l2 = ACC aDefPred s1) ->
      (andb (negb (ACC aInit s1)) (negb (ACC aFault s1)) = true ->
         pcAligned l2 /\ (ACC aNeeds s1 = false -> l2 = clearBit0 (ACC aSeqPc s1))) ->
      validA s1 = true -> InvA s1 ->
      RELG g (applyPA s1) s2 -> RELG g (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 l2 mr' Hmr1 Hmr2 Hst Hhv Hpv Hf Hl2a Hl2b Hv Hi Hg.
    destruct (pend_facts g s1 s2 Hv Hi Hg) as [Hnl [HfbE [Hd [Ha [Hfe Hw]]]]].
    destruct Hw as [[W1a [_ [_ [_ [_ W1f]]]]] [W2 _]].
    destruct (ACC fb_head s1 W1a Hhv) as [rest [Efb0 Erest]].
    pose proof Hst as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    (* the stale-like drop *)
    set (Y := applyPA (withFetchS s1' (ACC aFDrop s1))).
    assert (HstY : FASM (applyPA s1) Y (mr' ,, (iMemA (applyPA s1)).(Snd)) (ACC aFDrop (applyPA s1))).
    { unfold FasmStep; split; [exact Erf | split; [exact Ewb | split; [exact Emem | split; [| split; [exact ED | split; [| exact (conj Edm Emd)]]]]]].
      - subst Y; rewrite applyP_fetch.
        change (fetch_withPc pcAddrInit fetchCapacity instCapacity
                  (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (ACC aFDrop s1) (getDefault (Option StraddleHalf)))
                  (ACC redirTarget s1') = ACC aFDrop (applyPA s1)).
        unfold redirTarget, redirPcc, iRedirect; rewrite Eex; reflexivity.
      - subst Y; rewrite !applyP_exec, withFetchS_exec; unfold iExecEpoch; rewrite withFetchS_exec, Eex; reflexivity. }
    assert (HmX : ACC aMatch (applyPA s1) = false).
    { rewrite (ACC aMatch_eq (applyPA s1)).
      change (fbLiveA (applyPA s1) (ACC aE s1) = false).
      change (Forall (fun f => Zmod.eqb (fbExecEpoch f) (iExecEpochA (applyPA s1)) = false) (iFetchBufA s1)) in HfbE.
      rewrite Efb0 in HfbE; unfold fbLive; rewrite (Forall_inv HfbE); reflexivity. }
    pose proof (ACC asm_stale_rel clintS clint plicS plic initLine fwcs Hdisj g (applyPA s1) Y s2 mr'
                  Hmr1 Hmr2 HstY Hhv Hpv HmX Hg) as HgY.
    (* then the dead frame *)
    assert (HfbY : iFetchBufA Y = rest) by exact Erest.
    destruct (noLive_of_epochs Y (iExecEpochA s1)) as [HnlY HfbEY].
    { subst Y; rewrite applyP_epoch; unfold iExecEpoch; rewrite withFetchS_exec; exact (f_equal nextEpoch Eep). }
    { change (Forall (fun j => daExecEpoch j = iExecEpochA s1) (iD2aA s1')); unfold iD2a; rewrite ED; exact Hd. }
    { exact Ha. }
    { rewrite HfbY; rewrite Efb0 in Hfe; exact (Forall_inv_tail Hfe). }
    assert (Hl2al : ACC aInit s1 = false -> pcAligned l2).
    { intros Hinit; destruct (ACC aFault s1) eqn:Hfault.
      - rewrite (Hl2a ltac:(rewrite Hinit; reflexivity)).
        unfold aDefPred; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aInit s1))) with (ACC aInit s1).
        rewrite Hinit; cbv iota; change (pcAligned (ACC aInstPred s1)).
        unfold aInstPred; rewrite evalExpr_ITE.
        destruct (evalExpr (Eq (Var type (Bit LgFetchParcels) (ACC aLastP s1)) (Var type (Bit LgFetchParcels) (ACC aExit s1)))).
        + change (pcAligned (fbPredPc (ACC aE s1))).
          change (Forall (fun f => pcAligned (fbPredPc f)) (iFetchBufA s1)) in W1f.
          rewrite Efb0 in W1f; exact (Forall_inv W1f).
        + exact (ACC seqPc_even s1).
      - exact (proj1 (Hl2b ltac:(rewrite Hinit; reflexivity))). }
    destruct (ACC aInit s1) eqn:Hinit.
    - refine (front_dead_frame g Y (applyPA s1') s2 [] eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl _ _ _ (Forall_nil _) (Forall_nil _) _ HnlY eq_refl HfbEY HgY).
      + change (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') = fifoDeqState (FBF s1)).
        rewrite Efe; apply fEol_fbFifo.
      + change (fifo_wf (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1'))).
        rewrite Efe, fEol_instFifo, Hinit; exact W2.
      + rewrite app_nil_r.
        change (fifo_to_list (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1')) = iInstBufA s1).
        rewrite Efe, fEol_instFifo, Hinit; reflexivity.
      + intros C; exfalso.
        change (optValid (fetch_curParcelOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1')) = true) in C.
        rewrite Efe, fEol_curParcel in C; discriminate C.
    - refine (front_dead_frame g Y (applyPA s1') s2 [ACC aAsm s1 l2] eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl _ _ _ _ _ _ HnlY eq_refl HfbEY HgY).
      + change (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') = fifoDeqState (FBF s1)).
        rewrite Efe; apply fEol_fbFifo.
      + change (fifo_wf (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1'))).
        rewrite Efe, fEol_instFifo, Hinit; exact (fifo_wf_enq _ _ _ _ W2).
      + change (fifo_to_list (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1')) =
                (iInstBufA s1 ++ [ACC aAsm s1 l2])%list).
        rewrite Efe, fEol_instFifo, Hinit; exact (fifo_to_list_enq_nf _ _ _ _ W2 Hf).
      + constructor; [| constructor].
        subst Y; unfold aiLive; rewrite applyP_epoch; unfold iExecEpoch; rewrite withFetchS_exec.
        change (Zmod.eqb (iExecEpochA s1) (nextEpoch (iExecEpochA s1')) = false).
        rewrite Eep; exact (zmod_epoch_add1_neq _).
      + constructor; [exact (Hl2al eq_refl) | constructor].
      + intros C; exfalso.
        change (optValid (fetch_curParcelOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1')) = true) in C.
        rewrite Efe, fEol_curParcel in C; discriminate C.
  Qed.


  (* --- 3. The Stage --- *)

  Lemma pend_noMatch :
    forall (s1 : IState),
      validA s1 = true -> InvA s1 -> fifo_wf (FBF s1) -> (ACC aHead s1).(Snd).(Fst) = true ->
      ACC aMatch (applyPA s1) = false.
  Proof.
    intros s1 Hv [_ [_ I3]] Wfb Hhv; destruct (I3 Hv) as [_ [_ [_ Hf]]].
    destruct (ACC fb_head s1 Wfb Hhv) as [rest [Efb0 _]].
    rewrite (ACC aMatch_eq (applyPA s1)).
    change (fbLiveA (applyPA s1) (ACC aE s1) = false).
    rewrite Efb0 in Hf; unfold fbLive; rewrite applyP_epoch, (Forall_inv Hf).
    unfold nextEpoch; rewrite zmod_epoch_add1_neq; reflexivity.
  Qed.

  Lemma fetchAsm_pending :
    forall g (s1 s1' : IState) (s2 : SState),
      SemAction envI STAGE s1 s1' Zmod.zero -> validA s1 = true -> InvA s1 ->
      RELG g (applyPA s1) s2 -> RELG g (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 Hsem Hv Hi Hg.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    destruct (ACC aCp s1) eqn:Hcp.
    2: { rewrite (ACC asm_idle _ s1 s1' Hsem Hcp); exact Hg. }
    destruct ((ACC aHead s1).(Snd).(Fst)) eqn:Hhv.
    2: { exact (pend_stutter g s1 s1' s2 (ACC asm_noHead _ Hu s1 s1' Hsem Hcp Hhv) Hv Hi Hg). }
    destruct ((ACC aPkt s1).(Snd).(Fst)) eqn:Hpv.
    2: { exact (pend_stutter g s1 s1' s2 (ACC asm_noPkt _ Hu s1 s1' Hsem Hcp Hhv Hpv) Hv Hi Hg). }
    destruct (ACC aMatch s1) eqn:Hm.
    2: { destruct (ACC asm_stale _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm) as [mr' [Hmr1 [Hmr2 Hst]]].
         assert (Wfb : fifo_wf (FBF s1)) by (destruct Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; exact (proj1 (proj1 Hw))).
         pose proof Hst as [Erf [Ewb [Emem [_ [ED [_ [Edm Emd]]]]]]].
         destruct (fasm_applied s1 s1' _ _ Hst) as [Eex Efe].
         assert (HstX : FASM (applyPA s1) (applyPA s1') (mr' ,, (iMemA (applyPA s1)).(Snd)) (ACC aFDrop (applyPA s1))).
         { unfold FasmStep; split; [exact Erf | split; [exact Ewb | split; [exact Emem | split; [| split; [exact ED | split; [exact Eex | exact (conj Edm Emd)]]]]]].
           rewrite Efe; reflexivity. }
         exact (ACC asm_stale_rel clintS clint plicS plic initLine fwcs Hdisj g (applyPA s1) (applyPA s1') s2 mr'
                  Hmr1 Hmr2 HstX Hhv Hpv (pend_noMatch s1 Hv Hi Wfb Hhv) Hg). }
    destruct (ACC aIbFull s1) eqn:Hf.
    { exact (pend_stutter g s1 s1' s2 (ACC asm_ibFullStall _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf) Hv Hi Hg). }
    destruct (ACC aIsSeq s1) eqn:Hseq.
    - exact (pend_stay g s1 s1' s2 true (ACC asm_seq _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf Hseq) Hhv Hf Hv Hi Hg).
    - destruct (ACC asm_eol _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf Hseq) as [l2 [mr' [Hl2a [Hl2b [Hmr1 [Hmr2 [Heol Hstay]]]]]]].
      destruct (ACC aEol s1 l2) eqn:He.
      + exact (pend_eol g s1 s1' s2 l2 mr' Hmr1 (fun Hp => Hmr2 Hp eq_refl) (Heol eq_refl) Hhv Hpv Hf Hl2a Hl2b Hv Hi Hg).
      + pose proof (Hstay eq_refl) as Hst.
        unfold aEol in He; rewrite or2_eval, notE_eval, eqAddrE_eval in He.
        apply orb_false_iff in He as [He1 He2]; apply negb_false_iff, Zmod.eqb_eq in He1.
        change (l2 = ACC aSeqPc s1) in He1; rewrite He1 in Hst.
        exact (pend_stay g s1 s1' s2 false Hst Hhv Hf Hv Hi Hg).
  Qed.

  (* `RedirInv` across a fetchAssemble step: new instructions carry the current epoch *)
  Lemma inv_fasm :
    forall (s1 s1' : IState) m f (A : list (type AssembledInst)),
      FASM s1 s1' m f ->
      tagEcap (fetch_pccCopy pcAddrInit fetchCapacity instCapacity f) =
      tagEcap (fetch_pccCopy pcAddrInit fetchCapacity instCapacity (iFetchA s1)) ->
      fetch_fipCopy pcAddrInit fetchCapacity instCapacity f = fetch_fipCopy pcAddrInit fetchCapacity instCapacity (iFetchA s1) ->
      (forall P : type FetchBufEntry -> Prop, Forall P (iFetchBufA s1) ->
         Forall P (fifo_to_list (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity f))) ->
      fifo_to_list (fetch_instFifo pcAddrInit fetchCapacity instCapacity f) = (iInstBufA s1 ++ A)%list ->
      Forall (fun a => aiExecEpoch a = iExecEpochA s1) A ->
      InvA s1 -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' m f A [Erf [_ [_ [Efe [ED [Eex _]]]]]] Ep Efi Hfb Eib HA H.
    assert (Ev : validA s1' = validA s1) by (unfold iRedirValid; rewrite Eex; reflexivity).
    split; [| exact Ev].
    assert (E2 : tagEcap (ACC iFetchPcc s1') = tagEcap (ACC iFetchPcc s1)) by (unfold iFetchPcc; rewrite Efe; exact Ep).
    assert (E3 : ACC iFetchFip s1' = ACC iFetchFip s1) by (unfold iFetchFip; rewrite Efe; exact Efi).
    assert (E4 : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (E5 : ACC redirPcc s1' = ACC redirPcc s1) by (unfold redirPcc, iRedirect; rewrite Eex; reflexivity).
    assert (E6 : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (E7 : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (E8 : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (E9 : iInstBufA s1' = (iInstBufA s1 ++ A)%list) by (unfold iInstBuf; rewrite Efe; exact Eib).
    assert (E10 : forall P : type FetchBufEntry -> Prop, Forall P (iFetchBufA s1) -> Forall P (iFetchBufA s1'))
      by (intros P HP; unfold iFetchBuf; rewrite Efe; exact (Hfb P HP)).
    unfold RedirInv in *; rewrite Ev, E2, E3, E4, E5, E6, E7, E8, E9.
    destruct H as [I1 [I2 I3]]; split; [exact I1 | split; [exact I2 |]].
    intros hv; destruct (I3 hv) as [B1 [B2 [B3 B4]]].
    exact (conj B1 (conj B2 (conj (proj2 (Forall_app _ _ _) (conj B3 HA)) (E10 _ B4)))).
  Qed.

  Lemma fetchAsm_inv :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero -> fifo_wf (FBF s1) -> fifo_wf (IBF s1) ->
      InvA s1 -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' Hsem Wfb Wib Hi.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    assert (Hdrop : forall P : type FetchBufEntry -> Prop,
                      Forall P (iFetchBufA s1) -> Forall P (fifo_to_list (fifoDeqState (FBF s1)))).
    { intros P HP; rewrite (fifo_to_list_deq _ _ _ Wfb); exact (Forall_tl _ _ HP). }
    assert (Hsame : forall P : type FetchBufEntry -> Prop, Forall P (iFetchBufA s1) -> Forall P (iFetchBufA s1))
      by (intros P HP; exact HP).
    assert (Hf0 : forall m, FASM s1 s1' m (ACC aF0 s1) -> InvA s1' /\ validA s1' = validA s1)
      by (intros m Hst; exact (inv_fasm s1 s1' m _ [] Hst eq_refl eq_refl Hsame (eq_sym (app_nil_r _)) (Forall_nil _) Hi)).
    destruct (ACC aCp s1) eqn:Hcp.
    2: { rewrite (ACC asm_idle _ s1 s1' Hsem Hcp); exact (conj Hi eq_refl). }
    destruct ((ACC aHead s1).(Snd).(Fst)) eqn:Hhv; [| exact (Hf0 _ (ACC asm_noHead _ Hu s1 s1' Hsem Hcp Hhv))].
    destruct ((ACC aPkt s1).(Snd).(Fst)) eqn:Hpv; [| exact (Hf0 _ (ACC asm_noPkt _ Hu s1 s1' Hsem Hcp Hhv Hpv))].
    destruct (ACC aMatch s1) eqn:Hm.
    2: { destruct (ACC asm_stale _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm) as [mr' [_ [_ Hst]]].
         exact (inv_fasm s1 s1' _ _ [] Hst eq_refl eq_refl Hdrop (eq_sym (app_nil_r _)) (Forall_nil _) Hi). }
    destruct (ACC aIbFull s1) eqn:Hf; [exact (Hf0 _ (ACC asm_ibFullStall _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf)) |].
    assert (Hstay : forall cp pp m, FASM s1 s1' m (ACC fStay s1 cp pp) -> InvA s1' /\ validA s1' = validA s1).
    { intros cp pp m Hst.
      refine (inv_fasm s1 s1' m _ [ACC aAsm s1 pp] Hst eq_refl eq_refl Hsame _ _ Hi).
      - exact (fifo_to_list_enq_nf _ _ _ _ Wib Hf).
      - constructor; [reflexivity | constructor]. }
    destruct (ACC aIsSeq s1) eqn:Hseq; [exact (Hstay _ _ _ (ACC asm_seq _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf Hseq)) |].
    destruct (ACC asm_eol _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf Hseq) as [l2 [mr' [_ [_ [_ [_ [Heol Hst2]]]]]]].
    destruct (ACC aEol s1 l2) eqn:He; [| exact (Hstay _ _ _ (Hst2 eq_refl))].
    pose proof (Heol eq_refl) as Hst.
    destruct (ACC aInit s1) eqn:Hinit.
    - refine (inv_fasm s1 s1' _ _ [] Hst _ _ _ _ (Forall_nil _) Hi).
      + unfold fEol; rewrite Hinit; destruct (ACC aMis s1 l2); reflexivity.
      + unfold fEol; rewrite Hinit; destruct (ACC aMis s1 l2); reflexivity.
      + rewrite fEol_fbFifo; exact Hdrop.
      + rewrite fEol_instFifo, Hinit, app_nil_r; reflexivity.
    - refine (inv_fasm s1 s1' _ _ [ACC aAsm s1 l2] Hst _ _ _ _ _ Hi).
      + unfold fEol; rewrite Hinit; destruct (ACC aMis s1 l2); reflexivity.
      + unfold fEol; rewrite Hinit; destruct (ACC aMis s1 l2); reflexivity.
      + rewrite fEol_fbFifo; exact Hdrop.
      + rewrite fEol_instFifo, Hinit; exact (fifo_to_list_enq_nf _ _ _ _ Wib Hf).
      + constructor; [reflexivity | constructor].
  Qed.

  (* The hand-off: fetch assembly touches only fetch and the fetch side of the regions *)
  Lemma fetchAsm_hand :
    forall (s1 s1' : IState), SemAction envI STAGE s1 s1' Zmod.zero -> ACC HandInv s1 -> ACC HandInv s1'.
  Proof.
    intros s1 s1' Hsem Hh.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    assert (Hsame : forall f, FASM s1 s1' (iMemA s1) f -> ACC HandInv s1')
      by (intros f [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]]; exact (ACC HandInv_eq s1 s1' Eex ED Erf Edm Emem Hh)).
    assert (Hdq : forall mr' f, (ACC aPre s1 = true -> mr' = iRegionsA s1) ->
                  (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) mr') ->
                  FASM s1 s1' (mr' ,, (iMemA s1).(Snd)) f -> ACC HandInv s1').
    { intros mr' f _ _ [Erf [_ [Emem [_ [ED [Eex [Edm _]]]]]]].
      exact (ACC HandInv_regions s1 s1' mr' Eex ED Erf Edm Emem Hh). }
    destruct (ACC aCp s1) eqn:Hcp.
    2: { rewrite (ACC asm_idle _ s1 s1' Hsem Hcp); exact Hh. }
    destruct ((ACC aHead s1).(Snd).(Fst)) eqn:Hhv; [| exact (Hsame _ (ACC asm_noHead _ Hu s1 s1' Hsem Hcp Hhv))].
    destruct ((ACC aPkt s1).(Snd).(Fst)) eqn:Hpv; [| exact (Hsame _ (ACC asm_noPkt _ Hu s1 s1' Hsem Hcp Hhv Hpv))].
    destruct (ACC aMatch s1) eqn:Hm.
    2: { destruct (ACC asm_stale _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm) as [mr' [H1 [H2 Hst]]]; exact (Hdq mr' _ H1 H2 Hst). }
    destruct (ACC aIbFull s1) eqn:Hf; [exact (Hsame _ (ACC asm_ibFullStall _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf)) |].
    destruct (ACC aIsSeq s1) eqn:Hseq; [exact (Hsame _ (ACC asm_seq _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf Hseq)) |].
    destruct (ACC asm_eol _ Hu s1 s1' Hsem Hcp Hhv Hpv Hm Hf Hseq) as [l2 [mr' [_ [_ [H1 [H2 [Heol Hst2]]]]]]].
    destruct (ACC aEol s1 l2) eqn:He; [| exact (Hsame _ (Hst2 eq_refl))].
    refine (Hdq mr' _ H1 _ (Heol eq_refl)); intros Hp; exact (H2 Hp eq_refl).
  Qed.

  Theorem stepOK_fetchAsm : STEPOKRR STAGE.
  Proof.
    intros s1 s1' s2 Hsem _ [Hi [Hh [g Hg]]].
    exists s2; split; [apply NilAction; reflexivity |].
    assert (Hw : fifo_wf (FBF s1) /\ fifo_wf (IBF s1)).
    { pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; unfold effS in Hw.
      destruct (validA s1); exact (conj (proj1 (proj1 Hw)) (proj1 (proj2 Hw))). }
    destruct (fetchAsm_inv s1 s1' Hsem (proj1 Hw) (proj2 Hw) Hi) as [Hi' Ev].
    split; [exact Hi' | split; [exact (fetchAsm_hand s1 s1' Hsem Hh) | exists g]].
    destruct (validA s1) eqn:Hv.
    - erewrite effS_true in Hg by exact Hv; erewrite effS_true by exact Ev.
      exact (fetchAsm_pending g s1 s1' s2 Hsem Hv Hi Hg).
    - erewrite effS_false in Hg by exact Hv; erewrite effS_false by exact Ev.
      destruct Hi as [I1 _]; pose proof (I1 Hv) as Ht; unfold tagEcap in Ht; injection Ht as Et Ee.
      exact (ACC fetchAsm_live clintS clint plicS plic initLine fwcs Hdisj g s1 s1' s2 Hsem Ee Hg).
  Qed.

End RedirAsm.
