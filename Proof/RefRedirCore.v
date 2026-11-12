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
From Cheriot.Proof Require Import RefDmImpl RefDmStep RefLsfImpl RefLsfFenceI RefMdStep.
From Cheriot.Proof Require Import RefRevBitRule RefRedirect RefRedirStep.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * dataMem AND mulDiv STAGES UNDER `RefRelR` (item 3.4)
 * ===========================================================================
 * These stages touch neither fetch nor execute's epoch or redirect. Each one's step predicate
 * (`RevRpQ`, `LoadRpQ`, ...) carries over to the applied view (`*_tr`): every component it reads
 * is the same there, and fetch and execute keep their equalities. The stage's `_of` lemma then
 * gives the relation at the applied states. `lift_core` combines this with the stage's old
 * `StepOKR` and `RedirInv` preservation (`InvFrame`). *)

Local Abbreviation TS t := (TreeState ElemState t).

(* dataMem's empty check reads its state as `LoadRq` (tag 0) *)
Lemma dmEmpty_lrq : forall st : type DataMemState, Zmod.eqb st.(Snd) Zmod.zero = true -> dmLoadRq st = true.
Proof. intros [d tg]; cbn [Snd]; intros H; apply Zmod.eqb_eq in H; subst tg; reflexivity. Qed.

Lemma dmCheck_lrq : forall st, dmCheck st = true -> dmLoadRq st = false.
Proof. intros [d tg]; unfold dmCheck, dmLoadRq; cbn; intros H; apply Zmod.eqb_eq in H; subst tg; reflexivity. Qed.

(* a dequeue from a non-empty FIFO leaves it not full *)
Lemma fifo_deq_notFull :
  forall (cap : nat) (k : Kind) (f : TS (ShiftFifo.fifoTree cap k)),
    fifo_wf f -> Zmod.eqb (fifo_size f) Zmod.zero = false ->
    Zmod.eqb (fifo_size (fifoDeqState f)) (Zmod.of_Z _ (Z.of_nat cap)) = false.
Proof.
  intros cap k f Hwf Hemp.
  pose proof (fifo_size_nonzero cap k f Hemp) as H1.
  rewrite fifo_size_eqb_cap, (fifoDeqState_nonempty_eq cap k f Hemp), fifo_size_evalShift, fifo_size_setSize,
    (unsigned_fifoDecSize cap _ H1).
  unfold fifo_wf in Hwf; apply Nat.eqb_neq; lia.
Qed.

Section RedirCore.
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

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis Hmd : Is_true (mulDivStagesDivideXlen mulStages divStages).

  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation SRF :=
    (SpecRuleFrom pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwcs).
  Local Abbreviation STEPOKR :=
    (StepOKR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation STEPOKRR :=
    (StepOKRR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs).
  Local Abbreviation OF :=
    (StepOKR_of pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs).

  Local Abbreviation ACC f := (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA := (ACC iRf).
  Local Abbreviation iFetchA := (ACC iFetch).
  Local Abbreviation iDecodeA := (ACC iDecode).
  Local Abbreviation iExecA := (ACC iExec).
  Local Abbreviation iD2aA := (ACC iD2a).
  Local Abbreviation iExecEpochA := (ACC iExecEpoch).
  Local Abbreviation iFenceIPendingA := (ACC iFenceIPending).
  Local Abbreviation iPccA := (ACC iPcc).
  Local Abbreviation applyPA := (ACC applyP).
  Local Abbreviation effSA := (ACC effS).
  Local Abbreviation validA := (ACC iRedirValid).
  Local Abbreviation InvA := (ACC RedirInv).
  Local Abbreviation HandA := (ACC HandInv).
  Local Abbreviation NPCORE :=
    (Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPMEM :=
    (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  (* --- 1. The Lift --- *)

  Lemma lift_core :
    forall act : Action type ITree (Bit 0),
      (forall g (s1 s1' : IState) s2, SemAction envI act s1 s1' Zmod.zero -> RELG g (effSA s1) s2 -> InvA s1 ->
         InvA s1' /\ validA s1' = validA s1) ->
      (forall g (s1 s1' : IState) s2, SemAction envI act s1 s1' Zmod.zero -> RELG g (effSA s1) s2 -> HandA s1 ->
         HandA s1') ->
      (forall g (s1 s1' : IState) s2, SemAction envI act s1 s1' Zmod.zero -> SRF s2 -> validA s1 = true ->
         RELG g (applyPA s1) s2 -> exists s2' g', SemActions envS specActs s2 s2' /\ RELG g' (applyPA s1') s2') ->
      STEPOKR act -> STEPOKRR act.
  Proof.
    intros act Hinv Hhand Hpend H s1 s1' s2 Hs Hr [Hi [Hh [g Hg]]].
    destruct (Hinv g s1 s1' s2 Hs Hg Hi) as [Hi' Ev].
    pose proof (Hhand g s1 s1' s2 Hs Hg Hh) as Hh'.
    destruct (validA s1) eqn:Hv.
    - erewrite effS_true in Hg by exact Hv.
      destruct (Hpend g s1 s1' s2 Hs Hr Hv Hg) as [s2' [g' [Hss Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact Hi' | split; [exact Hh' | exists g']].
      erewrite effS_true by exact Ev; exact Hg'.
    - erewrite effS_false in Hg by exact Hv.
      destruct (H _ _ _ Hs Hr (ex_intro _ g Hg)) as [s2' [Hss [g' Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact Hi' | split; [exact Hh' | exists g']].
      erewrite effS_false by exact Ev; exact Hg'.
  Qed.

  (* --- 2. RedirInv Frames --- *)

  Definition InvFrame (s1 s1' : IState) : Prop :=
    iFetchA s1' = iFetchA s1 /\ ex_redirect (iExecA s1') = ex_redirect (iExecA s1) /\
    iExecEpochA s1' = iExecEpochA s1 /\ tagEcap (iPccA s1') = tagEcap (iPccA s1) /\ iD2aA s1' = iD2aA s1 /\
    (iFenceIPendingA s1' = true -> iFenceIPendingA s1 = true).

  Lemma inv_frame : forall (s1 s1' : IState), InvA s1 -> InvFrame s1 s1' -> InvA s1' /\ validA s1' = validA s1.
  Proof.
    intros s1 s1' [I1 [I2 I3]] [Efe [Erd [Eep [Etg [Ed2a Efip]]]]].
    assert (Ev : validA s1' = validA s1) by (unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity).
    split; [| exact Ev].
    assert (Ep : ACC iFetchPcc s1' = ACC iFetchPcc s1) by (unfold iFetchPcc; rewrite Efe; reflexivity).
    assert (Ef : ACC iFetchFip s1' = ACC iFetchFip s1) by (unfold iFetchFip; rewrite Efe; reflexivity).
    assert (Er : ACC redirPcc s1' = ACC redirPcc s1) by (unfold redirPcc, iRedirect; rewrite Erd; reflexivity).
    assert (Eib : ACC iInstBuf s1' = ACC iInstBuf s1) by (unfold iInstBuf; rewrite Efe; reflexivity).
    assert (Efb : ACC iFetchBuf s1' = ACC iFetchBuf s1) by (unfold iFetchBuf; rewrite Efe; reflexivity).
    unfold RedirInv; rewrite Ev, Ep, Ef, Er, Etg, Eep, Ed2a, Eib, Efb.
    split; [exact I1 | split; [intros hv hf; exact (I2 hv (Efip hf)) | exact I3]].
  Qed.

  Lemma invFrame_refl : forall s, InvFrame s s.
  Proof. intros s; repeat split; intros h; exact h. Qed.

  Lemma invFrame_eq :
    forall (s1 s1' : IState),
      iFetchA s1' = iFetchA s1 -> iExecA s1' = iExecA s1 -> iPccA s1' = iPccA s1 -> iDecodeA s1' = iDecodeA s1 ->
      InvFrame s1 s1'.
  Proof.
    intros s1 s1' Efe Eex Epcc Ede.
    split; [exact Efe |]; split; [rewrite Eex; reflexivity |]; split; [unfold iExecEpoch; rewrite Eex; reflexivity |].
    split; [rewrite Epcc; reflexivity |]; split; [unfold iD2a; rewrite Ede; reflexivity |].
    unfold iFenceIPending; rewrite Eex; intros h; exact h.
  Qed.

  Lemma pcc_rf : forall (s1 s1' : IState), iRfA s1' = iRfA s1 -> iPccA s1' = iPccA s1.
  Proof. intros s1 s1' E; unfold iPcc; rewrite E; reflexivity. Qed.

  Lemma pcc_gpr : forall (s1 s1' : IState) d v, iRfA s1' = writeGprVal pcAddrInit d v (iRfA s1) -> iPccA s1' = iPccA s1.
  Proof. intros s1 s1' d v E; unfold iPcc; rewrite E; apply readPcc_writeGprVal. Qed.

  Lemma dmFrame_frame : forall s1 s1', ACC DmFrame s1 s1' -> InvFrame s1 s1'.
  Proof. intros s1 s1' [Erf _ _ _ Efe Ede Eex _ _]; exact (invFrame_eq s1 s1' Efe Eex (pcc_rf _ _ Erf) Ede). Qed.

  Lemma dws_frame : forall s1 s1' d v, ACC DmWbStep s1 s1' d v -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' d v [Erf _ _ _ _ _ _ Efe Ede Eex _ _ _]; exact (invFrame_eq s1 s1' Efe Eex (pcc_gpr _ _ _ _ Erf) Ede).
  Qed.

  Lemma dwk_frame : forall s1 s1' d v, ACC DmWbKStep s1 s1' d v -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' d v [Erf _ _ Efe Ede Eex _ _ _]; exact (invFrame_eq s1 s1' Efe Eex (pcc_gpr _ _ _ _ Erf) Ede).
  Qed.

  Lemma lsfFrame_frame : forall s1 s1', ACC LsfFrame s1 s1' -> iExecA s1' = iExecA s1 -> InvFrame s1 s1'.
  Proof. intros s1 s1' [Erf _ Efe Ede _ _] Eex; exact (invFrame_eq s1 s1' Efe Eex (pcc_rf _ _ Erf) Ede). Qed.

  Lemma fia_frame : forall s1 s1', ACC FenceIAcc s1 s1' -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' [[Erf _ Efe Ede _ _] _ _ _ Efip Eep Erd _ _ _].
    split; [exact Efe |]; split; [exact Erd |]; split; [exact Eep |].
    split; [rewrite (pcc_rf _ _ Erf); reflexivity |]; split; [unfold iD2a; rewrite Ede; reflexivity |].
    intros C; rewrite Efip in C; discriminate C.
  Qed.

  (* --- 3. The Applied View --- *)

  Lemma app_fetch :
    forall (s1 s1' : IState), iFetchA s1' = iFetchA s1 -> ex_redirect (iExecA s1') = ex_redirect (iExecA s1) ->
      iFetchA (applyPA s1') = iFetchA (applyPA s1).
  Proof. intros s1 s1' Efe Erd; rewrite !applyP_fetch, Efe; unfold redirTarget, redirPcc, iRedirect; rewrite Erd; reflexivity. Qed.

  Lemma app_exec : forall (s1 s1' : IState), iExecA s1' = iExecA s1 -> iExecA (applyPA s1') = iExecA (applyPA s1).
  Proof. intros s1 s1' Eex; rewrite !applyP_exec; unfold iExecEpoch; rewrite Eex; reflexivity. Qed.

  Lemma dmFrame_tr : forall s1 s1', ACC DmFrame s1 s1' -> ACC DmFrame (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [Erf Ewb Ereg Erp Efe Ede Eex Emd Edmf].
    constructor; [exact Erf | exact Ewb | exact Ereg | exact Erp | exact (app_fetch _ _ Efe (f_equal ex_redirect Eex)) |
                  exact Ede | exact (app_exec _ _ Eex) | exact Emd | exact Edmf].
  Qed.

  Lemma dws_tr : forall s1 s1' d v, ACC DmWbStep s1 s1' d v -> ACC DmWbStep (applyPA s1) (applyPA s1') d v.
  Proof.
    intros s1 s1' d v [E1 E2 E3 E4 E5 E6 E7 Efe E9 Eex E11 E12 E13].
    constructor; [exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 |
                  exact (app_fetch _ _ Efe (f_equal ex_redirect Eex)) | exact E9 | exact (app_exec _ _ Eex) |
                  exact E11 | exact E12 | exact E13].
  Qed.

  Lemma dwk_tr : forall s1 s1' d v, ACC DmWbKStep s1 s1' d v -> ACC DmWbKStep (applyPA s1) (applyPA s1') d v.
  Proof.
    intros s1 s1' d v [E1 E2 E3 Efe E5 Eex E7 E8 E9].
    constructor; [exact E1 | exact E2 | exact E3 | exact (app_fetch _ _ Efe (f_equal ex_redirect Eex)) | exact E5 |
                  exact (app_exec _ _ Eex) | exact E7 | exact E8 | exact E9].
  Qed.

  Lemma lsfFrame_tr :
    forall s1 s1', ACC LsfFrame s1 s1' -> ex_redirect (iExecA s1') = ex_redirect (iExecA s1) ->
      ACC LsfFrame (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [E1 E2 Efe E4 E5 E6] Erd.
    constructor; [exact E1 | exact E2 | exact (app_fetch _ _ Efe Erd) | exact E4 | exact E5 | exact E6].
  Qed.

  Lemma storeAcc_tr : forall s1 s1' q, ACC StoreAcc s1 s1' q -> ACC StoreAcc (applyPA s1) (applyPA s1') q.
  Proof.
    intros s1 s1' q [Hfr Eex E3 E4 E5 E6 E7 E8 E9 E10 E11].
    constructor; [exact (lsfFrame_tr _ _ Hfr (f_equal ex_redirect Eex)) | exact (app_exec _ _ Eex) |
                  exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | exact E8 | exact E9 | exact E10 | exact E11].
  Qed.

  Lemma loadAcc_tr : forall s1 s1' q, ACC LoadAcc s1 s1' q -> ACC LoadAcc (applyPA s1) (applyPA s1') q.
  Proof.
    intros s1 s1' q [Hfr Eex E3 E4 E5 E6 E7 E8 E9 E10 E11 E12].
    constructor; [exact (lsfFrame_tr _ _ Hfr (f_equal ex_redirect Eex)) | exact (app_exec _ _ Eex) |
                  exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | exact E8 | exact E9 | exact E10 | exact E11 |
                  exact E12].
  Qed.

  Lemma plainAcc_tr : forall s1 s1', ACC PlainAcc s1 s1' -> ACC PlainAcc (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [Hfr Eex E3 E4].
    constructor; [exact (lsfFrame_tr _ _ Hfr (f_equal ex_redirect Eex)) | exact (app_exec _ _ Eex) | exact E3 | exact E4].
  Qed.

  Lemma fia_tr : forall s1 s1', ACC FenceIAcc s1 s1' -> ACC FenceIAcc (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [Hfr E2 E3 E4 Efip Eep Erd Ecp Efs Eho].
    constructor; [exact (lsfFrame_tr _ _ Hfr Erd) | exact E2 | exact E3 | exact E4 | exact Efip | | exact Erd
                  | rewrite !applyP_exec; exact Ecp | rewrite !applyP_exec; exact Efs | rewrite !applyP_exec; exact Eho].
    rewrite !applyP_epoch, Eep; reflexivity.
  Qed.

  (* --- 4. The Step Predicates --- *)

  Lemma revRpQ_tr : forall s1 s1', ACC RevRpQ s1 s1' -> ACC RevRpQ (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [E | [A [B [C D]]]]; [left; rewrite E; reflexivity |].
    right; exact (conj A (conj B (conj C (dws_tr _ _ _ _ D)))).
  Qed.

  Lemma revRpQ_frame : forall s1 s1', ACC RevRpQ s1 s1' -> InvFrame s1 s1'.
  Proof. intros s1 s1' [-> | [_ [_ [_ D]]]]; [exact (invFrame_refl _) | exact (dws_frame _ _ _ _ D)]. Qed.

  Lemma loadRpQ_tr : forall s1 s1', ACC LoadRpQ s1 s1' -> ACC LoadRpQ (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [E | [A [B [C [[T [Hf K]] | [T K]]]]]]; [left; rewrite E; reflexivity | |].
    - right; exact (conj A (conj B (conj C (or_introl (conj T (conj (dmFrame_tr _ _ Hf) K)))))).
    - right; refine (conj A (conj B (conj C (or_intror (conj T _))))).
      cbv zeta in K |- *; exact (dws_tr _ _ _ _ K).
  Qed.

  Lemma loadRpQ_frame : forall s1 s1', ACC LoadRpQ s1 s1' -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' [-> | [_ [_ [_ [[_ [Hf _]] | [_ K]]]]]];
      [exact (invFrame_refl _) | exact (dmFrame_frame _ _ Hf) | cbv zeta in K; exact (dws_frame _ _ _ _ K)].
  Qed.

  Lemma checkRevQ_tr : forall s1 s1', ACC CheckRevQ s1 s1' -> ACC CheckRevQ (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [E | [A [[N [I [P [Hf R]]]] | [[N [Hf R]] | [N W]]]]]; [left; rewrite E; reflexivity | | |].
    - right; exact (conj A (or_introl (conj N (conj I (conj P (conj (dmFrame_tr _ _ Hf) R)))))).
    - right; exact (conj A (or_intror (or_introl (conj N (conj (dmFrame_tr _ _ Hf) R))))).
    - right; exact (conj A (or_intror (or_intror (conj N (dwk_tr _ _ _ _ W))))).
  Qed.

  Lemma checkRevQ_frame : forall s1 s1', ACC CheckRevQ s1 s1' -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' [-> | [_ [[_ [_ [_ [Hf _]]]] | [[_ [Hf _]] | [_ W]]]]];
      [exact (invFrame_refl _) | exact (dmFrame_frame _ _ Hf) | exact (dmFrame_frame _ _ Hf) | exact (dwk_frame _ _ _ _ W)].
  Qed.

  Lemma issueQ_tr : forall s1 s1', ACC IssueQ s1 s1' -> ACC IssueQ (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [E | [A [B [C [Hf R]]]]]; [left; rewrite E; reflexivity |].
    right; exact (conj A (conj B (conj C (conj (dmFrame_tr _ _ Hf) R)))).
  Qed.

  Lemma issueQ_frame : forall s1 s1', ACC IssueQ s1 s1' -> InvFrame s1 s1'.
  Proof. intros s1 s1' [-> | [_ [_ [_ [Hf _]]]]]; [exact (invFrame_refl _) | exact (dmFrame_frame _ _ Hf)]. Qed.

  Lemma lsfQ_tr : forall s1 s1', ACC LsfQ s1 s1' -> ACC LsfQ (applyPA s1) (applyPA s1').
  Proof.
    intros s1 s1' [E | [q [rest [Eb [Hl Hc]]]]]; [left; rewrite E; reflexivity |].
    right; exists q, rest; split; [exact Eb | split; [exact Hl |]].
    destruct Hc as [[A [B H]] | [[A [B H]] | [[A [B H]] | [A [B H]]]]].
    - left; exact (conj A (conj B (storeAcc_tr _ _ _ H))).
    - right; left; exact (conj A (conj B (loadAcc_tr _ _ _ H))).
    - right; right; left; exact (conj A (conj B (plainAcc_tr _ _ H))).
    - right; right; right; exact (conj A (conj B (fia_tr _ _ H))).
  Qed.

  Lemma lsfQ_frame : forall s1 s1', ACC LsfQ s1 s1' -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' [-> | [q [rest [_ [_ Hc]]]]]; [exact (invFrame_refl _) |].
    destruct Hc as [[_ [_ H]] | [[_ [_ H]] | [[_ [_ H]] | [_ [_ H]]]]].
    - exact (lsfFrame_frame _ _ (sa_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) (sa_exec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)).
    - exact (lsfFrame_frame _ _ (la_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) (la_exec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)).
    - exact (lsfFrame_frame _ _ (pa_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) (pa_exec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)).
    - exact (fia_frame _ _ H).
  Qed.

  Lemma mdQ_frame : forall s1 s1', ACC MdQ s1 s1' -> InvFrame s1 s1'.
  Proof.
    intros s1 s1' [[smd [-> _]] | [smd [l1 [l2 [d [v [-> _]]]]]]].
    - exact (invFrame_refl s1).
    - refine (invFrame_eq s1 (ACC mdWbSet s1 smd d v) eq_refl eq_refl _ eq_refl).
      exact (pcc_gpr s1 (ACC mdWbSet s1 smd d v) d v eq_refl).
  Qed.

  (* --- 4b. The Hand-off Invariant --- *)

  (* What a dataMem / mulDiv step keeps of what the hand-off stands for *)
  Definition HandFrame (s1 s1' : IState) : Prop :=
    ex_canProceed (iExecA s1') = ex_canProceed (iExecA s1) /\ ex_firstSlot (iExecA s1') = ex_firstSlot (iExecA s1) /\
    ex_handoff (iExecA s1') = ex_handoff (iExecA s1) /\ iDecodeA s1' = iDecodeA s1 /\ iPccA s1' = iPccA s1 /\
    ex_redirect (iExecA s1') = ex_redirect (iExecA s1) /\
    (ACC hdDmFull s1' = true -> ACC hdDmFull s1 = true).

  (* No change, or dataMem was busy (so the empty and core-write checks of the hand-off are void) *)
  Definition HandStep (s1 s1' : IState) : Prop :=
    s1' = s1 \/ (ACC hdDmEmpty s1 = false /\ HandFrame s1 s1').

  Lemma hand_dm : forall s1 s1', HandStep s1 s1' -> HandA s1 -> HandA s1'.
  Proof.
    intros s1 s1' [-> | [He [E1 [E2 [E3 [E4 [E5 [E6 E7]]]]]]]] H; [exact H |].
    revert H; apply (ACC HandInv_frame);
      [exact E1 | exact E2 | exact E3 | intros _; unfold hdHead; rewrite E4; reflexivity | exact E5
      | unfold iRedirValid, ex_redirValid; rewrite E6; intros h; exact h | exact E7].
  Qed.

  Lemma hdDmFull_eq :
    forall s, ACC hdDmFull s = Zmod.eqb (fifo_size (dataMem_fifo dataMemCapacity (ACC iDm s)))
                                        (Zmod.of_Z _ (Z.of_nat dataMemCapacity)).
  Proof. reflexivity. Qed.

  Lemma hdDmEmpty_false : forall s, dmLoadRq (ACC iDmSt s) = false -> ACC hdDmEmpty s = false.
  Proof.
    intros s H; destruct (ACC hdDmEmpty s) eqn:E; [| reflexivity].
    unfold hdDmEmpty in E; apply andb_prop in E as [_ E].
    pose proof (dmEmpty_lrq _ E) as E'; change (dmLoadRq (ACC iDmSt s) = true) in E'.
    rewrite E' in H; discriminate H.
  Qed.

  Lemma hdDmEmpty_buf :
    forall s q rest, fifo_wf (dataMem_fifo dataMemCapacity (ACC iDm s)) ->
      ACC iDmBuf s = q :: rest -> ACC hdDmEmpty s = false.
  Proof.
    intros s q rest Hw Eb; unfold hdDmEmpty; unfold iDmBuf in Eb.
    change (dm_inputFifo dataMemCapacity (ACC iDm s)) with (dataMem_fifo dataMemCapacity (ACC iDm s)).
    rewrite (fifo_size_eqb_zero _ _ _ Hw), Eb; reflexivity.
  Qed.

  Lemma handFrame_of :
    forall s1 s1', iExecA s1' = iExecA s1 -> iDecodeA s1' = iDecodeA s1 -> iPccA s1' = iPccA s1 ->
      dataMem_fifo dataMemCapacity (ACC iDm s1') = dataMem_fifo dataMemCapacity (ACC iDm s1) -> HandFrame s1 s1'.
  Proof.
    intros s1 s1' Eex Ede Ep Ef; unfold HandFrame; rewrite Eex.
    split; [reflexivity |]; split; [reflexivity |]; split; [reflexivity |].
    split; [exact Ede |]; split; [exact Ep |]; split; [reflexivity |].
    rewrite !hdDmFull_eq, Ef; intros h; exact h.
  Qed.

  Lemma dmFrame_hand : forall s1 s1', ACC DmFrame s1 s1' -> HandFrame s1 s1'.
  Proof. intros s1 s1' [Erf _ _ _ _ Ede Eex _ Edmf]; exact (handFrame_of s1 s1' Eex Ede (pcc_rf _ _ Erf) Edmf). Qed.

  Lemma dws_hand : forall s1 s1' d v, ACC DmWbStep s1 s1' d v -> HandFrame s1 s1'.
  Proof.
    intros s1 s1' d v [Erf _ _ _ _ _ _ _ Ede Eex _ Edmf _]; exact (handFrame_of s1 s1' Eex Ede (pcc_gpr _ _ _ _ Erf) Edmf).
  Qed.

  Lemma dwk_hand : forall s1 s1' d v, ACC DmWbKStep s1 s1' d v -> HandFrame s1 s1'.
  Proof.
    intros s1 s1' d v [Erf _ _ _ Ede Eex _ Edmf _]; exact (handFrame_of s1 s1' Eex Ede (pcc_gpr _ _ _ _ Erf) Edmf).
  Qed.

  Lemma revRpQ_hand : forall s1 s1', ACC RevRpQ s1 s1' -> HandStep s1 s1'.
  Proof.
    intros s1 s1' [-> | [Hrv [_ [_ D]]]]; [left; reflexivity |].
    right; split; [apply hdDmEmpty_false; exact (proj1 (dmRevRp_excl3 _ Hrv)) | exact (dws_hand _ _ _ _ D)].
  Qed.

  Lemma loadRpQ_hand : forall s1 s1', ACC LoadRpQ s1 s1' -> HandStep s1 s1'.
  Proof.
    intros s1 s1' [-> | [Hlp [_ [_ [[_ [Hf _]] | [_ K]]]]]]; [left; reflexivity | |];
      (right; split; [apply hdDmEmpty_false; exact (proj1 (dmLoadRp_excl3 _ Hlp)) |]).
    - exact (dmFrame_hand _ _ Hf).
    - cbv zeta in K; exact (dws_hand _ _ _ _ K).
  Qed.

  Lemma checkRevQ_hand : forall s1 s1', ACC CheckRevQ s1 s1' -> HandStep s1 s1'.
  Proof.
    intros s1 s1' [-> | [Hck [[_ [_ [_ [Hf _]]]] | [[_ [Hf _]] | [_ W]]]]]; [left; reflexivity | | |];
      (right; split; [apply hdDmEmpty_false; exact (dmCheck_lrq _ Hck) |]).
    - exact (dmFrame_hand _ _ Hf).
    - exact (dmFrame_hand _ _ Hf).
    - exact (dwk_hand _ _ _ _ W).
  Qed.

  Lemma issueQ_hand : forall s1 s1', ACC IssueQ s1 s1' -> HandStep s1 s1'.
  Proof.
    intros s1 s1' [-> | [Hrq [_ [_ [Hf _]]]]]; [left; reflexivity |].
    right; split; [apply hdDmEmpty_false; exact (proj1 (dmRevRq_excl3 _ Hrq)) | exact (dmFrame_hand _ _ Hf)].
  Qed.

  Lemma lsf_handStep :
    forall s1 s1' q rest,
      fifo_wf (dataMem_fifo dataMemCapacity (ACC iDm s1)) ->
      ACC iDmBuf s1 = q :: rest -> ACC LsfFrame s1 s1' ->
      ex_canProceed (iExecA s1') = ex_canProceed (iExecA s1) -> ex_firstSlot (iExecA s1') = ex_firstSlot (iExecA s1) ->
      ex_handoff (iExecA s1') = ex_handoff (iExecA s1) -> ex_redirect (iExecA s1') = ex_redirect (iExecA s1) ->
      HandStep s1 s1'.
  Proof.
    intros s1 s1' q rest Hw Eb [Erf _ _ Ede _ Edmf] Ecp Efs Eho Erd.
    right; split; [exact (hdDmEmpty_buf s1 q rest Hw Eb) |].
    split; [exact Ecp |]; split; [exact Efs |]; split; [exact Eho |]; split; [exact Ede |].
    split; [exact (pcc_rf _ _ Erf) |]; split; [exact Erd |].
    assert (Hne : Zmod.eqb (fifo_size (dataMem_fifo dataMemCapacity (ACC iDm s1))) Zmod.zero = false)
      by (unfold iDmBuf in Eb; rewrite (fifo_size_eqb_zero _ _ _ Hw), Eb; reflexivity).
    intros C; rewrite hdDmFull_eq, Edmf, (fifo_deq_notFull _ _ _ Hw Hne) in C; discriminate C.
  Qed.

  Lemma lsfQ_hand :
    forall s1 s1', fifo_wf (dataMem_fifo dataMemCapacity (ACC iDm s1)) ->
      ACC LsfQ s1 s1' -> HandStep s1 s1'.
  Proof.
    intros s1 s1' Hw [-> | [q [rest [Eb [_ Hc]]]]]; [left; reflexivity |].
    destruct Hc as [[_ [_ [Hfr Eex _ _ _ _ _ _ _ _ _]]] | [[_ [_ [Hfr Eex _ _ _ _ _ _ _ _ _ _]]]
                   | [[_ [_ [Hfr Eex _ _]]] | [_ [_ [Hfr _ _ _ _ _ Erd Ecp Efs Eho]]]]]].
    1-3: apply (lsf_handStep s1 s1' q rest Hw Eb Hfr); rewrite Eex; reflexivity.
    exact (lsf_handStep s1 s1' q rest Hw Eb Hfr Ecp Efs Eho Erd).
  Qed.

  Lemma mdQ_hand : forall s1 s1', ACC MdQ s1 s1' -> HandA s1 -> HandA s1'.
  Proof.
    intros s1 s1' [[smd [-> _]] | [smd [l1 [l2 [d [v [-> _]]]]]]]; apply (ACC HandInv_frame);
      first [reflexivity | intros _; reflexivity | exact (pcc_gpr s1 (ACC mdWbSet s1 smd d v) d v eq_refl)
            | intros h; exact h].
  Qed.

  (* --- 5. The Stages --- *)

  Local Abbreviation REVRP :=
    (@revRpAndWriteBackStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation LOADRPS :=
    (@loadRpAndWritebackStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation CHECKS :=
    (@checkRevocationStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation ISSUES :=
    (@issueRevRqStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation LSF :=
    (@loadRqOrStoreOrFenceStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).
  Local Abbreviation MDACTS :=
    (@mulDivStageActions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).

  Theorem stepOK_revRp : STEPOKRR REVRP.
  Proof.
    apply lift_core.
    - intros g s1 s1' s2 Hs _ Hi.
      exact (inv_frame s1 s1' Hi (revRpQ_frame _ _ (ACC revRpStage_char _ s1 s1' _ Hs))).
    - intros g s1 s1' s2 Hs _ Hh.
      exact (hand_dm s1 s1' (revRpQ_hand _ _ (ACC revRpStage_char _ s1 s1' _ Hs)) Hh).
    - intros g s1 s1' s2 Hs _ _ Hg.
      destruct (ACC revRp_of clintS clint plicS plic initLine fwcs g _ _ s2
                  (revRpQ_tr _ _ (ACC revRpStage_char _ s1 s1' _ Hs)) Hg) as [g' Hg'].
      exists s2, g'; split; [apply NilAction; reflexivity | exact Hg'].
    - exact (OF _ (ACC stepOK_revRpAndWriteBackStage clintS clint plicS plic initLine fwcs)).
  Qed.

  Theorem stepOK_loadRp : STEPOKRR LOADRPS.
  Proof.
    apply lift_core.
    - intros g s1 s1' s2 Hs _ Hi.
      unfold loadRpAndWritebackStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      exact (inv_frame s1 _ Hi (loadRpQ_frame _ _ (ACC loadRpWb_char _ s1 c' _ Hc))).
    - intros g s1 s1' s2 Hs _ Hh.
      unfold loadRpAndWritebackStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      exact (hand_dm s1 _ (loadRpQ_hand _ _ (ACC loadRpWb_char _ s1 c' _ Hc)) Hh).
    - intros g s1 s1' s2 Hs _ _ Hg.
      unfold loadRpAndWritebackStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      destruct (ACC loadRp_of clintS clint plicS plic initLine fwcs g _ _ s2
                  (loadRpQ_tr _ _ (ACC loadRpWb_char _ s1 c' _ Hc)) Hg) as [g' Hg'].
      exists s2, g'; split; [apply NilAction; reflexivity | exact Hg'].
    - exact (OF _ (ACC stepOK_loadRpAndWritebackStage clintS clint plicS plic initLine fwcs)).
  Qed.

  Theorem stepOK_checkRev : STEPOKRR CHECKS.
  Proof.
    apply lift_core.
    - intros g s1 s1' s2 Hs _ Hi.
      unfold checkRevocationStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      exact (inv_frame s1 _ Hi (checkRevQ_frame _ _ (ACC checkRev_char _ s1 c' _ Hc))).
    - intros g s1 s1' s2 Hs _ Hh.
      unfold checkRevocationStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      exact (hand_dm s1 _ (checkRevQ_hand _ _ (ACC checkRev_char _ s1 c' _ Hc)) Hh).
    - intros g s1 s1' s2 Hs _ _ Hg.
      unfold checkRevocationStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      destruct (ACC checkRev_of clintS clint plicS plic initLine fwcs g _ _ s2
                  (checkRevQ_tr _ _ (ACC checkRev_char _ s1 c' _ Hc)) Hg) as [g' Hg'].
      exists s2, g'; split; [apply NilAction; reflexivity | exact Hg'].
    - exact (OF _ (ACC stepOK_checkRevocationStage clintS clint plicS plic initLine fwcs)).
  Qed.

  Theorem stepOK_issue : STEPOKRR ISSUES.
  Proof.
    apply lift_core.
    - intros g s1 s1' s2 Hs _ Hi.
      unfold issueRevRqStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      exact (inv_frame s1 _ Hi (issueQ_frame _ _ (ACC issueRevRq_char _ s1 c' _ Hc))).
    - intros g s1 s1' s2 Hs _ Hh.
      unfold issueRevRqStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      exact (hand_dm s1 _ (issueQ_hand _ _ (ACC issueRevRq_char _ s1 c' _ Hc)) Hh).
    - intros g s1 s1' s2 Hs _ _ Hg.
      unfold issueRevRqStage in Hs; apply SemAction_liftAction_iff in Hs as [c' [Hc ->]].
      destruct (ACC issue_of clintS clint plicS plic initLine fwcs g _ _ s2
                  (issueQ_tr _ _ (ACC issueRevRq_char _ s1 c' _ Hc)) Hg) as [g' Hg'].
      exists s2, g'; split; [apply NilAction; reflexivity | exact Hg'].
    - exact (OF _ (ACC stepOK_issueRevRqStage clintS clint plicS plic initLine fwcs)).
  Qed.

  Theorem stepOK_lsf : STEPOKRR LSF.
  Proof.
    apply lift_core.
    - intros g s1 s1' s2 Hs Hg Hi.
      pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [Hwd _]]]] _].
      rewrite effS_dm in Hwd.
      exact (inv_frame s1 s1' Hi (lsfQ_frame _ _ (ACC lsf_char _ s1 s1' _ Hwd Hs))).
    - intros g s1 s1' s2 Hs Hg Hh.
      pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [Hwd _]]]] _].
      rewrite effS_dm in Hwd.
      exact (hand_dm s1 s1' (lsfQ_hand _ _ Hwd (ACC lsf_char _ s1 s1' _ Hwd Hs)) Hh).
    - intros g s1 s1' s2 Hs _ _ Hg.
      pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [Hwd _]]]] _].
      destruct (ACC lsf_of clintS clint plicS plic initLine fwcs Hdisj g _ _ s2
                  (lsfQ_tr _ _ (ACC lsf_char _ s1 s1' _ Hwd Hs)) Hg) as [s2' [Hss [g' Hg']]].
      exists s2', g'; split; [exact Hss | exact Hg'].
    - exact (OF _ (ACC stepOK_loadRqOrStoreOrFenceStage clintS clint plicS plic initLine fwcs Hdisj)).
  Qed.

  Theorem stepOK_md : forall a, In a MDACTS -> STEPOKRR a.
  Proof.
    intros a Hin; apply lift_core.
    - intros g s1 s1' s2 Hs Hg Hi.
      pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [_ [Hwf _]]]]] _].
      rewrite effS_md in Hwf.
      exact (inv_frame s1 s1' Hi (mdQ_frame _ _ (ACC md_char Hmd a Hin _ s1 s1' Hs Hwf))).
    - intros g s1 s1' s2 Hs Hg Hh.
      pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [_ [Hwf _]]]]] _].
      rewrite effS_md in Hwf.
      exact (mdQ_hand _ _ (ACC md_char Hmd a Hin _ s1 s1' Hs Hwf) Hh).
    - intros g s1 s1' s2 Hs _ _ Hg.
      pose proof Hg as [_ _ _ _ _ _ _ _ _ _ _ [_ [_ [_ [_ [Hwf _]]]]] _].
      exists s2, g; split; [apply NilAction; reflexivity |].
      destruct (ACC md_char Hmd a Hin _ s1 s1' Hs Hwf)
        as [[smd [-> [Hwf' Hex]]] | [smd [l1 [l2 [d [v [-> [Hwf' [E1 E2]]]]]]]]].
      + exact (ACC RefRelG_mdFrame clintS clint plicS plic initLine fwcs g (applyPA s1) s2 smd Hg Hwf' Hex).
      + exact (ACC RefRelG_mdWb clintS clint plicS plic initLine fwcs g (applyPA s1) s2 smd l1 l2 d v Hg Hwf' E1 E2).
    - exact (OF _ (ACC stepOK_mulDivStageActions clintS clint plicS plic initLine fwcs Hmd a Hin)).
  Qed.

  (* --- 6. Rule Lists on the Memory Subtree --- *)

  Lemma lift_np_mem_map :
    forall (L : list (Action type (getNode NPMEM) (Bit 0))) act,
      In act (map (fun a => liftAction NPMEM a) L) -> STEPOKR act -> STEPOKRR act.
  Proof.
    intros L act Hin H; apply in_map_iff in Hin as [a [<- _]].
    exact (ACC lift_np_mem clintS clint plicS plic initLine fwcs a H).
  Qed.

End RedirCore.
