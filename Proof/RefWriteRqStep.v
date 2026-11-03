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
From Cheriot Require Import SpecDefines SpecDevice SpecFetchDeferred Spec Clint Plic Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefSpecRead RefSpecFetch RefRevTable RefReplay ImplSpec RefMemStep RefReadRp.
From Cheriot.Proof Require Import RefReadRpPorts RefRevoker RefRevokerStep RefExecAppend RefLoadCommit RefLoadCommitStep.
From Cheriot.Proof Require Import RefRevBitRule RefWriteRqPorts RefStoreCommit RefSnoopMiss RefStoreCommitStep.
From Cheriot.Proof Require Import RefRouteAt RefRqStepChar RefRqStage RefDevSim RefDevWrite RefDevCommit.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the write step of the memory `state` register (`writeRqStep`): an ExternalMem
 * line is staged in its region's `portRq` (the spec stutters); a CustomMem line is written to the
 * device and an unmapped line is dropped, both at once (the spec commits the store line). *)

Lemma msWriteRq_excl :
  forall st, msWriteRq st = true ->
    msIdle st = false /\ msReadRq st = false /\ msReadRqSent st = false /\ msReadRpReady st = false.
Proof.
  intros [d tg]; unfold msIdle, msReadRq, msReadRqSent, msReadRpReady, msWriteRq; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Section WriteRqStep.
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

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HrevTab : Is_true (revTableInExternalMem config specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation NPMI := (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPMS := (Spec.np_mem pcAddrInit specRegions).
  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA := (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA := (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL := (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               clintS clint plicS plic initLine fwcs).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation ACC := (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation REVK := (RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation RACC := (RevAccRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation PWS := (PortsWriteStaged pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* --- 1. Which Accesses the Step Can Serve --- *)

  (* With a write pending in `state` and no staged write, the access is a store's or the revoker's
   * write, not yet handed to a region *)
  Lemma AccessRel_writeRq :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 -> msWriteRq (iMemStA s1) = true -> noPortWriteB implRegions (iRegionsA s1) = true ->
      (exists addr size pkt b, g_acc pcAddrInit g = AccStore addr size pkt (WrPend b)) \/
      (exists addr pkt, g_acc pcAddrInit g = AccRevWrite addr pkt (WrPend false)).
  Proof.
    intros g s1 s2 Ha Hw Hnp.
    destruct (msWriteRq_excl _ Hw) as [X1 [X2 [X3 X4]]].
    assert (HWS : forall L w, lineKind implRegions L = Some true -> PWS L w s1 -> False).
    { intros L w Hk Hp.
      assert (Hall : AllPorts (fun r y => isRegionAddrB r L = true -> extPortRq r y = someWrite w) implRegions (iRegionsA s1)).
      { revert Hp; unfold PortsWriteStaged; apply AllPorts_impl; intros r y [_ Hp0] Hm; rewrite Hm in Hp0; exact Hp0. }
      rewrite (noPortWriteB_false L w implRegions _ Hk Hall) in Hnp; discriminate Hnp. }
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [b|b] | ld pkt0 [b|b|b|b rp|res]
                                     | rc [b|b|b|b rp|res] | [b|b|b|b rp|res]
                                     | [b|b|b|b rp|res] | addr pkt [b|b]];
      unfold WrStageRel, RdStageRel, rdSecond, wrSecond in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try congruence.
    all: try match goal with H : ?b = false |- _ => is_var b; subst b end.
    all: try (left; eexists _, _, _, _; reflexivity).
    all: try (right; eexists _, _; reflexivity).
    all: exfalso; eapply HWS; eassumption.
  Qed.

  (* --- 2. An ExternalMem Line: the Request Is Staged --- *)

  Local Abbreviation iRevArchA := (iRevArch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Lemma iRev_stage :
    forall (s1 s1' : IState) m' L v,
      s1' = writeSubTreeState NPMI s1 m' -> StageAtL L v implRegions (iRegionsA s1) m'.(Fst) -> iRevA s1' = iRevA s1.
  Proof.
    intros s1 s1' m' L v E1 Hst.
    unfold iRev, implRevState; rewrite E1.
    change (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              (writeSubTreeState NPMI s1 m')) with m'.(Fst).
    rewrite (regionStateAt_stage _ _ _ _ _ _ _ _ Hst) by exact I; reflexivity.
  Qed.

  Lemma MemRelC_stage :
    forall g g' (s1 s1' : IState) (s2 : SState) m' L v,
      s1' = writeSubTreeState NPMI s1 m' -> StageAtL L v implRegions (iRegionsA s1) m'.(Fst) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g -> MEMC g s1 s2 -> MEMC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 m' L v E1 Hst Eo Hm.
    assert (Ei : iRegionsA s1' = m'.(Fst)) by (rewrite E1; reflexivity).
    unfold MemRelC, MemRel, DevInv in *; rewrite Ei, Eo.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_stage _ _ _ _ _ _ _ _ Hst) by exact I.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    eapply MemRelPre_stage; [exact I | exact Hst | exact Hpre].
  Qed.

  (* The relation after a staging step: only the access changes, as the caller shows *)
  Lemma RefRelG_stage :
    forall g g' (s1 s1' : IState) (s2 : SState) m' L v,
      s1' = writeSubTreeState NPMI s1 m' -> StageAtL L v implRegions (iRegionsA s1) m'.(Fst) ->
      g_chain pcAddrInit g' = g_chain pcAddrInit g -> g_rf0 pcAddrInit g' = g_rf0 pcAddrInit g ->
      g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g -> g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g ->
      accTakesHead (g_acc pcAddrInit g') = accTakesHead (g_acc pcAddrInit g) ->
      ACC g' s1' s2 -> RACC g' s1' s2 -> RELG g s1 s2 -> RELG g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 m' L v E1 Hst Ech Erf Ecn Ed2a Eo Eat Ha Hra Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha0 Hc Hd Hfe Hs Hfr Hw Hrk].
    pose proof (iRev_stage s1 s1' m' L v E1 Hst) as HR.
    assert (Ei : iRegionsA s1' = m'.(Fst)) by (rewrite E1; reflexivity).
    apply (RefRelG_rq_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs g g' s1 s1' s2 s2 m' (sMemA s2) E1 eq_refl Ech Erf Ecn Ed2a Eat).
    - intros P HPi; rewrite Ei; exact (AllPorts_stage P (RqInsensitive_setPortRq P HPi) _ _ _ _ _ Hst).
    - intros L0; reflexivity.
    - apply FetchViewExt_refl.
    - exact (MemRelC_stage g g' s1 s1' s2 m' L v E1 Hst Eo Hm).
    - unfold LatchRel in *; rewrite Ech; exact Hl.
    - exact Ha.
    - unfold RevokerRel in *; destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
      rewrite HR; exact (conj K1 (conj K2 (conj K3 (conj K4 Hra)))).
    - exact Hg.
  Qed.

  Local Abbreviation iScanMsbA := (iScanMsb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The access after a store line was staged *)
  Lemma acc_stageStore :
    forall g g' (s1 s1' : IState) (s2 : SState) addr size pkt (b : bool) st',
      g_acc pcAddrInit g = AccStore addr size pkt (WrPend b) ->
      g_acc pcAddrInit g' = AccStore addr size pkt (WrStaged b) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g -> g_chain pcAddrInit g' = g_chain pcAddrInit g ->
      iMemStA s1' = st' ->
      (if andb (negb b) (crossesB addr size) then msWriteRq st' = true /\ msWriteRqV st' = stepOf true addr size pkt
       else msIdle st' = true) ->
      iReadRpA s1' = iReadRpA s1 -> iDmStA s1' = iDmStA s1 -> iRevA s1' = iRevA s1 ->
      lineKind implRegions (lineOf b addr) = Some true ->
      AllPorts (stagedP (lineOf b addr) (someWrite (buildW b addr pkt size))) implRegions (iRegionsA s1') ->
      ACC g s1 s2 -> ACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 addr size pkt b st' Eacc Eacc' Eo Ech Emst Hif Erp Edm HR Hk Hp Ha.
    unfold AccessRel in *; rewrite Eacc in Ha; rewrite Eacc', Eo.
    unfold WrStageRel in *; cbv beta iota zeta in Ha |- *.
    destruct Ha as [[Hrp0 _] [Hdlq [Hrnr [Hoff [Hsnoop Hm]]]]].
    unfold revNotReading, iRevPhase, iScanMsb, iRevSnoopHit, HeadReq in *.
    rewrite Erp, Edm, HR, Ech, Emst.
    refine (conj (conj Hrp0 (conj Hif (conj Hk Hp))) (conj Hdlq (conj Hrnr (conj Hoff (conj Hsnoop _))))).
    destruct b; exact Hm.
  Qed.

  (* The access after the revoker's write was staged *)
  Lemma acc_stageRev :
    forall g g' (s1 s1' : IState) (s2 : SState) addr pkt st',
      g_acc pcAddrInit g = AccRevWrite addr pkt (WrPend false) ->
      g_acc pcAddrInit g' = AccRevWrite addr pkt (WrStaged false) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g ->
      iMemStA s1' = st' ->
      (if andb (negb false) (crossesB addr capSz) then msWriteRq st' = true /\ msWriteRqV st' = stepOf true addr capSz pkt
       else msIdle st' = true) ->
      iReadRpA s1' = iReadRpA s1 -> iDmStA s1' = iDmStA s1 -> iRevA s1' = iRevA s1 ->
      lineKind implRegions (lineOf false addr) = Some true ->
      AllPorts (stagedP (lineOf false addr) (someWrite (buildW false addr pkt capSz))) implRegions (iRegionsA s1') ->
      ACC g s1 s2 -> ACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 addr pkt st' Eacc Eacc' Eo Emst Hif Erp Edm HR Hk Hp Ha.
    unfold AccessRel in *; rewrite Eacc in Ha; rewrite Eacc', Eo.
    unfold WrStageRel in *; cbv beta iota zeta in Ha |- *.
    destruct Ha as [[Hrp0 _] [Hidle [Hdna [Hoff [Hsec _]]]]].
    unfold iRevPhase, dmNotAccessing in *.
    rewrite Erp, Edm, HR, Emst.
    exact (conj (conj Hrp0 (conj Hif (conj Hk Hp))) (conj Hidle (conj Hdna (conj Hoff (conj Hsec eq_refl))))).
  Qed.

  Lemma racc_stageRev :
    forall g g' (s1 s1' : IState) (s2 : SState) addr pkt st st',
      g_acc pcAddrInit g = AccRevWrite addr pkt st -> g_acc pcAddrInit g' = AccRevWrite addr pkt st' ->
      iRevA s1' = iRevA s1 -> RACC g s1 s2 -> RACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 addr pkt st st' Eacc Eacc' HR H.
    unfold RevAccRel in *; rewrite Eacc in H; rewrite Eacc'.
    unfold RevWriteOK, iRevArch in *; rewrite HR; exact H.
  Qed.

  Lemma stepOf_inj :
    forall b addr size pkt b' addr' size' pkt',
      stepOf b addr size pkt = stepOf b' addr' size' pkt' -> b = b' /\ addr = addr' /\ size = size' /\ pkt = pkt'.
  Proof. intros b addr size pkt b' addr' size' pkt' E; unfold stepOf in E; injection E as -> -> -> ->; repeat split. Qed.

  Local Abbreviation revS := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revS plicS type).
  Local Abbreviation RULE := (RevBitRuleStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).

  (* --- 3. A CustomMem or Unmapped Line: the Store Line Commits --- *)

  Local Abbreviation iRevPhaseA := (iRevPhase pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevScanCapA := (iRevScanCap pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevScanBaseA := (iRevScanBase pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevSnoopHitA := (iRevSnoopHit pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iScanAddrA := (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RNR := (revNotReading pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA := (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation CNWB := (CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation DMQ := (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RELNE := (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).
  Local Abbreviation sClintA := (sClint pcAddrInit pre post revBase revPfB revPfA clintS).
  Local Abbreviation sPlicA := (sPlic pcAddrInit pre post revBase revPfB revPfA plicS).

  (* What a device write keeps of the impl revoker: the impl-only registers and the registers
   * software cannot write *)
  Definition RevKept (s1 s1' : IState) : Prop :=
    revExtraOf (iRevA s1') = revExtraOf (iRevA s1) /\ revKeyOf (iRevA s1') = revKeyOf (iRevA s1).

  Lemma RevKept_obs :
    forall (s1 s1' : IState), RevKept s1 s1' ->
      iRevPhaseA s1' = iRevPhaseA s1 /\ iRevScanCapA s1' = iRevScanCapA s1 /\ iRevScanBaseA s1' = iRevScanBaseA s1 /\
      iRevSnoopHitA s1' = iRevSnoopHitA s1 /\ iScanMsbA s1' = iScanMsbA s1 /\ iScanAddrA s1' = iScanAddrA s1 /\
      revEpochOf (iRevArchA s1') = revEpochOf (iRevArchA s1) /\ revSweepTopOf (iRevArchA s1') = revSweepTopOf (iRevArchA s1) /\
      revScanAddr (iRevArchA s1') = revScanAddr (iRevArchA s1).
  Proof.
    intros s1 s1' [Ee Ek].
    assert (Esa : revScanAddr (iRevArchA s1') = revScanAddr (iRevArchA s1)) by exact (f_equal (fun k => fst (snd k)) Ek).
    refine (conj (f_equal (fun e => e.(Fst)) Ee) (conj (f_equal (fun e => e.(Snd).(Fst)) Ee)
             (conj (f_equal (fun e => e.(Snd).(Snd).(Fst)) Ee) (conj (f_equal (fun e => e.(Snd).(Snd).(Snd).(Fst)) Ee)
             (conj Esa (conj _ (conj (f_equal fst Ek) (conj (f_equal (fun k => snd (snd k)) Ek) Esa)))))))).
    unfold iScanAddr; fold (iRevArchA s1') (iRevArchA s1); rewrite Esa; reflexivity.
  Qed.

  Lemma RevokerRel_dev :
    forall g g' (s1 s1' : IState) (s2 s2' : SState),
      RevKept s1 s1' ->
      (forall L, lineContent initLine specRegions (sMemA s2') L = lineContent initLine specRegions (sMemA s2) L) ->
      RACC g' s1' s2' -> REVK g s1 s2 -> REVK g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' HK Hlc Hra Hrk.
    assert (Hmv : forall a sz, memValAt pre post revBase revPfB revPfA initLine (sMemA s2') a sz =
                               memValAt pre post revBase revPfB revPfA initLine (sMemA s2) a sz)
      by (intros a sz; apply memValAt_ext; exact Hlc).
    assert (Hrb : forall b, revBitOf config pre post revBase revPfB revPfA initLine (sMemA s2') b =
                            revBitOf config pre post revBase revPfB revPfA initLine (sMemA s2) b)
      by (intros b; apply revBitOf_ext; exact Hlc).
    destruct (RevKept_obs s1 s1' HK) as [Eph [Ecap [Ebase [Esn [_ [Escan [Eep [Est Esa]]]]]]]].
    unfold RevokerRel in *; destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
    refine (conj _ (conj _ (conj _ (conj _ Hra)))).
    - intros H; rewrite Eph in H; specialize (K1 H).
      unfold revSweepingAt in *; rewrite Eep, Est, Esa; exact K1.
    - intros H; rewrite Eph in H; rewrite Ecap, Ebase, Escan; exact (K2 H).
    - intros H1 H2; rewrite Eph in H1; rewrite Esn in H2; rewrite Escan, Ecap, Hmv; exact (K3 H1 H2).
    - intros H1 H2; rewrite Eph in H1; rewrite Esn in H2; rewrite Ebase, Hrb; exact (K4 H1 H2).
  Qed.

  (* The access after the first line of a store went to a device or was dropped *)
  Lemma acc_devFirst :
    forall g1 (s1 s1' : IState) (s2m : SState) addr size pkt (cr : bool) sl0,
      iReadRpA s1' = iReadRpA s1 -> iDmStA s1' = iDmStA s1 -> RevKept s1 s1' ->
      g_acc pcAddrInit g1 = (if cr then AccStore addr size pkt (WrPend true) else AccNone) ->
      g_revOff pcAddrInit g1 = RevEq ->
      PQ s1' -> optValid (iReadRpA s1) = false ->
      (if andb (negb false) cr then msWriteRq (iMemStA s1') = true /\ msWriteRqV (iMemStA s1') = stepOf true addr size pkt
       else msIdle (iMemStA s1') = true) ->
      dmLoadRq (iDmStA s1) = true -> RNR s1 ->
      (snoopHitsB addr size (iScanMsbA s1) = true -> iRevSnoopHitA s1 = true) ->
      cr = crossesB addr size ->
      sSecondA s2m = (if cr then secondStoreOf addr pkt size else sl0) -> optValid sl0 = false ->
      ACC g1 s1' s2m.
  Proof.
    intros g1 s1 s1' s2m addr size pkt cr sl0 Erp Edm HK Eacc Eoff HPQ Hrp0 Hst0 Hdlq Hrnr Hsnoop Ecr Ess Hsl.
    destruct (RevKept_obs s1 s1' HK) as [Eph [_ [_ [Esn [Emsb _]]]]].
    unfold AccessRel; rewrite Eacc, Eoff.
    unfold revNotReading in Hrnr |- *.
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [_ Hx3]].
    destruct cr; cbn [andb negb] in Hst0.
    - unfold WrStageRel; cbv beta iota zeta.
      rewrite Erp, Edm, Eph, Esn, Emsb.
      destruct Hst0 as [Hwq Hwv].
      exact (conj (conj Hrp0 (conj Hwq (conj Hwv HPQ)))
               (conj Hdlq (conj Hrnr (conj eq_refl (conj Hsnoop (conj (eq_sym Ecr) Ess)))))).
    - cbv beta iota zeta; unfold dmNotAccessing.
      rewrite Erp, Edm, Eph, Ess.
      exact (conj Hst0 (conj Hrp0 (conj HPQ (conj eq_refl (conj (conj Hx1 Hx3) (conj Hrnr Hsl)))))).
  Qed.

  Lemma acc_devSecond :
    forall g1 (s1 s1' : IState) (s2m : SState),
      iReadRpA s1' = iReadRpA s1 -> iDmStA s1' = iDmStA s1 -> RevKept s1 s1' ->
      g_acc pcAddrInit g1 = AccNone -> g_revOff pcAddrInit g1 = RevEq ->
      PQ s1' -> optValid (iReadRpA s1) = false -> msIdle (iMemStA s1') = true ->
      dmLoadRq (iDmStA s1) = true -> RNR s1 -> optValid (sSecondA s2m) = false ->
      ACC g1 s1' s2m.
  Proof.
    intros g1 s1 s1' s2m Erp Edm HK Eacc Eoff HPQ Hrp0 Hidle Hdlq Hrnr Hsl.
    destruct (RevKept_obs s1 s1' HK) as [Eph _].
    unfold AccessRel; rewrite Eacc, Eoff.
    unfold revNotReading in Hrnr |- *; unfold dmNotAccessing.
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [_ Hx3]].
    rewrite Erp, Edm, Eph.
    exact (conj Hidle (conj Hrp0 (conj HPQ (conj eq_refl (conj (conj Hx1 Hx3) (conj Hrnr Hsl)))))).
  Qed.

  (* The relation without `rr_eager` after a commit whose memory write went to a device or was
   * dropped: the impl memory subtree may change anywhere but in the ExternalMem ports *)
  Lemma RefRelNE_devCommit :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) m' G0 m1,
      s1' = writeSubTreeState NPMI s1 m' ->
      (forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      TraceFrameS specRegions (sMemA s2) m1 -> FetchViewExt specRegions m1 (sMemA s2') ->
      g_chain pcAddrInit g = (G0 ++ g_chain pcAddrInit g')%list ->
      GChain pcAddrInit (g_rf0 pcAddrInit g) G0 (g_rf0 pcAddrInit g') ->
      GChain pcAddrInit (g_rf0 pcAddrInit g') (g_chain pcAddrInit g') (iFlushA s1) ->
      (forall e, In (GInst e) G0 -> entryIsFenceI e = false) ->
      g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g ->
      sRfA s2' = cnwbApply pcAddrInit (g_cnwb pcAddrInit g') (g_rf0 pcAddrInit g') ->
      (forall d v, g_cnwb pcAddrInit g' = Some (d, v) -> ChainAvoids (g_chain pcAddrInit g') d) ->
      MEMC g' s1' s2' ->
      (clintSampled (sClintA s2') = true -> clintSampled (sClintA s2) = true) ->
      (plicMeipOf (sPlicA s2') = true -> plicMeipOf (sPlicA s2) = true) ->
      ACC g' s1' s2' -> CNWB g' s1' s2' -> DMQ g' s1' -> REVK g' s1' s2' ->
      RELNE g s1 s2 -> RELNE g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' m' G0 m1 E1 HP Htf Hext1 Ech Hg0 Hgc Hfi Ed2a Erf Hav Hmem Hcf Hpf Hacc Hcn Hdq Hrev H.
    destruct H as [Hrf Hm Hl Hrp Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (Hext : FetchViewExt specRegions (sMemA s2) (sMemA s2')).
    { eapply FetchViewExt_trans; [exact (FetchViewExt_traceFrame specRegions _ _ Htf) | exact Hext1]. }
    constructor.
    - unfold RfRel in *.
      destruct Hrf as [R1 [R2 [R3 R4]]]; rewrite Ech in R4.
      split; [exact Erf |]; split; [rewrite E1; exact Hgc |]; split; [exact Hav |].
      intros G1 e G2 HG Hld; apply (R4 (G0 ++ G1)%list e G2); [rewrite HG, app_assoc; reflexivity | exact Hld].
    - exact Hmem.
    - unfold LatchRel in *.
      intros e Hin; destruct (Hl e) as [L1 L2]; [rewrite Ech; apply in_or_app; right; exact Hin |].
      split; [intros H0; exact (L1 (Hcf H0)) | intros H0; exact (L2 (Hpf H0))].
    - unfold ReplayRel in *.
      intros G1 e G2 rfe HG Hc1.
      apply (FetchAllowedInst_fetchViewExt initLine fwcs specRegions (sMemA s2) (sMemA s2') _ _ Hsnap Hext).
      apply (Hrp (G0 ++ G1)%list e G2 rfe); [rewrite Ech, HG, app_assoc; reflexivity |].
      exact (GChain_app pcAddrInit _ _ _ _ _ Hg0 Hc1).
    - exact Hacc.
    - exact Hcn.
    - exact Hdq.
    - unfold FenceRel, NoFenceIWait in *.
      rewrite HP.
      destruct Hf as [Hf1 [Hf2 Hf3]]; split; [| split].
      + intros Hp; rewrite E1 in Hp; destruct (Hf1 Hp) as [Hnl [Hst' [G1 [e [G2 [HG [Hfie HF]]]]]]].
        split; [rewrite E1; exact Hnl | split; [rewrite E1; exact Hst' |]].
        rewrite Ech in HG.
        assert (Hn : ~ In (GInst e) G0) by (intros Hin; rewrite (Hfi e Hin) in Hfie; discriminate Hfie).
        destruct (app_cons_split G0 (g_chain pcAddrInit g') G1 G2 (GInst e) HG Hn) as [G1' [_ HC]].
        exists G1', e, G2; split; [exact HC | split; [exact Hfie | exact HF]].
      + intros Hw'; destruct (Hf2 Hw') as [Hp [Hnl [Hst' Hno]]].
        split; [rewrite E1; exact Hp | split; [rewrite E1; exact Hnl | split; [rewrite E1; exact Hst' |]]].
        intros e Hin; apply (Hno e); rewrite Ech; apply in_or_app; right; exact Hin.
      + intros G1 e G2 HG Hfie; rewrite E1.
        apply (Hf3 (G0 ++ G1)%list e G2); [rewrite Ech, HG, app_assoc; reflexivity | exact Hfie].
    - unfold ScoreRel in *; rewrite Ed2a; rewrite E1; exact Hs.
    - unfold FrontRel, FetchRespRel in *; rewrite HP; subst s1'.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [exact F1 |]; split; [exact F2 |]; split; [exact F3 |].
      split; [exact F4 |]; split; [exact F5 |].
      split.
      + unfold LiveChain, liveInsts in *; rewrite Ed2a.
        eapply LiveChainG_mono; [exact Hsnap | exact Hext | | exact F6].
        intros p Hp; exact (FrontierRel_mono pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                              initLine fwcs _ s2 s2' p Hsnap Hext Hp).
      + refine (AllPorts_impl _ _ implRegions _ _ F7).
        intros r y HPr; cbv beta zeta in HPr |- *.
        destruct HPr as [C [HC1 [HC2 HC3]]]; exists C; split; [exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hla]]]; exists f, E'; split; [exact HE |].
        intros Hlv; exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hla Hlv)).
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd Whs]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 | split; [rewrite E1; exact Wmd |]].
      rewrite HP; exact Whs.
    - exact Hrev.
  Qed.

  Lemma fenceWait_free :
    forall g (s1 : IState) (s2 : SState) e,
      RELG g s1 s2 -> In (GInst e) (g_chain pcAddrInit g) -> SpecNoWait specRegions (sMemA s2).
  Proof.
    intros g s1 s2 e Hg Hin.
    destruct Hg as [_ Hm _ _ _ _ _ _ Hf _ _ _ _].
    assert (HdecW : forall r (y : TS (implExternalMemRegionTree r)),
               y.(Fst).(Fst).(Snd).(Snd).(Fst) = false \/ ~ y.(Fst).(Fst).(Snd).(Snd).(Fst) = false)
      by (intros r y; destruct (y.(Fst).(Fst).(Snd).(Snd).(Fst)); [right; discriminate | left; reflexivity]).
    destruct (AllPorts_dec (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) HdecW implRegions (iRegionsA s1))
      as [Hnw | Hnw].
    2: { exfalso; unfold FenceRel, NoFenceIWait in Hf; destruct Hf as [_ [Hf2 _]].
         destruct (Hf2 Hnw) as [_ [_ [_ Hno]]]; exact (Hno e Hin). }
    unfold MemRelC, MemRel in Hm; destruct Hm as [[Hpre _] _].
    eapply noWait_pre; [exact I | exact Hpre | exact Hnw].
  Qed.

  (* The first (or only) line of a store, to a device or unmapped: the spec performs the store *)
  Lemma storeDevCommit_first :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' st' env addr size pkt rdy,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (st' ,, (mrq ,, (mrp ,, tt)))) ->
      g_acc pcAddrInit g = AccStore addr size pkt (WrPend false) ->
      lineKind implRegions (lineOf false addr) <> Some true ->
      SemAction env (@implRegionsLineWriteRq type implRegions (buildW false addr pkt size)) mr mr' rdy ->
      (rdy = true -> if andb (negb false) (crossesB addr size)
                     then msWriteRq st' = true /\ msWriteRqV st' = stepOf true addr size pkt else msIdle st' = true) ->
      RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' st' env addr size pkt rdy EM E1 Eacc Hk Hreg Hrt Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold WrStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrp0 [_ [_ Hq]]] [Hdlq [Hrnr [Hoff [Hsnoop [Hsec Hhq]]]]]].
    destruct Hhq as [q [[e [G' [Hch Hq']]] [Hsto [Ea [Esz Epkt]]]]].
    pose proof (proj1 Hc Hdlq) as Hcn.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    rewrite Hch in R2.
    destruct (GChain_cons_inv pcAddrInit _ _ _ _ R2) as [rf1 [Hstep Hgc]]; cbn [ItemStep] in Hstep.
    assert (Hin : In (GInst e) (g_chain pcAddrInit g)) by (rewrite Hch; left; reflexivity).
    pose proof (fenceWait_free g s1 s2 e Hg Hin) as Hsnw.
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    assert (Hmem0 : MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq (sMemA s2) mr).
    { destruct Hm as [Hm0 _]; rewrite <- Hoff, <- Hmr; exact Hm0. }
    assert (Ew : buildW false (stAddrOf (storeCmdOf q)) (stPkt (storeCmdOf q)) (stSizeOf (storeCmdOf q)) =
                 buildW false addr pkt size)
      by (unfold stPkt; rewrite Ea, Esz, <- Epkt; reflexivity).
    rewrite <- Ew in Hreg.
    assert (Hk' : lineKind implRegions (lineOf false (stAddrOf (storeCmdOf q))) <> Some true) by (rewrite Ea; exact Hk).
    destruct (specStep_store_dev pcAddrInit config pre post revBase revPfB revPfA clintS clint plicS plic initLine fwcs
                Hdisj HclintIdx HplicIdx (g_rf0 pcAddrInit g) rf1 (sMemA s2) (sSecondA s2) e q env mr mr' rdy
                Hstep Hq' Hsto Hsnw Hsec (Hrp [] e G' (g_rf0 pcAddrInit g) Hch (GChainNil pcAddrInit _))
                (proj1 (Hl e Hin)) (proj2 (Hl e Hin)) Hmem0 Hk' Hreg)
      as [Erdy [m1 [ms' [Htf [Hok Hsp]]]]].
    specialize (Hrt Erdy).
    remember (crossesB addr size) as cr eqn:Ecr.
    assert (Esl : stCommitSl (storeCmdOf q) (sSecondA s2) = if cr then secondStoreOf addr pkt size else sSecondA s2)
      by (unfold stCommitSl, stPkt; rewrite Ea, Esz, <- Epkt, <- Ecr; reflexivity).
    rewrite Esl, <- R1, mkSys_eta in Hsp.
    remember (mkSysA rf1 ms' (if cr then secondStoreOf addr pkt size else sSecondA s2)) as s2m eqn:Es2m in Hsp.
    remember (if cr then AccStore addr size pkt (WrPend true) else AccNone) as acc' eqn:Eacc'.
    remember (mkGhost pcAddrInit G' rf1 None (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) acc') as g1 eqn:Eg1.
    assert (Ems : sMemA s2m = ms') by (rewrite Es2m; reflexivity).
    assert (Ess : sSecondA s2m = if cr then secondStoreOf addr pkt size else sSecondA s2) by (rewrite Es2m; reflexivity).
    assert (Ers : sRfA s2m = rf1) by (rewrite Es2m; reflexivity).
    destruct Hok as [Hmr' [Hdi [Hlc [Hfv [Hsn [Hcs [Hpm [HPorts [Hex Hky]]]]]]]]].
    assert (Hmr1 : iRegionsA s1' = mr') by (rewrite E1; reflexivity).
    assert (HK : RevKept s1 s1') by (split; unfold iRev; rewrite Hmr1, Hmr; [exact Hex | exact Hky]).
    assert (HP : forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P; rewrite Hmr1, Hmr; apply HPorts).
    assert (Hmem : MEMC g1 s1' s2m).
    { rewrite Eg1; unfold MemRelC; cbn [g_revOff]; rewrite Hoff, Hmr1, Ems.
      destruct Hm as [_ [Hdi0 Hsnap0]].
      split; [exact Hmr' |]; split; [apply Hdi; rewrite <- Hmr; exact Hdi0 |].
      apply Hsn; exact (SnapshotOK_traceFrame specRegions fwcs _ _ Htf Hsnap0). }
    assert (HPQ : PQ s1') by (unfold PortsQuiet; rewrite HP; exact Hq).
    assert (Hlc2 : forall L, lineContent initLine specRegions (sMemA s2m) L = lineContent initLine specRegions (sMemA s2) L).
    { intros L; rewrite Ems, Hlc; exact (lineContent_traceFrame initLine specRegions _ _ Htf L). }
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [Hx2 Hx3]].
    assert (Hne : RELNE g1 s1' s2m).
    { apply (RefRelNE_devCommit g g1 s1 s1' s2 s2m _ [GInst e] m1 E1 HP Htf).
      - rewrite Ems; exact Hfv.
      - rewrite Eg1; exact Hch.
      - rewrite Eg1; eapply GChainInst; [exact Hstep | apply GChainNil].
      - rewrite Eg1; exact Hgc.
      - intros e0 [He0 | []]; injection He0 as <-; unfold entryIsFenceI; rewrite Hq'; exact (opStore_notFenceI _ Hsto).
      - rewrite Eg1; reflexivity.
      - rewrite Eg1, Ers; reflexivity.
      - rewrite Eg1; intros d v Hcn'; discriminate Hcn'.
      - exact Hmem.
      - unfold sClint; rewrite Ems; intros H0; apply Hcs in H0.
        unfold specClintState in *; rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) in H0 by exact I; exact H0.
      - unfold sPlic; rewrite Ems; intros H0; apply Hpm in H0.
        unfold specPlicState in *; rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) in H0 by exact I; exact H0.
      - assert (Erp1 : iReadRpA s1' = iReadRpA s1) by (timeout 10 (rewrite E1; unfold iReadRp; rewrite EM; reflexivity)).
        assert (Edm1 : iDmStA s1' = iDmStA s1) by (timeout 10 (rewrite E1; reflexivity)).
        assert (Emst : iMemStA s1' = st') by (timeout 10 (rewrite E1; reflexivity)).
        assert (Hst1 : if andb (negb false) cr then msWriteRq (iMemStA s1') = true /\ msWriteRqV (iMemStA s1') = stepOf true addr size pkt
                       else msIdle (iMemStA s1') = true)
          by (timeout 10 (pose proof Hrt as H0; rewrite <- Emst in H0; exact H0)).
        assert (Eg1a : g_acc pcAddrInit g1 = (if cr then AccStore addr size pkt (WrPend true) else AccNone))
          by (timeout 10 (rewrite Eg1, Eacc'; reflexivity)).
        assert (Eg1o : g_revOff pcAddrInit g1 = RevEq) by (timeout 10 (rewrite Eg1; exact Hoff)).
        timeout 10 exact (acc_devFirst g1 s1 s1' s2m addr size pkt cr (sSecondA s2) Erp1 Edm1 HK Eg1a Eg1o HPQ Hrp0 Hst1
                            Hdlq Hrnr Hsnoop Ecr Ess Hsec).
      - rewrite Eg1; unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        assert (Edm : iDmStA s1' = iDmStA s1) by (rewrite E1; reflexivity).
        rewrite Edm, Hx1, Hx2.
        split; [intros _; reflexivity |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        intros H; discriminate H.
      - rewrite Eg1; unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc]; cbv zeta in Hd |- *.
        rewrite Eacc, Hch in Hd; cbn [accTakesHead] in Hd.
        rewrite (chainReqs_store_head e q G' Hq' Hsto) in Hd.
        assert (Eat : accTakesHead acc' = false) by (rewrite Eacc'; destruct cr; reflexivity).
        rewrite Eat; rewrite E1; exact Hd.
      - apply (RevokerRel_dev g g1 s1 s1' s2 s2m HK Hlc2); [| exact Hrk].
        rewrite Eg1; unfold RevAccRel; cbn [g_acc]; rewrite Eacc'; destruct cr; exact I.
      - apply RefRelNE_of_G; exact Hg. }
    assert (Hlen : (length (g_chain pcAddrInit g1) <= length G')%nat) by (rewrite Eg1; apply le_n).
    destruct (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity
                mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clintS clint plicS plic initLine fwcs
                Hdisj (length G') g1 s1' s2m Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction; [apply In_specStep_spec | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  (* The second line of a crossing store, to a device or unmapped: the spec performs it *)
  Lemma storeDevCommit_second :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' st' env addr size pkt rdy,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (st' ,, (mrq ,, (mrp ,, tt)))) ->
      g_acc pcAddrInit g = AccStore addr size pkt (WrPend true) ->
      lineKind implRegions (lineOf true addr) <> Some true ->
      SemAction env (@implRegionsLineWriteRq type implRegions (buildW true addr pkt size)) mr mr' rdy ->
      (rdy = true -> if andb (negb true) (crossesB addr size)
                     then msWriteRq st' = true /\ msWriteRqV st' = stepOf true addr size pkt else msIdle st' = true) ->
      RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' st' env addr size pkt rdy EM E1 Eacc Hk Hreg Hrt Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold WrStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrp0 [_ [_ Hq]]] [Hdlq [Hrnr [Hoff [Hsnoop [Hcr Hsec]]]]]].
    pose proof (proj1 Hc Hdlq) as Hcn.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    assert (Hmem0 : MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq (sMemA s2) mr).
    { destruct Hm as [Hm0 _]; rewrite <- Hoff, <- Hmr; exact Hm0. }
    destruct (specSecondLine_store_dev pcAddrInit config pre post revBase revPfB revPfA clintS clint plicS plic initLine fwcs
                Hdisj HclintIdx HplicIdx (sRfA s2) (sMemA s2) addr pkt size env mr mr' rdy Hmem0 Hk Hreg)
      as [Erdy [ms' [Hok Hsp]]].
    specialize (Hrt Erdy); cbn [andb negb] in Hrt.
    rewrite <- Hsec, mkSys_eta in Hsp.
    remember (mkSysA (sRfA s2) ms' (getDefault (Option SecondLine))) as s2m eqn:Es2m in Hsp.
    remember (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) None (g_revOff pcAddrInit g)
                (g_d2aFo pcAddrInit g) AccNone) as g1 eqn:Eg1.
    assert (Ems : sMemA s2m = ms') by (rewrite Es2m; reflexivity).
    assert (Ess : sSecondA s2m = getDefault (Option SecondLine)) by (rewrite Es2m; reflexivity).
    assert (Ers : sRfA s2m = sRfA s2) by (rewrite Es2m; reflexivity).
    destruct Hok as [Hmr' [Hdi [Hlc [Hfv [Hsn [Hcs [Hpm [HPorts [Hex Hky]]]]]]]]].
    assert (Hmr1 : iRegionsA s1' = mr') by (rewrite E1; reflexivity).
    assert (HK : RevKept s1 s1') by (split; unfold iRev; rewrite Hmr1, Hmr; [exact Hex | exact Hky]).
    assert (HP : forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P; rewrite Hmr1, Hmr; apply HPorts).
    assert (Hmem : MEMC g1 s1' s2m).
    { rewrite Eg1; unfold MemRelC; cbn [g_revOff]; rewrite Hoff, Hmr1, Ems.
      destruct Hm as [_ [Hdi0 Hsnap0]].
      split; [exact Hmr' |]; split; [apply Hdi; rewrite <- Hmr; exact Hdi0 | apply Hsn; exact Hsnap0]. }
    assert (HPQ : PQ s1') by (unfold PortsQuiet; rewrite HP; exact Hq).
    assert (Hlc2 : forall L, lineContent initLine specRegions (sMemA s2m) L = lineContent initLine specRegions (sMemA s2) L)
      by (intros L; rewrite Ems; apply Hlc).
    pose proof (TraceFrameS_refl specRegions (sMemA s2)) as Htf.
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [Hx2 Hx3]].
    assert (Hne : RELNE g1 s1' s2m).
    { apply (RefRelNE_devCommit g g1 s1 s1' s2 s2m _ [] (sMemA s2) E1 HP Htf).
      - rewrite Ems; exact Hfv.
      - rewrite Eg1; reflexivity.
      - rewrite Eg1; apply GChainNil.
      - rewrite Eg1; exact R2.
      - intros e0 [].
      - rewrite Eg1; reflexivity.
      - rewrite Eg1, Ers, R1; reflexivity.
      - rewrite Eg1; intros d v Hcn'; discriminate Hcn'.
      - exact Hmem.
      - unfold sClint; rewrite Ems; exact Hcs.
      - unfold sPlic; rewrite Ems; exact Hpm.
      - assert (Erp1 : iReadRpA s1' = iReadRpA s1) by (timeout 10 (rewrite E1; unfold iReadRp; rewrite EM; reflexivity)).
        assert (Edm1 : iDmStA s1' = iDmStA s1) by (timeout 10 (rewrite E1; reflexivity)).
        assert (Emst : iMemStA s1' = st') by (timeout 10 (rewrite E1; reflexivity)).
        assert (Hst1 : msIdle (iMemStA s1') = true) by (timeout 10 (pose proof Hrt as H0; rewrite <- Emst in H0; exact H0)).
        assert (Eg1a : g_acc pcAddrInit g1 = AccNone) by (timeout 10 (rewrite Eg1; reflexivity)).
        assert (Eg1o : g_revOff pcAddrInit g1 = RevEq) by (timeout 10 (rewrite Eg1; exact Hoff)).
        assert (Hsl1 : optValid (sSecondA s2m) = false) by (timeout 10 (rewrite Ess; reflexivity)).
        timeout 10 exact (acc_devSecond g1 s1 s1' s2m Erp1 Edm1 HK Eg1a Eg1o HPQ Hrp0 Hst1 Hdlq Hrnr Hsl1).
      - rewrite Eg1; unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        assert (Edm : iDmStA s1' = iDmStA s1) by (rewrite E1; reflexivity).
        rewrite Edm, Hx1, Hx2.
        split; [intros _; reflexivity |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        intros H; discriminate H.
      - rewrite Eg1; unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc]; cbv zeta in Hd |- *.
        rewrite Eacc in Hd; cbn [accTakesHead] in Hd |- *.
        rewrite E1; exact Hd.
      - apply (RevokerRel_dev g g1 s1 s1' s2 s2m HK Hlc2); [| exact Hrk].
        rewrite Eg1; unfold RevAccRel; exact I.
      - apply RefRelNE_of_G; exact Hg. }
    assert (Hlen : (length (g_chain pcAddrInit g1) <= length (g_chain pcAddrInit g))%nat) by (rewrite Eg1; apply le_n).
    destruct (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity
                mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clintS clint plicS plic initLine fwcs
                Hdisj (length (g_chain pcAddrInit g)) g1 s1' s2m Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction;
        [apply (In_specSecondLine_spec pcAddrInit config pre post revBase revPfB revPfA clintS plicS) | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.


  (* --- 4. The Step --- *)

  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                   clintS clint plicS plic initLine fwcs).

  Theorem stepOK_writeRqStep :
    STEPOK (@writeRqStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold writeRqStep in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    change (readSubTreeState NPMI s1) with (iMemA s1) in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    destruct (msWriteRqV mst) as [b [[addr [size [pkt []]]] []]] eqn:Ev.
    destruct (writeRqStep_char pre post revBase revPfB revPfA _ mr mst mrq mrp m' _ b addr size pkt Ev Hm')
      as [-> | [Hw [Hnp [mr' [rdy [st' [Hreg [-> [Hrf Hrt]]]]]]]]].
    { exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM]. }
    pose proof Hg as Hg0; destruct Hg0 as [Hrf0 Hm Hl Hrp He Ha Hc Hd Hfe Hs Hfr Hwf Hrk].
    assert (Hmst : iMemStA s1 = mst) by (unfold iMemSt; rewrite EM; reflexivity).
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    assert (Hu : forall L, lineUnique implRegions L)
      by (intros L; apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj).
    assert (Hw1 : msWriteRq (iMemStA s1) = true) by (rewrite Hmst; exact Hw).
    assert (Hnp1 : noPortWriteB implRegions (iRegionsA s1) = true) by (rewrite Hmr; exact Hnp).
    destruct (AccessRel_writeRq g s1 s2 Ha Hw1 Hnp1)
      as [[addr' [size' [pkt' [b' Eacc]]]] | [addr' [pkt' Eacc]]].
    - (* a store line *)
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'; unfold WrStageRel in Ha'; cbv beta iota zeta in Ha'.
      destruct Ha' as [[Hrp0 [_ [HwV Hq]]] _].
      rewrite Hmst, Ev in HwV.
      destruct (stepOf_inj _ _ _ _ _ _ _ _ HwV) as [<- [<- [<- <-]]].
      destruct (lineKind implRegions (lineOf b addr)) as [[|] |] eqn:Hk.
      + (* ExternalMem: staged *)
        assert (Hk' : lineKind implRegions (buildW b addr pkt size).(Fst) = Some true) by (rewrite buildW_addr; exact Hk).
        unfold PortsQuiet in Hq; rewrite Hmr in Hq.
        destruct (regionsWrite_stage implRegions _ mr mr' rdy (buildW b addr pkt size) Hk' (Hu _) Hq Hreg) as [-> Hst].
        rewrite buildW_addr in Hst.
        exists s2; split; [apply NilAction; reflexivity |].
        set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                  (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccStore addr size pkt (WrStaged b))).
        exists g'.
        rewrite <- Hmr in Hst.
        assert (HR : iRevA s1' = iRevA s1) by exact (iRev_stage s1 s1' _ _ _ E1 Hst).
        apply (RefRelG_stage g g' s1 s1' s2 _ _ _ E1 Hst eq_refl eq_refl eq_refl eq_refl eq_refl); [| | | exact Hg].
        * cbn [g_acc accTakesHead]; rewrite Eacc; destruct b; reflexivity.
        * apply (acc_stageStore g g' s1 s1' s2 addr size pkt b st' Eacc eq_refl eq_refl eq_refl);
            [rewrite E1; reflexivity | exact (Hrt eq_refl) | rewrite E1; unfold iReadRp; rewrite EM; reflexivity
            | rewrite E1; reflexivity | exact HR | exact Hk | | exact Ha].
          rewrite E1; change (AllPorts (stagedP (lineOf b addr) (someWrite (buildW b addr pkt size))) implRegions mr').
          apply (stagedP_stage _ _ _ (iRegionsA s1)); [apply Hu | rewrite Hmr; exact Hq | exact Hst].
        * unfold RevAccRel; exact I.
      + (* CustomMem: the device write commits *)
        assert (Hk2 : lineKind implRegions (lineOf b addr) <> Some true) by (rewrite Hk; discriminate).
        destruct b.
        * exact (storeDevCommit_second g s1 s1' s2 mr mst mrq mrp mr' st' _ addr size pkt rdy EM E1 Eacc Hk2 Hreg Hrt Hg).
        * exact (storeDevCommit_first g s1 s1' s2 mr mst mrq mrp mr' st' _ addr size pkt rdy EM E1 Eacc Hk2 Hreg Hrt Hg).
      + (* unmapped: the write is dropped, the spec commits *)
        assert (Hk2 : lineKind implRegions (lineOf b addr) <> Some true) by (rewrite Hk; discriminate).
        destruct b.
        * exact (storeDevCommit_second g s1 s1' s2 mr mst mrq mrp mr' st' _ addr size pkt rdy EM E1 Eacc Hk2 Hreg Hrt Hg).
        * exact (storeDevCommit_first g s1 s1' s2 mr mst mrq mrp mr' st' _ addr size pkt rdy EM E1 Eacc Hk2 Hreg Hrt Hg).
    - (* the revoker's write: its line is ExternalMem, so it is staged *)
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'; unfold WrStageRel in Ha'; cbv beta iota zeta in Ha'.
      destruct Ha' as [[Hrp0 [_ [HwV Hq]]] _].
      rewrite Hmst, Ev in HwV.
      destruct (stepOf_inj _ _ _ _ _ _ _ _ HwV) as [-> [<- [-> <-]]].
      pose proof Hrk as Hrk0; unfold RevokerRel in Hrk0; destruct Hrk0 as [_ [_ [_ [_ Hra]]]].
      pose proof Hra as Hra0; unfold RevAccRel in Hra0; rewrite Eacc in Hra0.
      destruct Hra0 as [sa [_ [_ [_ [_ [_ [_ Hk]]]]]]].
      assert (Hk' : lineKind implRegions (buildW false addr pkt capSz).(Fst) = Some true) by (rewrite buildW_addr; exact Hk).
      unfold PortsQuiet in Hq; rewrite Hmr in Hq.
      destruct (regionsWrite_stage implRegions _ mr mr' rdy (buildW false addr pkt capSz) Hk' (Hu _) Hq Hreg) as [-> Hst].
      rewrite buildW_addr in Hst.
      exists s2; split; [apply NilAction; reflexivity |].
      set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccRevWrite addr pkt (WrStaged false))).
      exists g'.
      rewrite <- Hmr in Hst.
      assert (HR : iRevA s1' = iRevA s1) by exact (iRev_stage s1 s1' _ _ _ E1 Hst).
      apply (RefRelG_stage g g' s1 s1' s2 _ _ _ E1 Hst eq_refl eq_refl eq_refl eq_refl eq_refl); [| | | exact Hg].
      + cbn [g_acc accTakesHead]; rewrite Eacc; reflexivity.
      + apply (acc_stageRev g g' s1 s1' s2 addr pkt st' Eacc eq_refl eq_refl);
          [rewrite E1; reflexivity | exact (Hrt eq_refl) | rewrite E1; unfold iReadRp; rewrite EM; reflexivity
          | rewrite E1; reflexivity | exact HR | exact Hk | | exact Ha].
        rewrite E1; change (AllPorts (stagedP (lineOf false addr) (someWrite (buildW false addr pkt capSz))) implRegions mr').
        apply (stagedP_stage _ _ _ (iRegionsA s1)); [apply Hu | rewrite Hmr; exact Hq | exact Hst].
      + exact (racc_stageRev g g' s1 s1' s2 addr pkt _ _ Eacc eq_refl HR Hra).
  Qed.
End WriteRqStep.
