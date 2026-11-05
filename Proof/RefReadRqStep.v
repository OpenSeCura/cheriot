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
From Cheriot.Proof Require Import RefRouteAt RefRqStepChar RefRqStage RefDevSim RefDevWrite RefDevCommit RefWriteRqStep.
From Cheriot.Proof Require Import RefRevCapDev.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the read step of the memory `state` register (`readRqStep`): an ExternalMem
 * line is staged in its region's `portRq` (the spec stutters); a CustomMem line is read from the
 * device and an unmapped line answers zeros, both at once (a load commits; the revoker's cap read
 * gives the spec revoker's step). *)

Lemma msReadRq_excl :
  forall st, msReadRq st = true ->
    msIdle st = false /\ msReadRqSent st = false /\ msReadRpReady st = false /\ msWriteRq st = false.
Proof.
  intros [d tg]; unfold msIdle, msReadRq, msReadRqSent, msReadRpReady, msWriteRq; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Section ReadRqStep.
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
  Local Abbreviation iRpReadyA := (iRpReady pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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

  Local Abbreviation iScanAddrA := (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevScanBaseA := (iRevScanBase pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RDS := (RdStageRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA := (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* --- 1. Which Accesses the Step Can Serve --- *)

  Lemma AccessRel_readRq :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 -> msReadRq (iMemStA s1) = true ->
      (exists ld pkt0 b, g_acc pcAddrInit g = AccLoad ld pkt0 (RdPend b)) \/
      (exists rc, g_acc pcAddrInit g = AccDmRev rc (RdPend false)) \/
      g_acc pcAddrInit g = AccRevCap (RdPend false) \/ g_acc pcAddrInit g = AccRevBit (RdPend false).
  Proof.
    intros g s1 s2 Ha Hr.
    destruct (msReadRq_excl _ Hr) as [X1 [X2 [X3 X4]]].
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [b|b] | ld pkt0 [b|b|b|b rp|res]
                                     | rc [b|b|b|b rp|res] | [b|b|b|b rp|res]
                                     | [b|b|b|b rp|res] | addr pkt [b|b]];
      unfold WrStageRel, RdStageRel, rdSecond, wrSecond in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      repeat match goal with H : (if ?c then _ else _) |- _ => destruct c; cbv iota in H end;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (match goal with H : ?x = true, H' : ?x = false |- _ => rewrite H in H'; discriminate H' end).
    all: try match goal with H : ?b = false |- _ => is_var b; subst b end.
    all: first [ left; eexists _, _, _; reflexivity | right; left; eexists; reflexivity
               | right; right; left; reflexivity | right; right; right; reflexivity ].
  Qed.

  (* --- 2. An ExternalMem Line: the Read Is Staged --- *)

  Lemma rds_staged :
    forall addr size pkt0 (b : bool) (s1 s1' : IState) st',
      RDS addr size pkt0 (RdPend b) s1 -> iMemStA s1' = st' -> msReadRqSent st' = true ->
      msReadRqSentV st' = (crossesB addr size ,, (stepOf b addr size pkt0 ,, tt)) ->
      iReadRpA s1' = iReadRpA s1 -> iRpReadyA s1' = iRpReadyA s1 -> lineKind implRegions (lineOf b addr) = Some true ->
      AllPorts (stagedP (lineOf b addr) (someRead (lineOf b addr))) implRegions (iRegionsA s1') ->
      RDS addr size pkt0 (RdStaged b) s1'.
  Proof.
    intros addr size pkt0 b s1 s1' st' H Emst Hs Hv Erp Erdy Hk Hp.
    unfold RdStageRel in *; destruct H as [_ [_ [Hrp [Hrdy _]]]].
    rewrite Emst, Erp, Erdy; exact (conj (conj Hs Hv) (conj Hrp (conj Hrdy (conj Hk Hp)))).
  Qed.

  Lemma acc_stageLoad :
    forall g g' (s1 s1' : IState) (s2 : SState) ld pkt0 (b : bool),
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdPend b) -> g_acc pcAddrInit g' = AccLoad ld pkt0 (RdStaged b) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g -> g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g ->
      g_chain pcAddrInit g' = g_chain pcAddrInit g ->
      RDS (ldAddr ld) (plSize (ldPending ld)) pkt0 (RdStaged b) s1' ->
      iRequesterA s1' = iRequesterA s1 -> iDmStA s1' = iDmStA s1 -> iRevA s1' = iRevA s1 ->
      ACC g s1 s2 -> ACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 ld pkt0 b Eacc Eacc' Eo Ec Ech Hrds Erq Edm HR Ha.
    unfold AccessRel in *; rewrite Eacc in Ha; rewrite Eacc', Eo, Ec.
    destruct Ha as [_ [Hq [Hdl [Hdv [Hrn [Hoff Hm]]]]]].
    unfold revNotReading, iRevPhase, HeadReq in *; rewrite Erq, Edm, HR, Ech.
    refine (conj Hrds (conj Hq (conj Hdl (conj Hdv (conj Hrn (conj Hoff _)))))).
    destruct b; exact Hm.
  Qed.

  Lemma acc_stageDmRev :
    forall g g' (s1 s1' : IState) (s2 : SState) rc,
      g_acc pcAddrInit g = AccDmRev rc (RdPend false) -> g_acc pcAddrInit g' = AccDmRev rc (RdStaged false) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g -> g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g ->
      RDS (revByteAddrOf config (rcBase rc)) byteSz (getDefault CapPacket) (RdStaged false) s1' ->
      iRequesterA s1' = iRequesterA s1 -> iDmStA s1' = iDmStA s1 -> iRevA s1' = iRevA s1 ->
      ACC g s1 s2 -> ACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 rc Eacc Eacc' Eo Ec Hrds Erq Edm HR Ha.
    unfold AccessRel in *; rewrite Eacc in Ha; rewrite Eacc', Eo, Ec.
    destruct Ha as [_ Hrest].
    unfold revNotReading, iRevPhase in *; rewrite Erq, Edm, HR.
    exact (conj Hrds Hrest).
  Qed.

  Lemma acc_stageRevCap :
    forall g g' (s1 s1' : IState) (s2 : SState),
      g_acc pcAddrInit g = AccRevCap (RdPend false) -> g_acc pcAddrInit g' = AccRevCap (RdStaged false) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g -> iRevA s1' = iRevA s1 ->
      RDS (iScanAddrA s1) capSz (getDefault CapPacket) (RdStaged false) s1' ->
      iRequesterA s1' = iRequesterA s1 -> iDmStA s1' = iDmStA s1 ->
      ACC g s1 s2 -> ACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 Eacc Eacc' Eo HR Hrds Erq Edm Ha.
    unfold AccessRel in *; rewrite Eacc in Ha; rewrite Eacc', Eo.
    destruct Ha as [_ Hrest].
    assert (Es : iScanAddrA s1' = iScanAddrA s1) by (unfold iScanAddr; rewrite HR; reflexivity).
    unfold dmNotAccessing, iRevPhase in *; rewrite Es, Erq, Edm, HR.
    exact (conj Hrds Hrest).
  Qed.

  Lemma acc_stageRevBit :
    forall g g' (s1 s1' : IState) (s2 : SState),
      g_acc pcAddrInit g = AccRevBit (RdPend false) -> g_acc pcAddrInit g' = AccRevBit (RdStaged false) ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g -> iRevA s1' = iRevA s1 ->
      RDS (revByteAddrOf config (iRevScanBaseA s1)) byteSz (getDefault CapPacket) (RdStaged false) s1' ->
      iRequesterA s1' = iRequesterA s1 -> iDmStA s1' = iDmStA s1 ->
      ACC g s1 s2 -> ACC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 Eacc Eacc' Eo HR Hrds Erq Edm Ha.
    unfold AccessRel in *; rewrite Eacc in Ha; rewrite Eacc', Eo.
    destruct Ha as [_ Hrest].
    assert (Es : iRevScanBaseA s1' = iRevScanBaseA s1) by (unfold iRevScanBase; rewrite HR; reflexivity).
    unfold dmNotAccessing, iRevPhase in *; rewrite Es, Erq, Edm, HR.
    exact (conj Hrds Hrest).
  Qed.

  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevStageA := (iRev_stage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The facts after an ExternalMem line was staged *)
  Lemma readStage_facts :
    forall (s1 s1' : IState) mr mst mrq mrp mrdy mr' st' mrp' env b addr size pkt res,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (st' ,, (mrq ,, (mrp' ,, (mrdy ,, tt))))) ->
      lineKind implRegions (lineOf b addr) = Some true -> PQ s1 ->
      SemAction env (@implRegionsLineReadRq type implRegions (rdLineOf b addr) (rdMaskOf b addr size)) mr mr' res ->
      (res.(Fst) = true -> msReadRqSent st' = true /\
                           msReadRqSentV st' = (crossesB addr size ,, (stepOf b addr size pkt ,, tt)) /\
                           mrp' = (if optValid res.(Snd).(Fst) then res.(Snd).(Fst) else mrp)) ->
      StageAtL (lineOf b addr) (someRead (lineOf b addr)) implRegions (iRegionsA s1) mr' /\
      iMemStA s1' = st' /\ msReadRqSent st' = true /\
      msReadRqSentV st' = (crossesB addr size ,, (stepOf b addr size pkt ,, tt)) /\
      iReadRpA s1' = iReadRpA s1 /\ iRpReadyA s1' = iRpReadyA s1 /\
      AllPorts (stagedP (lineOf b addr) (someRead (lineOf b addr))) implRegions (iRegionsA s1') /\
      iRequesterA s1' = iRequesterA s1 /\ iDmStA s1' = iDmStA s1 /\ iRevA s1' = iRevA s1.
  Proof.
    intros s1 s1' mr mst mrq mrp mrdy mr' st' mrp' env b addr size pkt res EM E1 Hk Hq Hreg Hrt.
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    assert (Hu : forall L, lineUnique implRegions L)
      by (intros L; apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj).
    unfold PortsQuiet in Hq; rewrite Hmr in Hq.
    rewrite rdLineOf_eq in Hreg.
    destruct (regionsRead_stage implRegions env mr mr' res (lineOf b addr) _ Hk (Hu _) Hq Hreg) as [Eres Hst].
    subst res; destruct (Hrt eq_refl) as [Hs [HsV Ermp]].
    assert (Emp : mrp' = mrp) by (rewrite Ermp; reflexivity).
    subst mrp'.
    rewrite <- Hmr in Hst.
    split; [exact Hst |].
    split; [rewrite E1; reflexivity |].
    split; [exact Hs |]; split; [exact HsV |].
    split; [rewrite E1; unfold iReadRp; rewrite EM; reflexivity |].
    split; [rewrite E1; unfold iRpReady; rewrite EM; reflexivity |].
    split.
    { rewrite E1; change (AllPorts (stagedP (lineOf b addr) (someRead (lineOf b addr))) implRegions mr').
      apply (stagedP_stage _ _ _ (iRegionsA s1)); [apply Hu | rewrite Hmr; exact Hq | exact Hst]. }
    split; [rewrite E1; unfold iRequester; rewrite EM; reflexivity |].
    split; [rewrite E1; reflexivity |].
    exact (iRevStageA s1 s1' _ _ _ E1 Hst).
  Qed.

  (* --- 3. A CustomMem or Unmapped Line: a Load Line Commits --- *)

  Local Abbreviation revS := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revS plicS type).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation specLoadWbA := (specLoadWb config pre post revBase revPfB revPfA initLine).
  Local Abbreviation ldDevRfA := (ldDevRf pcAddrInit config pre post revBase revPfB revPfA initLine).
  Local Abbreviation RELNE := (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).
  Local Abbreviation KEPT := (RevKept pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation keptObsA := (RevKept_obs pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation fenceFreeA := (fenceWait_free pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                      clintS clint plicS plic initLine fwcs).
  Local Abbreviation devNEA := (RefRelNE_devCommit pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).
  Local Abbreviation revDevA := (RevokerRel_dev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                   initLine).
  Local Abbreviation NEofG := (RefRelNE_of_G pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).
  Local Abbreviation eagerA := (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs Hdisj).
  Local Abbreviation stageA := (RefRelG_stage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).

  (* The committed load of a first line read from a device (`None` while the second line is pending) *)
  Definition ldDevCnwb (m2 : TS (specMemTree specRegions)) (ld : type LoadCmd) (rpv : type LineReadRp)
    : option (bits RegIdxSzReal * type FullECapWithTag) :=
    if crossesB (ldAddr ld) (plSize (ldPending ld)) then None
    else Some (specLoadWbA m2 (ldPending ld) (singleLoadVal ld rpv)).

  Lemma ldDevRf_cnwb : forall m2 ld rpv rf1, ldDevRfA m2 ld rpv rf1 = cnwbApply pcAddrInit (ldDevCnwb m2 ld rpv) rf1.
  Proof. intros m2 ld rpv rf1; unfold ldDevRf, ldDevCnwb; destruct (crossesB (ldAddr ld) (plSize (ldPending ld))); reflexivity. Qed.

  Lemma ldDevCnwb_dst : forall m2 ld rpv d v, ldDevCnwb m2 ld rpv = Some (d, v) -> d = (ldPending ld).(Fst).
  Proof.
    intros m2 ld rpv d v; unfold ldDevCnwb.
    destruct (crossesB (ldAddr ld) (plSize (ldPending ld))); intros H; [discriminate H |].
    apply some_eq_fst in H; cbn [fst] in H.
    rewrite <- H; apply fst_specLoadWb.
  Qed.

  (* The first (or only) line of a load, from a device or unmapped: the spec steps the load *)
  Lemma loadDevCommit_first :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mrdy mr' st' mrp' env ld pkt0 res,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (st' ,, (mrq ,, (mrp' ,, (mrdy ,, tt))))) ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdPend false) ->
      lineKind implRegions (lineOf false (ldAddr ld)) <> Some true ->
      SemAction env (@implRegionsLineReadRq type implRegions (rdLineOf false (ldAddr ld))
                       (rdMaskOf false (ldAddr ld) (plSize (ldPending ld)))) mr mr' res ->
      (res.(Fst) = true -> msReadRqSent st' = true /\
                           msReadRqSentV st' = (crossesB (ldAddr ld) (plSize (ldPending ld)) ,,
                                                (stepOf false (ldAddr ld) (plSize (ldPending ld)) pkt0 ,, tt)) /\
                           mrp' = (if optValid res.(Snd).(Fst) then res.(Snd).(Fst) else mrp)) ->
      RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' env ld pkt0 res EM E1 Eacc Hk Hreg Hrt Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrq [_ [Hrp0 [Hrdy0 Hq]]]] [Hreq [Hdlr [Hdlv [Hrnr [Hoff [Hsec [Hpk [Hcn Hhq]]]]]]]]].
    destruct Hhq as [q [[e [G' [Hch Hq']]] [Hld Eld]]].
    revert Hdlv; subst ld; intros Hdlv.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    rewrite Hch in R2.
    destruct (GChain_cons_inv pcAddrInit _ _ _ _ R2) as [rf1 [Hstep Hgc]]; cbn [ItemStep] in Hstep.
    assert (Hin : In (GInst e) (g_chain pcAddrInit g)) by (rewrite Hch; left; reflexivity).
    pose proof (fenceFreeA g s1 s2 e Hg Hin) as Hsnw.
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    assert (Hmem0 : MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq (sMemA s2) mr).
    { destruct Hm as [Hm0 _]; rewrite <- Hoff, <- Hmr; exact Hm0. }
    destruct (specStep_load_dev pcAddrInit config pre post revBase revPfB revPfA clintS clint plicS plic initLine fwcs
                Hdisj HclintIdx HplicIdx HrevTab (g_rf0 pcAddrInit g) rf1 (sMemA s2) (sSecondA s2) e q env mr mr' res
                Hstep Hq' Hld Hsnw Hsec (Hrp [] e G' (g_rf0 pcAddrInit g) Hch (GChainNil pcAddrInit _))
                (proj1 (Hl e Hin)) (proj2 (Hl e Hin)) Hmem0 Hk Hreg)
      as [rpv [m1 [ms' [m2 [Eres [Htf [Hok [Hm2 Hsp]]]]]]]].
    subst res; destruct (Hrt eq_refl) as [Hsent1 [HsV1 Emp]].
    assert (Emp' : mrp' = (rpv ,, (true ,, tt))) by (rewrite Emp; reflexivity).
    clear Emp; subst mrp'.
    rewrite <- R1, mkSys_eta in Hsp.
    remember (mkSysA (ldDevRfA m2 (loadCmdOf q) rpv rf1) m2 (ldDevSl (loadCmdOf q) rpv (sSecondA s2))) as s2m eqn:Es2m in Hsp.
    remember (mkGhost pcAddrInit G' rf1 (ldDevCnwb m2 (loadCmdOf q) rpv) (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g)
                (AccLoad (loadCmdOf q) pkt0 (RdArrived false rpv))) as g1 eqn:Eg1.
    assert (Ems : sMemA s2m = m2) by (rewrite Es2m; reflexivity).
    assert (Ess : sSecondA s2m = ldDevSl (loadCmdOf q) rpv (sSecondA s2)) by (rewrite Es2m; reflexivity).
    assert (Ers : sRfA s2m = ldDevRfA m2 (loadCmdOf q) rpv rf1) by (rewrite Es2m; reflexivity).
    destruct Hok as [Hmr' [Hdi [Hlc [Hfv [Hsn [Hcs [Hpm [HPorts [Hex Hky]]]]]]]]].
    assert (Hmr1 : iRegionsA s1' = mr') by (rewrite E1; reflexivity).
    assert (HK : KEPT s1 s1') by (split; unfold iRev; rewrite Hmr1, Hmr; [exact Hex | exact Hky]).
    assert (HP : forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P; rewrite Hmr1, Hmr; apply HPorts).
    pose proof (TraceFrameS_readFrame specRegions _ _ Hm2) as Htf2.
    assert (Hmem : MEMC g1 s1' s2m).
    { rewrite Eg1; unfold MemRelC; cbn [g_revOff]; rewrite Hoff, Hmr1, Ems.
      destruct Hm as [_ [Hdi0 Hsnap0]].
      split; [exact (MemRel_traceFrame pre post revBase revPfB revPfA clintS clint plicS plic ms' m2 mr' Htf2 Hmr') |].
      split; [apply Hdi; rewrite <- Hmr; exact Hdi0 |].
      apply (SnapshotOK_traceFrame specRegions fwcs _ _ Htf2), Hsn.
      exact (SnapshotOK_traceFrame specRegions fwcs _ _ Htf Hsnap0). }
    assert (HPQ : PQ s1') by (unfold PortsQuiet; rewrite HP; exact Hq).
    assert (Hlc2 : forall L, lineContent initLine specRegions (sMemA s2m) L = lineContent initLine specRegions (sMemA s2) L).
    { intros L; rewrite Ems, (lineContent_readFrame initLine specRegions _ _ Hm2 L), Hlc.
      exact (lineContent_traceFrame initLine specRegions _ _ Htf L). }
    destruct (dmLoadRp_excl _ Hdlr) as [Hx1 [Hx2 Hx3]].
    assert (Hdst : (ldPending (loadCmdOf q)).(Fst) = aluDstIdx (ge_aluOut e)).
    { rewrite (loadCmdOf_dst q Hld).
      destruct (entryReq_some e q Hq') as [_ Eq]; rewrite Eq; reflexivity. }
    assert (Havoid : ChainAvoids G' (aluDstIdx (ge_aluOut e))).
    { apply (R4 [] e G' Hch); unfold entryIsLoad; rewrite Hq'; exact Hld. }
    assert (Edm1 : iDmStA s1' = iDmStA s1) by (rewrite E1; reflexivity).
    assert (Hne : RELNE g1 s1' s2m).
    { apply (devNEA g g1 s1 s1' s2 s2m _ [GInst e] m1 E1 HP Htf).
      - rewrite Ems; exact (FetchViewExt_trans specRegions _ _ _ Hfv (FetchViewExt_traceFrame specRegions _ _ Htf2)).
      - rewrite Eg1; exact Hch.
      - rewrite Eg1; eapply GChainInst; [exact Hstep | apply GChainNil].
      - rewrite Eg1; exact Hgc.
      - intros e0 [He0 | []]; injection He0 as <-; unfold entryIsFenceI; rewrite Hq'; exact (opLoad_notFenceI _ Hld).
      - rewrite Eg1; reflexivity.
      - rewrite Eg1, Ers; apply ldDevRf_cnwb.
      - rewrite Eg1; cbn [g_cnwb g_chain]; intros d v Hcn'.
        rewrite (ldDevCnwb_dst _ _ _ _ _ Hcn'), Hdst; exact Havoid.
      - exact Hmem.
      - unfold sClint; rewrite Ems; intros H0; unfold specClintState in *.
        rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf2) in H0 by exact I.
        apply Hcs in H0.
        rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) in H0 by exact I; exact H0.
      - unfold sPlic; rewrite Ems; intros H0; unfold specPlicState in *.
        rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf2) in H0 by exact I.
        apply Hpm in H0.
        rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) in H0 by exact I; exact H0.
      - rewrite Eg1; unfold AccessRel; cbn [g_acc g_revOff g_cnwb]; unfold RdStageRel; cbv beta iota zeta.
        destruct (keptObsA s1 s1' HK) as [Eph _].
        unfold revNotReading in Hrnr |- *.
        assert (Emst : iMemStA s1' = st') by (rewrite E1; reflexivity).
        assert (Erp1 : iReadRpA s1' = (rpv ,, (true ,, tt))) by (rewrite E1; reflexivity).
        assert (Erdy1 : optValid (iRpReadyA s1') = false)
          by (rewrite E1; unfold iRpReady in Hrdy0 |- *; rewrite EM in Hrdy0; exact Hrdy0).
        assert (Erq1 : iRequesterA s1' = iRequesterA s1) by (rewrite E1; unfold iRequester; rewrite EM; reflexivity).
        rewrite Emst, Erp1, Erq1, Edm1, Eph, Ems, Ess.
        refine (conj (conj (conj Hsent1 HsV1) (conj eq_refl (conj Erdy1 HPQ)))
                  (conj Hreq (conj Hdlr (conj Hdlv (conj Hrnr (conj Hoff (conj Hpk _))))))).
        unfold ldDevSl, ldDevCnwb.
        destruct (crossesB (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q))));
          [split; reflexivity | split; [exact Hsec | reflexivity]].
      - rewrite Eg1; unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        rewrite Edm1, Hx1, Hx2.
        split; [intros H; discriminate H |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        split; [intros _ _ _; rewrite Hdlv, Hdst; exact Havoid |]. cnwb_fin.
      - rewrite Eg1; unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc accTakesHead]; cbv zeta in Hd |- *.
        rewrite Eacc, Hch in Hd; cbn [accTakesHead] in Hd.
        rewrite (chainReqs_load_head e q G' Hq' Hld) in Hd.
        rewrite E1; exact Hd.
      - apply (revDevA g g1 s1 s1' s2 s2m HK Hlc2); [| exact Hrk].
        rewrite Eg1; unfold RevAccRel; exact I.
      - apply NEofG; exact Hg. }
    assert (Hlen : (length (g_chain pcAddrInit g1) <= length G')%nat) by (rewrite Eg1; apply le_n).
    destruct (eagerA (length G') g1 s1' s2m Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction; [apply In_specStep_spec | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  (* The second line of a crossing load, from a device or unmapped: the spec performs it *)
  Lemma loadDevCommit_second :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mrdy mr' st' mrp' env ld pkt0 res,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (st' ,, (mrq ,, (mrp' ,, (mrdy ,, tt))))) ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdPend true) ->
      lineKind implRegions (lineOf true (ldAddr ld)) <> Some true ->
      SemAction env (@implRegionsLineReadRq type implRegions (rdLineOf true (ldAddr ld))
                       (rdMaskOf true (ldAddr ld) (plSize (ldPending ld)))) mr mr' res ->
      (res.(Fst) = true -> msReadRqSent st' = true /\
                           msReadRqSentV st' = (crossesB (ldAddr ld) (plSize (ldPending ld)) ,,
                                                (stepOf true (ldAddr ld) (plSize (ldPending ld)) pkt0 ,, tt)) /\
                           mrp' = (if optValid res.(Snd).(Fst) then res.(Snd).(Fst) else mrp)) ->
      RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' env ld pkt0 res EM E1 Eacc Hk Hreg Hrt Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrq [_ [Hrp0 [Hrdy0 Hq]]]] [Hreq [Hdlr [Hdlv [Hrnr [Hoff [Hcr [Hcn Hsec]]]]]]]].
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    assert (Hmem0 : MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq (sMemA s2) mr).
    { destruct Hm as [Hm0 _]; rewrite <- Hoff, <- Hmr; exact Hm0. }
    destruct (specSecondLine_load_dev pcAddrInit config pre post revBase revPfB revPfA clintS clint plicS plic initLine fwcs
                Hdisj HclintIdx HplicIdx HrevTab (sRfA s2) (sMemA s2) ld pkt0 env mr mr' res Hmem0 Hk Hreg)
      as [rpv [ms' [m2 [Eres [Hok [Hm2 Hsp]]]]]].
    subst res; destruct (Hrt eq_refl) as [Hsent1 [HsV1 Emp]].
    assert (Emp' : mrp' = (rpv ,, (true ,, tt))) by (rewrite Emp; reflexivity).
    clear Emp; subst mrp'.
    rewrite <- Hsec, mkSys_eta in Hsp.
    remember (mkSysA (cnwbApply pcAddrInit (Some (specLoadWbA m2 (ldPending ld) (mergedLoadVal ld pkt0 rpv))) (sRfA s2)) m2
                (getDefault (Option SecondLine))) as s2m eqn:Es2m in Hsp.
    remember (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g)
                (Some (specLoadWbA m2 (ldPending ld) (mergedLoadVal ld pkt0 rpv)))
                (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccLoad ld pkt0 (RdArrived true rpv))) as g1 eqn:Eg1.
    assert (Ems : sMemA s2m = m2) by (rewrite Es2m; reflexivity).
    assert (Ess : sSecondA s2m = getDefault (Option SecondLine)) by (rewrite Es2m; reflexivity).
    assert (Ers : sRfA s2m = cnwbApply pcAddrInit (Some (specLoadWbA m2 (ldPending ld) (mergedLoadVal ld pkt0 rpv))) (sRfA s2))
      by (rewrite Es2m; reflexivity).
    destruct Hok as [Hmr' [Hdi [Hlc [Hfv [Hsn [Hcs [Hpm [HPorts [Hex Hky]]]]]]]]].
    assert (Hmr1 : iRegionsA s1' = mr') by (rewrite E1; reflexivity).
    assert (HK : KEPT s1 s1') by (split; unfold iRev; rewrite Hmr1, Hmr; [exact Hex | exact Hky]).
    assert (HP : forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P; rewrite Hmr1, Hmr; apply HPorts).
    pose proof (TraceFrameS_readFrame specRegions _ _ Hm2) as Htf2.
    assert (Hmem : MEMC g1 s1' s2m).
    { rewrite Eg1; unfold MemRelC; cbn [g_revOff]; rewrite Hoff, Hmr1, Ems.
      destruct Hm as [_ [Hdi0 Hsnap0]].
      split; [exact (MemRel_traceFrame pre post revBase revPfB revPfA clintS clint plicS plic ms' m2 mr' Htf2 Hmr') |].
      split; [apply Hdi; rewrite <- Hmr; exact Hdi0 |].
      apply (SnapshotOK_traceFrame specRegions fwcs _ _ Htf2), Hsn; exact Hsnap0. }
    assert (HPQ : PQ s1') by (unfold PortsQuiet; rewrite HP; exact Hq).
    assert (Hlc2 : forall L, lineContent initLine specRegions (sMemA s2m) L = lineContent initLine specRegions (sMemA s2) L).
    { intros L; rewrite Ems, (lineContent_readFrame initLine specRegions _ _ Hm2 L); apply Hlc. }
    destruct (dmLoadRp_excl _ Hdlr) as [Hx1 [Hx2 Hx3]].
    assert (Havoid : ChainAvoids (g_chain pcAddrInit g) (ldPending ld).(Fst)).
    { destruct Hc as [_ [_ [_ C4]]]; rewrite <- Hdlv; apply C4; [exact Hdlr | exact Hcn | rewrite Eacc; reflexivity]. }
    assert (Edm1 : iDmStA s1' = iDmStA s1) by (rewrite E1; reflexivity).
    assert (Hne : RELNE g1 s1' s2m).
    { apply (devNEA g g1 s1 s1' s2 s2m _ [] (sMemA s2) E1 HP (TraceFrameS_refl specRegions (sMemA s2))).
      - rewrite Ems; exact (FetchViewExt_trans specRegions _ _ _ Hfv (FetchViewExt_traceFrame specRegions _ _ Htf2)).
      - rewrite Eg1; reflexivity.
      - rewrite Eg1; apply GChainNil.
      - rewrite Eg1; exact R2.
      - intros e0 [].
      - rewrite Eg1; reflexivity.
      - rewrite Eg1, Ers, R1; reflexivity.
      - rewrite Eg1; cbn [g_cnwb g_chain]; intros d v Hcn'.
        apply some_eq_fst in Hcn'; cbn [fst] in Hcn'.
        assert (Ed : d = (ldPending ld).(Fst)) by (rewrite <- Hcn'; apply fst_specLoadWb).
        rewrite Ed; exact Havoid.
      - exact Hmem.
      - unfold sClint; rewrite Ems; intros H0; unfold specClintState in *.
        rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf2) in H0 by exact I; exact (Hcs H0).
      - unfold sPlic; rewrite Ems; intros H0; unfold specPlicState in *.
        rewrite (regionStateAt_traceFrame specRegions _ _ _ _ _ Htf2) in H0 by exact I; exact (Hpm H0).
      - rewrite Eg1; unfold AccessRel; cbn [g_acc g_revOff g_cnwb]; unfold RdStageRel; cbv beta iota zeta.
        destruct (keptObsA s1 s1' HK) as [Eph _].
        unfold revNotReading in Hrnr |- *.
        assert (Emst : iMemStA s1' = st') by (rewrite E1; reflexivity).
        assert (Erp1 : iReadRpA s1' = (rpv ,, (true ,, tt))) by (rewrite E1; reflexivity).
        assert (Erdy1 : optValid (iRpReadyA s1') = false)
          by (rewrite E1; unfold iRpReady in Hrdy0 |- *; rewrite EM in Hrdy0; exact Hrdy0).
        assert (Erq1 : iRequesterA s1' = iRequesterA s1) by (rewrite E1; unfold iRequester; rewrite EM; reflexivity).
        rewrite Emst, Erp1, Erq1, Edm1, Eph, Ems, Ess.
        exact (conj (conj (conj Hsent1 HsV1) (conj eq_refl (conj Erdy1 HPQ)))
                 (conj Hreq (conj Hdlr (conj Hdlv (conj Hrnr (conj Hoff (conj Hcr (conj eq_refl eq_refl)))))))).
      - rewrite Eg1; unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        rewrite Edm1, Hx1, Hx2.
        split; [intros H; discriminate H |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        split; [intros _ H; discriminate H |]. cnwb_fin.
      - rewrite Eg1; unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc]; cbv zeta in Hd |- *.
        rewrite Eacc in Hd; cbn [accTakesHead] in Hd |- *.
        rewrite E1; exact Hd.
      - apply (revDevA g g1 s1 s1' s2 s2m HK Hlc2); [| exact Hrk].
        rewrite Eg1; unfold RevAccRel; exact I.
      - apply NEofG; exact Hg. }
    assert (Hlen : (length (g_chain pcAddrInit g1) <= length (g_chain pcAddrInit g))%nat) by (rewrite Eg1; apply le_n).
    destruct (eagerA (length (g_chain pcAddrInit g)) g1 s1' s2m Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction;
        [apply (In_specSecondLine_spec pcAddrInit config pre post revBase revPfB revPfA clintS plicS) | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  (* --- 4. A CustomMem or Unmapped Line: the Revoker's Cap Read (RefRevCapDev.v) --- *)

  Local Abbreviation revCapDevA := (revCapDev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                      clintS clint plicS plic initLine fwcs Hdisj HclintIdx HplicIdx).

  (* --- 5. The Step --- *)

  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                   clintS clint plicS plic initLine fwcs).

  Theorem stepOK_readRqStep :
    STEPOK (@readRqStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold readRqStep in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    change (readSubTreeState NPMI s1) with (iMemA s1) in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp [mrdy []]]]]].
    destruct (msReadRqV mst) as [b [[addr [size [pkt []]]] []]] eqn:Ev.
    destruct (readRqStep_char pre post revBase revPfB revPfA _ mr mst mrq mrp mrdy m' _ b addr size pkt Ev Hm')
      as [-> | [Hr [Hv [mr' [res [st' [mrp' [Hreg [-> [Hrf Hrt]]]]]]]]]].
    { exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM]. }
    pose proof Hg as Hg0; destruct Hg0 as [Hrf0 Hm Hl Hrp He Ha Hc Hd Hfe Hs Hfr Hwf Hrk].
    assert (Hmst : iMemStA s1 = mst) by (unfold iMemSt; rewrite EM; reflexivity).
    assert (Hr1 : msReadRq (iMemStA s1) = true) by (rewrite Hmst; exact Hr).
    destruct (AccessRel_readRq g s1 s2 Ha Hr1) as [[ld [pkt0 [b' Eacc]]] | [[rc Eacc] | [Eacc | Eacc]]].
    - (* a load line *)
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'.
      destruct Ha' as [Hrds _].
      pose proof Hrds as Hrds0; unfold RdStageRel in Hrds0; destruct Hrds0 as [_ [HrV [_ [_ Hq]]]].
      rewrite Hmst, Ev in HrV.
      destruct (stepOf_inj _ _ _ _ _ _ _ _ HrV) as [Eb [Ea [Es Ep]]]; subst b addr size pkt.
      destruct (lineKind implRegions (lineOf b' (ldAddr ld))) as [[|] |] eqn:Hk.
      + (* ExternalMem: staged *)
        destruct (readStage_facts s1 s1' mr mst mrq mrp mrdy mr' st' mrp' _ b' (ldAddr ld) (plSize (ldPending ld)) pkt0 res
                    EM E1 Hk Hq Hreg Hrt) as [Hst [Emst [Hs1 [HsV1 [Erp [Erdy [Hp [Erq [Edm HR]]]]]]]]].
        exists s2; split; [apply NilAction; reflexivity |].
        set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                  (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccLoad ld pkt0 (RdStaged b'))).
        exists g'.
        apply (stageA g g' s1 s1' s2 _ _ _ E1 Hst eq_refl eq_refl eq_refl eq_refl eq_refl); [| | | exact Hg].
        * cbn [g_acc accTakesHead]; rewrite Eacc; destruct b'; reflexivity.
        * apply (acc_stageLoad g g' s1 s1' s2 ld pkt0 b' Eacc eq_refl eq_refl eq_refl eq_refl);
            [| exact Erq | exact Edm | exact HR | exact Ha].
          exact (rds_staged _ _ _ b' s1 s1' st' Hrds Emst Hs1 HsV1 Erp Erdy Hk Hp).
        * unfold RevAccRel; exact I.
      + (* CustomMem: the device read commits the load line *)
        assert (Hk2 : lineKind implRegions (lineOf b' (ldAddr ld)) <> Some true) by (rewrite Hk; discriminate).
        destruct b'.
        * exact (loadDevCommit_second g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' _ ld pkt0 res EM E1 Eacc Hk2 Hreg Hrt Hg).
        * exact (loadDevCommit_first g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' _ ld pkt0 res EM E1 Eacc Hk2 Hreg Hrt Hg).
      + (* unmapped: zeros commit the load line *)
        assert (Hk2 : lineKind implRegions (lineOf b' (ldAddr ld)) <> Some true) by (rewrite Hk; discriminate).
        destruct b'.
        * exact (loadDevCommit_second g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' _ ld pkt0 res EM E1 Eacc Hk2 Hreg Hrt Hg).
        * exact (loadDevCommit_first g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' _ ld pkt0 res EM E1 Eacc Hk2 Hreg Hrt Hg).
    - (* dataMem's rev byte read: an ExternalMem line *)
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'.
      destruct Ha' as [Hrds [_ [_ [_ [_ [_ [_ [_ [_ [Hbr _]]]]]]]]]].
      pose proof Hrds as Hrds0; unfold RdStageRel in Hrds0; destruct Hrds0 as [_ [HrV [_ [_ Hq]]]].
      rewrite Hmst, Ev in HrV.
      destruct (stepOf_inj _ _ _ _ _ _ _ _ HrV) as [Eb [Ea [Es Ep]]]; subst b addr size pkt.
      assert (Hk : lineKind implRegions (lineOf false (revByteAddrOf config (rcBase rc))) = Some true).
      { rewrite <- lineKind_revSwap; exact (revByte_line config pre post revBase revPfB revPfA Hdisj HrevTab _ Hbr). }
      destruct (readStage_facts s1 s1' mr mst mrq mrp mrdy mr' st' mrp' _ false (revByteAddrOf config (rcBase rc)) byteSz
                  (getDefault CapPacket) res EM E1 Hk Hq Hreg Hrt) as [Hst [Emst [Hs1 [HsV1 [Erp [Erdy [Hp [Erq [Edm HR]]]]]]]]].
      exists s2; split; [apply NilAction; reflexivity |].
      set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccDmRev rc (RdStaged false))).
      exists g'.
      apply (stageA g g' s1 s1' s2 _ _ _ E1 Hst eq_refl eq_refl eq_refl eq_refl eq_refl); [| | | exact Hg].
      + cbn [g_acc accTakesHead]; rewrite Eacc; reflexivity.
      + apply (acc_stageDmRev g g' s1 s1' s2 rc Eacc eq_refl eq_refl eq_refl); [| exact Erq | exact Edm | exact HR | exact Ha].
        exact (rds_staged _ _ _ false s1 s1' st' Hrds Emst Hs1 HsV1 Erp Erdy Hk Hp).
      + unfold RevAccRel; exact I.
    - (* the revoker's cap read *)
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'.
      destruct Ha' as [Hrds _].
      pose proof Hrds as Hrds0; unfold RdStageRel in Hrds0; destruct Hrds0 as [_ [HrV [_ [_ Hq]]]].
      rewrite Hmst, Ev in HrV.
      destruct (stepOf_inj _ _ _ _ _ _ _ _ HrV) as [Eb [Ea [Es Ep]]]; subst b addr size pkt.
      destruct (lineKind implRegions (lineOf false (iScanAddrA s1))) as [[|] |] eqn:Hk.
      + (* ExternalMem: staged *)
        destruct (readStage_facts s1 s1' mr mst mrq mrp mrdy mr' st' mrp' _ false (iScanAddrA s1) capSz
                    (getDefault CapPacket) res EM E1 Hk Hq Hreg Hrt) as [Hst [Emst [Hs1 [HsV1 [Erp [Erdy [Hp [Erq [Edm HR]]]]]]]]].
        exists s2; split; [apply NilAction; reflexivity |].
        set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                  (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccRevCap (RdStaged false))).
        exists g'.
        apply (stageA g g' s1 s1' s2 _ _ _ E1 Hst eq_refl eq_refl eq_refl eq_refl eq_refl); [| | | exact Hg].
        * cbn [g_acc accTakesHead]; rewrite Eacc; reflexivity.
        * apply (acc_stageRevCap g g' s1 s1' s2 Eacc eq_refl eq_refl HR); [| exact Erq | exact Edm | exact Ha].
          exact (rds_staged _ _ _ false s1 s1' st' Hrds Emst Hs1 HsV1 Erp Erdy Hk Hp).
        * unfold RevAccRel; exact I.
      + assert (Hk2 : lineKind implRegions (lineOf false (iScanAddrA s1)) <> Some true) by (rewrite Hk; discriminate).
        exact (revCapDevA g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' _ res EM E1 Eacc Hk2 Hreg Hrt Hg).
      + assert (Hk2 : lineKind implRegions (lineOf false (iScanAddrA s1)) <> Some true) by (rewrite Hk; discriminate).
        exact (revCapDevA g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' _ res EM E1 Eacc Hk2 Hreg Hrt Hg).
    - (* the revoker's rev bit read: an ExternalMem line *)
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'.
      destruct Ha' as [Hrds [_ [Hwr _]]].
      pose proof Hrds as Hrds0; unfold RdStageRel in Hrds0; destruct Hrds0 as [_ [HrV [_ [_ Hq]]]].
      rewrite Hmst, Ev in HrV.
      destruct (stepOf_inj _ _ _ _ _ _ _ _ HrV) as [Eb [Ea [Es Ep]]]; subst b addr size pkt.
      pose proof Hrk as Hrk0; unfold RevokerRel in Hrk0; destruct Hrk0 as [_ [K2 _]].
      destruct (K2 (rpCheck_waitRevBitRp _ Hwr)) as [Hnc [Ebase _]].
      assert (Hk : lineKind implRegions (lineOf false (revByteAddrOf config (iRevScanBaseA s1))) = Some true).
      { rewrite <- lineKind_revSwap, Ebase; exact (revTab_needsCheck config pre post revBase revPfB revPfA Hdisj HrevTab _ Hnc). }
      destruct (readStage_facts s1 s1' mr mst mrq mrp mrdy mr' st' mrp' _ false (revByteAddrOf config (iRevScanBaseA s1)) byteSz
                  (getDefault CapPacket) res EM E1 Hk Hq Hreg Hrt) as [Hst [Emst [Hs1 [HsV1 [Erp [Erdy [Hp [Erq [Edm HR]]]]]]]]].
      exists s2; split; [apply NilAction; reflexivity |].
      set (g' := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccRevBit (RdStaged false))).
      exists g'.
      apply (stageA g g' s1 s1' s2 _ _ _ E1 Hst eq_refl eq_refl eq_refl eq_refl eq_refl); [| | | exact Hg].
      + cbn [g_acc accTakesHead]; rewrite Eacc; reflexivity.
      + apply (acc_stageRevBit g g' s1 s1' s2 Eacc eq_refl eq_refl HR); [| exact Erq | exact Edm | exact Ha].
        exact (rds_staged _ _ _ false s1 s1' st' Hrds Emst Hs1 HsV1 Erp Erdy Hk Hp).
      + unfold RevAccRel; exact I.
  Qed.
End ReadRqStep.
