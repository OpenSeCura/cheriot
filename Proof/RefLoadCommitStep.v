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
From Cheriot.Proof Require Import RefReadRpPorts RefRevokerStep RefExecAppend RefLoadCommit.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the commit of a load line (`readRpPorts` at `AccLoad .. (RdOut b)`): the response
 * enters `readRp`, and the spec performs the line.
 * 1. `RefRelNE_commit`: the relation after a data response step of the impl and a spec step that
 *    only reads memory and replays a prefix of the chain (the facts that change are premises).
 * 2. The first line (`b = false`): `specStep` of the head entry (`specStep_load`).
 * 3. The second line of a crossing load (`b = true`): `specSecondLine` (`specSecondLine_load`).
 * 4. `stepOK_readRpPorts`. *)

(* --- 1. The Relation after a Commit --- *)

Lemma app_cons_split :
  forall {A : Type} (G0 C G1 G2 : list A) x,
    (G0 ++ C = G1 ++ x :: G2)%list -> ~ In x G0 -> exists G1', G1 = (G0 ++ G1')%list /\ C = (G1' ++ x :: G2)%list.
Proof.
  intros A G0; induction G0 as [| y G0 IH]; intros C G1 G2 x E Hn.
  - exists G1; split; [reflexivity | exact E].
  - destruct G1 as [| z G1]; cbn [app] in E; injection E as E1 E2.
    + exfalso; apply Hn; left; exact E1.
    + destruct (IH C G1 G2 x E2 (fun H => Hn (or_intror H))) as [G1' [-> ->]].
      exists G1'; split; [rewrite E1; reflexivity | reflexivity].
Qed.

Section LoadCommit.
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

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation NPMI := (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA := (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation ACC := (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation CNWB := (CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation DMQ := (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RACC := (RevAccRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation RELNE := (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).

  (* A step of the impl memory subtree that keeps every port observation but the data responses
   * (`AllPorts_dataRpStep`), together with a spec step that only reads memory and replays the
   * chain prefix `G0` (no fence.i in it). The facts about the access, the committed load, the
   * memory and dataMem's queue are the caller's. *)
  Lemma RefRelNE_commit :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mi' G0,
      s1' = writeSubTreeState NPMI s1 mi' ->
      (forall P, (forall r y rp z, P r (dataRpTaken r y rp z) = P r y) -> (forall r y, P r (dataRpNone r y) = P r y) ->
                 AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)) ->
      iRevA s1' = iRevA s1 ->
      TraceFrameS specRegions (sMemA s2) (sMemA s2') ->
      g_chain pcAddrInit g = (G0 ++ g_chain pcAddrInit g')%list ->
      GChain pcAddrInit (g_rf0 pcAddrInit g) G0 (g_rf0 pcAddrInit g') ->
      GChain pcAddrInit (g_rf0 pcAddrInit g') (g_chain pcAddrInit g') (iFlushA s1) ->
      (forall e, In (GInst e) G0 -> entryIsFenceI e = false) ->
      g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g -> g_revOff pcAddrInit g' = g_revOff pcAddrInit g ->
      sRfA s2' = cnwbApply pcAddrInit (g_cnwb pcAddrInit g') (g_rf0 pcAddrInit g') ->
      (forall d v, g_cnwb pcAddrInit g' = Some (d, v) -> ChainAvoids (g_chain pcAddrInit g') d) ->
      MEMC g' s1' s2' -> ACC g' s1' s2' -> CNWB g' s1' s2' -> DMQ g' s1' -> RACC g' s1' s2' ->
      AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1') ->
      RELNE g s1 s2 -> RELNE g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mi' G0 E1 HP HR Htf Ech Hg0 Hgc Hfi Ed2a Eoff Erf Hav Hmem Hacc Hcn Hdq Hra Hhs H.
    destruct H as [Hrf Hm Hl Hrp Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    pose proof (FetchViewExt_traceFrame specRegions _ _ Htf) as Hext.
    pose proof (lineContent_traceFrame initLine specRegions _ _ Htf) as Hlc.
    constructor.
    - unfold RfRel in *.
      destruct Hrf as [R1 [R2 [R3 R4]]]; rewrite Ech in R4.
      split; [exact Erf |]; split; [rewrite E1; exact Hgc |]; split; [exact Hav |].
      intros G1 e G2 HG Hld; apply (R4 (G0 ++ G1)%list e G2); [rewrite HG, app_assoc; reflexivity | exact Hld].
    - exact Hmem.
    - unfold LatchRel in *.
      unfold sClint, sPlic in *.
      intros e Hin.
      erewrite specClintState_traceFrame; [| exact Htf].
      erewrite specPlicState_traceFrame; [| exact Htf].
      apply Hl; rewrite Ech; apply in_or_app; right; exact Hin.
    - unfold ReplayRel in *.
      intros G1 e G2 rfe HG Hc1.
      apply (FetchAllowedInst_fetchViewExt initLine fwcs specRegions (sMemA s2) (sMemA s2') _ _ Hsnap Hext).
      apply (Hrp (G0 ++ G1)%list e G2 rfe); [rewrite Ech, HG, app_assoc; reflexivity |].
      exact (GChain_app pcAddrInit _ _ _ _ _ Hg0 Hc1).
    - exact Hacc.
    - exact Hcn.
    - exact Hdq.
    - unfold FenceRel, NoFenceIWait in *.
      rewrite HP by (intros; reflexivity).
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
    - subst s1'.
      unfold FrontRel in *; destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [exact F1 |]; split; [exact F2 |]; split; [exact F3 |].
      split; [exact F4 |]; split; [exact F5 |].
      split.
      + unfold LiveChain, liveInsts in *; rewrite Ed2a.
        eapply LiveChainG_mono; [exact Hsnap | exact Hext | | exact F6].
        intros p Hp; exact (FrontierRel_mono pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                              initLine fwcs _ s2 s2' p Hsnap Hext Hp).
      + unfold FetchRespRel in *.
        rewrite HP by (intros; reflexivity).
        refine (AllPorts_impl _ _ implRegions _ _ F7).
        intros r y HPr; cbv beta zeta in HPr |- *.
        destruct HPr as [C [HC1 [HC2 HC3]]]; exists C; split; [exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hla]]]; exists f, E'; split; [exact HE |].
        intros Hlv; exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hla Hlv)).
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd _]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 | split; [rewrite E1; exact Wmd | exact Hhs]].
    - pose proof (RevokerRel_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    initLine g g s1 s1' s2 s2' eq_refl eq_refl HR Hlc Hrk) as Hrk'.
      unfold RevokerRel in *; destruct Hrk' as [K1 [K2 [K3 [K4 _]]]].
      exact (conj K1 (conj K2 (conj K3 (conj K4 Hra)))).
  Qed.

  (* --- 2. The First Line of a Load --- *)

  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL := (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               clintS clint plicS plic initLine fwcs).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation specLoadWbA := (specLoadWb config pre post revBase revPfB revPfA initLine).
  Local Abbreviation ldRp0A := (ldRp0 pre post revBase revPfB revPfA initLine).

  Local Abbreviation NEofG := (RefRelNE_of_G pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).
  Local Abbreviation eagerA := (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs Hdisj).
  Local Abbreviation takenA := (taken_impl pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  initLine fwcs Hdisj).
  Local Abbreviation rpContentA := (rp_spec_content pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                      clintS clint plicS plic initLine fwcs Hdisj).
  Local Abbreviation memDataRpA := (MemRelC_dataRpStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                      clintS clint plicS plic initLine fwcs).
  Local Abbreviation handshakeA := (handshake_s1' pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                      clintS clint plicS plic initLine fwcs).
  Local Abbreviation memTraceA := (MemRelC_traceFrame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                     clintS clint plicS plic fwcs).

  (* The committed load of the first line (`None` while the second line is pending) *)
  Definition ldCommitCnwb (m : TS (specMemTree specRegions)) (ld : type LoadCmd)
    : option (bits RegIdxSzReal * type FullECapWithTag) :=
    if crossesB (ldAddr ld) (plSize (ldPending ld)) then None
    else Some (specLoadWbA m (ldPending ld) (singleLoadVal ld (ldRp0A m ld))).

  Lemma ldCommitRf_cnwb :
    forall m ld rf1,
      ldCommitRf pcAddrInit config pre post revBase revPfB revPfA initLine m ld rf1 =
      cnwbApply pcAddrInit (ldCommitCnwb m ld) rf1.
  Proof.
    intros m ld rf1; unfold ldCommitRf, ldCommitCnwb.
    destruct (crossesB (ldAddr ld) (plSize (ldPending ld))); reflexivity.
  Qed.

  (* The committed load writes the load's destination *)
  Lemma ldCommitCnwb_dst :
    forall m ld d v, ldCommitCnwb m ld = Some (d, v) -> d = (ldPending ld).(Fst).
  Proof.
    intros m ld d v; unfold ldCommitCnwb.
    destruct (crossesB (ldAddr ld) (plSize (ldPending ld))); intros H; [discriminate H |].
    apply some_eq_fst in H; cbn [fst] in H.
    rewrite <- H; apply fst_specLoadWb.
  Qed.

  Lemma opLoad_notFenceI : forall op, opIsLoad op = true -> opIsFenceI op = false.
  Proof.
    intros op H; unfold opIsLoad, opIsFenceI in *; apply andb_prop in H as [Hm _]; rewrite Hm; reflexivity.
  Qed.

  Lemma opLoad_isMem : forall op, opIsLoad op = true -> opIsMem op = true.
  Proof. intros op H; unfold opIsLoad in H; apply andb_prop in H as [Hm _]; exact Hm. Qed.

  (* dataMem's queue after the head load left the chain and its access no longer takes the head *)
  Lemma chainReqs_load_head :
    forall e q G', entryReq e = Some q -> opIsLoad (mrOp q) = true ->
      tl (filter (fun q0 => negb (isPlainFence q0)) (chainReqs (GInst e :: G'))) =
      filter (fun q0 => negb (isPlainFence q0)) (chainReqs G').
  Proof.
    intros e q G' Hq Hld.
    unfold chainReqs; cbn [flat_map]; rewrite Hq; cbn [app filter].
    unfold isPlainFence; rewrite (opLoad_isMem _ Hld); reflexivity.
  Qed.

  (* The first line of a load arrives: the spec steps the head entry (its first line is read; a
   * crossing load records the rest, any other completes), then replays eagerly *)
  Lemma loadCommit_first :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o ld pkt0,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdOut false) -> RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' o ld pkt0 EM E1 Hst Hv Eacc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hsent [_ [Hlk Hout]]] [Hreq [Hdlr [Hdlv [Hrnr [Hoff [Hsec [Hpk [Hcn Hhq]]]]]]]]].
    destruct Hhq as [q [[e [G' [Hch Hq]]] [Hld Eld]]].
    destruct (takenA s1 s1' mr mst mrq mrp mr' o _ EM E1 Hst Hv Hout) as [ER [Est [Ereq [Edm [Erp' HPQ]]]]].
    pose proof (rpContentA g s1 s2 mr' o _ Hm Hout Hst Hv) as Hcont.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    rewrite Hch in R2.
    destruct (GChain_cons_inv pcAddrInit _ _ _ _ R2) as [rf1 [Hstep Hgc]]; cbn [ItemStep] in Hstep.
    assert (Hin : In (GInst e) (g_chain pcAddrInit g)) by (rewrite Hch; left; reflexivity).
    (* the spec waits for no fence.i ack: an entry is pending *)
    assert (HdecW : forall r (y : TS (implExternalMemRegionTree r)),
               y.(Fst).(Fst).(Snd).(Snd).(Fst) = false \/ ~ y.(Fst).(Fst).(Snd).(Snd).(Fst) = false)
      by (intros r y; destruct (y.(Fst).(Fst).(Snd).(Snd).(Fst)); [right; discriminate | left; reflexivity]).
    destruct (AllPorts_dec (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) HdecW implRegions (iRegionsA s1))
      as [Hnw | Hnw].
    2: { exfalso; unfold FenceRel, NoFenceIWait in Hf; destruct Hf as [_ [Hf2 _]].
         destruct (Hf2 Hnw) as [_ [_ [_ Hno]]]; exact (Hno e Hin). }
    assert (Hsnw : SpecNoWait specRegions (sMemA s2)).
    { unfold MemRelC, MemRel in Hm; destruct Hm as [[Hpre _] _].
      eapply noWait_pre; [exact I | exact Hpre | exact Hnw]. }
    assert (Hlk' : lineKind specRegions (lineOf false (ldAddr (loadCmdOf q))) = Some true)
      by (rewrite Eld, lineKind_revSwap; exact Hlk).
    destruct (specStep_load pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwcs Hdisj HrevTab
                (g_rf0 pcAddrInit g) rf1 (sMemA s2) (sSecondA s2) e q Hstep Hq Hld Hsnw Hsec
                (Hrp [] e G' (g_rf0 pcAddrInit g) Hch (GChainNil pcAddrInit _))
                (proj1 (Hl e Hin)) (proj2 (Hl e Hin)) Hlk')
      as [m' [Htf Hsp]].
    rewrite Eld in Hsp; rewrite <- R1, mkSys_eta in Hsp.
    set (s2m := mkSysA (ldCommitRf pcAddrInit config pre post revBase revPfB revPfA initLine (sMemA s2) ld rf1) m'
                  (ldCommitSl pre post revBase revPfB revPfA initLine (sMemA s2) ld (sSecondA s2))) in Hsp.
    pose proof (lineContent_traceFrame initLine specRegions (sMemA s2) m' Htf) as Hlc.
    (* the load's destination: no later entry touches it *)
    assert (Hdst : (ldPending ld).(Fst) = aluDstIdx (ge_aluOut e)).
    { pose proof (loadCmdOf_dst q Hld) as Hd0; rewrite Eld in Hd0; rewrite Hd0.
      destruct (entryReq_some e q Hq) as [_ Eq]; rewrite Eq; reflexivity. }
    assert (Havoid : ChainAvoids G' (aluDstIdx (ge_aluOut e))).
    { apply (R4 [] e G' Hch); unfold entryIsLoad; rewrite Hq; exact Hld. }
    set (g1 := mkGhost pcAddrInit G' rf1 (ldCommitCnwb (sMemA s2) ld) (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g)
                 (AccLoad ld pkt0 (RdArrived false (optData o)))).
    assert (Hne : RELNE g1 s1' s2m).
    { apply (RefRelNE_commit g g1 s1 s1' s2 s2m _ [GInst e] E1).
      - intros P HT HN; rewrite E1; exact (AllPorts_dataRpStep initLine P HT HN _ _ _ _ _ Hst).
      - exact ER.
      - exact Htf.
      - exact Hch.
      - eapply GChainInst; [exact Hstep | apply GChainNil].
      - exact Hgc.
      - intros e0 [He0 | []]; injection He0 as <-; unfold entryIsFenceI; rewrite Hq; exact (opLoad_notFenceI _ Hld).
      - reflexivity.
      - reflexivity.
      - unfold s2m; rewrite sRf_mkSys; apply ldCommitRf_cnwb.
      - cbn [g_cnwb g_chain g1]; intros d v Hcn'.
        rewrite (ldCommitCnwb_dst _ _ _ _ Hcn'), Hdst; exact Havoid.
      - exact (memTraceA g1 s1' s2 s2m Htf (memDataRpA g s1 s1' s2 mr' _ o E1 Hst Hm)).
      - unfold AccessRel; cbn [g_acc g_revOff g_cnwb g1]; unfold RdStageRel; cbv beta iota zeta.
        unfold revNotReading, iRevPhase in *; rewrite ER, Est, Ereq, Edm, Erp'.
        unfold s2m; rewrite sSecond_mkSys, sMem_mkSys.
        refine (conj (conj Hsent (conj eq_refl HPQ)) (conj Hreq (conj Hdlr (conj Hdlv (conj Hrnr (conj Hoff (conj Hpk _))))))).
        rewrite Hcont; unfold ldCommitSl, ldCommitCnwb.
        assert (Hdec : crossesB (ldAddr ld) (plSize (ldPending ld)) = true \/ crossesB (ldAddr ld) (plSize (ldPending ld)) = false)
          by (destruct (crossesB (ldAddr ld) (plSize (ldPending ld))); [left | right]; reflexivity).
        destruct Hdec as [Ecr | Ecr]; rewrite !Ecr.
        + split; reflexivity.
        + split; [exact Hsec |].
          rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine (sMemA s2) m' _ _ Hlc); reflexivity.
      - unfold CnwbRel; cbn [g_cnwb g_chain g_acc g1]; rewrite Edm.
        destruct (dmLoadRp_excl _ Hdlr) as [Hq0 [Hr0 _]]; rewrite Hq0, Hr0.
        split; [intros H; discriminate H |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        intros _ _ _; rewrite Hdlv, Hdst; exact Havoid.
      - unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc g1 accTakesHead]; cbv zeta in Hd |- *.
        rewrite Eacc, Hch in Hd; cbn [accTakesHead] in Hd.
        rewrite (chainReqs_load_head e q G' Hq Hld) in Hd.
        rewrite E1; exact Hd.
      - unfold RevAccRel; cbn [g_acc g1]; exact I.
      - exact (handshakeA g s1 s1' s2 mr' _ o E1 Hst Hg).
      - exact (NEofG g s1 s2 Hg). }
    destruct (eagerA (length G') g1 s1' s2m (le_n _) Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction; [apply In_specStep_spec | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  (* --- 3. The Second Line of a Crossing Load --- *)

  Lemma ldMergedWb_dst :
    forall m ld pkt0 d v,
      Some (ldMergedWb config pre post revBase revPfB revPfA initLine m ld pkt0) = Some (d, v) ->
      d = (ldPending ld).(Fst).
  Proof.
    intros m ld pkt0 d v H; apply some_eq_fst in H; cbn [fst] in H.
    rewrite <- H; unfold ldMergedWb; apply fst_specLoadWb.
  Qed.

  (* The second line of a crossing load arrives: the spec performs it (`specSecondLine`), which
   * completes the load, then replays eagerly *)
  Lemma loadCommit_second :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mr' o ld pkt0,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt)))) ->
      DataRpPortStepL initLine fwcs implRegions (iRegionsA s1) mr' o -> optValid o = true ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdOut true) -> RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mr' o ld pkt0 EM E1 Hst Hv Eacc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hsent [_ [Hlk Hout]]] [Hreq [Hdlr [Hdlv [Hrnr [Hoff [Hcr [Hcn Hsec]]]]]]]].
    destruct (takenA s1 s1' mr mst mrq mrp mr' o _ EM E1 Hst Hv Hout) as [ER [Est [Ereq [Edm [Erp' HPQ]]]]].
    pose proof (rpContentA g s1 s2 mr' o _ Hm Hout Hst Hv) as Hcont.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    assert (Hlk' : lineKind specRegions (lineOf true (ldAddr ld)) = Some true)
      by (rewrite lineKind_revSwap; exact Hlk).
    destruct (specSecondLine_load pcAddrInit config pre post revBase revPfB revPfA initLine fwcs Hdisj HrevTab
                (g_rf0 pcAddrInit g) (sMemA s2) ld pkt0 Hlk')
      as [m' [Hrd Hsp]].
    rewrite <- Hsec, <- R1, mkSys_eta in Hsp.
    set (s2m := mkSysA (cnwbApply pcAddrInit (Some (ldMergedWb config pre post revBase revPfB revPfA initLine (sMemA s2) ld pkt0))
                          (sRfA s2)) m' (getDefault (Option SecondLine))) in Hsp.
    pose proof (TraceFrameS_readFrame specRegions _ _ Hrd) as Htf.
    pose proof (lineContent_readFrame initLine specRegions (sMemA s2) m' Hrd) as Hlc.
    (* while the second line was out, the chain avoided the load's destination *)
    assert (Havoid : ChainAvoids (g_chain pcAddrInit g) (ldPending ld).(Fst)).
    { destruct Hc as [_ [_ [_ C4]]]; rewrite <- Hdlv; apply C4; [exact Hdlr | exact Hcn | rewrite Eacc; reflexivity]. }
    set (g1 := mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g)
                 (Some (ldMergedWb config pre post revBase revPfB revPfA initLine (sMemA s2) ld pkt0))
                 (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) (AccLoad ld pkt0 (RdArrived true (optData o)))).
    assert (Hne : RELNE g1 s1' s2m).
    { apply (RefRelNE_commit g g1 s1 s1' s2 s2m _ [] E1).
      - intros P HT HN; rewrite E1; exact (AllPorts_dataRpStep initLine P HT HN _ _ _ _ _ Hst).
      - exact ER.
      - exact Htf.
      - reflexivity.
      - apply GChainNil.
      - exact R2.
      - intros e0 [].
      - reflexivity.
      - reflexivity.
      - unfold s2m; rewrite sRf_mkSys, R1; reflexivity.
      - cbn [g_cnwb g_chain g1]; intros d v Hcn'.
        rewrite (ldMergedWb_dst _ _ _ _ _ Hcn'); exact Havoid.
      - exact (memTraceA g1 s1' s2 s2m Htf (memDataRpA g s1 s1' s2 mr' _ o E1 Hst Hm)).
      - unfold AccessRel; cbn [g_acc g_revOff g_cnwb g1]; unfold RdStageRel; cbv beta iota zeta.
        unfold revNotReading, iRevPhase in *; rewrite ER, Est, Ereq, Edm, Erp'.
        unfold s2m; rewrite sSecond_mkSys, sMem_mkSys.
        refine (conj (conj Hsent (conj eq_refl HPQ))
                  (conj Hreq (conj Hdlr (conj Hdlv (conj Hrnr (conj Hoff (conj Hcr (conj eq_refl _)))))))).
        rewrite Hcont; unfold ldMergedWb.
        rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine (sMemA s2) m' _ _ Hlc); reflexivity.
      - unfold CnwbRel; cbn [g_cnwb g_chain g_acc g1]; rewrite Edm.
        destruct (dmLoadRp_excl _ Hdlr) as [Hq0 [Hr0 _]]; rewrite Hq0, Hr0.
        split; [intros H; discriminate H |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        intros _ H; discriminate H.
      - unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc g1 accTakesHead]; cbv zeta in Hd |- *.
        rewrite Eacc in Hd; cbn [accTakesHead] in Hd.
        rewrite E1; exact Hd.
      - unfold RevAccRel; cbn [g_acc g1]; exact I.
      - exact (handshakeA g s1 s1' s2 mr' _ o E1 Hst Hg).
      - exact (NEofG g s1 s2 Hg). }
    destruct (eagerA (length (g_chain pcAddrInit g)) g1 s1' s2m (le_n _) Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction;
        [apply (In_specSecondLine_spec pcAddrInit config pre post revBase revPfB revPfA clintS plicS) | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  (* --- 4. The Data Response Ports --- *)

  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).

  Theorem stepOK_readRpPorts :
    forall act,
      In act (@readRpPorts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
      STEPOK act.
  Proof.
    apply stepOK_readRpPorts_of with (Hdisj := Hdisj).
    intros g s1 s1' s2 mr mst mrq mrp mr' o ld pkt0 [|] EM E1 Hst Hv Eacc Hg.
    - exact (loadCommit_second g s1 s1' s2 mr mst mrq mrp mr' o ld pkt0 EM E1 Hst Hv Eacc Hg).
    - exact (loadCommit_first g s1 s1' s2 mr mst mrq mrp mr' o ld pkt0 EM E1 Hst Hv Eacc Hg).
  Qed.
End LoadCommit.
