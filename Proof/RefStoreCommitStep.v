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
From Cheriot.Proof Require Import RefReadRpPorts RefRevokerStep RefExecAppend RefLoadCommit RefLoadCommitStep.
From Cheriot.Proof Require Import RefRevBitRule RefWriteRqPorts RefStoreCommit RefSnoopMiss.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

Lemma dmLoadRq_excl :
  forall st : type DataMemState,
    dmLoadRq st = true ->
    dmLoadRp st = false /\ dmRevRq st = false /\ dmRevRp st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma opStore_isMem : forall op, opIsStore op = true -> opIsMem op = true.
Proof. intros op H; unfold opIsStore in H; apply andb_prop in H as [Hm _]; exact Hm. Qed.

Lemma opStore_notFenceI : forall op, opIsStore op = true -> opIsFenceI op = false.
Proof. intros op H; unfold opIsFenceI; rewrite (opStore_isMem _ H); reflexivity. Qed.

(* dataMem's queue after the head store left the chain *)
Lemma chainReqs_store_head :
  forall e q G', entryReq e = Some q -> opIsStore (mrOp q) = true ->
    tl (filter (fun q0 => negb (isPlainFence q0)) (chainReqs (GInst e :: G'))) =
    filter (fun q0 => negb (isPlainFence q0)) (chainReqs G').
Proof.
  intros e q G' Hq Hst.
  unfold chainReqs; cbn [flat_map]; rewrite Hq; cbn [app filter].
  unfold isPlainFence; rewrite (opStore_isMem _ Hst); reflexivity.
Qed.

(* Milestone 4, the commit of a store line to an ExternalMem region (`writeRqPorts`, accepted).
 * 1. `RevokerRel_storeWrite`: the revoker facts survive a core store that misses the snoop (the
 *    snoop-miss lemma) under the rev-bit rule. *)

Section StoreCommit.
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
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation REVK := (RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation RACC := (RevAccRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation memValAtA := (memValAt pre post revBase revPfB revPfA initLine).
  Local Abbreviation revBitOfA := (revBitOf config pre post revBase revPfB revPfA initLine).
  Local Abbreviation SRULE := (SpecRevBitRule pcAddrInit config pre post revBase revPfB revPfA initLine).
  Local Abbreviation SFROM := (SpecRuleFrom pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwcs).

  (* The spec and impl memories read alike *)
  Definition MemAgree (s1 : IState) (s2 : SState) : Prop :=
    forall L, implLineContent initLine implRegions (iRegionsA s1) L = lineContent initLine specRegions (sMemA s2) L.

  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).

  Lemma MemAgree_of_MemRelC : forall g s1 s2, MEMC g s1 s2 -> MemAgree s1 s2.
  Proof.
    intros g s1 s2 Hm L; unfold MemRelC, MemRel in Hm; destruct Hm as [[Hpre _] _].
    exact (lineContent_pre initLine (clintIdx clintS) (plicIdx plicS) (specRevRegion revBase revPfB revPfA)
             (implRevRegion revBase revPfB revPfA) post pre 0 _ _ L I I eq_refl Hpre).
  Qed.

  Lemma memValAt_agree :
    forall s1 s2 a sz, MemAgree s1 s2 ->
      implMemValAt pre post revBase revPfB revPfA initLine (iRegionsA s1) a sz = memValAtA (sMemA s2) a sz.
  Proof. intros s1 s2 a sz H; unfold implMemValAt, memValAt; rewrite H; reflexivity. Qed.

  Lemma revBitOf_agree :
    forall s1 s2 b, MemAgree s1 s2 ->
      implRevBitOf config pre post revBase revPfB revPfA initLine (iRegionsA s1) b = revBitOfA (sMemA s2) b.
  Proof. intros s1 s2 b H; unfold implRevBitOf, revBitOf; cbv zeta; rewrite (memValAt_agree s1 s2 _ _ H); reflexivity. Qed.

  Local Abbreviation iScanMsbA := (iScanMsb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevSnoopHitA := (iRevSnoopHit pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The revoker facts after a core store line write that misses the snoop *)
  Lemma RevokerRel_storeWrite :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) m1 b addr pkt size,
      REVK g s1 s2 -> iRevA s1' = iRevA s1 ->
      TraceFrameS specRegions (sMemA s2) m1 ->
      sMemA s2' = specWriteLine specRegions (lineOf b addr) (buildW b addr pkt size) m1 ->
      lineKind specRegions (lineOf b addr) = Some true ->
      (b = true -> crossesB addr size = true) ->
      (snoopHitsB addr size (iScanMsbA s1) = true -> iRevSnoopHitA s1 = true) ->
      SRULE s2 s2' -> MemAgree s1 s2 -> MemAgree s1' s2' ->
      RACC g' s1' s2' ->
      REVK g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' m1 b addr pkt size Hrk HR Htf Em Hk Hc Hsn Hrule Ha1 Ha2 Hra.
    (* the capability at the scan position is unchanged while the snoop flag is clear *)
    assert (Hmv : iRevSnoopHitA s1 = false ->
                  memValAtA (sMemA s2') (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1) capSz =
                  memValAtA (sMemA s2) (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1) capSz).
    { intros Hsf.
      assert (Hmiss : snoopHitsB addr size (iScanMsbA s1) = false)
        by (destruct (snoopHitsB addr size (iScanMsbA s1)) eqn:E; [rewrite (Hsn eq_refl) in Hsf; discriminate Hsf | reflexivity]).
      rewrite Em.
      change (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
        with (scanFull (iScanMsbA s1)).
      rewrite (memValAt_write_miss pre post revBase revPfB revPfA initLine m1 b addr pkt size _ Hk
                 (lineUnique_disjoint _ _ (Is_true_eq_true _ Hdisj)) Hmiss Hc).
      apply memValAt_ext; exact (lineContent_traceFrame initLine specRegions _ _ Htf). }
    unfold RevokerRel in *.
    destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
    unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr, iScanMsb in *.
    rewrite HR.
    refine (conj K1 (conj K2 (conj _ (conj _ Hra)))).
    - intros Hck Hsf; rewrite (Hmv Hsf); exact (K3 Hck Hsf).
    - intros Hwc Hsf.
      rewrite <- (revBitOf_agree s1' s2' _ Ha2).
      destruct (bool_cases (implRevBitOf config pre post revBase revPfB revPfA initLine (iRegionsA s1')
                              (iRevScanBase pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)))
        as [T | F]; [exact T | exfalso].
      rewrite (revBitOf_agree s1' s2' _ Ha2) in F.
      pose proof (K4 Hwc Hsf) as Hb.
      pose proof (rpCheck_writeCap _ Hwc) as Hck.
      destruct (K2 Hck) as [Hn [Hbase _]].
      pose proof (K3 Hck Hsf) as Hcap.
      set (sa := revScanAddr (projImplRevokerArchState (iRevA s1))).
      match type of Hcap with _ = ?c =>
        assert (Hcap' : memValAtA (sMemA s2) (scanFull sa) capSz = c) by exact Hcap end.
      apply (Hrule _ Hb F sa).
      + rewrite Hcap'; exact Hn.
      + rewrite Hcap'; symmetry; exact Hbase.
  Qed.

  Local Abbreviation NPMI := (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The memory relation after a store line write: the spec reads (fetch) and writes line `L`, the
   * impl region holding `L` accepts the same write *)
  Lemma MemRelC_storeWrite :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mi' m1 L w,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL L w true implRegions (iRegionsA s1) mi' ->
      TraceFrameS specRegions (sMemA s2) m1 ->
      sMemA s2' = specWriteLine specRegions L w m1 ->
      g_revOff pcAddrInit g' = g_revOff pcAddrInit g ->
      MEMC g s1 s2 -> MEMC g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mi' m1 L w E1 Hw Htf Em Eoff Hm.
    unfold MemRelC, MemRel, DevInv in *.
    rewrite Eoff.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    assert (Ei : iRegionsA s1' = mi') by (rewrite E1; reflexivity).
    rewrite Ei, Em.
    unfold specClintState, specPlicState, specRevState, implClintState, implPlicState, implRevState in *.
    rewrite !regionStateAt_specWrite by exact I.
    rewrite !(regionStateAt_writeAt _ _ _ _ _ _ _ _ _ Hw) by exact I.
    rewrite !(regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) by exact I.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) _)).
    - apply (MemRelPre_write _ _ L w true (specRevRegion revBase revPfB revPfA) (implRevRegion revBase revPfB revPfA)
               post pre 0 m1 (iRegionsA s1) mi'); [exact I | reflexivity | exact Hw |].
      exact (MemRelPre_traceFrame _ _ _ _ _ _ _ _ _ _ Htf Hpre).
    - apply SnapshotOK_specWrite; exact (SnapshotOK_traceFrame specRegions fwcs _ _ Htf Hsnap).
  Qed.
  Local Abbreviation ACC := (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation CNWB := (CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation DMQ := (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RELNE := (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).
  Local Abbreviation iFlushA := (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).

  Lemma RefRelNE_storeCommit :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mi' G0 m1 L w,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL L w true implRegions (iRegionsA s1) mi' ->
      TraceFrameS specRegions (sMemA s2) m1 ->
      sMemA s2' = specWriteLine specRegions L w m1 ->
      g_chain pcAddrInit g = (G0 ++ g_chain pcAddrInit g')%list ->
      GChain pcAddrInit (g_rf0 pcAddrInit g) G0 (g_rf0 pcAddrInit g') ->
      GChain pcAddrInit (g_rf0 pcAddrInit g') (g_chain pcAddrInit g') (iFlushA s1) ->
      (forall e, In (GInst e) G0 -> entryIsFenceI e = false) ->
      g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g -> g_revOff pcAddrInit g' = g_revOff pcAddrInit g ->
      sRfA s2' = cnwbApply pcAddrInit (g_cnwb pcAddrInit g') (g_rf0 pcAddrInit g') ->
      (forall d v, g_cnwb pcAddrInit g' = Some (d, v) -> ChainAvoids (g_chain pcAddrInit g') d) ->
      ACC g' s1' s2' -> CNWB g' s1' s2' -> DMQ g' s1' -> REVK g' s1' s2' ->
      RELNE g s1 s2 -> RELNE g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mi' G0 m1 L w E1 Hwr Htf Em Ech Hg0 Hgc Hfi Ed2a Eoff Erf Hav Hacc Hcn Hdq Hrev H.
    pose proof H as H0; destruct H0 as [_ Hm0 _ _ _ _ _ _ _ _ _ _].
    pose proof (MemRelC_storeWrite g g' s1 s1' s2 s2' mi' m1 L w E1 Hwr Htf Em Eoff Hm0) as Hmem.
    destruct H as [Hrf Hm Hl Hrp Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (Hext : FetchViewExt specRegions (sMemA s2) (sMemA s2')).
    { rewrite Em; eapply FetchViewExt_trans; [exact (FetchViewExt_traceFrame specRegions _ _ Htf) |].
      apply FetchViewExt_specWrite. }
    assert (HP : forall P, (forall r y w rdy, P r (wrRqSent r y w rdy) = P r y) ->
                   AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)).
    { intros P HP0; rewrite E1; exact (AllPorts_writeAt P HP0 _ _ _ _ _ _ Hwr). }
    constructor.
    - unfold RfRel in *.
      destruct Hrf as [R1 [R2 [R3 R4]]]; rewrite Ech in R4.
      split; [exact Erf |]; split; [rewrite E1; exact Hgc |]; split; [exact Hav |].
      intros G1 e G2 HG Hld; apply (R4 (G0 ++ G1)%list e G2); [rewrite HG, app_assoc; reflexivity | exact Hld].
    - exact Hmem.
    - unfold LatchRel in *.
      unfold sClint, sPlic in *.
      intros e Hin.
      rewrite Em; unfold specClintState, specPlicState.
      rewrite !regionStateAt_specWrite by exact I.
      rewrite !(regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) by exact I.
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
      rewrite HP by (intros r y w0 [|]; reflexivity).
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
        rewrite HP by (intros r y w0 [|]; reflexivity).
        refine (AllPorts_impl _ _ implRegions _ _ F7).
        intros r y HPr; cbv beta zeta in HPr |- *.
        destruct HPr as [C [HC1 [HC2 HC3]]]; exists C; split; [exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hla]]]; exists f, E'; split; [exact HE |].
        intros Hlv; exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hla Hlv)).
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd Whs]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 | split; [rewrite E1; exact Wmd |]].
      rewrite HP by (intros r y w0 [|]; reflexivity); exact Whs.
    - exact Hrev.
  Qed.


  (* --- The write-request ports at the system level --- *)

  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).

  Lemma writeRqPorts_mem :
    forall act (s1 s1' : IState),
      In act (@writeRqPorts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
      SemAction envI act s1 s1' Zmod.zero ->
      exists mi', WrRqPortStepL implRegions (iRegionsA s1) mi' /\ s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)).
  Proof.
    intros act s1 s1' Hin Hsem.
    unfold writeRqPorts, implMemCollectLineWriteRqPorts in Hin.
    rewrite map_map in Hin; apply in_map_iff in Hin as [f [<- Hf]]; cbv beta in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    apply SemAction_liftAction_iff in Hm' as [mi' [Hmi' Em]].
    exists mi'; split.
    - exact (wrRqPorts_step implRegions f _ _ _ _ Hf Hmi').
    - rewrite E1, Em; reflexivity.
  Qed.

  (* --- A write the memory does not accept: only traces grow, the spec stutters --- *)

  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).

  Lemma MemRelC_wrNotAccepted :
    forall g (s1 s1' : IState) (s2 : SState) mi' L w,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL L w false implRegions (iRegionsA s1) mi' ->
      MEMC g s1 s2 -> MEMC g s1' s2.
  Proof.
    intros g s1 s1' s2 mi' L w E1 Hw Hm.
    unfold MemRelC, MemRel, DevInv in *.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    assert (Ei : iRegionsA s1' = mi') by (rewrite E1; reflexivity).
    rewrite Ei.
    unfold implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_writeAt _ _ _ _ _ _ _ _ _ Hw) by exact I.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    exact (MemRelPre_write _ _ L w false (specRevRegion revBase revPfB revPfA) (implRevRegion revBase revPfB revPfA)
             post pre 0 _ (iRegionsA s1) mi' I eq_refl Hw Hpre).
  Qed.

  Lemma RefRelG_wrNotAccepted :
    forall g (s1 s1' : IState) (s2 : SState) mi' L w,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL L w false implRegions (iRegionsA s1) mi' ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 mi' L w E1 Hw Hg.
    assert (HPw : forall P, (forall r y w0, P r (wrRqSent r y w0 false) = P r y) ->
                    AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)).
    { intros P HP0; rewrite E1; exact (AllPorts_writeAt_false P HP0 _ _ _ _ _ Hw). }
    assert (HR : iRevA s1' = iRevA s1).
    { unfold iRev, implRevState; rewrite E1.
      change (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)))) with mi'.
      rewrite (regionStateAt_writeAt _ _ _ _ _ _ _ _ _ Hw) by exact I; reflexivity. }
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hwf Hrk].
    apply (RefRelG_rq_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs g g s1 s1' s2 s2 _ (sMemA s2) E1);
      try reflexivity.
    - intros P HPi; apply HPw; intros r y w0; apply HPi; reflexivity.
    - apply FetchViewExt_refl.
    - exact (MemRelC_wrNotAccepted g s1 s1' s2 mi' L w E1 Hw Hm).
    - exact Hl.
    - apply (AccessRel_frame_ports pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
               initLine g s1 s1' s2 s2); try (rewrite E1; reflexivity); try reflexivity; try exact Ha;
        try (intros; unfold PortsQuiet, PortsReadStaged, PortsReadOut, PortsWriteStaged; apply HPw; reflexivity).
      exact HR.
    - exact (RevokerRel_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
               initLine g g s1 s1' s2 s2 eq_refl eq_refl HR (fun L => eq_refl) Hrk).
    - exact Hg.
  Qed.

  (* --- The first line of a store: accepted by its ExternalMem region --- *)

  Lemma iRev_writeAt :
    forall (s1 s1' : IState) mi' L w rdy,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL L w rdy implRegions (iRegionsA s1) mi' -> iRevA s1' = iRevA s1.
  Proof.
    intros s1 s1' mi' L w rdy E1 Hw.
    unfold iRev, implRevState; rewrite E1.
    change (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)))) with mi'.
    rewrite (regionStateAt_writeAt _ _ _ _ _ _ _ _ _ Hw) by exact I; reflexivity.
  Qed.

  Local Abbreviation REL := (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               clintS clint plicS plic initLine fwcs).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation NEofG := (RefRelNE_of_G pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).
  Local Abbreviation eagerA := (eager_replay pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs Hdisj).


  Local Abbreviation iMemStA := (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA := (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RNR := (revNotReading pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* Context-free facts on the access after a store's first line (a `destruct` of the crossing bit
   * inside the commit proof costs minutes at `Qed`) *)
  Lemma accTakesHead_storeNext :
    forall (c : bool) addr size pkt, accTakesHead (if c then AccStore addr size pkt (WrPend true) else AccNone) = false.
  Proof. intros [|] addr size pkt; reflexivity. Qed.

  Lemma RevAccRel_storeNext :
    forall g (s1 : IState) (s2 : SState) (c : bool) addr size pkt,
      g_acc pcAddrInit g = (if c then AccStore addr size pkt (WrPend true) else AccNone) -> RACC g s1 s2.
  Proof. intros g s1 s2 [|] addr size pkt E; unfold RevAccRel; rewrite E; exact I. Qed.

  (* The access after the first line of a store was accepted *)
  Lemma acc_storeFirst :
    forall g1 (s1 s1' : IState) (s2m : SState) addr size pkt (cr : bool) sl0,
      iMemStA s1' = iMemStA s1 -> iReadRpA s1' = iReadRpA s1 -> iDmStA s1' = iDmStA s1 -> iRevA s1' = iRevA s1 ->
      g_acc pcAddrInit g1 = (if cr then AccStore addr size pkt (WrPend true) else AccNone) ->
      g_revOff pcAddrInit g1 = RevEq ->
      PQ s1' -> optValid (iReadRpA s1) = false ->
      (if andb (negb false) cr then msWriteRq (iMemStA s1) = true /\ msWriteRqV (iMemStA s1) = stepOf true addr size pkt
       else msIdle (iMemStA s1) = true) ->
      dmLoadRq (iDmStA s1) = true -> RNR s1 ->
      (snoopHitsB addr size (iScanMsbA s1) = true -> iRevSnoopHitA s1 = true) ->
      cr = crossesB addr size ->
      sSecondA s2m = (if cr then secondStoreOf addr pkt size else sl0) -> optValid sl0 = false ->
      ACC g1 s1' s2m.
  Proof.
    intros g1 s1 s1' s2m addr size pkt cr sl0 Emst Erp Edm HR Eacc Eoff HPQ Hrp0 Hst0 Hdlq Hrnr Hsnoop Ecr Ess Hsl.
    unfold AccessRel; rewrite Eacc, Eoff.
    unfold revNotReading, iRevPhase, iScanMsb, iRevSnoopHit in Hrnr, Hsnoop |- *.
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [_ Hx3]].
    destruct cr; cbn [andb negb] in Hst0.
    - unfold WrStageRel; cbv beta iota zeta.
      rewrite ?HR, ?Emst, ?Erp, ?Edm.
      destruct Hst0 as [Hwq Hwv].
      exact (conj (conj Hrp0 (conj Hwq (conj Hwv HPQ)))
               (conj Hdlq (conj Hrnr (conj eq_refl (conj Hsnoop (conj (eq_sym Ecr) Ess)))))).
    - cbv beta iota zeta; unfold dmNotAccessing.
      rewrite ?HR, ?Emst, ?Erp, ?Edm, Ess.
      exact (conj Hst0 (conj Hrp0 (conj HPQ (conj eq_refl (conj (conj Hx1 Hx3) (conj Hrnr Hsl)))))).
  Qed.
  (* The first (or only) line of a store accepted by the memory: the spec performs the store *)
  Lemma storeCommit_first :
    forall g (s1 s1' : IState) (s2 : SState) mi' addr size pkt,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL (lineOf false addr) (buildW false addr pkt size) true implRegions (iRegionsA s1) mi' ->
      g_acc pcAddrInit g = AccStore addr size pkt (WrStaged false) ->
      SFROM s2 -> RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mi' addr size pkt E1 Hwr Eacc Hrule Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold WrStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrp0 [Hst0 [Hlk Hws]]] [Hdlq [Hrnr [Hoff [Hsnoop [Hsec Hhq]]]]]].
    destruct Hhq as [q [[e [G' [Hch Hq]]] [Hsto [Ea [Esz Epkt]]]]].
    remember (crossesB addr size) as cr eqn:Ecr.
    pose proof (proj1 Hc Hdlq) as Hcn.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    rewrite Hch in R2.
    destruct (GChain_cons_inv pcAddrInit _ _ _ _ R2) as [rf1 [Hstep Hgc]]; cbn [ItemStep] in Hstep.
    assert (Hin : In (GInst e) (g_chain pcAddrInit g)) by (rewrite Hch; left; reflexivity).
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
    assert (HlkS : lineKind specRegions (lineOf false addr) = Some true) by (rewrite lineKind_revSwap; exact Hlk).
    assert (Hlk' : lineKind specRegions (lineOf false (stAddrOf (storeCmdOf q))) = Some true) by (rewrite Ea; exact HlkS).
    destruct (specStep_store pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwcs Hdisj
                (g_rf0 pcAddrInit g) rf1 (sMemA s2) (sSecondA s2) e q Hstep Hq Hsto Hsnw Hsec
                (Hrp [] e G' (g_rf0 pcAddrInit g) Hch (GChainNil pcAddrInit _))
                (proj1 (Hl e Hin)) (proj2 (Hl e Hin)) Hlk')
      as [m1 [Htf Hsp]].
    assert (Est : stWriteM pre post revBase revPfB revPfA m1 (storeCmdOf q) =
                  specWriteLine specRegions (lineOf false addr) (buildW false addr pkt size) m1)
      by (unfold stWriteM, stPkt; rewrite Ea, Esz, <- Epkt; reflexivity).
    assert (Esl : stCommitSl (storeCmdOf q) (sSecondA s2) =
                  if cr then secondStoreOf addr pkt size else sSecondA s2)
      by (unfold stCommitSl, stPkt; rewrite Ea, Esz, <- Epkt, <- Ecr; reflexivity).
    rewrite Est, Esl, <- R1, mkSys_eta in Hsp.
    remember (mkSysA rf1 (specWriteLine specRegions (lineOf false addr) (buildW false addr pkt size) m1)
                (if cr then secondStoreOf addr pkt size else sSecondA s2)) as s2m eqn:Es2m in Hsp.
    remember (if cr then AccStore addr size pkt (WrPend true) else AccNone) as acc' eqn:Eacc'.
    remember (mkGhost pcAddrInit G' rf1 None (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) acc') as g1 eqn:Eg1.
    assert (Ems : sMemA s2m = specWriteLine specRegions (lineOf false addr) (buildW false addr pkt size) m1)
      by (rewrite Es2m; reflexivity).
    assert (Ess : sSecondA s2m = if cr then secondStoreOf addr pkt size else sSecondA s2)
      by (rewrite Es2m; reflexivity).
    assert (Ers : sRfA s2m = rf1) by (rewrite Es2m; reflexivity).
    pose proof (iRev_writeAt s1 s1' mi' _ _ _ E1 Hwr) as HR.
    assert (Hmem : MEMC g1 s1' s2m)
      by (rewrite Eg1 at 1; exact (MemRelC_storeWrite g _ s1 s1' s2 s2m mi' m1 _ _ E1 Hwr Htf Ems eq_refl Hm)).
    assert (HPQ : PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1').
    { unfold PortsQuiet; rewrite E1.
      change (AllPorts quietP implRegions mi').
      refine (quiet_writeAt _ _ _ _ _ _ Hws Hwr).
      apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj. }
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [Hx2 Hx3]].
    assert (Hne : RELNE g1 s1' s2m).
    { apply (RefRelNE_storeCommit g g1 s1 s1' s2 s2m mi' [GInst e] m1 _ _ E1 Hwr Htf).
      - exact Ems.
      - rewrite Eg1; exact Hch.
      - rewrite Eg1; eapply GChainInst; [exact Hstep | apply GChainNil].
      - rewrite Eg1; exact Hgc.
      - intros e0 [He0 | []]; injection He0 as <-; unfold entryIsFenceI; rewrite Hq; exact (opStore_notFenceI _ Hsto).
      - rewrite Eg1; reflexivity.
      - rewrite Eg1; reflexivity.
      - rewrite Eg1, Ers; reflexivity.
      - rewrite Eg1; intros d v Hcn'; discriminate Hcn'.
      - apply (acc_storeFirst g1 s1 s1' s2m addr size pkt cr (sSecondA s2));
          [rewrite E1; reflexivity | rewrite E1; reflexivity | rewrite E1; reflexivity | exact HR
          | rewrite Eg1, Eacc'; reflexivity | rewrite Eg1; exact Hoff | exact HPQ | exact Hrp0
          | exact Hst0 | exact Hdlq | exact Hrnr | exact Hsnoop
          | exact Ecr | exact Ess | exact Hsec].
      - rewrite Eg1; unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        assert (Edm : iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                      iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
          by (rewrite E1; reflexivity).
        rewrite Edm, Hx1, Hx2.
        split; [intros _; reflexivity |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        intros H; discriminate H.
      - rewrite Eg1; unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc]; cbv zeta in Hd |- *.
        rewrite Eacc, Hch in Hd; cbn [accTakesHead] in Hd.
        rewrite (chainReqs_store_head e q G' Hq Hsto) in Hd.
        assert (Eat : accTakesHead acc' = false) by (rewrite Eacc'; apply accTakesHead_storeNext).
        rewrite Eat; rewrite E1; exact Hd.
      - apply (RevokerRel_storeWrite g g1 s1 s1' s2 s2m m1 false addr pkt size Hrk HR Htf Ems HlkS
                 (fun H => ltac:(discriminate H)) Hsnoop
                 (Hrule s2 s2m _ ltac:(constructor 1; reflexivity) ltac:(apply In_specStep_spec) Hsp)
                 (MemAgree_of_MemRelC g s1 s2 Hm) (MemAgree_of_MemRelC g1 s1' s2m Hmem)).
        apply (RevAccRel_storeNext _ _ _ cr addr size pkt); rewrite Eg1, Eacc'; reflexivity.
      - exact (NEofG g s1 s2 Hg). }
    assert (Hlen : (length (g_chain pcAddrInit g1) <= length G')%nat) by (rewrite Eg1; apply le_n).
    destruct (eagerA (length G') g1 s1' s2m Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction; [apply In_specStep_spec | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.

  (* --- The second line of a crossing store: accepted by its ExternalMem region --- *)

  (* The access after the second line of a store was accepted *)
  Lemma acc_storeSecond :
    forall g1 (s1 s1' : IState) (s2m : SState),
      iMemStA s1' = iMemStA s1 -> iReadRpA s1' = iReadRpA s1 -> iDmStA s1' = iDmStA s1 -> iRevA s1' = iRevA s1 ->
      g_acc pcAddrInit g1 = AccNone -> g_revOff pcAddrInit g1 = RevEq ->
      PQ s1' -> optValid (iReadRpA s1) = false -> msIdle (iMemStA s1) = true ->
      dmLoadRq (iDmStA s1) = true -> RNR s1 -> optValid (sSecondA s2m) = false ->
      ACC g1 s1' s2m.
  Proof.
    intros g1 s1 s1' s2m Emst Erp Edm HR Eacc Eoff HPQ Hrp0 Hidle Hdlq Hrnr Hsl.
    unfold AccessRel; rewrite Eacc, Eoff.
    unfold revNotReading, iRevPhase in Hrnr |- *; unfold dmNotAccessing.
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [_ Hx3]].
    rewrite ?HR, ?Emst, ?Erp, ?Edm.
    exact (conj Hidle (conj Hrp0 (conj HPQ (conj eq_refl (conj (conj Hx1 Hx3) (conj Hrnr Hsl)))))).
  Qed.

  (* The second line of a crossing store accepted by the memory: the spec performs it
   * (`specSecondLine`), which completes the store, then replays eagerly *)
  Lemma storeCommit_second :
    forall g (s1 s1' : IState) (s2 : SState) mi' addr size pkt,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL (lineOf true addr) (buildW true addr pkt size) true implRegions (iRegionsA s1) mi' ->
      g_acc pcAddrInit g = AccStore addr size pkt (WrStaged true) ->
      SFROM s2 -> RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mi' addr size pkt E1 Hwr Eacc Hrule Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold WrStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrp0 [Hst0 [Hlk Hws]]] [Hdlq [Hrnr [Hoff [Hsnoop [Hcr Hsec]]]]]].
    cbn [andb negb] in Hst0.
    pose proof (proj1 Hc Hdlq) as Hcn.
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hcn in R1; cbn [cnwbApply] in R1.
    assert (HlkS : lineKind specRegions (lineOf true addr) = Some true) by (rewrite lineKind_revSwap; exact Hlk).
    pose proof (specSecondLine_store pcAddrInit config pre post revBase revPfB revPfA initLine fwcs Hdisj
                  (sRfA s2) (sMemA s2) addr pkt size HlkS) as Hsp.
    rewrite <- Hsec, mkSys_eta in Hsp.
    remember (mkSysA (sRfA s2) (specWriteLine specRegions (lineOf true addr) (buildW true addr pkt size) (sMemA s2))
                (getDefault (Option SecondLine))) as s2m eqn:Es2m in Hsp.
    remember (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) None (g_revOff pcAddrInit g)
                (g_d2aFo pcAddrInit g) AccNone) as g1 eqn:Eg1.
    assert (Ems : sMemA s2m = specWriteLine specRegions (lineOf true addr) (buildW true addr pkt size) (sMemA s2))
      by (rewrite Es2m; reflexivity).
    assert (Ess : sSecondA s2m = getDefault (Option SecondLine)) by (rewrite Es2m; reflexivity).
    assert (Ers : sRfA s2m = sRfA s2) by (rewrite Es2m; reflexivity).
    pose proof (TraceFrameS_refl specRegions (sMemA s2)) as Htf.
    pose proof (iRev_writeAt s1 s1' mi' _ _ _ E1 Hwr) as HR.
    assert (Hmem : MEMC g1 s1' s2m)
      by (rewrite Eg1 at 1; exact (MemRelC_storeWrite g _ s1 s1' s2 s2m mi' (sMemA s2) _ _ E1 Hwr Htf Ems eq_refl Hm)).
    assert (HPQ : PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1').
    { unfold PortsQuiet; rewrite E1.
      change (AllPorts quietP implRegions mi').
      refine (quiet_writeAt _ _ _ _ _ _ Hws Hwr).
      apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj. }
    destruct (dmLoadRq_excl _ Hdlq) as [Hx1 [Hx2 Hx3]].
    assert (Hne : RELNE g1 s1' s2m).
    { apply (RefRelNE_storeCommit g g1 s1 s1' s2 s2m mi' [] (sMemA s2) _ _ E1 Hwr Htf).
      - exact Ems.
      - rewrite Eg1; reflexivity.
      - rewrite Eg1; apply GChainNil.
      - rewrite Eg1; exact R2.
      - intros e0 [].
      - rewrite Eg1; reflexivity.
      - rewrite Eg1; reflexivity.
      - rewrite Eg1, Ers, R1; reflexivity.
      - rewrite Eg1; intros d v Hcn'; discriminate Hcn'.
      - apply (acc_storeSecond g1 s1 s1' s2m);
          [rewrite E1; reflexivity | rewrite E1; reflexivity | rewrite E1; reflexivity | exact HR
          | rewrite Eg1; reflexivity | rewrite Eg1; exact Hoff | exact HPQ | exact Hrp0
          | exact Hst0 | exact Hdlq | exact Hrnr | rewrite Ess; reflexivity].
      - rewrite Eg1; unfold CnwbRel; cbn [g_cnwb g_chain g_acc].
        assert (Edm : iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                      iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
          by (rewrite E1; reflexivity).
        rewrite Edm, Hx1, Hx2.
        split; [intros _; reflexivity |]; split; [intros H; discriminate H |]; split; [intros H; discriminate H |].
        intros H; discriminate H.
      - rewrite Eg1; unfold DmQueueRel in Hd |- *; cbn [g_chain g_acc]; cbv zeta in Hd |- *.
        rewrite Eacc in Hd; cbn [accTakesHead] in Hd |- *.
        rewrite E1; exact Hd.
      - apply (RevokerRel_storeWrite g g1 s1 s1' s2 s2m (sMemA s2) true addr pkt size Hrk HR Htf Ems HlkS
                 (fun _ => Hcr) Hsnoop
                 (Hrule s2 s2m _ ltac:(constructor 1; reflexivity)
                    ltac:(apply (In_specSecondLine_spec pcAddrInit config pre post revBase revPfB revPfA clintS plicS)) Hsp)
                 (MemAgree_of_MemRelC g s1 s2 Hm) (MemAgree_of_MemRelC g1 s1' s2m Hmem)).
        rewrite Eg1; unfold RevAccRel; exact I.
      - exact (NEofG g s1 s2 Hg). }
    assert (Hlen : (length (g_chain pcAddrInit g1) <= length (g_chain pcAddrInit g))%nat) by (rewrite Eg1; apply le_n).
    destruct (eagerA (length (g_chain pcAddrInit g)) g1 s1' s2m Hlen Hne) as [g'' [s2'' [Hss Hg'']]].
    exists s2''; split.
    - eapply ConsAction;
        [apply (In_specSecondLine_spec pcAddrInit config pre post revBase revPfB revPfA clintS plicS) | exact Hsp | exact Hss].
    - exists g''; exact Hg''.
  Qed.
End StoreCommit.
