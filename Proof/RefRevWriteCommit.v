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
From Cheriot.Proof Require Import RefBits RefUntagWrite.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the revoker's untagging write accepted by the memory (`writeRqPorts` at
 * `AccRevWrite`): the spec revoker takes the position's step, which writes the same untagged
 * capability, and the offset `RevImplAhead` closes.
 * 1. `specRevStep_write`: the spec revoker step of a position whose capability is revoked. *)

(* --- 1. The Spec Revoker Step That Untags --- *)

Section SpecRevWrite.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation sRevR := (specRevRegion revBase revPfB revPfA).
  Local Abbreviation pfS := (nth_error_app_cons_len pre sRevR post).
  Local Abbreviation revS := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation MS := (specMemTree specRegions).
  Local Abbreviation specRevStateA := (specRevState pre post revBase revPfB revPfA).
  Local Abbreviation setRevSA := (setRevS pre post revBase revPfB revPfA).

  Ltac srev_cbn :=
    cbn -[evalExpr evalLetExpr toAction specRevState setRevS envRegionAt nthRegionAction specMemRead specMemWrite
          readRevBit].

  Ltac srev_lens Ex :=
    apply evalActionPropGen_liftRevS;
    rewrite ?specRevState_setRevS; rewrite ?Ex; srev_cbn;
    rewrite ?setRevS_setRevS;
    repeat match goal with
    | |- context [setRevSA ?ms ?X] =>
        replace (setRevSA ms X) with ms by (symmetry; apply setRevS_same; rewrite Ex; reflexivity)
    end.

  Lemma specRevStep_write :
    forall initLine fwcs env (ms : TS MS) b t c e ist ir sa st,
      SpecEnvOK initLine specRegions fwcs env ->
      specRevStateA ms = mkRev8 b t c e ist ir sa st ->
      epochOdd e = true -> scanDone sa st = false ->
      lineKind specRegions (lineOf false (scanFull sa)) = Some true ->
      lineUnique specRegions (lineOf false (scanFull sa)) ->
      capNeedsCheck config (memValAt pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz) = true ->
      lineKind specRegions
        (lineOf false (revByteAddrOf config (capBase (memValAt pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)))) = Some true ->
      lineUnique specRegions
        (lineOf false (revByteAddrOf config (capBase (memValAt pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)))) ->
      revBitOf config pre post revBase revPfB revPfA initLine ms
        (capBase (memValAt pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)) = true ->
      exists ms1, ReadFrameS specRegions ms ms1 /\
        SemAction env (@SpecRevoker.specRevokerStep [] specRegions revS config type) ms
          (setRevSA (specWriteLine specRegions (lineOf false (scanFull sa))
                       (buildW false (scanFull sa)
                          (disassembleW (scanFull sa)
                             (untagCap (memValAt pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)) capSz)
                          capSz) ms1)
             (mkRev8 b t c e ist ir (scanNext sa) st)) Zmod.zero.
  Proof.
    intros initLine fwcs env ms b t c e ist ir sa st Henv Ex Hodd Hnd Hk Hu Hck Hk2 Hu2 Hrb.
    set (cv := memValAt pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz) in *.
    set (w := buildW false (scanFull sa) (disassembleW (scanFull sa) (untagCap cv) capSz) capSz).
    assert (HP : evalActionPropGen env (@SpecRevoker.specRevokerStep [] specRegions revS config type) ms
                   (fun ms' v => (exists ms1, ReadFrameS specRegions ms ms1 /\
                                    ms' = setRevSA (specWriteLine specRegions (lineOf false (scanFull sa)) w ms1)
                                            (mkRev8 b t c e ist ir (scanNext sa) st)) /\ v = Zmod.zero)).
    { unfold SpecRevoker.specRevokerStep; cbn [evalActionPropGen].
      srev_lens Ex; rewrite ?evalExpr_Var.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with true by (symmetry; exact Hodd) end.
      srev_cbn.
      srev_lens Ex; srev_lens Ex; rewrite ?evalExpr_Var.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with true by (change (true = negb (scanDone sa st)); rewrite Hnd; reflexivity) end.
      srev_cbn.
      apply (specMemRead_wp initLine _ _ specRegions fwcs env ms); [exact Henv | exact Hk | exact Hu |].
      intros ms1 Hfr1; cbv beta.
      assert (Ex1 : specRevStateA ms1 = mkRev8 b t c e ist ir sa st).
      { rewrite <- Ex; exact (regionStateAt_readFrame specRegions (length pre) sRevR pfS ms ms1 Hfr1 I). }
      apply evalActionPropGen_toAction; cbv beta.
      srev_cbn.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with (capNeedsCheck config cv) by reflexivity end.
      rewrite Hck.
      srev_cbn.
      unfold readRevBit; cbn [evalActionPropGen].
      apply evalActionPropGen_toAction; cbv beta.
      srev_cbn.
      apply (specMemRead_wp initLine _ _ specRegions fwcs env ms1); [exact Henv | exact Hk2 | exact Hu2 |].
      intros ms2 Hfr2; cbv beta.
      assert (Ex2 : specRevStateA ms2 = mkRev8 b t c e ist ir sa st).
      { rewrite <- Ex1; exact (regionStateAt_readFrame specRegions (length pre) sRevR pfS ms1 ms2 Hfr2 I). }
      srev_cbn.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with (revBitOf config pre post revBase revPfB revPfA initLine ms1 (capBase cv)) by reflexivity end.
      rewrite (revBitOf_ext config pre post revBase revPfB revPfA initLine ms ms1 _
                 (lineContent_readFrame initLine specRegions ms ms1 Hfr1)), Hrb.
      srev_cbn.
      apply (specMemWrite_wp specRegions); [exact Hk | exact Hu |].
      intros v; cbv beta.
      srev_cbn.
      match goal with |- evalActionPropGen _ _ ?m3 _ =>
        assert (Ex3 : specRevStateA m3 = mkRev8 b t c e ist ir sa st)
          by (unfold specRevState; rewrite regionStateAt_specWrite by exact I; exact Ex2) end.
      srev_lens Ex3.
      split; [| reflexivity].
      exists ms2; split; [exact (ReadFrameS_trans specRegions _ _ _ Hfr1 Hfr2) |].
      reflexivity. }
    destruct (evalActionPropGen_to_SemAction _ _ _ HP) as [ms' [v [Hsem [[ms1 [Hfr ->]] ->]]]].
    exists ms1; split; [exact Hfr | exact Hsem].
  Qed.
End SpecRevWrite.

(* --- 2. Small Facts --- *)

Section ZmodCancel.
  Variable m : Z.
  Add Ring zmodRing2 : (Zmod.ring_theory m).

  Lemma Zmod_add_one_inj : forall x y : Zmod m, Zmod.add x Zmod.one = Zmod.add y Zmod.one -> x = y.
  Proof.
    intros x y H.
    assert (Ex : x = Zmod.sub (Zmod.add x Zmod.one) Zmod.one) by ring.
    assert (Ey : y = Zmod.sub (Zmod.add y Zmod.one) Zmod.one) by ring.
    rewrite Ex, Ey, H; reflexivity.
  Qed.
End ZmodCancel.

(* The spec revoker one position behind the impl's *)
Lemma RevRel_implAhead :
  forall xs b t c e ist ir sa st ph sc sb sh cp,
    RevRel RevImplAhead xs (mkRev12 b t c e ist ir (Zmod.add sa Zmod.one) st ph sc sb sh cp) ->
    xs = mkRev8 b t c e ist ir sa st.
Proof.
  intros xs b t c e ist ir sa st ph sc sb sh cp HR.
  destruct xs as [b0 [t0 [c0 [e0 [i0 [r0 [s0 [st0 []]]]]]]]].
  unfold RevRel in HR.
  assert (E7 : Zmod.add sa Zmod.one = Zmod.add s0 Zmod.one)
    by exact (f_equal (fun x : TS (Node "revoker" (revokerChildren [])) => x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)) HR).
  apply Zmod_add_one_inj in E7; subst s0.
  exact (eq_sym (f_equal (revWithScanAddr sa) HR)).
Qed.

(* --- 3. The Commit --- *)

Section RevWriteCommit.
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
  Local Abbreviation NPMS := (Spec.np_mem pcAddrInit specRegions).
  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
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
  Local Abbreviation LATCH := (LatchRel pcAddrInit pre post revBase revPfB revPfA clintS plicS).

  (* The relation after a line write accepted by the impl memory together with a spec memory step
   * that only extends the fetch view; the facts that change are premises *)
  Lemma RefRelG_writeFrame :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mi' ms' L w,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL L w true implRegions (iRegionsA s1) mi' ->
      s2' = writeSubTreeState NPMS s2 ms' ->
      g_chain pcAddrInit g' = g_chain pcAddrInit g -> g_rf0 pcAddrInit g' = g_rf0 pcAddrInit g ->
      g_cnwb pcAddrInit g' = g_cnwb pcAddrInit g -> g_d2aFo pcAddrInit g' = g_d2aFo pcAddrInit g ->
      accTakesHead (g_acc pcAddrInit g') = accTakesHead (g_acc pcAddrInit g) ->
      (forall rc, revWb config pre post revBase revPfB revPfA initLine (sMemA s2') rc =
                  revWb config pre post revBase revPfB revPfA initLine (sMemA s2) rc) ->
      FetchViewExt specRegions (sMemA s2) (sMemA s2') ->
      MEMC g' s1' s2' -> LATCH g' s2' -> ACC g' s1' s2' -> REVK g' s1' s2' ->
      RELG g s1 s2 -> RELG g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mi' ms' L w E1 Hwr E2 Ech Erf Ecn Ed2a Eacc Hrw Hext Hmem Hlat Hacc Hrev H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (HP : forall P, (forall r y w0 rdy, P r (wrRqSent r y w0 rdy) = P r y) ->
                   AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1)).
    { intros P HP0; rewrite E1; exact (AllPorts_writeAt P HP0 _ _ _ _ _ _ Hwr). }
    assert (Edm : iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                  iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
      by (rewrite E1; reflexivity).
    constructor.
    - unfold RfRel in *; rewrite Ech, Erf, Ecn; rewrite E1, E2; exact Hrf.
    - exact Hmem.
    - exact Hlat.
    - unfold ReplayRel in *; rewrite Ech, Erf; intros G1 e G2 rfe Hg Hch.
      exact (FetchAllowedInst_fetchViewExt initLine fwcs specRegions _ _ _ _ Hsnap Hext (Hrp G1 e G2 rfe Hg Hch)).
    - unfold EagerRel in *; rewrite Ech; rewrite E2; exact He.
    - exact Hacc.
    - unfold CnwbRel in *; rewrite Ecn, Ech, Eacc; destruct Hc as [Hc1 Hc2]; rewrite Edm, !Hrw; exact (conj Hc1 Hc2).
    - unfold DmQueueRel in *; rewrite Ech, Eacc; rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite Ech.
      rewrite HP by (intros r y w0 [|]; reflexivity).
      rewrite E1; exact Hf.
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

  Local Abbreviation setRevSA := (setRevS pre post revBase revPfB revPfA).
  Local Abbreviation sRevR := (specRevRegion revBase revPfB revPfA).
  Local Abbreviation pfS := (nth_error_app_cons_len pre sRevR post).
  Local Abbreviation memValAtA := (memValAt pre post revBase revPfB revPfA initLine).
  Local Abbreviation revBitOfA := (revBitOf config pre post revBase revPfB revPfA initLine).
  Local Abbreviation revS := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revS plicS type).

  (* The spec revoker's untagging write of slot `sa` after reads `ms -> ms1`, then its new registers *)
  Definition revWriteMem (ms ms1 : TS (specMemTree specRegions)) (sa : bits TagAddrWidth) x : TS (specMemTree specRegions) :=
    setRevSA (specWriteLine specRegions (lineOf false (scanFull sa))
                (buildW false (scanFull sa) (disassembleW (scanFull sa) (untagCap (memValAtA ms (scanFull sa) capSz)) capSz)
                   capSz) ms1) x.

  Lemma revBitOf_revWrite :
    forall ms ms1 sa x b,
      ReadFrameS specRegions ms ms1 -> lineKind specRegions (lineOf false (scanFull sa)) = Some true ->
      revBitOfA (revWriteMem ms ms1 sa x) b = revBitOfA ms b.
  Proof.
    intros ms ms1 sa x b Hfr Hk; unfold revWriteMem.
    rewrite (revBitOf_ext config pre post revBase revPfB revPfA initLine _ (setRevSA _ x) b
               (fun L => lineContent_upd initLine specRegions (length pre) sRevR pfS _ x L I)).
    rewrite <- (memValAt_ext pre post revBase revPfB revPfA initLine ms ms1 _ _
                  (lineContent_readFrame initLine specRegions ms ms1 Hfr)).
    transitivity (revBitOfA ms1 b).
    - exact (revBitOf_untag config pre post revBase revPfB revPfA initLine ms1 sa b Hk
               (lineUnique_disjoint _ _ (Is_true_eq_true _ Hdisj))).
    - exact (revBitOf_ext config pre post revBase revPfB revPfA initLine ms ms1 b
               (lineContent_readFrame initLine specRegions ms ms1 Hfr)).
  Qed.

  Lemma revWb_revWrite :
    forall ms ms1 sa x rc,
      ReadFrameS specRegions ms ms1 -> lineKind specRegions (lineOf false (scanFull sa)) = Some true ->
      revWb config pre post revBase revPfB revPfA initLine (revWriteMem ms ms1 sa x) rc =
      revWb config pre post revBase revPfB revPfA initLine ms rc.
  Proof.
    intros ms ms1 sa x rc Hfr Hk; unfold revWb; cbv zeta.
    rewrite (revBitOf_revWrite ms ms1 sa x _ Hfr Hk); reflexivity.
  Qed.

  Lemma FetchViewExt_revWrite :
    forall ms ms1 sa x, ReadFrameS specRegions ms ms1 -> FetchViewExt specRegions ms (revWriteMem ms ms1 sa x).
  Proof.
    intros ms ms1 sa x Hfr; unfold revWriteMem.
    eapply FetchViewExt_trans; [exact (FetchViewExt_readFrame specRegions _ _ Hfr) |].
    eapply FetchViewExt_trans; [apply FetchViewExt_specWrite |].
    exact (FetchViewExt_upd specRegions (length pre) sRevR pfS _ x I).
  Qed.

  Lemma specClintState_specWrite :
    forall L w m, specClintState pre post revBase revPfB revPfA clintS (specWriteLine specRegions L w m) =
                  specClintState pre post revBase revPfB revPfA clintS m.
  Proof. intros L w m; unfold specClintState; rewrite regionStateAt_specWrite by exact I; reflexivity. Qed.

  Lemma specPlicState_specWrite :
    forall L w m, specPlicState pre post revBase revPfB revPfA plicS (specWriteLine specRegions L w m) =
                  specPlicState pre post revBase revPfB revPfA plicS m.
  Proof. intros L w m; unfold specPlicState; rewrite regionStateAt_specWrite by exact I; reflexivity. Qed.

  Lemma LatchRel_revWrite :
    forall g (s2 : SState) ms1 sa x,
      ReadFrameS specRegions (sMemA s2) ms1 -> LATCH g s2 ->
      LATCH g (writeSubTreeState NPMS s2 (revWriteMem (sMemA s2) ms1 sa x)).
  Proof.
    intros g s2 ms1 sa x Hfr Hl; unfold LatchRel, sClint, sPlic in *.
    intros e0 Hin; destruct (Hl e0 Hin) as [L1 L2]; split.
    - intros Hs0; apply L1; revert Hs0.
      change (sMemA (writeSubTreeState NPMS s2 (revWriteMem (sMemA s2) ms1 sa x))) with (revWriteMem (sMemA s2) ms1 sa x).
      unfold revWriteMem.
      rewrite specClintState_setRevS, specClintState_specWrite, (specClintState_readFrame _ _ _ _ _ _ _ _ Hfr).
      exact (fun H => H).
    - intros Hp0; apply L2; revert Hp0.
      change (sMemA (writeSubTreeState NPMS s2 (revWriteMem (sMemA s2) ms1 sa x))) with (revWriteMem (sMemA s2) ms1 sa x).
      unfold revWriteMem.
      rewrite specPlicState_setRevS, specPlicState_specWrite, (specPlicState_readFrame _ _ _ _ _ _ _ _ Hfr).
      exact (fun H => H).
  Qed.

  (* The memory relation after the impl memory accepted the revoker's write and the spec revoker
   * wrote the same line and moved on *)
  Lemma MemRelC_revWrite :
    forall g g1 (s1 s1' : IState) (s2 s2' : SState) mi' ms1 sa xs',
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL (lineOf false (scanFull sa))
        (buildW false (scanFull sa) (disassembleW (scanFull sa) (untagCap (memValAtA (sMemA s2) (scanFull sa) capSz)) capSz)
           capSz) true implRegions (iRegionsA s1) mi' ->
      ReadFrameS specRegions (sMemA s2) ms1 ->
      sMemA s2' = revWriteMem (sMemA s2) ms1 sa xs' ->
      RevRel (g_revOff pcAddrInit g1) xs' (iRevA s1') ->
      MEMC g s1 s2 -> MEMC g1 s1' s2'.
  Proof.
    intros g g1 s1 s1' s2 s2' mi' ms1 sa xs' E1 Hwr Hfr E2 HR Hm.
    set (s2X := writeSubTreeState NPMS s2
                  (specWriteLine specRegions (lineOf false (scanFull sa))
                     (buildW false (scanFull sa)
                        (disassembleW (scanFull sa) (untagCap (memValAtA (sMemA s2) (scanFull sa) capSz)) capSz) capSz) ms1)).
    assert (HX : MEMC g s1' s2X).
    { eapply MemRelC_storeWrite with (g := g) (g' := g) (s2 := s2) (s2' := s2X);
        [exact E1 | exact Hwr | exact (TraceFrameS_readFrame specRegions _ _ Hfr) | reflexivity | reflexivity | exact Hm]. }
    eapply MemRelC_revLock with (g := g) (g' := g1) (s1 := s1') (s1' := s1') (s2 := s2X) (s2' := s2')
                                (mr := iRegionsA s1') (x' := iRevA s1') (ms1 := sMemA s2X) (xs' := xs').
    - reflexivity.
    - symmetry; apply setRevR_revOfR.
    - apply ReadFrameS_refl.
    - exact E2.
    - exact HR.
    - exact HX.
  Qed.

  Local Abbreviation iRevArchA := (iRevArch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The revoker's write accepted by the memory: the spec revoker takes the position's step *)
  Lemma revWrite_commit :
    forall g (s1 s1' : IState) (s2 : SState) mi' addr pkt,
      s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)) ->
      WriteAtL (lineOf false addr) (buildW false addr pkt capSz) true implRegions (iRegionsA s1) mi' ->
      g_acc pcAddrInit g = AccRevWrite addr pkt (WrStaged false) ->
      RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mi' addr pkt E1 Hwr Eacc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold WrStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrp0 [Hrdy0 [Hst0 [Hlk Hws]]]] [Hidle [Hdna [Hoff [Hsec _]]]]].
    pose proof Hrk as Hrk0; unfold RevokerRel in Hrk0; destruct Hrk0 as [_ [_ [_ [_ Hra]]]].
    unfold RevAccRel in Hra; rewrite Eacc in Hra.
    destruct Hra as [sa [Esa [Ea [Hsw [Hnc [Hrb [Epkt _]]]]]]].
    subst addr pkt.
    rewrite crossesB_scanFull in Hst0; cbn [andb negb] in Hst0.
    assert (HR : iRevA s1' = iRevA s1) by (eapply iRev_writeAt; [exact E1 | exact Hwr]).
    remember (iRevA s1) as x eqn:Ex.
    destruct x as [b [t [c [e [ist [ir [sa1 [st [ph [sc [sb [sh [cp []]]]]]]]]]]]]].
    unfold iRevArch in Esa, Hsw; rewrite <- Ex in Esa, Hsw; cbn [projImplRevokerArchState revScanAddr Fst Snd] in Esa.
    subst sa1.
    destruct Hsw as [Hodd Hnd].
    unfold iRevPhase in Hidle; rewrite <- Ex in Hidle; cbn [Fst Snd] in Hidle.
    pose proof Hm as Hm0; destruct Hm0 as [[_ [_ [_ Hrv]]] _].
    change (RevRel (g_revOff pcAddrInit g) (specRevState pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
    rewrite <- Ex, Hoff in Hrv.
    pose proof (RevRel_implAhead _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv) as Hxs.
    assert (HlkS : lineKind specRegions (lineOf false (scanFull sa)) = Some true) by (rewrite lineKind_revSwap; exact Hlk).
    pose proof (lineUnique_disjoint _ (lineOf false (scanFull sa)) (Is_true_eq_true _ Hdisj)) as Hu.
    assert (Hk2 : lineKind specRegions (lineOf false (revByteAddrOf config (capBase (memValAtA (sMemA s2) (scanFull sa) capSz))))
                  = Some true)
      by (apply revTab_needsCheck with (Hdisj := Hdisj) (HrevTab := HrevTab); exact Hnc).
    pose proof (lineUnique_disjoint _ (lineOf false (revByteAddrOf config (capBase (memValAtA (sMemA s2) (scanFull sa) capSz)))) (Is_true_eq_true _ Hdisj)) as Hu2.
    destruct (specRevStep_write config pre post revBase revPfB revPfA initLine fwcs (subEnv NPMS envS s2) (sMemA s2)
                b t c e ist ir sa st (specEnvOK_mem pcAddrInit pre post revBase revPfB revPfA initLine fwcs s2)
                Hxs Hodd Hnd HlkS Hu Hnc Hk2 Hu2 Hrb)
      as [ms1 [Hfr1 Hsem1]].
    set (xs' := mkRev8 b t c e ist ir (scanNext sa) st) in Hsem1.
    change (setRevS pre post revBase revPfB revPfA _ xs') with (revWriteMem (sMemA s2) ms1 sa xs') in Hsem1.
    exists (writeSubTreeState NPMS s2 (revWriteMem (sMemA s2) ms1 sa xs')).
    destruct (rpIdle_excl _ Hidle) as [Q1 [Q2 [Q3 Q4]]].
    assert (ER' : iRevA s1' = mkRev12 b t c e ist ir (Zmod.add sa Zmod.one) st ph sc sb sh cp) by (rewrite HR; try rewrite <- Ex; reflexivity).
    split.
    - eapply ConsAction; [apply In_specRevokerStep | | apply NilAction; reflexivity].
      unfold Spec.specRevokerStep.
      apply SemAction_liftAction_iff; eexists; split; [exact Hsem1 | reflexivity].
    - exists (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
                RevEq (g_d2aFo pcAddrInit g) AccNone).
      apply (RefRelG_writeFrame g _ s1 s1' s2 _ mi' _ _ _ E1 Hwr eq_refl);
        [reflexivity | reflexivity | reflexivity | reflexivity | | | | | | | | exact Hg].
      + cbn [g_acc accTakesHead]; rewrite Eacc; reflexivity.
      + intros rc; exact (revWb_revWrite _ ms1 sa xs' rc Hfr1 HlkS).
      + exact (FetchViewExt_revWrite _ ms1 sa xs' Hfr1).
      + apply (MemRelC_revWrite g _ s1 s1' s2 (writeSubTreeState NPMS s2 (revWriteMem (sMemA s2) ms1 sa xs')) mi' ms1 sa xs' E1 Hwr Hfr1 eq_refl); [| exact Hm].
        cbn [g_revOff]; rewrite ER'; unfold RevRel, xs'; rewrite scanNext_eq; reflexivity.
      + exact (LatchRel_revWrite g s2 ms1 sa xs' Hfr1 Hl).
      + unfold AccessRel; cbn [g_acc g_revOff].
        unfold revNotReading, iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        refine (conj _ (conj _ (conj _ (conj _ (conj eq_refl (conj _ (conj (conj Q1 Q3) _))))))).
        * rewrite E1; exact Hst0.
        * rewrite E1; exact Hrp0.
        * rewrite E1; exact Hrdy0.
        * unfold PortsQuiet; rewrite E1.
          change (AllPorts quietP implRegions mi').
          refine (quiet_writeAt _ _ _ _ _ _ Hws Hwr).
          apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj.
        * rewrite E1; exact Hdna.
        * exact Hsec.
      + unfold RevokerRel; cbn [g_acc].
        unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        split; [rewrite Hidle; intros Hc'; discriminate Hc' |].
        unfold rpCheck; rewrite Q2, Q3, Q4.
        split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
        split; [intros Hc'; discriminate Hc' | exact I].
  Qed.

  (* --- 4. The Write-Request Ports --- *)

  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PRS := (PortsReadStaged pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation PRO := (PortsReadOut pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation NoWrite := (fun (s1 : IState) =>
                                   AllPorts (fun r y => portRqIsWrite r y = false) implRegions (iRegionsA s1)).

  (* A Write is staged only for a store or the revoker's write *)
  Lemma AccessRel_wr :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 ->
      NoWrite s1 \/
      (exists addr size pkt b, g_acc pcAddrInit g = AccStore addr size pkt (WrStaged b)) \/
      (exists addr pkt, g_acc pcAddrInit g = AccRevWrite addr pkt (WrStaged false)).
  Proof.
    intros g s1 s2 Ha.
    assert (HQ1 : PQ s1 -> NoWrite s1).
    { unfold PortsQuiet; apply AllPorts_impl; intros r y [Hv _]; exact (portRqIsWrite_invalid r y Hv). }
    assert (HQ2 : forall L, PRS L s1 -> NoWrite s1).
    { intros L; unfold PortsReadStaged; apply AllPorts_impl; intros r y [_ Hp].
      destruct (isRegionAddrB r L); [exact (portRqIsWrite_read r y L Hp) | exact (portRqIsWrite_invalid r y Hp)]. }
    assert (HQ3 : forall L, PRO L s1 -> NoWrite s1).
    { intros L; unfold PortsReadOut; apply AllPorts_impl; intros r y [Hv _]; exact (portRqIsWrite_invalid r y Hv). }
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [b|b] | ld pkt0 [b|b|b|b rp|res]
                                     | rc [b|b|b|b rp|res] | [b|b|b|b rp|res]
                                     | [b|b|b|b rp|res] | addr pkt [b|b]];
      unfold WrStageRel, RdStageRel, rdSecond, wrSecond in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (left; first [ match goal with H : PQ s1 |- _ => exact (HQ1 H) end
                       | match goal with H : PRS _ s1 |- _ => exact (HQ2 _ H) end
                       | match goal with H : PRO _ s1 |- _ => exact (HQ3 _ H) end ]).
    all: try match goal with H : ?b = false |- _ => is_var b; subst b end.
    - right; left; eexists _, _, _, _; reflexivity.
    - right; right; eexists _, _; reflexivity.
  Qed.

  Local Abbreviation STEPOKR := (StepOKR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                   clintS clint plicS plic initLine fwcs).

  Theorem stepOK_writeRqPorts :
    forall act,
      In act (@writeRqPorts pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type) ->
      STEPOKR act.
  Proof.
    intros act Hin s1 s1' s2 Hsem Hrule [g Hg].
    assert (HW : exists mi', WrRqPortStepL implRegions (iRegionsA s1) mi' /\
                             s1' = writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd)))
      by (eapply writeRqPorts_mem; [exact Hin | exact Hsem]).
    destruct HW as [mi' [Hst E1]].
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    assert (Hu : forall L, lineUnique implRegions L)
      by (intros L; apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj).
    assert (Hstut : mi' = iRegionsA s1 -> exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2').
    { intros Emi; exists s2; split; [apply NilAction; reflexivity | exists g].
      replace s1' with s1; [exact Hg |].
      rewrite E1, Emi; reflexivity. }
    destruct (AccessRel_wr g s1 s2 Ha) as [Hnw | [[addr [size [pkt [b Eacc]]]] | [addr [pkt Eacc]]]].
    - apply Hstut; exact (wrRqStep_noWrite _ _ _ Hnw Hst).
    - pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'; unfold WrStageRel in Ha'; cbv beta iota zeta in Ha'.
      destruct Ha' as [[_ [_ [_ [_ Hws]]]] _].
      destruct (wrRqStep_staged _ _ _ _ _ (Hu _) Hws Hst) as [Emi | [[|] Hwr]].
      + apply Hstut; exact Emi.
      + destruct b.
        * eapply storeCommit_second; eassumption.
        * eapply storeCommit_first; eassumption.
      + exists s2; split; [apply NilAction; reflexivity |].
        exists g; eapply RefRelG_wrNotAccepted; eassumption.
    - pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Eacc in Ha'; unfold WrStageRel in Ha'; cbv beta iota zeta in Ha'.
      destruct Ha' as [[_ [_ [_ [_ Hws]]]] _].
      destruct (wrRqStep_staged _ _ _ _ _ (Hu _) Hws Hst) as [Emi | [[|] Hwr]].
      + apply Hstut; exact Emi.
      + exact (revWrite_commit g s1 s1' s2 mi' addr pkt E1 Hwr Eacc Hg).
      + exists s2; split; [apply NilAction; reflexivity |].
        exists g; eapply RefRelG_wrNotAccepted; eassumption.
  Qed.
End RevWriteCommit.
