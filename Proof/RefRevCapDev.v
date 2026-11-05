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
From Cheriot.Proof Require Import RefRevoker RefRevokerStep RefDevWrite RefRqStepChar RefDevCommit RefWriteRqStep.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the revoker's cap read of a CustomMem or unmapped line (`readRqStep`): the
 * device answers at once with no tags, so the spec revoker takes that position's step (it reads
 * the same device line and needs no check) and runs one position ahead (`RevSpecAhead`). *)

(* --- 1. A Device Line Has No Tags --- *)

Lemma nth_pf_repeat : forall A (x : A) n i pf, @nth_pf A (repeat x n) i pf = x.
Proof.
  intros A x n; induction n as [| n IH]; intros i pf; [destruct (Nat_ltb_0 pf) |].
  destruct i; [reflexivity | exact (IH i pf)].
Qed.

Lemma readNat_all_false :
  forall n (r : FinType n -> bool) i, (forall p, r p = false) -> readNatToFinType false r i = false.
Proof.
  intros n r i H; unfold readNatToFinType.
  assert (G : forall b (e : (i <? n)%nat = b),
             match b as b0 return (i <? n)%nat = b0 -> bool with
             | true => fun pf => r (Build_FinType _ (transparent_Is_true _ (Is_true_eq_left _ pf)))
             | false => fun _ => false
             end e = false)
    by (intros [|] e; [apply H | reflexivity]).
  exact (G _ eq_refl).
Qed.

Lemma readDefault_false :
  forall n i, readNatToFinType false (@readSameTuple bool n (SameTupleDefault false n)) i = false.
Proof. intros n i; apply readNat_all_false; intros p; unfold readSameTuple; apply nth_pf_repeat. Qed.

Lemma specPkt_untagged :
  forall a d, (specPkt a (rpOfData d)).(Snd).(Fst) = false.
Proof. intros a d; exact (readDefault_false NumLineTags (Z.to_nat (Zmod.to_Z (evalExpr (memTagSlot (Var type Addr a)))))). Qed.

Lemma lineVal_untagged : forall a sz d, (lineVal a sz (rpOfData d)).(Fst) = false.
Proof.
  intros a sz d; pose proof (specPkt_untagged a d) as Ht.
  unfold lineVal; cbv [evalLetExpr memAssembleCapRead].
  match goal with |- context [Var type Bool (evalExpr ?c)] => destruct (evalExpr c) end.
  - exact Ht.
  - reflexivity.
Qed.

Lemma capNeedsCheck_untagged : forall config c, c.(Fst) = false -> capNeedsCheck config c = false.
Proof. intros config c H; unfold capNeedsCheck, needsRevocationCheck; rewrite H; reflexivity. Qed.

(* --- 2. The Spec Revoker One Position Ahead --- *)

Section ZmodRing2.
  Variable m : Z.
  Add Ring zmodRing2 : (Zmod.ring_theory m).

  Lemma Zmod_add_one_sub_one : forall (x : Zmod m), Zmod.sub (Zmod.add x Zmod.one) Zmod.one = x.
  Proof. intros x; ring. Qed.
End ZmodRing2.

(* The spec revoker's step at the impl's position puts it one position ahead *)
Lemma RevRel_specAhead :
  forall xs xi, RevRel RevEq xs xi -> RevRel RevSpecAhead (revWithScanAddr (scanNext (revScanAddr xs)) xs) xi.
Proof.
  intros xs xi H; unfold RevRel in *; cbn [revOffAddr] in *.
  rewrite H; unfold revWithScanAddr, revScanAddr; cbn [Fst Snd].
  rewrite scanNext_eq, Zmod_add_one_sub_one; reflexivity.
Qed.

Section SpecRevDev.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revS := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation MS := (specMemTree specRegions).
  Local Abbreviation specRevStateA := (specRevState pre post revBase revPfB revPfA).
  Local Abbreviation setRevSA := (setRevS pre post revBase revPfB revPfA).
  Local Abbreviation SRP := (SpecRP pre post revBase revPfB revPfA).

  Ltac srev_cbn :=
    cbn -[evalExpr evalLetExpr toAction specRevState setRevS envRegionAt nthRegionAction specMemRead specMemWrite
          readRevBit].

  Ltac srev_lens Ex :=
    apply evalActionPropGen_liftRevS;
    rewrite ?specRevState_setRevS; rewrite ?Ex; srev_cbn;
    rewrite ?setRevS_setRevS;
    repeat match goal with
    | |- context [setRevS ?a ?b ?c ?d ?e ?ms ?X] =>
        replace (setRevS a b c d e ms X) with ms by (symmetry; apply setRevS_same; rewrite Ex; reflexivity)
    end.

  (* `specMemRead` of a line through a read WP fact *)
  Lemma specMemRead_srp :
    forall env (ms ms' : TS MS) a sz rpv P,
      SRP env ms (rdLineOf false a) (rdMaskOf false a sz) ms' rpv -> P ms' (lineVal a sz rpv) ->
      evalActionPropGen env (@specMemRead type specRegions a sz) ms P.
  Proof.
    intros env ms ms' a sz rpv P Hrp HP.
    unfold specMemRead, specMemReadFirstLine; cbn [evalActionPropGen].
    apply evalActionPropGen_toAction; cbv beta.
    apply Hrp.
    apply evalActionPropGen_toAction; cbv beta.
    apply evalActionPropGen_toAction; cbv beta.
    exact HP.
  Qed.

  (* Odd epoch and scanAddr below the sweep's top, the cap read from a device (no tag): the spec
   * moves on *)
  Lemma specRevStep_scan_dev :
    forall env (ms ms' : TS MS) b t c e ist ir sa st rpv,
      specRevStateA ms = mkRev8 b t c e ist ir sa st ->
      epochOdd e = true -> scanDone sa st = false ->
      SRP env ms (rdLineOf false (scanFull sa)) (rdMaskOf false (scanFull sa) capSz) ms' rpv ->
      capNeedsCheck config (lineVal (scanFull sa) capSz rpv) = false ->
      SemAction env (@SpecRevoker.specRevokerStep [] specRegions revS config type) ms
        (setRevSA ms' (revWithScanAddr (scanNext sa) (specRevStateA ms'))) Zmod.zero.
  Proof.
    intros env ms ms' b t c e ist ir sa st rpv Ex Hodd Hnd Hrp Hnc.
    destruct (specRevStateA ms') as [b1 [t1 [c1 [e1 [ist1 [ir1 [sa1 [st1 []]]]]]]]] eqn:Ex1.
    rewrite SemAction_iff_evalActionPropGen.
    unfold SpecRevoker.specRevokerStep; cbn [evalActionPropGen].
    srev_lens Ex; rewrite ?evalExpr_Var.
    match goal with |- context [if ?cd then _ else _] =>
      replace cd with true by (symmetry; exact Hodd) end.
    srev_cbn.
    srev_lens Ex; srev_lens Ex; rewrite ?evalExpr_Var.
    match goal with |- context [if ?cd then _ else _] =>
      replace cd with true by (change (true = negb (scanDone sa st)); rewrite Hnd; reflexivity) end.
    srev_cbn.
    apply (specMemRead_srp env ms ms' _ _ rpv _ Hrp); cbv beta.
    apply evalActionPropGen_toAction; cbv beta.
    srev_cbn.
    match goal with |- context [if ?cd then _ else _] =>
      replace cd with (capNeedsCheck config (lineVal (scanFull sa) capSz rpv)) by reflexivity end.
    rewrite Hnc.
    srev_cbn.
    srev_lens Ex1.
    split; reflexivity.
  Qed.
End SpecRevDev.

(* --- 3. The Step --- *)

Section RevCapDev.
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
  Local Abbreviation iRequesterA := (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iScanAddrA := (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevArchA := (iRevArch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).
  Local Abbreviation REL := (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               clintS clint plicS plic initLine fwcs).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation KEPT := (RevKept pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation keptObsA := (RevKept_obs pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation revDevA := (RevokerRel_dev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                   initLine).
  Local Abbreviation revS := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revS plicS type).
  Local Abbreviation setRevSA := (setRevS pre post revBase revPfB revPfA).
  Local Abbreviation specRevStateA := (specRevState pre post revBase revPfB revPfA).
  Local Abbreviation sRevR := (specRevRegion revBase revPfB revPfA).
  Local Abbreviation pfS := (nth_error_app_cons_len pre sRevR post).
  Local Abbreviation DWOK := (DevWriteOK pre post revBase revPfB revPfA clintS clint plicS plic).

  (* The memory relation after a device read and the spec revoker's step *)
  Lemma MemRelC_devRev :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mr mr' ms' xs',
      iRegionsA s1 = mr -> iRegionsA s1' = mr' -> g_revOff pcAddrInit g = RevEq ->
      DWOK (sMemA s2) ms' mr mr' -> sMemA s2' = setRevSA ms' xs' ->
      RevRel (g_revOff pcAddrInit g') xs' (implRevState pre post revBase revPfB revPfA mr') ->
      MEMC g s1 s2 -> MEMC g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mr mr' ms' xs' E0 E1 Hoff Hok E2 HR Hm.
    destruct Hok as [Hmr' [Hdi [_ [_ [Hsn _]]]]].
    unfold MemRelC in *; rewrite Hoff, E0 in Hm; rewrite E1, E2.
    destruct Hm as [_ [Hdi0 Hsnap0]].
    unfold MemRel in Hmr' |- *; destruct Hmr' as [Hpre [Hcl [Hpl _]]].
    rewrite specClintState_setRevS, specPlicState_setRevS, specRevState_setRevS.
    refine (conj (conj _ (conj Hcl (conj Hpl HR))) (conj (Hdi Hdi0) _)).
    - unfold setRevS; apply MemRelPre_upd_rev_spec; exact Hpre.
    - exact (SnapshotOK_upd specRegions fwcs (length pre) sRevR pfS ms' xs' I (Hsn fwcs Hsnap0)).
  Qed.

  (* The revoker's cap read of a CustomMem or unmapped line: the spec revoker takes the
   * position's step on the same device read *)
  Lemma revCapDev :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp mrdy mr' st' mrp' env res,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) ->
      s1' = writeSubTreeState NPMI s1 (mr' ,, (st' ,, (mrq ,, (mrp' ,, (mrdy ,, tt))))) ->
      g_acc pcAddrInit g = AccRevCap (RdPend false) ->
      lineKind implRegions (lineOf false (iScanAddrA s1)) <> Some true ->
      SemAction env (@implRegionsLineReadRq type implRegions (rdLineOf false (iScanAddrA s1))
                       (rdMaskOf false (iScanAddrA s1) capSz)) mr mr' res ->
      (res.(Fst) = true -> msReadRqSent st' = true /\
                           msReadRqSentV st' = (crossesB (iScanAddrA s1) capSz ,,
                                                (stepOf false (iScanAddrA s1) capSz (getDefault CapPacket) ,, tt)) /\
                           mrp' = (if optValid res.(Snd).(Fst) then res.(Snd).(Fst) else mrp)) ->
      RELG g s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp mrdy mr' st' mrp' env res EM E1 Eacc Hk Hreg Hrt Hg.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    unfold AccessRel in Ha; rewrite Eacc in Ha; unfold RdStageRel in Ha; cbv beta iota zeta in Ha.
    destruct Ha as [[Hrq [_ [Hrp0 [Hrdy0 Hq]]]] [Hreq [Hwc0 [Hdna [Hoff [Hsec _]]]]]].
    assert (Hmr : iRegionsA s1 = mr) by (unfold iRegions; rewrite EM; reflexivity).
    destruct (iRevA s1) as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]] eqn:Ex.
    pose proof Hwc0 as Hwc; unfold iRevPhase in Hwc; rewrite Ex in Hwc; cbn [Fst Snd] in Hwc.
    destruct (rpWaitCapRp_excl _ Hwc) as [P0 _].
    pose proof Hrk as Hrk0; unfold RevokerRel in Hrk0; destruct Hrk0 as [K1 _].
    unfold iRevArch, iRevPhase in K1; rewrite Ex in K1; cbn [Fst Snd] in K1.
    destruct (K1 P0) as [Hodd Hnd].
    assert (Hxs : specRevStateA (sMemA s2) = mkRev8 b t c e ist ir sa st).
    { destruct Hm as [[_ [_ [_ Hrv]]] _].
      change (RevRel (g_revOff pcAddrInit g) (specRevStateA (sMemA s2)) (iRevA s1)) in Hrv.
      rewrite Ex, Hoff in Hrv.
      exact (RevRel_eq _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv). }
    assert (Esc : iScanAddrA s1 = scanFull sa) by (unfold iScanAddr; rewrite Ex; reflexivity).
    rewrite Esc in Hk, Hreg, Hrt.
    assert (Hmem0 : MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq (sMemA s2) mr).
    { destruct Hm as [Hm0 _]; rewrite <- Hoff, <- Hmr; exact Hm0. }
    pose proof (specEnvOK_mem pcAddrInit pre post revBase revPfB revPfA initLine fwcs s2) as HenvR.
    destruct (devRead_mem pre post revBase revPfB revPfA clintS clint plicS plic Hdisj HclintIdx HplicIdx
                env (subEnv NPMS envS s2) (sMemA s2) mr mr' (rdLineOf false (scanFull sa)) (rdMaskOf false (scanFull sa) capSz)
                res Hmem0 Hk (SpecEnvOK_custom pre post revBase revPfB revPfA initLine fwcs _ HenvR) Hreg)
      as [ms' [rpv [Eres [Hrp1 [Hok [d Ed]]]]]].
    assert (Hnc : capNeedsCheck config (lineVal (scanFull sa) capSz rpv) = false)
      by (rewrite Ed; apply capNeedsCheck_untagged, lineVal_untagged).
    pose proof (specRevStep_scan_dev config pre post revBase revPfB revPfA (subEnv NPMS envS s2) (sMemA s2) ms'
                  b t c e ist ir sa st rpv Hxs Hodd Hnd Hrp1 Hnc) as Hspec.
    subst res; destruct (Hrt eq_refl) as [Hsent1 [HsV1 Emp]].
    assert (Emp' : mrp' = (rpv ,, (true ,, tt))) by (rewrite Emp; reflexivity).
    clear Emp; subst mrp'.
    set (xsF := revWithScanAddr (scanNext sa) (specRevStateA ms')) in Hspec.
    exists (writeSubTreeState NPMS s2 (setRevSA ms' xsF)).
    split.
    { eapply ConsAction; [apply In_specRevokerStep | | apply NilAction; reflexivity].
      unfold Spec.specRevokerStep.
      apply SemAction_liftAction_iff; eexists; split; [exact Hspec | reflexivity]. }
    pose proof Hok as Hok0.
    destruct Hok as [Hmr' [Hdi [Hlc [Hfv [Hsn [Hcs [Hpm [HPorts [Hex Hky]]]]]]]]].
    assert (Hmr1 : iRegionsA s1' = mr') by (rewrite E1; reflexivity).
    assert (HK : KEPT s1 s1') by (split; unfold iRev; rewrite Hmr1, Hmr; [exact Hex | exact Hky]).
    assert (HP : forall P, AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P; rewrite Hmr1, Hmr; apply HPorts).
    destruct (keptObsA s1 s1' HK) as [Eph [_ [_ [_ [_ [Escan [_ [_ Esa]]]]]]]].
    set (s2' := writeSubTreeState NPMS s2 (setRevSA ms' xsF)).
    assert (Ems : sMemA s2' = setRevSA ms' xsF) by reflexivity.
    assert (Ess : sSecondA s2' = sSecondA s2) by reflexivity.
    assert (Hlc2 : forall L, lineContent initLine specRegions (sMemA s2') L = lineContent initLine specRegions (sMemA s2) L).
    { intros L; rewrite Ems.
      transitivity (lineContent initLine specRegions ms' L);
        [exact (lineContent_upd initLine specRegions (length pre) sRevR pfS ms' xsF L I) | apply Hlc]. }
    assert (HPQ : PQ s1') by (unfold PortsQuiet; rewrite HP; exact Hq).
    exists (mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
              RevSpecAhead (g_d2aFo pcAddrInit g) (AccRevCap (RdArrived false rpv))).
    eapply (RefRelG_mem_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2);
      [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP | exact Hlc2
      | | | | | | exact Hg].
    - cbn [g_acc accTakesHead]; rewrite Eacc; reflexivity.
    - rewrite Ems; exact (FetchViewExt_trans specRegions _ _ _ Hfv (FetchViewExt_upd specRegions (length pre) sRevR pfS ms' xsF I)).
    - apply (MemRelC_devRev g _ s1 s1' s2 s2' mr mr' ms' xsF Hmr Hmr1 Hoff Hok0 Ems); [| exact Hm].
      cbn [g_revOff].
      destruct Hmr' as [_ [_ [_ Hrv']]].
      change (RevRel RevEq (specRevStateA ms') (implRevState pre post revBase revPfB revPfA mr')) in Hrv'.
      assert (Esa' : revScanAddr (specRevStateA ms') = sa).
      { transitivity (revScanAddr (projImplRevokerArchState (implRevState pre post revBase revPfB revPfA mr'))).
        - unfold RevRel in Hrv'; rewrite Hrv'; reflexivity.
        - unfold iRevArch in Esa; rewrite Ex in Esa; unfold iRev in Esa; rewrite Hmr1 in Esa; exact Esa. }
      unfold xsF; rewrite <- Esa'; exact (RevRel_specAhead _ _ Hrv').
    - unfold LatchRel in *; intros e0 Hin; destruct (Hl e0 Hin) as [L1 L2].
      split; intros H0; [apply L1, Hcs | apply L2, Hpm]; unfold sClint, sPlic in H0; rewrite Ems in H0;
        [rewrite specClintState_setRevS in H0 | rewrite specPlicState_setRevS in H0]; exact H0.
    - unfold AccessRel; cbn [g_acc g_revOff]; unfold RdStageRel; cbv beta iota zeta.
      assert (Emst : iMemStA s1' = st') by (rewrite E1; reflexivity).
      assert (Erp1 : iReadRpA s1' = (rpv ,, (true ,, tt))) by (rewrite E1; reflexivity).
      assert (Erdy1 : optValid (iRpReadyA s1') = false)
        by (rewrite E1; unfold iRpReady in Hrdy0 |- *; rewrite EM in Hrdy0; exact Hrdy0).
      assert (Erq1 : iRequesterA s1' = iRequesterA s1) by (rewrite E1; unfold iRequester; rewrite EM; reflexivity).
      assert (Edm1 : iDmStA s1' = iDmStA s1) by (rewrite E1; reflexivity).
      unfold dmNotAccessing in Hdna |- *.
      rewrite Emst, Erp1, Erq1, Edm1, Eph, Escan, Esc, Ess.
      refine (conj (conj (conj Hsent1 HsV1) (conj eq_refl (conj Erdy1 HPQ))) (conj Hreq (conj Hwc0 (conj Hdna (conj _ (conj Hsec eq_refl)))))).
      discriminate.
    - apply (revDevA g _ s1 s1' s2 s2' HK Hlc2); [| exact Hrk].
      unfold RevAccRel; cbn [g_acc]; unfold RevCapOK; cbn [g_revOff].
      rewrite Escan, Esc; exact Hnc.
  Qed.
End RevCapDev.
