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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker RefSpecRead.
From Cheriot.Proof Require Import RefRevTable.
From Cheriot.Proof Require Import ImplSpec.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE IMPL REVOKER STEPS REFINE THE SPEC
 * ===========================================================================
 * Each of the five revoker rules keeps the refinement relation (`StepOK`):
 * - WaitRevBitRq and WriteCap hand a read or a write to the memory; the spec stutters
 *   (the write leaves the impl one position ahead, `RevImplAhead`);
 * - Idle issues the cap read of position scanAddr (the spec stutters) or takes an
 *   architectural step with the spec (sweep done, kick, idle);
 * - WaitCapRp and WaitRevBitRp finish a position: when it needs no write the spec takes the
 *   position's step, which only reads memory (`specRevStep_scan`, `scan_commit`); otherwise
 *   the spec stutters, or closes a `RevSpecAhead` offset.
 * The steps assume that the regions are pairwise disjoint (`Hdisj`) and that the whole
 * revocation table is ExternalMem (`HrevTab`). *)

Local Abbreviation TS t := (TreeState DomainElemState t).

(* --- 1. More Tags --- *)

Lemma msReadRpReady_excl :
  forall st, msReadRpReady st = true ->
    msIdle st = false /\ msReadRq st = false /\ msReadRqSent st = false /\ msWriteRq st = false.
Proof.
  intros [d tg]; unfold msIdle, msReadRq, msReadRqSent, msReadRpReady, msWriteRq; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma rpCheck_waitRevBitRq : forall p, rpWaitRevBitRq p = true -> rpCheck p = true.
Proof. intros p H; unfold rpCheck; rewrite H; reflexivity. Qed.

Lemma rpCheck_waitRevBitRp : forall p, rpWaitRevBitRp p = true -> rpCheck p = true.
Proof. intros p H; unfold rpCheck; rewrite H, orb_true_r; reflexivity. Qed.

Lemma rpCheck_writeCap : forall p, rpWriteCap p = true -> rpCheck p = true.
Proof. intros p H; unfold rpCheck; rewrite H, !orb_true_r; reflexivity. Qed.

(* --- 2. The Memory Relation When the Impl Revoker Changes --- *)

Section MemRelPreRev.
  Variable core : string.
  Variables cp pp : nat.

  (* The position `length l` (the revoker) is not read by `MemRelPre` *)
  Lemma MemRelPre_upd_rev_impl :
    forall sRev iRev post l i (ms : TS (specMemTree core (l ++ sRev :: post)))
           (mi : TS (implRegionsTree core (l ++ iRev :: post))) w,
      MemRelPre core cp pp i l sRev iRev post ms mi ->
      MemRelPre core cp pp i l sRev iRev post ms
        (updRegionStateAt (implMemRegionTree core) (length l) (l ++ iRev :: post) iRev
           (nth_error_app_cons_len l iRev post) mi w).
  Proof.
    intros sRev iRev post l; induction l as [| r l IH]; intros i ms mi w H.
    - exact H.
    - cbn [MemRelPre length app nth_error_app_cons_len updRegionStateAt Fst Snd] in *.
      destruct H as [H0 H1]; split; [exact H0 | exact (IH _ _ _ w H1)].
  Qed.
  (* ... and neither is the spec one *)
  Lemma MemRelPre_upd_rev_spec :
    forall sRev iRev post l i (ms : TS (specMemTree core (l ++ sRev :: post)))
           (mi : TS (implRegionsTree core (l ++ iRev :: post))) w,
      MemRelPre core cp pp i l sRev iRev post ms mi ->
      MemRelPre core cp pp i l sRev iRev post
        (updRegionStateAt (memRegionTree core) (length l) (l ++ sRev :: post) sRev
           (nth_error_app_cons_len l sRev post) ms w) mi.
  Proof.
    intros sRev iRev post l; induction l as [| r l IH]; intros i ms mi w H.
    - exact H.
    - cbn [MemRelPre length app nth_error_app_cons_len updRegionStateAt Fst Snd] in *.
      destruct H as [H0 H1]; split; [exact H0 | exact (IH _ _ _ w H1)].
  Qed.
End MemRelPreRev.

(* --- 2b. The Scan Address --- *)

Lemma scanNext_eq : forall sa, scanNext sa = Zmod.add sa Zmod.one.
Proof. intros sa; unfold scanNext; cbn; rewrite Zmod.add_0_l; reflexivity. Qed.

Section RevRelFacts.
  Variable core : string.

  Definition mkRev12 (b t : bits TagAddrWidth) (c : bool) (e : bits Xlen) (ist ir : bool) (sa st : bits TagAddrWidth)
    (ph : type RevPhase) (sc : type FullCapWithTag) (sb : type (Bit (AddrSz + 1))) (sh : bool)
    : TS (implRevokerTree core) :=
    (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))).

  Lemma RevRel_scan :
    forall o xs b t c e ist ir sa st ph sc sb sh,
      RevRel core o xs (mkRev12 b t c e ist ir sa st ph sc sb sh) -> sa = revOffAddr o (revScanAddr core xs).
  Proof. intros o xs b t c e ist ir sa st ph sc sb sh HR; exact (f_equal (revScanAddr core) HR). Qed.

  (* The impl-only registers do not matter *)
  Lemma RevRel_implRegs :
    forall o xs b t c e ist ir sa st ph sc sb sh ph2 sc2 sb2 sh2,
      RevRel core o xs (mkRev12 b t c e ist ir sa st ph sc sb sh) ->
      RevRel core o xs (mkRev12 b t c e ist ir sa st ph2 sc2 sb2 sh2).
  Proof. intros; assumption. Qed.

  (* The impl advances its scan address *)
  Lemma RevRel_advance :
    forall o o' xs b t c e ist ir sa st ph sc sb sh ph2 sc2 sb2 sh2,
      RevRel core o xs (mkRev12 b t c e ist ir sa st ph sc sb sh) ->
      scanNext sa = revOffAddr o' (revScanAddr core xs) ->
      RevRel core o' xs (mkRev12 b t c e ist ir (scanNext sa) st ph2 sc2 sb2 sh2).
  Proof.
    intros o o' xs b t c e ist ir sa st ph sc sb sh ph2 sc2 sb2 sh2 HR Hn.
    unfold RevRel in *; rewrite <- Hn.
    transitivity (revWithScanAddr core (scanNext sa)
                    (projImplRevokerArchState core (mkRev12 b t c e ist ir sa st ph sc sb sh))); [reflexivity |].
    rewrite HR; reflexivity.
  Qed.
  Definition mkRev8 (b t : bits TagAddrWidth) (c : bool) (e : bits Xlen) (ist ir : bool) (sa st : bits TagAddrWidth)
    : TS (Node "revoker" (revokerChildren core [])) :=
    (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, tt)))))))).

  (* With no offset the spec revoker is the impl's architectural part *)
  Lemma RevRel_eq :
    forall xs b t c e ist ir sa st ph sc sb sh,
      RevRel core RevEq xs (mkRev12 b t c e ist ir sa st ph sc sb sh) -> xs = mkRev8 b t c e ist ir sa st.
  Proof.
    intros xs b t c e ist ir sa st ph sc sb sh HR.
    destruct xs as [b0 [t0 [c0 [e0 [ist0 [ir0 [sa0 [st0 []]]]]]]]].
    exact (eq_sym HR).
  Qed.
End RevRelFacts.

(* --- 2c. The Spec Revoker Inside the Spec Memory --- *)

Section SpecRevLens.
  Variable core : string.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf core pre post revBase revPfB revPfA).
  Local Abbreviation sRevR := (specRevRegion core revBase revPfB revPfA).
  Local Abbreviation pfS := (nth_error_app_cons_len pre sRevR post).
  Local Abbreviation revS := (revSpecOf core pre post revBase revPfB revPfA).
  Local Abbreviation MS := (specMemTree core specRegions).
  Local Abbreviation RS := (Node "revoker" (revokerChildren core [])).
  Local Abbreviation specRevStateA := (specRevState core pre post revBase revPfB revPfA).

  Definition setRevS (ms : TS MS) (x : TS RS) : TS MS :=
    updRegionStateAt (memRegionTree core) (length pre) specRegions sRevR pfS ms x.

  Lemma evalActionPropGen_liftRevS :
    forall env k (a : Action type RS k) (ms : TS MS) P,
      evalActionPropGen env (@nthRegionAction core type (length pre) specRegions sRevR pfS k a) ms P <->
      evalActionPropGen (envRegionAt (memRegionTree core) (length pre) specRegions sRevR pfS env ms) a
        (specRevStateA ms) (fun x v => P (setRevS ms x) v).
  Proof. intros env k a ms P; unfold nthRegionAction; apply evalActionPropGen_genNthRegionAction. Qed.

  Lemma specRevState_setRevS : forall ms x, specRevStateA (setRevS ms x) = x.
  Proof. intros ms x; exact (regionStateAt_updRegionStateAt (memRegionTree core) (length pre) specRegions sRevR pfS ms x). Qed.

  Lemma setRevS_setRevS : forall ms x y, setRevS (setRevS ms x) y = setRevS ms y.
  Proof. intros ms x y; exact (updRegionStateAt_updRegionStateAt (memRegionTree core) (length pre) specRegions sRevR pfS ms x y). Qed.

  Lemma setRevS_same : forall ms x, specRevStateA ms = x -> setRevS ms x = ms.
  Proof. intros ms x <-; exact (updRegionStateAt_regionStateAt (memRegionTree core) (length pre) specRegions sRevR pfS ms). Qed.

  Ltac srev_cbn :=
    cbn -[evalExpr evalLetExpr toAction specRevState setRevS envRegionAt nthRegionAction specMemRead specMemWrite
          readRevBit].

  Ltac srev_lens Ex :=
    apply evalActionPropGen_liftRevS;
    rewrite ?specRevState_setRevS; rewrite ?Ex; srev_cbn;
    rewrite ?setRevS_setRevS;
    repeat match goal with
    | |- context [setRevS ?ms ?X] =>
        replace (setRevS ms X) with ms by (symmetry; apply setRevS_same; rewrite Ex; reflexivity)
    end.

  (* Even epoch: no sweep; a kick starts one *)
  Lemma specRevStep_even :
    forall env (ms : TS MS) b t c e ist ir sa st,
      specRevStateA ms = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, tt)))))))) ->
      epochOdd e = false ->
      SemAction env (@SpecRevoker.specRevokerStep core [] specRegions revS config type) ms
        (setRevS ms (if c then (b ,, (t ,, (false ,, (epochMkOdd e ,, (false ,, (ir ,, (b ,, (t ,, tt))))))))
                     else (b ,, (t ,, (c ,, (e ,, (false ,, (ir ,, (sa ,, (st ,, tt)))))))))) Zmod.zero.
  Proof.
    intros env ms b t c e ist ir sa st Ex Hev.
    rewrite SemAction_iff_evalActionPropGen.
    unfold SpecRevoker.specRevokerStep; cbn [evalActionPropGen].
    srev_lens Ex; rewrite ?evalExpr_Var.
    match goal with |- context [if ?cd then _ else _] =>
      replace cd with false by (symmetry; exact Hev) end.
    srev_cbn.
    srev_lens Ex; srev_lens Ex; rewrite ?evalExpr_Var.
    destruct c.
    - srev_cbn.
      srev_lens Ex; srev_lens Ex; srev_lens Ex; srev_lens Ex; srev_lens Ex; srev_lens Ex.
      split; reflexivity.
    - srev_cbn.
      split; reflexivity.
  Qed.

  (* Odd epoch and scanAddr at the sweep's top: the sweep completes *)
  Lemma specRevStep_done :
    forall env (ms : TS MS) b t c e ist ir sa st,
      specRevStateA ms = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, tt)))))))) ->
      epochOdd e = true -> scanDone sa st = true ->
      SemAction env (@SpecRevoker.specRevokerStep core [] specRegions revS config type) ms
        (setRevS ms (b ,, (t ,, (c ,, (epochInc e ,, ((if ir then true else ist) ,, (ir ,, (sa ,, (st ,, tt))))))))) Zmod.zero.
  Proof.
    intros env ms b t c e ist ir sa st Ex Hodd Hdone.
    rewrite SemAction_iff_evalActionPropGen.
    unfold SpecRevoker.specRevokerStep; cbn [evalActionPropGen].
    srev_lens Ex; rewrite ?evalExpr_Var.
    match goal with |- context [if ?cd then _ else _] =>
      replace cd with true by (symmetry; exact Hodd) end.
    srev_cbn.
    srev_lens Ex; srev_lens Ex; rewrite ?evalExpr_Var.
    match goal with |- context [if ?cd then _ else _] =>
      replace cd with false by (change (false = negb (scanDone sa st)); rewrite Hdone; reflexivity) end.
    srev_cbn.
    srev_lens Ex; srev_lens Ex; rewrite ?evalExpr_Var.
    destruct ir.
    - srev_cbn; srev_lens Ex.
      split; reflexivity.
    - srev_cbn.
      split; reflexivity.
  Qed.
  (* Odd epoch and scanAddr below the sweep's top, and the position needs no write: the spec
   * reads the cap (and its rev bit when it needs a check) and moves on *)
  Lemma specRevStep_scan :
    forall initLine fwcs env (ms : TS MS) b t c e ist ir sa st,
      SpecEnvOK core initLine specRegions fwcs env ->
      specRevStateA ms = mkRev8 core b t c e ist ir sa st ->
      epochOdd e = true -> scanDone sa st = false ->
      lineKind specRegions (lineOf false (scanFull sa)) = Some true ->
      lineUnique specRegions (lineOf false (scanFull sa)) ->
      (capNeedsCheck config (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz) = true ->
       lineKind specRegions
         (lineOf false (revByteAddrOf config (capBase (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)))) = Some true /\
       lineUnique specRegions
         (lineOf false (revByteAddrOf config (capBase (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)))) /\
       revBitOf core config pre post revBase revPfB revPfA initLine ms
         (capBase (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)) = false) ->
      exists ms1, ReadFrameS core specRegions ms ms1 /\
        SemAction env (@SpecRevoker.specRevokerStep core [] specRegions revS config type) ms
          (setRevS ms1 (mkRev8 core b t c e ist ir (scanNext sa) st)) Zmod.zero.
  Proof.
    intros initLine fwcs env ms b t c e ist ir sa st Henv Ex Hodd Hnd Hk Hu Hck.
    assert (HP : evalActionPropGen env (@SpecRevoker.specRevokerStep core [] specRegions revS config type) ms
                   (fun ms' v => (exists ms1, ReadFrameS core specRegions ms ms1 /\
                                    ms' = setRevS ms1 (mkRev8 core b t c e ist ir (scanNext sa) st)) /\ v = Zmod.zero)).
    { unfold SpecRevoker.specRevokerStep; cbn [evalActionPropGen].
      srev_lens Ex; rewrite ?evalExpr_Var.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with true by (symmetry; exact Hodd) end.
      srev_cbn.
      srev_lens Ex; srev_lens Ex; rewrite ?evalExpr_Var.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with true by (change (true = negb (scanDone sa st)); rewrite Hnd; reflexivity) end.
      srev_cbn.
      apply (specMemRead_wp core initLine _ _ specRegions fwcs env ms); [exact Henv | exact Hk | exact Hu |].
      intros ms1 Hfr1; cbv beta.
      assert (Ex1 : specRevStateA ms1 = mkRev8 core b t c e ist ir sa st).
      { rewrite <- Ex; exact (regionStateAt_readFrame core specRegions (length pre) sRevR pfS ms ms1 Hfr1 I). }
      apply evalActionPropGen_toAction; cbv beta.
      srev_cbn.
      match goal with |- context [if ?cd then _ else _] =>
        replace cd with (capNeedsCheck config (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz))
          by reflexivity end.
      destruct (capNeedsCheck config (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)) eqn:Ech.
      - (* a check: the rev bit is read; it is 0 *)
        destruct (Hck eq_refl) as [Hk2 [Hu2 Hrb]].
        srev_cbn.
        unfold readRevBit; cbn [evalActionPropGen].
        apply evalActionPropGen_toAction; cbv beta.
        srev_cbn.
        apply (specMemRead_wp core initLine _ _ specRegions fwcs env ms1); [exact Henv | exact Hk2 | exact Hu2 |].
        intros ms2 Hfr2; cbv beta.
        assert (Ex2 : specRevStateA ms2 = mkRev8 core b t c e ist ir sa st).
        { rewrite <- Ex1; exact (regionStateAt_readFrame core specRegions (length pre) sRevR pfS ms1 ms2 Hfr2 I). }
        srev_cbn.
        match goal with |- context [if ?cd then _ else _] =>
          replace cd with (revBitOf core config pre post revBase revPfB revPfA initLine ms1
                             (capBase (memValAt core pre post revBase revPfB revPfA initLine ms (scanFull sa) capSz)))
            by reflexivity end.
        rewrite (revBitOf_ext core config pre post revBase revPfB revPfA initLine ms ms1 _
                   (lineContent_readFrame core initLine specRegions ms ms1 Hfr1)), Hrb.
        srev_cbn.
        srev_lens Ex2.
        split; [exists ms2; split; [exact (ReadFrameS_trans core specRegions _ _ _ Hfr1 Hfr2) | reflexivity] | reflexivity].
      - (* no check *)
        srev_cbn.
        srev_lens Ex1.
        split; [exists ms1; split; [exact Hfr1 | reflexivity] | reflexivity]. }
    destruct (evalActionPropGen_to_SemAction _ _ _ HP) as [ms' [v [Hsem [[ms1 [Hfr ->]] ->]]]].
    exists ms1; split; [exact Hfr | exact Hsem].
  Qed.
End SpecRevLens.

(* --- 2d. Small Facts --- *)

Section ZmodRing.
  Variable m : Z.
  Add Ring zmodRing : (Zmod.ring_theory m).

  Lemma Zmod_sub_add_one : forall (x : Zmod m), Zmod.add (Zmod.sub x Zmod.one) Zmod.one = x.
  Proof. intros x; ring. Qed.
End ZmodRing.

(* The spec and impl revoker regions sit at the same addresses, both CustomMem *)
Lemma lineKind_revSwap :
  forall core pre post revBase revPfB revPfA L,
    lineKind (specRegionsOf core pre post revBase revPfB revPfA) L =
    lineKind (implRegionsOf core pre post revBase revPfB revPfA) L.
Proof.
  intros core pre post revBase revPfB revPfA L; unfold specRegionsOf, implRegionsOf.
  induction pre as [| r rs IH]; cbn [app lineKind]; [reflexivity | rewrite IH; reflexivity].
Qed.

(* --- 3. The Revoker Steps against the Relation --- *)

Section RevSteps.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf core pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf core pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance core specRegions.
  Variable clint : @ClintInstance core implRegions.
  Variable plicS : @PlicInstance core (S (S (length (collectIrqActions core specRegions)))) specRegions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions core implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation SState := (SpecState core pcAddrInit specRegions).
  Local Abbreviation NPMI := (Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation NPMS := (Spec.np_mem core pcAddrInit specRegions).
  Local Abbreviation revI := (revImplOf core pre post revBase revPfB revPfA).

  Local Abbreviation iMemA := (iMem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA := (iMemSt core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA := (iRequester core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRevPhaseA := (iRevPhase core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem core pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation revOfRA := (revOfR core pre post revBase revPfB revPfA).
  Local Abbreviation setRevRA := (setRevR core pre post revBase revPfB revPfA).

  Local Abbreviation ACC := (AccessRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation MEMC := (MemRelC core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation PWS := (PortsWriteStaged core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation STEPOK := (StepOK core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).

  Lemma iMem_write : forall (s1 : IState) m', iMemA (writeSubTreeState NPMI s1 m') = m'.
  Proof. reflexivity. Qed.

  Lemma iMem_read : forall (s1 : IState), readSubTreeState NPMI s1 = iMemA s1.
  Proof. reflexivity. Qed.

  (* --- 3a. The Access in Flight When the Memory Is Ready or Answers the Revoker --- *)

  Lemma PortsWriteStaged_npw :
    forall (s1 : IState) L rq,
      lineKind implRegions L = Some true -> PWS L rq s1 -> noPortWriteB core implRegions (iRegionsA s1) = false.
  Proof.
    intros s1 L rq Hk Hw.
    apply (noPortWriteB_false core L rq implRegions _ Hk).
    unfold PortsWriteStaged in Hw; revert Hw; apply AllPorts_impl.
    intros r y [_ Hy] Hr; rewrite Hr in Hy; exact Hy.
  Qed.

  (* `state` idle and no write staged: nothing is in flight *)
  Lemma AccessRel_rdy_none :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 -> msIdle (iMemStA s1) = true -> noPortWriteB core implRegions (iRegionsA s1) = true ->
      g_acc core pcAddrInit g = AccNone.
  Proof.
    intros g s1 s2 Ha Hidle Hnpw.
    destruct (msIdle_excl _ Hidle) as [N1 [N2 [N3 N4]]].
    unfold AccessRel in Ha.
    destruct (g_acc core pcAddrInit g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      [reflexivity | ..]; exfalso;
      unfold WrStageRel, RdStageRel in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      first
        [ match goal with H : ?f ?x = true, N : ?f ?x = false |- _ => rewrite N in H; discriminate H end
        | match goal with
          | Hk : lineKind _ _ = Some true, Hw : PortsWriteStaged _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
              rewrite (PortsWriteStaged_npw _ _ _ Hk Hw) in Hnpw; discriminate Hnpw
          end ].
  Qed.

  (* A response ready for the revoker is the revoker's cap read or rev-bit read *)
  Lemma AccessRel_rpReady_rev :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 -> msReadRpReady (iMemStA s1) = true -> isReqRevoker (iRequesterA s1) = true ->
      (g_acc core pcAddrInit g = AccRevCap (RdReady (msReadRpReadyV (iMemStA s1))) /\ rpWaitCapRp (iRevPhaseA s1) = true) \/
      (g_acc core pcAddrInit g = AccRevBit (RdReady (msReadRpReadyV (iMemStA s1))) /\ rpWaitRevBitRp (iRevPhaseA s1) = true).
  Proof.
    intros g s1 s2 Ha Hr Hq.
    destruct (msReadRpReady_excl _ Hr) as [N1 [N2 [N3 N4]]].
    pose proof (isReqRevoker_excl _ Hq) as Nq.
    unfold AccessRel in Ha.
    destruct (g_acc core pcAddrInit g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      unfold WrStageRel, RdStageRel in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (match goal with H : (if ?c then _ else _) |- _ => destruct c end;
           repeat match goal with H : _ /\ _ |- _ => destruct H end);
      try (exfalso; match goal with H : ?f ?x = true, N : ?f ?x = false |- _ => rewrite N in H; discriminate H end).
    - left; split; [match goal with H : msReadRpReadyV _ = _ |- _ => rewrite H; reflexivity end | assumption].
    - right; split; [match goal with H : msReadRpReadyV _ = _ |- _ => rewrite H; reflexivity end | assumption].
  Qed.

  (* --- 3b. The Memory Relation When Only the Impl Revoker Changes --- *)

  Lemma MemRelC_revImpl :
    forall g g' (s1 s1' : IState) (s2 : SState) mr x',
      iRegionsA s1 = mr ->
      iRegionsA s1' = setRevRA mr x' ->
      RevRel core (g_revOff core pcAddrInit g') (specRevState core pre post revBase revPfB revPfA (sMemA s2)) x' ->
      MEMC g s1 s2 -> MEMC g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 mr x' E0 E1 HR Hm.
    unfold MemRelC, MemRel, DevInv in *.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    rewrite E1; rewrite E0 in Hpre, Hcl, Hpl, Hci, Hpi.
    unfold setRevR, implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_upd_other (implMemRegionTree core) (length pre))
      by (intros E; first [ exact (clint_ne_rev core pre post revBase revPfB revPfA clint (eq_sym E))
                          | exact (plic_ne_rev core pre post revBase revPfB revPfA plic (eq_sym E)) ]).
    rewrite regionStateAt_updRegionStateAt; cbn [Fst].
    refine (conj (conj _ (conj Hcl (conj Hpl HR))) (conj (conj Hci Hpi) Hsnap)).
    apply MemRelPre_upd_rev_impl; exact Hpre.
  Qed.

  Local Abbreviation iRevScanBaseA := (iRevScanBase core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).

  Lemma iRev_eq : forall (s1 : IState), iRevA s1 = revOfRA (iRegionsA s1).
  Proof. reflexivity. Qed.

  Lemma iRegions_eq : forall (s1 : IState), iRegionsA s1 = (iMemA s1).(Fst).
  Proof. reflexivity. Qed.

  (* --- 3c. WaitRevBitRq: the rev-bit read is issued; the spec stutters --- *)

  Lemma stepOK_waitRevBitRq :
    STEPOK (@implRevokerWaitRevBitRqStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions revI type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implRevokerWaitRevBitRqStepSys in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    remember (revOfRA mr) as x eqn:Ex; symmetry in Ex.
    destruct x as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
    destruct (waitRevBitRq_char core config pre post revBase revPfB revPfA _ mr mst mrq mrp m' _
                b t c e ist ir sa st ph sc sb sh Ex Hm')
      as [-> | [Hph [Hidle [Hnpw [st' [rq' [ph' [-> [Hrq [HrqV [Hreq Hph']]]]]]]]]]].
    - exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM].
    - pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
      assert (ER : iRevA s1 = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt))))))))))))).
      { rewrite iRev_eq, iRegions_eq, EM; exact Ex. }
      assert (EM' : iMemA s1' = (setRevRA mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,,
                                 (st' ,, (rq' ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
      assert (ER' : iRevA s1' = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt))))))))))))).
      { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
      assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
      { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
      assert (Hacc0 : g_acc core pcAddrInit g = AccNone).
      { apply (AccessRel_rdy_none g s1 s2 Ha).
        - unfold iMemSt; rewrite EM; exact Hidle.
        - rewrite iRegions_eq, EM; exact Hnpw. }
      unfold AccessRel in Ha; rewrite Hacc0 in Ha.
      destruct Ha as [Hi0 [Hrp0 [Hq0 [Hoff0 [Hdm0 [Hrn0 Hsec0]]]]]].
      exists s2; split; [apply NilAction; reflexivity |].
      exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g) (g_revOff core pcAddrInit g) (g_d2aFo core pcAddrInit g) (AccRevBit (RdPend false))).
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
      + cbn [g_acc]; rewrite Hacc0; reflexivity.
      + eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                     | rewrite iRegions_eq, EM'; reflexivity | |].
        * destruct Hm as [[_ [_ [_ Hrv]]] _].
          change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
          rewrite ER in Hrv; exact Hrv.
        * exact Hm.
      + unfold AccessRel; cbn [g_acc g_revOff].
        unfold RdStageRel, PortsQuiet, dmNotAccessing in *; cbv zeta.
        unfold iMemSt, iRequester, iReadRp; rewrite EM'; cbn [Fst Snd].
        unfold iRevPhase, iRevScanBase; rewrite ER'; cbn [Fst Snd].
        unfold iReadRp in Hrp0; rewrite EM in Hrp0; cbn [Fst Snd] in Hrp0.
        rewrite HP.
        split; [split; [exact Hrq | split; [exact HrqV | split; [exact Hrp0 | exact Hq0]]] |].
        split; [exact Hreq | split; [exact Hph' | split; [rewrite E1; exact Hdm0 | split; [exact Hoff0 | exact Hsec0]]]].
      + unfold RevokerRel in Hrk |- *; cbn [g_acc].
        destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
        unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in K1, K2, K3, K4 |- *.
        rewrite ER'; rewrite ER in K1, K2, K3, K4; cbn [Fst Snd] in K1, K2, K3, K4 |- *.
        destruct (rpWaitRevBitRq_excl _ Hph) as [P1 _].
        destruct (rpWaitRevBitRp_excl _ Hph') as [_ [_ [_ Q4]]].
        split; [intros _; exact (K1 P1) |].
        split; [intros _; exact (K2 (rpCheck_waitRevBitRq _ Hph)) |].
        split; [intros _ Hsn; exact (K3 (rpCheck_waitRevBitRq _ Hph) Hsn) |].
        split; [intros Hwc; rewrite Q4 in Hwc; discriminate Hwc | exact I].
  Qed.

  Local Abbreviation iReadRpA := (iReadRp core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation revNotReadingA := (revNotReading core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).

  (* The revoker's accesses in flight go with its phase *)
  Lemma AccessRel_revPhase :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 ->
      match g_acc core pcAddrInit g with
      | AccRevCap _ => rpWaitCapRp (iRevPhaseA s1) = true
      | AccRevBit _ => rpWaitRevBitRp (iRevPhaseA s1) = true
      | AccRevWrite _ _ _ => rpIdle (iRevPhaseA s1) = true
      | _ => True
      end.
  Proof.
    intros g s1 s2 Ha; unfold AccessRel in Ha.
    destruct (g_acc core pcAddrInit g); try exact I; tauto.
  Qed.

  (* A core access in flight survives a change of the revoker registers that keeps the revoker
   * from reading *)
  Lemma AccessRel_coreAcc_revRegs :
    forall g (s1 s1' : IState) (s2 : SState),
      (forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)) ->
      iMemStA s1' = iMemStA s1 -> iReadRpA s1' = iReadRpA s1 -> iRequesterA s1' = iRequesterA s1 ->
      iDmStA s1' = iDmStA s1 -> revNotReadingA s1' ->
      match g_acc core pcAddrInit g with AccRevCap _ | AccRevBit _ | AccRevWrite _ _ _ => False | _ => True end ->
      ACC g s1 s2 -> ACC g s1' s2.
  Proof.
    intros g s1 s1' s2 HP Emst Erp Ereq Edm Hrn Hcore Ha.
    unfold AccessRel in *.
    revert Ha.
    destruct (g_acc core pcAddrInit g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      try (exfalso; exact Hcore); intros Ha;
      unfold WrStageRel, RdStageRel, PortsQuiet, PortsReadStaged, PortsReadOut, PortsWriteStaged, dmNotAccessing in *;
      cbv beta iota zeta in *;
      rewrite ?HP, ?Emst, ?Erp, ?Ereq, ?Edm;
      (let rec go H :=
         lazymatch goal with
         | |- revNotReadingA s1' => exact Hrn
         | |- _ /\ _ =>
             let H1 := fresh "H" in let H2 := fresh "H" in
             destruct H as [H1 H2]; split; [go H1 | go H2]
         | |- _ => exact H
         end in
       go Ha).
  Qed.

  Lemma RevAccRel_coreAcc :
    forall g (s1 : IState) (s2 : SState),
      match g_acc core pcAddrInit g with AccRevCap _ | AccRevBit _ | AccRevWrite _ _ _ => False | _ => True end ->
      RevAccRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity
        mulStages divStages mulDivMode config pre post revBase revPfB revPfA initLine g s1 s2.
  Proof.
    intros g s1 s2 Hcore; unfold RevAccRel.
    destruct (g_acc core pcAddrInit g) as [| | | | [] | [] |]; try (exfalso; exact Hcore); exact I.
  Qed.

  (* --- 3d. WriteCap: the untagged cap is handed to the memory, or the position is retried --- *)

  Lemma stepOK_writeCap :
    STEPOK (@implRevokerWriteCapStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions revI type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implRevokerWriteCapStepSys in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    remember (revOfRA mr) as x eqn:Ex; symmetry in Ex.
    destruct x as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh) by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
    destruct (writeCap_char core pre post revBase revPfB revPfA _ mr mst mrq mrp m' _
                b t c e ist ir sa st ph sc sb sh Ex Hm')
      as [-> | [[Hph [Hsh [ph' [Hph' ->]]]] | [Hph [Hsh [Hidle [Hnpw [st' [ph' [-> [Hwr [HwrV Hph']]]]]]]]]]].
    - exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM].
    - (* a store hit the position: retry it (the spec stutters, the ghost is kept) *)
      assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir sa st ph' sc sb sh) ,, (mst ,, (mrq ,, (mrp ,, tt)))))
        by (rewrite E1; apply iMem_write).
      assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir sa st ph' sc sb sh).
      { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
      assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
      { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
      destruct (rpWriteCap_excl _ Hph) as [P1 [P2 [P3 P4]]].
      destruct (rpIdle_excl _ Hph') as [Q1 [_ [Q3 Q4]]].
      assert (Hcore : match g_acc core pcAddrInit g with AccRevCap _ | AccRevBit _ | AccRevWrite _ _ _ => False | _ => True end).
      { pose proof (AccessRel_revPhase g s1 s2 Ha) as Hp.
        unfold iRevPhase in Hp; rewrite ER in Hp; cbn [mkRev12 Fst Snd] in Hp.
        destruct (g_acc core pcAddrInit g); cbv beta iota in Hp |- *; try exact I; congruence. }
      exists s2; split; [apply NilAction; reflexivity |].
      exists g.
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
      + eapply (MemRelC_revImpl g g s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                   | rewrite iRegions_eq, EM'; reflexivity | |].
        * destruct Hm as [[_ [_ [_ Hrv]]] _].
          change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
          rewrite ER in Hrv; exact (RevRel_implRegs core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv).
        * exact Hm.
      + apply (AccessRel_coreAcc_revRegs g s1 s1' s2 HP); try exact Hcore; try exact Ha.
        * unfold iMemSt; rewrite EM', EM; reflexivity.
        * unfold iReadRp; rewrite EM', EM; reflexivity.
        * unfold iRequester; rewrite EM', EM; reflexivity.
        * rewrite E1; reflexivity.
        * unfold revNotReading, iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd]; split; assumption.
      + unfold RevokerRel; unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        split; [rewrite Hph'; intros Hc'; discriminate Hc' |].
        unfold rpCheck; rewrite Q3, Q4, (proj1 (proj2 (rpIdle_excl _ Hph'))).
        split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
        split; [intros Hc'; discriminate Hc' |].
        exact (RevAccRel_coreAcc g s1' s2 Hcore).
    - (* the write is handed to the memory: the impl moves one position ahead *)
      assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh) ,,
                                 (st' ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
      assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh).
      { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
      assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
      { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
      assert (Hacc0 : g_acc core pcAddrInit g = AccNone).
      { apply (AccessRel_rdy_none g s1 s2 Ha).
        - unfold iMemSt; rewrite EM; exact Hidle.
        - rewrite iRegions_eq, EM; exact Hnpw. }
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Hacc0 in Ha'.
      destruct Ha' as [Hi0 [Hrp0 [Hq0 [Hoff0 [Hdm0 [Hrn0 Hsec0]]]]]].
      destruct (rpWriteCap_excl _ Hph) as [P1 _].
      destruct (rpIdle_excl _ Hph') as [Q1 [_ [Q3 Q4]]].
      unfold RevokerRel in Hrk; destruct Hrk as [K1 [K2 [K3 [K4 _]]]].
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in K1, K2, K3, K4.
      rewrite ER in K1, K2, K3, K4; cbn [mkRev12 Fst Snd] in K1, K2, K3, K4.
      specialize (K1 P1).
      destruct (K2 (rpCheck_writeCap _ Hph)) as [Hnc [Hsb _]].
      specialize (K3 (rpCheck_writeCap _ Hph) Hsh).
      change (memValAt core pre post revBase revPfB revPfA initLine (sMemA s2) (scanFull sa) capSz = sc) in K3.
      specialize (K4 Hph Hsh).
      pose proof Hm as Hm0.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] Hdi].
      change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
      rewrite ER, Hoff0 in Hrv.
      pose proof (RevRel_scan core _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv) as Esa; cbn [revOffAddr] in Esa.
      exists s2; split; [apply NilAction; reflexivity |].
      exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                RevImplAhead (g_d2aFo core pcAddrInit g)
                (AccRevWrite (scanFull sa) (disassembleW (scanFull sa) (untagCap sc) capSz) (WrPend false))).
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
      + cbn [g_acc]; rewrite Hacc0; reflexivity.
      + eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                   | rewrite iRegions_eq, EM'; reflexivity | |].
        * cbn [g_revOff].
          apply (RevRel_advance core RevEq RevImplAhead _ b t c e ist ir sa st ph sc sb sh ph' sc sb sh Hrv).
          cbn [revOffAddr]; rewrite <- Esa; apply scanNext_eq.
        * exact Hm0.
      + unfold AccessRel; cbn [g_acc g_revOff].
        unfold WrStageRel, PortsQuiet, dmNotAccessing in *.
        unfold iMemSt, iReadRp; rewrite EM'; cbn [Fst Snd].
        unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        unfold iReadRp in Hrp0; rewrite EM in Hrp0; cbn [Fst Snd] in Hrp0.
        rewrite HP.
        split; [split; [exact Hrp0 | split; [exact Hwr | split; [exact HwrV | exact Hq0]]] |].
        split; [exact Hph' | split; [rewrite E1; exact Hdm0 | split; [reflexivity | exact Hsec0]]].
      + unfold RevokerRel; cbn [g_acc].
        unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        split; [rewrite Hph'; intros Hc'; discriminate Hc' |].
        unfold rpCheck; rewrite Q3, Q4, (proj1 (proj2 (rpIdle_excl _ Hph'))).
        split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
        split; [intros Hc'; discriminate Hc' |].
        unfold RevAccRel, RevWriteOK; cbn [g_acc].
        exists sa.
        unfold iRevArch; rewrite ER'.
        split; [cbn; apply scanNext_eq |].
        split; [reflexivity |].
        split; [exact K1 |].
        rewrite K3.
        split; [exact Hnc |].
        split; [rewrite <- Hsb; exact K4 | reflexivity].
  Qed.

  (* --- 3e. Idle: the cap read is issued, or the impl and the spec step together --- *)

  Local Abbreviation revS := (revSpecOf core pre post revBase revPfB revPfA).
  Local Abbreviation setRevSA := (setRevS core pre post revBase revPfB revPfA).
  Local Abbreviation specRevStateA := (specRevState core pre post revBase revPfB revPfA).
  Local Abbreviation envS := (specEnv core pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (map snd (@spec core pcAddrInit config specRegions clintS revS plicS type)).
  Local Abbreviation RELG := (RefRelG core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).
  Local Abbreviation sRevR := (specRevRegion core revBase revPfB revPfA).
  Local Abbreviation pfS := (nth_error_app_cons_len pre sRevR post).

  Lemma In_specRevokerStep : In (@Spec.specRevokerStep core pcAddrInit config specRegions revS type) specActs.
  Proof.
    rewrite (map_snd_specMod core pcAddrInit config specRegions clintS revS plicS).
    apply in_or_app; left; cbn [In]; right; left; reflexivity.
  Qed.

  Lemma specClintState_setRevS :
    forall ms x, specClintState core pre post revBase revPfB revPfA clintS (setRevSA ms x) =
                 specClintState core pre post revBase revPfB revPfA clintS ms.
  Proof.
    intros ms x; unfold specClintState, setRevS.
    rewrite regionStateAt_upd_other; [reflexivity |].
    intros E; exact (clintS_ne_rev core pre post revBase revPfB revPfA clintS (eq_sym E)).
  Qed.

  Lemma specPlicState_setRevS :
    forall ms x, specPlicState core pre post revBase revPfB revPfA plicS (setRevSA ms x) =
                 specPlicState core pre post revBase revPfB revPfA plicS ms.
  Proof.
    intros ms x; unfold specPlicState, setRevS.
    rewrite regionStateAt_upd_other; [reflexivity |].
    intros E; exact (plicS_ne_rev core pre post revBase revPfB revPfA plicS (eq_sym E)).
  Qed.

  Lemma specClintState_readFrame :
    forall ms ms1, ReadFrameS core specRegions ms ms1 ->
      specClintState core pre post revBase revPfB revPfA clintS ms1 = specClintState core pre post revBase revPfB revPfA clintS ms.
  Proof. intros ms ms1 H; exact (regionStateAt_readFrame core specRegions (clintIdx clintS) (clintRegion clintS) (pfClint clintS) _ _ H I). Qed.

  Lemma specPlicState_readFrame :
    forall ms ms1, ReadFrameS core specRegions ms ms1 ->
      specPlicState core pre post revBase revPfB revPfA plicS ms1 = specPlicState core pre post revBase revPfB revPfA plicS ms.
  Proof. intros ms ms1 H; exact (regionStateAt_readFrame core specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) _ _ H I). Qed.

  (* The impl revoker and the spec revoker change together, after spec data reads *)
  Lemma MemRelC_revLock :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mr x' ms1 xs',
      iRegionsA s1 = mr ->
      iRegionsA s1' = setRevRA mr x' ->
      ReadFrameS core specRegions (sMemA s2) ms1 ->
      sMemA s2' = setRevSA ms1 xs' ->
      RevRel core (g_revOff core pcAddrInit g') xs' x' ->
      MEMC g s1 s2 -> MEMC g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mr x' ms1 xs' E0 E1 Hfr E2 HR Hm.
    unfold MemRelC, MemRel, DevInv in *.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    rewrite E1, E2; rewrite E0 in Hpre, Hcl, Hpl, Hci, Hpi.
    rewrite specClintState_setRevS, specPlicState_setRevS, specRevState_setRevS.
    rewrite (specClintState_readFrame _ _ Hfr), (specPlicState_readFrame _ _ Hfr).
    unfold setRevR, implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_upd_other (implMemRegionTree core) (length pre))
      by (intros E; first [ exact (clint_ne_rev core pre post revBase revPfB revPfA clint (eq_sym E))
                          | exact (plic_ne_rev core pre post revBase revPfB revPfA plic (eq_sym E)) ]).
    rewrite regionStateAt_updRegionStateAt; cbn [Fst].
    refine (conj (conj _ (conj Hcl (conj Hpl HR))) (conj (conj Hci Hpi) _)).
    - unfold setRevS; apply MemRelPre_upd_rev_spec; apply MemRelPre_upd_rev_impl.
      exact (MemRelPre_readFrame core _ _ _ _ _ _ _ _ _ _ Hfr Hpre).
    - exact (SnapshotOK_upd core specRegions fwcs (length pre) sRevR pfS ms1 xs' I
               (SnapshotOK_readFrame core specRegions fwcs _ _ Hfr Hsnap)).
  Qed.

  Lemma LatchRel_setRevS :
    forall g (s2 : SState) ms1 x,
      ReadFrameS core specRegions (sMemA s2) ms1 ->
      LatchRel core pcAddrInit pre post revBase revPfB revPfA clintS plicS g s2 ->
      LatchRel core pcAddrInit pre post revBase revPfB revPfA clintS plicS g (writeSubTreeState NPMS s2 (setRevSA ms1 x)).
  Proof.
    intros g s2 ms1 x Hfr Hl; unfold LatchRel, sClint, sPlic in *.
    intros e0 Hin; destruct (Hl e0 Hin) as [L1 L2]; split.
    - intros Hs0; apply L1; revert Hs0.
      change (sMemA (writeSubTreeState NPMS s2 (setRevSA ms1 x))) with (setRevSA ms1 x).
      rewrite specClintState_setRevS, (specClintState_readFrame _ _ Hfr); exact (fun H => H).
    - intros Hp0; apply L2; revert Hp0.
      change (sMemA (writeSubTreeState NPMS s2 (setRevSA ms1 x))) with (setRevSA ms1 x).
      rewrite specPlicState_setRevS, (specPlicState_readFrame _ _ Hfr); exact (fun H => H).
  Qed.

  (* The revoker idle with no write waiting: a core access (or none) is in flight, at no offset *)
  Lemma AccessRel_idle_core :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 -> rpIdle (iRevPhaseA s1) = true -> msWriteRq (iMemStA s1) = false ->
      noPortWriteB core implRegions (iRegionsA s1) = true ->
      g_revOff core pcAddrInit g = RevEq /\
      match g_acc core pcAddrInit g with AccRevCap _ | AccRevBit _ | AccRevWrite _ _ _ => False | _ => True end.
  Proof.
    intros g s1 s2 Ha Hph Hwr Hnpw.
    destruct (rpIdle_excl _ Hph) as [N1 [N2 [N3 N4]]].
    unfold AccessRel in Ha.
    destruct (g_acc core pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt [b0|b0]];
      unfold WrStageRel in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      first
        [ split; [assumption | exact I]
        | exfalso;
          first
            [ match goal with H : ?f ?x = true, N : ?f ?x = false |- _ => rewrite N in H; discriminate H end
            | match goal with
              | Hk : lineKind _ _ = Some true, Hw : PortsWriteStaged _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
                  rewrite (PortsWriteStaged_npw _ _ _ Hk Hw) in Hnpw; discriminate Hnpw
              end ] ].
  Qed.

  (* The impl revoker takes an architectural step from Idle and the spec revoker takes the same step *)
  Lemma idle_lock :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp b t c e ist ir sa st ph sc sb sh
           b' t' c' e' ist' ir' sa' st',
      RELG g s1 s2 ->
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      revOfRA mr = mkRev12 core b t c e ist ir sa st ph sc sb sh ->
      rpIdle ph = true -> msWriteRq mst = false -> noPortWriteB core implRegions mr = true ->
      s1' = writeSubTreeState NPMI s1
              (setRevRA mr (mkRev12 core b' t' c' e' ist' ir' sa' st' ph sc sb sh) ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      (specRevStateA (sMemA s2) = mkRev8 core b t c e ist ir sa st ->
       forall env, SemAction env (@SpecRevoker.specRevokerStep core [] specRegions revS config type) (sMemA s2)
                     (setRevSA (sMemA s2) (mkRev8 core b' t' c' e' ist' ir' sa' st')) Zmod.zero) ->
      exists s2', SemActions envS specActs s2 s2' /\ exists g', RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh b' t' c' e' ist' ir' sa' st'
           Hg EM Ex Hph Hwr Hnpw E1 Hspec.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    destruct (rpIdle_excl _ Hph) as [Q1 [Q2 [Q3 Q4]]].
    assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh)
      by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
    assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b' t' c' e' ist' ir' sa' st' ph sc sb sh) ,,
                               (mst ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
    assert (ER' : iRevA s1' = mkRev12 core b' t' c' e' ist' ir' sa' st' ph sc sb sh).
    { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
    assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
    { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
    assert (Hph1 : rpIdle (iRevPhaseA s1) = true) by (unfold iRevPhase; rewrite ER; exact Hph).
    assert (Hwr1 : msWriteRq (iMemStA s1) = false) by (unfold iMemSt; rewrite EM; exact Hwr).
    assert (Hnpw1 : noPortWriteB core implRegions (iRegionsA s1) = true) by (rewrite iRegions_eq, EM; exact Hnpw).
    destruct (AccessRel_idle_core g s1 s2 Ha Hph1 Hwr1 Hnpw1) as [Hoff Hcore].
    assert (Hxs : specRevStateA (sMemA s2) = mkRev8 core b t c e ist ir sa st).
    { destruct Hm as [[_ [_ [_ Hrv]]] _].
      change (RevRel core (g_revOff core pcAddrInit g) (specRevStateA (sMemA s2)) (iRevA s1)) in Hrv.
      rewrite ER, Hoff in Hrv.
      exact (RevRel_eq core _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv). }
    exists (writeSubTreeState NPMS s2 (setRevSA (sMemA s2) (mkRev8 core b' t' c' e' ist' ir' sa' st'))).
    split.
    - eapply ConsAction; [apply In_specRevokerStep | | apply NilAction; reflexivity].
      unfold Spec.specRevokerStep.
      apply SemAction_liftAction_iff; eexists; split; [| reflexivity].
      exact (Hspec Hxs _).
    - exists g.
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HP
        | | | | | | | exact Hg].
      + intros L.
        exact (lineContent_upd core initLine specRegions (length pre) sRevR pfS (sMemA s2)
                 (mkRev8 core b' t' c' e' ist' ir' sa' st') L I).
      + exact (FetchViewExt_upd core specRegions (length pre) sRevR pfS (sMemA s2) (mkRev8 core b' t' c' e' ist' ir' sa' st') I).
      + apply (MemRelC_revLock g g s1 s1' s2 _ mr (mkRev12 core b' t' c' e' ist' ir' sa' st' ph sc sb sh)
                 (sMemA s2) (mkRev8 core b' t' c' e' ist' ir' sa' st')).
        * rewrite iRegions_eq, EM; reflexivity.
        * rewrite iRegions_eq, EM'; reflexivity.
        * apply ReadFrameS_refl.
        * reflexivity.
        * rewrite Hoff; unfold RevRel; reflexivity.
        * exact Hm.
      + apply LatchRel_setRevS; [apply ReadFrameS_refl | exact Hl].
      + assert (Ha1 : ACC g s1' s2).
        { apply (AccessRel_coreAcc_revRegs g s1 s1' s2 HP); try exact Hcore; try exact Ha.
          - unfold iMemSt; rewrite EM', EM; reflexivity.
          - unfold iReadRp; rewrite EM', EM; reflexivity.
          - unfold iRequester; rewrite EM', EM; reflexivity.
          - rewrite E1; reflexivity.
          - unfold revNotReading, iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd]; split; assumption. }
        eapply AccessRel_frame with (s1 := s1') (s2 := s2);
          [intros P; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | | exact Ha1].
        intros L.
        exact (lineContent_upd core initLine specRegions (length pre) sRevR pfS (sMemA s2)
                 (mkRev8 core b' t' c' e' ist' ir' sa' st') L I).
      + unfold RevokerRel; unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        split; [rewrite Hph; intros Hc'; discriminate Hc' |].
        unfold rpCheck; rewrite Q2, Q3, Q4.
        split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
        split; [intros Hc'; discriminate Hc' |].
        exact (RevAccRel_coreAcc g s1' _ Hcore).
  Qed.

  Lemma stepOK_idle :
    STEPOK (@implRevokerIdleStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions revI type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implRevokerIdleStepSys in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    remember (revOfRA mr) as x eqn:Ex; symmetry in Ex.
    destruct x as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
    destruct (idle_char core pre post revBase revPfB revPfA _ mr mst mrq mrp m' _
                b t c e ist ir sa st ph sc sb sh Ex Hm')
      as [-> | [[Hnp [Hph [Hodd [Hnd [Hidle [st' [rq' [ph' [-> [Hrq [HrqV [Hreq Hph']]]]]]]]]]]]
              | [[Hnp [Hph [Hodd [Hdone ->]]]]
              | [[Hnp [Hph [Hev [Hc ->]]]]
              | [Hnp [Hph [Hev [Hc ->]]]]]]]].
    - (* nothing changes *)
      exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM].
    - (* the cap read of position sa is sent; the spec stutters *)
      apply andb_prop in Hnp as [_ Hnpw].
      pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hcn Hd Hf Hs Hfr Hw Hrk].
      assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh)
        by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
      assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir sa st ph' sc sb false) ,,
                                 (st' ,, (rq' ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
      assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir sa st ph' sc sb false).
      { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
      assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
      { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
      assert (Hacc0 : g_acc core pcAddrInit g = AccNone).
      { apply (AccessRel_rdy_none g s1 s2 Ha).
        - unfold iMemSt; rewrite EM; exact Hidle.
        - rewrite iRegions_eq, EM; exact Hnpw. }
      pose proof Ha as Ha'; unfold AccessRel in Ha'; rewrite Hacc0 in Ha'.
      destruct Ha' as [Hi0 [Hrp0 [Hq0 [Hoff0 [Hdm0 [Hrn0 Hsec0]]]]]].
      exists s2; split; [apply NilAction; reflexivity |].
      exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                (g_revOff core pcAddrInit g) (g_d2aFo core pcAddrInit g) (AccRevCap (RdPend false))).
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
      + cbn [g_acc]; rewrite Hacc0; reflexivity.
      + eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                     | rewrite iRegions_eq, EM'; reflexivity | |].
        * destruct Hm as [[_ [_ [_ Hrv]]] _].
          change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
          rewrite ER in Hrv; exact Hrv.
        * exact Hm.
      + unfold AccessRel; cbn [g_acc g_revOff].
        unfold RdStageRel, PortsQuiet, dmNotAccessing in *; cbv zeta.
        unfold iMemSt, iRequester, iReadRp; rewrite EM'; cbn [Fst Snd].
        unfold iRevPhase, iScanAddr; rewrite ER'.
        unfold iReadRp in Hrp0; rewrite EM in Hrp0; cbn [Fst Snd] in Hrp0.
        rewrite HP.
        split; [split; [exact Hrq | split; [exact HrqV | split; [exact Hrp0 | exact Hq0]]] |].
        split; [exact Hreq | split; [exact Hph' | split; [rewrite E1; exact Hdm0 | split; [exact Hoff0 | exact Hsec0]]]].
      + unfold RevokerRel; cbn [g_acc].
        unfold iRevArch, iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        destruct (rpWaitCapRp_excl _ Hph') as [Q0 [Q2 [Q3 Q4]]].
        split; [intros _; exact (conj Hodd Hnd) |].
        unfold rpCheck; rewrite Q2, Q3, Q4.
        split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
        split; [intros Hc'; discriminate Hc' | exact I].
    - (* the sweep completes: lockstep *)
      apply andb_prop in Hnp as [Hwr Hnpw]; apply negb_true_iff in Hwr.
      exact (idle_lock g s1 s1' s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh
               b t c (epochInc e) (if ir then true else ist) ir sa st Hg EM Ex Hph Hwr Hnpw E1
               (fun Hx env => specRevStep_done core config pre post revBase revPfB revPfA env (sMemA s2)
                                b t c e ist ir sa st Hx Hodd Hdone)).
    - (* even epoch, kick: lockstep *)
      apply andb_prop in Hnp as [Hwr Hnpw]; apply negb_true_iff in Hwr.
      subst c.
      exact (idle_lock g s1 s1' s2 mr mst mrq mrp b t true e ist ir sa st ph sc sb sh
               b t false (epochMkOdd e) false ir b t Hg EM Ex Hph Hwr Hnpw E1
               (fun Hx env => specRevStep_even core config pre post revBase revPfB revPfA env (sMemA s2)
                                b t true e ist ir sa st Hx Hev)).
    - (* even epoch, no kick: lockstep *)
      apply andb_prop in Hnp as [Hwr Hnpw]; apply negb_true_iff in Hwr.
      subst c.
      exact (idle_lock g s1 s1' s2 mr mst mrq mrp b t false e ist ir sa st ph sc sb sh
               b t false e false ir sa st Hg EM Ex Hph Hwr Hnpw E1
               (fun Hx env => specRevStep_even core config pre post revBase revPfB revPfA env (sMemA s2)
                                b t false e ist ir sa st Hx Hev)).
  Qed.

  (* --- 3f. Committing a Position: the Impl Moves On, the Spec Takes the Position's Step --- *)

  (* The regions are pairwise disjoint, so each line is in at most one region *)
  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Lemma lineUnique_spec : forall L, lineUnique specRegions L.
  Proof. intros L; apply lineUnique_disjoint, Is_true_eq_true; exact Hdisj. Qed.

  (* The whole revocation table is ExternalMem *)
  Hypothesis HrevTab : Is_true (revTableInExternalMem config specRegions).

  (* So the rev byte the sweep reads for a capability that needs a check is ExternalMem *)
  Lemma revTab_needsCheck :
    forall c, capNeedsCheck config c = true ->
      lineKind specRegions (lineOf false (revByteAddrOf config (capBase c))) = Some true.
  Proof.
    intros c Hc; destruct (revByte_needsCheck_inTable config c Hc) as [a [Ha ->]].
    exact (revTab_line config specRegions (Is_true_eq_true _ Hdisj) (Is_true_eq_true _ HrevTab) a Ha).
  Qed.

  Local Abbreviation PQ := (PortsQuiet core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation DNA := (dmNotAccessing core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond core pcAddrInit pre post revBase revPfB revPfA).

  Lemma scan_commit :
    forall g (s1 s1' : IState) (s2 : SState) mr mst mrq mrp b t c e ist ir sa st ph sc sb sh st' ph' ms1,
      RELG g s1 s2 ->
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      revOfRA mr = mkRev12 core b t c e ist ir sa st ph sc sb sh ->
      s1' = writeSubTreeState NPMI s1
              (setRevRA mr (mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh) ,, (st' ,, (mrq ,, (mrp ,, tt)))) ->
      msIdle st' = true -> rpIdle ph' = true ->
      g_revOff core pcAddrInit g = RevEq -> accTakesHead (g_acc core pcAddrInit g) = false ->
      optValid mrp = false -> PQ s1 -> DNA s1 -> optValid (sSecondA s2) = false ->
      ReadFrameS core specRegions (sMemA s2) ms1 ->
      SemAction (subEnv NPMS envS s2) (@SpecRevoker.specRevokerStep core [] specRegions revS config type) (sMemA s2)
        (setRevSA ms1 (mkRev8 core b t c e ist ir (scanNext sa) st)) Zmod.zero ->
      exists s2', SemActions envS specActs s2 s2' /\ exists g', RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh st' ph' ms1
           Hg EM Ex E1 Hidle' Hph' Hoff Htk Hrp Hq Hdm Hsec Hfr Hspec.
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp0 He Ha Hc Hd Hf Hs Hfrt Hw Hrk].
    destruct (rpIdle_excl _ Hph') as [Q1 [Q2 [Q3 Q4]]].
    assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh) ,,
                               (st' ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
    assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh).
    { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
    assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
    { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
    exists (writeSubTreeState NPMS s2 (setRevSA ms1 (mkRev8 core b t c e ist ir (scanNext sa) st))).
    split.
    - eapply ConsAction; [apply In_specRevokerStep | | apply NilAction; reflexivity].
      unfold Spec.specRevokerStep.
      apply SemAction_liftAction_iff; eexists; split; [exact Hspec | reflexivity].
    - exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                RevEq (g_d2aFo core pcAddrInit g) AccNone).
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
        | | | | | | | exact Hg].
      + cbn [g_acc accTakesHead]; rewrite Htk; reflexivity.
      + intros L.
        transitivity (lineContent core initLine specRegions ms1 L).
        * exact (lineContent_upd core initLine specRegions (length pre) sRevR pfS ms1
                   (mkRev8 core b t c e ist ir (scanNext sa) st) L I).
        * exact (lineContent_readFrame core initLine specRegions _ _ Hfr L).
      + exact (FetchViewExt_trans core specRegions _ _ _ (FetchViewExt_readFrame core specRegions _ _ Hfr)
                 (FetchViewExt_upd core specRegions (length pre) sRevR pfS ms1 (mkRev8 core b t c e ist ir (scanNext sa) st) I)).
      + apply (MemRelC_revLock g _ s1 s1' s2 _ mr (mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh) ms1
                 (mkRev8 core b t c e ist ir (scanNext sa) st)).
        * rewrite iRegions_eq, EM; reflexivity.
        * rewrite iRegions_eq, EM'; reflexivity.
        * exact Hfr.
        * reflexivity.
        * cbn [g_revOff]; unfold RevRel; reflexivity.
        * exact Hm.
      + apply LatchRel_setRevS; [exact Hfr | exact Hl].
      + unfold AccessRel; cbn [g_acc g_revOff].
        unfold PortsQuiet, dmNotAccessing, revNotReading in *.
        unfold iMemSt, iReadRp; rewrite EM'; cbn [Fst Snd].
        unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        rewrite HP.
        split; [exact Hidle' |]. split; [exact Hrp |]. split; [exact Hq |]. split; [reflexivity |].
        split; [rewrite E1; exact Hdm |]. split; [split; assumption | exact Hsec].
      + unfold RevokerRel; cbn [g_acc].
        unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        split; [rewrite Hph'; intros Hc'; discriminate Hc' |].
        unfold rpCheck; rewrite Q2, Q3, Q4.
        split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
        split; [intros Hc'; discriminate Hc' | exact I].
  Qed.

  (* --- 3g. WaitCapRp: the Cap Read Answered --- *)

  Lemma waitCapRp_facts :
    forall g (s1 : IState) (s2 : SState) mr mst mrq mrp b t c e ist ir sa st ph sc sb sh,
      RELG g s1 s2 ->
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      revOfRA mr = mkRev12 core b t c e ist ir sa st ph sc sb sh ->
      rpWaitCapRp ph = true -> msReadRpReady mst = true -> isReqRevoker mrq = true ->
      g_acc core pcAddrInit g = AccRevCap (RdReady (msReadRpReadyV mst)) /\
      optValid mrp = false /\ PQ s1 /\ DNA s1 /\ g_revOff core pcAddrInit g <> RevImplAhead /\
      optValid (sSecondA s2) = false /\ epochOdd e = true /\ scanDone sa st = false /\
      (g_revOff core pcAddrInit g = RevSpecAhead -> capNeedsCheck config (msReadRpReadyV mst) = false) /\
      (g_revOff core pcAddrInit g <> RevSpecAhead ->
         lineKind implRegions (lineOf false (scanFull sa)) = Some true /\
         msReadRpReadyV mst = memValAt core pre post revBase revPfB revPfA initLine (sMemA s2) (scanFull sa) capSz).
  Proof.
    intros g s1 s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh Hg EM Ex Hph Hrdy Hreq.
    destruct Hg as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh) by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
    destruct (rpWaitCapRp_excl _ Hph) as [P0 [P2 [P3 P4]]].
    assert (H1 : msReadRpReady (iMemStA s1) = true) by (unfold iMemSt; rewrite EM; exact Hrdy).
    assert (H2 : isReqRevoker (iRequesterA s1) = true) by (unfold iRequester; rewrite EM; exact Hreq).
    assert (Hacc : g_acc core pcAddrInit g = AccRevCap (RdReady (msReadRpReadyV mst))).
    { destruct (AccessRel_rpReady_rev g s1 s2 Ha H1 H2) as [[Ea _] | [_ Hb]].
      - unfold iMemSt in Ea; rewrite EM in Ea; exact Ea.
      - unfold iRevPhase in Hb; rewrite ER in Hb; cbn [mkRev12 Fst Snd] in Hb; rewrite P3 in Hb; discriminate Hb. }
    pose proof Ha as Ha'; unfold AccessRel, RdStageRel in Ha'; rewrite Hacc in Ha'; cbv beta iota zeta in Ha'.
    destruct Ha' as [[_ [_ [Hr3 Hr4]]] [_ [_ [Hdm0 [Hoff0 Hsec0]]]]].
    unfold RevokerRel in Hrk; destruct Hrk as [K1 [_ [_ [_ K5]]]].
    unfold RevAccRel in K5; rewrite Hacc in K5; unfold RevCapOK in K5.
    unfold iRevArch, iRevPhase, iScanAddr in K1, K5; rewrite ER in K1, K5; cbn [mkRev12 Fst Snd] in K1, K5.
    destruct (K1 P0) as [Hodd Hnd].
    unfold iReadRp in Hr3; rewrite EM in Hr3; cbn [Fst Snd] in Hr3.
    split; [exact Hacc |].
    split; [exact Hr3 |]. split; [exact Hr4 |]. split; [exact Hdm0 |]. split; [exact Hoff0 |].
    split; [exact Hsec0 |]. split; [exact Hodd |]. split; [exact Hnd |].
    split.
    - intros E; rewrite E in K5; exact K5.
    - intros E; revert K5; destruct (g_revOff core pcAddrInit g) eqn:Eo; intros K5;
        [exact K5 | exact K5 | exfalso; exact (E eq_refl)].
  Qed.

  Lemma stepOK_waitCapRp :
    STEPOK (@implRevokerWaitCapRpStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions revI type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implRevokerWaitCapRpStepSys in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    remember (revOfRA mr) as x eqn:Ex; symmetry in Ex.
    destruct x as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
    destruct (waitCapRp_char core config pre post revBase revPfB revPfA _ mr mst mrq mrp m' _
                b t c e ist ir sa st ph sc sb sh Ex Hm')
      as [-> | [[Hph [Hrdy [Hreq [Hck [st' [ph' [-> [Hidle' Hph']]]]]]]]
              | [Hph [Hrdy [Hreq [Hck [st' [ph' [-> [Hidle' Hph']]]]]]]]]].
    - (* nothing changes *)
      exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM].
    - (* a check is needed: the cap and its base are saved; the spec stutters *)
      destruct (waitCapRp_facts g s1 s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh Hg EM Ex Hph Hrdy Hreq)
        as [Hacc [Hrp0 [Hq0 [Hdm0 [Hoff0 [Hsec0 [Hodd [Hnd [Hsa Hnsa]]]]]]]]].
      assert (Hoff : g_revOff core pcAddrInit g = RevEq).
      { destruct (g_revOff core pcAddrInit g) eqn:Eo.
        - reflexivity.
        - exfalso; exact (Hoff0 eq_refl).
        - rewrite (Hsa eq_refl) in Hck; discriminate Hck. }
      assert (Hns : g_revOff core pcAddrInit g <> RevSpecAhead) by (rewrite Hoff; discriminate).
      destruct (Hnsa Hns) as [Hlk Hv].
      pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
      assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh)
        by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
      assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir sa st ph' (msReadRpReadyV mst)
                                                 (capBase (msReadRpReadyV mst)) sh) ,,
                                 (st' ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
      assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir sa st ph' (msReadRpReadyV mst) (capBase (msReadRpReadyV mst)) sh).
      { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
      assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
      { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
      destruct (rpWaitRevBitRq_excl _ Hph') as [Q0 [Q1 [Q3 Q4]]].
      exists s2; split; [apply NilAction; reflexivity |].
      exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                (g_revOff core pcAddrInit g) (g_d2aFo core pcAddrInit g) AccNone).
      eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
      + cbn [g_acc accTakesHead]; rewrite Hacc; reflexivity.
      + eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                     | rewrite iRegions_eq, EM'; reflexivity | |].
        * destruct Hm as [[_ [_ [_ Hrv]]] _].
          change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
          rewrite ER in Hrv; exact Hrv.
        * exact Hm.
      + unfold AccessRel; cbn [g_acc g_revOff].
        unfold PortsQuiet, dmNotAccessing, revNotReading in *.
        unfold iMemSt, iReadRp; rewrite EM'; cbn [Fst Snd].
        unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
        rewrite HP.
        split; [exact Hidle' |]. split; [exact Hrp0 |]. split; [exact Hq0 |]. split; [exact Hoff |].
        split; [rewrite E1; exact Hdm0 |]. split; [split; assumption | exact Hsec0].
      + unfold RevokerRel; cbn [g_acc].
        unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr; rewrite ER'; cbn [mkRev12 Fst Snd].
        split; [intros _; exact (conj Hodd Hnd) |].
        split; [intros _; split; [exact Hck | split; [reflexivity | exact Hlk]] |].
        split; [intros _ _; symmetry; exact Hv |].
        split; [intros Hc'; rewrite Q4 in Hc'; discriminate Hc' | exact I].
    - (* no check: the impl moves on *)
      destruct (waitCapRp_facts g s1 s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh Hg EM Ex Hph Hrdy Hreq)
        as [Hacc [Hrp0 [Hq0 [Hdm0 [Hoff0 [Hsec0 [Hodd [Hnd [Hsa Hnsa]]]]]]]]].
      pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
      assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh)
        by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
      destruct (g_revOff core pcAddrInit g) eqn:Eo.
      + (* the spec takes the position's step *)
        destruct (Hnsa ltac:(discriminate)) as [Hlk Hv].
        assert (Hxs : specRevStateA (sMemA s2) = mkRev8 core b t c e ist ir sa st).
        { destruct Hm as [[_ [_ [_ Hrv]]] _].
          change (RevRel core (g_revOff core pcAddrInit g) (specRevStateA (sMemA s2)) (iRevA s1)) in Hrv.
          rewrite ER, Eo in Hrv.
          exact (RevRel_eq core _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv). }
        assert (Hk1 : lineKind specRegions (lineOf false (scanFull sa)) = Some true)
          by (rewrite lineKind_revSwap; exact Hlk).
        destruct (specRevStep_scan core config pre post revBase revPfB revPfA initLine fwcs (subEnv NPMS envS s2) (sMemA s2)
                    b t c e ist ir sa st
                    (specEnvOK_mem core pcAddrInit pre post revBase revPfB revPfA initLine fwcs s2) Hxs Hodd Hnd Hk1
                    (lineUnique_spec _)
                    (fun Hc' => ltac:(exfalso; rewrite <- Hv in Hc'; rewrite Hc' in Hck; discriminate Hck)))
          as [ms1 [Hfr1 Hsem1]].
        apply (scan_commit g s1 s1' s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh st' ph' ms1
                 Hg EM Ex E1 Hidle' Hph' Eo); [rewrite Hacc; reflexivity | exact Hrp0 | exact Hq0 | exact Hdm0
                                             | exact Hsec0 | exact Hfr1 | exact Hsem1].
      + exfalso; exact (Hoff0 eq_refl).
      + (* the spec took the position's step already: the offset closes *)
        assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh) ,,
                                   (st' ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
        assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir (scanNext sa) st ph' sc sb sh).
        { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
        assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
        { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
        destruct (rpIdle_excl _ Hph') as [Q1 [Q2 [Q3 Q4]]].
        exists s2; split; [apply NilAction; reflexivity |].
        exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                  RevEq (g_d2aFo core pcAddrInit g) AccNone).
        eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                  clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
          [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
          | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
        * cbn [g_acc accTakesHead]; rewrite Hacc; reflexivity.
        * eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                       | rewrite iRegions_eq, EM'; reflexivity | |].
          -- destruct Hm as [[_ [_ [_ Hrv]]] _].
             change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
             rewrite ER, Eo in Hrv.
             cbn [g_revOff].
             apply (RevRel_advance core RevSpecAhead RevEq _ b t c e ist ir sa st ph sc sb sh ph' sc sb sh Hrv).
             pose proof (RevRel_scan core _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv) as Esa; cbn [revOffAddr] in Esa |- *.
             rewrite Esa, scanNext_eq; apply Zmod_sub_add_one.
          -- exact Hm.
        * unfold AccessRel; cbn [g_acc g_revOff].
          unfold PortsQuiet, dmNotAccessing, revNotReading in *.
          unfold iMemSt, iReadRp; rewrite EM'; cbn [Fst Snd].
          unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
          rewrite HP.
          split; [exact Hidle' |]. split; [exact Hrp0 |]. split; [exact Hq0 |]. split; [reflexivity |].
          split; [rewrite E1; exact Hdm0 |]. split; [split; assumption | exact Hsec0].
        * unfold RevokerRel; cbn [g_acc].
          unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
          split; [rewrite Hph'; intros Hc'; discriminate Hc' |].
          unfold rpCheck; rewrite Q2, Q3, Q4.
          split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
          split; [intros Hc'; discriminate Hc' | exact I].
  Qed.

  (* --- 3h. WaitRevBitRp: the Rev-Bit Read Answered --- *)

  Lemma waitRevBitRp_facts :
    forall g (s1 : IState) (s2 : SState) mr mst mrq mrp b t c e ist ir sa st ph sc sb sh,
      RELG g s1 s2 ->
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      revOfRA mr = mkRev12 core b t c e ist ir sa st ph sc sb sh ->
      rpWaitRevBitRp ph = true -> msReadRpReady mst = true -> isReqRevoker mrq = true ->
      g_acc core pcAddrInit g = AccRevBit (RdReady (msReadRpReadyV mst)) /\
      optValid mrp = false /\ PQ s1 /\ DNA s1 /\ g_revOff core pcAddrInit g = RevEq /\
      optValid (sSecondA s2) = false /\ epochOdd e = true /\ scanDone sa st = false /\
      capNeedsCheck config sc = true /\ sb = capBase sc /\
      lineKind implRegions (lineOf false (scanFull sa)) = Some true /\
      (sh = false -> memValAt core pre post revBase revPfB revPfA initLine (sMemA s2) (scanFull sa) capSz = sc) /\
      revBitOfVal config sb (msReadRpReadyV mst) = revBitOf core config pre post revBase revPfB revPfA initLine (sMemA s2) sb.
  Proof.
    intros g s1 s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh Hg EM Ex Hph Hrdy Hreq.
    destruct Hg as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh) by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
    destruct (rpWaitRevBitRp_excl _ Hph) as [P0 [P1 [P2 P4]]].
    assert (H1 : msReadRpReady (iMemStA s1) = true) by (unfold iMemSt; rewrite EM; exact Hrdy).
    assert (H2 : isReqRevoker (iRequesterA s1) = true) by (unfold iRequester; rewrite EM; exact Hreq).
    assert (Hacc : g_acc core pcAddrInit g = AccRevBit (RdReady (msReadRpReadyV mst))).
    { destruct (AccessRel_rpReady_rev g s1 s2 Ha H1 H2) as [[_ Hb] | [Ea _]].
      - unfold iRevPhase in Hb; rewrite ER in Hb; cbn [mkRev12 Fst Snd] in Hb; rewrite P1 in Hb; discriminate Hb.
      - unfold iMemSt in Ea; rewrite EM in Ea; exact Ea. }
    pose proof Ha as Ha'; unfold AccessRel, RdStageRel in Ha'; rewrite Hacc in Ha'; cbv beta iota zeta in Ha'.
    destruct Ha' as [[_ [_ [Hr3 Hr4]]] [_ [_ [Hdm0 [Hoff0 Hsec0]]]]].
    unfold RevokerRel in Hrk; destruct Hrk as [K1 [K2 [K3 [_ K5]]]].
    unfold RevAccRel in K5; rewrite Hacc in K5.
    unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in K1, K2, K3, K5;
      rewrite ER in K1, K2, K3, K5; cbn [mkRev12 Fst Snd] in K1, K2, K3, K5.
    destruct (K1 P0) as [Hodd Hnd].
    destruct (K2 (rpCheck_waitRevBitRp _ Hph)) as [Hnc [Hsb Hlk]].
    specialize (K3 (rpCheck_waitRevBitRp _ Hph)).
    unfold iReadRp in Hr3; rewrite EM in Hr3; cbn [Fst Snd] in Hr3.
    split; [exact Hacc |].
    split; [exact Hr3 |]. split; [exact Hr4 |]. split; [exact Hdm0 |]. split; [exact Hoff0 |].
    split; [exact Hsec0 |]. split; [exact Hodd |]. split; [exact Hnd |].
    split; [exact Hnc |]. split; [exact Hsb |]. split; [exact Hlk |].
    split; [exact K3 |].
    unfold revBitOfVal, revBitOf; cbv zeta; rewrite K5; reflexivity.
  Qed.

  Lemma stepOK_waitRevBitRp :
    STEPOK (@implRevokerWaitRevBitRpStepSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions revI type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implRevokerWaitRevBitRpStepSys in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    remember (revOfRA mr) as x eqn:Ex; symmetry in Ex.
    destruct x as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
    destruct (waitRevBitRp_char core config pre post revBase revPfB revPfA _ mr mst mrq mrp m' _
                b t c e ist ir sa st ph sc sb sh Ex Hm')
      as [-> | [Hph [Hrdy [Hreq [st' [ph' [Hidle' Hcases]]]]]]].
    - (* nothing changes *)
      exists s2; split; [apply NilAction; reflexivity |].
      exists g; replace s1' with s1; [exact Hg |].
      rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [reflexivity | f_equal; exact EM].
    - destruct (waitRevBitRp_facts g s1 s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh Hg EM Ex Hph Hrdy Hreq)
        as [Hacc [Hrp0 [Hq0 [Hdm0 [Hoff [Hsec0 [Hodd [Hnd [Hnc [Hsb [Hlk [Hmv Hrbv]]]]]]]]]]]].
      pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
      assert (ER : iRevA s1 = mkRev12 core b t c e ist ir sa st ph sc sb sh)
        by (rewrite iRev_eq, iRegions_eq, EM; exact Ex).
      destruct Hcases as [[Hsh [Hph' ->]] | [[Hsh [Hrb [Hph' ->]]] | [Hsh [Hrb [Hph' ->]]]]].
      + (* a store hit the position: it is retried; the spec stutters *)
        assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir sa st ph' sc sb sh) ,,
                                   (st' ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
        assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir sa st ph' sc sb sh).
        { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
        assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
        { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
        destruct (rpIdle_excl _ Hph') as [Q1 [Q2 [Q3 Q4]]].
        exists s2; split; [apply NilAction; reflexivity |].
        exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                  (g_revOff core pcAddrInit g) (g_d2aFo core pcAddrInit g) AccNone).
        eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                  clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
          [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
          | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
        * cbn [g_acc accTakesHead]; rewrite Hacc; reflexivity.
        * eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                       | rewrite iRegions_eq, EM'; reflexivity | |].
          -- destruct Hm as [[_ [_ [_ Hrv]]] _].
             change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
             rewrite ER in Hrv; exact Hrv.
          -- exact Hm.
        * unfold AccessRel; cbn [g_acc g_revOff].
          unfold PortsQuiet, dmNotAccessing, revNotReading in *.
          unfold iMemSt, iReadRp; rewrite EM'; cbn [Fst Snd].
          unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
          rewrite HP.
          split; [exact Hidle' |]. split; [exact Hrp0 |]. split; [exact Hq0 |]. split; [exact Hoff |].
          split; [rewrite E1; exact Hdm0 |]. split; [split; assumption | exact Hsec0].
        * unfold RevokerRel; cbn [g_acc].
          unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
          split; [rewrite Hph'; intros Hc'; discriminate Hc' |].
          unfold rpCheck; rewrite Q2, Q3, Q4.
          split; [intros Hc'; discriminate Hc' | split; [intros Hc'; discriminate Hc' |]].
          split; [intros Hc'; discriminate Hc' | exact I].
      + (* the rev bit is set: the untagged cap is to be written; the spec stutters *)
        assert (EM' : iMemA s1' = (setRevRA mr (mkRev12 core b t c e ist ir sa st ph' sc sb sh) ,,
                                   (st' ,, (mrq ,, (mrp ,, tt))))) by (rewrite E1; apply iMem_write).
        assert (ER' : iRevA s1' = mkRev12 core b t c e ist ir sa st ph' sc sb sh).
        { rewrite iRev_eq, iRegions_eq, EM'; cbn [Fst]; apply revOfR_setRevR. }
        assert (HP : forall P, AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
        { intros P; rewrite !iRegions_eq, EM', EM; cbn [Fst]; unfold setRevR; apply AllPorts_upd; exact I. }
        destruct (rpWriteCap_excl _ Hph') as [Q0 [Q1 [Q2 Q3]]].
        exists s2; split; [apply NilAction; reflexivity |].
        exists (mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
                  (g_revOff core pcAddrInit g) (g_d2aFo core pcAddrInit g) AccNone).
        eapply (RefRelG_mem_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                  clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
          [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HP
          | intros L; reflexivity | apply FetchViewExt_refl | | exact Hl | | | exact Hg].
        * cbn [g_acc accTakesHead]; rewrite Hacc; reflexivity.
        * eapply (MemRelC_revImpl g _ s1 s1' s2 mr); [rewrite iRegions_eq, EM; reflexivity
                                                       | rewrite iRegions_eq, EM'; reflexivity | |].
          -- destruct Hm as [[_ [_ [_ Hrv]]] _].
             change (RevRel core (g_revOff core pcAddrInit g) (specRevState core pre post revBase revPfB revPfA (sMemA s2)) (iRevA s1)) in Hrv.
             rewrite ER in Hrv; exact Hrv.
          -- exact Hm.
        * unfold AccessRel; cbn [g_acc g_revOff].
          unfold PortsQuiet, dmNotAccessing, revNotReading in *.
          unfold iMemSt, iReadRp; rewrite EM'; cbn [Fst Snd].
          unfold iRevPhase; rewrite ER'; cbn [mkRev12 Fst Snd].
          rewrite HP.
          split; [exact Hidle' |]. split; [exact Hrp0 |]. split; [exact Hq0 |]. split; [exact Hoff |].
          split; [rewrite E1; exact Hdm0 |]. split; [split; assumption | exact Hsec0].
        * unfold RevokerRel; cbn [g_acc].
          unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr; rewrite ER'; cbn [mkRev12 Fst Snd].
          split; [intros _; exact (conj Hodd Hnd) |].
          split; [intros _; split; [exact Hnc | split; [exact Hsb | exact Hlk]] |].
          split; [intros _ _; exact (Hmv Hsh) |].
          split; [intros _ _; rewrite <- Hrbv; exact Hrb | exact I].
      + (* the rev bit is clear: the spec takes the position's step *)
        assert (Hxs : specRevStateA (sMemA s2) = mkRev8 core b t c e ist ir sa st).
        { destruct Hm as [[_ [_ [_ Hrv]]] _].
          change (RevRel core (g_revOff core pcAddrInit g) (specRevStateA (sMemA s2)) (iRevA s1)) in Hrv.
          rewrite ER, Hoff in Hrv.
          exact (RevRel_eq core _ _ _ _ _ _ _ _ _ _ _ _ _ Hrv). }
        assert (Hk1 : lineKind specRegions (lineOf false (scanFull sa)) = Some true)
          by (rewrite lineKind_revSwap; exact Hlk).
        destruct (specRevStep_scan core config pre post revBase revPfB revPfA initLine fwcs (subEnv NPMS envS s2) (sMemA s2)
                    b t c e ist ir sa st
                    (specEnvOK_mem core pcAddrInit pre post revBase revPfB revPfA initLine fwcs s2) Hxs Hodd Hnd Hk1
                    (lineUnique_spec _)
                    (fun _ => ltac:(rewrite (Hmv Hsh); split; [exact (revTab_needsCheck sc Hnc) |
                                      split; [apply lineUnique_spec | rewrite <- Hsb, <- Hrbv; exact Hrb]])))
          as [ms1 [Hfr1 Hsem1]].
        apply (scan_commit g s1 s1' s2 mr mst mrq mrp b t c e ist ir sa st ph sc sb sh st' ph' ms1
                 Hg EM Ex E1 Hidle' Hph' Hoff); [rewrite Hacc; reflexivity | exact Hrp0 | exact Hq0 | exact Hdm0
                                                | exact Hsec0 | exact Hfr1 | exact Hsem1].
  Qed.

  (* --- 3i. The Five Revoker Rules --- *)

  Theorem stepOK_implRevokerStepsSys :
    forall act,
      In act (@implRevokerStepsSys core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions revI type) ->
      STEPOK act.
  Proof.
    intros act Hin.
    apply In_implRevokerStepsSys_decomp in Hin as [-> | [-> | [-> | [-> | ->]]]].
    - apply stepOK_idle.
    - apply stepOK_waitCapRp.
    - apply stepOK_waitRevBitRq.
    - apply stepOK_waitRevBitRp.
    - apply stepOK_writeCap.
  Qed.

End RevSteps.
