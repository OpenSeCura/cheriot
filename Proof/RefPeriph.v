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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * STEP OBLIGATIONS: CAN-PROCEED FLAGS, PERIPHERALS AND FENCE.I ACKS
 * ===========================================================================
 * `StepOK act`: an impl step of `act` from a related state is matched by spec
 * steps (none, for a stutter) ending in a related state. *)

Local Abbreviation TS t := (TreeState DomainElemState t).

(* --- CLINT Steps --- *)

Section ClintFun.
  Variable core : string.
  Local Abbreviation ClintS := (TS (Node "clint" (clintChildren core))).

  (* `clintSampleMtip`: sampledMtip |= mtip *)
  Lemma clintSample_eq :
    forall env (xi xi' : ClintS) v,
      SemAction env (clintSampleMtip core type) xi xi' v ->
      xi' = clintWithSampled core (orb (clintSampled core xi) (clintMtip core xi)) xi.
  Proof.
    intros env xi xi' v H; rewrite SemAction_iff_evalActionPropGen in H.
    destruct xi as [a [b [c [d []]]]].
    unfold clintSampleMtip, clintWithSampled, clintMtip, clintSampled in *; cbn in H.
    destruct c, d; cbn in H; destruct H as [H _]; subst xi'; reflexivity.
  Qed.

  (* `clintTick` on two states that differ only in sampledMtip: the results differ only
   * in sampledMtip, and each run keeps sampledMtip only while mtip stays set *)
  Lemma clintTick_rel :
    forall env1 env2 (xi xi' xs : ClintS) v,
      SemAction env1 (clintTick core type) xi xi' v ->
      xs = clintWithSampled core (clintSampled core xs) xi ->
      SemAction env2 (clintTick core type) xs
        (clintWithSampled core (andb (clintSampled core xs) (clintMtip core xi')) xi') v /\
      clintSampled core xi' = andb (clintSampled core xi) (clintMtip core xi').
  Proof.
    intros env1 env2 xi xi' xs v H Hxs.
    rewrite SemAction_iff_evalActionPropGen in H; rewrite SemAction_iff_evalActionPropGen.
    destruct xi as [a [b [c [d []]]]], xs as [a' [b' [c' [d' []]]]].
    unfold clintWithSampled, clintSampled in Hxs.
    pose proof (f_equal (fun x : ClintS => x.(Fst)) Hxs) as Ea.
    pose proof (f_equal (fun x : ClintS => x.(Snd).(Fst)) Hxs) as Eb.
    pose proof (f_equal (fun x : ClintS => x.(Snd).(Snd).(Fst)) Hxs) as Ec.
    cbn in Ea, Eb, Ec; subst a' b' c'; clear Hxs.
    unfold clintTick, clintWithSampled, clintMtip, clintSampled, readClintMtime, readClintMtimecmp in *.
    cbn -[evalExpr] in *.
    revert H.
    match goal with |- context [evalExpr (Uge ?p ?q)] => destruct (evalExpr (Uge p q)) end;
      destruct c; cbn; intros [H Hv]; subst xi'; cbn;
      (split; [split; [| exact Hv] |]); destruct d, d'; reflexivity.
  Qed.

  Lemma ClintRel_sample :
    forall xs xi, ClintRel core xs xi ->
      ClintRel core xs (clintWithSampled core (orb (clintSampled core xi) (clintMtip core xi)) xi).
  Proof.
    intros xs xi [H1 H2]; split.
    - transitivity (clintWithSampled core (clintSampled core xs) xi); [exact H1 | reflexivity].
    - intros Hs.
      change (orb (clintSampled core xi) (clintMtip core xi) = true).
      rewrite (H2 Hs); reflexivity.
  Qed.

  Lemma ClintInv_sample :
    forall xi, ClintInv core xi ->
      ClintInv core (clintWithSampled core (orb (clintSampled core xi) (clintMtip core xi)) xi).
  Proof.
    intros [a [b [c [d []]]]]; unfold ClintInv, clintWithSampled, clintSampled, clintMtip; cbn [Fst Snd].
    destruct c, d; cbn; auto.
  Qed.

  Lemma ClintRel_tick :
    forall xs xi xi', ClintRel core xs xi ->
      clintSampled core xi' = andb (clintSampled core xi) (clintMtip core xi') ->
      ClintRel core (clintWithSampled core (andb (clintSampled core xs) (clintMtip core xi')) xi') xi'.
  Proof.
    intros xs xi xi' [H1 H2] Hs'; split; [reflexivity |].
    intros Hb.
    change (andb (clintSampled core xs) (clintMtip core xi') = true) in Hb.
    apply andb_prop in Hb as [Hb1 Hb2].
    rewrite Hs', (H2 Hb1), Hb2; reflexivity.
  Qed.

  Lemma ClintInv_tick :
    forall xi xi', clintSampled core xi' = andb (clintSampled core xi) (clintMtip core xi') -> ClintInv core xi'.
  Proof.
    intros xi xi' Hs'; unfold ClintInv; rewrite Hs'; intros Hb; apply andb_prop in Hb as [_ Hb]; exact Hb.
  Qed.

End ClintFun.

(* --- PLIC Steps --- *)

Lemma isZero_false_neq :
  forall {sz : Z} (x : bits sz), evalExpr (isZero (Var type (Bit sz) x)) = false -> x <> Zmod.zero.
Proof.
  intros sz x H.
  assert (H' : Zmod.eqb x Zmod.zero = false) by (rewrite <- H; reflexivity).
  intros E; rewrite E, Zmod.eqb_refl in H'; discriminate H'.
Qed.

Section PlicFun.
  Variable core : string.
  Variable n : nat.
  Local Abbreviation PS := (TS (plicTree core n)).

  (* `plicSampleMeip`: meip |= (claim != 0) *)
  Lemma plicSample_eq :
    forall env (xi xi' : PS) v,
      SemAction env (@plicSampleMeip core n type) xi xi' v ->
      xi' = plicWithMeip core (orb (plicMeipOf core xi) (evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf core xi))))) xi.
  Proof.
    intros env xi xi' v H; rewrite SemAction_iff_evalActionPropGen in H.
    destruct xi as [pr [pe [en [th [cl [me [insv [ua []]]]]]]]].
    unfold plicSampleMeip, plicWithMeip, plicMeipOf, plicClaimOf in *; cbn -[evalExpr] in H |- *.
    destruct (evalExpr (isNotZero (Var type (Bit Xlen) cl))), me; cbn in H; destruct H as [H _]; subst xi'; reflexivity.
  Qed.

  Lemma PlicRelSame_sample :
    forall (xs xi : PS) c,
      PlicRelSame core n xs xi -> PlicRelSame core n xs (plicWithMeip core (orb (plicMeipOf core xi) c) xi).
  Proof.
    intros xs xi c [H1 H2]; split.
    - transitivity (plicWithMeip core (plicMeipOf core xs) xi); [exact H1 | reflexivity].
    - intros Hs; change (orb (plicMeipOf core xi) c = true); rewrite (H2 Hs); reflexivity.
  Qed.

  Lemma PlicInv_sample :
    forall (xi : PS),
      PlicInv core xi ->
      PlicInv core (plicWithMeip core (orb (plicMeipOf core xi) (evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf core xi))))) xi).
  Proof.
    intros xi H; unfold PlicInv in *; intros Hm.
    change (plicClaimOf core xi <> Zmod.zero).
    change (orb (plicMeipOf core xi) (evalExpr (isNotZero (Var type (Bit Xlen) (plicClaimOf core xi)))) = true) in Hm.
    destruct (plicMeipOf core xi) eqn:E; [apply H; first [exact E | reflexivity] |].
    cbn [orb] in Hm.
    apply isZero_false_neq.
    change (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi)))) = true) in Hm.
    apply negb_true_iff in Hm; exact Hm.
  Qed.

  Lemma evalActionPropGen_plic_readRegs :
    forall {k ans} env (paths : list (RegOfKind (t := plicTree core n) k))
           (kc : list (type k) -> Action type (plicTree core n) ans) (s : PS) P,
      evalActionPropGen env (@readRegs core n type k paths ans kc) s P <->
      evalActionPropGen env (kc (map (fun rk => readRegOfKind rk s) paths)) s P.
  Proof.
    intros k ans env paths; induction paths as [| rk rest IH]; intros kc s P;
      cbn [readRegs evalActionPropGen map]; [reflexivity |].
    rewrite IH; reflexivity.
  Qed.

  Fixpoint allSrcVals (prios : list (RegOfKind (t := plicTree core n) (Bit Xlen)))
    (pends insvs : list (RegOfKind (t := plicTree core n) Bool)) (s : PS)
    : (list (type (Bit Xlen)) * list (type Bool)) * list (type Bool) :=
    match prios, pends, insvs with
    | rp :: rps, rd :: rds, ri :: ris =>
        let t := allSrcVals rps rds ris s in
        ((readRegOfKind rp s :: fst (fst t), readRegOfKind rd s :: snd (fst t)), readRegOfKind ri s :: snd t)
    | _, _, _ => (([], []), [])
    end.

  Lemma evalActionPropGen_plic_readAllSources :
    forall {ans} env prios pends insvs
           (kc : list (type (Bit Xlen)) -> list (type Bool) -> list (type Bool) -> Action type (plicTree core n) ans)
           (s : PS) P,
      evalActionPropGen env (@readAllSources core n type prios pends insvs ans kc) s P <->
      evalActionPropGen env (kc (fst (fst (allSrcVals prios pends insvs s))) (snd (fst (allSrcVals prios pends insvs s)))
                               (snd (allSrcVals prios pends insvs s))) s P.
  Proof.
    intros ans env prios; induction prios as [| rp rps IH]; intros [| rd rds] [| ri ris] kc s P;
      cbn [readAllSources evalActionPropGen allSrcVals fst snd]; try reflexivity.
    rewrite IH; reflexivity.
  Qed.

  Lemma map_readRegOfKind_enables_meip :
    forall b (x : PS),
      map (fun rk => readRegOfKind rk (plicWithMeip core b x)) (enablesPathsWithKind core n) =
      map (fun rk => readRegOfKind rk x) (enablesPathsWithKind core n).
  Proof.
    intros b x; apply map_ext_in; intros rk Hin; unfold enablesPathsWithKind in Hin.
    apply in_map_iff in Hin as [rk0 [<- _]]; reflexivity.
  Qed.

  Lemma allSrcVals_meip :
    forall b (x : PS),
      allSrcVals (priorityPathsWithKind core n) (pendingPathsWithKind core n) (inServicePathsWithKind core n)
        (plicWithMeip core b x) =
      allSrcVals (priorityPathsWithKind core n) (pendingPathsWithKind core n) (inServicePathsWithKind core n) x.
  Proof.
    intros b x.
    assert (Hp : forall rk, In rk (priorityPathsWithKind core n) -> readRegOfKind rk (plicWithMeip core b x) = readRegOfKind rk x)
      by (intros rk Hin; unfold priorityPathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; reflexivity).
    assert (Hd : forall rk, In rk (pendingPathsWithKind core n) -> readRegOfKind rk (plicWithMeip core b x) = readRegOfKind rk x)
      by (intros rk Hin; unfold pendingPathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; reflexivity).
    assert (Hi : forall rk, In rk (inServicePathsWithKind core n) -> readRegOfKind rk (plicWithMeip core b x) = readRegOfKind rk x)
      by (intros rk Hin; unfold inServicePathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; reflexivity).
    revert Hp Hd Hi.
    generalize (priorityPathsWithKind core n) (pendingPathsWithKind core n) (inServicePathsWithKind core n).
    intros ps; induction ps as [| rp rps IH]; intros [| rd rds] [| ri ris] Hp Hd Hi; cbn [allSrcVals]; try reflexivity.
    rewrite (Hp rp (or_introl eq_refl)), (Hd rd (or_introl eq_refl)), (Hi ri (or_introl eq_refl)).
    rewrite (IH rds ris (fun rk H => Hp rk (or_intror H)) (fun rk H => Hd rk (or_intror H)) (fun rk H => Hi rk (or_intror H))).
    reflexivity.
  Qed.

  (* `updateClaim` on two states that differ only in meip: both write the same claim, and
   * each clears its meip exactly when the new claim is 0 *)
  Lemma updateClaim_rel :
    forall env1 env2 (xi xi' : PS) v b,
      SemAction env1 (@updateClaim core n type) xi xi' v ->
      SemAction env2 (@updateClaim core n type) (plicWithMeip core b xi)
        (plicWithMeip core (andb b (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi')))))) xi') v /\
      plicMeipOf core xi' = andb (plicMeipOf core xi) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi'))))).
  Proof.
    intros env1 env2 xi xi' v b H.
    rewrite SemAction_iff_evalActionPropGen in H; rewrite SemAction_iff_evalActionPropGen.
    unfold updateClaim, readPlicState in *.
    cbn [evalActionPropGen] in H |- *.
    rewrite evalActionPropGen_plic_readRegs in H; rewrite evalActionPropGen_plic_readRegs.
    rewrite evalActionPropGen_plic_readAllSources in H; rewrite evalActionPropGen_plic_readAllSources.
    rewrite (map_readRegOfKind_enables_meip b xi), (allSrcVals_meip b xi).
    cbn [evalActionPropGen] in H |- *.
    rewrite evalActionPropGen_toAction in H; rewrite evalActionPropGen_toAction.
    cbn in H |- *.
    revert H.
    match goal with |- (if ?c then _ else _) -> _ => destruct c eqn:HC end;
      intros [H Hv]; subst xi'.
    all: split; [split; [| exact Hv] |];
      unfold plicWithMeip, plicMeipOf, plicClaimOf; cbn; rewrite ?HC; cbn;
      destruct b; try destruct (Fst (Snd (Snd (Snd (Snd (Snd xi)))))); reflexivity.
  Qed.

  Lemma PlicInv_claim :
    forall (xi xi' : PS),
      plicMeipOf core xi' = andb (plicMeipOf core xi) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi'))))) ->
      PlicInv core xi'.
  Proof.
    intros xi xi' Hm; unfold PlicInv; intros Hs; rewrite Hm in Hs.
    apply andb_prop in Hs as [_ Hs]; apply negb_true_iff in Hs.
    exact (isZero_false_neq _ Hs).
  Qed.

  Lemma PlicRelSame_claim :
    forall (xs xi xi' : PS),
      PlicRelSame core n xs xi ->
      plicMeipOf core xi' = andb (plicMeipOf core xi) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi'))))) ->
      PlicRelSame core n
        (plicWithMeip core (andb (plicMeipOf core xs) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi')))))) xi')
        xi'.
  Proof.
    intros xs xi xi' [H1 H2] Hm; split; [reflexivity |].
    intros Hb.
    change (andb (plicMeipOf core xs) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi'))))) = true) in Hb.
    apply andb_prop in Hb as [Hb1 Hb2].
    rewrite Hm, (H2 Hb1), Hb2; reflexivity.
  Qed.


  (* A pending update reads the source's pending and in-service bits and writes its pending bit *)
  Lemma updatePendingLeaf_rel :
    forall env1 env2 (xi xi' : PS) pendRk insvRk irqVal v b,
      In pendRk (pendingPathsWithKind core n) -> In insvRk (inServicePathsWithKind core n) ->
      SemAction env1 (@updatePendingLeaf core n type pendRk insvRk irqVal) xi xi' v ->
      SemAction env2 (@updatePendingLeaf core n type pendRk insvRk irqVal) (plicWithMeip core b xi)
        (plicWithMeip core b xi') v /\
      plicMeipOf core xi' = plicMeipOf core xi /\ plicClaimOf core xi' = plicClaimOf core xi.
  Proof.
    intros env1 env2 xi xi' pendRk insvRk irqVal v b Hp Hi H.
    unfold pendingPathsWithKind in Hp; apply in_map_iff in Hp as [p0 [<- _]].
    unfold inServicePathsWithKind in Hi; apply in_map_iff in Hi as [i0 [<- _]].
    rewrite SemAction_iff_evalActionPropGen in H; rewrite SemAction_iff_evalActionPropGen.
    unfold updatePendingLeaf in *; cbn [evalActionPropGen] in H |- *.
    destruct H as [H Hv]; subst xi'.
    split; [split; [reflexivity | exact Hv] | split; reflexivity].
  Qed.

  (* The UART interrupt line: both sides receive the same value *)
  Lemma uartRecv_rel :
    forall env1 env2 (xi xi' : PS) w b,
      SemAction env1 (Recv "uartIrq" (plicUartIrqPath core n) (fun v => Return (Var type Bool v))) xi xi' w ->
      (forall s x v, env2 s x v) ->
      SemAction env2 (Recv "uartIrq" (plicUartIrqPath core n) (fun v => Return (Var type Bool v)))
        (plicWithMeip core b xi) (plicWithMeip core b xi') w /\
      plicMeipOf core xi' = plicMeipOf core xi /\ plicClaimOf core xi' = plicClaimOf core xi.
  Proof.
    intros env1 env2 xi xi' w b H Henv.
    rewrite SemAction_iff_evalActionPropGen in H; rewrite SemAction_iff_evalActionPropGen.
    cbn [evalActionPropGen] in H |- *.
    destruct H as [rv [_ [H Hv]]]; subst xi' w.
    split; [exists rv; split; [apply Henv | split; reflexivity] | split; reflexivity].
  Qed.

End PlicFun.

(* The spec and impl PLICs are over propositionally equal source counts *)
Section PlicTransport.
  Variable core : string.

  Lemma PlicRel_sample :
    forall n1 n2 (xs : TS (plicTree core n1)) (xi : TS (plicTree core n2)) c,
      PlicRel core n1 n2 xs xi -> PlicRel core n1 n2 xs (plicWithMeip core (orb (plicMeipOf core xi) c) xi).
  Proof.
    intros n1 n2 xs xi c [e H]; exists e; apply PlicRelSame_sample; exact H.
  Qed.

  (* Claim update, lockstep: the spec meip only falls *)
  Lemma PlicRel_claim :
    forall n1 n2 (xs : TS (plicTree core n1)) (xi xi' : TS (plicTree core n2)) env1 v,
      PlicRel core n1 n2 xs xi ->
      SemAction env1 (@updateClaim core n2 type) xi xi' v ->
      exists xs',
        (forall env2, SemAction env2 (@updateClaim core n1 type) xs xs' v) /\
        PlicRel core n1 n2 xs' xi' /\
        (plicMeipOf core xs' = true -> plicMeipOf core xs = true) /\
        PlicInv core xi'.
  Proof.
    intros n1 n2 xs xi xi' env1 v [e H] Hsem.
    subst n2; cbn [eq_rect] in H.
    destruct H as [H1 H2].
    pose proof (proj2 (updateClaim_rel core n1 env1 env1 xi xi' v (plicMeipOf core xs) Hsem)) as Hm.
    exists (plicWithMeip core (andb (plicMeipOf core xs) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi')))))) xi').
    split; [| split; [| split]].
    - intros env2.
      pose proof (proj1 (updateClaim_rel core n1 env1 env2 xi xi' v (plicMeipOf core xs) Hsem)) as Hs.
      rewrite <- H1 in Hs; exact Hs.
    - exists eq_refl; cbn [eq_rect]; exact (PlicRelSame_claim core n1 xs xi xi' (conj H1 H2) Hm).
    - intros Hb.
      change (andb (plicMeipOf core xs) (negb (evalExpr (isZero (Var type (Bit Xlen) (plicClaimOf core xi'))))) = true) in Hb.
      apply andb_prop in Hb as [Hb _]; exact Hb.
    - exact (PlicInv_claim core n1 xi xi' Hm).
  Qed.


  (* Pending update of source `j`, lockstep: the paths at `j` are the same on both sides *)
  Lemma PlicRel_leaf :
    forall n1 n2 (xs : TS (plicTree core n1)) (xi xi' : TS (plicTree core n2)) j pS iS pI iI irq env1 v,
      PlicRel core n1 n2 xs xi ->
      nth_error (pendingPathsWithKind core n1) j = Some pS -> nth_error (inServicePathsWithKind core n1) j = Some iS ->
      nth_error (pendingPathsWithKind core n2) j = Some pI -> nth_error (inServicePathsWithKind core n2) j = Some iI ->
      SemAction env1 (@updatePendingLeaf core n2 type pI iI irq) xi xi' v ->
      exists xs',
        (forall env2, SemAction env2 (@updatePendingLeaf core n1 type pS iS irq) xs xs' v) /\
        PlicRel core n1 n2 xs' xi' /\
        plicMeipOf core xs' = plicMeipOf core xs /\
        plicMeipOf core xi' = plicMeipOf core xi /\ plicClaimOf core xi' = plicClaimOf core xi.
  Proof.
    intros n1 n2 xs xi xi' j pS iS pI iI irq env1 v [e H] HpS HiS HpI HiI Hsem.
    subst n2; cbn [eq_rect] in H; destruct H as [H1 H2].
    rewrite HpS in HpI; injection HpI as HpI; subst pI.
    rewrite HiS in HiI; injection HiI as HiI; subst iI.
    assert (Hp : In pS (pendingPathsWithKind core n1)) by (eapply nth_error_In; exact HpS).
    assert (Hi : In iS (inServicePathsWithKind core n1)) by (eapply nth_error_In; exact HiS).
    destruct (updatePendingLeaf_rel core n1 env1 env1 xi xi' pS iS irq v (plicMeipOf core xs) Hp Hi Hsem)
      as [_ [Hm Hc]].
    exists (plicWithMeip core (plicMeipOf core xs) xi').
    split; [| split; [| split; [reflexivity | split; [exact Hm | exact Hc]]]].
    - intros env2.
      pose proof (proj1 (updatePendingLeaf_rel core n1 env1 env2 xi xi' pS iS irq v (plicMeipOf core xs) Hp Hi Hsem))
        as Hs.
      rewrite <- H1 in Hs; exact Hs.
    - exists eq_refl; cbn [eq_rect]; split; [reflexivity |].
      intros Hb; rewrite Hm; apply H2; exact Hb.
  Qed.

  (* UART interrupt line, lockstep *)
  Lemma PlicRel_uart :
    forall n1 n2 (xs : TS (plicTree core n1)) (xi xi' : TS (plicTree core n2)) env1 env2 w,
      PlicRel core n1 n2 xs xi ->
      SemAction env1 (Recv "uartIrq" (plicUartIrqPath core n2) (fun v => Return (Var type Bool v))) xi xi' w ->
      (forall s x v, env2 s x v) ->
      exists xs',
        SemAction env2 (Recv "uartIrq" (plicUartIrqPath core n1) (fun v => Return (Var type Bool v))) xs xs' w /\
        PlicRel core n1 n2 xs' xi' /\
        plicMeipOf core xs' = plicMeipOf core xs /\
        plicMeipOf core xi' = plicMeipOf core xi /\ plicClaimOf core xi' = plicClaimOf core xi.
  Proof.
    intros n1 n2 xs xi xi' env1 env2 w [e H] Hsem Henv.
    subst n2; cbn [eq_rect] in H; destruct H as [H1 H2].
    destruct (uartRecv_rel core n1 env1 env2 xi xi' w (plicMeipOf core xs) Hsem Henv) as [Hs [Hm Hc]].
    exists (plicWithMeip core (plicMeipOf core xs) xi').
    split; [rewrite <- H1 in Hs; exact Hs |].
    split; [| split; [reflexivity | split; [exact Hm | exact Hc]]].
    exists eq_refl; cbn [eq_rect]; split; [reflexivity |].
    intros Hb; rewrite Hm; apply H2; exact Hb.
  Qed.

  Lemma nth_pend_transport :
    forall n1 n2, n1 = n2 ->
      forall j (p2 : RegOfKind (t := plicTree core n2) Bool),
        nth_error (pendingPathsWithKind core n2) j = Some p2 ->
        exists p1, nth_error (pendingPathsWithKind core n1) j = Some p1.
  Proof. intros n1 n2 e; subst n2; intros j p2 H; exists p2; exact H. Qed.

  Lemma nth_insv_transport :
    forall n1 n2, n1 = n2 ->
      forall j (p2 : RegOfKind (t := plicTree core n2) Bool),
        nth_error (inServicePathsWithKind core n2) j = Some p2 ->
        exists p1, nth_error (inServicePathsWithKind core n1) j = Some p1.
  Proof. intros n1 n2 e; subst n2; intros j p2 H; exists p2; exact H. Qed.

End PlicTransport.


(* --- Envs of CustomMem Regions --- *)

Section EnvCustom.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma specRegionEnv_custom :
    forall r fwc, isCustomR r -> forall s x v, specRegionEnv core initLine r fwc s x v.
  Proof.
    intros r fwc; unfold isCustomR, specRegionEnv, memRegionTree.
    destruct (regionKind r); intros H; [contradiction | intros s x v; exact I].
  Qed.

  (* `env` accepts whatever the region envs accept (whatever the casts of path and value) *)
  Definition EnvCovers (l : list MemRegion) (fwcs : nat -> nat -> nat) (env : Env (specMemTree core l)) : Prop :=
    forall s (x : RecvPath (specMemTree core l)) v,
      (forall pf (v' : type (getRecvKindFromPath x.(recvPath))),
         specRegionsEnv core initLine fwcs l s (@Build_RecvPath (specMemTree core l) x.(recvPath) pf) v') ->
      env s x v.

  (* The env accepts every value at the receive ports of the CustomMem regions *)
  Fixpoint EnvCustomTrue (l : list MemRegion) : Env (specMemTree core l) -> Prop :=
    match l as l0 return Env (specMemTree core l0) -> Prop with
    | [] => fun _ => True
    | r :: rs => fun env =>
        (isCustomR r -> forall ms s x v, subEnv child0Path env ms s x v) /\
        (forall ms, EnvCustomTrue rs (subEnv child1Path env ms))
    end.

  Lemma EnvCovers_tail :
    forall r rs fwcs (env : Env (specMemTree core (r :: rs))) ms,
      EnvCovers (r :: rs) fwcs env -> EnvCovers rs (fun i => fwcs (S i)) (subEnv child1Path env ms).
  Proof.
    intros r rs fwcs env ms H s x v Hall.
    unfold subEnv; apply H; intros pf v'.
    cbn [specRegionsEnv]; unfold envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionsEnv specRegionEnv].
    apply Hall.
  Qed.

  Lemma EnvCovers_custom :
    forall l fwcs (env : Env (specMemTree core l)), EnvCovers l fwcs env -> EnvCustomTrue l env.
  Proof.
    induction l as [| r rs IH]; intros fwcs env H; cbn [EnvCustomTrue]; [exact I |].
    split.
    - intros Hc ms s x v; unfold subEnv; apply H; intros pf v'.
      cbn [specRegionsEnv]; unfold envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionsEnv specRegionEnv].
      apply specRegionEnv_custom; exact Hc.
    - intros ms; apply (IH (fun i => fwcs (S i))); apply EnvCovers_tail; exact H.
  Qed.

  Lemma envRegionAt_customTrue :
    forall l idx r0 (pf : nth_error l idx = Some r0) (env : Env (specMemTree core l)) s,
      EnvCustomTrue l env -> isCustomR r0 ->
      forall sub x v, envRegionAt (memRegionTree core) idx l r0 pf env s sub x v.
  Proof.
    induction l as [| r rs IH]; intros [| i'] r0 pf env s Henv Hc; try discriminate pf;
      cbn [EnvCustomTrue] in Henv; destruct Henv as [H0 H1].
    - cbn [envRegionAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      intros sub x v; exact (H0 Hc s sub x v).
    - cbn [envRegionAt].
      apply IH; [apply H1 | exact Hc].
  Qed.
End EnvCustom.

(* --- Changes Confined to CustomMem Regions --- *)

Section CustomOnly.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Fixpoint CustomOnlyS (l : list MemRegion) : TS (specMemTree core l) -> TS (specMemTree core l) -> Prop :=
    match l as l0 return TS (specMemTree core l0) -> TS (specMemTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun ms ms' =>
        (isCustomR r \/ ms'.(Fst) = ms.(Fst)) /\ CustomOnlyS rs ms.(Snd).(Fst) ms'.(Snd).(Fst)
    end.

  Fixpoint CustomOnlyI (l : list MemRegion) : TS (implRegionsTree core l) -> TS (implRegionsTree core l) -> Prop :=
    match l as l0 return TS (implRegionsTree core l0) -> TS (implRegionsTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun mi mi' =>
        (isCustomR r \/ mi'.(Fst) = mi.(Fst)) /\ CustomOnlyI rs mi.(Snd).(Fst) mi'.(Snd).(Fst)
    end.

  Lemma CustomOnlyS_refl : forall l ms, CustomOnlyS l ms ms.
  Proof.
    induction l as [| r rs IH]; intros ms; cbn [CustomOnlyS]; [exact I | split; [right; reflexivity | apply IH]].
  Qed.

  Lemma CustomOnlyI_refl : forall l mi, CustomOnlyI l mi mi.
  Proof.
    induction l as [| r rs IH]; intros mi; cbn [CustomOnlyI]; [exact I | split; [right; reflexivity | apply IH]].
  Qed.

  Lemma AllPorts_customOnly :
    forall P l mi mi', CustomOnlyI l mi mi' -> AllPorts core P l mi' = AllPorts core P l mi.
  Proof.
    intros P; induction l as [| r rs IH]; intros mi mi' H; cbn [CustomOnlyI AllPorts] in *; [reflexivity |].
    destruct H as [[Hc | E] H].
    - rewrite !RegionPort_custom by exact Hc; rewrite (IH _ _ H); reflexivity.
    - rewrite E, (IH _ _ H); reflexivity.
  Qed.

  Lemma lineContent_customOnly :
    forall l ms ms', CustomOnlyS l ms ms' ->
      forall L, lineContent core initLine l ms' L = lineContent core initLine l ms L.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H L; cbn [CustomOnlyS lineContent] in *; [reflexivity |].
    destruct H as [[Hc | E] H].
    - rewrite !RegionLineContent_custom by exact Hc; rewrite (IH _ _ H); reflexivity.
    - rewrite E, (IH _ _ H); reflexivity.
  Qed.

  Lemma FetchViewExt_customOnly :
    forall l ms ms', CustomOnlyS l ms ms' -> FetchViewExt core l ms ms'.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H; cbn [CustomOnlyS FetchViewExt] in *; [exact I |].
    destruct H as [[Hc | E] H]; split; try exact (IH _ _ H).
    - exact (RegionFetchViewExt_custom core r _ _ Hc).
    - rewrite E; apply RegionFetchViewExt_refl.
  Qed.

  Lemma SnapshotOK_customOnly :
    forall l fwcs ms ms', CustomOnlyS l ms ms' -> SnapshotOK core fwcs l ms -> SnapshotOK core fwcs l ms'.
  Proof.
    induction l as [| r rs IH]; intros fwcs ms ms' H Hs; cbn [CustomOnlyS SnapshotOK] in *; [exact I |].
    destruct H as [[Hc | E] H], Hs as [Hs0 Hs1]; split; try exact (IH _ _ _ H Hs1).
    - exact (RegionSnapshotOK_custom core r _ _ Hc).
    - rewrite E; exact Hs0.
  Qed.
End CustomOnly.

(* --- Unchanged at a Position --- *)

Section SameAtSec.
  Variable regionTree : MemRegion -> Tree DomainElem.

  Definition SameAt (j : nat) (l : list MemRegion) (s s' : TS (regionsTree regionTree l)) : Prop :=
    forall r0 (pf : nth_error l j = Some r0),
      regionStateAt regionTree j l r0 pf s' = regionStateAt regionTree j l r0 pf s.

  Lemma SameAt_refl : forall j l s, SameAt j l s s.
  Proof. intros j l s r0 pf; reflexivity. Qed.

  Lemma SameAt_head :
    forall r rs (s s' : TS (regionsTree regionTree (r :: rs))), s'.(Fst) = s.(Fst) -> SameAt 0 (r :: rs) s s'.
  Proof. intros r rs s s' E r0 pf; cbn [regionStateAt]; rewrite E; reflexivity. Qed.

  Lemma SameAt_tail :
    forall r rs j (s s' : TS (regionsTree regionTree (r :: rs))),
      SameAt j rs s.(Snd).(Fst) s'.(Snd).(Fst) -> SameAt (S j) (r :: rs) s s'.
  Proof. intros r rs j s s' H r0 pf; cbn [regionStateAt]; apply H. Qed.
End SameAtSec.

(* --- Interrupt Sources of the Regions: One Side --- *)

Lemma option_map_Some_inv :
  forall {A B : Type} (g : A -> B) (o : option A) (b : B), option_map g o = Some b -> exists a, o = Some a /\ b = g a.
Proof.
  intros A B g [a |] b H; cbn in H; [injection H as H; subst b; exists a; split; reflexivity | discriminate H].
Qed.

Lemma nth_error_snoc_inv :
  forall {A : Type} (L : list A) (u : A) k a,
    nth_error (L ++ [u]) k = Some a -> nth_error L k = Some a \/ (k = length L /\ a = u).
Proof.
  intros A L u k a H.
  destruct (Nat.lt_ge_cases k (length L)) as [Hlt | Hge].
  - left; rewrite nth_error_app1 in H by exact Hlt; exact H.
  - right; rewrite nth_error_app2 in H by exact Hge.
    revert H; destruct (k - length L)%nat as [| j] eqn:Ej; intros H.
    + cbn in H; injection H as H; split; [lia | symmetry; exact H].
    + destruct j; discriminate H.
Qed.

Lemma nth_error_app_map_l :
  forall {A B : Type} (g : A -> B) (L : list A) (u : B) k a,
    nth_error L k = Some a -> nth_error (map g L ++ [u]) k = Some (g a).
Proof.
  intros A B g L u k a H.
  assert (Hlt : (k < length L)%nat) by (apply nth_error_Some; rewrite H; discriminate).
  rewrite nth_error_app1 by (rewrite length_map; exact Hlt).
  rewrite nth_error_map, H; reflexivity.
Qed.

Lemma nth_error_app_last :
  forall {A : Type} (L : list A) (u : A) k, k = length L -> nth_error (L ++ [u]) k = Some u.
Proof.
  intros A L u k ->; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
Qed.

Section IrqFrame.
  Variable core : string.

  (* The region's interrupt sources do not change its state *)
  Definition IrqROS (r : MemRegion) : Prop :=
    forall f, In f (memRegionIrqActions core r) ->
      forall env (x x' : TS (memRegionTree core r)) v, SemAction env (f type) x x' v -> x' = x.

  Lemma irqs_custom : forall r, memRegionIrqActions core r <> [] -> isCustomR r.
  Proof.
    intros [nm bs sz tg kd im ba sa]; unfold memRegionIrqActions, memRegionIrqAction, isCustomR; cbn [regionKind].
    destruct kd as [| ch rd wr [irq |]]; intros H; try exact I; exfalso; apply H; reflexivity.
  Qed.

  Lemma IrqROS_noirq : forall r, memRegionIrqActions core r = [] -> IrqROS r.
  Proof. intros r E f Hf; rewrite E in Hf; destruct Hf. Qed.

  Lemma revIrq_eq :
    forall extra env (x x' : TS (Node "revoker" (revokerChildren core extra))) v,
      SemAction env (@revokerLocalInterrupt core extra type) x x' v -> x' = x.
  Proof.
    intros extra env x x' v H.
    rewrite SemAction_iff_evalActionPropGen in H; unfold revokerLocalInterrupt in H; cbn [evalActionPropGen] in H.
    destruct H as [H _]; symmetry; exact H.
  Qed.

  Lemma IrqROS_rev :
    forall extra base pfB pfA, IrqROS (@revokerMemRegion core extra base pfB pfA).
  Proof.
    intros extra base pfB pfA f Hf env x x' v H.
    cbn in Hf; destruct Hf as [<- | []].
    exact (revIrq_eq extra env x x' v H).
  Qed.

  Lemma revIrq_char :
    forall extra base pfB pfA f, In f (memRegionIrqActions core (@revokerMemRegion core extra base pfB pfA)) ->
      forall env (x x' : TS (memRegionTree core (@revokerMemRegion core extra base pfB pfA))) v,
        SemAction env (f type) x x' v <-> SemAction env (@revokerLocalInterrupt core extra type) x x' v.
  Proof.
    intros extra base pfB pfA f Hf env x x' v.
    cbn in Hf; destruct Hf as [<- | []]; reflexivity.
  Qed.

  Lemma length_implIrqs : forall r, length (implMemRegionIrqActions core r) = length (memRegionIrqActions core r).
  Proof. intros r; unfold implMemRegionIrqActions; apply length_map. Qed.

  Lemma length_implCollect : forall l, length (implCollectIrqActions core l) = length (collectIrqActions core l).
  Proof.
    induction l as [| r rs IH]; [reflexivity |].
    unfold implCollectIrqActions, implCollectRegionActions, collectIrqActions in *; cbn [genCollectRegionActions].
    rewrite !length_app, !length_map.
    apply (f_equal2 Nat.add); [first [reflexivity | apply length_implIrqs] | exact IH].
  Qed.

  Lemma irqSpec_frame :
    forall l k (aS : forall ty, Action ty (specMemTree core l) Bool) env (ms ms' : TS (specMemTree core l)) v,
      nth_error (collectIrqActions core l) k = Some aS ->
      SemAction env (aS type) ms ms' v ->
      CustomOnlyS core l ms ms' /\
      (forall j, (forall r0, nth_error l j = Some r0 -> IrqROS r0) -> SameAt (memRegionTree core) j l ms ms').
  Proof.
    induction l as [| r rs IH]; intros k aS env ms ms' v Hk Hsem;
      [unfold collectIrqActions in Hk; destruct k; cbn in Hk; discriminate Hk |].
    unfold collectIrqActions in Hk; cbn [genCollectRegionActions] in Hk.
    destruct (Nat.lt_ge_cases k (length (memRegionIrqActions core r))) as [Hlt | Hge].
    - rewrite nth_error_app1 in Hk by (rewrite length_map; exact Hlt).
      rewrite nth_error_map in Hk.
      apply option_map_Some_inv in Hk as [f [Hf Hk]]; subst aS; cbv beta in Hsem.
      apply SemAction_liftAction_iff in Hsem as [x' [Hx' ->]].
      assert (HfIn : In f (memRegionIrqActions core r)) by (eapply nth_error_In; exact Hf).
      assert (Hne : memRegionIrqActions core r <> []) by (intros E; rewrite E in HfIn; destruct HfIn).
      split.
      + cbn [CustomOnlyS]; split; [left; exact (irqs_custom r Hne) | apply CustomOnlyS_refl].
      + intros [| j] Hro.
        * apply SameAt_head.
          exact (Hro r eq_refl f HfIn _ _ _ _ Hx').
        * apply SameAt_tail; apply SameAt_refl.
    - rewrite nth_error_app2 in Hk by (rewrite length_map; exact Hge).
      rewrite length_map, nth_error_map in Hk.
      apply option_map_Some_inv in Hk as [aS' [HaS' Hk]]; subst aS; cbv beta in Hsem.
      apply SemAction_liftAction_iff in Hsem as [ms'' [Hms'' ->]].
      destruct (IH _ _ _ _ _ _ HaS' Hms'') as [H1 H2].
      split.
      + cbn [CustomOnlyS]; split; [right; reflexivity | exact H1].
      + intros [| j] Hro.
        * apply SameAt_head; reflexivity.
        * apply SameAt_tail; apply H2; intros r0 Hr0; exact (Hro r0 Hr0).
  Qed.

  Lemma irqImpl_frame :
    forall l k (aI : forall ty, Action ty (implRegionsTree core l) Bool) env (mi mi' : TS (implRegionsTree core l)) v,
      nth_error (implCollectIrqActions core l) k = Some aI ->
      SemAction env (aI type) mi mi' v ->
      CustomOnlyI core l mi mi' /\
      (forall j, (forall r0, nth_error l j = Some r0 -> IrqROS r0) -> SameAt (implMemRegionTree core) j l mi mi').
  Proof.
    induction l as [| r rs IH]; intros k aI env mi mi' v Hk Hsem;
      [unfold implCollectIrqActions, implCollectRegionActions in Hk; destruct k; cbn in Hk; discriminate Hk |].
    unfold implCollectIrqActions, implCollectRegionActions in Hk; cbn [genCollectRegionActions] in Hk.
    unfold implMemRegionIrqActions in Hk.
    destruct (Nat.lt_ge_cases k (length (memRegionIrqActions core r))) as [Hlt | Hge].
    - rewrite nth_error_app1 in Hk by (rewrite !length_map; exact Hlt).
      rewrite !nth_error_map in Hk.
      apply option_map_Some_inv in Hk as [y [Hy Hk]]; subst aI.
      apply option_map_Some_inv in Hy as [f [Hf Hy]]; subst y; cbv beta in Hsem.
      apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
      unfold liftToImplRegion in Hy'.
      apply SemAction_liftAction_iff in Hy' as [x' [Hx' ->]].
      assert (HfIn : In f (memRegionIrqActions core r)) by (eapply nth_error_In; exact Hf).
      assert (Hne : memRegionIrqActions core r <> []) by (intros E; rewrite E in HfIn; destruct HfIn).
      split.
      + cbn [CustomOnlyI]; split; [left; exact (irqs_custom r Hne) | apply CustomOnlyI_refl].
      + intros [| j] Hro.
        * apply SameAt_head.
          pose proof (Hro r eq_refl f HfIn _ _ _ _ Hx') as Ex.
          rewrite Ex; reflexivity.
        * apply SameAt_tail; apply SameAt_refl.
    - rewrite nth_error_app2 in Hk by (rewrite !length_map; exact Hge).
      rewrite !length_map, nth_error_map in Hk.
      apply option_map_Some_inv in Hk as [aI' [HaI' Hk]]; subst aI; cbv beta in Hsem.
      apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
      destruct (IH _ _ _ _ _ _ HaI' Hmi'') as [H1 H2].
      split.
      + cbn [CustomOnlyI]; split; [right; reflexivity | exact H1].
      + intros [| j] Hro.
        * apply SameAt_head; reflexivity.
        * apply SameAt_tail; apply H2; intros r0 Hr0; exact (Hro r0 Hr0).
  Qed.
End IrqFrame.

(* --- Interrupt Sources of the Regions: Spec and Impl Together --- *)

Section IrqRel.
  Variable core : string.
  Variables cp pp : nat.
  Variable post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.
  Local Abbreviation sRevR := (specRevRegion core revBase revPfB revPfA).
  Local Abbreviation iRevR := (implRevRegion core revBase revPfB revPfA).

  Lemma length_collect_rev :
    forall l, length (collectIrqActions core (l ++ iRevR :: post)) = length (collectIrqActions core (l ++ sRevR :: post)).
  Proof.
    induction l as [| r rs IH]; unfold collectIrqActions in *; cbn [genCollectRegionActions app];
      rewrite !length_app, !length_map; [reflexivity | apply (f_equal2 Nat.add); [reflexivity | exact IH]].
  Qed.

  Lemma RegionRelAt_custom :
    forall i r (x : TS (memRegionTree core r)) (y : TS (implMemRegionTree core r)),
      isCustomR r -> (RegionRelAt core cp pp i r x y <-> (i = cp \/ i = pp \/ x = y.(Fst))).
  Proof.
    intros i r; unfold isCustomR, RegionRelAt, memRegionTree, implMemRegionTree.
    destruct (regionKind r); intros x y H; [contradiction | reflexivity].
  Qed.

  Lemma irqHead_rel :
    forall i r rsS rsI (ms : TS (specMemTree core (r :: rsS))) (mi mi' : TS (implRegionsTree core (r :: rsI)))
           (f : forall ty, Action ty (memRegionTree core r) Bool) envI envS v,
      In f (memRegionIrqActions core r) ->
      RegionRelAt core cp pp i r ms.(Fst) mi.(Fst) ->
      i <> cp -> i <> pp ->
      (isCustomR r -> forall ms0 s x w, subEnv child0Path envS ms0 s x w) ->
      SemAction envI (liftAction child0Path (liftToImplRegion (f type))) mi mi' v ->
      exists ms',
        SemAction envS (liftAction child0Path (f type)) ms ms' v /\
        RegionRelAt core cp pp i r ms'.(Fst) mi'.(Fst) /\ ms'.(Snd) = ms.(Snd) /\ mi'.(Snd) = mi.(Snd).
  Proof.
    intros i r rsS rsI ms mi mi' f envI envS v Hf Hrel Hcp Hpp Henv Hsem.
    assert (Hc : isCustomR r) by (apply (irqs_custom core); intros E; rewrite E in Hf; destruct Hf).
    apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
    unfold liftToImplRegion in Hy'.
    apply SemAction_liftAction_iff in Hy' as [x' [Hx' ->]].
    apply (proj1 (RegionRelAt_custom i r _ _ Hc)) in Hrel.
    destruct Hrel as [E | [E | E]]; [contradiction | contradiction |].
    assert (Hx'' : SemAction (subEnv child0Path envS ms) (f type) mi.(Fst).(Fst) x' v).
    { refine (SemAction_env_mono _ _ (f type) _ _ _ _ Hx'); intros s x w _; exact (Henv Hc ms s x w). }
    rewrite <- E in Hx''.
    exists (x' ,, ms.(Snd)); split; [| split; [| split; reflexivity]].
    - apply SemAction_liftAction_iff; exists x'; split; [exact Hx'' | reflexivity].
    - apply (proj2 (RegionRelAt_custom i r _ _ Hc)); right; right; reflexivity.
  Qed.

  Lemma irqPost_rel :
    forall l i (ms : TS (specMemTree core l)) (mi mi' : TS (implRegionsTree core l)) k
           (aS : forall ty, Action ty (specMemTree core l) Bool)
           (aI : forall ty, Action ty (implRegionsTree core l) Bool) envI envS v,
      nth_error (collectIrqActions core l) k = Some aS ->
      nth_error (implCollectIrqActions core l) k = Some aI ->
      MemRelPost core cp pp i l ms mi ->
      (forall j r, nth_error l j = Some r -> (i + j = cp \/ i + j = pp)%nat -> memRegionIrqActions core r = []) ->
      EnvCustomTrue core l envS ->
      SemAction envI (aI type) mi mi' v ->
      exists ms', SemAction envS (aS type) ms ms' v /\ MemRelPost core cp pp i l ms' mi'.
  Proof.
    induction l as [| r rs IH]; intros i ms mi mi' k aS aI envI envS v HkS HkI Hrel Hno Henv Hsem;
      [unfold collectIrqActions in HkS; destruct k; cbn in HkS; discriminate HkS |].
    unfold collectIrqActions in HkS; cbn [genCollectRegionActions] in HkS.
    unfold implCollectIrqActions, implCollectRegionActions in HkI; cbn [genCollectRegionActions] in HkI.
    unfold implMemRegionIrqActions in HkI.
    cbn [MemRelPost EnvCustomTrue] in Hrel, Henv.
    destruct Hrel as [Hrel0 Hrel1], Henv as [Henv0 Henv1].
    destruct (Nat.lt_ge_cases k (length (memRegionIrqActions core r))) as [Hlt | Hge].
    - rewrite nth_error_app1 in HkS by (rewrite length_map; exact Hlt).
      rewrite nth_error_app1 in HkI by (rewrite !length_map; exact Hlt).
      rewrite nth_error_map in HkS; rewrite !nth_error_map in HkI.
      apply option_map_Some_inv in HkS as [f [Hf HkS]]; subst aS.
      apply option_map_Some_inv in HkI as [y [Hy HkI]]; subst aI.
      apply option_map_Some_inv in Hy as [f' [Hf' Hy]]; subst y.
      assert (Ef : f' = f) by (pose proof (eq_trans (eq_sym Hf') Hf) as E; injection E as E; exact E).
      subst f'; cbv beta in Hsem |- *.
      assert (HfIn : In f (memRegionIrqActions core r)) by (eapply nth_error_In; exact Hf).
      assert (Hcp : i <> cp).
      { intros E; rewrite (Hno 0%nat r eq_refl (or_introl (eq_trans (Nat.add_0_r i) E))) in HfIn; destruct HfIn. }
      assert (Hpp : i <> pp).
      { intros E; rewrite (Hno 0%nat r eq_refl (or_intror (eq_trans (Nat.add_0_r i) E))) in HfIn; destruct HfIn. }
      destruct (irqHead_rel i r rs rs ms mi mi' f envI envS v HfIn Hrel0 Hcp Hpp Henv0 Hsem)
        as [ms' [Hs' [Hr' [E1 E2]]]].
      exists ms'; split; [exact Hs' |].
      cbn [MemRelPost]; split; [exact Hr' |].
      rewrite E1, E2; exact Hrel1.
    - rewrite nth_error_app2 in HkS by (rewrite length_map; exact Hge).
      rewrite nth_error_app2 in HkI by (rewrite !length_map; exact Hge).
      rewrite length_map, nth_error_map in HkS; rewrite !length_map, nth_error_map in HkI.
      apply option_map_Some_inv in HkS as [aS' [HaS' HkS]]; subst aS.
      apply option_map_Some_inv in HkI as [aI' [HaI' HkI]]; subst aI; cbv beta in Hsem |- *.
      apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
      assert (Hno' : forall j r0, nth_error rs j = Some r0 -> (S i + j = cp \/ S i + j = pp)%nat ->
                                 memRegionIrqActions core r0 = []).
      { intros j r0 Hr0 Hj; apply (Hno (S j) r0 Hr0); destruct Hj as [Hj | Hj]; [left | right]; lia. }
      destruct (IH (S i) ms.(Snd).(Fst) mi.(Snd).(Fst) mi'' _ aS' aI' _ _ v HaS' HaI' Hrel1 Hno' (Henv1 ms) Hmi'')
        as [ms'' [Hs'' Hr'']].
      exists (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd))); split.
      + apply SemAction_liftAction_iff; exists ms''; split; [exact Hs'' | reflexivity].
      + cbn [MemRelPost]; split; [exact Hrel0 | exact Hr''].
  Qed.

  Lemma revIrq_rel :
    forall adv env1 env2 (xs : TS (Node "revoker" (revokerChildren core []))) (xi xi' : TS (implRevokerTree core)) v,
      RevRel core adv xs xi ->
      SemAction env1 (@revokerLocalInterrupt core (implRevokerExtraChildren core) type) xi xi' v ->
      SemAction env2 (@revokerLocalInterrupt core [] type) xs xs v.
  Proof.
    intros adv env1 env2 xs xi xi' v HR H.
    pose proof (f_equal (fun z => z.(Snd).(Snd).(Snd).(Snd).(Fst)) HR) as E4.
    pose proof (f_equal (fun z => z.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)) HR) as E5.
    cbn in E4, E5.
    rewrite SemAction_iff_evalActionPropGen in H; rewrite SemAction_iff_evalActionPropGen.
    unfold revokerLocalInterrupt in *; cbn [evalActionPropGen] in H |- *.
    destruct H as [_ Hv]; split; [reflexivity |].
    rewrite <- Hv; cbn; rewrite ?E4, ?E5; reflexivity.
  Qed.

  Lemma irqPre_rel :
    forall l i (ms : TS (specMemTree core (l ++ sRevR :: post)))
           (mi mi' : TS (implRegionsTree core (l ++ iRevR :: post)))
           k aS aI envI envS v adv,
      nth_error (collectIrqActions core (l ++ sRevR :: post)) k = Some aS ->
      nth_error (implCollectIrqActions core (l ++ iRevR :: post)) k = Some aI ->
      MemRelPre core cp pp i l sRevR iRevR post ms mi ->
      RevRel core adv
        (regionStateAt (memRegionTree core) (length l) (l ++ sRevR :: post) sRevR (nth_error_app_cons_len l sRevR post) ms)
        (regionStateAt (implMemRegionTree core) (length l) (l ++ iRevR :: post) iRevR
           (nth_error_app_cons_len l iRevR post) mi).(Fst) ->
      (forall j r, nth_error (l ++ sRevR :: post) j = Some r -> (i + j = cp \/ i + j = pp)%nat ->
                   memRegionIrqActions core r = []) ->
      EnvCustomTrue core (l ++ sRevR :: post) envS ->
      SemAction envI (aI type) mi mi' v ->
      exists ms', SemAction envS (aS type) ms ms' v /\ MemRelPre core cp pp i l sRevR iRevR post ms' mi'.
  Proof.
    induction l as [| r rs IH]; intros i ms mi mi' k aS aI envI envS v adv HkS HkI Hrel HR Hno Henv Hsem.
    - unfold collectIrqActions in HkS; cbn [genCollectRegionActions app] in HkS.
      unfold implCollectIrqActions, implCollectRegionActions in HkI; cbn [genCollectRegionActions app] in HkI.
      cbn [MemRelPre] in Hrel.
      cbn [EnvCustomTrue app] in Henv; destruct Henv as [Henv0 Henv1].
      cbn [length nth_error_app_cons_len regionStateAt app] in HR.
      unfold implMemRegionIrqActions in HkI.
      destruct (Nat.lt_ge_cases k 1) as [Hlt | Hge].
      + rewrite nth_error_app1 in HkS by (rewrite length_map; exact Hlt).
        rewrite nth_error_app1 in HkI by (rewrite !length_map; exact Hlt).
        rewrite nth_error_map in HkS; rewrite !nth_error_map in HkI.
        apply option_map_Some_inv in HkS as [fS [HfS HkS]]; subst aS.
        apply option_map_Some_inv in HkI as [y [Hy HkI]]; subst aI.
        apply option_map_Some_inv in Hy as [fI [HfI Hy]]; subst y; cbv beta in Hsem |- *.
        apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
        unfold liftToImplRegion in Hy'.
        apply SemAction_liftAction_iff in Hy' as [x' [Hx' ->]].
        assert (HfSIn : In fS (memRegionIrqActions core sRevR)) by (eapply nth_error_In; exact HfS).
        assert (HfIIn : In fI (memRegionIrqActions core iRevR)) by (eapply nth_error_In; exact HfI).
        apply (proj1 (revIrq_char core _ _ _ _ fI HfIIn _ _ _ _)) in Hx'.
        pose proof (revIrq_rel adv _ (subEnv child0Path envS ms) _ _ _ v HR Hx') as Hs.
        apply (proj2 (revIrq_char core _ _ _ _ fS HfSIn _ _ _ _)) in Hs.
        exists ms; split.
        * apply SemAction_liftAction_iff; exists ms.(Fst); split; [exact Hs | reflexivity].
        * exact Hrel.
      + rewrite nth_error_app2 in HkS by (rewrite length_map; exact Hge).
        rewrite nth_error_app2 in HkI by (rewrite !length_map; exact Hge).
        rewrite length_map, nth_error_map in HkS; rewrite !length_map, nth_error_map in HkI.
        apply option_map_Some_inv in HkS as [aS' [HaS' HkS]]; subst aS.
        apply option_map_Some_inv in HkI as [aI' [HaI' HkI]]; subst aI; cbv beta in Hsem |- *.
        apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
        assert (Hno' : forall j r0, nth_error post j = Some r0 -> (S i + j = cp \/ S i + j = pp)%nat ->
                                   memRegionIrqActions core r0 = []).
        { intros j r0 Hr0 Hj; apply (Hno (S j) r0 Hr0); destruct Hj as [Hj | Hj]; [left | right]; lia. }
        destruct (irqPost_rel post (S i) ms.(Snd).(Fst) mi.(Snd).(Fst) mi'' _ aS' aI' _ _ v HaS' HaI' Hrel Hno'
                    (Henv1 ms) Hmi'') as [ms'' [Hs'' Hr'']].
        exists (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd))); split.
        * apply SemAction_liftAction_iff; exists ms''; split; [exact Hs'' | reflexivity].
        * exact Hr''.
    - unfold collectIrqActions in HkS; cbn [genCollectRegionActions app] in HkS.
      unfold implCollectIrqActions, implCollectRegionActions in HkI; cbn [genCollectRegionActions app] in HkI.
      unfold implMemRegionIrqActions in HkI.
      cbn [MemRelPre] in Hrel; destruct Hrel as [Hrel0 Hrel1].
      cbn [EnvCustomTrue app] in Henv; destruct Henv as [Henv0 Henv1].
      cbn [length nth_error_app_cons_len regionStateAt app] in HR.
      destruct (Nat.lt_ge_cases k (length (memRegionIrqActions core r))) as [Hlt | Hge].
      + rewrite nth_error_app1 in HkS by (rewrite length_map; exact Hlt).
        rewrite nth_error_app1 in HkI by (rewrite !length_map; exact Hlt).
        rewrite nth_error_map in HkS; rewrite !nth_error_map in HkI.
        apply option_map_Some_inv in HkS as [f [Hf HkS]]; subst aS.
        apply option_map_Some_inv in HkI as [y [Hy HkI]]; subst aI.
        apply option_map_Some_inv in Hy as [f' [Hf' Hy]]; subst y.
        assert (Ef : f' = f) by (pose proof (eq_trans (eq_sym Hf') Hf) as E; injection E as E; exact E).
        subst f'; cbv beta in Hsem |- *.
        assert (HfIn : In f (memRegionIrqActions core r)) by (eapply nth_error_In; exact Hf).
        assert (Hcp : i <> cp).
        { intros E; rewrite (Hno 0%nat r eq_refl (or_introl (eq_trans (Nat.add_0_r i) E))) in HfIn; destruct HfIn. }
        assert (Hpp : i <> pp).
        { intros E; rewrite (Hno 0%nat r eq_refl (or_intror (eq_trans (Nat.add_0_r i) E))) in HfIn; destruct HfIn. }
        destruct (irqHead_rel i r (rs ++ sRevR :: post) (rs ++ iRevR :: post) ms mi mi' f envI envS v
                    HfIn Hrel0 Hcp Hpp Henv0 Hsem) as [ms' [Hs' [Hr' [E1 E2]]]].
        exists ms'; split; [exact Hs' |].
        cbn [MemRelPre]; split; [exact Hr' |].
        rewrite E1, E2; exact Hrel1.
      + rewrite nth_error_app2 in HkS by (rewrite length_map; exact Hge).
        rewrite nth_error_app2 in HkI by (rewrite !length_map; exact Hge).
        rewrite length_map, nth_error_map in HkS; rewrite !length_map, nth_error_map in HkI.
        apply option_map_Some_inv in HkS as [aS' [HaS' HkS]]; subst aS.
        apply option_map_Some_inv in HkI as [aI' [HaI' HkI]]; subst aI; cbv beta in Hsem |- *.
        apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
        assert (Hno' : forall j r0, nth_error (rs ++ sRevR :: post) j = Some r0 -> (S i + j = cp \/ S i + j = pp)%nat ->
                                   memRegionIrqActions core r0 = []).
        { intros j r0 Hr0 Hj; apply (Hno (S j) r0 Hr0); destruct Hj as [Hj | Hj]; [left | right]; lia. }
        destruct (IH (S i) ms.(Snd).(Fst) mi.(Snd).(Fst) mi'' _ aS' aI' _ _ v adv HaS' HaI' Hrel1 HR Hno'
                    (Henv1 ms) Hmi'') as [ms'' [Hs'' Hr'']].
        exists (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd))); split.
        * apply SemAction_liftAction_iff; exists ms''; split; [exact Hs'' | reflexivity].
        * cbn [MemRelPre]; split; [exact Hrel0 | exact Hr''].
  Qed.
End IrqRel.

(* --- fence.i Acks of One ExternalMem Region --- *)

Section FenceAckRegion.
  Variable core : string.

  (* The effect of one ack step on a region's spec part: `None` when `fenceIWait` was clear,
   * `Some ack` when the ack was received (fenceIWait was set) *)
  Definition AckUpd {r : MemRegion} (o : option bool) (s s' : TS (externalMemRegionTree core r)) : Prop :=
    match o with
    | None => s'.(Snd) = s.(Snd) /\ s'.(Fst) = s.(Fst)
    | Some b =>
        s'.(Snd) = s.(Snd) /\ s'.(Fst).(Fst) = s.(Fst).(Fst) /\ s'.(Fst).(Snd).(Fst) = s.(Fst).(Snd).(Fst) /\
        s'.(Fst).(Snd).(Snd).(Fst) = negb b /\
        s'.(Fst).(Snd).(Snd).(Snd).(Fst) = s.(Fst).(Snd).(Snd).(Snd).(Fst) /\
        s'.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) = b :: s.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) /\
        s.(Fst).(Snd).(Snd).(Fst) = true
    end.

  (* Same fenceIWait and an env that accepts the impl's ack: the spec takes the same step;
   * the impl env accepted the ack received *)
  Lemma extFenceIAck_sim :
    forall r (envI envS : Env (externalMemRegionTree core r)) (x z z' : TS (externalMemRegionTree core r)) v,
      x.(Fst).(Snd).(Snd).(Fst) = z.(Fst).(Snd).(Snd).(Fst) ->
      (forall ack, subEnv child0Path envI z z.(Fst) (pExtFetchFenceIAck core) ack ->
                   subEnv child0Path envS x x.(Fst) (pExtFetchFenceIAck core) ack) ->
      SemAction envI (@externalFenceIAckStep core r type) z z' v ->
      exists o x', SemAction envS (@externalFenceIAckStep core r type) x x' v /\ AckUpd o z z' /\ AckUpd o x x' /\
        (forall b, o = Some b -> subEnv child0Path envI z z.(Fst) (pExtFetchFenceIAck core) b).
  Proof.
    intros r envI envS x z z' v Hw Henv Hsem.
    unfold externalFenceIAckStep in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn in Hsem.
    destruct (z.(Fst).(Snd).(Snd).(Fst)) eqn:Hwait.
    - destruct Hsem as [ack [Hack Hrest]].
      pose proof (Henv ack Hack) as HackS.
      assert (HS : evalActionPropGen envS (@externalFenceIAckStep core r type) x
                     (fun x' v' => AckUpd (Some ack) x x' /\ v' = v)).
      { unfold externalFenceIAckStep; rewrite evalActionPropGen_liftAction; cbn.
        destruct (x.(Fst).(Snd).(Snd).(Fst)) eqn:HwaitS; [| exfalso; congruence].
        exists ack; split; [exact HackS |].
        destruct ack; cbn in Hrest |- *; destruct Hrest as [_ Hv];
          (split; [repeat split; cbn; first [reflexivity | exact HwaitS] | exact Hv]). }
      destruct (evalActionPropGen_to_SemAction _ _ _ HS) as [x' [v' [HsemS [Hupd Hv']]]]; subst v'.
      exists (Some ack), x'; split; [exact HsemS | split; [| split; [exact Hupd |
        intros b Eb; injection Eb as Eb; subst b; exact Hack]]].
      destruct ack; cbn in Hrest; destruct Hrest as [<- _]; repeat split; cbn; first [reflexivity | exact Hwait].
    - cbn in Hsem; destruct Hsem as [Hz Hv].
      assert (HS : evalActionPropGen envS (@externalFenceIAckStep core r type) x
                     (fun x' v' => AckUpd None x x' /\ v' = v)).
      { unfold externalFenceIAckStep; rewrite evalActionPropGen_liftAction; cbn.
        destruct (x.(Fst).(Snd).(Snd).(Fst)) eqn:HwaitS; [exfalso; congruence |].
        cbn; split; [split; reflexivity | exact Hv]. }
      destruct (evalActionPropGen_to_SemAction _ _ _ HS) as [x' [v' [HsemS [Hupd Hv']]]]; subst v'.
      exists None, x'; split; [exact HsemS | split; [| split; [exact Hupd | intros b Eb; discriminate Eb]]].
      subst z'; split; reflexivity.
  Qed.

  (* The ack step keeps ExtRel *)
  Lemma ExtRel_ack :
    forall r o (x x' : TS (externalMemRegionTree core r)) (y : TS (implExternalMemRegionTree core r))
           (z' : TS (externalMemRegionTree core r)),
      ExtRel core r x y -> @AckUpd r o y.(Fst) z' -> @AckUpd r o x x' -> ExtRel core r x' (z' ,, y.(Snd)).
  Proof.
    intros r o x x' y z' [E1 [E2 [E3 E4]]] Hz Hx.
    destruct o as [b |]; cbn [AckUpd] in Hz, Hx.
    - destruct Hz as [Z1 [Z2 [Z3 [Z4 [Z5 [Z6 _]]]]]], Hx as [X1 [X2 [X3 [X4 [X5 [X6 _]]]]]].
      unfold ExtRel, implAccWrites in *; cbn [Fst Snd] in *.
      split; [rewrite X1, Z1; exact E1 |].
      split; [rewrite X4, Z4; reflexivity |].
      split; [rewrite X5, Z5; exact E3 |].
      rewrite X6, Z6; cbn [count_true]; rewrite E4; reflexivity.
    - destruct Hz as [Z1 Z2], Hx as [X1 X2].
      unfold ExtRel, implAccWrites in *; cbn [Fst Snd] in *.
      rewrite X1, Z1, X2, Z2; exact (conj E1 (conj E2 (conj E3 E4))).
  Qed.
  (* The env condition at one region: for an ExternalMem region, an ack the impl env accepts is
   * accepted by the spec env when the region states are related, and it meets the constraint
   * of the region's write count oracle `fwc` *)
  Definition AckEnvAt (r : MemRegion) (fwc : nat -> nat) :
    Env (memRegionTree core r) -> Env (implMemRegionTree core r) ->
    TS (memRegionTree core r) -> TS (implMemRegionTree core r) -> Prop :=
    match r.(regionKind) as k
      return Env (memRegionKindTree core r k) -> Env (implMemRegionKindTree core r k) ->
             TS (memRegionKindTree core r k) -> TS (implMemRegionKindTree core r k) -> Prop
    with
    | ExternalMem => fun eS eI x y =>
        ExtRel core r x y ->
        forall ack, subEnv child0Path (subEnv child0Path eI y) y.(Fst) y.(Fst).(Fst) (pExtFetchFenceIAck core) ack ->
                    subEnv child0Path eS x x.(Fst) (pExtFetchFenceIAck core) ack /\
                    EnvFenceIAckAt fwc (length x.(Fst).(Snd).(Snd).(Snd).(Fst)) x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                                   (length x.(Snd).(Snd).(Snd).(Fst)) ack
    | CustomMem _ _ _ _ => fun _ _ _ _ => True
    end.

  (* `fwcs i`: the oracle of the region at position `i` *)
  Fixpoint EnvAckRel (fwcs : nat -> nat -> nat) (l : list MemRegion)
    : Env (specMemTree core l) -> Env (implRegionsTree core l) -> Prop :=
    match l as l0 return Env (specMemTree core l0) -> Env (implRegionsTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun envS envI =>
        (forall ms mi, AckEnvAt r (fwcs 0%nat) (subEnv child0Path envS ms) (subEnv child0Path envI mi) ms.(Fst) mi.(Fst)) /\
        (forall ms mi, EnvAckRel (fun i => fwcs (S i)) rs (subEnv child1Path envS ms) (subEnv child1Path envI mi))
    end.
End FenceAckRegion.

(* --- Region Changes Confined to fenceIWait and the fenceIAck Trace --- *)

Section AckFrameSec.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation WaitClearP :=
    (fun r (y : TS (implExternalMemRegionTree core r)) => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false).
  Local Abbreviation FenceICntP :=
    (fun r (y : TS (implExternalMemRegionTree core r)) => RegionFenceICountInv core r y.(Fst)).

  Lemma prod_ext : forall {A B : Type} (p q : A ** B), p.(Fst) = q.(Fst) -> p.(Snd) = q.(Snd) -> p = q.
  Proof. intros A B [a b] [c d]; cbn; intros -> ->; reflexivity. Qed.

  Definition RegionAckFrameS (r : MemRegion) : TS (memRegionTree core r) -> TS (memRegionTree core r) -> Prop :=
    match r.(regionKind) as k return TS (memRegionKindTree core r k) -> TS (memRegionKindTree core r k) -> Prop with
    | ExternalMem => fun x x' => exists w a, x' = setAcksS core r x w a
    | CustomMem _ _ _ _ => fun x x' => x' = x
    end.

  Definition RegionAckFrameI (r : MemRegion) : TS (implMemRegionTree core r) -> TS (implMemRegionTree core r) -> Prop :=
    match r.(regionKind) as k
      return TS (implMemRegionKindTree core r k) -> TS (implMemRegionKindTree core r k) -> Prop
    with
    | ExternalMem => fun y y' => exists w a, y' = setAcksI core r y w a
    | CustomMem _ _ _ _ => fun y y' => y' = y
    end.

  Fixpoint AckFrameS (l : list MemRegion) : TS (specMemTree core l) -> TS (specMemTree core l) -> Prop :=
    match l as l0 return TS (specMemTree core l0) -> TS (specMemTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun ms ms' => RegionAckFrameS r ms.(Fst) ms'.(Fst) /\ AckFrameS rs ms.(Snd).(Fst) ms'.(Snd).(Fst)
    end.

  Fixpoint AckFrameI (l : list MemRegion) : TS (implRegionsTree core l) -> TS (implRegionsTree core l) -> Prop :=
    match l as l0 return TS (implRegionsTree core l0) -> TS (implRegionsTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun mi mi' => RegionAckFrameI r mi.(Fst) mi'.(Fst) /\ AckFrameI rs mi.(Snd).(Fst) mi'.(Snd).(Fst)
    end.

  Lemma RegionAckFrameS_refl : forall r x, RegionAckFrameS r x x.
  Proof.
    intros r; unfold RegionAckFrameS, memRegionTree; destruct (regionKind r); intros x; [| reflexivity].
    exists x.(Fst).(Snd).(Snd).(Fst), x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst); reflexivity.
  Qed.

  Lemma RegionAckFrameI_refl : forall r y, RegionAckFrameI r y y.
  Proof.
    intros r; unfold RegionAckFrameI, implMemRegionTree; destruct (regionKind r); intros y; [| reflexivity].
    exists y.(Fst).(Fst).(Snd).(Snd).(Fst), y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst); reflexivity.
  Qed.

  Lemma AckFrameS_refl : forall l ms, AckFrameS l ms ms.
  Proof.
    induction l as [| r rs IH]; intros ms; cbn [AckFrameS]; [exact I | exact (conj (RegionAckFrameS_refl r _) (IH _))].
  Qed.

  Lemma AckFrameI_refl : forall l mi, AckFrameI l mi mi.
  Proof.
    induction l as [| r rs IH]; intros mi; cbn [AckFrameI]; [exact I | exact (conj (RegionAckFrameI_refl r _) (IH _))].
  Qed.

  Lemma AllPorts_ackFrame :
    forall P, AckInsensitive core P ->
      forall l mi mi', AckFrameI l mi mi' -> AllPorts core P l mi' = AllPorts core P l mi.
  Proof.
    intros P HP; induction l as [| r rs IH]; intros mi mi' H; cbn [AckFrameI AllPorts] in *; [reflexivity |].
    destruct H as [H0 H1]; rewrite (IH _ _ H1); f_equal.
    revert H0; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionAckFrameI, RegionPort, implMemRegionTree.
    destruct (regionKind r); intros y' y Hy; [destruct Hy as [w [a ->]]; exact (HP r y w a) | reflexivity].
  Qed.

  Lemma lineContent_ackFrame :
    forall l ms ms', AckFrameS l ms ms' -> forall L, lineContent core initLine l ms' L = lineContent core initLine l ms L.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H L; cbn [AckFrameS lineContent] in *; [reflexivity |].
    destruct H as [H0 H1]; rewrite (IH _ _ H1).
    destruct (isRegionAddrB r L); [| reflexivity].
    revert H0; generalize (ms'.(Fst)) (ms.(Fst)); unfold RegionAckFrameS, RegionLineContent, memRegionTree.
    destruct (regionKind r); intros x' x Hx; [destruct Hx as [w [a ->]]; reflexivity | reflexivity].
  Qed.

  Lemma regionStateAtS_ackFrame :
    forall l j r0 (pf : nth_error l j = Some r0) (ms ms' : TS (specMemTree core l)),
      AckFrameS l ms ms' -> isCustomR r0 ->
      regionStateAt (memRegionTree core) j l r0 pf ms' = regionStateAt (memRegionTree core) j l r0 pf ms.
  Proof.
    induction l as [| r rs IH]; intros [| j'] r0 pf ms ms' H Hc; try discriminate pf;
      cbn [AckFrameS] in H; destruct H as [H0 H1].
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      revert H0; generalize (ms'.(Fst)) (ms.(Fst)); unfold RegionAckFrameS, isCustomR, memRegionTree in *.
      destruct (regionKind r0); [contradiction | intros x' x Hx; exact Hx].
    - cbn [regionStateAt]; exact (IH j' r0 pf _ _ H1 Hc).
  Qed.

  Lemma regionStateAtI_ackFrame :
    forall l j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree core l)),
      AckFrameI l mi mi' -> isCustomR r0 ->
      regionStateAt (implMemRegionTree core) j l r0 pf mi' = regionStateAt (implMemRegionTree core) j l r0 pf mi.
  Proof.
    induction l as [| r rs IH]; intros [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [AckFrameI] in H; destruct H as [H0 H1].
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      revert H0; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionAckFrameI, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt]; exact (IH j' r0 pf _ _ H1 Hc).
  Qed.

  (* The effect of an ack step on its region (spec part `x`, impl region `y`) *)
  Definition RegionFenceFrame (r : MemRegion) (fwc : nat -> nat)
    (x x' : TS (memRegionTree core r)) (y y' : TS (implMemRegionTree core r)) : Prop :=
    ((x' = x /\ y' = y) \/ ~ RegionPort core WaitClearP r y) /\
    RegionAckFrameS r x x' /\ RegionAckFrameI r y y' /\
    (RegionSnapshotOK core r fwc x -> RegionSnapshotOK core r fwc x') /\
    (RegionPort core FenceICntP r y -> RegionPort core FenceICntP r y').

  (* ... and on the region lists: either nothing changed or some impl region waits for an ack *)
  Definition FenceFrame (fwcs : nat -> nat -> nat) (lS lI : list MemRegion)
    (ms ms' : TS (specMemTree core lS)) (mi mi' : TS (implRegionsTree core lI)) : Prop :=
    ((ms' = ms /\ mi' = mi) \/ ~ AllPorts core WaitClearP lI mi) /\
    AckFrameS lS ms ms' /\ AckFrameI lI mi mi' /\
    (SnapshotOK core fwcs lS ms -> SnapshotOK core fwcs lS ms') /\
    (AllPorts core FenceICntP lI mi -> AllPorts core FenceICntP lI mi').

  Lemma FenceFrame_head :
    forall fwcs r rsS rsI (ms ms' : TS (specMemTree core (r :: rsS))) (mi mi' : TS (implRegionsTree core (r :: rsI))),
      RegionFenceFrame r (fwcs 0%nat) ms.(Fst) ms'.(Fst) mi.(Fst) mi'.(Fst) ->
      ms'.(Snd) = ms.(Snd) -> mi'.(Snd) = mi.(Snd) ->
      FenceFrame fwcs (r :: rsS) (r :: rsI) ms ms' mi mi'.
  Proof.
    intros fwcs r rsS rsI ms ms' mi mi' [Fd [FS [FI [Fsn Ffc]]]] Es Ei.
    unfold FenceFrame; cbn [AckFrameS AckFrameI SnapshotOK AllPorts].
    split; [| split; [split; [exact FS | rewrite Es; apply AckFrameS_refl] |
             split; [split; [exact FI | rewrite Ei; apply AckFrameI_refl] |
             split; [intros [H0 H1]; split; [exact (Fsn H0) | rewrite Es; exact H1] |
                     intros [H0 H1]; split; [exact (Ffc H0) | rewrite Ei; exact H1]]]]].
    destruct Fd as [[Ex Ey] | Hw].
    - left; split; apply prod_ext; assumption.
    - right; intros [H0 _]; exact (Hw H0).
  Qed.

  Lemma FenceFrame_tail :
    forall fwcs rS rI rsS rsI (ms : TS (specMemTree core (rS :: rsS))) (mi : TS (implRegionsTree core (rI :: rsI)))
           (ms'' : TS (specMemTree core rsS)) (mi'' : TS (implRegionsTree core rsI)),
      FenceFrame (fun i => fwcs (S i)) rsS rsI ms.(Snd).(Fst) ms'' mi.(Snd).(Fst) mi'' ->
      FenceFrame fwcs (rS :: rsS) (rI :: rsI) ms (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd)))
                 mi (mi.(Fst) ,, (mi'' ,, mi.(Snd).(Snd))).
  Proof.
    intros fwcs rS rI rsS rsI ms mi ms'' mi'' [Fd [FS [FI [Fsn Ffc]]]].
    unfold FenceFrame; cbn [AckFrameS AckFrameI SnapshotOK AllPorts Fst Snd].
    split; [| split; [split; [apply RegionAckFrameS_refl | exact FS] |
             split; [split; [apply RegionAckFrameI_refl | exact FI] |
             split; [intros [H0 H1]; split; [exact H0 | exact (Fsn H1)] |
                     intros [H0 H1]; split; [exact H0 | exact (Ffc H1)]]]]].
    destruct Fd as [[-> ->] | Hw]; [left; split; reflexivity | right; intros [_ H1]; exact (Hw H1)].
  Qed.

  (* What one ack step does to an ExternalMem region, given the ack constraint of the env *)
  Lemma extFenceFrame :
    forall r fwc o (x x' : TS (externalMemRegionTree core r)) (y : TS (implExternalMemRegionTree core r)) z',
      @AckUpd core r o y.(Fst) z' -> @AckUpd core r o x x' ->
      (forall b, o = Some b ->
         EnvFenceIAckAt fwc (length x.(Fst).(Snd).(Snd).(Snd).(Fst)) x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                        (length x.(Snd).(Snd).(Snd).(Fst)) b) ->
      ((x' = x /\ (z' ,, y.(Snd)) = y) \/ y.(Fst).(Fst).(Snd).(Snd).(Fst) <> false) /\
      (exists w a, x' = setAcksS core r x w a) /\
      (exists w a, (z' ,, y.(Snd)) = setAcksI core r y w a) /\
      ((length x.(Snd).(Snd).(Snd).(Fst) >= fenceISnapshotCount fwc x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))%nat ->
       (length x'.(Snd).(Snd).(Snd).(Fst) >= fenceISnapshotCount fwc x'.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))%nat) /\
      (RegionFenceICountInv core r y.(Fst) -> RegionFenceICountInv core r z').
  Proof.
    intros r fwc o x x' y z' Hz Hx Henv.
    destruct o as [b |]; cbn [AckUpd] in Hz, Hx.
    - destruct Hz as [Z1 [Z2 [Z3 [Z4 [Z5 [Z6 Zw]]]]]], Hx as [X1 [X2 [X3 [X4 [X5 [X6 Xw]]]]]].
      assert (Ex : x' = setAcksS core r x (negb b) (b :: x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))).
      { revert X1 X2 X3 X4 X5 X6; destruct x' as [[q [p [w [fr [ak u]]]]] sn]; cbn [Fst Snd].
        intros -> -> -> -> -> ->; unfold setAcksS; destruct u.
        destruct (x.(Fst).(Snd).(Snd).(Snd).(Snd).(Snd)); reflexivity. }
      assert (Ez : z' = setAcksS core r y.(Fst) (negb b) (b :: y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))).
      { revert Z1 Z2 Z3 Z4 Z5 Z6; destruct z' as [[q [p [w [fr [ak u]]]]] sn]; cbn [Fst Snd].
        intros -> -> -> -> -> ->; unfold setAcksS; destruct u.
        destruct (y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Snd)); reflexivity. }
      split; [right; rewrite Zw; discriminate |].
      split; [exists (negb b), (b :: x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)); exact Ex |].
      split; [exists (negb b), (b :: y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)); rewrite Ez; reflexivity |].
      split.
      + intros Hs; rewrite X1, X6.
        destruct b; unfold fenceISnapshotCount in *; cbn [count_true] in *; [| exact Hs].
        destruct (Henv true eq_refl eq_refl) as [_ Hw]; rewrite Hw; lia.
      + unfold RegionFenceICountInv; cbv zeta; rewrite Zw, Z4, Z5, Z6.
        destruct b; cbn [negb count_true]; intros H; exact H.
    - destruct Hz as [Z1 Z2], Hx as [X1 X2].
      assert (Ex : x' = x) by (apply prod_ext; assumption).
      assert (Ez : z' = y.(Fst)) by (apply prod_ext; assumption).
      subst x' z'.
      split; [left; split; reflexivity |].
      split; [exists x.(Fst).(Snd).(Snd).(Fst), x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst); reflexivity |].
      split; [exists y.(Fst).(Fst).(Snd).(Snd).(Fst), y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst); reflexivity |].
      split; intros H; exact H.
  Qed.
End AckFrameSec.

(* --- fence.i Acks along the Region Lists --- *)

Section FenceList.
  Variable core : string.
  Variables cp pp : nat.
  Variable post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.
  Local Abbreviation sRevR := (specRevRegion core revBase revPfB revPfA).
  Local Abbreviation iRevR := (implRevRegion core revBase revPfB revPfA).

  Lemma fenceHead_rel :
    forall i r rsS rsI fwcs (ms : TS (specMemTree core (r :: rsS))) (mi mi' : TS (implRegionsTree core (r :: rsI)))
           (f : forall ty, Action ty (memRegionTree core r) (Bit 0)) envI envS v,
      In f (memRegionFenceIAckActions core r) ->
      RegionRelAt core cp pp i r ms.(Fst) mi.(Fst) ->
      AckEnvAt core r (fwcs 0%nat) (subEnv child0Path envS ms) (subEnv child0Path envI mi) ms.(Fst) mi.(Fst) ->
      SemAction envI (liftAction child0Path (liftToImplRegion (f type))) mi mi' v ->
      exists ms',
        SemAction envS (liftAction child0Path (f type)) ms ms' v /\
        RegionRelAt core cp pp i r ms'.(Fst) mi'.(Fst) /\ ms'.(Snd) = ms.(Snd) /\ mi'.(Snd) = mi.(Snd) /\
        FenceFrame core fwcs (r :: rsS) (r :: rsI) ms ms' mi mi'.
  Proof.
    intros i r rsS rsI fwcs ms mi mi' f envI envS v Hf Hrel Henv Hsem.
    apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
    unfold liftToImplRegion in Hy'.
    apply SemAction_liftAction_iff in Hy' as [z' [Hz' ->]].
    revert f Hf Hrel Henv Hz'.
    destruct r as [nm bs sz tg kd im ba sa]; destruct kd; cbn [memRegionFenceIAckActions regionKind In];
      intros f Hf; try contradiction.
    destruct Hf as [<- | []]; intros Hrel Henv Hz'.
    unfold RegionRelAt, AckEnvAt in Hrel, Henv; cbn [regionKind] in Hrel, Henv.
    pose proof Hrel as [_ [Hw _]].
    destruct (extFenceIAck_sim core _ (subEnv child0Path (subEnv child0Path envI mi) mi.(Fst)) (subEnv child0Path envS ms)
                ms.(Fst) mi.(Fst).(Fst) z' v Hw (fun ack H => proj1 (Henv Hrel ack H)) Hz')
      as [o [x' [HsS [HuZ [HuX Hacc]]]]].
    pose proof (extFenceFrame core _ (fwcs 0%nat) o ms.(Fst) x' mi.(Fst) z' HuZ HuX
                  (fun b Eb => proj2 (Henv Hrel b (Hacc b Eb)))) as [Fd [FS [FI [Fsn Ffc]]]].
    exists (x' ,, ms.(Snd)); split; [| split; [| split; [reflexivity | split; [reflexivity |]]]].
    - apply SemAction_liftAction_iff; exists x'; split; [exact HsS | reflexivity].
    - unfold RegionRelAt; cbn [regionKind].
      first [exact (ExtRel_ack core _ o _ x' _ z' Hrel HuZ HuX)
            | eapply ExtRel_ack; [exact Hrel | exact HuZ | exact HuX]].
    - apply FenceFrame_head; [| reflexivity | reflexivity].
      exact (conj Fd (conj FS (conj FI (conj Fsn Ffc)))).
  Qed.

  Lemma fencePost_rel :
    forall l i fwcs (ms : TS (specMemTree core l)) (mi mi' : TS (implRegionsTree core l)) k
           (aS : forall ty, Action ty (specMemTree core l) (Bit 0))
           (aI : forall ty, Action ty (implRegionsTree core l) (Bit 0)) envI envS v,
      nth_error (collectFenceIAckActions core l) k = Some aS ->
      nth_error (implCollectFenceIAckActions core l) k = Some aI ->
      MemRelPost core cp pp i l ms mi ->
      EnvAckRel core fwcs l envS envI ->
      SemAction envI (aI type) mi mi' v ->
      exists ms', SemAction envS (aS type) ms ms' v /\ MemRelPost core cp pp i l ms' mi' /\
                  FenceFrame core fwcs l l ms ms' mi mi'.
  Proof.
    induction l as [| r rs IH]; intros i fwcs ms mi mi' k aS aI envI envS v HkS HkI Hrel Henv Hsem;
      [unfold collectFenceIAckActions in HkS; destruct k; cbn in HkS; discriminate HkS |].
    unfold collectFenceIAckActions in HkS; cbn [genCollectRegionActions] in HkS.
    unfold implCollectFenceIAckActions, implCollectRegionActions in HkI; cbn [genCollectRegionActions] in HkI.
    unfold implMemRegionFenceIAckActions in HkI.
    cbn [MemRelPost EnvAckRel] in Hrel, Henv.
    destruct Hrel as [Hrel0 Hrel1], Henv as [Henv0 Henv1].
    destruct (Nat.lt_ge_cases k (length (memRegionFenceIAckActions core r))) as [Hlt | Hge].
    - rewrite nth_error_app1 in HkS by (rewrite length_map; exact Hlt).
      rewrite nth_error_app1 in HkI by (rewrite !length_map; exact Hlt).
      rewrite nth_error_map in HkS; rewrite !nth_error_map in HkI.
      apply option_map_Some_inv in HkS as [f [Hf HkS]]; subst aS.
      apply option_map_Some_inv in HkI as [y [Hy HkI]]; subst aI.
      apply option_map_Some_inv in Hy as [f' [Hf' Hy]]; subst y.
      assert (Ef : f' = f) by (pose proof (eq_trans (eq_sym Hf') Hf) as E; injection E as E; exact E).
      subst f'; cbv beta in Hsem |- *.
      assert (HfIn : In f (memRegionFenceIAckActions core r)) by (eapply nth_error_In; exact Hf).
      destruct (fenceHead_rel i r rs rs fwcs ms mi mi' f envI envS v HfIn Hrel0 (Henv0 ms mi) Hsem)
        as [ms' [Hs' [Hr' [E1 [E2 Hfr]]]]].
      exists ms'; split; [exact Hs' |]; split; [| exact Hfr].
      cbn [MemRelPost]; split; [exact Hr' |].
      rewrite E1, E2; exact Hrel1.
    - rewrite nth_error_app2 in HkS by (rewrite length_map; exact Hge).
      rewrite nth_error_app2 in HkI by (rewrite !length_map; exact Hge).
      rewrite length_map, nth_error_map in HkS; rewrite !length_map, nth_error_map in HkI.
      apply option_map_Some_inv in HkS as [aS' [HaS' HkS]]; subst aS.
      apply option_map_Some_inv in HkI as [aI' [HaI' HkI]]; subst aI; cbv beta in Hsem |- *.
      apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
      destruct (IH (S i) (fun j => fwcs (S j)) ms.(Snd).(Fst) mi.(Snd).(Fst) mi'' _ aS' aI' _ _ v HaS' HaI' Hrel1
                  (Henv1 ms mi) Hmi'') as [ms'' [Hs'' [Hr'' Hfr'']]].
      exists (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd))); split; [| split].
      + apply SemAction_liftAction_iff; exists ms''; split; [exact Hs'' | reflexivity].
      + cbn [MemRelPost]; split; [exact Hrel0 | exact Hr''].
      + exact (FenceFrame_tail core fwcs r r rs rs ms mi ms'' mi'' Hfr'').
  Qed.

  (* The env condition along `l ++ rev :: post`, skipping the revoker position *)
  Fixpoint EnvAckPre (fwcs : nat -> nat -> nat) (l : list MemRegion)
    : Env (specMemTree core (l ++ sRevR :: post)) -> Env (implRegionsTree core (l ++ iRevR :: post)) -> Prop :=
    match l as l0
      return Env (specMemTree core (l0 ++ sRevR :: post)) -> Env (implRegionsTree core (l0 ++ iRevR :: post)) -> Prop
    with
    | [] => fun envS envI =>
        forall ms mi, EnvAckRel core (fun i => fwcs (S i)) post (subEnv child1Path envS ms) (subEnv child1Path envI mi)
    | r :: rs => fun envS envI =>
        (forall ms mi, AckEnvAt core r (fwcs 0%nat) (subEnv child0Path envS ms) (subEnv child0Path envI mi) ms.(Fst) mi.(Fst)) /\
        (forall ms mi, EnvAckPre (fun i => fwcs (S i)) rs (subEnv child1Path envS ms) (subEnv child1Path envI mi))
    end.

  Lemma fencePre_rel :
    forall l i fwcs (ms : TS (specMemTree core (l ++ sRevR :: post)))
           (mi mi' : TS (implRegionsTree core (l ++ iRevR :: post))) k
           (aS : forall ty, Action ty (specMemTree core (l ++ sRevR :: post)) (Bit 0))
           (aI : forall ty, Action ty (implRegionsTree core (l ++ iRevR :: post)) (Bit 0)) envI envS v,
      nth_error (collectFenceIAckActions core (l ++ sRevR :: post)) k = Some aS ->
      nth_error (implCollectFenceIAckActions core (l ++ iRevR :: post)) k = Some aI ->
      MemRelPre core cp pp i l sRevR iRevR post ms mi ->
      EnvAckPre fwcs l envS envI ->
      SemAction envI (aI type) mi mi' v ->
      exists ms', SemAction envS (aS type) ms ms' v /\ MemRelPre core cp pp i l sRevR iRevR post ms' mi' /\
                  FenceFrame core fwcs (l ++ sRevR :: post) (l ++ iRevR :: post) ms ms' mi mi'.
  Proof.
    induction l as [| r rs IH]; intros i fwcs ms mi mi' k aS aI envI envS v HkS HkI Hrel Henv Hsem.
    - unfold collectFenceIAckActions in HkS; cbn [genCollectRegionActions app] in HkS.
      unfold implCollectFenceIAckActions, implCollectRegionActions in HkI; cbn [genCollectRegionActions app] in HkI.
      cbn [MemRelPre EnvAckPre] in Hrel, Henv.
      rewrite nth_error_app2 in HkS by (cbn; lia).
      rewrite nth_error_app2 in HkI by (cbn; lia).
      rewrite nth_error_map in HkS, HkI.
      apply option_map_Some_inv in HkS as [aS' [HaS' HkS]]; subst aS.
      apply option_map_Some_inv in HkI as [aI' [HaI' HkI]]; subst aI; cbv beta in Hsem |- *.
      apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
      destruct (fencePost_rel post (S i) (fun j => fwcs (S j)) ms.(Snd).(Fst) mi.(Snd).(Fst) mi'' _ aS' aI' _ _ v
                  HaS' HaI' Hrel (Henv ms mi) Hmi'') as [ms'' [Hs'' [Hr'' Hfr'']]].
      exists (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd))); split; [| split].
      + apply SemAction_liftAction_iff; exists ms''; split; [exact Hs'' | reflexivity].
      + exact Hr''.
      + exact (FenceFrame_tail core fwcs sRevR iRevR post post ms mi ms'' mi'' Hfr'').
    - unfold collectFenceIAckActions in HkS; cbn [genCollectRegionActions app] in HkS.
      unfold implCollectFenceIAckActions, implCollectRegionActions in HkI; cbn [genCollectRegionActions app] in HkI.
      unfold implMemRegionFenceIAckActions in HkI.
      cbn [MemRelPre EnvAckPre] in Hrel, Henv.
      destruct Hrel as [Hrel0 Hrel1], Henv as [Henv0 Henv1].
      destruct (Nat.lt_ge_cases k (length (memRegionFenceIAckActions core r))) as [Hlt | Hge].
      + rewrite nth_error_app1 in HkS by (rewrite length_map; exact Hlt).
        rewrite nth_error_app1 in HkI by (rewrite !length_map; exact Hlt).
        rewrite nth_error_map in HkS; rewrite !nth_error_map in HkI.
        apply option_map_Some_inv in HkS as [f [Hf HkS]]; subst aS.
        apply option_map_Some_inv in HkI as [y [Hy HkI]]; subst aI.
        apply option_map_Some_inv in Hy as [f' [Hf' Hy]]; subst y.
        assert (Ef : f' = f) by (pose proof (eq_trans (eq_sym Hf') Hf) as E; injection E as E; exact E).
        subst f'; cbv beta in Hsem |- *.
        assert (HfIn : In f (memRegionFenceIAckActions core r)) by (eapply nth_error_In; exact Hf).
        destruct (fenceHead_rel i r _ _ fwcs ms mi mi' f envI envS v HfIn Hrel0 (Henv0 ms mi) Hsem)
          as [ms' [Hs' [Hr' [E1 [E2 Hfr]]]]].
        exists ms'; split; [exact Hs' |]; split; [| exact Hfr].
        cbn [MemRelPre]; split; [exact Hr' |].
        rewrite E1, E2; exact Hrel1.
      + rewrite nth_error_app2 in HkS by (rewrite length_map; exact Hge).
        rewrite nth_error_app2 in HkI by (rewrite !length_map; exact Hge).
        rewrite length_map, nth_error_map in HkS; rewrite !length_map, nth_error_map in HkI.
        apply option_map_Some_inv in HkS as [aS' [HaS' HkS]]; subst aS.
        apply option_map_Some_inv in HkI as [aI' [HaI' HkI]]; subst aI; cbv beta in Hsem |- *.
        apply SemAction_liftAction_iff in Hsem as [mi'' [Hmi'' ->]].
        destruct (IH (S i) (fun j => fwcs (S j)) ms.(Snd).(Fst) mi.(Snd).(Fst) mi'' _ aS' aI' _ _ v HaS' HaI' Hrel1
                    (Henv1 ms mi) Hmi'') as [ms'' [Hs'' [Hr'' Hfr'']]].
        exists (ms.(Fst) ,, (ms'' ,, ms.(Snd).(Snd))); split; [| split].
        * apply SemAction_liftAction_iff; exists ms''; split; [exact Hs'' | reflexivity].
        * cbn [MemRelPre]; split; [exact Hrel0 | exact Hr''].
        * exact (FenceFrame_tail core fwcs r r _ _ ms mi ms'' mi'' Hfr'').
  Qed.

  Lemma length_implFenceCollect :
    forall l, length (implCollectFenceIAckActions core l) = length (collectFenceIAckActions core l).
  Proof.
    induction l as [| r rs IH]; [reflexivity |].
    unfold implCollectFenceIAckActions, implCollectRegionActions, collectFenceIAckActions in *;
      cbn [genCollectRegionActions].
    rewrite !length_app, !length_map.
    apply (f_equal2 Nat.add); [unfold implMemRegionFenceIAckActions; apply length_map | exact IH].
  Qed.

  Lemma length_fenceCollect_rev :
    forall l, length (collectFenceIAckActions core (l ++ iRevR :: post)) =
              length (collectFenceIAckActions core (l ++ sRevR :: post)).
  Proof.
    induction l as [| r rs IH]; unfold collectFenceIAckActions in *; cbn [genCollectRegionActions app];
      rewrite !length_app, !length_map; [reflexivity | apply (f_equal2 Nat.add); [reflexivity | exact IH]].
  Qed.
End FenceList.

(* --- The ack Constraint of the Region Envs --- *)

Section FenceEnv.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma specExtEnv_ack :
    forall r fwc (x : TS (externalMemRegionTree core r)) ack,
      EnvFenceIAckAt fwc (length x.(Fst).(Snd).(Snd).(Snd).(Fst)) x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                     (length x.(Snd).(Snd).(Snd).(Fst)) ack ->
      subEnv child0Path (specExtRegionEnv core initLine r fwc) x x.(Fst) (pExtFetchFenceIAck core) ack.
  Proof.
    intros r fwc x ack H.
    unfold subEnv, cast_recv_inv, specExtRegionEnv, extRegionEnvCtx, extFetchEnvCtx.
    cbn -[eq_rect EnvFenceIAckAt].
    rewrite !eq_rect_Kind_refl.
    exact H.
  Qed.

  Lemma implExtEnv_ack :
    forall r fwc (y : TS (implExternalMemRegionTree core r)) ack,
      subEnv child0Path (subEnv child0Path (implExtRegionEnv core initLine r fwc) y) y.(Fst) y.(Fst).(Fst)
        (pExtFetchFenceIAck core) ack ->
      EnvFenceIAckAt fwc (length y.(Fst).(Fst).(Snd).(Snd).(Snd).(Fst)) y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                     (length (implAccWrites core r y)) ack.
  Proof.
    intros r fwc y ack H.
    unfold subEnv, cast_recv_inv, implExtRegionEnv, extRegionEnvCtx, extFetchEnvCtx in H.
    cbn -[eq_rect EnvFenceIAckAt implAccWrites] in H.
    rewrite !eq_rect_Kind_refl in H.
    exact H.
  Qed.
End FenceEnv.

(* --- The Real Region Envs along the Region Lists --- *)

Section FenceEnvList.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma Is_true_pi : forall (b : bool) (p q : Is_true b), p = q.
  Proof. intros [|] p q; [destruct p, q; reflexivity | destruct p]. Qed.

  Lemma subEnvS0 :
    forall r rs (env : Env (specMemTree core (r :: rs))) (ms : TS (specMemTree core (r :: rs))) sub
           (x : RecvPath (memRegionTree core r)) (v : type (getRecvKind x)),
      subEnv child0Path env ms sub x v = env (writeSubTreeState child0Path ms sub) (embedRecvPath child0Path x) v.
  Proof. intros; unfold subEnv; f_equal; unfold cast_recv_inv; apply eq_rect_Kind_refl. Qed.

  Lemma subEnvS1 :
    forall r rs (env : Env (specMemTree core (r :: rs))) (ms : TS (specMemTree core (r :: rs))) sub
           (x : RecvPath (specMemTree core rs)) (v : type (getRecvKind x)),
      subEnv child1Path env ms sub x v = env (writeSubTreeState child1Path ms sub) (embedRecvPath child1Path x) v.
  Proof. intros; unfold subEnv; f_equal; unfold cast_recv_inv; apply eq_rect_Kind_refl. Qed.

  Lemma subEnvI0 :
    forall r rs (env : Env (implRegionsTree core (r :: rs))) (mi : TS (implRegionsTree core (r :: rs))) sub
           (x : RecvPath (implMemRegionTree core r)) (v : type (getRecvKind x)),
      subEnv child0Path env mi sub x v = env (writeSubTreeState child0Path mi sub) (embedRecvPath child0Path x) v.
  Proof. intros; unfold subEnv; f_equal; unfold cast_recv_inv; apply eq_rect_Kind_refl. Qed.

  Lemma subEnvI1 :
    forall r rs (env : Env (implRegionsTree core (r :: rs))) (mi : TS (implRegionsTree core (r :: rs))) sub
           (x : RecvPath (implRegionsTree core rs)) (v : type (getRecvKind x)),
      subEnv child1Path env mi sub x v = env (writeSubTreeState child1Path mi sub) (embedRecvPath child1Path x) v.
  Proof. intros; unfold subEnv; f_equal; unfold cast_recv_inv; apply eq_rect_Kind_refl. Qed.

  (* The spec memory env accepts what the regions env accepts (same path, same value) *)
  Definition SpecEnvOK (l : list MemRegion) (fwcs : nat -> nat -> nat) (env : Env (specMemTree core l)) : Prop :=
    forall s (lp : LeafPath (specMemTree core l)) pf' (v : type (getRecvKindFromPath lp)),
      (forall pf, specRegionsEnv core initLine fwcs l s (@Build_RecvPath (specMemTree core l) lp pf) v) ->
      env s (@Build_RecvPath (specMemTree core l) lp pf') v.

  (* The impl regions env accepts only what the regions env accepts *)
  Definition ImplEnvOK (l : list MemRegion) (fwcs : nat -> nat -> nat) (env : Env (implRegionsTree core l)) : Prop :=
    forall s (lp : LeafPath (implRegionsTree core l)) pf (v : type (getRecvKindFromPath lp)),
      env s (@Build_RecvPath (implRegionsTree core l) lp pf) v ->
      forall pf', implRegionsEnv core initLine fwcs l s (@Build_RecvPath (implRegionsTree core l) lp pf') v.

  Lemma SpecEnvOK_head :
    forall r rs fwcs (env : Env (specMemTree core (r :: rs))) (ms : TS (specMemTree core (r :: rs))),
      SpecEnvOK (r :: rs) fwcs env ->
      forall sub (x : RecvPath (memRegionTree core r)) (v : type (getRecvKind x)),
        specRegionEnv core initLine r (fwcs 0%nat) sub x v -> subEnv child0Path env ms sub x v.
  Proof.
    intros r rs fwcs env ms H sub [lp q] v Hx.
    rewrite subEnvS0.
    apply H; intros pf.
    cbn [specRegionsEnv]; unfold envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionEnv specRegionsEnv].
    match goal with |- context [@Build_RecvPath _ lp ?q'] => rewrite (Is_true_pi _ q' q) end.
    exact Hx.
  Qed.

  Lemma SpecEnvOK_tail :
    forall r rs fwcs (env : Env (specMemTree core (r :: rs))) (ms : TS (specMemTree core (r :: rs))),
      SpecEnvOK (r :: rs) fwcs env -> SpecEnvOK rs (fun i => fwcs (S i)) (subEnv child1Path env ms).
  Proof.
    intros r rs fwcs env ms H s lp pf' v Hx.
    rewrite subEnvS1.
    apply H; intros pf.
    cbn [specRegionsEnv]; unfold envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionEnv specRegionsEnv].
    apply Hx.
  Qed.

  Lemma ImplEnvOK_head :
    forall r rs fwcs (env : Env (implRegionsTree core (r :: rs))) (mi : TS (implRegionsTree core (r :: rs))),
      ImplEnvOK (r :: rs) fwcs env ->
      forall sub (x : RecvPath (implMemRegionTree core r)) (v : type (getRecvKind x)),
        subEnv child0Path env mi sub x v -> implRegionEnv core initLine r (fwcs 0%nat) sub x v.
  Proof.
    intros r rs fwcs env mi H sub [lp pf] v Hx.
    rewrite subEnvI0 in Hx.
    pose proof (H _ _ _ _ Hx) as H'.
    specialize (H' (embedRecvPath child0Path (@Build_RecvPath _ lp pf)).(recvPathPf)).
    cbn [implRegionsEnv] in H'; unfold envNodeCons, envCtxCons, envCtxMap in H';
      cbn -[implRegionEnv implRegionsEnv] in H'.
    match type of H' with context [@Build_RecvPath _ lp ?q] => rewrite (Is_true_pi _ q pf) in H' end.
    exact H'.
  Qed.

  Lemma ImplEnvOK_tail :
    forall r rs fwcs (env : Env (implRegionsTree core (r :: rs))) (mi : TS (implRegionsTree core (r :: rs))),
      ImplEnvOK (r :: rs) fwcs env -> ImplEnvOK rs (fun i => fwcs (S i)) (subEnv child1Path env mi).
  Proof.
    intros r rs fwcs env mi H s lp pf v Hx pf'.
    rewrite subEnvI1 in Hx.
    pose proof (H _ _ _ _ Hx) as H'.
    specialize (H' (embedRecvPath child1Path (@Build_RecvPath _ lp pf)).(recvPathPf)).
    cbn [implRegionsEnv] in H'; unfold envNodeCons, envCtxCons, envCtxMap in H';
      cbn -[implRegionEnv implRegionsEnv] in H'.
    match type of H' with context [@Build_RecvPath _ lp ?q] => rewrite (Is_true_pi _ q pf') in H' end.
    exact H'.
  Qed.

  Lemma ExtRel_envAck :
    forall r fwc (x : TS (externalMemRegionTree core r)) (y : TS (implExternalMemRegionTree core r)) ack,
      ExtRel core r x y ->
      EnvFenceIAckAt fwc (length y.(Fst).(Fst).(Snd).(Snd).(Snd).(Fst)) y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                     (length (implAccWrites core r y)) ack ->
      EnvFenceIAckAt fwc (length x.(Fst).(Snd).(Snd).(Snd).(Fst)) x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                     (length x.(Snd).(Snd).(Snd).(Fst)) ack.
  Proof.
    intros r fwc x y ack [E1 [_ [E3 E4]]]; unfold EnvFenceIAckAt; rewrite E1, E3, E4; exact (fun H => H).
  Qed.

  Lemma AckEnvAt_of_heads :
    forall r fwc (eS : Env (memRegionTree core r)) (eI : Env (implMemRegionTree core r)) x y,
      (forall sub (p : RecvPath (memRegionTree core r)) (v : type (getRecvKind p)),
         specRegionEnv core initLine r fwc sub p v -> eS sub p v) ->
      (forall sub (p : RecvPath (implMemRegionTree core r)) (v : type (getRecvKind p)),
         eI sub p v -> implRegionEnv core initLine r fwc sub p v) ->
      AckEnvAt core r fwc eS eI x y.
  Proof.
    intros r fwc; destruct r as [nm bs sz tg kd im ba sa]; destruct kd; cbn [AckEnvAt regionKind];
      intros eS eI x y HS HI; [| exact I].
    intros Hrel ack Hack.
    unfold subEnv in Hack.
    apply HI in Hack.
    pose proof (implExtEnv_ack core initLine _ fwc y ack Hack) as HE.
    pose proof (ExtRel_envAck _ fwc x y ack Hrel HE) as HE'.
    split; [| exact HE'].
    unfold subEnv; apply HS.
    exact (specExtEnv_ack core initLine _ fwc x ack HE').
  Qed.

  Lemma EnvAckRel_real :
    forall l fwcs (envS : Env (specMemTree core l)) (envI : Env (implRegionsTree core l)),
      SpecEnvOK l fwcs envS -> ImplEnvOK l fwcs envI -> EnvAckRel core fwcs l envS envI.
  Proof.
    induction l as [| r rs IH]; intros fwcs envS envI HS HI; cbn [EnvAckRel]; [exact I |].
    split; intros ms mi.
    - apply AckEnvAt_of_heads.
      + exact (SpecEnvOK_head r rs fwcs envS ms HS).
      + exact (ImplEnvOK_head r rs fwcs envI mi HI).
    - apply (IH (fun i => fwcs (S i))).
      + exact (SpecEnvOK_tail r rs fwcs envS ms HS).
      + exact (ImplEnvOK_tail r rs fwcs envI mi HI).
  Qed.

  Lemma EnvAckPre_real :
    forall post revBase
           (revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z) l fwcs
           (envS : Env (specMemTree core (l ++ specRevRegion core revBase revPfB revPfA :: post)))
           (envI : Env (implRegionsTree core (l ++ implRevRegion core revBase revPfB revPfA :: post))),
      SpecEnvOK (l ++ specRevRegion core revBase revPfB revPfA :: post) fwcs envS ->
      ImplEnvOK (l ++ implRevRegion core revBase revPfB revPfA :: post) fwcs envI ->
      EnvAckPre core post revBase revPfB revPfA fwcs l envS envI.
  Proof.
    intros post revBase revPfB revPfA.
    induction l as [| r rs IH]; intros fwcs envS envI HS HI; cbn [EnvAckPre].
    - intros ms mi.
      apply (EnvAckRel_real post (fun i => fwcs (S i))).
      + exact (SpecEnvOK_tail _ _ fwcs envS ms HS).
      + exact (ImplEnvOK_tail _ _ fwcs envI mi HI).
    - split; intros ms mi.
      + apply AckEnvAt_of_heads.
        * exact (SpecEnvOK_head r _ fwcs envS ms HS).
        * exact (ImplEnvOK_head r _ fwcs envI mi HI).
      + apply (IH (fun i => fwcs (S i))).
        * exact (SpecEnvOK_tail r _ fwcs envS ms HS).
        * exact (ImplEnvOK_tail r _ fwcs envI mi HI).
  Qed.
End FenceEnvList.

Section Periph.
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

  Local Abbreviation revSpec := (revSpecOf core pre post revBase revPfB revPfA).
  Local Abbreviation ITree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation STree := (SpecTree core pcAddrInit specRegions).
  Local Abbreviation envI :=
    (implEnv core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv core pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (map snd (@spec core pcAddrInit config specRegions clintS revSpec plicS type)).
  Local Abbreviation REL :=
    (RefRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).

  Definition StepOK (act : Action type ITree (Bit 0)) : Prop :=
    forall (s1 s1' : TS ITree) (s2 : TS STree),
      SemAction envI act s1 s1' Zmod.zero ->
      REL s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.

  (* --- 1. Can-Proceed Flags (stutter; the flags are not part of the relation) --- *)

  Lemma stepOK_setFetchCanProceed :
    StepOK (@setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold setFetchCanProceedStage, setFetchCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew _]; subst s1'.
    exists s2; split; [apply NilAction; reflexivity |].
    exists g; destruct Hg; constructor; assumption.
  Qed.

  Lemma stepOK_setDecodeCanProceed :
    StepOK (@setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold setDecodeCanProceedStage, setDecodeCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew _]; subst s1'.
    exists s2; split; [apply NilAction; reflexivity |].
    exists g; destruct Hg; constructor; assumption.
  Qed.

  Lemma stepOK_setExecuteCanProceed :
    StepOK (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold setExecuteCanProceedStage, setExecuteCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew _]; subst s1'.
    exists s2; split; [apply NilAction; reflexivity |].
    exists g; destruct Hg; constructor; assumption.
  Qed.

  Theorem stepOK_setCanProceedSteps :
    forall act,
      In act (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type) ->
      StepOK act.
  Proof.
    intros act Hin; cbn [setCanProceedSteps In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]].
    - apply stepOK_setFetchCanProceed.
    - apply stepOK_setDecodeCanProceed.
    - apply stepOK_setExecuteCanProceed.
  Qed.

  (* --- 2. Positions of the Devices --- *)

  (* The spec and impl instances name the same positions of the shared list *)
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation sRevR := (specRevRegion core revBase revPfB revPfA).
  Local Abbreviation iRevR := (implRevRegion core revBase revPfB revPfA).

  Lemma nth_impl_rev : nth_error implRegions (length pre) = Some iRevR.
  Proof. exact (nth_error_app_cons_len pre iRevR post). Qed.

  Lemma nth_spec_rev : nth_error specRegions (length pre) = Some sRevR.
  Proof. exact (nth_error_app_cons_len pre sRevR post). Qed.

  Lemma clint_ne_rev : clintIdx clint <> length pre.
  Proof.
    intros E; pose proof (pfClint clint) as H; rewrite E, nth_impl_rev in H.
    discriminate H.
  Qed.

  Lemma clintS_ne_rev : clintIdx clintS <> length pre.
  Proof.
    intros E; pose proof (pfClint clintS) as H; rewrite E, nth_spec_rev in H.
    discriminate H.
  Qed.

  Lemma plic_ne_rev : plicIdx plic <> length pre.
  Proof.
    intros E; pose proof (pfPlic plic) as H; rewrite E, nth_impl_rev in H.
    discriminate H.
  Qed.

  Lemma plicS_ne_rev : plicIdx plicS <> length pre.
  Proof.
    intros E; pose proof (pfPlic plicS) as H; rewrite E, nth_spec_rev in H.
    discriminate H.
  Qed.

  Lemma clint_ne_plic : clintIdx clint <> plicIdx plic.
  Proof.
    intros E; pose proof (pfClint clint) as H1; pose proof (pfPlic plic) as H2.
    rewrite E, H2 in H1; discriminate H1.
  Qed.

  Lemma clintS_ne_plicS : clintIdx clintS <> plicIdx plicS.
  Proof.
    intros E; pose proof (pfClint clintS) as H1; pose proof (pfPlic plicS) as H2.
    rewrite E, H2 in H1; discriminate H1.
  Qed.

  (* --- 3. Device Steps --- *)

  Local Abbreviation IREG := (iRegions core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation IMEM := (iMem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation SMEM := (sMem core pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation NPMI := (Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation NPMS := (Spec.np_mem core pcAddrInit specRegions).

  (* An impl step of the device at position `idx` runs its action on the device state *)
  Lemma SemAction_implDevStep :
    forall env idx r0 (pf : nth_error implRegions idx = Some r0) (act : Action type (memRegionTree core r0) (Bit 0))
           (s1 s1' : TS ITree) v,
      SemAction env (liftAction NPMI (@implNthRegionAction core type idx implRegions r0 pf (Bit 0) act)) s1 s1' v ->
      exists envR x',
        SemAction envR act (regionStateAt (implMemRegionTree core) idx implRegions r0 pf (IREG s1)).(Fst) x' v /\
        s1' = writeSubTreeState NPMI s1
                (updRegionStateAt (implMemRegionTree core) idx implRegions r0 pf (IREG s1)
                   (x' ,, (regionStateAt (implMemRegionTree core) idx implRegions r0 pf (IREG s1)).(Snd))
                 ,, (IMEM s1).(Snd)).
  Proof.
    intros env idx r0 pf act s1 s1' v Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' ->]].
    unfold implNthRegionAction in Hm'.
    apply SemAction_liftAction_iff in Hm' as [rg' [Hrg' ->]].
    unfold implRegionsNthRegionAction in Hrg'.
    apply SemAction_genNthRegionAction_iff in Hrg' as [y' [Hy' ->]].
    unfold liftToImplRegion in Hy'.
    apply SemAction_liftAction_iff in Hy' as [x' [Hx' ->]].
    do 2 eexists; split; [exact Hx' | reflexivity].
  Qed.

  (* A spec step of the device at position `idx` from a device-level step *)
  Lemma SemAction_specDevStep_intro :
    forall env idx r0 (pf : nth_error specRegions idx = Some r0) (act : Action type (memRegionTree core r0) (Bit 0))
           (s2 : TS STree) x' v,
      (forall envR, SemAction envR act (regionStateAt (memRegionTree core) idx specRegions r0 pf (SMEM s2)) x' v) ->
      SemAction env (liftAction NPMS (@nthRegionAction core type idx specRegions r0 pf (Bit 0) act)) s2
        (writeSubTreeState NPMS s2 (updRegionStateAt (memRegionTree core) idx specRegions r0 pf (SMEM s2) x')) v.
  Proof.
    intros env idx r0 pf act s2 x' v Hx.
    apply SemAction_liftAction_iff; eexists; split; [| reflexivity].
    unfold nthRegionAction.
    apply SemAction_genNthRegionAction_iff; eexists; split; [apply Hx | reflexivity].
  Qed.

  (* --- 4. CLINT --- *)

  (* Sampling MTIP: impl only, the spec stutters (its sampledMtip may lag) *)
  Lemma stepOK_implSampleMtipStep :
    StepOK (@implSampleMtipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions clint type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implSampleMtipStep in Hsem.
    apply SemAction_implDevStep in Hsem as [envR [x' [Hx' E1]]].
    apply clintSample_eq in Hx'.
    assert (Hreg : IREG s1' =
                   updRegionStateAt (implMemRegionTree core) (clintIdx clint) implRegions (clintRegion clint) (pfClint clint)
                     (IREG s1)
                     (x' ,, (regionStateAt (implMemRegionTree core) (clintIdx clint) implRegions (clintRegion clint)
                               (pfClint clint) (IREG s1)).(Snd)))
      by (rewrite E1; reflexivity).
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    exists s2; split; [apply NilAction; reflexivity |].
    exists g.
    eapply RefRelG_regions_frame with (ms' := SMEM s2); [exact E1 | reflexivity | | | | | | | exact Hg].
    - intros P; rewrite Hreg; apply AllPorts_upd; exact I.
    - unfold iRev, implRevState; rewrite Hreg, regionStateAt_upd_other; [reflexivity | exact clint_ne_rev].
    - intros L; reflexivity.
    - apply FetchViewExt_refl.
    - unfold MemRelC, MemRel, DevInv in *.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
      rewrite Hreg.
      unfold implClintState, implPlicState, implRevState in *.
      rewrite regionStateAt_updRegionStateAt.
      rewrite !(regionStateAt_upd_other (implMemRegionTree core) (clintIdx clint))
        by first [exact clint_ne_plic | exact clint_ne_rev].
      cbn [Fst].
      rewrite Hx'.
      refine (conj (conj _ (conj _ (conj Hpl Hrv))) (conj (conj _ Hpi) Hsnap)).
      + exact (MemRelPre_upd_impl core (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                 (clintIdx clintS) (clintIdx clint) (clintRegion clintS) (clintRegion clint)
                 (pfClint clintS) (pfClint clint) _ _ _ HclintIdx clintS_ne_rev
                 (fun x y => or_introl eq_refl) Hpre).
      + exact (ClintRel_sample core _ _ Hcl).
      + exact (ClintInv_sample core _ Hci).
    - exact Hl.
  Qed.

  (* Timer tick: lockstep with the spec tick *)
  Lemma stepOK_implTickTimer :
    StepOK (@implTickTimer core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions clint type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implTickTimer in Hsem.
    apply SemAction_implDevStep in Hsem as [envR [x' [Hx' E1]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    unfold MemRelC, MemRel, DevInv in Hm.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold specClintState, implClintState in Hcl, Hci.
    set (xs := regionStateAt (memRegionTree core) (clintIdx clintS) specRegions (clintRegion clintS) (pfClint clintS)
                 (SMEM s2)) in *.
    destruct (clintTick_rel core envR envR _ x' xs Zmod.zero Hx' (proj1 Hcl)) as [_ Hsamp].
    set (xs' := clintWithSampled core (andb (clintSampled core xs) (clintMtip core x')) x').
    set (ms' := updRegionStateAt (memRegionTree core) (clintIdx clintS) specRegions (clintRegion clintS)
                  (pfClint clintS) (SMEM s2) xs').
    assert (Es : SMEM (writeSubTreeState NPMS s2 ms') = ms') by reflexivity.
    assert (Hreg : IREG s1' =
                   updRegionStateAt (implMemRegionTree core) (clintIdx clint) implRegions (clintRegion clint) (pfClint clint)
                     (IREG s1)
                     (x' ,, (regionStateAt (implMemRegionTree core) (clintIdx clint) implRegions (clintRegion clint)
                               (pfClint clint) (IREG s1)).(Snd)))
      by (rewrite E1; reflexivity).
    exists (writeSubTreeState NPMS s2 ms'); split.
    - eapply ConsAction;
        [apply (In_specTickTimer_spec core pcAddrInit config specRegions clintS revSpec plicS) | |
         apply NilAction; reflexivity].
      unfold specTickTimer, clintTickAction, clintAction.
      apply SemAction_specDevStep_intro.
      intros envR'.
      exact (proj1 (clintTick_rel core envR envR' _ x' xs Zmod.zero Hx' (proj1 Hcl))).
    - exists g.
      eapply RefRelG_regions_frame; [exact E1 | reflexivity | | | | | | | exact Hg].
      + intros P; rewrite Hreg; apply AllPorts_upd; exact I.
      + unfold iRev, implRevState; rewrite Hreg, regionStateAt_upd_other; [reflexivity | exact clint_ne_rev].
      + intros L; rewrite Es; exact (lineContent_upd core initLine specRegions (clintIdx clintS) (clintRegion clintS) (pfClint clintS) (SMEM s2) xs' L I).
      + rewrite Es; exact (FetchViewExt_upd core specRegions (clintIdx clintS) (clintRegion clintS) (pfClint clintS) (SMEM s2) xs' I).
      + unfold MemRelC, MemRel, DevInv.
        rewrite Hreg, Es.
        unfold ms', specClintState, implClintState, specPlicState, implPlicState, specRevState, implRevState in *.
        rewrite !regionStateAt_updRegionStateAt.
        rewrite !regionStateAt_upd_other
          by first [exact clint_ne_plic | exact clint_ne_rev | exact clintS_ne_plicS | exact clintS_ne_rev].
        cbn [Fst].
        refine (conj (conj _ (conj _ (conj Hpl Hrv))) (conj (conj _ Hpi) _)).
        * exact (MemRelPre_upd2 core (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                   (clintIdx clintS) (clintIdx clint) (clintRegion clintS) (clintRegion clint)
                   (pfClint clintS) (pfClint clint) _ _ _ _ HclintIdx clintS_ne_rev
                   (fun x y => or_introl eq_refl) Hpre).
        * exact (ClintRel_tick core xs _ x' Hcl Hsamp).
        * exact (ClintInv_tick core _ x' Hsamp).
        * exact (SnapshotOK_upd core specRegions fwcs (clintIdx clintS) (clintRegion clintS) (pfClint clintS) (SMEM s2) xs' I Hsnap).
      + unfold LatchRel in *; intros e Hin; destruct (Hl e Hin) as [L1 L2]; split.
        * intros Hs; apply L1; revert Hs.
          unfold sClint; rewrite Es; unfold ms', specClintState.
          rewrite regionStateAt_updRegionStateAt; unfold xs'; intros Hs.
          change (andb (clintSampled core xs) (clintMtip core x') = true) in Hs.
          apply andb_prop in Hs as [Hs _]; exact Hs.
        * intros Hp; apply L2; revert Hp.
          unfold sPlic; rewrite Es; unfold ms', specPlicState.
          rewrite regionStateAt_upd_other by exact clintS_ne_plicS.
          intros Hp; exact Hp.
  Qed.


  (* --- 5. PLIC --- *)

  (* Sampling MEIP: impl only, the spec stutters (its meip may lag) *)
  Lemma stepOK_implPlicSampleMeipStep :
    StepOK (@implPlicSampleMeipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions plic type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implPlicSampleMeipStep in Hsem.
    apply SemAction_implDevStep in Hsem as [envR [x' [Hx' E1]]].
    apply plicSample_eq in Hx'.
    assert (Hreg : IREG s1' =
                   updRegionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic) (pfPlic plic)
                     (IREG s1)
                     (x' ,, (regionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic)
                               (pfPlic plic) (IREG s1)).(Snd)))
      by (rewrite E1; reflexivity).
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    exists s2; split; [apply NilAction; reflexivity |].
    exists g.
    eapply RefRelG_regions_frame with (ms' := SMEM s2); [exact E1 | reflexivity | | | | | | | exact Hg].
    - intros P; rewrite Hreg; apply AllPorts_upd; exact I.
    - unfold iRev, implRevState; rewrite Hreg, regionStateAt_upd_other; [reflexivity | exact plic_ne_rev].
    - intros L; reflexivity.
    - apply FetchViewExt_refl.
    - unfold MemRelC, MemRel, DevInv in *.
      destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
      rewrite Hreg.
      unfold implClintState, implPlicState, implRevState in *.
      rewrite regionStateAt_updRegionStateAt.
      rewrite !(regionStateAt_upd_other (implMemRegionTree core) (plicIdx plic))
        by first [exact (not_eq_sym clint_ne_plic) | exact plic_ne_rev].
      cbn [Fst].
      rewrite Hx'.
      refine (conj (conj _ (conj Hcl (conj _ Hrv))) (conj (conj Hci _) Hsnap)).
      + exact (MemRelPre_upd_impl core (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                 (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
                 (pfPlic plicS) (pfPlic plic) _ _ _ HplicIdx plicS_ne_rev
                 (fun x y => or_intror (or_introl eq_refl)) Hpre).
      + exact (PlicRel_sample core _ _ _ _ _ Hpl).
      + exact (PlicInv_sample core _ _ Hpi).
    - exact Hl.
  Qed.

  (* Claim update: lockstep with the spec claim update *)
  Lemma stepOK_implPlicClaimStep :
    StepOK (@implPlicClaimStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions plic type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implPlicClaimStep in Hsem.
    apply SemAction_implDevStep in Hsem as [envR [x' [Hx' E1]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    unfold MemRelC, MemRel, DevInv in Hm.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold specPlicState, implPlicState in Hpl, Hpi.
    set (xs := regionStateAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS)
                 (SMEM s2)) in *.
    destruct (PlicRel_claim core _ _ xs _ x' envR Zmod.zero Hpl Hx') as [xs' [Hs' [Hpl' [Hfall Hpi']]]].
    set (ms' := updRegionStateAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS)
                  (pfPlic plicS) (SMEM s2) xs').
    assert (Es : SMEM (writeSubTreeState NPMS s2 ms') = ms') by reflexivity.
    assert (Hreg : IREG s1' =
                   updRegionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic) (pfPlic plic)
                     (IREG s1)
                     (x' ,, (regionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic)
                               (pfPlic plic) (IREG s1)).(Snd)))
      by (rewrite E1; reflexivity).
    exists (writeSubTreeState NPMS s2 ms'); split.
    - eapply ConsAction;
        [apply (In_specPlicClaimStep_spec core pcAddrInit config specRegions clintS revSpec plicS) | |
         apply NilAction; reflexivity].
      unfold specPlicClaimStep, plicClaimStep, plicAction.
      apply SemAction_specDevStep_intro.
      exact Hs'.
    - exists g.
      eapply RefRelG_regions_frame; [exact E1 | reflexivity | | | | | | | exact Hg].
      + intros P; rewrite Hreg; apply AllPorts_upd; exact I.
      + unfold iRev, implRevState; rewrite Hreg, regionStateAt_upd_other; [reflexivity | exact plic_ne_rev].
      + intros L; rewrite Es; exact (lineContent_upd core initLine specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' L I).
      + rewrite Es; exact (FetchViewExt_upd core specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' I).
      + unfold MemRelC, MemRel, DevInv.
        rewrite Hreg, Es.
        unfold ms', specClintState, implClintState, specPlicState, implPlicState, specRevState, implRevState in *.
        rewrite !regionStateAt_updRegionStateAt.
        rewrite !regionStateAt_upd_other
          by first [exact (not_eq_sym clint_ne_plic) | exact plic_ne_rev
                   | exact (not_eq_sym clintS_ne_plicS) | exact plicS_ne_rev].
        cbn [Fst].
        refine (conj (conj _ (conj Hcl (conj Hpl' Hrv))) (conj (conj Hci Hpi') _)).
        * exact (MemRelPre_upd2 core (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                   (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
                   (pfPlic plicS) (pfPlic plic) _ _ _ _ HplicIdx plicS_ne_rev
                   (fun x y => or_intror (or_introl eq_refl)) Hpre).
        * exact (SnapshotOK_upd core specRegions fwcs (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' I Hsnap).
      + unfold LatchRel in *; intros e Hin; destruct (Hl e Hin) as [L1 L2]; split.
        * intros Hs; apply L1; revert Hs.
          unfold sClint; rewrite Es; unfold ms', specClintState.
          rewrite regionStateAt_upd_other by exact (not_eq_sym clintS_ne_plicS).
          intros Hs; exact Hs.
        * intros Hp; apply L2; revert Hp.
          unfold sPlic; rewrite Es; unfold ms', specPlicState.
          rewrite regionStateAt_updRegionStateAt.
          intros Hp; exact (Hfall Hp).
  Qed.


  (* --- 6. PLIC Pending Updates --- *)

  Local Abbreviation nI := (S (S (length (collectIrqActions core implRegions)))).
  Local Abbreviation nS := (S (S (length (collectIrqActions core specRegions)))).
  Local Abbreviation RELG :=
    (RefRelG core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).

  Lemma length_irq_eq :
    length (implCollectIrqActions core implRegions) = length (collectIrqActions core specRegions).
  Proof. rewrite length_implCollect; apply length_collect_rev. Qed.

  Lemma nS_nI : nS = nI.
  Proof.
    assert (E : length (collectIrqActions core specRegions) = length (collectIrqActions core implRegions))
      by (symmetry; apply length_collect_rev).
    rewrite E; reflexivity.
  Qed.

  Lemma writeNPMI_twice : forall (s : TS ITree) a b, writeSubTreeState NPMI (writeSubTreeState NPMI s a) b = writeSubTreeState NPMI s b.
  Proof. intros; reflexivity. Qed.

  Lemma writeNPMS_twice : forall (s : TS STree) a b, writeSubTreeState NPMS (writeSubTreeState NPMS s a) b = writeSubTreeState NPMS s b.
  Proof. intros; reflexivity. Qed.

  (* A device action of the impl memory (without the system lift) *)
  Lemma SemAction_implMemDev :
    forall env idx r0 (pf : nth_error implRegions idx = Some r0) {k} (act : Action type (memRegionTree core r0) k)
           (m m' : TS (implMemTree core implRegions)) v,
      SemAction env (@implNthRegionAction core type idx implRegions r0 pf k act) m m' v ->
      exists envR x',
        SemAction envR act (regionStateAt (implMemRegionTree core) idx implRegions r0 pf m.(Fst)).(Fst) x' v /\
        m' = (updRegionStateAt (implMemRegionTree core) idx implRegions r0 pf m.(Fst)
                (x' ,, (regionStateAt (implMemRegionTree core) idx implRegions r0 pf m.(Fst)).(Snd)) ,, m.(Snd)).
  Proof.
    intros env idx r0 pf k act m m' v Hm'.
    unfold implNthRegionAction in Hm'.
    apply SemAction_liftAction_iff in Hm' as [rg' [Hrg' ->]].
    unfold implRegionsNthRegionAction in Hrg'.
    apply SemAction_genNthRegionAction_iff in Hrg' as [y' [Hy' ->]].
    unfold liftToImplRegion in Hy'.
    apply SemAction_liftAction_iff in Hy' as [x' [Hx' ->]].
    do 2 eexists; split; [exact Hx' | reflexivity].
  Qed.

  Lemma SemAction_specMemDev_intro :
    forall env idx r0 (pf : nth_error specRegions idx = Some r0) {k} (act : Action type (memRegionTree core r0) k)
           (ms : TS (specMemTree core specRegions)) x' v,
      SemAction (envRegionAt (memRegionTree core) idx specRegions r0 pf env ms) act
        (regionStateAt (memRegionTree core) idx specRegions r0 pf ms) x' v ->
      SemAction env (@nthRegionAction core type idx specRegions r0 pf k act) ms
        (updRegionStateAt (memRegionTree core) idx specRegions r0 pf ms x') v.
  Proof.
    intros env idx r0 pf k act ms x' v H.
    unfold nthRegionAction; apply SemAction_genNthRegionAction_iff; exists x'; split; [exact H | reflexivity].
  Qed.

  (* The spec env at the memory accepts what the region envs accept *)
  Lemma envS_covers : forall s2 : TS STree, EnvCovers core initLine specRegions fwcs (subEnv NPMS envS s2).
  Proof.
    intros s2 s x v Hall; unfold subEnv.
    unfold specEnv, envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionsEnv].
    apply Hall.
  Qed.

  (* Phase 1, the interrupt source of a region: the spec reads the same value *)
  Lemma irqStep_region :
    forall g s1 s2 k gI rgMid vIrq envX,
      RELG g s1 s2 ->
      nth_error (implCollectIrqActions core implRegions) k = Some gI ->
      SemAction envX (gI type) (IREG s1) rgMid vIrq ->
      exists gS msMid,
        nth_error (collectIrqActions core specRegions) k = Some gS /\
        SemAction (subEnv NPMS envS s2) (gS type) (SMEM s2) msMid vIrq /\
        RELG g (writeSubTreeState NPMI s1 (rgMid ,, (IMEM s1).(Snd))) (writeSubTreeState NPMS s2 msMid).
  Proof.
    intros g s1 s2 k gI rgMid vIrq envX Hg HgI Hsem.
    assert (Hlt : (k < length (collectIrqActions core specRegions))%nat).
    { rewrite <- length_irq_eq; apply nth_error_Some; rewrite HgI; discriminate. }
    destruct (nth_error (collectIrqActions core specRegions) k) as [gS |] eqn:HgS;
      [| apply nth_error_None in HgS; lia].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    unfold MemRelC, MemRel, DevInv in Hm.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    assert (Hno : forall j r, nth_error specRegions j = Some r -> (0 + j = clintIdx clintS \/ 0 + j = plicIdx plicS)%nat ->
                              memRegionIrqActions core r = []).
    { intros j r Hr [Hj | Hj]; cbn [Nat.add] in Hj; subst j.
      - rewrite (pfClint clintS) in Hr; injection Hr as Hr; subst r; reflexivity.
      - rewrite (pfPlic plicS) in Hr; injection Hr as Hr; subst r; reflexivity. }
    assert (HenvC : EnvCustomTrue core specRegions (subEnv NPMS envS s2))
      by exact (EnvCovers_custom core initLine specRegions fwcs _ (envS_covers s2)).
    destruct (irqPre_rel core (clintIdx clintS) (plicIdx plicS) post revBase revPfB revPfA pre 0 (SMEM s2) (IREG s1) rgMid
                k gS gI envX (subEnv NPMS envS s2) vIrq _ HgS HgI Hpre Hrv Hno HenvC Hsem) as [msMid [HsS HpreMid]].
    exists gS, msMid; split; [first [reflexivity | exact HgS] | split; [exact HsS |]].
    destruct (irqSpec_frame core specRegions k gS _ (SMEM s2) msMid vIrq HgS HsS) as [HcoS HsameS].
    destruct (irqImpl_frame core implRegions k gI envX (IREG s1) rgMid vIrq HgI Hsem) as [HcoI HsameI].
    assert (HroS : forall j, (j = clintIdx clintS \/ j = plicIdx plicS \/ j = length pre)%nat ->
                             forall r0, nth_error specRegions j = Some r0 -> IrqROS core r0).
    { intros j Hj r0 Hr0; destruct Hj as [-> | [-> | ->]].
      - rewrite (pfClint clintS) in Hr0; injection Hr0 as Hr0; subst r0; apply IrqROS_noirq; reflexivity.
      - rewrite (pfPlic plicS) in Hr0; injection Hr0 as Hr0; subst r0; apply IrqROS_noirq; reflexivity.
      - rewrite nth_spec_rev in Hr0; injection Hr0 as Hr0; subst r0; apply IrqROS_rev. }
    assert (HroI : forall j, (j = clintIdx clint \/ j = plicIdx plic \/ j = length pre)%nat ->
                             forall r0, nth_error implRegions j = Some r0 -> IrqROS core r0).
    { intros j Hj r0 Hr0; destruct Hj as [-> | [-> | ->]].
      - rewrite (pfClint clint) in Hr0; injection Hr0 as Hr0; subst r0; apply IrqROS_noirq; reflexivity.
      - rewrite (pfPlic plic) in Hr0; injection Hr0 as Hr0; subst r0; apply IrqROS_noirq; reflexivity.
      - rewrite nth_impl_rev in Hr0; injection Hr0 as Hr0; subst r0; apply IrqROS_rev. }
    pose proof (HsameS _ (HroS _ (or_introl eq_refl)) (clintRegion clintS) (pfClint clintS)) as EclS.
    pose proof (HsameS _ (HroS _ (or_intror (or_introl eq_refl))) (plicRegion plicS) (pfPlic plicS)) as EplS.
    pose proof (HsameS _ (HroS _ (or_intror (or_intror eq_refl))) sRevR (nth_error_app_cons_len pre sRevR post)) as ErvS.
    pose proof (HsameI _ (HroI _ (or_introl eq_refl)) (clintRegion clint) (pfClint clint)) as EclI.
    pose proof (HsameI _ (HroI _ (or_intror (or_introl eq_refl))) (plicRegion plic) (pfPlic plic)) as EplI.
    pose proof (HsameI _ (HroI _ (or_intror (or_intror eq_refl))) iRevR (nth_error_app_cons_len pre iRevR post)) as ErvI.
    assert (EsM : SMEM (writeSubTreeState NPMS s2 msMid) = msMid) by reflexivity.
    assert (EiM : IREG (writeSubTreeState NPMI s1 (rgMid ,, (IMEM s1).(Snd))) = rgMid) by reflexivity.
    eapply RefRelG_regions_frame with (mi' := rgMid) (ms' := msMid); [reflexivity | reflexivity | | | | | | | exact Hg].
    - intros P; rewrite EiM; apply AllPorts_customOnly; exact HcoI.
    - unfold iRev, implRevState; rewrite EiM, ErvI; reflexivity.
    - intros L; rewrite EsM; apply lineContent_customOnly; exact HcoS.
    - rewrite EsM; apply FetchViewExt_customOnly; exact HcoS.
    - unfold MemRelC, MemRel, DevInv; rewrite EsM, EiM.
      unfold specClintState, implClintState, specPlicState, implPlicState, specRevState, implRevState in *.
      rewrite EclS, EplS, ErvS, EclI, EplI, ErvI.
      refine (conj (conj HpreMid (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) _)).
      exact (SnapshotOK_customOnly core specRegions fwcs _ _ HcoS Hsnap).
    - unfold LatchRel in *; intros e Hin; destruct (Hl e Hin) as [L1 L2]; split.
      + intros Hs; apply L1; revert Hs; unfold sClint, specClintState; rewrite EsM, EclS; exact (fun H => H).
      + intros Hp; apply L2; revert Hp; unfold sPlic, specPlicState; rewrite EsM, EplS; exact (fun H => H).
  Qed.

  (* Phase 1, the UART line: both PLICs record the same value *)
  Lemma irqStep_uart :
    forall g s1 s2 mMid vIrq envX,
      RELG g s1 s2 ->
      SemAction envX (Impl.implPlicUartIrqAction plic type) (IMEM s1) mMid vIrq ->
      exists msMid,
        SemAction (subEnv NPMS envS s2) (plicUartIrqAction plicS type) (SMEM s2) msMid vIrq /\
        RELG g (writeSubTreeState NPMI s1 mMid) (writeSubTreeState NPMS s2 msMid).
  Proof.
    intros g s1 s2 mMid vIrq envX Hg Hsem.
    unfold Impl.implPlicUartIrqAction, Impl.implPlicAction in Hsem.
    apply SemAction_implMemDev in Hsem as [envR [x' [Hx' Em]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    unfold MemRelC, MemRel, DevInv in Hm.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold specPlicState, implPlicState in Hpl, Hpi.
    set (xs := regionStateAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS)
                 (SMEM s2)) in *.
    assert (Henv : forall s x w,
               envRegionAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS)
                 (subEnv NPMS envS s2) (SMEM s2) s x w).
    { apply envRegionAt_customTrue; [exact (EnvCovers_custom core initLine specRegions fwcs _ (envS_covers s2)) | exact I]. }
    destruct (PlicRel_uart core _ _ xs _ x' envR _ vIrq Hpl Hx' Henv) as [xs' [Hs' [Hpl' [Hms [Hmi Hci']]]]].
    set (ms' := updRegionStateAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS)
                  (pfPlic plicS) (SMEM s2) xs').
    assert (Es : SMEM (writeSubTreeState NPMS s2 ms') = ms') by reflexivity.
    assert (Hreg : IREG (writeSubTreeState NPMI s1 mMid) =
                   updRegionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic) (pfPlic plic)
                     (IREG s1)
                     (x' ,, (regionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic)
                               (pfPlic plic) (IREG s1)).(Snd)))
      by (rewrite Em; reflexivity).
    exists ms'; split.
    - unfold plicUartIrqAction, plicAction; apply SemAction_specMemDev_intro; exact Hs'.
    - eapply RefRelG_regions_frame; [rewrite Em; reflexivity | reflexivity | | | | | | | exact Hg].
      + intros P; rewrite Hreg; apply AllPorts_upd; exact I.
      + unfold iRev, implRevState; rewrite Hreg, regionStateAt_upd_other; [reflexivity | exact plic_ne_rev].
      + intros L; rewrite Es; exact (lineContent_upd core initLine specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' L I).
      + rewrite Es; exact (FetchViewExt_upd core specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' I).
      + unfold MemRelC, MemRel, DevInv.
        rewrite Hreg, Es.
        unfold ms', specClintState, implClintState, specPlicState, implPlicState, specRevState, implRevState in *.
        rewrite !regionStateAt_updRegionStateAt.
        rewrite !regionStateAt_upd_other
          by first [exact (not_eq_sym clint_ne_plic) | exact plic_ne_rev
                   | exact (not_eq_sym clintS_ne_plicS) | exact plicS_ne_rev].
        cbn [Fst].
        refine (conj (conj _ (conj Hcl (conj Hpl' Hrv))) (conj (conj Hci _) _)).
        * exact (MemRelPre_upd2 core (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                   (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
                   (pfPlic plicS) (pfPlic plic) _ _ _ _ HplicIdx plicS_ne_rev
                   (fun x y => or_intror (or_introl eq_refl)) Hpre).
        * unfold PlicInv in *; rewrite Hmi, Hci'; exact Hpi.
        * exact (SnapshotOK_upd core specRegions fwcs (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' I Hsnap).
      + unfold LatchRel in *; intros e Hin; destruct (Hl e Hin) as [L1 L2]; split.
        * intros Hs; apply L1; revert Hs.
          unfold sClint; rewrite Es; unfold ms', specClintState.
          rewrite regionStateAt_upd_other by exact (not_eq_sym clintS_ne_plicS).
          intros Hs; exact Hs.
        * intros Hp; apply L2; revert Hp.
          unfold sPlic; rewrite Es; unfold ms', specPlicState.
          rewrite regionStateAt_updRegionStateAt, Hms.
          intros Hp; exact Hp.
  Qed.

  (* Phase 2, the pending bit of source `j`: lockstep *)
  Lemma leafStep :
    forall g s1 s2 m' j pI iI pS iS irq envX,
      RELG g s1 s2 ->
      nth_error (pendingPathsWithKind core nS) j = Some pS -> nth_error (inServicePathsWithKind core nS) j = Some iS ->
      nth_error (pendingPathsWithKind core nI) j = Some pI -> nth_error (inServicePathsWithKind core nI) j = Some iI ->
      SemAction envX (Impl.implPlicAction plic (@updatePendingLeaf core nI type pI iI irq)) (IMEM s1) m' Zmod.zero ->
      exists ms',
        (forall envY, SemAction envY (plicAction plicS (@updatePendingLeaf core nS type pS iS irq)) (SMEM s2) ms' Zmod.zero) /\
        RELG g (writeSubTreeState NPMI s1 m') (writeSubTreeState NPMS s2 ms').
  Proof.
    intros g s1 s2 m' j pI iI pS iS irq envX Hg HpS HiS HpI HiI Hsem.
    unfold Impl.implPlicAction in Hsem.
    apply SemAction_implMemDev in Hsem as [envR [x' [Hx' Em]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ _].
    unfold MemRelC, MemRel, DevInv in Hm.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold specPlicState, implPlicState in Hpl, Hpi.
    set (xs := regionStateAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS)
                 (SMEM s2)) in *.
    destruct (PlicRel_leaf core _ _ xs _ x' j pS iS pI iI irq envR Zmod.zero Hpl HpS HiS HpI HiI Hx')
      as [xs' [Hs' [Hpl' [Hms [Hmi Hci']]]]].
    set (ms' := updRegionStateAt (memRegionTree core) (plicIdx plicS) specRegions (plicRegion plicS)
                  (pfPlic plicS) (SMEM s2) xs').
    assert (Es : SMEM (writeSubTreeState NPMS s2 ms') = ms') by reflexivity.
    assert (Hreg : IREG (writeSubTreeState NPMI s1 m') =
                   updRegionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic) (pfPlic plic)
                     (IREG s1)
                     (x' ,, (regionStateAt (implMemRegionTree core) (plicIdx plic) implRegions (plicRegion plic)
                               (pfPlic plic) (IREG s1)).(Snd)))
      by (rewrite Em; reflexivity).
    exists ms'; split.
    - intros envY; unfold plicAction; apply SemAction_specMemDev_intro; apply Hs'.
    - eapply RefRelG_regions_frame; [rewrite Em; reflexivity | reflexivity | | | | | | | exact Hg].
      + intros P; rewrite Hreg; apply AllPorts_upd; exact I.
      + unfold iRev, implRevState; rewrite Hreg, regionStateAt_upd_other; [reflexivity | exact plic_ne_rev].
      + intros L; rewrite Es; exact (lineContent_upd core initLine specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' L I).
      + rewrite Es; exact (FetchViewExt_upd core specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' I).
      + unfold MemRelC, MemRel, DevInv.
        rewrite Hreg, Es.
        unfold ms', specClintState, implClintState, specPlicState, implPlicState, specRevState, implRevState in *.
        rewrite !regionStateAt_updRegionStateAt.
        rewrite !regionStateAt_upd_other
          by first [exact (not_eq_sym clint_ne_plic) | exact plic_ne_rev
                   | exact (not_eq_sym clintS_ne_plicS) | exact plicS_ne_rev].
        cbn [Fst].
        refine (conj (conj _ (conj Hcl (conj Hpl' Hrv))) (conj (conj Hci _) _)).
        * exact (MemRelPre_upd2 core (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
                   (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
                   (pfPlic plicS) (pfPlic plic) _ _ _ _ HplicIdx plicS_ne_rev
                   (fun x y => or_intror (or_introl eq_refl)) Hpre).
        * unfold PlicInv in *; rewrite Hmi, Hci'; exact Hpi.
        * exact (SnapshotOK_upd core specRegions fwcs (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) (SMEM s2) xs' I Hsnap).
      + unfold LatchRel in *; intros e Hin; destruct (Hl e Hin) as [L1 L2]; split.
        * intros Hs; apply L1; revert Hs.
          unfold sClint; rewrite Es; unfold ms', specClintState.
          rewrite regionStateAt_upd_other by exact (not_eq_sym clintS_ne_plicS).
          intros Hs; exact Hs.
        * intros Hp; apply L2; revert Hp.
          unfold sPlic; rewrite Es; unfold ms', specPlicState.
          rewrite regionStateAt_updRegionStateAt, Hms.
          intros Hp; exact Hp.
  Qed.

  (* The k-th pending step of the impl and of the spec *)
  Lemma In_implHelper :
    forall (acts : list (Action type (implMemTree core implRegions) Bool)) pends insvs act,
      In act (Impl.implPlicPendingStepsHelper plic acts pends insvs) ->
      exists k a p i,
        nth_error acts k = Some a /\ nth_error pends k = Some p /\ nth_error insvs k = Some i /\
        act = (LetA irqVal : Bool <- a ; Impl.implPlicAction plic (@updatePendingLeaf core nI type p i irqVal)).
  Proof.
    induction acts as [| a acts IH]; intros [| p pends] [| i insvs] act Hin;
      cbn [Impl.implPlicPendingStepsHelper In] in Hin; try contradiction.
    destruct Hin as [<- | Hin].
    - exists 0%nat, a, p, i; repeat split; reflexivity.
    - destruct (IH pends insvs act Hin) as [k [a' [p' [i' [H1 [H2 [H3 ->]]]]]]].
      exists (S k), a', p', i'; repeat split; assumption.
  Qed.

  Lemma In_specHelper :
    forall (acts : list (Action type (specMemTree core specRegions) Bool)) pends insvs k a p i,
      nth_error acts k = Some a -> nth_error pends k = Some p -> nth_error insvs k = Some i ->
      In (LetA irqVal : Bool <- a ; plicAction plicS (@updatePendingLeaf core nS type p i irqVal))
         (plicPendingStepsHelper plicS acts pends insvs).
  Proof.
    induction acts as [| a0 acts IH]; intros [| p0 pends] [| i0 insvs] k a p i Ha Hp Hi;
      try (destruct k; discriminate).
    destruct k as [| k]; cbn [plicPendingStepsHelper In].
    - cbn in Ha, Hp, Hi; injection Ha as <-; injection Hp as <-; injection Hi as <-; left; reflexivity.
    - right; exact (IH pends insvs k a p i Ha Hp Hi).
  Qed.

  Theorem stepOK_implPlicPendingsSteps :
    forall act,
      In act (@implPlicPendingsSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions plic type) ->
      StepOK act.
  Proof.
    intros act Hin s1 s1' s2 Hsem [g Hg].
    unfold implPlicPendingsSteps in Hin; cbv zeta in Hin.
    apply in_map_iff in Hin as [memAct [<- HinMem]]; cbv beta in Hsem.
    revert HinMem.
    destruct (pendingPathsWithKind core nI) as [| p0I dPI] eqn:EpI; [intros [] |].
    destruct (inServicePathsWithKind core nI) as [| i0I dII] eqn:EiI; [intros [] |].
    intros HinMem; cbv beta iota in HinMem.
    apply In_implHelper in HinMem as [k [aI [pI [iI [HaI [HpI [HiI ->]]]]]]].
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite SemAction_iff_evalActionPropGen in Hm'; cbn [evalActionPropGen] in Hm'.
    destruct (evalActionPropGen_to_SemAction aI _ _ Hm') as [mMid [vIrq [HaSem Hleaf]]].
    cbv beta in Hleaf.
    first [rewrite <- SemAction_iff_evalActionPropGen in Hleaf | apply SemAction_iff_evalActionPropGen in Hleaf].
    assert (HpI' : nth_error (pendingPathsWithKind core nI) (S k) = Some pI) by (rewrite EpI; exact HpI).
    assert (HiI' : nth_error (inServicePathsWithKind core nI) (S k) = Some iI) by (rewrite EiI; exact HiI).
    destruct (nth_pend_transport core nS nI nS_nI (S k) pI HpI') as [pS HpS].
    destruct (nth_insv_transport core nS nI nS_nI (S k) iI HiI') as [iS HiS].
    assert (EL : length (map (fun f => f type) (collectIrqActions core specRegions)) =
                 length (implMemCollectIrqActions core implRegions type)).
    { unfold implMemCollectIrqActions; rewrite !length_map; symmetry; exact length_irq_eq. }
    assert (Hph1 : exists aS msMid,
               nth_error (map (fun f => f type) (collectIrqActions core specRegions) ++ [plicUartIrqAction plicS type]) k
                 = Some aS /\
               SemAction (subEnv NPMS envS s2) aS (SMEM s2) msMid vIrq /\
               RELG g (writeSubTreeState NPMI s1 mMid) (writeSubTreeState NPMS s2 msMid)).
    { destruct (nth_error_snoc_inv _ _ _ _ HaI) as [HaI' | [Ek HaU]].
      - unfold implMemCollectIrqActions in HaI'; rewrite nth_error_map in HaI'.
        apply option_map_Some_inv in HaI' as [gI [HgI HaI']]; subst aI; cbv beta in HaSem.
        apply SemAction_liftAction_iff in HaSem as [rgMid [HrgMid EMid]].
        destruct (irqStep_region g s1 s2 k gI rgMid vIrq _ Hg HgI HrgMid) as [gS [msMid [HgS [HsS HgMid]]]].
        exists (gS type), msMid; split; [exact (nth_error_app_map_l (fun f => f type) _ _ k gS HgS) |].
        split; [exact HsS |].
        rewrite EMid; exact HgMid.
      - subst aI.
        destruct (irqStep_uart g s1 s2 mMid vIrq _ Hg HaSem) as [msMid [HsS HgMid]].
        exists (plicUartIrqAction plicS type), msMid; split; [| split; [exact HsS | exact HgMid]].
        apply nth_error_app_last; rewrite Ek; symmetry; exact EL. }
    destruct Hph1 as [aS [msMid [HaS [HsS HgMid]]]].
    destruct (leafStep g _ _ m' (S k) pI iI pS iS vIrq _ HgMid HpS HiS HpI' HiI' Hleaf) as [ms' [Hs' Hg']].
    assert (HinS : In (liftAction NPMS (LetA irqVal : Bool <- aS ;
                                        plicAction plicS (@updatePendingLeaf core nS type pS iS irqVal))) specActs).
    { first [rewrite map_snd_specMod
            | refine (eq_ind_r (fun L => In _ L) _ (map_snd_specMod core pcAddrInit config specRegions clintS revSpec plicS))].
      apply in_or_app; right; apply in_or_app; left.
      unfold specPlicPendingsSteps, plicPendingsSteps; cbv zeta.
      apply in_map_iff; eexists; split; [reflexivity |].
      revert HpS HiS.
      destruct (pendingPathsWithKind core nS) as [| p0S dPS] eqn:EpS; [intros H; discriminate H |].
      destruct (inServicePathsWithKind core nS) as [| i0S dIS] eqn:EiS; [intros _ H; discriminate H |].
      intros HpS0 HiS0.
      exact (In_specHelper _ dPS dIS k aS pS iS HaS HpS0 HiS0). }
    exists (writeSubTreeState NPMS s2 ms'); split.
    - eapply ConsAction; [exact HinS | | apply NilAction; reflexivity].
      apply SemAction_liftAction_iff; exists ms'; split; [| reflexivity].
      eapply SemLetAction; [exact HsS | exact (Hs' _)].
    - exists g; rewrite writeNPMI_twice, writeNPMS_twice in Hg'; rewrite E1; exact Hg'.
  Qed.

  (* --- 7. mcycle Tick --- *)

  Local Abbreviation SRF := (sRf core pcAddrInit pre post revBase revPfB revPfA).

  Lemma stepOK_implTickCycle :
    StepOK (@implTickCycle core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold implTickCycle in Hsem.
    apply SemAction_liftAction_iff in Hsem as [rf' [Hrf' E1]].
    apply SemAction_incrementMcycle_iff in Hrf' as [Erf _]; subst rf'.
    destruct (g_chain core pcAddrInit g) eqn:Hch.
    - exists (writeSubTreeState (Spec.np_rf core pcAddrInit specRegions) s2
                (evalIncrementMcycle core pcAddrInit (SRF s2))).
      split.
      + eapply ConsAction;
          [apply (In_specTickCycle_spec core pcAddrInit config specRegions clintS revSpec plicS) | |
           apply NilAction; reflexivity].
        unfold specTickCycle; apply SemAction_liftAction_iff; eexists; split; [| reflexivity].
        apply SemAction_incrementMcycle_iff; split; reflexivity.
      + eexists; eapply RefRelG_tick_lockstep; [exact E1 | reflexivity | exact Hch | exact Hg].
    - exists s2; split; [apply NilAction; reflexivity |].
      eexists; eapply RefRelG_tick_ghost; [exact E1 | rewrite Hch; discriminate | exact Hg].
  Qed.

  (* --- 8. All Peripheral Steps --- *)

  Theorem stepOK_implPeripheralSteps :
    forall act,
      In act (@implPeripheralSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions clint plic type) ->
      StepOK act.
  Proof.
    intros act Hin.
    unfold implPeripheralSteps, implPlicSteps, implTimerSteps in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    - apply in_app_or in Hin as [Hin | Hin].
      + exact (stepOK_implPlicPendingsSteps act Hin).
      + cbn [In] in Hin; destruct Hin as [<- | [<- | []]].
        * exact stepOK_implPlicClaimStep.
        * exact stepOK_implPlicSampleMeipStep.
    - cbn [In] in Hin; destruct Hin as [<- | [<- | [<- | []]]].
      + exact stepOK_implTickCycle.
      + exact stepOK_implTickTimer.
      + exact stepOK_implSampleMtipStep.
  Qed.

  (* --- 9. fence.i Acks --- *)

  Lemma length_fence_eq :
    length (implCollectFenceIAckActions core implRegions) = length (collectFenceIAckActions core specRegions).
  Proof. rewrite length_implFenceCollect; apply length_fenceCollect_rev. Qed.

  Lemma In_specFenceIAck :
    forall a, In a (@specFenceIAckSteps core pcAddrInit specRegions type) -> In a specActs.
  Proof.
    intros a Ha; rewrite (map_snd_specMod core pcAddrInit config specRegions clintS revSpec plicS).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Ha.
  Qed.

  (* The real envs: the spec memory env is exactly the regions env, and so is the impl's *)
  Lemma specEnvOK_mem : forall s2 : TS STree, SpecEnvOK core initLine specRegions fwcs (subEnv NPMS envS s2).
  Proof.
    intros s2 s lp pf' v Hall.
    unfold subEnv, cast_recv_inv.
    match goal with |- context [eq_rect _ _ v _ ?e] => rewrite (Kind_uip_refl _ e) end.
    cbn [eq_rect].
    unfold specEnv, envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionsEnv].
    apply Hall.
  Qed.

  Lemma implEnvOK_regions :
    forall (s1 : TS ITree) (m : TS (implMemTree core implRegions)),
      ImplEnvOK core initLine implRegions fwcs (subEnv child0Path (subEnv NPMI envI s1) m).
  Proof.
    intros s1 m s lp pf v H pf'.
    unfold subEnv, cast_recv_inv in H.
    match type of H with context [eq_rect _ _ (eq_rect _ _ v _ ?e1) _ ?e2] =>
      rewrite (Kind_uip_refl _ e1), (Kind_uip_refl _ e2) in H end.
    cbn [eq_rect] in H.
    unfold implEnv, implMemEnv, envNodeCons, envCtxCons, envCtxMap in H; cbn -[implRegionsEnv] in H.
    match type of H with context [@Build_RecvPath _ lp ?q] => rewrite (Is_true_pi _ q pf') in H end.
    exact H.
  Qed.

  Lemma envAckPre_real :
    forall (s1 : TS ITree) (s2 : TS STree),
      EnvAckPre core post revBase revPfB revPfA fwcs pre
        (subEnv NPMS envS s2) (subEnv child0Path (subEnv NPMI envI s1) (IMEM s1)).
  Proof.
    intros s1 s2; apply (EnvAckPre_real core initLine); [apply specEnvOK_mem | apply implEnvOK_regions].
  Qed.

  (* The device states sit at CustomMem positions, which an ack step leaves alone *)
  Lemma specDev_ackFrame :
    forall ms ms', AckFrameS core specRegions ms ms' ->
      specClintState core pre post revBase revPfB revPfA clintS ms' =
        specClintState core pre post revBase revPfB revPfA clintS ms /\
      specPlicState core pre post revBase revPfB revPfA plicS ms' =
        specPlicState core pre post revBase revPfB revPfA plicS ms /\
      specRevState core pre post revBase revPfB revPfA ms' = specRevState core pre post revBase revPfB revPfA ms.
  Proof.
    intros ms ms' H; unfold specClintState, specPlicState, specRevState.
    split; [| split]; (rewrite (regionStateAtS_ackFrame core _ _ _ _ _ _ H); [reflexivity | exact I]).
  Qed.

  Lemma implDev_ackFrame :
    forall mi mi', AckFrameI core implRegions mi mi' ->
      implClintState core pre post revBase revPfB revPfA clint mi' =
        implClintState core pre post revBase revPfB revPfA clint mi /\
      implPlicState core pre post revBase revPfB revPfA plic mi' =
        implPlicState core pre post revBase revPfB revPfA plic mi /\
      implRevState core pre post revBase revPfB revPfA mi' = implRevState core pre post revBase revPfB revPfA mi.
  Proof.
    intros mi mi' H; unfold implClintState, implPlicState, implRevState.
    split; [| split]; (rewrite (regionStateAtI_ackFrame core _ _ _ _ _ _ H); [reflexivity | exact I]).
  Qed.

  (* An impl ack step: a stutter if it changed nothing, else the spec takes the same ack step
   * (some fenceIWait is set, so the wait frame applies) *)
  Theorem stepOK_fenceIAcks :
    forall act,
      In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type) ->
      StepOK act.
  Proof.
    intros act Hin s1 s1' s2 Hsem [g Hg].
    unfold fenceIAcks, implMemCollectFenceIAckActions in Hin.
    rewrite map_map in Hin.
    apply In_nth_error in Hin as [k Hk].
    rewrite nth_error_map in Hk.
    apply option_map_Some_inv in Hk as [aI [HkI ->]]; cbv beta in Hsem.
    assert (Hlt : (k < length (collectFenceIAckActions core specRegions))%nat).
    { rewrite <- length_fence_eq.
      match type of HkI with @nth_error ?A ?L k = Some _ =>
        exact (proj1 (@nth_error_Some A L k) ltac:(rewrite HkI; discriminate)) end. }
    destruct (nth_error (collectFenceIAckActions core specRegions) k) as [aS |] eqn:HkS;
      [| apply nth_error_Some in Hlt; contradiction].
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    apply SemAction_liftAction_iff in Hm' as [mi' [Hmi' Em]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ Hw _].
    unfold MemRelC, MemRel, DevInv in Hm.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    destruct (fencePre_rel core _ _ post revBase revPfB revPfA pre 0%nat fwcs _ _ mi' k aS aI _ _ _
                HkS HkI Hpre (envAckPre_real s1 s2) Hmi')
      as [ms' [Hs' [Hpre' [Hd [HfS [HfI [Hsn Hfc]]]]]]].
    destruct Hd as [[Ems Emi] | Hwait].
    - exists s2; split; [apply NilAction; reflexivity |].
      exists g.
      assert (Es1 : s1' = s1).
      { rewrite E1, Em, Emi.
        first [reflexivity
              | change (IREG s1) with (readSubTreeState child0Path (readSubTreeState NPMI s1));
                rewrite !writeSubTreeState_readSubTreeState; reflexivity]. }
      rewrite Es1; exact Hg.
    - assert (HIn : In (liftAction NPMS (aS type)) specActs).
      { apply In_specFenceIAck; unfold specFenceIAckSteps; apply in_map_iff.
        exists aS; split; [reflexivity | eapply nth_error_In; exact HkS]. }
      exists (writeSubTreeState NPMS s2 ms'); split.
      + eapply ConsAction; [exact HIn | | apply NilAction; reflexivity].
        apply SemAction_liftAction_iff; exists ms'; split; [exact Hs' | reflexivity].
      + exists g.
        assert (Ei1 : IREG s1' = mi') by (rewrite E1, Em; reflexivity).
        assert (Es2 : SMEM (writeSubTreeState NPMS s2 ms') = ms') by reflexivity.
        destruct (specDev_ackFrame _ _ HfS) as [Sc [Sp Sr]].
        destruct (implDev_ackFrame _ _ HfI) as [Ic [Ip Ir]].
        eapply RefRelG_wait_frame with (mi' := mi') (ms' := ms').
        * rewrite E1, Em; reflexivity.
        * reflexivity.
        * exact Hwait.
        * intros P HP; rewrite Ei1; exact (AllPorts_ackFrame core P HP _ _ _ HfI).
        * unfold iRev; rewrite Ei1; exact Ir.
        * intros L; rewrite Es2; exact (lineContent_ackFrame core initLine _ _ _ HfS L).
        * rewrite Ei1; apply Hfc.
          unfold WfRel in Hw; destruct Hw as [_ [_ [_ [_ W5]]]].
          revert W5; apply AllPorts_impl; intros r y [_ Hy]; exact Hy.
        * unfold MemRelC, MemRel, DevInv; rewrite Ei1, Es2.
          rewrite Sc, Sp, Sr, Ic, Ip, Ir.
          exact (conj (conj Hpre' (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) (Hsn Hsnap))).
        * unfold LatchRel in *; intros e Hin'; destruct (Hl e Hin') as [L1 L2].
          unfold sClint, sPlic; rewrite Es2, Sc, Sp; exact (conj L1 L2).
        * exact Hg.
  Qed.
End Periph.
