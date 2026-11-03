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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefFetch RefMemRel RefCoreRel
  RefFrame RefPeriph RefSpecRead RefSpecFetch RefReplay.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE fence.i REQUEST TO THE REGIONS
 * ===========================================================================
 * The spec's deferred fence.i (`specMemSendFenceIRq`) and the impl's dataMem stage
 * (`implRegionsSendFenceIRq`) run the same action on every region: an ExternalMem region sets
 * its fetch subtree's fenceIWait and records the request; a CustomMem region does nothing.
 * `sendAllS`/`sendAllI` are the closed forms; the relations survive them. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Closed Forms --- *)

Definition sendExt (r : MemRegion) (x : TS (externalMemRegionTree r)) : TS (externalMemRegionTree r) :=
  ((x.(Fst).(Fst) ,, (x.(Fst).(Snd).(Fst) ,, (true ,,
     ((evalExpr ($0 : Expr type (Bit 0)) :: x.(Fst).(Snd).(Snd).(Snd).(Fst)) ,,
      x.(Fst).(Snd).(Snd).(Snd).(Snd))))) ,, x.(Snd)).

Definition sendRegion (r : MemRegion) : TS (memRegionTree r) -> TS (memRegionTree r) :=
  match r.(regionKind) as k return TS (memRegionKindTree r k) -> TS (memRegionKindTree r k) with
  | ExternalMem => fun x => sendExt r x
  | CustomMem _ _ _ _ => fun x => x
  end.

Definition sendRegionI (r : MemRegion) : TS (implMemRegionTree r) -> TS (implMemRegionTree r) :=
  match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) with
  | ExternalMem => fun y => (sendExt r y.(Fst) ,, y.(Snd))
  | CustomMem _ _ _ _ => fun y => y
  end.

Fixpoint sendAllS (l : list MemRegion) : TS (specMemTree l) -> TS (specMemTree l) :=
  match l as l0 return TS (specMemTree l0) -> TS (specMemTree l0) with
  | [] => fun m => m
  | r :: rs => fun m => (sendRegion r m.(Fst) ,, (sendAllS rs m.(Snd).(Fst) ,, m.(Snd).(Snd)))
  end.

Fixpoint sendAllI (l : list MemRegion) : TS (implRegionsTree l) -> TS (implRegionsTree l) :=
  match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) with
  | [] => fun m => m
  | r :: rs => fun m => (sendRegionI r m.(Fst) ,, (sendAllI rs m.(Snd).(Fst) ,, m.(Snd).(Snd)))
  end.

(* --- 2. The Spec Send --- *)

Lemma region_send_wp :
  forall r (env : Env (memRegionTree r)) (x : TS (memRegionTree r)) P,
    (forall v, P (sendRegion r x) v) -> evalActionPropGen env (@memRegionSendFenceIRq r type) x P.
Proof.
  intros r; unfold sendRegion, memRegionSendFenceIRq, memRegionTree.
  destruct (regionKind r); intros env x P HP.
  - unfold externalSendFenceIRq.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    destruct x as [[frq [frp [fw [firq [fack []]]]]] rest].
    cbn.
    unfold cast_reg.
    repeat match goal with |- context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
      rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) end.
    apply HP.
  - apply HP.
Qed.

Lemma send_fold_wp :
  forall l c acc (ms : TS (specMemTree l)) (env : Env (specMemTree l)) P,
    (forall v, P (sendAllS l ms) v) ->
    evalActionPropGen env (genFoldRegionActionsAux memRegionTree (fun r => @memRegionSendFenceIRq r type) c acc l) ms P.
Proof.
  induction l as [| r rs IH]; intros c acc ms env P HP.
  - cbn [genFoldRegionActionsAux].
    apply ev_return; apply HP.
  - cbn [genFoldRegionActionsAux].
    destruct ms as [m0 [m1 []]].
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd].
    apply region_send_wp; intros v; cbv beta.
    cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
    apply IH; intros v'.
    cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd]; apply HP.
Qed.

Lemma specMemSendFenceIRq_wp :
  forall l (env : Env (specMemTree l)) ms P,
    (forall v, P (sendAllS l ms) v) -> evalActionPropGen env (@specMemSendFenceIRq type l) ms P.
Proof.
  intros l env ms P HP; unfold specMemSendFenceIRq, genFoldRegionUnitActions, genFoldRegionActions.
  apply send_fold_wp; exact HP.
Qed.

(* --- 3. The Impl Send --- *)

Lemma region_send_impl :
  forall r env (y : TS (implMemRegionTree r)) Q,
    evalActionPropGen env (@liftToImplRegion type r (Bit 0) (memRegionSendFenceIRq r)) y Q ->
    exists v, Q (sendRegionI r y) v.
Proof.
  intros r; unfold liftToImplRegion, sendRegionI, sendRegion, memRegionSendFenceIRq, implMemRegionTree, memRegionTree.
  destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros env y Q H.
  - unfold externalSendFenceIRq in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    destruct y as [[[frq [frp [fw [firq [fack []]]]]] rest] ex].
    cbn in H.
    unfold cast_reg in H.
    repeat match type of H with context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
      rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) in H end.
    eexists; exact H.
  - apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H; cbn [evalActionPropGen] in H.
    rewrite writeSubTreeState_readSubTreeState in H.
    eexists; exact H.
Qed.

Lemma send_fold_impl :
  forall l c acc (env : Env (implRegionsTree l)) mi P,
    evalActionPropGen env (genFoldRegionActionsAux implMemRegionTree
                             (fun r => @liftToImplRegion type r (Bit 0) (memRegionSendFenceIRq r)) c acc l) mi P ->
    exists v, P (sendAllI l mi) v.
Proof.
  intros l; induction l as [| r rs IH]; intros c acc env mi P H.
  - cbn [genFoldRegionActionsAux evalActionPropGen] in H.
    eexists; exact H.
  - cbn [genFoldRegionActionsAux evalActionPropGen] in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    destruct mi as [m0 [m1 []]].
    cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in H.
    apply region_send_impl in H as [v0 H]; cbv beta in H.
    cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd] in H.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H.
    cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd] in H.
    apply IH in H as [v1 H].
    cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd] in H.
    exists v1; exact H.
Qed.

Lemma implRegionsSendFenceIRq_char :
  forall l env (mi mi' : TS (implRegionsTree l)) v,
    SemAction env (@implRegionsSendFenceIRq type l) mi mi' v -> mi' = sendAllI l mi.
Proof.
  intros l env mi mi' v H.
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implRegionsSendFenceIRq, genFoldRegionUnitActions, genFoldRegionActions in H.
  apply send_fold_impl in H as [v' [E _]]; symmetry; exact E.
Qed.

(* --- 4. What the Send Keeps --- *)

Lemma ExtRel_send :
  forall r x y, ExtRel r x y -> ExtRel r (sendExt r x) (sendExt r y.(Fst) ,, y.(Snd)).
Proof.
  intros r x y [E1 [E2 [E3 E4]]]; unfold ExtRel, sendExt; cbn [Fst Snd length].
  split; [exact E1 | split; [reflexivity | split; [f_equal; exact E3 | exact E4]]].
Qed.

Lemma RegionRelAt_send :
  forall cp pp i r x y, RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r (sendRegion r x) (sendRegionI r y).
Proof.
  intros cp pp i r; unfold RegionRelAt, sendRegion, sendRegionI, memRegionTree, implMemRegionTree.
  destruct (regionKind r); intros x y H; [exact (ExtRel_send r x y H) | exact H].
Qed.

Lemma MemRelPost_send :
  forall cp pp l i ms mi, MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l (sendAllS l ms) (sendAllI l mi).
Proof.
  intros cp pp; induction l as [| r rs IH]; intros i ms mi H; cbn [MemRelPost sendAllS sendAllI Fst Snd] in *;
    [exact I |].
  destruct H as [H0 H1]; split; [exact (RegionRelAt_send cp pp i r _ _ H0) | exact (IH _ _ _ H1)].
Qed.

Lemma MemRelPre_send :
  forall cp pp sRev iRev post l i ms mi,
    MemRelPre cp pp i l sRev iRev post ms mi ->
    MemRelPre cp pp i l sRev iRev post (sendAllS (l ++ sRev :: post) ms) (sendAllI (l ++ iRev :: post) mi).
Proof.
  intros cp pp sRev iRev post; induction l as [| r l IH]; intros i ms mi H;
    cbn [MemRelPre sendAllS sendAllI app Fst Snd] in *.
  - exact (MemRelPost_send cp pp post (S i) _ _ H).
  - destruct H as [H0 H1]; split; [exact (RegionRelAt_send cp pp i r _ _ H0) | exact (IH _ _ _ H1)].
Qed.

Lemma regionStateAtS_send :
  forall l j r0 (pf : nth_error l j = Some r0) (ms : TS (specMemTree l)),
    isCustomR r0 -> regionStateAt memRegionTree j l r0 pf (sendAllS l ms) = regionStateAt memRegionTree j l r0 pf ms.
Proof.
  induction l as [| r rs IH]; intros [| j'] r0 pf ms Hc; try discriminate pf.
  - cbn [regionStateAt sendAllS Fst].
    set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                with eq_refl => eq_refl end).
    clearbody Heq; clear pf; destruct Heq.
    cbv beta iota.
    revert Hc; generalize (ms.(Fst)); unfold sendRegion, isCustomR, memRegionTree.
    destruct (regionKind r0); intros x Hc; [contradiction | reflexivity].
  - cbn [regionStateAt sendAllS Fst Snd]; exact (IH j' r0 pf _ Hc).
Qed.

Lemma regionStateAtI_send :
  forall l j r0 (pf : nth_error l j = Some r0) (mi : TS (implRegionsTree l)),
    isCustomR r0 ->
    regionStateAt implMemRegionTree j l r0 pf (sendAllI l mi) = regionStateAt implMemRegionTree j l r0 pf mi.
Proof.
  induction l as [| r rs IH]; intros [| j'] r0 pf mi Hc; try discriminate pf.
  - cbn [regionStateAt sendAllI Fst].
    set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                with eq_refl => eq_refl end).
    clearbody Heq; clear pf; destruct Heq.
    cbv beta iota.
    revert Hc; generalize (mi.(Fst)); unfold sendRegionI, isCustomR, implMemRegionTree.
    destruct (regionKind r0); intros y Hc; [contradiction | reflexivity].
  - cbn [regionStateAt sendAllI Fst Snd]; exact (IH j' r0 pf _ Hc).
Qed.

(* A port view that reads neither fenceIWait nor the fence.i requests is unchanged *)
Lemma AllPorts_send :
  forall P, (forall r y, P r (sendExt r y.(Fst) ,, y.(Snd)) = P r y) ->
    forall l mi, AllPorts P l (sendAllI l mi) = AllPorts P l mi.
Proof.
  intros P HP; induction l as [| r rs IH]; intros mi; cbn [AllPorts sendAllI Fst Snd]; [reflexivity |].
  rewrite IH; f_equal.
  generalize (mi.(Fst)); unfold RegionPort, sendRegionI, implMemRegionTree.
  destruct (regionKind r); intros y; [exact (HP r y) | reflexivity].
Qed.

Lemma AllPorts_send_map :
  forall (P Q : forall r, TS (implExternalMemRegionTree r) -> Prop),
    (forall r y, P r y -> Q r (sendExt r y.(Fst) ,, y.(Snd))) ->
    forall l mi, AllPorts P l mi -> AllPorts Q l (sendAllI l mi).
Proof.
  intros P Q HPQ; induction l as [| r rs IH]; intros mi H; cbn [AllPorts sendAllI Fst Snd] in *; [exact I |].
  destruct H as [H0 H1]; split; [| exact (IH _ H1)].
  revert H0; generalize (mi.(Fst)); unfold RegionPort, sendRegionI, implMemRegionTree.
  destruct (regionKind r); intros y Hy; [exact (HPQ r y Hy) | exact I].
Qed.

(* The request count matches the acks again (no request was outstanding) *)
Lemma fenceICount_send :
  forall r (y : TS (implExternalMemRegionTree r)),
    y.(Fst).(Fst).(Snd).(Snd).(Fst) = false -> RegionFenceICountInv r y.(Fst) ->
    RegionFenceICountInv r (sendExt r y.(Fst) ,, y.(Snd)).(Fst).
Proof.
  intros r y Hw Hi; unfold RegionFenceICountInv in *; cbv zeta in *; rewrite Hw in Hi.
  unfold sendExt; cbn [Fst Snd length]; f_equal; exact Hi.
Qed.

Lemma lineContent_send :
  forall initLine l ms L, lineContent initLine l (sendAllS l ms) L = lineContent initLine l ms L.
Proof.
  intros initLine; induction l as [| r rs IH]; intros ms L; cbn [lineContent sendAllS Fst Snd]; [reflexivity |].
  rewrite IH; destruct (isRegionAddrB r L); [| reflexivity].
  generalize (ms.(Fst)); unfold RegionLineContent, sendRegion, memRegionTree.
  destruct (regionKind r); intros x; reflexivity.
Qed.

Lemma SnapshotOK_send :
  forall l fwcs ms, SnapshotOK fwcs l ms -> SnapshotOK fwcs l (sendAllS l ms).
Proof.
  induction l as [| r rs IH]; intros fwcs ms H; cbn [SnapshotOK sendAllS Fst Snd] in *; [exact I |].
  destruct H as [H0 H1]; split; [| exact (IH _ _ H1)].
  revert H0; generalize (ms.(Fst)); unfold RegionSnapshotOK, sendRegion, memRegionTree.
  destruct (regionKind r); intros x Hx; exact Hx.
Qed.

(* --- 5. The Memory Relation --- *)

Section SendRel.
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

  Lemma MemRel_send :
    forall o ms mi,
      MemRel pre post revBase revPfB revPfA clintS clint plicS plic o ms mi ->
      MemRel pre post revBase revPfB revPfA clintS clint plicS plic o (sendAllS specRegions ms) (sendAllI implRegions mi).
  Proof.
    intros o ms mi [Hpre [Hcl [Hpl Hrv]]]; unfold MemRel.
    unfold specClintState, implClintState, specPlicState, implPlicState, specRevState, implRevState in *.
    rewrite !regionStateAtS_send, !regionStateAtI_send by exact I.
    refine (conj _ (conj Hcl (conj Hpl Hrv))).
    exact (MemRelPre_send _ _ _ _ post pre 0 ms mi Hpre).
  Qed.

  Lemma DevInv_send :
    forall mi, DevInv pre post revBase revPfB revPfA clint plic mi ->
      DevInv pre post revBase revPfB revPfA clint plic (sendAllI implRegions mi).
  Proof.
    intros mi H; unfold DevInv, implClintState, implPlicState in *.
    rewrite !regionStateAtI_send by exact I; exact H.
  Qed.
End SendRel.
