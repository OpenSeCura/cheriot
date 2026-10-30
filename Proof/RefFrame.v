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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * FRAME LEMMAS FOR REGION UPDATES
 * ===========================================================================
 * A device step changes the state of one region (`updRegionStateAt`). Here:
 * 1. the other positions keep their states;
 * 2. a CustomMem position is invisible to the ExternalMem ports (`AllPorts`),
 *    to the line contents and to the fetch view of the spec memory;
 * 3. the memory relation survives an update at a position where it is trivial. *)

Local Notation TS t := (TreeState DomainElemState t).

(* --- 1. Other Positions --- *)

Section RegionAtOther.
  Variable regionTree : MemRegion -> Tree DomainElem.

  Lemma regionStateAt_upd_other :
    forall (i j : nat) (regions : list MemRegion) (r0 r1 : MemRegion)
           (pfi : nth_error regions i = Some r0) (pfj : nth_error regions j = Some r1)
           (s : TS (regionsTree regionTree regions)) (v : TS (regionTree r0)),
      i <> j ->
      regionStateAt regionTree j regions r1 pfj (updRegionStateAt regionTree i regions r0 pfi s v) =
      regionStateAt regionTree j regions r1 pfj s.
  Proof.
    intros i j regions; revert i j.
    induction regions as [| r rs IH]; intros [| i'] [| j'] r0 r1 pfi pfj s v Hne;
      try discriminate pfi; try discriminate pfj.
    - exfalso; apply Hne; reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn [regionStateAt updRegionStateAt Fst Snd].
      apply IH; intros E; apply Hne; rewrite E; reflexivity.
  Qed.

End RegionAtOther.

(* --- 2. CustomMem Positions --- *)

Definition isCustomR (r : MemRegion) : Prop :=
  match r.(regionKind) with
  | ExternalMem => False
  | CustomMem _ _ _ _ => True
  end.

Section CustomInvisible.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma RegionPort_custom :
    forall P r (y : TS (implMemRegionTree core r)), isCustomR r -> RegionPort core P r y = True.
  Proof.
    intros P r; unfold isCustomR, RegionPort, implMemRegionTree.
    destruct (regionKind r); intros y H; [contradiction | reflexivity].
  Qed.

  Lemma AllPorts_upd :
    forall P l idx r0 (pf : nth_error l idx = Some r0) (mi : TS (implRegionsTree core l)) v,
      isCustomR r0 ->
      AllPorts core P l (updRegionStateAt (implMemRegionTree core) idx l r0 pf mi v) = AllPorts core P l mi.
  Proof.
    intros P l; induction l as [| r rs IH]; intros [| i'] r0 pf mi v Hc; try discriminate pf.
    - cbn [AllPorts updRegionStateAt Fst Snd].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      rewrite !RegionPort_custom by exact Hc; reflexivity.
    - cbn [AllPorts updRegionStateAt Fst Snd].
      rewrite IH by exact Hc; reflexivity.
  Qed.

  Lemma RegionLineContent_custom :
    forall r (x : TS (memRegionTree core r)) L,
      isCustomR r -> RegionLineContent core initLine r x L = getDefault LineReadRp.
  Proof.
    intros r; unfold isCustomR, RegionLineContent, memRegionTree.
    destruct (regionKind r); intros x L H; [contradiction | reflexivity].
  Qed.

  Lemma lineContent_upd :
    forall l idx r0 (pf : nth_error l idx = Some r0) (ms : TS (specMemTree core l)) w L,
      isCustomR r0 ->
      lineContent core initLine l (updRegionStateAt (memRegionTree core) idx l r0 pf ms w) L =
      lineContent core initLine l ms L.
  Proof.
    intros l; induction l as [| r rs IH]; intros [| i'] r0 pf ms w L Hc; try discriminate pf.
    - cbn [lineContent updRegionStateAt Fst Snd].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      rewrite !RegionLineContent_custom by exact Hc; reflexivity.
    - cbn [lineContent updRegionStateAt Fst Snd].
      rewrite IH by exact Hc; reflexivity.
  Qed.

  Lemma RegionFetchViewExt_custom :
    forall r (x y : TS (memRegionTree core r)), isCustomR r -> RegionFetchViewExt core r x y.
  Proof.
    intros r; unfold isCustomR, RegionFetchViewExt, memRegionTree.
    destruct (regionKind r); intros x y H; [contradiction | exact I].
  Qed.

  Lemma FetchViewExt_upd :
    forall l idx r0 (pf : nth_error l idx = Some r0) (ms : TS (specMemTree core l)) w,
      isCustomR r0 ->
      FetchViewExt core l ms (updRegionStateAt (memRegionTree core) idx l r0 pf ms w).
  Proof.
    intros l; induction l as [| r rs IH]; intros [| i'] r0 pf ms w Hc; try discriminate pf.
    - cbn [FetchViewExt updRegionStateAt Fst Snd].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      split; [exact (RegionFetchViewExt_custom r0 _ _ Hc) | apply FetchViewExt_refl].
    - cbn [FetchViewExt updRegionStateAt Fst Snd].
      split; [apply RegionFetchViewExt_refl | exact (IH i' r0 pf _ w Hc)].
  Qed.

  Lemma RegionSnapshotOK_custom :
    forall r fwc (x : TS (memRegionTree core r)), isCustomR r -> RegionSnapshotOK core r fwc x.
  Proof.
    intros r fwc; unfold isCustomR, RegionSnapshotOK, memRegionTree.
    destruct (regionKind r); intros x H; [contradiction | exact I].
  Qed.

  Lemma SnapshotOK_upd :
    forall l fwcs idx r0 (pf : nth_error l idx = Some r0) (ms : TS (specMemTree core l)) w,
      isCustomR r0 ->
      SnapshotOK core fwcs l ms ->
      SnapshotOK core fwcs l (updRegionStateAt (memRegionTree core) idx l r0 pf ms w).
  Proof.
    intros l; induction l as [| r rs IH]; intros fwcs [| i'] r0 pf ms w Hc Hs; try discriminate pf.
    - cbn [SnapshotOK updRegionStateAt Fst Snd] in *.
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      split; [exact (RegionSnapshotOK_custom r0 _ _ Hc) | exact (proj2 Hs)].
    - cbn [SnapshotOK updRegionStateAt Fst Snd] in *.
      split; [exact (proj1 Hs) | exact (IH _ i' r0 pf _ w Hc (proj2 Hs))].
  Qed.

End CustomInvisible.

(* --- 3. The Memory Relation at Trivial Positions --- *)

Section MemRelUpd.
  Variable core : string.
  Variables cp pp : nat.

  Lemma MemRelPost_upd :
    forall l i idx r0S r0I (pfS : nth_error l idx = Some r0S) (pfI : nth_error l idx = Some r0I)
           (ms : TS (specMemTree core l)) (mi : TS (implRegionsTree core l)) v w,
      (forall x y, RegionRelAt core cp pp (i + idx) r0S x y) ->
      MemRelPost core cp pp i l ms mi ->
      MemRelPost core cp pp i l (updRegionStateAt (memRegionTree core) idx l r0S pfS ms v)
                                (updRegionStateAt (implMemRegionTree core) idx l r0I pfI mi w).
  Proof.
    intros l; induction l as [| r rs IH]; intros i [| i'] r0S r0I pfS pfI ms mi v w Htriv Hrel;
      try discriminate pfS.
    - cbn [MemRelPost updRegionStateAt Fst Snd] in *.
      set (HeqS := match pfS in (_ = o) return match o with Some r0' => r0' = r | None => False end
                   with eq_refl => eq_refl end).
      set (HeqI := match pfI in (_ = o) return match o with Some r0' => r0' = r | None => False end
                   with eq_refl => eq_refl end).
      clearbody HeqS HeqI; clear pfS pfI.
      destruct HeqS.
      cbv beta iota.
      split; [| exact (proj2 Hrel)].
      rewrite Nat.add_0_r in Htriv; apply Htriv.
    - cbn [MemRelPost updRegionStateAt Fst Snd] in *.
      split; [exact (proj1 Hrel) |].
      apply IH; [| exact (proj2 Hrel)].
      replace (S i + i')%nat with (i + S i')%nat by lia; exact Htriv.
  Qed.

  Lemma MemRelPre_upd :
    forall sRev iRev post l i idx r0S r0I
           (pfS : nth_error (l ++ sRev :: post) idx = Some r0S)
           (pfI : nth_error (l ++ iRev :: post) idx = Some r0I)
           (ms : TS (specMemTree core (l ++ sRev :: post))) (mi : TS (implRegionsTree core (l ++ iRev :: post)))
           v w,
      idx <> length l ->
      (forall x y, RegionRelAt core cp pp (i + idx) r0S x y) ->
      MemRelPre core cp pp i l sRev iRev post ms mi ->
      MemRelPre core cp pp i l sRev iRev post
        (updRegionStateAt (memRegionTree core) idx (l ++ sRev :: post) r0S pfS ms v)
        (updRegionStateAt (implMemRegionTree core) idx (l ++ iRev :: post) r0I pfI mi w).
  Proof.
    intros sRev iRev post l; induction l as [| r rs IH];
      intros i [| i'] r0S r0I pfS pfI ms mi v w Hne Htriv Hrel.
    - exfalso; apply Hne; reflexivity.
    - cbn [MemRelPre app updRegionStateAt Fst Snd] in *.
      apply (MemRelPost_upd post (S i) i' r0S r0I pfS pfI); [| exact Hrel].
      replace (S i + i')%nat with (i + S i')%nat by lia; exact Htriv.
    - cbn [MemRelPre app updRegionStateAt Fst Snd] in *.
      set (HeqS := match pfS in (_ = o) return match o with Some r0' => r0' = r | None => False end
                   with eq_refl => eq_refl end).
      set (HeqI := match pfI in (_ = o) return match o with Some r0' => r0' = r | None => False end
                   with eq_refl => eq_refl end).
      clearbody HeqS HeqI; clear pfS pfI.
      destruct HeqS.
      cbv beta iota.
      split; [| exact (proj2 Hrel)].
      rewrite Nat.add_0_r in Htriv; apply Htriv.
    - cbn [MemRelPre app updRegionStateAt Fst Snd length] in *.
      split; [exact (proj1 Hrel) |].
      apply IH; [lia | | exact (proj2 Hrel)].
      replace (S i + i')%nat with (i + S i')%nat by lia; exact Htriv.
  Qed.

  (* The two sides may name the position by different (equal) indices *)
  Lemma MemRelPre_upd2 :
    forall sRev iRev post l i idxS idxI r0S r0I
           (pfS : nth_error (l ++ sRev :: post) idxS = Some r0S)
           (pfI : nth_error (l ++ iRev :: post) idxI = Some r0I)
           (ms : TS (specMemTree core (l ++ sRev :: post))) (mi : TS (implRegionsTree core (l ++ iRev :: post)))
           v w,
      idxI = idxS ->
      idxS <> length l ->
      (forall x y, RegionRelAt core cp pp (i + idxS) r0S x y) ->
      MemRelPre core cp pp i l sRev iRev post ms mi ->
      MemRelPre core cp pp i l sRev iRev post
        (updRegionStateAt (memRegionTree core) idxS (l ++ sRev :: post) r0S pfS ms v)
        (updRegionStateAt (implMemRegionTree core) idxI (l ++ iRev :: post) r0I pfI mi w).
  Proof.
    intros sRev iRev post l i idxS idxI r0S r0I pfS pfI ms mi v w E; subst idxI.
    apply MemRelPre_upd.
  Qed.

  (* Only the impl side changes *)
  Lemma MemRelPre_upd_impl :
    forall sRev iRev post l i idxS idxI r0S r0I
           (pfS : nth_error (l ++ sRev :: post) idxS = Some r0S)
           (pfI : nth_error (l ++ iRev :: post) idxI = Some r0I)
           (ms : TS (specMemTree core (l ++ sRev :: post))) (mi : TS (implRegionsTree core (l ++ iRev :: post)))
           w,
      idxI = idxS ->
      idxS <> length l ->
      (forall x y, RegionRelAt core cp pp (i + idxS) r0S x y) ->
      MemRelPre core cp pp i l sRev iRev post ms mi ->
      MemRelPre core cp pp i l sRev iRev post ms
        (updRegionStateAt (implMemRegionTree core) idxI (l ++ iRev :: post) r0I pfI mi w).
  Proof.
    intros sRev iRev post l i idxS idxI r0S r0I pfS pfI ms mi w E Hne Htriv H.
    pose proof (MemRelPre_upd2 sRev iRev post l i idxS idxI r0S r0I pfS pfI ms mi
                  (regionStateAt (memRegionTree core) idxS (l ++ sRev :: post) r0S pfS ms) w E Hne Htriv H) as H'.
    rewrite updRegionStateAt_regionStateAt in H'; exact H'.
  Qed.

End MemRelUpd.

(* --- 4. Steps of the Region at a Position --- *)

Lemma SemAction_genNthRegionAction_iff :
  forall (regionTree : MemRegion -> Tree DomainElem) idx regions r0 (pf : nth_error regions idx = Some r0) {k}
         (act : Action type (regionTree r0) k) (env : Env (regionsTree regionTree regions))
         (s s' : TS (regionsTree regionTree regions)) (v : type k),
    SemAction env (@genNthRegionAction regionTree type idx regions r0 pf k act) s s' v <->
    exists x',
      SemAction (envRegionAt regionTree idx regions r0 pf env s) act (regionStateAt regionTree idx regions r0 pf s) x' v /\
      s' = updRegionStateAt regionTree idx regions r0 pf s x'.
Proof.
  intros regionTree idx regions r0 pf k act env s s' v.
  rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_genNthRegionAction.
  split.
  - intros H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [x' [v' [HS [Hs Hv]]]]; subst v'.
    exists x'; split; [exact HS | symmetry; exact Hs].
  - intros [x' [HS ->]].
    rewrite SemAction_iff_evalActionPropGen in HS.
    eapply evalActionPropGen_mono; [| exact HS].
    intros x'' r [Hx Hr]; subst; split; reflexivity.
Qed.
