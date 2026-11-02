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
From Cheriot Require Import SpecDefines SpecDevice Clint Plic SpecRevoker Impl.ImplRevoker Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefFetch RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefSpecRead RefRevoker RefMemStep RefRevokerStep RefWriteRqPorts RefRouteAt RefRqStepChar RefDevSim.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, a write request to a CustomMem line (a device) or an unmapped line, memory part:
 * the impl regions' write is matched by the spec memory's write of the same request, and the
 * memory relation holds after both. *)

(* --- 1. A CustomMem Region's Write --- *)

Section CustomWrite.
  (* The impl region runs the spec region's line write on its base state *)
  Lemma implCustomWrite_inv :
    forall r env (y y' : TS (implMemRegionTree r)) (w : type LineWriteRq) v,
      isCustomR r -> SemAction env (@implMemRegionLineWriteRq r type w) y y' v ->
      v = true /\ y'.(Snd) = y.(Snd) /\
      exists env' v0, SemAction env' (@memRegionLineWrite r type w) y.(Fst) y'.(Fst) v0.
  Proof.
    intros r; unfold isCustomR, implMemRegionLineWriteRq, memRegionLineWrite, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd as [| ch rd wr irq]; cbn [regionKind];
      intros env y y' w v Hc H; [contradiction |].
    unfold implCustomLineWriteRq in H.
    rewrite SemAction_iff_evalActionPropGen in H.
    cbn [evalActionPropGen] in H.
    rewrite evalActionPropGen_liftAction in H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [x' [v0 [Hx Hk]]].
    cbv beta in Hk; cbn [evalActionPropGen] in Hk; destruct Hk as [E1 E2].
    destruct y as [y0 []]; subst y'.
    split; [symmetry; exact E2 | split; [reflexivity |]].
    exists (subEnv child0Path env (y0 ,, tt)), v0.
    rewrite SemAction_iff_evalActionPropGen.
    cbn [evalActionPropGen child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
    cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in Hx.
    rewrite SemAction_iff_evalActionPropGen in Hx.
    eapply evalActionPropGen_mono; [| exact Hx].
    intros s r0 [-> ->]; split; reflexivity.
  Qed.

  Lemma lineKind_custom_at :
    forall L l, lineKind l L = Some false ->
      exists j r (pf : nth_error l j = Some r), isRegionAddrB r L = true /\ isCustomR r.
  Proof.
    intros L l; induction l as [| r rs IH]; intros Hk; [discriminate Hk |].
    cbn [lineKind] in Hk.
    destruct (isRegionAddrB r L) eqn:Em.
    - exists 0%nat, r, eq_refl; split; [exact Em |].
      unfold isCustomR; destruct (regionKind r); [discriminate Hk | exact I].
    - destruct (IH Hk) as [j [r' [pf [Hm Hc]]]].
      exists (S j), r', pf; split; [exact Hm | exact Hc].
  Qed.

  (* The region holding a line is unique *)
  Lemma line_index_unique :
    forall L l j k r r', lineUnique l L -> nth_error l j = Some r -> isRegionAddrB r L = true ->
      nth_error l k = Some r' -> isRegionAddrB r' L = true -> j = k.
  Proof.
    intros L l; induction l as [| r0 rs IH]; intros [| j'] [| k'] r r' Hu Hj Hm Hk Hm'; try discriminate Hj;
      try discriminate Hk; cbn [nth_error lineUnique] in *; [reflexivity | | | f_equal].
    - injection Hj as ->; rewrite Hm in Hu.
      exfalso; exact (lineKind_some_nth L rs k' r' Hk Hm' Hu).
    - injection Hk as ->; rewrite Hm' in Hu.
      exfalso; exact (lineKind_some_nth L rs j' r Hj Hm Hu).
    - destruct (isRegionAddrB r0 L) eqn:E0.
      + exfalso; exact (lineKind_some_nth L rs j' r Hj Hm Hu).
      + exact (IH _ _ _ _ Hu Hj Hm Hk Hm').
  Qed.

  Lemma nth_error_app_ne :
    forall (A : Type) (pre post : list A) a b i, i <> length pre ->
      nth_error (pre ++ a :: post) i = nth_error (pre ++ b :: post) i.
  Proof.
    intros A pre; induction pre as [| x xs IH]; intros post a b [| i'] Hne; cbn [app nth_error length] in *;
      try reflexivity; [lia |].
    apply IH; lia.
  Qed.
End CustomWrite.

(* --- 2. The Devices' Line Writes, as Region Writes --- *)

Section DevRegionWrite.
  Ltac mrw H := rewrite SemAction_iff_evalActionPropGen in H;
    cbn [memRegionLineWrite clintMemRegion plicMemRegion revokerMemRegion specRevRegion implRevRegion
         regionKind evalActionPropGen] in H;
    rewrite <- SemAction_iff_evalActionPropGen in H.

  Ltac mrw_goal := rewrite SemAction_iff_evalActionPropGen;
    cbn [memRegionLineWrite clintMemRegion plicMemRegion revokerMemRegion specRevRegion implRevRegion
         regionKind evalActionPropGen];
    rewrite <- SemAction_iff_evalActionPropGen.

  Lemma clintMem_write_sim :
    forall b pbI paI pbS paS envI envS (xs xi xi' : TS (Node "clint" clintChildren)) (w : type LineWriteRq) v,
      ClintRel xs xi ->
      SemAction envI (@memRegionLineWrite (@clintMemRegion b pbI paI) type w) xi xi' v ->
      exists xs', SemAction envS (@memRegionLineWrite (@clintMemRegion b pbS paS) type w) xs xs' v /\
        ClintRel xs' xi' /\ (clintSampled xs' = true -> clintSampled xs = true) /\ (ClintInv xi -> ClintInv xi').
  Proof.
    intros b pbI paI pbS paS envI envS xs xi xi' w v HR H.
    mrw H.
    destruct (clintWrite_sim b envI envS xs xi xi' _ _ _ v HR H) as [xs' [Hs Hrest]].
    exists xs'; split; [mrw_goal; exact Hs | exact Hrest].
  Qed.

  Lemma plicMem_write_sim :
    forall n1 n2 b pbI paI pbS paS envI envS (xs : TS (plicTree n1)) (xi xi' : TS (plicTree n2)) (w : type LineWriteRq) v,
      PlicRel n1 n2 xs xi ->
      SemAction envI (@memRegionLineWrite (@plicMemRegion n2 b pbI paI) type w) xi xi' v ->
      exists xs', SemAction envS (@memRegionLineWrite (@plicMemRegion n1 b pbS paS) type w) xs xs' v /\
        PlicRel n1 n2 xs' xi' /\ (plicMeipOf xs' = true -> plicMeipOf xs = true) /\ (PlicInv xi -> PlicInv xi').
  Proof.
    intros n1 n2 b pbI paI pbS paS envI envS xs xi xi' w v [e HR] H.
    subst n2; cbn [eq_rect] in HR.
    mrw H.
    destruct (plicWrite_sim n1 b envI envS xs xi xi' _ _ _ v HR H) as [xs' [Hs [HR' Hrest]]].
    exists xs'; split; [mrw_goal; exact Hs | split; [exists eq_refl; exact HR' | exact Hrest]].
  Qed.

  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Lemma RevRel_eq_proj :
    forall xs (xi : TS implRevokerTree), RevRel RevEq xs xi <-> projImplRevokerArchState xi = xs.
  Proof.
    intros xs xi; unfold RevRel, revOffAddr, revWithScanAddr, revScanAddr.
    destruct xs as [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 []]]]]]]]]; cbn [Fst Snd]; reflexivity.
  Qed.

  Lemma revMem_write_sim :
    forall envI envS xs (xi xi' : TS implRevokerTree) (w : type LineWriteRq) v,
      RevRel RevEq xs xi ->
      SemAction envI (@memRegionLineWrite (implRevRegion revBase revPfB revPfA) type w) xi xi' v ->
      SemAction envS (@memRegionLineWrite (specRevRegion revBase revPfB revPfA) type w) xs (projImplRevokerArchState xi') v /\
      RevRel RevEq (projImplRevokerArchState xi') xi' /\ revExtraOf xi' = revExtraOf xi /\ revKeyOf xi' = revKeyOf xi.
  Proof.
    intros envI envS xs xi xi' w v HR H.
    assert (E : projImplRevokerArchState xi = xs) by exact (proj1 (RevRel_eq_proj xs xi) HR).
    rewrite <- E.
    mrw H.
    destruct (revMmioWrite_sim revBase envI envS xi xi' _ _ _ v H) as [Hs [E1 E2]].
    split; [mrw_goal; exact Hs |].
    split; [apply RevRel_eq_proj; reflexivity | exact (conj E1 E2)].
  Qed.
End DevRegionWrite.

(* --- 2b. Reads: a CustomMem Region's Read, and the Devices' Line Reads as Region Reads --- *)

(* The line a CustomMem read returns: the device's data, no tags *)
Definition rpOfData (d : type (Array LineBytes (Bit 8))) : type LineReadRp :=
  evalExpr (STRUCT { "data" ::= Var type (Array LineBytes (Bit 8)) d ;
                     "tag"  ::= Const type (Array NumLineTags Bool) (getDefault _) } : Expr type LineReadRp).

Section CustomRead.
  Lemma implCustomRead_inv :
    forall r env (y y' : TS (implMemRegionTree r)) (L : type Addr) mask res,
      isCustomR r -> SemAction env (@implMemRegionLineReadRq r type L mask) y y' res ->
      y'.(Snd) = y.(Snd) /\
      exists env' v, SemAction env' (@memRegionLineRead r type L mask) y.(Fst) y'.(Fst) v /\
                     res = (true ,, ((v ,, (true ,, tt)) ,, tt)) /\ exists d, v = rpOfData d.
  Proof.
    intros r; unfold isCustomR, implMemRegionLineReadRq, memRegionLineRead, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd as [| ch rd wr irq]; cbn [regionKind];
      intros env y y' L mask res Hc H; [contradiction |].
    unfold implCustomLineReadRq in H.
    rewrite SemAction_iff_evalActionPropGen in H.
    cbn [evalActionPropGen] in H.
    rewrite evalActionPropGen_liftAction in H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [x' [d [Hx Hk]]].
    cbv beta in Hk; cbn [evalActionPropGen] in Hk; destruct Hk as [E1 E2].
    destruct y as [y0 []]; subst y'.
    split; [reflexivity |].
    exists (subEnv child0Path env (y0 ,, tt)), (rpOfData d).
    split; [| split; [rewrite <- E2; reflexivity | exists d; reflexivity]].
    rewrite SemAction_iff_evalActionPropGen.
    cbn [evalActionPropGen child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
    cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd] in Hx.
    rewrite SemAction_iff_evalActionPropGen in Hx.
    eapply evalActionPropGen_mono; [| exact Hx].
    intros s0 r0 [-> ->]; cbn [evalActionPropGen]; split; reflexivity.
  Qed.

End CustomRead.

Section DevRegionRead.
  Ltac mrr H := rewrite SemAction_iff_evalActionPropGen in H;
    cbn [memRegionLineRead clintMemRegion plicMemRegion revokerMemRegion specRevRegion implRevRegion
         regionKind evalActionPropGen] in H;
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [?s [?d [?Hs ?Hk]]]; clear H;
    cbv beta in *; cbn [evalActionPropGen] in *.

  Ltac mrr_goal Hs E :=
    rewrite SemAction_iff_evalActionPropGen;
    cbn [memRegionLineRead clintMemRegion plicMemRegion revokerMemRegion specRevRegion implRevRegion
         regionKind evalActionPropGen];
    rewrite SemAction_iff_evalActionPropGen in Hs;
    eapply evalActionPropGen_mono; [| exact Hs];
    intros ?s0 ?r0 [-> ->]; cbn [evalActionPropGen]; split; [reflexivity | exact E].

  Lemma clintMem_read_sim :
    forall bI bS pbI paI pbS paS envI envS (xs xi xi' : TS (Node "clint" clintChildren)) (L : type Addr) mask v,
      bS = bI -> ClintRel xs xi ->
      SemAction envI (@memRegionLineRead (@clintMemRegion bI pbI paI) type L mask) xi xi' v ->
      xi' = xi /\ SemAction envS (@memRegionLineRead (@clintMemRegion bS pbS paS) type L mask) xs xs v.
  Proof.
    intros bI bS pbI paI pbS paS envI envS xs xi xi' L mask v Eb HR H; subst bS.
    mrr H. destruct Hk as [E1 E2]; subst s.
    destruct (clintRead_sim bI envI envS xs xi xi' _ _ _ HR Hs) as [-> Hs2].
    split; [reflexivity |].
    mrr_goal Hs2 E2.
  Qed.

  Lemma plicMem_read_sim :
    forall n1 n2 bI bS pbI paI pbS paS envI envS (xs : TS (plicTree n1)) (xi xi' : TS (plicTree n2)) (L : type Addr) mask v,
      bS = bI -> PlicRel n1 n2 xs xi ->
      SemAction envI (@memRegionLineRead (@plicMemRegion n2 bI pbI paI) type L mask) xi xi' v ->
      exists xs', SemAction envS (@memRegionLineRead (@plicMemRegion n1 bS pbS paS) type L mask) xs xs' v /\
        PlicRel n1 n2 xs' xi' /\ (plicMeipOf xs' = true -> plicMeipOf xs = true) /\ (PlicInv xi -> PlicInv xi').
  Proof.
    intros n1 n2 bI bS pbI paI pbS paS envI envS xs xi xi' L mask v Eb [e HR] H; subst bS n2; cbn [eq_rect] in HR.
    mrr H. destruct Hk as [E1 E2]; subst s.
    destruct (plicRead_sim n1 bI envI envS xs xi xi' _ _ _ HR Hs) as [xs' [Hs2 [HR' Hrest]]].
    exists xs'; split; [mrr_goal Hs2 E2 | split; [exists eq_refl; exact HR' | exact Hrest]].
  Qed.

  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Lemma revMem_read_sim :
    forall envI envS xs (xi xi' : TS implRevokerTree) (L : type Addr) mask v,
      RevRel RevEq xs xi ->
      SemAction envI (@memRegionLineRead (implRevRegion revBase revPfB revPfA) type L mask) xi xi' v ->
      xi' = xi /\ SemAction envS (@memRegionLineRead (specRevRegion revBase revPfB revPfA) type L mask) xs xs v.
  Proof.
    intros envI envS xs xi xi' L mask v HR H.
    assert (E : projImplRevokerArchState xi = xs) by exact (proj1 (RevRel_eq_proj xs xi) HR).
    rewrite <- E.
    mrr H. destruct Hk as [E1 E2]; subst s.
    destruct (revMmioRead_sim revBase envI envS xi xi' _ _ _ Hs) as [-> Hs2].
    split; [reflexivity |].
    mrr_goal Hs2 E2.
  Qed.
End DevRegionRead.

(* --- 3. Positions in `pre` and `post`, Named Alike on Both Sides --- *)

(* A position of `pre` (or of `post`) as a position of `pre ++ x :: post`: the proof does not depend
 * on `x`, so the spec and impl lists name the position by casts that reduce alike *)
Fixpoint nth_pre_pf {A : Type} (pre : list A) (x : A) (post : list A) (k : nat) (r : A) {struct pre}
  : nth_error pre k = Some r -> nth_error (pre ++ x :: post) k = Some r :=
  match pre as l, k as k0 return nth_error l k0 = Some r -> nth_error (l ++ x :: post) k0 = Some r with
  | [], 0%nat => fun pf => match pf in (_ = o) return if o is Some _ then _ else True with eq_refl => I end
  | [], S _ => fun pf => match pf in (_ = o) return if o is Some _ then _ else True with eq_refl => I end
  | a :: pre', 0%nat => fun pf => pf
  | a :: pre', S k' => fun pf => nth_pre_pf pre' x post k' r pf
  end.

Fixpoint nth_post_pf {A : Type} (pre : list A) (x : A) (post : list A) (k : nat) (r : A) {struct pre}
  : nth_error post k = Some r -> nth_error (pre ++ x :: post) (S (length pre + k)) = Some r :=
  match pre as l return nth_error post k = Some r -> nth_error (l ++ x :: post) (S (length l + k)) = Some r with
  | [] => fun pf => pf
  | a :: pre' => fun pf => nth_post_pf pre' x post k r pf
  end.

Lemma nth_error_app_split :
  forall (A : Type) (pre post : list A) x j r, nth_error (pre ++ x :: post) j = Some r ->
    (exists k (pf : nth_error pre k = Some r), j = k) \/ (j = length pre /\ r = x) \/
    (exists k (pf : nth_error post k = Some r), j = S (length pre + k)).
Proof.
  intros A pre; induction pre as [| a pre' IH]; intros post x [| j'] r H; cbn [app nth_error length] in *.
  - right; left; injection H as ->; split; reflexivity.
  - right; right; exists j', H; reflexivity.
  - left; exists 0%nat, H; reflexivity.
  - destruct (IH post x j' r H) as [[k [pf ->]] | [[-> ->] | [k [pf ->]]]].
    + left; exists (S k), pf; reflexivity.
    + right; left; split; reflexivity.
    + right; right; exists k, pf; reflexivity.
Qed.

Section PosRel.
  Variables cp pp : nat.

  Lemma MemRelPost_at :
    forall l i k r (pf : nth_error l k = Some r) ms mi,
      MemRelPost cp pp i l ms mi ->
      RegionRelAt cp pp (i + k) r (regionStateAt memRegionTree k l r pf ms) (regionStateAt implMemRegionTree k l r pf mi).
  Proof.
    induction l as [| r0 rs IH]; intros i [| k'] r pf ms mi H; try discriminate pf; cbn [MemRelPost] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r0 | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      rewrite Nat.add_0_r; exact (proj1 H).
    - cbn [regionStateAt].
      replace (i + S k')%nat with (S i + k')%nat by lia.
      exact (IH _ _ _ pf _ _ (proj2 H)).
  Qed.

  Lemma MemRelPost_upd_at :
    forall l i k r (pf : nth_error l k = Some r) ms mi v w,
      RegionRelAt cp pp (i + k) r v w -> MemRelPost cp pp i l ms mi ->
      MemRelPost cp pp i l (updRegionStateAt memRegionTree k l r pf ms v) (updRegionStateAt implMemRegionTree k l r pf mi w).
  Proof.
    induction l as [| r0 rs IH]; intros i [| k'] r pf ms mi v w Hr H; try discriminate pf; cbn [MemRelPost] in H |- *.
    - cbn [updRegionStateAt Fst Snd].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r0 | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      rewrite Nat.add_0_r in Hr; exact (conj Hr (proj2 H)).
    - cbn [updRegionStateAt Fst Snd].
      split; [exact (proj1 H) |].
      apply IH; [| exact (proj2 H)].
      replace (S i + k')%nat with (i + S k')%nat by lia; exact Hr.
  Qed.

  Variables sRev iRev : MemRegion.
  Variable post : list MemRegion.

  Lemma MemRelPre_at_pre :
    forall l i k r (pf : nth_error l k = Some r) ms mi,
      MemRelPre cp pp i l sRev iRev post ms mi ->
      RegionRelAt cp pp (i + k) r (regionStateAt memRegionTree k (l ++ sRev :: post) r (nth_pre_pf l sRev post k r pf) ms)
                                  (regionStateAt implMemRegionTree k (l ++ iRev :: post) r (nth_pre_pf l iRev post k r pf) mi).
  Proof.
    induction l as [| r0 rs IH]; intros i [| k'] r pf ms mi H; try discriminate pf; cbn [MemRelPre] in H.
    - cbn [regionStateAt nth_pre_pf app nth_error] in pf |- *.
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r0 | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      rewrite Nat.add_0_r; exact (proj1 H).
    - cbn [regionStateAt nth_pre_pf app].
      replace (i + S k')%nat with (S i + k')%nat by lia.
      exact (IH _ _ _ pf _ _ (proj2 H)).
  Qed.

  Lemma MemRelPre_upd_pre :
    forall l i k r (pf : nth_error l k = Some r) ms mi v w,
      RegionRelAt cp pp (i + k) r v w -> MemRelPre cp pp i l sRev iRev post ms mi ->
      MemRelPre cp pp i l sRev iRev post
        (updRegionStateAt memRegionTree k (l ++ sRev :: post) r (nth_pre_pf l sRev post k r pf) ms v)
        (updRegionStateAt implMemRegionTree k (l ++ iRev :: post) r (nth_pre_pf l iRev post k r pf) mi w).
  Proof.
    induction l as [| r0 rs IH]; intros i [| k'] r pf ms mi v w Hr H; try discriminate pf; cbn [MemRelPre] in H |- *.
    - cbn [updRegionStateAt nth_pre_pf app nth_error Fst Snd] in pf |- *.
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r0 | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      rewrite Nat.add_0_r in Hr; exact (conj Hr (proj2 H)).
    - cbn [updRegionStateAt nth_pre_pf app Fst Snd].
      split; [exact (proj1 H) |].
      apply IH; [| exact (proj2 H)].
      replace (S i + k')%nat with (i + S k')%nat by lia; exact Hr.
  Qed.

  Lemma MemRelPre_at_post :
    forall l i k r (pf : nth_error post k = Some r) ms mi,
      MemRelPre cp pp i l sRev iRev post ms mi ->
      RegionRelAt cp pp (i + S (length l + k)) r
        (regionStateAt memRegionTree (S (length l + k)) (l ++ sRev :: post) r (nth_post_pf l sRev post k r pf) ms)
        (regionStateAt implMemRegionTree (S (length l + k)) (l ++ iRev :: post) r (nth_post_pf l iRev post k r pf) mi).
  Proof.
    induction l as [| r0 rs IH]; intros i k r pf ms mi H; cbn [MemRelPre] in H.
    - cbn [regionStateAt nth_post_pf app length].
      replace (i + S (0 + k))%nat with (S i + k)%nat by lia.
      exact (MemRelPost_at post (S i) k r pf _ _ H).
    - cbn [regionStateAt nth_post_pf app length].
      match goal with |- RegionRelAt _ _ ?n _ _ _ => replace n with (S i + S (length rs + k))%nat by lia end.
      exact (IH _ _ _ pf _ _ (proj2 H)).
  Qed.

  Lemma MemRelPre_upd_post :
    forall l i k r (pf : nth_error post k = Some r) ms mi v w,
      RegionRelAt cp pp (i + S (length l + k)) r v w -> MemRelPre cp pp i l sRev iRev post ms mi ->
      MemRelPre cp pp i l sRev iRev post
        (updRegionStateAt memRegionTree (S (length l + k)) (l ++ sRev :: post) r (nth_post_pf l sRev post k r pf) ms v)
        (updRegionStateAt implMemRegionTree (S (length l + k)) (l ++ iRev :: post) r (nth_post_pf l iRev post k r pf) mi w).
  Proof.
    induction l as [| r0 rs IH]; intros i k r pf ms mi v w Hr H; cbn [MemRelPre] in H |- *.
    - cbn [updRegionStateAt nth_post_pf app length Fst Snd] in *.
      apply MemRelPost_upd_at; [| exact H].
      match goal with |- RegionRelAt _ _ ?n _ _ _ => replace n with (i + S (0 + k))%nat by lia end; exact Hr.
    - cbn [updRegionStateAt nth_post_pf app length Fst Snd].
      split; [exact (proj1 H) |].
      apply IH; [| exact (proj2 H)].
      cbn [length] in Hr.
      match type of Hr with RegionRelAt _ _ ?n _ _ _ => replace (S i + S (length rs + k))%nat with n by lia end; exact Hr.
  Qed.
End PosRel.

Lemma RegionRelAt_custom :
  forall cp pp i r x (y : TS (implMemRegionTree r)), isCustomR r ->
    RegionRelAt cp pp i r x y <-> (i = cp \/ i = pp \/ x = y.(Fst)).
Proof.
  intros cp pp i r; unfold isCustomR, RegionRelAt, implMemRegionTree, memRegionTree.
  destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros x y Hc; [contradiction | reflexivity].
Qed.

(* --- 4. The Memory Relation after the Write --- *)

Section DevWriteMem.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation sRevR := (specRevRegion revBase revPfB revPfA).
  Local Abbreviation iRevR := (implRevRegion revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation MS := (TS (specMemTree specRegions)).
  Local Abbreviation MI := (TS (implRegionsTree implRegions)).
  Local Abbreviation MEMREL := (MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq).
  Local Abbreviation DEVINV := (DevInv pre post revBase revPfB revPfA clint plic).
  Local Abbreviation sClintA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation sPlicA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation iRevStA := (implRevState pre post revBase revPfB revPfA).

  (* What the write keeps or changes *)
  Definition DevWriteOK (ms ms' : MS) (mi mi' : MI) : Prop :=
    MEMREL ms' mi' /\ (DEVINV mi -> DEVINV mi') /\
    (forall initLine L, lineContent initLine specRegions ms' L = lineContent initLine specRegions ms L) /\
    FetchViewExt specRegions ms ms' /\ (forall fwcs, SnapshotOK fwcs specRegions ms -> SnapshotOK fwcs specRegions ms') /\
    (clintSampled (sClintA ms') = true -> clintSampled (sClintA ms) = true) /\
    (plicMeipOf (sPlicA ms') = true -> plicMeipOf (sPlicA ms) = true) /\
    (forall P, AllPorts P implRegions mi' = AllPorts P implRegions mi) /\
    revExtraOf (iRevStA mi') = revExtraOf (iRevStA mi) /\ revKeyOf (iRevStA mi') = revKeyOf (iRevStA mi).

  (* The spec memory's write of `w` may end in `ms'` *)
  Definition SpecWP (envS : Env (specMemTree specRegions)) (ms : MS) (w : type LineWriteRq) (ms' : MS) : Prop :=
    forall P, (forall v, P ms' v) -> evalActionPropGen envS (@specMemLineWrite type specRegions w) ms P.

  Lemma uniqS : forall L, lineUnique specRegions L.
  Proof. intros L; apply lineUnique_disjoint, Is_true_eq_true, Hdisj. Qed.

  Lemma uniqI : forall L, lineUnique implRegions L.
  Proof. intros L; apply lineUnique_implRegions, Is_true_eq_true, Hdisj. Qed.

  Lemma specWP_none : forall envS ms w, lineKind specRegions w.(Fst) = None -> SpecWP envS ms w ms.
  Proof.
    intros envS ms w Hk P HP.
    unfold specMemLineWrite, genRouteRegionUnitAction.
    apply ev_let_fwd; cbv beta.
    apply route_none_unit; [exact Hk | exact HP].
  Qed.

  Lemma specWP_at :
    forall envS ms j r (pf : nth_error specRegions j = Some r) w x' v,
      isRegionAddrB r w.(Fst) = true ->
      SemAction (envRegionAt memRegionTree j specRegions r pf envS ms) (@memRegionLineWrite r type w)
        (regionStateAt memRegionTree j specRegions r pf ms) x' v ->
      SpecWP envS ms w (updRegionStateAt memRegionTree j specRegions r pf ms x').
  Proof.
    intros envS ms j r pf w x' v Hm Hs P HP.
    unfold specMemLineWrite, genRouteRegionUnitAction.
    apply ev_let_fwd; cbv beta.
    apply (route_at_unit memRegionTree _ _ _ specRegions j r pf); [exact Hm | apply uniqS |].
    rewrite SemAction_iff_evalActionPropGen in Hs.
    eapply evalActionPropGen_mono; [| exact Hs].
    intros s r0 [-> _] w0; apply HP.
  Qed.

  Lemma DevWriteOK_refl : forall ms mi, MEMREL ms mi -> DevWriteOK ms ms mi mi.
  Proof.
    intros ms mi H.
    refine (conj H (conj (fun x => x) (conj (fun _ _ => eq_refl) (conj (FetchViewExt_refl _ _) (conj (fun _ x => x)
              (conj (fun x => x) (conj (fun x => x) (conj (fun _ => eq_refl) (conj eq_refl eq_refl))))))))).
  Qed.

  Lemma devWrite_none :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy,
      MEMREL ms mi -> lineKind implRegions w.(Fst) = None ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy Hrel Hk H.
    destruct (regionsWrite_none pre post revBase revPfB revPfA envI mi mi' rdy w Hk H) as [-> ->].
    split; [reflexivity |]; exists ms; split; [| exact (DevWriteOK_refl ms mi Hrel)].
    apply specWP_none; rewrite lineKind_revSwap; exact Hk.
  Qed.

  (* --- Device positions --- *)

  Lemma nth_impl_rev' : nth_error implRegions (length pre) = Some iRevR.
  Proof. exact (nth_error_app_cons_len pre iRevR post). Qed.
  Lemma nth_spec_rev' : nth_error specRegions (length pre) = Some sRevR.
  Proof. exact (nth_error_app_cons_len pre sRevR post). Qed.

  Lemma cI_rev : clintIdx clint <> length pre.
  Proof. intros E; pose proof (pfClint clint) as H; rewrite E, nth_impl_rev' in H; discriminate H. Qed.
  Lemma cS_rev : clintIdx clintS <> length pre.
  Proof. intros E; pose proof (pfClint clintS) as H; rewrite E, nth_spec_rev' in H; discriminate H. Qed.
  Lemma pI_rev : plicIdx plic <> length pre.
  Proof. intros E; pose proof (pfPlic plic) as H; rewrite E, nth_impl_rev' in H; discriminate H. Qed.
  Lemma pS_rev : plicIdx plicS <> length pre.
  Proof. intros E; pose proof (pfPlic plicS) as H; rewrite E, nth_spec_rev' in H; discriminate H. Qed.
  Lemma cI_pI : clintIdx clint <> plicIdx plic.
  Proof. intros E; pose proof (pfClint clint) as H1; pose proof (pfPlic plic) as H2; rewrite E, H2 in H1; discriminate H1. Qed.
  Lemma cS_pS : clintIdx clintS <> plicIdx plicS.
  Proof. intros E; pose proof (pfClint clintS) as H1; pose proof (pfPlic plicS) as H2; rewrite E, H2 in H1; discriminate H1. Qed.

  Lemma clintRegion_eq : clintRegion clintS = clintRegion clint.
  Proof.
    pose proof (pfClint clintS) as H1; pose proof (pfClint clint) as H2.
    rewrite HclintIdx in H2.
    assert (E : nth_error specRegions (clintIdx clintS) = nth_error implRegions (clintIdx clintS))
      by exact (nth_error_app_ne _ pre post sRevR iRevR _ cS_rev).
    rewrite E in H1.
    exact (f_equal (fun o => match o with Some x => x | None => clintRegion clintS end) (eq_trans (eq_sym H1) H2)).
  Qed.

  Lemma plicRegion_eq : regionBase (plicRegion plicS) = regionBase (plicRegion plic) /\
                        forall L, isRegionAddrB (plicRegion plicS) L = isRegionAddrB (plicRegion plic) L.
  Proof.
    pose proof (pfPlic plicS) as H1; pose proof (pfPlic plic) as H2.
    rewrite HplicIdx in H2.
    assert (E : nth_error specRegions (plicIdx plicS) = nth_error implRegions (plicIdx plicS))
      by exact (nth_error_app_ne _ pre post sRevR iRevR _ pS_rev).
    rewrite E in H1.
    pose proof (f_equal (fun o => match o with Some x => x | None => plicRegion plicS end) (eq_trans (eq_sym H1) H2)) as E2.
    cbv beta iota in E2.
    split; [exact (f_equal regionBase E2) | intros L; unfold plicRegion; rewrite E2; reflexivity].
  Qed.

  Lemma clintMem_write_sim2 :
    forall bI bS pbI paI pbS paS envI envS (xs xi xi' : TS (Node "clint" clintChildren)) (w : type LineWriteRq) v,
      bS = bI -> ClintRel xs xi ->
      SemAction envI (@memRegionLineWrite (@clintMemRegion bI pbI paI) type w) xi xi' v ->
      exists xs', SemAction envS (@memRegionLineWrite (@clintMemRegion bS pbS paS) type w) xs xs' v /\
        ClintRel xs' xi' /\ (clintSampled xs' = true -> clintSampled xs = true) /\ (ClintInv xi -> ClintInv xi').
  Proof. intros; subst; eapply clintMem_write_sim; eassumption. Qed.

  Lemma devWrite_clint :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy,
      MEMREL ms mi -> isRegionAddrB (clintRegion clint) w.(Fst) = true ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy Hrel Hm H.
    destruct (regionsWrite_at pre post revBase revPfB revPfA envI mi mi' rdy w (clintIdx clint) (clintRegion clint)
                (pfClint clint) Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomWrite_inv (clintRegion clint) _ _ _ _ _ I Hy) as [-> [_ [envX [v0 Hx]]]].
    split; [reflexivity |].
    destruct Hrel as [Hpre [Hcl [Hpl Hrv]]].
    unfold specClintState, implClintState in Hcl.
    pose proof clintRegion_eq as Ereg.
    destruct (clintMem_write_sim2 (clintBaseAddr clint) (clintBaseAddr clintS) _ _ (Clint.pfBound clintS) (Clint.pfAligned clintS)
                envX (envRegionAt memRegionTree (clintIdx clintS) specRegions (clintRegion clintS) (pfClint clintS) envS ms)
                _ _ _ w v0 (f_equal regionBase Ereg) Hcl Hx)
      as [xs' [Hs [Hcl' [Hsamp Hinv]]]].
    exists (updRegionStateAt memRegionTree (clintIdx clintS) specRegions (clintRegion clintS) (pfClint clintS) ms xs').
    split; [apply (specWP_at envS ms _ _ _ w xs' v0); [exact (eq_trans (f_equal (fun r => isRegionAddrB r w.(Fst)) Ereg) Hm) | exact Hs] |].
    unfold DevWriteOK, MemRel, DevInv, specClintState, implClintState, specPlicState, implPlicState,
      specRevState, implRevState in *.
    rewrite !regionStateAt_updRegionStateAt.
    rewrite !regionStateAt_upd_other by first [exact cI_pI | exact cI_rev | exact cS_pS | exact cS_rev].
    refine (conj (conj _ (conj Hcl' (conj Hpl Hrv))) (conj _ (conj _ (conj _ (conj _ (conj Hsamp
              (conj (fun x => x) (conj _ (conj eq_refl eq_refl))))))))).
    - exact (MemRelPre_upd2 (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
               (clintIdx clintS) (clintIdx clint) (clintRegion clintS) (clintRegion clint)
               (pfClint clintS) (pfClint clint) _ _ _ _ HclintIdx cS_rev (fun x y => or_introl eq_refl) Hpre).
    - intros [Hci Hpi]; exact (conj (Hinv Hci) Hpi).
    - intros initLine L; exact (lineContent_upd initLine specRegions _ _ _ ms xs' L I).
    - exact (FetchViewExt_upd specRegions _ _ _ ms xs' I).
    - intros fwcs Hs0; exact (SnapshotOK_upd specRegions fwcs _ _ _ ms xs' I Hs0).
    - intros P; apply AllPorts_upd; exact I.
  Qed.

  Lemma plicMem_write_sim2 :
    forall n1 n2 bI bS pbI paI pbS paS envI envS (xs : TS (plicTree n1)) (xi xi' : TS (plicTree n2)) (w : type LineWriteRq) v,
      bS = bI -> PlicRel n1 n2 xs xi ->
      SemAction envI (@memRegionLineWrite (@plicMemRegion n2 bI pbI paI) type w) xi xi' v ->
      exists xs', SemAction envS (@memRegionLineWrite (@plicMemRegion n1 bS pbS paS) type w) xs xs' v /\
        PlicRel n1 n2 xs' xi' /\ (plicMeipOf xs' = true -> plicMeipOf xs = true) /\ (PlicInv xi -> PlicInv xi').
  Proof. intros; subst; eapply plicMem_write_sim; eassumption. Qed.

  Lemma devWrite_plic :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy,
      MEMREL ms mi -> isRegionAddrB (plicRegion plic) w.(Fst) = true ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy Hrel Hm H.
    destruct (regionsWrite_at pre post revBase revPfB revPfA envI mi mi' rdy w (plicIdx plic) (plicRegion plic)
                (pfPlic plic) Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomWrite_inv (plicRegion plic) _ _ _ _ _ I Hy) as [-> [_ [envX [v0 Hx]]]].
    split; [reflexivity |].
    destruct Hrel as [Hpre [Hcl [Hpl Hrv]]].
    unfold specPlicState, implPlicState in Hpl.
    destruct plicRegion_eq as [Eb Ea].
    destruct (plicMem_write_sim2 _ _ (plicBaseAddr plic) (plicBaseAddr plicS) _ _ (Plic.pfBound plicS) (Plic.pfAligned plicS)
                envX (envRegionAt memRegionTree (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS) envS ms)
                _ _ _ w v0 Eb Hpl Hx)
      as [xs' [Hs [Hpl' [Hmeip Hinv]]]].
    exists (updRegionStateAt memRegionTree (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS) ms xs').
    split; [apply (specWP_at envS ms _ _ _ w xs' v0); [exact (eq_trans (Ea w.(Fst)) Hm) | exact Hs] |].
    unfold DevWriteOK, MemRel, DevInv, specClintState, implClintState, specPlicState, implPlicState,
      specRevState, implRevState in *.
    rewrite !regionStateAt_updRegionStateAt.
    rewrite !regionStateAt_upd_other
      by first [exact (not_eq_sym cI_pI) | exact pI_rev | exact (not_eq_sym cS_pS) | exact pS_rev].
    refine (conj (conj _ (conj Hcl (conj Hpl' Hrv))) (conj _ (conj _ (conj _ (conj _ (conj (fun x => x)
              (conj Hmeip (conj _ (conj eq_refl eq_refl))))))))).
    - exact (MemRelPre_upd2 (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
               (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
               (pfPlic plicS) (pfPlic plic) _ _ _ _ HplicIdx pS_rev (fun x y => or_intror (or_introl eq_refl)) Hpre).
    - intros [Hci Hpi]; exact (conj Hci (Hinv Hpi)).
    - intros initLine L; exact (lineContent_upd initLine specRegions _ _ _ ms xs' L I).
    - exact (FetchViewExt_upd specRegions _ _ _ ms xs' I).
    - intros fwcs Hs0; exact (SnapshotOK_upd specRegions fwcs _ _ _ ms xs' I Hs0).
    - intros P; apply AllPorts_upd; exact I.
  Qed.

  Lemma devWrite_rev :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy,
      MEMREL ms mi -> isRegionAddrB iRevR w.(Fst) = true ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy Hrel Hm H.
    destruct (regionsWrite_at pre post revBase revPfB revPfA envI mi mi' rdy w (length pre) iRevR
                (nth_error_app_cons_len pre iRevR post) Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomWrite_inv iRevR _ _ _ _ _ I Hy) as [-> [_ [envX [v0 Hx]]]].
    split; [reflexivity |].
    destruct Hrel as [Hpre [Hcl [Hpl Hrv]]].
    unfold specRevState, implRevState in Hrv.
    destruct (revMem_write_sim revBase revPfB revPfA envX
                (envRegionAt memRegionTree (length pre) specRegions sRevR (nth_error_app_cons_len pre sRevR post) envS ms)
                _ _ _ w v0 Hrv Hx) as [Hs [Hrv' [Ee Ek]]].
    exists (updRegionStateAt memRegionTree (length pre) specRegions sRevR (nth_error_app_cons_len pre sRevR post) ms
              (projImplRevokerArchState y'.(Fst))).
    split; [apply (specWP_at envS ms _ _ _ w _ v0); [exact Hm | exact Hs] |].
    unfold DevWriteOK, MemRel, DevInv, specClintState, implClintState, specPlicState, implPlicState,
      specRevState, implRevState in *.
    rewrite !regionStateAt_updRegionStateAt.
    rewrite !regionStateAt_upd_other
      by first [exact (not_eq_sym cI_rev) | exact (not_eq_sym pI_rev) | exact (not_eq_sym cS_rev) | exact (not_eq_sym pS_rev)].
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv'))) (conj (fun x => x) (conj _ (conj _ (conj _ (conj (fun x => x)
              (conj (fun x => x) (conj _ (conj Ee Ek))))))))).
    - exact (MemRelPre_upd_rev_spec _ _ _ _ _ pre 0 _ _ _ (MemRelPre_upd_rev_impl _ _ _ _ _ pre 0 _ _ _ Hpre)).
    - intros initLine L; exact (lineContent_upd initLine specRegions (length pre) sRevR (nth_error_app_cons_len pre sRevR post) ms _ L I).
    - exact (FetchViewExt_upd specRegions (length pre) sRevR (nth_error_app_cons_len pre sRevR post) ms _ I).
    - intros fwcs Hs0; exact (SnapshotOK_upd specRegions fwcs (length pre) sRevR (nth_error_app_cons_len pre sRevR post) ms _ I Hs0).
    - intros P; apply AllPorts_upd; exact I.
  Qed.

  (* An ordinary CustomMem position: equal states on both sides, the spec env accepts anything *)
  Lemma devWrite_ord_gen :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy idx r
           (pfS : nth_error specRegions idx = Some r) (pfI : nth_error implRegions idx = Some r),
      MEMREL ms mi -> isRegionAddrB r w.(Fst) = true -> isCustomR r ->
      idx <> length pre -> idx <> clintIdx clintS -> idx <> plicIdx plicS ->
      RegionRelAt (clintIdx clintS) (plicIdx plicS) idx r (regionStateAt memRegionTree idx specRegions r pfS ms)
        (regionStateAt implMemRegionTree idx implRegions r pfI mi) ->
      (forall v y, RegionRelAt (clintIdx clintS) (plicIdx plicS) idx r v y ->
         MemRelPre (clintIdx clintS) (plicIdx plicS) 0 pre sRevR iRevR post
           (updRegionStateAt memRegionTree idx specRegions r pfS ms v) (updRegionStateAt implMemRegionTree idx implRegions r pfI mi y)) ->
      EnvCustomTrue specRegions envS ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy idx r pfS pfI Hrel Hm Hc Hnr Hnc Hnp Hat Hupd Henv H.
    destruct (regionsWrite_at pre post revBase revPfB revPfA envI mi mi' rdy w idx r pfI Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomWrite_inv r _ _ _ _ _ Hc Hy) as [-> [_ [envX [v0 Hx]]]].
    split; [reflexivity |].
    destruct (proj1 (RegionRelAt_custom _ _ _ _ _ _ Hc) Hat) as [E | [E | Ex]]; [contradiction | contradiction |].
    assert (Hs : SemAction (envRegionAt memRegionTree idx specRegions r pfS envS ms) (@memRegionLineWrite r type w)
                   (regionStateAt memRegionTree idx specRegions r pfS ms) y'.(Fst) v0).
    { rewrite Ex; apply (SemAction_env_mono envX); [| exact Hx].
      intros s0 x0 v1 _; exact (envRegionAt_customTrue specRegions idx r pfS envS ms Henv Hc s0 x0 v1). }
    exists (updRegionStateAt memRegionTree idx specRegions r pfS ms y'.(Fst)).
    split; [exact (specWP_at envS ms idx r pfS w _ v0 Hm Hs) |].
    destruct Hrel as [Hpre [Hcl [Hpl Hrv]]].
    assert (HnrS : idx <> length pre) by exact Hnr.
    assert (HncI : idx <> clintIdx clint) by (rewrite HclintIdx; exact Hnc).
    assert (HnpI : idx <> plicIdx plic) by (rewrite HplicIdx; exact Hnp).
    unfold DevWriteOK, MemRel, DevInv, specClintState, implClintState, specPlicState, implPlicState,
      specRevState, implRevState in *.
    rewrite !regionStateAt_upd_other by first [exact HncI | exact HnpI | exact Hnr | exact Hnc | exact Hnp].
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (fun x => x) (conj _ (conj _ (conj _ (conj (fun x => x)
              (conj (fun x => x) (conj _ (conj eq_refl eq_refl))))))))).
    - apply Hupd; apply (proj2 (RegionRelAt_custom _ _ _ _ _ _ Hc)); right; right; reflexivity.
    - intros initLine L; exact (lineContent_upd initLine specRegions _ _ _ ms _ L Hc).
    - exact (FetchViewExt_upd specRegions _ _ _ ms _ Hc).
    - intros fwcs Hs0; exact (SnapshotOK_upd specRegions fwcs _ _ _ ms _ Hc Hs0).
    - intros P; apply AllPorts_upd; exact Hc.
  Qed.

  Lemma nth_error_lt : forall (A : Type) (l : list A) k r, nth_error l k = Some r -> (k < length l)%nat.
  Proof. intros A l k r H; apply nth_error_Some; rewrite H; discriminate. Qed.

  Lemma devWrite_ord :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy j r (pf : nth_error implRegions j = Some r),
      MEMREL ms mi -> isRegionAddrB r w.(Fst) = true -> isCustomR r ->
      isRegionAddrB (clintRegion clint) w.(Fst) = false -> isRegionAddrB (plicRegion plic) w.(Fst) = false ->
      isRegionAddrB iRevR w.(Fst) = false ->
      EnvCustomTrue specRegions envS ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy j r pf Hrel Hm Hc Hcl Hpl Hrv Henv H.
    assert (Hnc : forall k, nth_error implRegions k = Some r -> k <> clintIdx clintS).
    { intros k Hk E; rewrite <- HclintIdx in E; subst k.
      rewrite (pfClint clint) in Hk; injection Hk as <-; unfold clintRegion in Hcl; rewrite Hm in Hcl; discriminate Hcl. }
    assert (Hnp : forall k, nth_error implRegions k = Some r -> k <> plicIdx plicS).
    { intros k Hk E; rewrite <- HplicIdx in E; subst k.
      rewrite (pfPlic plic) in Hk; injection Hk as <-; unfold plicRegion in Hpl; rewrite Hm in Hpl; discriminate Hpl. }
    pose proof (proj1 Hrel) as Hpre.
    destruct (nth_error_app_split _ pre post iRevR j r pf) as [[k [pfp ->]] | [[-> ->] | [k [pfp ->]]]].
    - pose proof (nth_error_lt _ _ _ _ pfp) as Hlt.
      apply (devWrite_ord_gen envI envS ms mi mi' w rdy k r (nth_pre_pf pre sRevR post k r pfp) (nth_pre_pf pre iRevR post k r pfp)
               Hrel Hm Hc); try lia.
      + exact (Hnc k (nth_pre_pf pre iRevR post k r pfp)).
      + exact (Hnp k (nth_pre_pf pre iRevR post k r pfp)).
      + exact (MemRelPre_at_pre _ _ sRevR iRevR post pre 0 k r pfp ms mi Hpre).
      + intros v y Hr; exact (MemRelPre_upd_pre _ _ sRevR iRevR post pre 0 k r pfp ms mi v y Hr Hpre).
      + exact Henv.
      + exact H.
    - rewrite Hm in Hrv; discriminate Hrv.
    - apply (devWrite_ord_gen envI envS ms mi mi' w rdy _ r (nth_post_pf pre sRevR post k r pfp) (nth_post_pf pre iRevR post k r pfp)
               Hrel Hm Hc); try lia.
      + exact (Hnc _ (nth_post_pf pre iRevR post k r pfp)).
      + exact (Hnp _ (nth_post_pf pre iRevR post k r pfp)).
      + exact (MemRelPre_at_post _ _ sRevR iRevR post pre 0 k r pfp ms mi Hpre).
      + intros v y Hr; exact (MemRelPre_upd_post _ _ sRevR iRevR post pre 0 k r pfp ms mi v y Hr Hpre).
      + exact Henv.
      + exact H.
  Qed.

  (* The write of a line that is not ExternalMem *)
  Theorem devWrite_mem :
    forall envI envS (ms : MS) (mi mi' : MI) (w : type LineWriteRq) rdy,
      MEMREL ms mi -> lineKind implRegions w.(Fst) <> Some true -> EnvCustomTrue specRegions envS ->
      SemAction envI (@implRegionsLineWriteRq type implRegions w) mi mi' rdy ->
      rdy = true /\ exists ms', SpecWP envS ms w ms' /\ DevWriteOK ms ms' mi mi'.
  Proof.
    intros envI envS ms mi mi' w rdy Hrel Hk Henv H.
    destruct (lineKind implRegions w.(Fst)) as [[|] |] eqn:Hk'; [contradiction | | exact (devWrite_none envI envS ms mi mi' w rdy Hrel Hk' H)].
    destruct (isRegionAddrB (clintRegion clint) w.(Fst)) eqn:Ec; [exact (devWrite_clint envI envS ms mi mi' w rdy Hrel Ec H) |].
    destruct (isRegionAddrB (plicRegion plic) w.(Fst)) eqn:Ep; [exact (devWrite_plic envI envS ms mi mi' w rdy Hrel Ep H) |].
    destruct (isRegionAddrB iRevR w.(Fst)) eqn:Er; [exact (devWrite_rev envI envS ms mi mi' w rdy Hrel Er H) |].
    destruct (lineKind_custom_at _ _ Hk') as [j [r [pf [Hm Hc]]]].
    exact (devWrite_ord envI envS ms mi mi' w rdy j r pf Hrel Hm Hc Ec Ep Er Henv H).
  Qed.

  (* --- Reads --- *)

  (* The spec memory's read of line `L` may end in `ms'` and answer `rpv` *)
  Definition SpecRP (envS : Env (specMemTree specRegions)) (ms : MS) (L : type Addr) (mask : type (Array LineBytes Bool))
    (ms' : MS) (rpv : type LineReadRp) : Prop :=
    forall P, P ms' rpv -> evalActionPropGen envS (@specMemLineRead type specRegions L mask) ms P.

  Lemma specRP_none : forall envS ms L mask, lineKind specRegions L = None -> SpecRP envS ms L mask ms (getDefault LineReadRp).
  Proof.
    intros envS ms L mask Hk P HP.
    unfold specMemLineRead, genRouteRegionAction.
    apply (proj2 (route_none_or memRegionTree LineReadRp _ L specRegions [] envS ms P Hk)).
    exact HP.
  Qed.

  Lemma specRP_at :
    forall envS ms j r (pf : nth_error specRegions j = Some r) L mask x' v,
      isRegionAddrB r L = true ->
      SemAction (envRegionAt memRegionTree j specRegions r pf envS ms) (@memRegionLineRead r type L mask)
        (regionStateAt memRegionTree j specRegions r pf ms) x' v ->
      SpecRP envS ms L mask (updRegionStateAt memRegionTree j specRegions r pf ms x') v.
  Proof.
    intros envS ms j r pf L mask x' v Hm Hs P HP.
    unfold specMemLineRead, genRouteRegionAction.
    apply (proj2 (route_at_or memRegionTree LineReadRp _ L specRegions j r pf [] envS ms P Hm (uniqS L) (Forall_nil _))).
    rewrite SemAction_iff_evalActionPropGen in Hs.
    eapply evalActionPropGen_mono; [| exact Hs].
    intros s0 r0 [-> ->]; exact HP.
  Qed.

  Local Abbreviation ReadOK envS ms mi mi' L mask res :=
    (exists ms' rpv, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\ SpecRP envS ms L mask ms' rpv /\ DevWriteOK ms ms' mi mi' /\
                     exists d, rpv = rpOfData d).

  Lemma devRead_none :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res,
      MEMREL ms mi -> lineKind implRegions L = None ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res -> ReadOK envS ms mi mi' L mask res.
  Proof.
    intros envI envS ms mi mi' L mask res Hrel Hk H.
    destruct (regionsRead_none pre post revBase revPfB revPfA envI mi mi' res L mask Hk H) as [-> ->].
    exists ms, (getDefault LineReadRp); split; [reflexivity | split; [| split; [exact (DevWriteOK_refl ms mi Hrel) | exists (getDefault _); reflexivity]]].
    apply specRP_none; rewrite lineKind_revSwap; exact Hk.
  Qed.

  Lemma devRead_clint :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res,
      MEMREL ms mi -> isRegionAddrB (clintRegion clint) L = true ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res -> ReadOK envS ms mi mi' L mask res.
  Proof.
    intros envI envS ms mi mi' L mask res Hrel Hm H.
    destruct (regionsRead_at pre post revBase revPfB revPfA envI mi mi' res L mask (clintIdx clint) (clintRegion clint)
                (pfClint clint) Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomRead_inv (clintRegion clint) _ _ _ _ _ _ I Hy) as [Ey [envX [v [Hx [-> Hd]]]]].
    pose proof Hrel as Hrel0; destruct Hrel0 as [Hpre [Hcl [Hpl Hrv]]].
    unfold specClintState, implClintState in Hcl.
    pose proof clintRegion_eq as Ereg.
    destruct (clintMem_read_sim (clintBaseAddr clint) (clintBaseAddr clintS) _ _ (Clint.pfBound clintS) (Clint.pfAligned clintS)
                envX (envRegionAt memRegionTree (clintIdx clintS) specRegions (clintRegion clintS) (pfClint clintS) envS ms)
                _ _ _ L mask v (f_equal regionBase Ereg) Hcl Hx) as [Exi Hs].
    assert (Ey' : y' = regionStateAt implMemRegionTree (clintIdx clint) implRegions (clintRegion clint) (pfClint clint) mi)
      by (apply prod_ext; [exact Exi | exact Ey]).
    rewrite Ey', updRegionStateAt_regionStateAt.
    exists ms, v; split; [reflexivity | split; [| split; [exact (DevWriteOK_refl ms mi Hrel) | exact Hd]]].
    intros P HP.
    apply (specRP_at envS ms _ _ _ L mask _ v (eq_trans (f_equal (fun r => isRegionAddrB r L) Ereg) Hm) Hs).
    rewrite updRegionStateAt_regionStateAt; exact HP.
  Qed.

  Lemma devRead_plic :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res,
      MEMREL ms mi -> isRegionAddrB (plicRegion plic) L = true ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res -> ReadOK envS ms mi mi' L mask res.
  Proof.
    intros envI envS ms mi mi' L mask res Hrel Hm H.
    destruct (regionsRead_at pre post revBase revPfB revPfA envI mi mi' res L mask (plicIdx plic) (plicRegion plic)
                (pfPlic plic) Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomRead_inv (plicRegion plic) _ _ _ _ _ _ I Hy) as [_ [envX [v [Hx [-> Hd]]]]].
    destruct Hrel as [Hpre [Hcl [Hpl Hrv]]].
    unfold specPlicState, implPlicState in Hpl.
    destruct plicRegion_eq as [Eb Ea].
    destruct (plicMem_read_sim _ _ (plicBaseAddr plic) (plicBaseAddr plicS) _ _ (Plic.pfBound plicS) (Plic.pfAligned plicS)
                envX (envRegionAt memRegionTree (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS) envS ms)
                _ _ _ L mask v Eb Hpl Hx)
      as [xs' [Hs [Hpl' [Hmeip Hinv]]]].
    exists (updRegionStateAt memRegionTree (plicIdx plicS) specRegions (plicRegion plicS) (pfPlic plicS) ms xs'), v.
    split; [reflexivity |].
    split; [exact (specRP_at envS ms _ _ _ L mask xs' v (eq_trans (Ea L) Hm) Hs) |].
    split; [| exact Hd].
    unfold DevWriteOK, MemRel, DevInv, specClintState, implClintState, specPlicState, implPlicState,
      specRevState, implRevState in *.
    rewrite !regionStateAt_updRegionStateAt.
    rewrite !regionStateAt_upd_other
      by first [exact (not_eq_sym cI_pI) | exact pI_rev | exact (not_eq_sym cS_pS) | exact pS_rev].
    refine (conj (conj _ (conj Hcl (conj Hpl' Hrv))) (conj _ (conj _ (conj _ (conj _ (conj (fun x => x)
              (conj Hmeip (conj _ (conj eq_refl eq_refl))))))))).
    - exact (MemRelPre_upd2 (clintIdx clintS) (plicIdx plicS) sRevR iRevR post pre 0
               (plicIdx plicS) (plicIdx plic) (plicRegion plicS) (plicRegion plic)
               (pfPlic plicS) (pfPlic plic) _ _ _ _ HplicIdx pS_rev (fun x y => or_intror (or_introl eq_refl)) Hpre).
    - intros [Hci Hpi]; exact (conj Hci (Hinv Hpi)).
    - intros initLine L0; exact (lineContent_upd initLine specRegions _ _ _ ms xs' L0 I).
    - exact (FetchViewExt_upd specRegions _ _ _ ms xs' I).
    - intros fwcs Hs0; exact (SnapshotOK_upd specRegions fwcs _ _ _ ms xs' I Hs0).
    - intros P; apply AllPorts_upd; exact I.
  Qed.

  Lemma devRead_rev :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res,
      MEMREL ms mi -> isRegionAddrB iRevR L = true ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res -> ReadOK envS ms mi mi' L mask res.
  Proof.
    intros envI envS ms mi mi' L mask res Hrel Hm H.
    destruct (regionsRead_at pre post revBase revPfB revPfA envI mi mi' res L mask (length pre) iRevR
                (nth_error_app_cons_len pre iRevR post) Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomRead_inv iRevR _ _ _ _ _ _ I Hy) as [Ey [envX [v [Hx [-> Hd]]]]].
    pose proof Hrel as Hrel0; destruct Hrel0 as [Hpre [Hcl [Hpl Hrv]]].
    unfold specRevState, implRevState in Hrv.
    destruct (revMem_read_sim revBase revPfB revPfA envX
                (envRegionAt memRegionTree (length pre) specRegions sRevR (nth_error_app_cons_len pre sRevR post) envS ms)
                _ _ _ L mask v Hrv Hx) as [Exi Hs].
    assert (Ey' : y' = regionStateAt implMemRegionTree (length pre) implRegions iRevR (nth_error_app_cons_len pre iRevR post) mi)
      by (apply prod_ext; [exact Exi | exact Ey]).
    rewrite Ey', updRegionStateAt_regionStateAt.
    exists ms, v; split; [reflexivity | split; [| split; [exact (DevWriteOK_refl ms mi Hrel) | exact Hd]]].
    intros P HP.
    apply (specRP_at envS ms (length pre) sRevR (nth_error_app_cons_len pre sRevR post) L mask _ v Hm Hs).
    rewrite updRegionStateAt_regionStateAt; exact HP.
  Qed.

  Lemma devRead_ord_gen :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res idx r
           (pfS : nth_error specRegions idx = Some r) (pfI : nth_error implRegions idx = Some r),
      MEMREL ms mi -> isRegionAddrB r L = true -> isCustomR r ->
      idx <> length pre -> idx <> clintIdx clintS -> idx <> plicIdx plicS ->
      RegionRelAt (clintIdx clintS) (plicIdx plicS) idx r (regionStateAt memRegionTree idx specRegions r pfS ms)
        (regionStateAt implMemRegionTree idx implRegions r pfI mi) ->
      (forall v y, RegionRelAt (clintIdx clintS) (plicIdx plicS) idx r v y ->
         MemRelPre (clintIdx clintS) (plicIdx plicS) 0 pre sRevR iRevR post
           (updRegionStateAt memRegionTree idx specRegions r pfS ms v) (updRegionStateAt implMemRegionTree idx implRegions r pfI mi y)) ->
      EnvCustomTrue specRegions envS ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res -> ReadOK envS ms mi mi' L mask res.
  Proof.
    intros envI envS ms mi mi' L mask res idx r pfS pfI Hrel Hm Hc Hnr Hnc Hnp Hat Hupd Henv H.
    destruct (regionsRead_at pre post revBase revPfB revPfA envI mi mi' res L mask idx r pfI Hm (uniqI _) H) as [y' [Hy ->]].
    destruct (implCustomRead_inv r _ _ _ _ _ _ Hc Hy) as [_ [envX [v [Hx [-> Hd]]]]].
    destruct (proj1 (RegionRelAt_custom _ _ _ _ _ _ Hc) Hat) as [E | [E | Ex]]; [contradiction | contradiction |].
    assert (Hs : SemAction (envRegionAt memRegionTree idx specRegions r pfS envS ms) (@memRegionLineRead r type L mask)
                   (regionStateAt memRegionTree idx specRegions r pfS ms) y'.(Fst) v).
    { rewrite Ex; apply (SemAction_env_mono envX); [| exact Hx].
      intros s0 x0 v1 _; exact (envRegionAt_customTrue specRegions idx r pfS envS ms Henv Hc s0 x0 v1). }
    exists (updRegionStateAt memRegionTree idx specRegions r pfS ms y'.(Fst)), v.
    split; [reflexivity |].
    split; [exact (specRP_at envS ms idx r pfS L mask _ v Hm Hs) |].
    split; [| exact Hd].
    destruct Hrel as [Hpre [Hcl [Hpl Hrv]]].
    assert (HncI : idx <> clintIdx clint) by (rewrite HclintIdx; exact Hnc).
    assert (HnpI : idx <> plicIdx plic) by (rewrite HplicIdx; exact Hnp).
    unfold DevWriteOK, MemRel, DevInv, specClintState, implClintState, specPlicState, implPlicState,
      specRevState, implRevState in *.
    rewrite !regionStateAt_upd_other by first [exact HncI | exact HnpI | exact Hnr | exact Hnc | exact Hnp].
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (fun x => x) (conj _ (conj _ (conj _ (conj (fun x => x)
              (conj (fun x => x) (conj _ (conj eq_refl eq_refl))))))))).
    - apply Hupd; apply (proj2 (RegionRelAt_custom _ _ _ _ _ _ Hc)); right; right; reflexivity.
    - intros initLine L0; exact (lineContent_upd initLine specRegions _ _ _ ms _ L0 Hc).
    - exact (FetchViewExt_upd specRegions _ _ _ ms _ Hc).
    - intros fwcs Hs0; exact (SnapshotOK_upd specRegions fwcs _ _ _ ms _ Hc Hs0).
    - intros P; apply AllPorts_upd; exact Hc.
  Qed.

  Lemma devRead_ord :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res j r (pf : nth_error implRegions j = Some r),
      MEMREL ms mi -> isRegionAddrB r L = true -> isCustomR r ->
      isRegionAddrB (clintRegion clint) L = false -> isRegionAddrB (plicRegion plic) L = false ->
      isRegionAddrB iRevR L = false -> EnvCustomTrue specRegions envS ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res -> ReadOK envS ms mi mi' L mask res.
  Proof.
    intros envI envS ms mi mi' L mask res j r pf Hrel Hm Hc Hcl Hpl Hrv Henv H.
    assert (Hnc : forall k, nth_error implRegions k = Some r -> k <> clintIdx clintS).
    { intros k Hk E; rewrite <- HclintIdx in E; subst k.
      rewrite (pfClint clint) in Hk; injection Hk as <-; unfold clintRegion in Hcl; rewrite Hm in Hcl; discriminate Hcl. }
    assert (Hnp : forall k, nth_error implRegions k = Some r -> k <> plicIdx plicS).
    { intros k Hk E; rewrite <- HplicIdx in E; subst k.
      rewrite (pfPlic plic) in Hk; injection Hk as <-; unfold plicRegion in Hpl; rewrite Hm in Hpl; discriminate Hpl. }
    pose proof (proj1 Hrel) as Hpre.
    destruct (nth_error_app_split _ pre post iRevR j r pf) as [[k [pfp ->]] | [[-> ->] | [k [pfp ->]]]].
    - pose proof (nth_error_lt _ _ _ _ pfp) as Hlt.
      apply (devRead_ord_gen envI envS ms mi mi' L mask res k r (nth_pre_pf pre sRevR post k r pfp) (nth_pre_pf pre iRevR post k r pfp)
               Hrel Hm Hc); try lia.
      + exact (Hnc k (nth_pre_pf pre iRevR post k r pfp)).
      + exact (Hnp k (nth_pre_pf pre iRevR post k r pfp)).
      + exact (MemRelPre_at_pre _ _ sRevR iRevR post pre 0 k r pfp ms mi Hpre).
      + intros v y Hr; exact (MemRelPre_upd_pre _ _ sRevR iRevR post pre 0 k r pfp ms mi v y Hr Hpre).
      + exact Henv.
      + exact H.
    - rewrite Hm in Hrv; discriminate Hrv.
    - apply (devRead_ord_gen envI envS ms mi mi' L mask res _ r (nth_post_pf pre sRevR post k r pfp) (nth_post_pf pre iRevR post k r pfp)
               Hrel Hm Hc); try lia.
      + exact (Hnc _ (nth_post_pf pre iRevR post k r pfp)).
      + exact (Hnp _ (nth_post_pf pre iRevR post k r pfp)).
      + exact (MemRelPre_at_post _ _ sRevR iRevR post pre 0 k r pfp ms mi Hpre).
      + intros v y Hr; exact (MemRelPre_upd_post _ _ sRevR iRevR post pre 0 k r pfp ms mi v y Hr Hpre).
      + exact Henv.
      + exact H.
  Qed.

  (* The read of a line that is not ExternalMem *)
  Theorem devRead_mem :
    forall envI envS (ms : MS) (mi mi' : MI) (L : type Addr) mask res,
      MEMREL ms mi -> lineKind implRegions L <> Some true -> EnvCustomTrue specRegions envS ->
      SemAction envI (@implRegionsLineReadRq type implRegions L mask) mi mi' res ->
      exists ms' rpv, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\ SpecRP envS ms L mask ms' rpv /\ DevWriteOK ms ms' mi mi' /\
                      exists d, rpv = rpOfData d.
  Proof.
    intros envI envS ms mi mi' L mask res Hrel Hk Henv H.
    destruct (lineKind implRegions L) as [[|] |] eqn:Hk'; [contradiction | | exact (devRead_none envI envS ms mi mi' L mask res Hrel Hk' H)].
    destruct (isRegionAddrB (clintRegion clint) L) eqn:Ec; [exact (devRead_clint envI envS ms mi mi' L mask res Hrel Ec H) |].
    destruct (isRegionAddrB (plicRegion plic) L) eqn:Ep; [exact (devRead_plic envI envS ms mi mi' L mask res Hrel Ep H) |].
    destruct (isRegionAddrB iRevR L) eqn:Er; [exact (devRead_rev envI envS ms mi mi' L mask res Hrel Er H) |].
    destruct (lineKind_custom_at _ _ Hk') as [j [r [pf [Hm Hc]]]].
    exact (devRead_ord envI envS ms mi mi' L mask res j r pf Hrel Hm Hc Ec Ep Er Henv H).
  Qed.
End DevWriteMem.
