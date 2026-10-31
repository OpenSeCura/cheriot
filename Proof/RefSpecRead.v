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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * A DATA READ OF THE SPEC MEMORY
 * ===========================================================================
 * The spec reads a line through the region router, which ORs the answers of the regions
 * holding the line. When the line is in exactly one region, an ExternalMem one:
 * 1. the read changes only the data-read traces of the ExternalMem regions (`ReadFrameS`),
 *    which none of the relations read;
 * 2. the read returns the line content (`specMemLineRead_wp`, `specMemRead_wp`);
 * 3. a line is in at most one region when the regions are pairwise disjoint
 *    (`lineUnique_disjoint`). *)

Local Abbreviation TS t := (TreeState DomainElemState t).

(* --- 1. Data Reads Change Only the Data-Read Traces --- *)

Section ReadFrame.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  (* An ExternalMem region keeps its fetch part and its write trace; a CustomMem region is
   * unchanged *)
  Definition RegionReadFrame (r : MemRegion) : TS (memRegionTree core r) -> TS (memRegionTree core r) -> Prop :=
    match r.(regionKind) as k return TS (memRegionKindTree core r k) -> TS (memRegionKindTree core r k) -> Prop with
    | ExternalMem => fun x x' => x'.(Fst) = x.(Fst) /\ x'.(Snd).(Snd).(Snd) = x.(Snd).(Snd).(Snd)
    | CustomMem _ _ _ _ => fun x x' => x' = x
    end.

  Fixpoint ReadFrameS (l : list MemRegion) : TS (specMemTree core l) -> TS (specMemTree core l) -> Prop :=
    match l as l0 return TS (specMemTree core l0) -> TS (specMemTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun ms ms' => RegionReadFrame r ms.(Fst) ms'.(Fst) /\ ReadFrameS rs ms.(Snd).(Fst) ms'.(Snd).(Fst)
    end.

  Lemma RegionReadFrame_refl : forall r x, RegionReadFrame r x x.
  Proof. intros r; unfold RegionReadFrame, memRegionTree; destruct (regionKind r); intros x; [split |]; reflexivity. Qed.

  Lemma ReadFrameS_refl : forall l ms, ReadFrameS l ms ms.
  Proof.
    induction l as [| r rs IH]; intros ms; cbn [ReadFrameS]; [exact I | split; [apply RegionReadFrame_refl | apply IH]].
  Qed.

  Lemma RegionReadFrame_trans :
    forall r x y z, RegionReadFrame r x y -> RegionReadFrame r y z -> RegionReadFrame r x z.
  Proof.
    intros r; unfold RegionReadFrame, memRegionTree; destruct (regionKind r); intros x y z H1 H2.
    - destruct H1 as [A1 B1], H2 as [A2 B2]; split; congruence.
    - congruence.
  Qed.

  Lemma ReadFrameS_trans : forall l x y z, ReadFrameS l x y -> ReadFrameS l y z -> ReadFrameS l x z.
  Proof.
    induction l as [| r rs IH]; intros x y z H1 H2; cbn [ReadFrameS] in *; [exact I |].
    destruct H1 as [A1 B1], H2 as [A2 B2].
    split; [exact (RegionReadFrame_trans r _ _ _ A1 A2) | exact (IH _ _ _ B1 B2)].
  Qed.

  Lemma RegionReadFrame_custom : forall r, isCustomR r -> forall x x', RegionReadFrame r x x' -> x' = x.
  Proof.
    intros r; unfold RegionReadFrame, isCustomR, memRegionTree; destruct (regionKind r); intros Hc x x' H;
      [contradiction | exact H].
  Qed.

  Lemma RegionLineContent_readFrame :
    forall r x x' L, RegionReadFrame r x x' -> RegionLineContent core initLine r x' L = RegionLineContent core initLine r x L.
  Proof.
    intros r; unfold RegionReadFrame, RegionLineContent, memRegionTree; destruct (regionKind r); intros x x' L H.
    - destruct H as [_ H]; rewrite H; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma lineContent_readFrame :
    forall l ms ms', ReadFrameS l ms ms' -> forall L, lineContent core initLine l ms' L = lineContent core initLine l ms L.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H L; cbn [ReadFrameS lineContent] in *; [reflexivity |].
    destruct H as [H0 H1].
    rewrite (RegionLineContent_readFrame r _ _ L H0), (IH _ _ H1); reflexivity.
  Qed.

  Lemma RegionFetchViewExt_readFrame : forall r x x', RegionReadFrame r x x' -> RegionFetchViewExt core r x x'.
  Proof.
    intros r; unfold RegionReadFrame, RegionFetchViewExt, memRegionTree; destruct (regionKind r); intros x x' H.
    - destruct H as [H0 H1]; rewrite H0; split; [reflexivity |].
      exists []; rewrite H1; reflexivity.
    - exact I.
  Qed.

  Lemma FetchViewExt_readFrame : forall l ms ms', ReadFrameS l ms ms' -> FetchViewExt core l ms ms'.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H; cbn [ReadFrameS FetchViewExt] in *; [exact I |].
    destruct H as [H0 H1]; split; [exact (RegionFetchViewExt_readFrame r _ _ H0) | exact (IH _ _ H1)].
  Qed.

  Lemma RegionSnapshotOK_readFrame :
    forall r fwc x x', RegionReadFrame r x x' -> RegionSnapshotOK core r fwc x -> RegionSnapshotOK core r fwc x'.
  Proof.
    intros r fwc; unfold RegionReadFrame, RegionSnapshotOK, memRegionTree; destruct (regionKind r); intros x x' H Hs.
    - destruct H as [H0 H1]; rewrite H0, H1; exact Hs.
    - exact I.
  Qed.

  Lemma SnapshotOK_readFrame :
    forall l fwcs ms ms', ReadFrameS l ms ms' -> SnapshotOK core fwcs l ms -> SnapshotOK core fwcs l ms'.
  Proof.
    induction l as [| r rs IH]; intros fwcs ms ms' H Hs; cbn [ReadFrameS SnapshotOK] in *; [exact I |].
    destruct H as [H0 H1], Hs as [Hs0 Hs1].
    split; [exact (RegionSnapshotOK_readFrame r _ _ _ H0 Hs0) | exact (IH _ _ _ H1 Hs1)].
  Qed.

  Lemma RegionRelAt_readFrame :
    forall cp pp i r x x' y, RegionReadFrame r x x' -> RegionRelAt core cp pp i r x y -> RegionRelAt core cp pp i r x' y.
  Proof.
    intros cp pp i r; unfold RegionReadFrame, RegionRelAt, memRegionTree, implMemRegionTree.
    destruct (regionKind r); intros x x' y H Hr.
    - destruct H as [H0 H1]; unfold ExtRel in *; rewrite H0, H1; exact Hr.
    - subst; exact Hr.
  Qed.

  Lemma MemRelPost_readFrame :
    forall cp pp l i ms ms' mi, ReadFrameS l ms ms' -> MemRelPost core cp pp i l ms mi -> MemRelPost core cp pp i l ms' mi.
  Proof.
    intros cp pp; induction l as [| r rs IH]; intros i ms ms' mi H Hm; cbn [ReadFrameS MemRelPost] in *; [exact I |].
    destruct H as [H0 H1], Hm as [Hm0 Hm1].
    split; [exact (RegionRelAt_readFrame cp pp i r _ _ _ H0 Hm0) | exact (IH _ _ _ _ H1 Hm1)].
  Qed.

  Lemma MemRelPre_readFrame :
    forall cp pp sRev iRev post l i ms ms' mi,
      ReadFrameS (l ++ sRev :: post) ms ms' ->
      MemRelPre core cp pp i l sRev iRev post ms mi -> MemRelPre core cp pp i l sRev iRev post ms' mi.
  Proof.
    intros cp pp sRev iRev post; induction l as [| r l IH]; intros i ms ms' mi H Hm;
      cbn [ReadFrameS MemRelPre app] in *.
    - destruct H as [_ H1]; exact (MemRelPost_readFrame cp pp post (S i) _ _ _ H1 Hm).
    - destruct H as [H0 H1], Hm as [Hm0 Hm1].
      split; [exact (RegionRelAt_readFrame cp pp i r _ _ _ H0 Hm0) | exact (IH _ _ _ _ H1 Hm1)].
  Qed.

  (* A CustomMem region (the CLINT, the PLIC, the revoker) is unchanged *)
  Lemma regionStateAt_readFrame :
    forall l idx r0 (pf : nth_error l idx = Some r0) ms ms',
      ReadFrameS l ms ms' -> isCustomR r0 ->
      regionStateAt (memRegionTree core) idx l r0 pf ms' = regionStateAt (memRegionTree core) idx l r0 pf ms.
  Proof.
    induction l as [| r rs IH]; intros [| i'] r0 pf ms ms' H Hc; try discriminate pf;
      cbn [ReadFrameS] in H; destruct H as [H0 H1].
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      rewrite (RegionReadFrame_custom r0 Hc _ _ H0); reflexivity.
    - cbn [regionStateAt]; apply IH; assumption.
  Qed.
End ReadFrame.

(* --- 2. A Data Read of One Region --- *)

Section RegionRead.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma region_line_read_wp :
    forall r fwc (env : Env (memRegionTree core r)) (x : TS (memRegionTree core r)) (L : type Addr)
           (mask : type (Array LineBytes Bool)) P,
      (forall sub (y : RecvPath (memRegionTree core r)) v, specRegionEnv core initLine r fwc sub y v -> env sub y v) ->
      match r.(regionKind) with ExternalMem => true | CustomMem _ _ _ _ => false end = true ->
      (forall x', RegionReadFrame core r x x' -> P x' (RegionLineContent core initLine r x L)) ->
      evalActionPropGen env (@memRegionLineRead core r type L mask) x P.
  Proof.
    intros r fwc; unfold RegionReadFrame, RegionLineContent, specRegionEnv, memRegionLineRead, memRegionTree.
    destruct (regionKind r) as [| ch rd wr irq]; intros env x L mask P Henv Hk HP; [| discriminate Hk].
    unfold externalLineRead, externalLineReadRq, externalLineReadRp.
    destruct x as [xf [xrq [xrp [xwr []]]]].
    cbn.
    exists (evalLineWriteRqTrace (initLine r) xwr L).
    split.
    - apply Henv; cbn; reflexivity.
    - apply HP; cbn; split; reflexivity.
  Qed.
End RegionRead.

(* --- 3. A Data Read through the Router --- *)

Section RouteRead.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  (* No region after the first one holding line `L` holds it *)
  Fixpoint lineUnique (l : list MemRegion) (L : type Addr) : Prop :=
    match l with
    | [] => True
    | r :: rs => if isRegionAddrB r L then lineKind rs L = None else lineUnique rs L
    end.

  Definition orAll (vs : list (type LineReadRp)) : type LineReadRp :=
    fold_left (@evalOrBinary LineReadRp) vs (getDefault LineReadRp).

  Lemma rev_tail_rev : forall {A : Type} (l acc : list A), rev_tail l acc = (rev l ++ acc)%list.
  Proof.
    intros A l; induction l as [| x xs IH]; intros acc; cbn [rev_tail rev]; [reflexivity |].
    rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma orAll_snoc_default : forall vs, orAll (vs ++ [getDefault LineReadRp]) = orAll vs.
  Proof. intros vs; unfold orAll; rewrite fold_left_app; cbn [fold_left]; apply evalOrBinary_getDefault_r. Qed.

  Lemma orAll_defaults_snoc :
    forall vs v, Forall (fun x => x = getDefault LineReadRp) vs -> orAll (vs ++ [v]) = v.
  Proof.
    intros vs v H; unfold orAll; rewrite fold_left_app.
    rewrite (fold_left_evalOrBinary_default vs _ H); cbn [fold_left].
    apply evalOrBinary_getDefault_l.
  Qed.

  Lemma route_none_wp :
    forall (getAction : forall r, Action type (memRegionTree core r) LineReadRp) L l acc
           (env : Env (specMemTree core l)) ms P,
      lineKind l L = None ->
      P ms (orAll (map (@evalExpr _) (rev acc))) ->
      evalActionPropGen env (genRouteRegionActionAux (memRegionTree core) getAction (@Or type LineReadRp) L acc l) ms P.
  Proof.
    intros getAction L l; induction l as [| r rs IH]; intros acc env ms P Hk HP.
    - cbn [genRouteRegionActionAux evalActionPropGen].
      rewrite rev_tail_rev, app_nil_r; exact HP.
    - cbn [lineKind] in Hk.
      destruct (isRegionAddrB r L) eqn:Em; [discriminate Hk |].
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      rewrite Em.
      rewrite evalActionPropGen_liftAction.
      apply IH; [exact Hk |].
      destruct ms as [m0 [m1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
      cbn [rev map]; rewrite map_app; cbn [map].
      change (evalExpr (Var type LineReadRp (evalExpr ConstDef))) with (getDefault LineReadRp).
      rewrite orAll_snoc_default; exact HP.
  Qed.

  Lemma route_match_wp :
    forall (L : type Addr) (mask : type (Array LineBytes Bool)) l fwcs acc (env : Env (specMemTree core l)) ms P,
      SpecEnvOK core initLine l fwcs env ->
      lineKind l L = Some true -> lineUnique l L ->
      Forall (fun e => evalExpr e = getDefault LineReadRp) acc ->
      (forall ms', ReadFrameS core l ms ms' -> P ms' (lineContent core initLine l ms L)) ->
      evalActionPropGen env
        (genRouteRegionActionAux (memRegionTree core) (fun r => @memRegionLineRead core r type L mask)
           (@Or type LineReadRp) L acc l) ms P.
  Proof.
    intros L mask l; induction l as [| r rs IH]; intros fwcs acc env ms P Henv Hk Hu Hacc HP;
      [discriminate Hk |].
    cbn [lineKind lineUnique lineContent] in Hk, Hu, HP.
    cbn [genRouteRegionActionAux evalActionPropGen].
    change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
    destruct ms as [m0 [m1 []]].
    revert Hk Hu HP; destruct (isRegionAddrB r L) eqn:Em; intros Hk Hu HP; rewrite evalActionPropGen_liftAction.
    - (* r holds L: its read, then no other region answers *)
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd].
      apply (region_line_read_wp core initLine r (fwcs 0%nat)).
      + intros sub y v Hy; exact (SpecEnvOK_head core initLine r rs fwcs env _ Henv sub y v Hy).
      + injection Hk as Hk; exact Hk.
      + intros x' Hx'.
        cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
        rewrite evalActionPropGen_liftAction.
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
        apply route_none_wp; [exact Hu |].
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd].
        cbn [rev map]; rewrite map_app; cbn [map].
        change (evalExpr (Var type LineReadRp (RegionLineContent core initLine r m0 L)))
          with (RegionLineContent core initLine r m0 L).
        rewrite orAll_defaults_snoc by (apply Forall_map; apply Forall_rev; exact Hacc).
        apply HP; cbn [ReadFrameS Fst Snd]; split; [exact Hx' | apply ReadFrameS_refl].
    - (* r does not hold L *)
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
      apply (IH (fun i => fwcs (S i))).
      + exact (SpecEnvOK_tail core initLine r rs fwcs env _ Henv).
      + exact Hk.
      + exact Hu.
      + constructor; [reflexivity | exact Hacc].
      + intros ms' Hms'.
        cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd].
        apply HP; cbn [ReadFrameS Fst Snd]; split; [apply RegionReadFrame_refl | exact Hms'].
  Qed.

  Lemma specMemLineRead_wp :
    forall (L : type Addr) (mask : type (Array LineBytes Bool)) l fwcs (env : Env (specMemTree core l)) ms P,
      SpecEnvOK core initLine l fwcs env ->
      lineKind l L = Some true -> lineUnique l L ->
      (forall ms', ReadFrameS core l ms ms' -> P ms' (lineContent core initLine l ms L)) ->
      evalActionPropGen env (@specMemLineRead core type l L mask) ms P.
  Proof.
    intros L mask l fwcs env ms P Henv Hk Hu HP.
    unfold specMemLineRead, genRouteRegionAction.
    exact (route_match_wp L mask l fwcs [] env ms P Henv Hk Hu (Forall_nil _) HP).
  Qed.

  (* A single-line data read returns the line content's value *)
  Lemma specMemRead_wp :
    forall (addr : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)) l fwcs (env : Env (specMemTree core l)) ms P,
      SpecEnvOK core initLine l fwcs env ->
      lineKind l (lineOf false addr) = Some true -> lineUnique l (lineOf false addr) ->
      (forall ms', ReadFrameS core l ms ms' ->
         P ms' (evalLetExpr (memAssembleCapRead (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) sz)
                  (Var type CapPacket (specPkt addr (lineContent core initLine l ms (lineOf false addr))))))) ->
      evalActionPropGen env (@specMemRead core type l addr sz) ms P.
  Proof.
    intros addr sz l fwcs env ms P Henv Hk Hu HP.
    unfold specMemRead, specMemReadFirstLine; cbn [evalActionPropGen].
    apply evalActionPropGen_toAction; cbv beta.
    apply (specMemLineRead_wp _ _ l fwcs); [exact Henv | exact Hk | exact Hu |].
    intros ms' Hms'.
    apply evalActionPropGen_toAction; cbv beta.
    apply evalActionPropGen_toAction; cbv beta.
    exact (HP ms' Hms').
  Qed.
End RouteRead.

(* --- 4. One Region per Line: Disjoint Regions --- *)

Lemma regionSize_nonneg : forall r, (0 <= regionSize r)%Z.
Proof. intros r; apply Z.leb_le, Is_true_eq_true, regionSizeNonNeg. Qed.

Lemma isRegionAddrB_eq :
  forall r L, isRegionAddrB r L =
    andb (negb (Zmod.to_Z L <? Zmod.to_Z (Zmod.of_Z (2 ^ AddrSz) (regionBase r))))%Z
         (Zmod.to_Z L <? Zmod.to_Z (Zmod.of_Z (2 ^ AddrSz) (regionBase r + regionSize r)))%Z.
Proof. reflexivity. Qed.

Lemma isRegionAddrB_bounds :
  forall r L, isRegionAddrB r L = true -> (regionBase r <= Zmod.to_Z L < regionBase r + regionSize r)%Z.
Proof.
  intros r L H.
  pose proof (regionSize_nonneg r) as Hs.
  assert (Hin : ((0 <=? regionBase r) && (regionBase r + regionSize r <=? Z.shiftl 1 AddrSz))%Z = true)
    by (apply Is_true_eq_true; exact (regionInMemory r)).
  apply andb_prop in Hin as [Hb Ht]; apply Z.leb_le in Hb; apply Z.leb_le in Ht; rewrite Z.shiftl_1_l in Ht.
  rewrite isRegionAddrB_eq, !Zmod.to_Z_of_Z in H.
  assert (Hpos : (0 < 2 ^ AddrSz)%Z) by (apply Z.pow_pos_nonneg; cbv; congruence).
  pose proof (Zmod.unsigned_pos_bound L Hpos) as HL.
  apply andb_prop in H as [H1 H2]; apply negb_true_iff, Z.ltb_ge in H1; apply Z.ltb_lt in H2.
  destruct (Z.eq_dec (regionBase r + regionSize r) (2 ^ AddrSz)) as [E | E].
  - rewrite E, Z_mod_same_full in H2.
    lia.
  - rewrite Z.mod_small in H1 by lia.
    rewrite Z.mod_small in H2 by lia.
    lia.
Qed.

Lemma isRegionAddrB_disjoint :
  forall r1 r2 L, disjointBool r1 r2 = true -> isRegionAddrB r1 L = true -> isRegionAddrB r2 L = false.
Proof.
  intros r1 r2 L Hd Hm1.
  destruct (isRegionAddrB r2 L) eqn:Hm2; [exfalso | reflexivity].
  apply isRegionAddrB_bounds in Hm1; apply isRegionAddrB_bounds in Hm2.
  unfold disjointBool in Hd; apply orb_true_iff in Hd as [Hd | Hd]; apply Z.leb_le in Hd; lia.
Qed.

Lemma lineKind_none_disjoint :
  forall r rs L, forallb (disjointBool r) rs = true -> isRegionAddrB r L = true -> lineKind rs L = None.
Proof.
  intros r rs L; induction rs as [| r' rs IH]; intros Hd Hm; [reflexivity |].
  cbn [forallb] in Hd; apply andb_prop in Hd as [Hd1 Hd2].
  cbn [lineKind]; rewrite (isRegionAddrB_disjoint r r' L Hd1 Hm).
  apply IH; assumption.
Qed.

Lemma lineUnique_disjoint : forall l L, pairwiseDisjoint l = true -> lineUnique l L.
Proof.
  induction l as [| r rs IH]; intros L Hd; [exact I |].
  cbn [pairwiseDisjoint] in Hd; apply andb_prop in Hd as [Hd1 Hd2].
  cbn [lineUnique]; destruct (isRegionAddrB r L) eqn:Hm.
  - exact (lineKind_none_disjoint r rs L Hd1 Hm).
  - apply IH; exact Hd2.
Qed.
