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
From Cheriot Require Import SpecDefines SpecDevice SpecFetchDeferred.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefGhost RefFetch RefMemRel RefCoreRel
  RefFrame RefPeriph RefSpecRead.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * A SPEC INSTRUCTION FETCH
 * ===========================================================================
 * The spec replays an instruction the impl executed: `specFetch` must return the fetch output
 * the impl used. `FetchAllowedInst` (RefFetch.v) says the spec memory allows it, and this file
 * turns that into an execution of `specFetch`:
 * 1. a read (fetch or data) of the spec memory changes only read traces of ExternalMem regions
 *    (`TraceFrameS`), which none of the relations read;
 * 2. a fetch read of a line routed through the regions can return any response `LineAllowed`
 *    allows (`specMemFetchLineRead_wp`);
 * 3. `specMemFetchRead` and `specFetch` then return what `specFetchRd` / `FetchAllowedInst`
 *    describe. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* When a value an action computes is compared with the transcription of RefFetch.v, unfold the
 * transcription first: the alternative, evaluating `evalExpr` on symbolic values, is slow in the
 * kernel (this file must check in time linear in its size). *)
Local Strategy expand [specPkt specWord specTopExc specCrosses specReads2 specFetchRd specPreFault pccTopOf
                       specFetchOutOf specPreFaultTopExc].

(* --- 1. Reads Change Only Read Traces --- *)

Section TraceFrame.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  (* An ExternalMem region keeps everything but its fetch and data read request/response traces:
   * its fence.i state, its acks and its writes. A CustomMem region is unchanged. *)
  Definition RegionTraceFrame (r : MemRegion) : TS (memRegionTree r) -> TS (memRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (memRegionKindTree r k) -> TS (memRegionKindTree r k) -> Prop with
    | ExternalMem => fun x x' => x'.(Fst).(Snd).(Snd) = x.(Fst).(Snd).(Snd) /\ x'.(Snd).(Snd).(Snd) = x.(Snd).(Snd).(Snd)
    | CustomMem _ _ _ _ => fun x x' => x' = x
    end.

  Fixpoint TraceFrameS (l : list MemRegion) : TS (specMemTree l) -> TS (specMemTree l) -> Prop :=
    match l as l0 return TS (specMemTree l0) -> TS (specMemTree l0) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun ms ms' => RegionTraceFrame r ms.(Fst) ms'.(Fst) /\ TraceFrameS rs ms.(Snd).(Fst) ms'.(Snd).(Fst)
    end.

  Lemma RegionTraceFrame_refl : forall r x, RegionTraceFrame r x x.
  Proof. intros r; unfold RegionTraceFrame, memRegionTree; destruct (regionKind r); intros x; [split |]; reflexivity. Qed.

  Lemma TraceFrameS_refl : forall l ms, TraceFrameS l ms ms.
  Proof.
    induction l as [| r rs IH]; intros ms; cbn [TraceFrameS]; [exact I | split; [apply RegionTraceFrame_refl | apply IH]].
  Qed.

  Lemma RegionTraceFrame_trans :
    forall r x y z, RegionTraceFrame r x y -> RegionTraceFrame r y z -> RegionTraceFrame r x z.
  Proof.
    intros r; unfold RegionTraceFrame, memRegionTree; destruct (regionKind r); intros x y z H1 H2.
    - destruct H1 as [A1 B1], H2 as [A2 B2]; split; congruence.
    - congruence.
  Qed.

  Lemma TraceFrameS_trans : forall l x y z, TraceFrameS l x y -> TraceFrameS l y z -> TraceFrameS l x z.
  Proof.
    induction l as [| r rs IH]; intros x y z H1 H2; cbn [TraceFrameS] in *; [exact I |].
    destruct H1 as [A1 B1], H2 as [A2 B2].
    split; [exact (RegionTraceFrame_trans r _ _ _ A1 A2) | exact (IH _ _ _ B1 B2)].
  Qed.

  Lemma RegionTraceFrame_readFrame : forall r x x', RegionReadFrame r x x' -> RegionTraceFrame r x x'.
  Proof.
    intros r; unfold RegionReadFrame, RegionTraceFrame, memRegionTree; destruct (regionKind r); intros x x' H.
    - destruct H as [H0 H1]; rewrite H0, H1; split; reflexivity.
    - exact H.
  Qed.

  Lemma TraceFrameS_readFrame : forall l ms ms', ReadFrameS l ms ms' -> TraceFrameS l ms ms'.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H; cbn [ReadFrameS TraceFrameS] in *; [exact I |].
    destruct H as [H0 H1]; split; [exact (RegionTraceFrame_readFrame r _ _ H0) | exact (IH _ _ H1)].
  Qed.

  Lemma RegionTraceFrame_custom : forall r, isCustomR r -> forall x x', RegionTraceFrame r x x' -> x' = x.
  Proof.
    intros r; unfold RegionTraceFrame, isCustomR, memRegionTree; destruct (regionKind r); intros Hc x x' H;
      [contradiction | exact H].
  Qed.

  Lemma RegionLineContent_traceFrame :
    forall r x x' L, RegionTraceFrame r x x' -> RegionLineContent initLine r x' L = RegionLineContent initLine r x L.
  Proof.
    intros r; unfold RegionTraceFrame, RegionLineContent, memRegionTree; destruct (regionKind r); intros x x' L H.
    - destruct H as [_ H]; rewrite H; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma lineContent_traceFrame :
    forall l ms ms', TraceFrameS l ms ms' -> forall L, lineContent initLine l ms' L = lineContent initLine l ms L.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H L; cbn [TraceFrameS lineContent] in *; [reflexivity |].
    destruct H as [H0 H1].
    rewrite (RegionLineContent_traceFrame r _ _ L H0), (IH _ _ H1); reflexivity.
  Qed.

  Lemma RegionFetchViewExt_traceFrame : forall r x x', RegionTraceFrame r x x' -> RegionFetchViewExt r x x'.
  Proof.
    intros r; unfold RegionTraceFrame, RegionFetchViewExt, memRegionTree; destruct (regionKind r); intros x x' H.
    - destruct H as [H0 H1]; rewrite H0; split; [reflexivity |].
      exists []; rewrite H1; reflexivity.
    - exact I.
  Qed.

  Lemma FetchViewExt_traceFrame : forall l ms ms', TraceFrameS l ms ms' -> FetchViewExt l ms ms'.
  Proof.
    induction l as [| r rs IH]; intros ms ms' H; cbn [TraceFrameS FetchViewExt] in *; [exact I |].
    destruct H as [H0 H1]; split; [exact (RegionFetchViewExt_traceFrame r _ _ H0) | exact (IH _ _ H1)].
  Qed.

  Lemma RegionSnapshotOK_traceFrame :
    forall r fwc x x', RegionTraceFrame r x x' -> RegionSnapshotOK r fwc x -> RegionSnapshotOK r fwc x'.
  Proof.
    intros r fwc; unfold RegionTraceFrame, RegionSnapshotOK, memRegionTree; destruct (regionKind r);
      intros x x' H Hs.
    - destruct H as [H0 H1]; rewrite H0, H1; exact Hs.
    - exact I.
  Qed.

  Lemma SnapshotOK_traceFrame :
    forall l fwcs ms ms', TraceFrameS l ms ms' -> SnapshotOK fwcs l ms -> SnapshotOK fwcs l ms'.
  Proof.
    induction l as [| r rs IH]; intros fwcs ms ms' H Hs; cbn [TraceFrameS SnapshotOK] in *; [exact I |].
    destruct H as [H0 H1], Hs as [Hs0 Hs1].
    split; [exact (RegionSnapshotOK_traceFrame r _ _ _ H0 Hs0) | exact (IH _ _ _ H1 Hs1)].
  Qed.

  Lemma RegionLineAllowed_traceFrame :
    forall r fwc x x' L rp,
      RegionTraceFrame r x x' -> RegionLineAllowed initLine r fwc x L rp -> RegionLineAllowed initLine r fwc x' L rp.
  Proof.
    intros r fwc; unfold RegionTraceFrame, RegionLineAllowed, memRegionTree; destruct (regionKind r);
      intros x x' L rp H Ha.
    - destruct H as [H0 H1]; rewrite H0, H1; exact Ha.
    - exact I.
  Qed.

  Lemma LineAllowed_traceFrame :
    forall l fwcs ms ms' L rp,
      TraceFrameS l ms ms' -> LineAllowed initLine fwcs l ms L rp -> LineAllowed initLine fwcs l ms' L rp.
  Proof.
    induction l as [| r rs IH]; intros fwcs ms ms' L rp H Ha; cbn [TraceFrameS LineAllowed] in *; [exact Ha |].
    destruct H as [H0 H1].
    destruct (evalExpr (isRegionAddr r (Var type Addr L))).
    - exact (RegionLineAllowed_traceFrame r _ _ _ L rp H0 Ha).
    - exact (IH _ _ _ L rp H1 Ha).
  Qed.

  Lemma FetchAllowedInst_traceFrame :
    forall l fwcs ms ms' pcc fo,
      TraceFrameS l ms ms' -> FetchAllowedInst initLine fwcs l ms pcc fo -> FetchAllowedInst initLine fwcs l ms' pcc fo.
  Proof.
    intros l fwcs ms ms' pcc fo H Ha; unfold FetchAllowedInst in *.
    destruct (specPreFault pcc); [exact Ha |].
    destruct Ha as [rp0 [rp1 [H0 [H1 Hfo]]]].
    exists rp0, rp1; split; [| split; [| exact Hfo]].
    - exact (LineAllowed_traceFrame l fwcs ms ms' _ rp0 H H0).
    - intros Hc; exact (LineAllowed_traceFrame l fwcs ms ms' _ rp1 H (H1 Hc)).
  Qed.

  Lemma RegionRelAt_traceFrame :
    forall cp pp i r x x' y, RegionTraceFrame r x x' -> RegionRelAt cp pp i r x y -> RegionRelAt cp pp i r x' y.
  Proof.
    intros cp pp i r; unfold RegionTraceFrame, RegionRelAt, memRegionTree, implMemRegionTree.
    destruct (regionKind r); intros x x' y H Hr.
    - destruct H as [H0 H1]; unfold ExtRel in *; rewrite H0, H1; exact Hr.
    - subst; exact Hr.
  Qed.

  Lemma MemRelPost_traceFrame :
    forall cp pp l i ms ms' mi, TraceFrameS l ms ms' -> MemRelPost cp pp i l ms mi -> MemRelPost cp pp i l ms' mi.
  Proof.
    intros cp pp; induction l as [| r rs IH]; intros i ms ms' mi H Hm; cbn [TraceFrameS MemRelPost] in *;
      [exact I |].
    destruct H as [H0 H1], Hm as [Hm0 Hm1].
    split; [exact (RegionRelAt_traceFrame cp pp i r _ _ _ H0 Hm0) | exact (IH _ _ _ _ H1 Hm1)].
  Qed.

  Lemma MemRelPre_traceFrame :
    forall cp pp sRev iRev post l i ms ms' mi,
      TraceFrameS (l ++ sRev :: post) ms ms' ->
      MemRelPre cp pp i l sRev iRev post ms mi -> MemRelPre cp pp i l sRev iRev post ms' mi.
  Proof.
    intros cp pp sRev iRev post; induction l as [| r l IH]; intros i ms ms' mi H Hm;
      cbn [TraceFrameS MemRelPre app] in *.
    - destruct H as [_ H1]; exact (MemRelPost_traceFrame cp pp post (S i) _ _ _ H1 Hm).
    - destruct H as [H0 H1], Hm as [Hm0 Hm1].
      split; [exact (RegionRelAt_traceFrame cp pp i r _ _ _ H0 Hm0) | exact (IH _ _ _ _ H1 Hm1)].
  Qed.

  (* A CustomMem region (the CLINT, the PLIC, the revoker) is unchanged *)
  Lemma regionStateAt_traceFrame :
    forall l idx r0 (pf : nth_error l idx = Some r0) ms ms',
      TraceFrameS l ms ms' -> isCustomR r0 ->
      regionStateAt memRegionTree idx l r0 pf ms' = regionStateAt memRegionTree idx l r0 pf ms.
  Proof.
    induction l as [| r rs IH]; intros [| i'] r0 pf ms ms' H Hc; try discriminate pf;
      cbn [TraceFrameS] in H; destruct H as [H0 H1].
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      rewrite (RegionTraceFrame_custom r0 Hc _ _ H0); reflexivity.
    - cbn [regionStateAt]; apply IH; assumption.
  Qed.
End TraceFrame.

(* --- 1b. One Step of an Action ---
 * One lemma per action constructor. Proofs step through an action with these and a local
 * `cbv beta` instead of reducing `evalActionPropGen` over the whole goal: each step is then a
 * syntactic match for the kernel, which keeps `Qed` linear in the size of the action. *)

Section OneStep.
  Context {t : Tree Elem} (env : Env t).

  Lemma ev_letExp :
    forall {k k'} s (e : Expr type k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (cont (evalExpr e)) old P -> evalActionPropGen env (LetExp s e cont) old P.
  Proof. intros k k' s e cont old P H; exact H. Qed.

  Lemma ev_letAction :
    forall {k k'} s (a : Action type t k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env a old (fun s' r => evalActionPropGen env (cont r) s' P) ->
      evalActionPropGen env (LetAction s a cont) old P.
  Proof. intros k k' s a cont old P H; exact H. Qed.

  Lemma ev_letL :
    forall {k k'} s (le : LetExpr type k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (cont (evalLetExpr le)) old P ->
      evalActionPropGen env (LetAction s (@toAction type t k' le) cont) old P.
  Proof.
    intros k k' s le cont old P H; cbn [evalActionPropGen].
    apply (proj2 (evalActionPropGen_toAction le old _)); exact H.
  Qed.

  Lemma ev_ifElse_true :
    forall {k k'} s (p : Expr type Bool) (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
      evalExpr p = true ->
      evalActionPropGen env tb old (fun s' r => evalActionPropGen env (cont r) s' P) ->
      evalActionPropGen env (IfElse s p tb fb cont) old P.
  Proof. intros k k' s p tb fb cont old P Hp H; cbn [evalActionPropGen]; rewrite Hp; exact H. Qed.

  Lemma ev_ifElse_false :
    forall {k k'} s (p : Expr type Bool) (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
      evalExpr p = false ->
      evalActionPropGen env fb old (fun s' r => evalActionPropGen env (cont r) s' P) ->
      evalActionPropGen env (IfElse s p tb fb cont) old P.
  Proof. intros k k' s p tb fb cont old P Hp H; cbn [evalActionPropGen]; rewrite Hp; exact H. Qed.

  Lemma ev_return :
    forall {k} (e : Expr type k) old P, P old (evalExpr e) -> evalActionPropGen env (Return e) old P.
  Proof. intros k e old P H; exact H. Qed.
End OneStep.

(* --- 2. A Fetch Read of One Line through the Router --- *)

Section FetchRead.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma region_fetch_read_wp :
    forall r fwc (env : Env (memRegionTree r)) (x : TS (memRegionTree r)) (L : type Addr) rp P,
      (forall sub (y : RecvPath (memRegionTree r)) v, specRegionEnv initLine r fwc sub y v -> env sub y v) ->
      RegionLineAllowed initLine r fwc x L rp ->
      (forall x', RegionTraceFrame r x x' -> P x' rp) ->
      evalActionPropGen env (@memRegionFetchLineRead r type L) x P.
  Proof.
    intros r fwc; unfold RegionTraceFrame, RegionLineAllowed, specRegionEnv, memRegionFetchLineRead, memRegionTree.
    destruct (regionKind r) as [| ch rd wr irq]; intros env x L rp P Henv Hal HP.
    - unfold externalFetchLineRead, externalFetchLineReadRq, externalFetchLineReadRp.
      destruct x as [[frq [frp [fw [firq [fack []]]]]] [xrq [xrp [xwr []]]]].
      cbn.
      unfold cast_send_expr.
      repeat match goal with |- context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
        rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) end.
      cbn.
      exists rp; split.
      + apply Henv; cbn; exact Hal.
      + unfold cast_recv.
        repeat match goal with |- context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
          rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) end.
        apply HP; cbn; split; reflexivity.
    - cbn; exists rp; apply HP; reflexivity.
  Qed.

  Lemma route_fetch_wp :
    forall (L : type Addr) l fwcs acc (env : Env (specMemTree l)) ms rp P,
      SpecEnvOK initLine l fwcs env ->
      lineUnique l L ->
      LineAllowed initLine fwcs l ms L rp ->
      Forall (fun e => evalExpr e = getDefault LineReadRp) acc ->
      (forall ms', TraceFrameS l ms ms' -> P ms' rp) ->
      evalActionPropGen env
        (genRouteRegionActionAux memRegionTree (fun r => @memRegionFetchLineRead r type L)
           (@Or type LineReadRp) L acc l) ms P.
  Proof.
    intros L l; induction l as [| r rs IH]; intros fwcs acc env ms rp P Henv Hu Hal Hacc HP.
    - cbn [LineAllowed] in Hal; subst rp.
      apply route_none_wp; [reflexivity |].
      unfold orAll; rewrite fold_left_evalOrBinary_default by (apply Forall_map; apply Forall_rev; exact Hacc).
      apply HP; exact I.
    - cbn [lineUnique LineAllowed] in Hu, Hal.
      cbn [genRouteRegionActionAux evalActionPropGen].
      change (evalExpr (Var type Bool (evalExpr (isRegionAddr r (Var type Addr L))))) with (isRegionAddrB r L).
      change (evalExpr (isRegionAddr r (Var type Addr L))) with (isRegionAddrB r L) in Hal.
      destruct ms as [m0 [m1 []]].
      revert Hu Hal HP; destruct (isRegionAddrB r L) eqn:Em; intros Hu Hal HP; rewrite evalActionPropGen_liftAction.
      + (* r holds L: its fetch read, then no other region answers *)
        cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd].
        apply (region_fetch_read_wp r (fwcs 0%nat) _ _ L rp).
        * intros sub y v Hy; exact (SpecEnvOK_head initLine r rs fwcs env _ Henv sub y v Hy).
        * exact Hal.
        * intros x' Hx'.
          cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
          rewrite evalActionPropGen_liftAction.
          cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
          apply route_none_wp; [exact Hu |].
          cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd].
          cbn [rev map]; rewrite map_app; cbn [map].
          change (evalExpr (Var type LineReadRp rp)) with rp.
          rewrite orAll_defaults_snoc by (apply Forall_map; apply Forall_rev; exact Hacc).
          apply HP; cbn [TraceFrameS Fst Snd]; split; [exact Hx' | apply TraceFrameS_refl].
      + (* r does not hold L *)
        cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
        apply (IH (fun i => fwcs (S i)) _ _ _ rp).
        * exact (SpecEnvOK_tail initLine r rs fwcs env _ Henv).
        * exact Hu.
        * exact Hal.
        * constructor; [reflexivity | exact Hacc].
        * intros ms' Hms'.
          cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd].
          apply HP; cbn [TraceFrameS Fst Snd]; split; [apply RegionTraceFrame_refl | exact Hms'].
  Qed.

  Lemma specMemFetchLineRead_wp :
    forall (L : type Addr) l fwcs (env : Env (specMemTree l)) ms rp P,
      SpecEnvOK initLine l fwcs env -> lineUnique l L ->
      LineAllowed initLine fwcs l ms L rp ->
      (forall ms', TraceFrameS l ms ms' -> P ms' rp) ->
      evalActionPropGen env (@specMemFetchLineRead type l L) ms P.
  Proof.
    intros L l fwcs env ms rp P Henv Hu Hal HP.
    unfold specMemFetchLineRead, genRouteRegionAction.
    exact (route_fetch_wp L l fwcs [] env ms rp P Henv Hu Hal (Forall_nil _) HP).
  Qed.

  (* --- 3. The Instruction Read: One or Two Lines --- *)

  Lemma specMemFetchRead_wp :
    forall l fwcs (env : Env (specMemTree l)) ms (pc : type Addr) (top : type (Bit (AddrSz + 2))) rp0 rp1 P,
      SpecEnvOK initLine l fwcs env ->
      (forall L, lineUnique l L) ->
      LineAllowed initLine fwcs l ms (evalExpr (memLineAddr (Var type Addr pc))) rp0 ->
      (specReads2 pc top (specWord pc (specPkt pc rp0)) = true ->
       LineAllowed initLine fwcs l ms (evalExpr (memNextLineAddr (Var type Addr pc))) rp1) ->
      (forall ms', TraceFrameS l ms ms' ->
         P ms' (fst (specFetchRd pc top rp0 rp1) ,, (snd (specFetchRd pc top rp0 rp1) ,, tt))) ->
      evalActionPropGen env (@specMemFetchRead type l pc top) ms P.
  Proof.
    intros l fwcs env ms pc top rp0 rp1 P Henv Hu H0 H1 HP.
    destruct (specReads2 pc top (specWord pc (specPkt pc rp0))) eqn:Ec;
      unfold specMemFetchRead;
      apply ev_letExp; cbv beta;
      apply ev_letAction;
      (apply (specMemFetchLineRead_wp _ l fwcs env ms rp0); [exact Henv | apply Hu | exact H0 |]);
      intros ms1 Hms1; cbv beta;
      repeat first [apply ev_letExp; cbv beta | apply ev_letL; cbv beta].
    - apply ev_ifElse_true; [exact Ec |].
      apply ev_letExp; cbv beta.
      apply ev_letAction.
      apply (specMemFetchLineRead_wp _ l fwcs env ms1 rp1); [exact Henv | apply Hu | |].
      + exact (LineAllowed_traceFrame initLine l fwcs ms ms1 _ rp1 Hms1 (H1 eq_refl)).
      + intros ms2 Hms2; cbv beta.
        apply ev_letL; cbv beta.
        apply ev_return; cbv beta.
        repeat first [apply ev_letExp; cbv beta | apply ev_letL; cbv beta].
        apply ev_return.
        match goal with |- P ?m ?v =>
          replace v with (fst (specFetchRd pc top rp0 rp1) ,, (snd (specFetchRd pc top rp0 rp1) ,, tt))
        end.
        * apply HP; exact (TraceFrameS_trans l _ _ _ Hms1 Hms2).
        * unfold specFetchRd; cbv zeta; rewrite Ec; reflexivity.
    - apply ev_ifElse_false; [exact Ec |].
      apply ev_return; cbv beta.
      repeat first [apply ev_letExp; cbv beta | apply ev_letL; cbv beta].
      apply ev_return.
      match goal with |- P ?m ?v =>
        replace v with (fst (specFetchRd pc top rp0 rp1) ,, (snd (specFetchRd pc top rp0 rp1) ,, tt))
      end.
      + apply HP; exact Hms1.
      + unfold specFetchRd; cbv zeta; rewrite Ec; reflexivity.
  Qed.
End FetchRead.

(* --- 4. `specFetch` at the Core Level --- *)

Section SpecFetchCore.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable pcAddrInit : Z.
  Variable regions : list MemRegion.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation CT := (specCoreTree pcAddrInit regions).

  (* The spec core state: [ rf [ rfTree ]; mem [ specMemTree ]; secondLine ] *)
  Definition mkCore (rf : RfState pcAddrInit) (m : TS (specMemTree regions)) (sl : type (Option SecondLine))
    : TS CT :=
    ((rf ,, tt) ,, ((m ,, tt) ,, (sl ,, tt))).

  Lemma core_read_rf :
    forall rf m sl, readSubTreeState (SpecFetchDeferred.np_rf pcAddrInit regions) (mkCore rf m sl) = rf.
  Proof. reflexivity. Qed.

  Lemma core_write_rf :
    forall rf m sl rf',
      writeSubTreeState (SpecFetchDeferred.np_rf pcAddrInit regions) (mkCore rf m sl) rf' = mkCore rf' m sl.
  Proof. reflexivity. Qed.

  Lemma core_read_mem :
    forall rf m sl, readSubTreeState (SpecFetchDeferred.np_mem pcAddrInit regions) (mkCore rf m sl) = m.
  Proof. reflexivity. Qed.

  Lemma core_write_mem :
    forall rf m sl m',
      writeSubTreeState (SpecFetchDeferred.np_mem pcAddrInit regions) (mkCore rf m sl) m' = mkCore rf m' sl.
  Proof. reflexivity. Qed.

  (* The register index 0 of the actions' PCC accesses *)
  Lemma evalExpr_idx0 : evalExpr ($0 : Expr type (Bit RegIdxSzReal)) = (Zmod.zero : bits RegIdxSzReal).
  Proof. reflexivity. Qed.

  Lemma readPcc_idx0 :
    forall rf, evalReadRegsList (gprPathsWithKind pcAddrInit) (evalExpr ($0 : Expr type (Bit RegIdxSzReal))) rf =
               readPcc pcAddrInit rf.
  Proof. intros rf; rewrite evalExpr_idx0; reflexivity. Qed.

  Lemma writePcc_idx0 :
    forall v rf, evalWriteRegsList (gprPathsWithKind pcAddrInit) (evalExpr ($0 : Expr type (Bit RegIdxSzReal))) v rf =
                 writePcc pcAddrInit v rf.
  Proof. intros v rf; rewrite evalExpr_idx0; reflexivity. Qed.

  Local Opaque memAssembleCapRead memExtractCapPacket memMergeCapPacket memCrossesLine isCompressed
    AdderAccessEnd memLineAddr memNextLineAddr preDecode.

  (* The PCC read at the start of `specFetch` *)
  Lemma core_pccRead_wp :
    forall (env : Env CT) rf m sl s k (K : type FullECapWithTag -> Action type CT k) P,
      evalActionPropGen env
        (K (evalReadRegsList (gprPathsWithKind pcAddrInit) (evalExpr ($0 : Expr type (Bit RegIdxSzReal))) rf))
        (mkCore rf m sl) P ->
      evalActionPropGen env
        (LetAction s (liftAction (SpecFetchDeferred.np_rf pcAddrInit regions)
                        (readRegsList (gprPathsWithKind pcAddrInit) ($0 : Expr type (Bit RegIdxSzReal)))) K)
        (mkCore rf m sl) P.
  Proof.
    intros env rf m sl s k K P H.
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    apply (proj2 (evalActionPropGen_readRegsList _ _ _ _)).
    exact H.
  Qed.

  (* An action of the memory subtree bound by `LetA` *)
  Lemma core_memAct_wp :
    forall (env : Env CT) rf m sl s k k' (a : Action type (specMemTree regions) k')
           (K : type k' -> Action type CT k) P,
      evalActionPropGen (subEnv (SpecFetchDeferred.np_mem pcAddrInit regions) env (mkCore rf m sl)) a m
        (fun m' r => evalActionPropGen env (K r) (mkCore rf m' sl) P) ->
      evalActionPropGen env (LetAction s (liftAction (SpecFetchDeferred.np_mem pcAddrInit regions) a) K)
        (mkCore rf m sl) P.
  Proof.
    intros env rf m sl s k k' a K P H.
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    exact H.
  Qed.

  Lemma specFetch_wp :
    forall (env : Env CT) rf m sl fo P,
      (forall sc, SpecEnvOK initLine regions fwcs (subEnv (SpecFetchDeferred.np_mem pcAddrInit regions) env sc)) ->
      (forall L, lineUnique regions L) ->
      FetchAllowedInst initLine fwcs regions m (readPcc pcAddrInit rf) fo ->
      (forall m', TraceFrameS regions m m' -> P (mkCore rf m' sl) fo) ->
      evalActionPropGen env (@specFetch pcAddrInit regions type) (mkCore rf m sl) P.
  Proof.
    intros env rf m sl fo P Henv Hu Hfa HP.
    unfold FetchAllowedInst in Hfa; cbv zeta in Hfa.
    rewrite <- readPcc_idx0 in Hfa.
    destruct (specPreFault (evalReadRegsList (gprPathsWithKind pcAddrInit)
                              (evalExpr ($0 : Expr type (Bit RegIdxSzReal))) rf)) eqn:Ep;
      unfold specFetch;
      apply core_pccRead_wp; cbv beta;
      repeat (apply ev_letExp; cbv beta).
    - apply ev_ifElse_true; [exact Ep |].
      apply ev_letExp; cbv beta.
      apply ev_letL; cbv beta.
      apply ev_return; cbv beta.
      repeat (apply ev_letExp; cbv beta).
      apply ev_return.
      subst fo; exact (HP m (TraceFrameS_refl regions m)).
    - destruct Hfa as [rp0 [rp1 [H0 [H1 Hfo]]]].
      apply ev_ifElse_false; [exact Ep |].
      apply core_memAct_wp.
      apply (specMemFetchRead_wp initLine regions fwcs _ m _ _ rp0 rp1); [apply Henv | exact Hu | exact H0 | exact H1 |].
      intros m' Hm'; cbv beta.
      apply ev_letExp; cbv beta.
      apply ev_letL; cbv beta.
      apply ev_return; cbv beta.
      repeat (apply ev_letExp; cbv beta).
      apply ev_return.
      subst fo; exact (HP m' Hm').
  Qed.
End SpecFetchCore.
