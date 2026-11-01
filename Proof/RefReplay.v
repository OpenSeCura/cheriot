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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph
  RefSpecRead RefSpecFetch.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE SPEC REPLAYS A GHOST ENTRY
 * ===========================================================================
 * At a commit point the spec runs `specStep` for the head entry of the ghost chain, and then for
 * the following ticks and non-blocking entries (the eager replay). This file builds such a
 * `specStep` from the relation's facts about the entry (`specStep_wp`): its deferred part is left
 * to the caller, which knows the entry's kind.
 * Proofs step through the actions with the one-step lemmas of RefSpecFetch.v (see the handoff,
 * 3.1: `cbn [evalActionPropGen]` over big goals makes `Qed` slow). *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. The fence.i Wait Flags of the Spec Memory --- *)

Definition regionWaitB (r : MemRegion) : TS (memRegionTree r) -> bool :=
  match r.(regionKind) as k return TS (memRegionKindTree r k) -> bool with
  | ExternalMem => fun x => x.(Fst).(Snd).(Snd).(Fst)
  | CustomMem _ _ _ _ => fun _ => false
  end.

(* No ExternalMem region of the spec memory waits for a fence.i ack *)
Fixpoint SpecNoWait (l : list MemRegion) : TS (specMemTree l) -> Prop :=
  match l as l0 return TS (specMemTree l0) -> Prop with
  | [] => fun _ => True
  | r :: rs => fun ms => regionWaitB r ms.(Fst) = false /\ SpecNoWait rs ms.(Snd).(Fst)
  end.

Lemma regionWait_wp :
  forall r (env : Env (memRegionTree r)) (x : TS (memRegionTree r)) P,
    P x (regionWaitB r x) -> evalActionPropGen env (@memRegionReadFenceIWait r type) x P.
Proof.
  intros r; unfold regionWaitB, memRegionReadFenceIWait, memRegionTree.
  destruct (regionKind r); intros env x P HP.
  - unfold externalReadFenceIWait.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    destruct x as [[frq [frp [fw [firq [fack []]]]]] rest].
    cbn.
    unfold cast_reg.
    repeat match goal with |- context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
      rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) end.
    exact HP.
  - exact HP.
Qed.

Lemma fenceIWait_fold :
  forall l acc (ms : TS (specMemTree l)) (env : Env (specMemTree l)) P,
    Forall (fun e => evalExpr e = getDefault Bool) acc -> SpecNoWait l ms -> P ms (getDefault Bool) ->
    evalActionPropGen env (genFoldRegionActionsAux memRegionTree (fun r => @memRegionReadFenceIWait r type)
                             (@Or type Bool) acc l) ms P.
Proof.
  induction l as [| r rs IH]; intros acc ms env P Hacc Hw HP.
  - cbn [genFoldRegionActionsAux].
    apply ev_return.
    rewrite rev_tail_rev, app_nil_r.
    change (evalExpr (Or (rev acc))) with (fold_left (@evalOrBinary Bool) (map (@evalExpr Bool) (rev acc)) (getDefault Bool)).
    rewrite fold_left_evalOrBinary_default by (apply Forall_map; apply Forall_rev; exact Hacc).
    exact HP.
  - cbn [genFoldRegionActionsAux].
    destruct ms as [m0 [m1 []]]; cbn [SpecNoWait Fst Snd] in Hw; destruct Hw as [Hw0 Hw1].
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd].
    apply regionWait_wp; cbv beta.
    cbn [writeSubTreeState writeSubTreeState_child child0Path Fst Snd].
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd].
    apply IH.
    + constructor; [exact Hw0 | exact Hacc].
    + exact Hw1.
    + cbn [writeSubTreeState writeSubTreeState_child child1Path Fst Snd]; exact HP.
Qed.

Lemma specMemReadFenceIWait_wp :
  forall l (env : Env (specMemTree l)) ms P,
    SpecNoWait l ms -> P ms false -> evalActionPropGen env (@specMemReadFenceIWait type l) ms P.
Proof.
  intros l env ms P Hw HP.
  unfold specMemReadFenceIWait, genFoldRegionActions.
  apply fenceIWait_fold; [constructor | exact Hw | exact HP].
Qed.

(* The spec waits for an ack only where the impl does (`ExtRel`) *)
Lemma regionNoWait_rel :
  forall cp pp i r x y,
    RegionRelAt cp pp i r x y -> RegionPort (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) r y ->
    regionWaitB r x = false.
Proof.
  intros cp pp i r; unfold RegionRelAt, RegionPort, regionWaitB, memRegionTree, implMemRegionTree.
  destruct (regionKind r); intros x y Hr Hp; [| reflexivity].
  unfold ExtRel in Hr; destruct Hr as [_ [Hw _]]; rewrite Hw; exact Hp.
Qed.

Lemma noWait_post :
  forall cp pp l i ms mi,
    MemRelPost cp pp i l ms mi -> AllPorts (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) l mi ->
    SpecNoWait l ms.
Proof.
  intros cp pp; induction l as [| r l IH]; intros i ms mi Hm Hp; cbn [MemRelPost AllPorts SpecNoWait] in *;
    [exact I |].
  destruct Hm as [Hm0 Hm1], Hp as [Hp0 Hp1].
  split; [exact (regionNoWait_rel cp pp i r _ _ Hm0 Hp0) | exact (IH _ _ _ Hm1 Hp1)].
Qed.

Lemma regionWait_custom : forall r (x : TS (memRegionTree r)), isCustomR r -> regionWaitB r x = false.
Proof.
  intros r; unfold regionWaitB, isCustomR, memRegionTree; destruct (regionKind r); intros x Hc;
    [contradiction | reflexivity].
Qed.

Lemma noWait_pre :
  forall cp pp sRev iRev post l i ms mi,
    isCustomR sRev ->
    MemRelPre cp pp i l sRev iRev post ms mi ->
    AllPorts (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) (l ++ iRev :: post) mi ->
    SpecNoWait (l ++ sRev :: post) ms.
Proof.
  intros cp pp sRev iRev post; induction l as [| r l IH]; intros i ms mi Hc Hm Hp;
    cbn [MemRelPre AllPorts SpecNoWait app] in *.
  - destruct Hp as [_ Hp1].
    split; [exact (regionWait_custom sRev _ Hc) | exact (noWait_post cp pp post (S i) _ _ Hm Hp1)].
  - destruct Hm as [Hm0 Hm1], Hp as [Hp0 Hp1].
    split; [exact (regionNoWait_rel cp pp i r _ _ Hm0 Hp0) | exact (IH _ _ _ Hc Hm1 Hp1)].
Qed.

(* --- 2. Booleans of the Interrupt Check --- *)

Lemma andb_orb_mono :
  forall a b c m1 t1 m2 t2 : bool,
    (m1 = true -> m2 = true) -> (t1 = true -> t2 = true) ->
    andb a (orb (andb m2 b) (andb t2 c)) = false -> andb a (orb (andb m1 b) (andb t1 c)) = false.
Proof.
  intros [] [] [] [] [] [] [] H1 H2 H; cbn in *;
    first [reflexivity | exact H | discriminate (H1 eq_refl) | discriminate (H2 eq_refl) | discriminate H].
Qed.

Lemma evalIsInterruptPending_mono :
  forall pcAddrInit m1 t1 m2 t2 rf,
    (m1 = true -> m2 = true) -> (t1 = true -> t2 = true) ->
    evalIsInterruptPending pcAddrInit m2 t2 rf = false -> evalIsInterruptPending pcAddrInit m1 t1 rf = false.
Proof.
  intros pcAddrInit m1 t1 m2 t2 rf H1 H2.
  unfold evalIsInterruptPending.
  apply andb_orb_mono; assumption.
Qed.

(* --- 3. specStep up to Its Deferred Part --- *)

(* The arguments `specStep` gives `specExecuteDeferred`, in its syntax *)
Definition defDst (aluOut : type AluOutUnion) : type (Bit RegIdxSzReal) := evalExpr (##aluOut`"dstIdx").
Definition defAddr (aluOut : type AluOutUnion) : type Addr :=
  let dstValue : type FullECapWithTag := evalExpr (##aluOut`"dstValue") in evalExpr (##dstValue`"addr").
Definition defDm (execOut : type ExecuteOut) : type (Option MemFenceUnion) := evalExpr (##execOut`"dataMem").
Definition defMd (execOut : type ExecuteOut) : type (Option MulDivUnion) := evalExpr (##execOut`"mulDiv").
Definition defNextPcc (execOut : type ExecuteOut) : type FullECapWithTag := evalExpr (##execOut`"nextPcc").

Lemma defDst_eq : forall a, defDst a = aluDstIdx a.
Proof. reflexivity. Qed.
Lemma defAddr_eq : forall a, defAddr a = (aluDstVal a).(Snd).(Snd).(Fst).
Proof. reflexivity. Qed.
Lemma defDm_eq : forall x, defDm x = execDataMem x.
Proof. reflexivity. Qed.
Lemma defMd_eq : forall x, defMd x = execMulDiv x.
Proof. reflexivity. Qed.
Lemma defNextPcc_eq : forall x, defNextPcc x = execNextPcc x.
Proof. reflexivity. Qed.

(* Conversions with values the actions compute unfold these wrappers first (handoff 3.2) *)
Local Strategy expand [defDst defAddr defDm defMd defNextPcc geAluOut geAluIn evalAluOut evalDecode readPcc writePcc].

(* --- 4. Facts for the Deferred Part of Non-Blocking Entries --- *)

Lemma isNotZero_false :
  forall sz (x : bits sz), Zmod.eqb x Zmod.zero = true -> evalExpr (isNotZero (Var type (Bit sz) x)) = false.
Proof.
  intros sz x H.
  destruct (evalExpr (isNotZero (Var type (Bit sz) x))) eqn:E; [| reflexivity].
  apply isNotZero_true_iff in E; rewrite H in E; discriminate E.
Qed.

(* A fence that is not a memory access: `dispatchMemFence` builds a fence action *)
Lemma dispatchMemFence_notMem :
  forall d a op, opIsMem op = false ->
    evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `? "Mem") = false.
Proof.
  intros d a op H; unfold opIsMem in H; unfold dispatchMemFence; cbn [evalLetExpr]; rewrite H; reflexivity.
Qed.

Definition fenceIFlag (f : type FenceOp) : bool := evalExpr (##f`"FenceI").

Lemma dispatchMemFence_fenceI :
  forall d a op, opIsMem op = false ->
    fenceIFlag (evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `! "Fence")) =
    opIsFenceI op.
Proof.
  intros d a op H.
  assert (E : evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `! "Fence") = opFenceV op).
  { unfold opIsMem in H; unfold dispatchMemFence; cbn [evalLetExpr]; rewrite H; cbv beta iota.
    match goal with |- evalExpr (ReadUnionData _ ?i) = _ =>
      exact (evalExpr_ReadUnionData_BuildUnion MemFenceActionType i (Var type FenceOp (opFenceV op)) eq_refl)
    end. }
  rewrite E; unfold opIsFenceI; rewrite H; reflexivity.
Qed.

Local Strategy expand [fenceIFlag].

(* Whether every port satisfies a decidable predicate is decidable (no classical axioms) *)
Lemma RegionPort_dec :
  forall (P : forall r, TS (implExternalMemRegionTree r) -> Prop),
    (forall r y, P r y \/ ~ P r y) -> forall r y, RegionPort P r y \/ ~ RegionPort P r y.
Proof.
  intros P HP r; unfold RegionPort, implMemRegionTree.
  destruct (regionKind r); intros y; [exact (HP r y) | left; exact I].
Qed.

Lemma AllPorts_dec :
  forall (P : forall r, TS (implExternalMemRegionTree r) -> Prop),
    (forall r y, P r y \/ ~ P r y) -> forall l mi, AllPorts P l mi \/ ~ AllPorts P l mi.
Proof.
  intros P HP; induction l as [| r l IH]; intros mi; cbn [AllPorts]; [left; exact I |].
  destruct (RegionPort_dec P HP r mi.(Fst)) as [H0 | H0]; [| right; intros [H _]; exact (H0 H)].
  destruct (IH mi.(Snd).(Fst)) as [H1 | H1]; [left; split; assumption | right; intros [_ H]; exact (H1 H)].
Qed.

Section Replay.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
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

  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation CT := (specCoreTree pcAddrInit specRegions).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation RfSt := (RfState pcAddrInit).
  Local Abbreviation specClintStateA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation specPlicStateA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation mkCoreA := (mkCore pcAddrInit specRegions).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELNE := (RefRelNE pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                 clintS clint plicS plic initLine fwcs).

  (* 3a. Spec states *)

  Definition mkSys (rf : RfSt) (m : TS (specMemTree specRegions)) (sl : type (Option SecondLine)) : SState :=
    (mkCoreA rf m sl ,, tt).

  Lemma sRf_mkSys : forall rf m sl, sRfA (mkSys rf m sl) = rf.
  Proof. reflexivity. Qed.

  Lemma sMem_mkSys : forall rf m sl, sMemA (mkSys rf m sl) = m.
  Proof. reflexivity. Qed.

  Lemma sSecond_mkSys : forall rf m sl, sSecondA (mkSys rf m sl) = sl.
  Proof. reflexivity. Qed.

  Lemma mkSys_eta : forall s2 : SState, mkSys (sRfA s2) (sMemA s2) (sSecondA s2) = s2.
  Proof. intros [[[rf []] [[m []] [sl []]]] []]; reflexivity. Qed.

  (* 3b. The envs of the core and its memory *)

  Definition CoreEnvOK (env : Env CT) : Prop :=
    forall sc, SpecEnvOK initLine specRegions fwcs (subEnv (SpecFetchDeferred.np_mem pcAddrInit specRegions) env sc).

  Lemma coreEnvOK : forall s2 : SState, CoreEnvOK (subEnv (Spec.np_core pcAddrInit specRegions) envS s2).
  Proof.
    intros s2 sc s lp pf' v Hall.
    unfold subEnv, cast_recv_inv.
    match goal with |- context [eq_rect _ _ (eq_rect _ _ v _ ?e1) _ ?e2] =>
      rewrite (Kind_uip_refl _ e1), (Kind_uip_refl _ e2) end.
    cbn [eq_rect].
    unfold specEnv, envNodeCons, envCtxCons, envCtxMap; cbn -[specRegionsEnv].
    apply Hall.
  Qed.

  (* 3c. Steps of the system tree, each bound by `LetA` (or `Act`) *)

  Lemma sys_memAct_wp :
    forall (env : Env STree) rf m sl s k k' (a : Action type (specMemTree specRegions) k')
           (K : type k' -> Action type STree k) P,
      evalActionPropGen (subEnv (Spec.np_mem pcAddrInit specRegions) env (mkSys rf m sl)) a m
        (fun m' r => evalActionPropGen env (K r) (mkSys rf m' sl) P) ->
      evalActionPropGen env (LetAction s (liftAction (Spec.np_mem pcAddrInit specRegions) a) K) (mkSys rf m sl) P.
  Proof.
    intros env rf m sl s k k' a K P H.
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    exact H.
  Qed.

  Lemma sys_coreAct_wp :
    forall (env : Env STree) rf m sl s k k' (a : Action type CT k') (K : type k' -> Action type STree k) P,
      evalActionPropGen (subEnv (Spec.np_core pcAddrInit specRegions) env (mkSys rf m sl)) a (mkCoreA rf m sl)
        (fun sc' r => evalActionPropGen env (K r) (sc' ,, tt) P) ->
      evalActionPropGen env (LetAction s (liftAction (Spec.np_core pcAddrInit specRegions) a) K) (mkSys rf m sl) P.
  Proof.
    intros env rf m sl s k k' a K P H.
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    exact H.
  Qed.

  Lemma sys_rfAct_wp :
    forall (env : Env STree) rf m sl s k k' (a : Action type (rfTree pcAddrInit) k')
           (K : type k' -> Action type STree k) P,
      evalActionPropGen (subEnv (Spec.np_rf pcAddrInit specRegions) env (mkSys rf m sl)) a rf
        (fun rf' r => evalActionPropGen env (K r) (mkSys rf' m sl) P) ->
      evalActionPropGen env (LetAction s (liftAction (Spec.np_rf pcAddrInit specRegions) a) K) (mkSys rf m sl) P.
  Proof.
    intros env rf m sl s k k' a K P H.
    apply ev_letAction.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    exact H.
  Qed.

  (* 3d. Reads of the spec's latches and of `secondLine` *)

  Lemma plicMeip_wp :
    forall (env : Env (specMemTree specRegions)) m P,
      P m (plicMeipOf (specPlicStateA m)) -> evalActionPropGen env (plicMeipSystem plicS type) m P.
  Proof.
    intros env m P HP.
    unfold plicMeipSystem, plicAction, nthRegionAction.
    apply (proj2 (evalActionPropGen_genNthRegionAction _ _ _ _ _ _ _ _ _)).
    unfold plicMeip; cbn [evalActionPropGen].
    rewrite updRegionStateAt_regionStateAt.
    exact HP.
  Qed.

  Lemma clintMtip_wp :
    forall (env : Env (specMemTree specRegions)) m P,
      P m (clintSampled (specClintStateA m)) -> evalActionPropGen env (readClintMtipAction clintS type) m P.
  Proof.
    intros env m P HP.
    unfold readClintMtipAction, clintAction, nthRegionAction.
    apply (proj2 (evalActionPropGen_genNthRegionAction _ _ _ _ _ _ _ _ _)).
    unfold readClintMtip; cbn [evalActionPropGen].
    rewrite updRegionStateAt_regionStateAt.
    exact HP.
  Qed.

  Lemma readSecondLine_wp :
    forall (env : Env CT) rf m sl P,
      P (mkCoreA rf m sl) sl -> evalActionPropGen env (readSecondLine pcAddrInit specRegions type) (mkCoreA rf m sl) P.
  Proof. intros env rf m sl P HP; exact HP. Qed.

  (* 3e. The execute step of an entry, on the spec register file *)

  Lemma readPcc_cnwbApply : forall c rf, readPcc pcAddrInit (cnwbApply pcAddrInit c rf) = readPcc pcAddrInit rf.
  Proof. intros [[d v] |] rf; cbn [cnwbApply]; [apply readPcc_writeGprVal | reflexivity]. Qed.

  Lemma writePcc_cnwbApply :
    forall p c rf, writePcc pcAddrInit p (cnwbApply pcAddrInit c rf) = cnwbApply pcAddrInit c (writePcc pcAddrInit p rf).
  Proof. intros p [[d v] |] rf; cbn [cnwbApply]; [apply writePcc_writeGprVal | reflexivity]. Qed.

  Lemma geAluOut_cnwbApply :
    forall e c rf, (forall d v, c = Some (d, v) -> EntryAvoids e d) ->
      geAluOut pcAddrInit (cnwbApply pcAddrInit c rf) e = geAluOut pcAddrInit rf e.
  Proof.
    intros e [[d v] |] rf H; cbn [cnwbApply]; [apply geAluOut_writeGprVal; exact (H d v eq_refl) | reflexivity].
  Qed.

  Lemma noRecv_rfTree : noRecvTree (rfTree pcAddrInit) = true.
  Proof. reflexivity. Qed.

  Lemma execND_wp :
    forall (env : Env (rfTree pcAddrInit)) e rf0 rfMid execOut c pcc meip mtip aluOut Q,
      isVirtualCsrAluOut (ge_aluOut e) = false ->
      evalIsInterruptPending pcAddrInit (ge_meip e) (ge_mtip e) rf0 = false ->
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type (readPcc pcAddrInit rf0) (ge_meip e) (ge_mtip e) (ge_aluOut e))
        rf0 rfMid execOut ->
      (forall d v, c = Some (d, v) -> EntryAvoids e d) ->
      pcc = readPcc pcAddrInit rf0 -> aluOut = ge_aluOut e ->
      (meip = true -> ge_meip e = true) -> (mtip = true -> ge_mtip e = true) ->
      Q (cnwbApply pcAddrInit c rfMid) execOut ->
      evalActionPropGen env (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut) (cnwbApply pcAddrInit c rf0) Q.
  Proof.
    intros env e rf0 rfMid execOut c pcc meip mtip aluOut Q Hvc Hint Hsem Hav Ep Ea Hme Hmt HQ.
    subst pcc aluOut.
    pose proof (evalIsInterruptPending_mono pcAddrInit meip mtip (ge_meip e) (ge_mtip e) rf0 Hme Hmt Hint) as Hint'.
    pose proof (proj1 (SemAction_executeNonDeferred_not_virtCsr_meip_mtip_indep pcAddrInit
                         (readPcc pcAddrInit rf0) (ge_meip e) (ge_mtip e) meip mtip (ge_aluOut e) rf0 rfMid execOut
                         Hint Hint' Hvc) Hsem) as Hsem1.
    assert (Hsem2 : SemAction defaultEnv
                      (@executeNonDeferred pcAddrInit type (readPcc pcAddrInit rf0) meip mtip (ge_aluOut e))
                      (cnwbApply pcAddrInit c rf0) (cnwbApply pcAddrInit c rfMid) execOut).
    { destruct c as [[d v] |]; cbn [cnwbApply]; [| exact Hsem1].
      apply SemAction_executeNonDeferred_writeGprVal; [| exact Hsem1].
      destruct (Hav d v eq_refl) as [_ [_ Hdst]].
      intros Hd Hx Heq; exact (Hdst Hd Hx (eq_sym Heq)). }
    rewrite SemAction_iff_evalActionPropGen in Hsem2.
    apply (proj1 (evalActionPropGen_noRecvTree_env defaultEnv env _ _ _ noRecv_rfTree)).
    eapply evalActionPropGen_mono; [| exact Hsem2].
    intros s r [-> ->]; exact HQ.
  Qed.

  (* 3f. `specStep` for ghost entry `e`, from the spec register file `cnwbApply c rf0`: everything
   * up to the deferred part, which the caller supplies for the entry's kind *)
  Lemma specStep_wp :
    forall rf0 m sl e rfMid execOut c Q,
      isVirtualCsrAluOut (ge_aluOut e) = false ->
      ge_aluOut e = geAluOut pcAddrInit rf0 e ->
      evalIsInterruptPending pcAddrInit (ge_meip e) (ge_mtip e) rf0 = false ->
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type (readPcc pcAddrInit rf0) (ge_meip e) (ge_mtip e) (ge_aluOut e))
        rf0 rfMid execOut ->
      (forall d v, c = Some (d, v) -> EntryAvoids e d) ->
      SpecNoWait specRegions m ->
      optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      (forall m' (envC : Env CT) aluOut rfC,
         CoreEnvOK envC -> TraceFrameS specRegions m m' -> aluOut = ge_aluOut e ->
         rfC = cnwbApply pcAddrInit c (writePcc pcAddrInit (defNextPcc execOut) rfMid) ->
         evalActionPropGen envC
           (@specExecuteDeferred pcAddrInit config specRegions type
              (defDst aluOut) (defAddr aluOut) (defDm execOut) (defMd execOut))
           (mkCoreA rfC m' sl) (fun sc' _ => Q sc')) ->
      evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
        (mkSys (cnwbApply pcAddrInit c rf0) m sl) (fun s2' _ => Q s2'.(Fst)).
  Proof.
    intros rf0 m sl e rfMid execOut c Q Hvc Halu Hint Hsem Hav Hnw Hsl Hfa Hmt Hme HD.
    unfold specStep.
    apply sys_memAct_wp; apply specMemReadFenceIWait_wp; [exact Hnw |]; cbv beta.
    apply sys_coreAct_wp; apply readSecondLine_wp; cbv beta.
    apply ev_ifElse_true; [unfold optValid in Hsl; cbn; rewrite Hsl; reflexivity |].
    apply sys_memAct_wp; apply plicMeip_wp; cbv beta.
    apply sys_memAct_wp; apply clintMtip_wp; cbv beta.
    apply sys_coreAct_wp.
    apply (specFetch_wp initLine pcAddrInit specRegions fwcs _ _ m sl (ge_fetchOut e)).
    - apply coreEnvOK.
    - intros L; apply lineUnique_disjoint, Is_true_eq_true, Hdisj.
    - rewrite readPcc_cnwbApply; exact Hfa.
    - intros m' Hm'; cbv beta.
      apply ev_letL; cbv beta.
      apply sys_rfAct_wp; apply (proj2 (evalActionPropGen_regRead _ _ _ _)); cbv beta.
      apply sys_rfAct_wp; apply (proj2 (evalActionPropGen_readRegsList _ _ _ _)); cbv beta.
      apply ev_letL; cbv beta.
      match goal with |- evalActionPropGen _ (LetAction _ (liftAction _ (@executeNonDeferred _ _ _ _ _ ?a)) _) _ _ =>
        assert (Ha : a = ge_aluOut e)
      end.
      { match goal with |- evalLetExpr (@wrappedAlu _ ?p _) = _ =>
          replace p with (readPcc pcAddrInit (cnwbApply pcAddrInit c rf0))
            by (unfold readPcc, readGpr; f_equal; reflexivity)
        end.
        change (geAluOut pcAddrInit (cnwbApply pcAddrInit c rf0) e = ge_aluOut e).
        rewrite (geAluOut_cnwbApply e c rf0 Hav); symmetry; exact Halu. }
      apply sys_rfAct_wp.
      apply (execND_wp _ e rf0 rfMid execOut c);
        [exact Hvc | exact Hint | exact Hsem | exact Hav | | exact Ha | exact Hme | exact Hmt |].
      + transitivity (readPcc pcAddrInit (cnwbApply pcAddrInit c rf0));
          [unfold readPcc, readGpr; f_equal; reflexivity | apply readPcc_cnwbApply].
      + cbv beta.
        apply sys_rfAct_wp; apply (proj2 (evalActionPropGen_writeRegsList _ _ _ _ _)); cbv beta.
        repeat (apply ev_letExp; cbv beta).
        apply sys_coreAct_wp.
        eapply evalActionPropGen_mono; [| apply (HD m' _ _ _ (coreEnvOK _) Hm' Ha)].
        * intros sc' r HQ; cbv beta.
          apply ev_return; cbv beta; apply ev_return; exact HQ.
        * rewrite <- writePcc_cnwbApply; unfold writePcc, updGpr; f_equal; reflexivity.
  Qed.

  (* 3g. The deferred part of a non-blocking entry, one lemma per case (each `Qed` stays small).
   * No memory or fence request and no mulDiv result: nothing happens. *)
  Lemma deferred_none_wp :
    forall (envC : Env CT) rfC m sl aluOut execOut (Q : TS CT -> Prop),
      optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = false ->
      Q (mkCoreA rfC m sl) ->
      evalActionPropGen envC
        (@specExecuteDeferred pcAddrInit config specRegions type
           (defDst aluOut) (defAddr aluOut) (defDm execOut) (defMd execOut))
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl aluOut execOut Q Hdm Hmd HQ.
    unfold specExecuteDeferred.
    apply ev_ifElse_false; [exact Hdm |].
    apply ev_ifElse_false; [exact Hmd |].
    repeat (apply ev_return; cbv beta).
    exact HQ.
  Qed.

  (* A mulDiv result for destination x0: nothing is written *)
  Lemma deferred_md0_wp :
    forall (envC : Env CT) rfC m sl aluOut execOut (Q : TS CT -> Prop),
      optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = true ->
      Zmod.eqb (aluDstIdx aluOut) Zmod.zero = true ->
      Q (mkCoreA rfC m sl) ->
      evalActionPropGen envC
        (@specExecuteDeferred pcAddrInit config specRegions type
           (defDst aluOut) (defAddr aluOut) (defDm execOut) (defMd execOut))
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl aluOut execOut Q Hdm Hmd Ed HQ.
    unfold specExecuteDeferred.
    apply ev_ifElse_false; [exact Hdm |].
    apply ev_ifElse_true; [exact Hmd |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_ifElse_false; [apply isNotZero_false; exact Ed |].
    repeat (apply ev_return; cbv beta).
    exact HQ.
  Qed.

  (* A mulDiv result for a non-zero destination: written to the register file *)
  Lemma deferred_mdWrite_wp :
    forall (envC : Env CT) rfC m sl aluOut execOut (Q : TS CT -> Prop),
      optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = true ->
      Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false ->
      Q (mkCoreA (evalWriteRegsList (gprPathsWithKind pcAddrInit) (aluDstIdx aluOut)
                    (mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type (aluDstVal aluOut).(Snd).(Snd).(Fst)
                                                 (execMulDiv execOut).(Fst)))) rfC) m sl) ->
      evalActionPropGen envC
        (@specExecuteDeferred pcAddrInit config specRegions type
           (defDst aluOut) (defAddr aluOut) (defDm execOut) (defMd execOut))
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl aluOut execOut Q Hdm Hmd Ed HQ.
    unfold specExecuteDeferred.
    apply ev_ifElse_false; [exact Hdm |].
    apply ev_ifElse_true; [exact Hmd |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_ifElse_true; [apply isNotZero_true_iff; exact Ed |].
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    apply (proj2 (evalActionPropGen_writeRegsList _ _ _ _ _)); cbv beta.
    repeat (apply ev_return; cbv beta).
    exact HQ.
  Qed.

  (* The three closed forms of `specMulDivWb` without a memory or fence request. Separate small
   * lemmas: reshaping the hypothesis `Q (mkCoreA (specMulDivWb ..) ..)` in place made the kernel
   * check of the dispatcher take 74 s (handoff 3.2). *)
  Lemma specMulDivWb_none :
    forall aluOut execOut rf,
      optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = false ->
      specMulDivWb pcAddrInit aluOut execOut rf = rf.
  Proof.
    intros aluOut execOut rf Hdm Hmd; unfold specMulDivWb, optValid in *; cbv zeta.
    rewrite Hdm, Hmd; reflexivity.
  Qed.

  Lemma specMulDivWb_md0 :
    forall aluOut execOut rf,
      optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = true ->
      Zmod.eqb (aluDstIdx aluOut) Zmod.zero = true ->
      specMulDivWb pcAddrInit aluOut execOut rf = rf.
  Proof.
    intros aluOut execOut rf Hdm Hmd Ed; unfold specMulDivWb, writeGprVal, optValid in *; cbv zeta.
    rewrite Hdm, Hmd, Ed; reflexivity.
  Qed.

  Lemma specMulDivWb_write :
    forall aluOut execOut rf,
      optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = true ->
      Zmod.eqb (aluDstIdx aluOut) Zmod.zero = false ->
      specMulDivWb pcAddrInit aluOut execOut rf =
      evalWriteRegsList (gprPathsWithKind pcAddrInit) (aluDstIdx aluOut)
        (mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type (aluDstVal aluOut).(Snd).(Snd).(Fst)
                                     (execMulDiv execOut).(Fst)))) rf.
  Proof.
    intros aluOut execOut rf Hdm Hmd Ed; unfold specMulDivWb, writeGprVal, optValid in *; cbv zeta.
    rewrite Hdm, Hmd, Ed; reflexivity.
  Qed.

  (* No memory or fence request: the mulDiv result, if any, is written (`specMulDivWb`) *)
  Lemma deferred_noDm_wp :
    forall (envC : Env CT) rfC m sl aluOut execOut (Q : TS CT -> Prop),
      optValid (execDataMem execOut) = false ->
      Q (mkCoreA (specMulDivWb pcAddrInit aluOut execOut rfC) m sl) ->
      evalActionPropGen envC
        (@specExecuteDeferred pcAddrInit config specRegions type
           (defDst aluOut) (defAddr aluOut) (defDm execOut) (defMd execOut))
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl aluOut execOut Q Hdm HQ.
    destruct (optValid (execMulDiv execOut)) eqn:Emd.
    - destruct (Zmod.eqb (aluDstIdx aluOut) Zmod.zero) eqn:Ed.
      + apply (deferred_md0_wp envC rfC m sl aluOut execOut Q Hdm Emd Ed).
        rewrite (specMulDivWb_md0 aluOut execOut rfC Hdm Emd Ed) in HQ; exact HQ.
      + apply (deferred_mdWrite_wp envC rfC m sl aluOut execOut Q Hdm Emd Ed).
        rewrite (specMulDivWb_write aluOut execOut rfC Hdm Emd Ed) in HQ; exact HQ.
    - apply (deferred_none_wp envC rfC m sl aluOut execOut Q Hdm Emd).
      rewrite (specMulDivWb_none aluOut execOut rfC Hdm Emd) in HQ; exact HQ.
  Qed.

  (* A plain fence (neither a memory access nor fence.i): nothing happens *)
  Lemma deferred_plainFence_wp :
    forall (envC : Env CT) rfC m sl aluOut execOut (Q : TS CT -> Prop),
      optValid (execDataMem execOut) = true ->
      opIsMem (optData (execDataMem execOut)) = false ->
      opIsFenceI (optData (execDataMem execOut)) = false ->
      Q (mkCoreA rfC m sl) ->
      evalActionPropGen envC
        (@specExecuteDeferred pcAddrInit config specRegions type
           (defDst aluOut) (defAddr aluOut) (defDm execOut) (defMd execOut))
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl aluOut execOut Q Hv Hm Hfi HQ.
    unfold specExecuteDeferred.
    apply ev_ifElse_true; [exact Hv |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_ifElse_false; [exact (dispatchMemFence_notMem _ _ _ Hm) |].
    apply ev_letExp; cbv beta.
    apply ev_ifElse_false; [exact (eq_trans (dispatchMemFence_fenceI _ _ _ Hm) Hfi) |].
    repeat (apply ev_return; cbv beta).
    exact HQ.
  Qed.

  (* 3h. `specStep` replays a non-blocking chain entry `rf0 -> rf1` *)
  Lemma specStep_nonBlocking :
    forall rf0 rf1 m sl e c,
      GInstStep pcAddrInit rf0 rf1 e ->
      (optValid (ge_dm e) = true -> opIsMem (optData (ge_dm e)) = false /\ opIsFenceI (optData (ge_dm e)) = false) ->
      (forall d v, c = Some (d, v) -> EntryAvoids e d) ->
      SpecNoWait specRegions m ->
      optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      exists m', TraceFrameS specRegions m m' /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSys (cnwbApply pcAddrInit c rf0) m sl) (mkSys (cnwbApply pcAddrInit c rf1) m' sl) Zmod.zero.
  Proof.
    intros rf0 rf1 m sl e c [Hvc [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]]] Hnb Hav Hnw Hsl Hfa Hmt Hme.
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSys (cnwbApply pcAddrInit c rf0) m sl)
                    (fun s2' _ => exists m', TraceFrameS specRegions m m' /\
                                             s2'.(Fst) = mkCoreA (cnwbApply pcAddrInit c rf1) m' sl)).
    { apply (specStep_wp rf0 m sl e rfMid execOut c
               (fun sc => exists m', TraceFrameS specRegions m m' /\ sc = mkCoreA (cnwbApply pcAddrInit c rf1) m' sl));
        try assumption.
      intros m' envC aluOut rfC _ Hm' Ha Hrf.
      destruct (optValid (execDataMem execOut)) eqn:Edm.
      - pose proof Edm as Edm'; rewrite Hdm in Edm'.
        destruct (Hnb Edm') as [Hnm Hnf].
        apply deferred_plainFence_wp; [exact Edm | rewrite Hdm; exact Hnm | rewrite Hdm; exact Hnf |].
        exists m'; split; [exact Hm' |].
        rewrite Hrf, Hrf1; unfold specMulDivWb; unfold optValid in Edm; rewrite Edm; reflexivity.
      - apply deferred_noDm_wp; [exact Edm |].
        exists m'; split; [exact Hm' |].
        rewrite Hrf, Hrf1, Ha.
        destruct c as [[d v] |]; cbn [cnwbApply]; [| reflexivity].
        rewrite specMulDivWb_writeGprVal; [reflexivity |].
        destruct (Hav d v eq_refl) as [_ [_ Hd]]; exact Hd. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [m' [Hm' E]]]]].
    exists m'; split; [exact Hm' |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.

  Lemma specTick_step :
    forall s2 : SState,
      SemAction envS (@specTickCycle pcAddrInit specRegions type) s2
        (writeSubTreeState (Spec.np_rf pcAddrInit specRegions) s2 (evalIncrementMcycle pcAddrInit (sRfA s2))) Zmod.zero.
  Proof.
    intros s2; unfold specTickCycle; apply SemAction_liftAction_iff; eexists; split; [| reflexivity].
    apply SemAction_incrementMcycle_iff; split; reflexivity.
  Qed.

  Lemma In_specStep_spec : In (@specStep pcAddrInit config specRegions clintS plicS type) specActs.
  Proof.
    refine (eq_ind_r (fun L => In _ L) _ (map_snd_specMod pcAddrInit config specRegions clintS revSpec plicS)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; do 5 right; left; reflexivity.
  Qed.

  (* --- 5. The Eager Replay --- *)

  (* A spec read changes neither the devices nor the memory relation *)
  Lemma specClintState_traceFrame :
    forall ms ms', TraceFrameS specRegions ms ms' -> specClintStateA ms' = specClintStateA ms.
  Proof. intros ms ms' H; exact (regionStateAt_traceFrame specRegions (clintIdx clintS) (clintRegion clintS) (pfClint clintS) _ _ H I). Qed.

  Lemma specPlicState_traceFrame :
    forall ms ms', TraceFrameS specRegions ms ms' -> specPlicStateA ms' = specPlicStateA ms.
  Proof. intros ms ms' H; exact (regionStateAt_traceFrame specRegions (plicIdx plicS) (plicRegion plicS) (pfPlic plicS) _ _ H I). Qed.

  Lemma specRevState_traceFrame :
    forall ms ms', TraceFrameS specRegions ms ms' ->
      specRevState pre post revBase revPfB revPfA ms' = specRevState pre post revBase revPfB revPfA ms.
  Proof.
    intros ms ms' H.
    exact (regionStateAt_traceFrame specRegions (length pre) _
             (nth_error_app_cons_len pre (specRevRegion revBase revPfB revPfA) post) _ _ H I).
  Qed.

  Lemma MemRelC_traceFrame :
    forall g (s1 : IState) (s2 s2' : SState),
      TraceFrameS specRegions (sMemA s2) (sMemA s2') -> MEMC g s1 s2 -> MEMC g s1 s2'.
  Proof.
    intros g s1 s2 s2' Ht Hm.
    unfold MemRelC, MemRel in *.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [Hdev Hsnap]].
    rewrite (specClintState_traceFrame _ _ Ht), (specPlicState_traceFrame _ _ Ht), (specRevState_traceFrame _ _ Ht).
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj Hdev _)).
    - exact (MemRelPre_traceFrame _ _ _ _ _ _ _ _ _ _ Ht Hpre).
    - exact (SnapshotOK_traceFrame specRegions fwcs _ _ Ht Hsnap).
  Qed.

  (* The spec replays the head item of the chain: a tick, or a non-blocking entry (with no
   * crossing access between its halves) *)
  Lemma replay_head :
    forall g it G' (s1 : IState) (s2 : SState),
      RELNE g s1 s2 -> g_chain pcAddrInit g = it :: G' ->
      itemNonBlocking it = true -> (it <> GTick -> optValid (sSecondA s2) = false) ->
      exists rf1 s2', SemActions envS specActs s2 s2' /\ RELNE (gPop pcAddrInit g G' rf1) s1 s2'.
  Proof.
    intros g it G' s1 s2 H Hch Hnb Hsl.
    pose proof H as H0; destruct H0 as [Hrf Hm Hl Hrp Ha Hc Hd Hf Hs Hfr Hw Hrk].
    destruct Hrf as [R1 [R2 [R3 R4]]].
    rewrite Hch in R2.
    destruct (GChain_cons_inv pcAddrInit _ _ _ _ R2) as [rf1 [Hst Hgc]].
    exists rf1.
    destruct it as [| e].
    - (* a tick *)
      exists (writeSubTreeState (Spec.np_rf pcAddrInit specRegions) s2 (evalIncrementMcycle pcAddrInit (sRfA s2))).
      split.
      + eapply ConsAction; [apply (In_specTickCycle_spec pcAddrInit config specRegions clintS revSpec plicS) |
                            apply specTick_step | apply NilAction; reflexivity].
      + cbn [ItemStep] in Hst.
        eapply RefRelNE_pop with (s2 := s2);
          [exact Hch | exact Hst | exact Hgc | exact Hnb | | reflexivity | intros L; reflexivity |
           apply FetchViewExt_refl | exact Hm | reflexivity | reflexivity | exact H].
        rewrite Hst.
        change (evalIncrementMcycle pcAddrInit (sRfA s2) =
                cnwbApply pcAddrInit (g_cnwb pcAddrInit g) (evalIncrementMcycle pcAddrInit (g_rf0 pcAddrInit g))).
        rewrite R1; apply cnwbApply_incr.
    - (* a non-blocking entry *)
      pose proof Hnb as Hb; cbn [itemNonBlocking] in Hb; apply negb_true_iff in Hb.
      assert (Hsl0 : optValid (sSecondA s2) = false) by (apply Hsl; discriminate).
      assert (Hin : In (GInst e) (g_chain pcAddrInit g)) by (rewrite Hch; left; reflexivity).
      assert (HdecW : forall r (y : TS (implExternalMemRegionTree r)),
                 y.(Fst).(Fst).(Snd).(Snd).(Fst) = false \/ ~ y.(Fst).(Fst).(Snd).(Snd).(Fst) = false)
        by (intros r y; destruct (y.(Fst).(Fst).(Snd).(Snd).(Fst)); [right; discriminate | left; reflexivity]).
      destruct (AllPorts_dec (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) HdecW implRegions (iRegionsA s1))
        as [Hnw | Hnw].
      2: { exfalso; unfold FenceRel, NoFenceIWait in Hf; destruct Hf as [_ Hf2].
           destruct (Hf2 Hnw) as [_ [_ [_ Hno]]]; exact (Hno e Hin). }
      assert (Hsnw : SpecNoWait specRegions (sMemA s2)).
      { unfold MemRelC, MemRel in Hm; destruct Hm as [[Hpre _] _].
        eapply noWait_pre; [exact I | exact Hpre | exact Hnw]. }
      cbn [ItemStep] in Hst.
      destruct (specStep_nonBlocking (g_rf0 pcAddrInit g) rf1 (sMemA s2) (sSecondA s2) e (g_cnwb pcAddrInit g) Hst
                  (nonBlocking_dm e Hb) (fun d v Hcn => R3 d v Hcn e Hin) Hsnw Hsl0
                  (Hrp [] e G' (g_rf0 pcAddrInit g) Hch (GChainNil pcAddrInit _))
                  (proj1 (Hl e Hin)) (proj2 (Hl e Hin)))
        as [m' [Hm' Hstep]].
      exists (mkSys (cnwbApply pcAddrInit (g_cnwb pcAddrInit g) rf1) m' (sSecondA s2)).
      split.
      + eapply ConsAction; [apply In_specStep_spec | | apply NilAction; reflexivity].
        rewrite <- R1, mkSys_eta in Hstep; exact Hstep.
      + eapply RefRelNE_pop with (s2 := s2);
          [exact Hch | exact Hst | exact Hgc | exact Hnb | reflexivity | reflexivity | | | | | | exact H].
        * intros L; exact (lineContent_traceFrame initLine specRegions _ _ Hm' L).
        * exact (FetchViewExt_traceFrame specRegions _ _ Hm').
        * apply (MemRelC_traceFrame g s1 s2); [exact Hm' | exact Hm].
        * unfold sClint; exact (specClintState_traceFrame _ _ Hm').
        * unfold sPlic; exact (specPlicState_traceFrame _ _ Hm').
  Qed.

  (* Replaying head items until `EagerRel` holds (at most the length of the chain) *)
  Lemma eager_replay :
    forall n g (s1 : IState) (s2 : SState),
      (length (g_chain pcAddrInit g) <= n)%nat -> RELNE g s1 s2 ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' s1 s2'.
  Proof.
    induction n as [| n IH]; intros g s1 s2 Hlen H.
    - exists g, s2; split; [apply NilAction; reflexivity |].
      apply RefRelG_of_NE; [exact H |].
      left; apply length_zero_iff_nil; lia.
    - revert Hlen; destruct (g_chain pcAddrInit g) as [| it G'] eqn:Hch; intros Hlen.
      + exists g, s2; split; [apply NilAction; reflexivity |].
        apply RefRelG_of_NE; [exact H | left; exact Hch].
      + destruct (andb (itemNonBlocking it)
                       (match it with GTick => true | GInst _ => negb (optValid (sSecondA s2)) end)) eqn:Er.
        * apply andb_prop in Er as [Hnb Hsl].
          assert (Hsl' : it <> GTick -> optValid (sSecondA s2) = false).
          { intros Hne; destruct it as [| e]; [exfalso; apply Hne; reflexivity |].
            apply negb_true_iff in Hsl; exact Hsl. }
          destruct (replay_head g it G' s1 s2 H Hch Hnb Hsl') as [rf1 [s2' [Hs Hg']]].
          assert (Hlen' : (length (g_chain pcAddrInit (gPop pcAddrInit g G' rf1)) <= n)%nat)
            by (cbn [length] in Hlen; unfold gPop; cbn [g_chain]; lia).
          destruct (IH _ s1 s2' Hlen' Hg') as [g'' [s2'' [Hs' Hg'']]].
          exists g'', s2''; split; [eapply SemActions_trans; [exact Hs | exact Hs'] | exact Hg''].
        * exists g, s2; split; [apply NilAction; reflexivity |].
          apply RefRelG_of_NE; [exact H |].
          right; destruct it as [| e]; [cbn in Er; discriminate Er |].
          exists e, G'; split; [exact Hch |].
          cbn [itemNonBlocking] in Er.
          revert Er; destruct (entryBlocking e); intros Er; [right; reflexivity | left].
          revert Er; destruct (optValid (sSecondA s2)); cbn; intros Er; [reflexivity | discriminate Er].
  Qed.
End Replay.
