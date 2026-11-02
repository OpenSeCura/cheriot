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
From Cheriot.Proof Require Import RefSpecRead RefSpecFetch RefRevTable RefReplay RefExecLive.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the commit of a load (`readRpPorts` at `AccLoad .. (RdOut b)`), spec side:
 * 1. combinational facts of the load path (`dispatchMemFence`, `dispatchLoadResponse`);
 * 2. the two line reads of a data access;
 * 3. `specCompleteLoad`, the deferred part of a load entry and `specStep` for a load entry. *)

Local Strategy expand [defDst defAddr defDm defMd defNextPcc geAluOut geAluIn evalAluOut evalDecode readPcc writePcc
                       loadCmdOf ldAddr ldPending plSize crossesB lineOf specPkt singleLoadVal secondLoadOf
                       revByteAddrOf].

(* --- 1. Combinational Facts of the Load Path --- *)

(* Reading back the payload of a union built from a variable *)
Ltac strip_var u :=
  lazymatch u with
  | evalExpr (Var _ _ ?u') => strip_var u'
  | _ => u
  end.

Ltac readback :=
  match goal with |- context [evalExpr (@ReadUnionData _ ?ls (Var ?ty ?k ?u) ?i)] =>
    let w := strip_var u in
    lazymatch w with evalExpr (BuildUnion _ (Var ?ty2 ?k2 ?x)) =>
      replace (evalExpr (@ReadUnionData _ ls (Var ty k u) i)) with x
        by (symmetry; exact (evalExpr_ReadUnionData_BuildUnion ls i (Var ty2 k2 x) eq_refl))
    end
  end.

(* Fix the store/load case of the memory operation inside `dispatchMemFence` *)
Ltac store_case Hs :=
  match goal with |- context [evalExpr (ReadUnionTag (Var ?ty ?k ?x) ?j)] =>
    assert (Hs' : evalExpr (ReadUnionTag (Var ty k x) j) = false) by exact Hs;
    rewrite Hs'; cbv iota
  end.

(* A union tag test that computes to the other boolean is contradictory *)
Ltac tag_contra H :=
  match type of H with
  | ?L = true => assert (Hc_ : L = false) by reflexivity; rewrite Hc_ in H; discriminate H
  | ?L = false => assert (Hc_ : L = true) by reflexivity; rewrite Hc_ in H; discriminate H
  end.

Lemma opLoad_notStore : forall op, opIsLoad op = true -> opIsStore op = false.
Proof.
  intros op H; unfold opIsLoad, opIsStore in *; cbv zeta in *.
  apply andb_prop in H as [Hm Hl]; rewrite Hm; cbn [andb].
  cbn [evalExpr] in Hl |- *.
  apply Zmod.eqb_eq in Hl; rewrite Hl; reflexivity.
Qed.

(* The outcome of a load response keeps the load's destination; a rev lookup is for a revokable base *)
Lemma loadOutcome_facts :
  forall config (pl : type PendingLoad) (v : type FullCapWithTag),
    (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = true ->
       (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `! "RevLookup")).(Snd).(Fst).(Fst)
         = pl.(Fst) /\
       baseRevokable config (rcBase (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v)))
                                                 `! "RevLookup"))) = true) /\
    (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = false ->
       (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `! "Writeback")).(Fst) = pl.(Fst)).
Proof.
  intros config pl v.
  unfold dispatchLoadResponse; cbn [evalLetExpr].
  match goal with |- context [evalExpr (Var type Bool (evalExpr (Eq ?x ?y)))] =>
    change (evalExpr (Var type Bool (evalExpr (Eq x y)))) with (evalExpr (Eq x y));
    destruct (evalExpr (Eq x y)); cbv iota
  end.
  - match goal with |- context [evalExpr (Var type Bool (evalExpr (needsRevocationCheck ?c ?e ?tg)))] =>
      change (evalExpr (Var type Bool (evalExpr (needsRevocationCheck c e tg))))
        with (evalExpr (needsRevocationCheck c e tg));
      destruct (evalExpr (needsRevocationCheck c e tg)) eqn:En; cbv iota
    end.
    + split.
      * intros _; readback; split; [reflexivity |].
        unfold needsRevocationCheck in En; cbn [evalExpr map fold_left] in En.
        change (evalAndBinary (k:=Bool)) with andb in En.
        apply andb_prop in En as [_ En].
        unfold baseRevokable, rcBase; exact En.
      * intros Hf; tag_contra Hf.
    + split.
      * intros Ht; tag_contra Ht.
      * intros _; readback; reflexivity.
  - split.
    + intros Ht; tag_contra Ht.
    + intros _; readback; reflexivity.
Qed.

Lemma isNotZero_expr :
  forall sz (e : Expr type (Bit sz)), evalExpr (isNotZero e) = negb (Zmod.eqb (evalExpr e) Zmod.zero).
Proof.
  intros sz e.
  destruct (Zmod.eqb (evalExpr e) Zmod.zero) eqn:E; cbn [negb].
  - destruct (evalExpr (isNotZero e)) eqn:F; [| reflexivity].
    apply (proj1 (isNotZero_true_iff (evalExpr e))) in F; rewrite F in E; discriminate E.
  - apply (proj2 (isNotZero_true_iff (evalExpr e))); exact E.
Qed.

(* `dispatchMemFence` on a load: a memory action that is not a store *)
Lemma dispatchMemFence_load :
  forall d a op, opIsLoad op = true ->
    evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `? "Mem") = true /\
    evalExpr ((Var type MemAction (evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `! "Mem")))
                `? "Store") = false.
Proof.
  intros d a op H.
  pose proof (opLoad_notStore op H) as Hs.
  unfold opIsLoad, opIsStore, opMemPayload, opIsMem in *; cbv zeta in *.
  apply andb_prop in H as [Hm _]; rewrite Hm in Hs; cbn [andb] in Hs.
  unfold dispatchMemFence; cbn [evalLetExpr]; rewrite Hm; cbv beta iota.
  split; [reflexivity |].
  readback.
  store_case Hs.
  reflexivity.
Qed.

(* --- 2. The Two Line Reads of a Data Access --- *)

Section LineReads.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Lemma specMemReadFirstLine_wp :
    forall (addr : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)) l fwcs (env : Env (specMemTree l)) ms P,
      SpecEnvOK initLine l fwcs env ->
      lineKind l (lineOf false addr) = Some true -> lineUnique l (lineOf false addr) ->
      (forall ms', ReadFrameS l ms ms' -> P ms' (lineContent initLine l ms (lineOf false addr))) ->
      evalActionPropGen env (@specMemReadFirstLine type l addr sz) ms P.
  Proof.
    intros addr sz l fwcs env ms P Henv Hk Hu HP.
    unfold specMemReadFirstLine; cbn [evalActionPropGen].
    apply evalActionPropGen_toAction; cbv beta.
    exact (specMemLineRead_wp initLine _ _ l fwcs env ms P Henv Hk Hu HP).
  Qed.

  Lemma specMemReadSecondLine_wp :
    forall (addr : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)) l fwcs (env : Env (specMemTree l)) ms P,
      SpecEnvOK initLine l fwcs env ->
      lineKind l (lineOf true addr) = Some true -> lineUnique l (lineOf true addr) ->
      (forall ms', ReadFrameS l ms ms' -> P ms' (lineContent initLine l ms (lineOf true addr))) ->
      evalActionPropGen env (@specMemReadSecondLine type l addr sz) ms P.
  Proof.
    intros addr sz l fwcs env ms P Henv Hk Hu HP.
    unfold specMemReadSecondLine; cbn [evalActionPropGen].
    apply evalActionPropGen_toAction; cbv beta.
    exact (specMemLineRead_wp initLine _ _ l fwcs env ms P Henv Hk Hu HP).
  Qed.
End LineReads.

(* A `Let` whose value becomes a fresh variable with its equation *)
Section OneStepGen.
  Context {t : Tree Elem} (env : Env t).

  Lemma ev_letExpGen :
    forall {k k'} s (e : Expr type k') (cont : type k' -> Action type t k) old P,
      (forall v, v = evalExpr e -> evalActionPropGen env (cont v) old P) ->
      evalActionPropGen env (LetExp s e cont) old P.
  Proof. intros k k' s e cont old P H; exact (H _ eq_refl). Qed.
End OneStepGen.

(* --- 3. The Spec Side of a Load Commit --- *)

Section LoadSpec.
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
  Hypothesis HrevTab : Is_true (revTableInExternalMem config specRegions).

  Local Abbreviation CT := (specCoreTree pcAddrInit specRegions).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specClintStateA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation specPlicStateA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation mkCoreA := (mkCore pcAddrInit specRegions).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation CEOK := (CoreEnvOK pcAddrInit pre post revBase revPfB revPfA initLine fwcs).
  Local Abbreviation lineContentS := (lineContent initLine specRegions).
  Local Abbreviation specLoadWbA := (specLoadWb config pre post revBase revPfB revPfA initLine).
  Local Abbreviation revBitOfA := (revBitOf config pre post revBase revPfB revPfA initLine).

  Lemma lineUnique_specL : forall L, lineUnique specRegions L.
  Proof. intros L; apply lineUnique_disjoint, Is_true_eq_true, Hdisj. Qed.

  (* The rev byte of a revokable base is in an ExternalMem line *)
  Lemma revByte_line :
    forall base, baseRevokable config base = true ->
      lineKind specRegions (lineOf false (revByteAddrOf config base)) = Some true.
  Proof.
    intros base Hb; destruct (lgRevGranularity_bounds config) as [Hg0 Hg1].
    destruct (revByteAddrOf_inTable config Hg0 Hg1 (revTableSize_nonneg config) base Hb) as [a [Ha Ea]].
    rewrite Ea.
    exact (revTab_line config specRegions (Is_true_eq_true _ Hdisj) (Is_true_eq_true _ HrevTab) a Ha).
  Qed.

  Lemma readRevBit_wp :
    forall (base : type (Bit (AddrSz + 1))) (env : Env (specMemTree specRegions)) ms P,
      SpecEnvOK initLine specRegions fwcs env ->
      lineKind specRegions (lineOf false (revByteAddrOf config base)) = Some true ->
      (forall ms', ReadFrameS specRegions ms ms' -> P ms' (revBitOfA ms base)) ->
      evalActionPropGen env (@readRevBit type config specRegions base) ms P.
  Proof.
    intros base env ms P Henv Hk HP.
    unfold readRevBit.
    apply ev_letL; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_letAction.
    apply (specMemRead_wp initLine _ _ specRegions fwcs env ms); [exact Henv | exact Hk | apply lineUnique_specL |].
    intros ms' Hms'; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_return.
    exact (HP ms' Hms').
  Qed.

  Lemma specLoadWb_rev :
    forall m pl v,
      evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = true ->
      specLoadWbA m pl v =
      (let revInfo : type RevCmd :=
         evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `! "RevLookup") in
       let pr : type PendingRev := evalExpr (##revInfo`"pendingRev") in
       let wb := evalLetExpr (dispatchRevResponse pr (revBitOfA m (evalExpr (##revInfo`"base")))) in
       (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal"))).
  Proof. intros m pl v H; unfold specLoadWb; cbv zeta; rewrite H; reflexivity. Qed.

  Lemma specLoadWb_wb :
    forall m pl v,
      evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = false ->
      specLoadWbA m pl v =
      (let wb : type WbCmd :=
         evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `! "Writeback") in
       (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal"))).
  Proof. intros m pl v H; unfold specLoadWb; cbv zeta; rewrite H; reflexivity. Qed.

  (* The register write of a completed load is the load's destination (`loadOutcome_dst`,
   * RefExecLive.v) *)
  Lemma specLoadWb_dst : forall m pl v, fst (specLoadWbA m pl v) = pl.(Fst).
  Proof.
    intros m pl v.
    destruct (loadOutcome_dst config pl v) as [Hrev Hwb].
    destruct (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup")) eqn:E.
    - rewrite (specLoadWb_rev m pl v E); cbv zeta; cbn [fst].
      rewrite <- (Hrev eq_refl); reflexivity.
    - rewrite (specLoadWb_wb m pl v E); cbv zeta; cbn [fst].
      rewrite <- (Hwb eq_refl); reflexivity.
  Qed.

  Lemma writeSecondLine_wp :
    forall (env : Env CT) rf m sl (v : Expr type (Option SecondLine)) P,
      (forall r, P (mkCoreA rf m (evalExpr v)) r) ->
      evalActionPropGen env (@writeSecondLine pcAddrInit specRegions type v) (mkCoreA rf m sl) P.
  Proof. intros env rf m sl v P HP; exact (HP _). Qed.

  (* The register write of a completed load (`specCompleteLoad`'s last `If`) *)
  Definition wbIfAct (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag) : Action type CT (Bit 0) :=
    IfElse ""%string (isNotZero d)
      (liftAction (SpecFetchDeferred.np_rf pcAddrInit specRegions) (writeRegsList (gprPathsWithKind pcAddrInit) d val))
      (Return (Const type (Bit 0) (getDefault (Bit 0))))
      (fun _ => Retv).

  Lemma wbIf_skip_wp :
    forall (envC : Env CT) rf m sl (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag)
           (P : TS CT -> type (Bit 0) -> Prop),
      Zmod.eqb (evalExpr d) Zmod.zero = true -> (forall r, P (mkCoreA rf m sl) r) ->
      evalActionPropGen envC (wbIfAct d val) (mkCoreA rf m sl) P.
  Proof.
    intros envC rf m sl d val P Hz HP.
    pose proof (isNotZero_expr _ d) as Ec; rewrite Hz in Ec; cbn [negb] in Ec.
    unfold wbIfAct.
    apply ev_ifElse_false; [exact Ec |].
    apply ev_return; cbv beta; apply ev_return; apply HP.
  Qed.

  Lemma wbIf_write_wp :
    forall (envC : Env CT) rf m sl (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag)
           (P : TS CT -> type (Bit 0) -> Prop),
      Zmod.eqb (evalExpr d) Zmod.zero = false ->
      (forall r, P (mkCoreA (evalWriteRegsList (gprPathsWithKind pcAddrInit) (evalExpr d) (evalExpr val) rf) m sl) r) ->
      evalActionPropGen envC (wbIfAct d val) (mkCoreA rf m sl) P.
  Proof.
    intros envC rf m sl d val P Hz HP.
    pose proof (isNotZero_expr _ d) as Ec; rewrite Hz in Ec; cbn [negb] in Ec.
    unfold wbIfAct.
    apply ev_ifElse_true; [exact Ec |].
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    apply (proj2 (evalActionPropGen_writeRegsList _ _ _ _ _)); cbv beta.
    apply ev_return; apply HP.
  Qed.

  Lemma cnwbApply_some :
    forall rf (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag),
      cnwbApply pcAddrInit (Some (evalExpr d, evalExpr val)) rf = writeGprVal pcAddrInit (evalExpr d) (evalExpr val) rf.
  Proof. intros; reflexivity. Qed.

  Lemma writeGprVal_zero :
    forall rf (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag),
      Zmod.eqb (evalExpr d) Zmod.zero = true ->
      writeGprVal pcAddrInit (evalExpr d) (evalExpr val) rf = rf.
  Proof. intros rf d val Hz; unfold writeGprVal; rewrite Hz; reflexivity. Qed.

  Lemma writeGprVal_nz :
    forall rf (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag),
      Zmod.eqb (evalExpr d) Zmod.zero = false ->
      writeGprVal pcAddrInit (evalExpr d) (evalExpr val) rf =
      evalWriteRegsList (gprPathsWithKind pcAddrInit) (evalExpr d) (evalExpr val) rf.
  Proof. intros rf d val Hz; unfold writeGprVal; rewrite Hz; reflexivity. Qed.

  Lemma wbIf_wp :
    forall (envC : Env CT) rf m sl (d : Expr type (Bit RegIdxSzReal)) (val : Expr type FullECapWithTag)
           (P : TS CT -> type (Bit 0) -> Prop),
      (forall r, P (mkCoreA (cnwbApply pcAddrInit (Some (evalExpr d, evalExpr val)) rf) m sl) r) ->
      evalActionPropGen envC (wbIfAct d val) (mkCoreA rf m sl) P.
  Proof.
    intros envC rf m sl d val P HP.
    rewrite cnwbApply_some in HP.
    assert (Hdec : Zmod.eqb (evalExpr d) Zmod.zero = true \/ Zmod.eqb (evalExpr d) Zmod.zero = false)
      by (destruct (Zmod.eqb (evalExpr d) Zmod.zero); [left | right]; reflexivity).
    destruct Hdec as [Hz | Hz].
    - rewrite (writeGprVal_zero rf d val Hz) in HP; exact (wbIf_skip_wp envC rf m sl d val P Hz HP).
    - rewrite (writeGprVal_nz rf d val Hz) in HP; exact (wbIf_write_wp envC rf m sl d val P Hz HP).
  Qed.

  (* `specCompleteLoad`, one lemma per outcome. A rev lookup reads the rev bit (memory reads only). *)
  Lemma completeLoad_rev_wp :
    forall (envC : Env CT) rf m sl pl v (Q : TS CT -> Prop),
      CEOK envC ->
      evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = true ->
      (forall m', ReadFrameS specRegions m m' ->
         Q (mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA m pl v)) rf) m' sl)) ->
      evalActionPropGen envC (@specCompleteLoad pcAddrInit config specRegions type pl v) (mkCoreA rf m sl)
        (fun sc' _ => Q sc').
  Proof.
    intros envC rf m sl pl v Q Henv Erl HQ.
    destruct (proj1 (loadOutcome_facts config pl v) Erl) as [_ Hb].
    unfold specCompleteLoad.
    apply ev_letL; cbv beta.
    apply ev_ifElse_true; [exact Erl |].
    apply ev_letExp; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_letExp; cbv beta.
    apply core_memAct_wp.
    apply readRevBit_wp; [apply Henv | apply revByte_line; exact Hb |].
    intros m1 Hm1; cbv beta.
    apply ev_letL; cbv beta.
    apply (wbIf_wp envC); intros r; cbv beta.
    apply ev_return.
    pose proof (HQ m1 Hm1) as HQ1.
    rewrite (specLoadWb_rev m pl v Erl) in HQ1; cbv zeta in HQ1.
    exact HQ1.
  Qed.

  Lemma completeLoad_wb_wp :
    forall (envC : Env CT) rf m sl pl v (Q : TS CT -> Prop),
      evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = false ->
      Q (mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA m pl v)) rf) m sl) ->
      evalActionPropGen envC (@specCompleteLoad pcAddrInit config specRegions type pl v) (mkCoreA rf m sl)
        (fun sc' _ => Q sc').
  Proof.
    intros envC rf m sl pl v Q Erl HQ.
    unfold specCompleteLoad.
    apply ev_letL; cbv beta.
    apply ev_ifElse_false; [exact Erl |].
    apply ev_letExp; cbv beta.
    apply (wbIf_wp envC); intros r; cbv beta.
    apply ev_return.
    rewrite (specLoadWb_wb m pl v Erl) in HQ; cbv zeta in HQ.
    exact HQ.
  Qed.

  Lemma specCompleteLoad_wp :
    forall (envC : Env CT) rf m sl pl v (Q : TS CT -> Prop),
      CEOK envC ->
      (forall m', ReadFrameS specRegions m m' ->
         Q (mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA m pl v)) rf) m' sl)) ->
      evalActionPropGen envC (@specCompleteLoad pcAddrInit config specRegions type pl v) (mkCoreA rf m sl)
        (fun sc' _ => Q sc').
  Proof.
    intros envC rf m sl pl v Q Henv HQ.
    assert (Hdec : evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = true \/
                   evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = false)
      by (destruct (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup"));
          [left | right]; reflexivity).
    destruct Hdec as [Erl | Erl].
    - exact (completeLoad_rev_wp envC rf m sl pl v Q Henv Erl HQ).
    - exact (completeLoad_wb_wp envC rf m sl pl v Q Erl (HQ m (ReadFrameS_refl specRegions m))).
  Qed.

  (* The deferred part of a load entry: the first line is read; a crossing load records its second
   * line, any other completes (register write `specLoadWb`) *)
  Lemma deferred_load_wp :
    forall (envC : Env CT) rfC m sl (d : type (Bit RegIdxSzReal)) (a : type Addr) (dm : type (Option MemFenceUnion))
           (md : type (Option MulDivUnion)) ld (Q : TS CT -> Prop),
      CEOK envC ->
      optValid dm = true -> opIsLoad (optData dm) = true ->
      ld = loadCmdOf (d ,, (a ,, (optData dm ,, tt))) ->
      lineKind specRegions (lineOf false (ldAddr ld)) = Some true ->
      (forall m', ReadFrameS specRegions m m' ->
         if crossesB (ldAddr ld) (plSize (ldPending ld))
         then Q (mkCoreA rfC m' (secondLoadOf ld (specPkt (ldAddr ld) (lineContentS m (lineOf false (ldAddr ld))))))
         else Q (mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA m (ldPending ld)
                  (singleLoadVal ld (lineContentS m (lineOf false (ldAddr ld)))))) rfC) m' sl)) ->
      evalActionPropGen envC (@specExecuteDeferred pcAddrInit config specRegions type d a dm md)
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl d a dm md ld Q Henv Hv Hld Eld Hk HQ.
    destruct (dispatchMemFence_load d a (optData dm) Hld) as [Hmem Hst].
    unfold specExecuteDeferred.
    apply ev_ifElse_true; [exact Hv |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_ifElse_true; [exact Hmem |].
    apply ev_letExp; cbv beta.
    apply ev_ifElse_false; [exact Hst |].
    apply ev_letExpGen; intros ldv Eldv.
    assert (E : ldv = ld) by (rewrite Eldv, Eld; reflexivity).
    clear Eldv; subst ldv.
    do 3 (apply ev_letExp; cbv beta).
    apply core_memAct_wp.
    apply (specMemReadFirstLine_wp initLine _ _ specRegions fwcs); [apply Henv | exact Hk | apply lineUnique_specL |].
    intros m1 Hm1; cbv beta.
    apply ev_letL; cbv beta.
    pose proof (HQ m1 Hm1) as HQ1.
    assert (Hdec : crossesB (ldAddr ld) (plSize (ldPending ld)) = true \/ crossesB (ldAddr ld) (plSize (ldPending ld)) = false)
      by (destruct (crossesB (ldAddr ld) (plSize (ldPending ld))); [left | right]; reflexivity).
    destruct Hdec as [Ecr | Ecr]; rewrite Ecr in HQ1.
    - apply ev_ifElse_true; [exact Ecr |].
      apply ev_letExp; cbv beta.
      apply writeSecondLine_wp; intros r; cbv beta.
      repeat (apply ev_return; cbv beta).
      exact HQ1.
    - apply ev_ifElse_false; [exact Ecr |].
      apply ev_letL; cbv beta.
      eapply evalActionPropGen_mono; [| apply (specCompleteLoad_wp envC rfC m1 sl _ _ (fun sc => Q sc) Henv)].
      + intros sc' r HQ'; cbv beta; repeat (apply ev_return; cbv beta); exact HQ'.
      + intros m2 Hm2; cbv beta.
        pose proof (HQ m2 (ReadFrameS_trans specRegions _ _ _ Hm1 Hm2)) as HQ2; rewrite Ecr in HQ2.
        rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine m m1 _ _
                   (lineContent_readFrame initLine specRegions m m1 Hm1)).
        exact HQ2.
  Qed.
  (* --- 3b. `specStep` for a load at the head of the chain --- *)

  (* The first line of load `ld` in spec memory `m`, and the spec's register file and `secondLine`
   * after the load's step (`rf1`: the register file after the entry's execute step) *)
  Definition ldRp0 (m : TS (specMemTree specRegions)) (ld : type LoadCmd) : type LineReadRp :=
    lineContentS m (lineOf false (ldAddr ld)).
  Definition ldCommitRf (m : TS (specMemTree specRegions)) (ld : type LoadCmd) (rf1 : RfState pcAddrInit)
    : RfState pcAddrInit :=
    if crossesB (ldAddr ld) (plSize (ldPending ld)) then rf1
    else cnwbApply pcAddrInit (Some (specLoadWbA m (ldPending ld) (singleLoadVal ld (ldRp0 m ld)))) rf1.
  Definition ldCommitSl (m : TS (specMemTree specRegions)) (ld : type LoadCmd) (sl : type (Option SecondLine))
    : type (Option SecondLine) :=
    if crossesB (ldAddr ld) (plSize (ldPending ld)) then secondLoadOf ld (specPkt (ldAddr ld) (ldRp0 m ld)) else sl.

  Lemma specMulDivWb_dmValid :
    forall a x rf, optValid (execDataMem x) = true -> specMulDivWb pcAddrInit a x rf = rf.
  Proof. intros a x rf H; unfold specMulDivWb, optValid in *; cbv zeta; rewrite H; reflexivity. Qed.

  Lemma entryReq_some :
    forall e q, entryReq e = Some q ->
      optValid (ge_dm e) = true /\
      q =(aluDstIdx (ge_aluOut e) ,, ((aluDstVal (ge_aluOut e)).(Snd).(Snd).(Fst) ,, (optData (ge_dm e) ,, tt))).
  Proof.
    intros e q Hq; unfold entryReq in Hq.
    destruct (optValid (ge_dm e)); [injection Hq as <-; split; reflexivity | discriminate Hq].
  Qed.

  Lemma specStep_load :
    forall rf0 rf1 m sl e q,
      GInstStep pcAddrInit rf0 rf1 e ->
      entryReq e = Some q -> opIsLoad (mrOp q) = true ->
      SpecNoWait specRegions m -> optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      lineKind specRegions (lineOf false (ldAddr (loadCmdOf q))) = Some true ->
      exists m', TraceFrameS specRegions m m' /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSysA rf0 m sl) (mkSysA (ldCommitRf m (loadCmdOf q) rf1) m' (ldCommitSl m (loadCmdOf q) sl)) Zmod.zero.
  Proof.
    intros rf0 rf1 m sl e q [Hvc [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]]] Hq Hld Hnw Hsl Hfa Hmt Hme Hk.
    destruct (entryReq_some e q Hq) as [Hv Eq].
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSysA (cnwbApply pcAddrInit None rf0) m sl)
                    (fun s2' _ => exists m', TraceFrameS specRegions m m' /\
                       s2'.(Fst) = mkCoreA (ldCommitRf m (loadCmdOf q) rf1) m' (ldCommitSl m (loadCmdOf q) sl))).
    { apply specStep_wp with (Hdisj := Hdisj) (e := e) (rfMid := rfMid) (execOut := execOut)
        (Q := fun sc => exists m', TraceFrameS specRegions m m' /\
                 sc = mkCoreA (ldCommitRf m (loadCmdOf q) rf1) m' (ldCommitSl m (loadCmdOf q) sl));
        try assumption.
      - intros d v Hc; discriminate Hc.
      - intros m1 envC aluOut rfC HenvC Hm1 Ha Hrf.
        subst aluOut.
        assert (Erf : rfC = rf1).
        { rewrite Hrf, Hrf1, specMulDivWb_dmValid by (rewrite Hdm; exact Hv).
          rewrite defNextPcc_eq; reflexivity. }
        apply (deferred_load_wp envC rfC m1 sl _ _ _ _ (loadCmdOf q) _ HenvC).
        + rewrite defDm_eq, Hdm; exact Hv.
        + rewrite defDm_eq, Hdm; rewrite Eq in Hld; exact Hld.
        + rewrite defDst_eq, defAddr_eq, defDm_eq, Hdm, Eq; reflexivity.
        + exact Hk.
        + intros m2 Hm2.
          assert (Hdec : crossesB (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q))) = true \/
                         crossesB (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q))) = false)
            by (destruct (crossesB (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q)))); [left | right]; reflexivity).
          assert (Hm12 : TraceFrameS specRegions m m2)
            by exact (TraceFrameS_trans specRegions _ _ _ Hm1 (TraceFrameS_readFrame specRegions _ _ Hm2)).
          rewrite (lineContent_traceFrame initLine specRegions m m1 Hm1).
          unfold ldCommitRf, ldCommitSl, ldRp0.
          destruct Hdec as [Ecr | Ecr]; rewrite !Ecr.
          * exists m2; split; [exact Hm12 | rewrite Erf; reflexivity].
          * exists m2; split; [exact Hm12 |].
            rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine m m1 _ _
                       (lineContent_traceFrame initLine specRegions m m1 Hm1)).
            rewrite Erf; reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [m' [Hm' E]]]]].
    exists m'; split; [exact Hm' |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.
  (* --- 3c. `specSecondLine` for the second line of a crossing load --- *)

  Lemma secondLine_load_wp :
    forall (envC : Env CT) rf m ld pkt0 (Q : TS CT -> Prop),
      CEOK envC ->
      lineKind specRegions (lineOf true (ldAddr ld)) = Some true ->
      (forall m', ReadFrameS specRegions m m' ->
         Q (mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA m (ldPending ld)
               (mergedLoadVal ld pkt0 (lineContentS m (lineOf true (ldAddr ld)))))) rf) m'
               (getDefault (Option SecondLine)))) ->
      evalActionPropGen envC (@specSecondLineStep pcAddrInit config specRegions type)
        (mkCoreA rf m (secondLoadOf ld pkt0)) (fun sc' _ => Q sc').
  Proof.
    intros envC rf m ld pkt0 Q Henv Hk HQ.
    unfold specSecondLineStep.
    apply ev_letAction; apply (readSecondLine_wp pcAddrInit pre post revBase revPfB revPfA); cbv beta.
    apply ev_ifElse_true; [reflexivity |].
    apply ev_letExpGen; intros sv Esv.
    assert (Ed : sv = evalExpr (UNION (SecondLineType, "Load" ::=
                                 Var type SecondLineLoad (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt))))))
      by (rewrite Esv; reflexivity).
    clear Esv; subst sv.
    apply ev_ifElse_false; [reflexivity |].
    apply ev_letExpGen; intros lv Elv.
    assert (El : lv = (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt)))).
    { rewrite Elv.
      exact (evalExpr_ReadUnionData_BuildUnion SecondLineType (@Build_FinType 2 0 I)
               (Var type SecondLineLoad (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt)))) eq_refl). }
    clear Elv; subst lv.
    do 4 (apply ev_letExp; cbv beta).
    apply core_memAct_wp.
    apply (specMemReadSecondLine_wp initLine _ _ specRegions fwcs); [apply Henv | exact Hk | apply lineUnique_specL |].
    intros m1 Hm1; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply (specCompleteLoad_wp envC); [exact Henv |].
    intros m2 Hm2.
    apply writeSecondLine_wp; intros r; cbv beta.
    apply ev_return.
    pose proof (HQ m2 (ReadFrameS_trans specRegions _ _ _ Hm1 Hm2)) as HQ2.
    rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine m m1 _ _
               (lineContent_readFrame initLine specRegions m m1 Hm1)).
    exact HQ2.
  Qed.
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).

  Lemma In_specSecondLine_spec : In (@specSecondLine pcAddrInit config specRegions type) specActs.
  Proof.
    refine (eq_ind_r (fun L => In _ L) _ (map_snd_specMod pcAddrInit config specRegions clintS revSpec plicS)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; do 6 right; left; reflexivity.
  Qed.

  (* The value the second line of crossing load `ld` (first-line packet `pkt0`) commits in memory `m` *)
  Definition ldMergedWb (m : TS (specMemTree specRegions)) (ld : type LoadCmd) (pkt0 : type CapPacket) :=
    specLoadWbA m (ldPending ld) (mergedLoadVal ld pkt0 (lineContentS m (lineOf true (ldAddr ld)))).

  Lemma specSecondLine_load :
    forall rf m ld pkt0,
      lineKind specRegions (lineOf true (ldAddr ld)) = Some true ->
      exists m', ReadFrameS specRegions m m' /\
        SemAction envS (@specSecondLine pcAddrInit config specRegions type)
          (mkSysA rf m (secondLoadOf ld pkt0))
          (mkSysA (cnwbApply pcAddrInit (Some (ldMergedWb m ld pkt0)) rf) m' (getDefault (Option SecondLine)))
          Zmod.zero.
  Proof.
    intros rf m ld pkt0 Hk.
    assert (Hev : evalActionPropGen envS (@specSecondLine pcAddrInit config specRegions type)
                    (mkSysA rf m (secondLoadOf ld pkt0))
                    (fun s2' _ => exists m', ReadFrameS specRegions m m' /\
                       s2'.(Fst) = mkCoreA (cnwbApply pcAddrInit (Some (ldMergedWb m ld pkt0)) rf) m'
                                     (getDefault (Option SecondLine)))).
    { unfold specSecondLine.
      apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
      eapply evalActionPropGen_mono;
        [| apply (secondLine_load_wp _ rf m ld pkt0
                    (fun sc => exists m', ReadFrameS specRegions m m' /\
                       sc = mkCoreA (cnwbApply pcAddrInit (Some (ldMergedWb m ld pkt0)) rf) m'
                              (getDefault (Option SecondLine))))].
      - intros sc r H; exact H.
      - apply coreEnvOK.
      - exact Hk.
      - intros m' Hm'; exists m'; split; [exact Hm' | reflexivity]. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [m' [Hm' E]]]]].
    exists m'; split; [exact Hm' |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.
End LoadSpec.
