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

(* Spec side of the load commit (milestone 4), the parts that build. The draft of the rest
 * (dispatchMemFence_load, loadCmdOf_dst, loadOutcome_facts, specLoadWb_dst, specCompleteLoad_wp,
 * deferred_load_wp) is in RefLoadCommit.v.wip, which is not built. *)

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot Require Import SpecDefines SpecDevice SpecFetchDeferred Spec Clint Plic Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefSpecRead RefSpecFetch RefRevTable RefReplay.

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
  match goal with |- context [evalExpr (ReadUnionData (Var ?ty ?k ?u) ?i)] =>
    let w := strip_var u in
    lazymatch w with evalExpr (BuildUnion _ (Var _ _ ?x)) =>
      replace (evalExpr (ReadUnionData (Var ty k u) i)) with x
        by (symmetry; exact (evalExpr_ReadUnionData_BuildUnion _ i (Var _ _ x) eq_refl))
    end
  end.

(* Fix the store/load case of the memory operation inside `dispatchMemFence` *)
Ltac store_case Hs :=
  match goal with |- context [evalExpr (ReadUnionTag (Var ?ty ?k ?x) ?j)] =>
    idtac "CAND" k;
    assert (Hs' : evalExpr (ReadUnionTag (Var ty k x) j) = false) by (first [exact Hs | idtac "EXACTFAIL"; fail]);
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




Lemma isNotZero_expr :
  forall sz (e : Expr type (Bit sz)), evalExpr (isNotZero e) = negb (Zmod.eqb (evalExpr e) Zmod.zero).
Proof.
  intros sz e.
  destruct (Zmod.eqb (evalExpr e) Zmod.zero) eqn:E; cbn [negb].
  - destruct (evalExpr (isNotZero e)) eqn:F; [| reflexivity].
    apply (proj1 (isNotZero_true_iff (evalExpr e))) in F; rewrite F in E; discriminate E.
  - apply (proj2 (isNotZero_true_iff (evalExpr e))); exact E.
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



  Lemma writeSecondLine_wp :
    forall (env : Env CT) rf m sl (v : Expr type (Option SecondLine)) P,
      (forall r, P (mkCoreA rf m (evalExpr v)) r) ->
      evalActionPropGen env (@writeSecondLine pcAddrInit specRegions type v) (mkCoreA rf m sl) P.
  Proof. intros env rf m sl v P HP; exact (HP _). Qed.

  (* The deferred part of a load entry: the first line is read; a crossing load records its second
   * line, any other completes (register write `specLoadWb`) *)
End LoadSpec.
