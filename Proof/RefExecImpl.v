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

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute SimDataMem GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead RefSpecFetch RefRevoker RefReplay.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7: THE IMPL SIDE OF `aluAndExecuteNonDeferredStage`
 * ===========================================================================
 * One lemma per branch of `aluAndExecuteNonDeferred` (Impl/ImplExecute.v): from the stage's
 * `SemAction` and the branch condition, what the step does to each part of the impl state that
 * the relation reads. The action is stepped one constructor at a time on the hypothesis
 * (`fw_*` lemmas), never unfolded as a whole (guide 3.2). *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. One Forward Step of an Action Hypothesis --- *)

Section Forward.
  Context {t : Tree Elem} (env : Env t).

  Lemma fw_letExp :
    forall {k k'} s (e : Expr type k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (LetExp s e cont) old P -> evalActionPropGen env (cont (evalExpr e)) old P.
  Proof. intros k k' s e cont old P H; exact H. Qed.

  (* A `Let` whose value is given by name (the equation is proven once, on a small goal) *)
  Lemma fw_letExpV :
    forall {k k'} s (e : Expr type k') (cont : type k' -> Action type t k) old P (v : type k'),
      evalExpr e = v -> evalActionPropGen env (LetExp s e cont) old P -> evalActionPropGen env (cont v) old P.
  Proof. intros k k' s e cont old P v E H; rewrite <- E; exact H. Qed.

  Lemma fw_letL :
    forall {k k'} s (le : LetExpr type k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (LetAction s (@toAction type t k' le) cont) old P ->
      evalActionPropGen env (cont (evalLetExpr le)) old P.
  Proof.
    intros k k' s le cont old P H; cbn [evalActionPropGen] in H.
    exact (proj1 (evalActionPropGen_toAction le old _) H).
  Qed.

  Lemma fw_letAction :
    forall {k k'} s (a : Action type t k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (LetAction s a cont) old P ->
      evalActionPropGen env a old (fun s' r => evalActionPropGen env (cont r) s' P).
  Proof. intros k k' s a cont old P H; exact H. Qed.

  Lemma fw_lift :
    forall {k k'} s (p : NodePath t) (a : Action type (getNode p) k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (LetAction s (liftAction p a) cont) old P ->
      evalActionPropGen (subEnv p env old) a (readSubTreeState p old)
        (fun x r => evalActionPropGen env (cont r) (writeSubTreeState p old x) P).
  Proof.
    intros k k' s p a cont old P H; cbn [evalActionPropGen] in H.
    exact (proj1 (evalActionPropGen_liftAction p a old _) H).
  Qed.

  Lemma fw_ifTrue :
    forall {k k'} s (p : Expr type Bool) (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
      evalExpr p = true ->
      evalActionPropGen env (IfElse s p tb fb cont) old P ->
      evalActionPropGen env tb old (fun s' r => evalActionPropGen env (cont r) s' P).
  Proof. intros k k' s p tb fb cont old P Hp H; cbn [evalActionPropGen] in H; rewrite Hp in H; exact H. Qed.

  Lemma fw_ifFalse :
    forall {k k'} s (p : Expr type Bool) (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
      evalExpr p = false ->
      evalActionPropGen env (IfElse s p tb fb cont) old P ->
      evalActionPropGen env fb old (fun s' r => evalActionPropGen env (cont r) s' P).
  Proof. intros k k' s p tb fb cont old P Hp H; cbn [evalActionPropGen] in H; rewrite Hp in H; exact H. Qed.

  Lemma fw_return :
    forall {k} (e : Expr type k) old P, evalActionPropGen env (Return e) old P -> P old (evalExpr e).
  Proof. intros k e old P H; exact H. Qed.

  (* A `LetL` whose value becomes a fresh variable: conversions can then never evaluate it *)
  Lemma fw_letLGen :
    forall {k k'} s (le : LetExpr type k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (LetAction s (@toAction type t k' le) cont) old P ->
      exists v, v = evalLetExpr le /\ evalActionPropGen env (cont v) old P.
  Proof.
    intros k k' s le cont old P H; apply fw_letL in H.
    exists (evalLetExpr le); split; [reflexivity | exact H].
  Qed.

  (* An `If`, split into its two branches *)
  Lemma fw_ifTF :
    forall {k k'} s (c : Expr type Bool) (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (IfElse s c tb fb cont) old P ->
      (evalExpr c = true /\ evalActionPropGen env tb old (fun s' r => evalActionPropGen env (cont r) s' P)) \/
      (evalExpr c = false /\ evalActionPropGen env fb old (fun s' r => evalActionPropGen env (cont r) s' P)).
  Proof.
    intros k k' s c tb fb cont old P H; cbn [evalActionPropGen] in H.
    destruct (evalExpr c); [left | right]; (split; [reflexivity | exact H]).
  Qed.

  (* `apply L in H` matches `H` against `L`'s premises from right to left; a failed match makes
   * Coq reduce `H`'s action to weak head normal form (it evaluates the action).  So every
   * lemma here takes the action hypothesis as its LAST premise. *)

  (* A read-only sub-action whose value is known *)
  Lemma fw_read :
    forall {k} (a : Action type t k) old (v : type k) P,
      (forall old' r, SemAction env a old old' r -> old' = old /\ r = v) ->
      evalActionPropGen env a old P -> P old v.
  Proof.
    intros k a old v P Hc H.
    destruct (evalActionPropGen_to_SemAction a old P H) as [old' [r [Hs HP]]].
    destruct (Hc old' r Hs) as [-> ->]; exact HP.
  Qed.

  (* `p`'s sub-state updated by `f`.  Kept folded: unfolded, the old state occurs twice, and a
   * chain of steps would double the term at each step. *)
  Definition updSub (p : NodePath t) (f : TS (getNode p) -> TS (getNode p)) (old : TS t) : TS t :=
    writeSubTreeState p old (f (readSubTreeState p old)).

  (* A lifted sub-action that reads only: the state is unchanged *)
  Lemma fw_liftRead :
    forall {k k'} s (p : NodePath t) (a : Action type (getNode p) k') (cont : type k' -> Action type t k) old
           (g : TS (getNode p) -> type k') P,
      (forall env' sub Q, evalActionPropGen env' a sub Q -> Q sub (g sub)) ->
      evalActionPropGen env (LetAction s (liftAction p a) cont) old P ->
      evalActionPropGen env (cont (g (readSubTreeState p old))) old P.
  Proof.
    intros k k' s p a cont old g P Hr H.
    apply fw_lift in H; specialize (Hr _ _ _ H); cbv beta in Hr.
    rewrite writeSubTreeState_readSubTreeState in Hr; exact Hr.
  Qed.

  (* A lifted sub-action that updates its sub-state by a known function *)
  Lemma fw_liftUpd :
    forall {k k'} s (p : NodePath t) (a : Action type (getNode p) k') (cont : type k' -> Action type t k) old
           (f : TS (getNode p) -> TS (getNode p)) (g : TS (getNode p) -> type k') P,
      (forall env' sub Q, evalActionPropGen env' a sub Q -> Q (f sub) (g sub)) ->
      evalActionPropGen env (LetAction s (liftAction p a) cont) old P ->
      evalActionPropGen env (cont (g (readSubTreeState p old))) (updSub p f old) P.
  Proof.
    intros k k' s p a cont old f g P Hr H.
    apply fw_lift in H; exact (Hr _ _ _ H).
  Qed.

  (* The same, as the last action of a block *)
  Lemma fw_liftUpdLast :
    forall {k'} (p : NodePath t) (a : Action type (getNode p) k') old
           (f : TS (getNode p) -> TS (getNode p)) (g : TS (getNode p) -> type k') P,
      (forall env' sub Q, evalActionPropGen env' a sub Q -> Q (f sub) (g sub)) ->
      evalActionPropGen env (liftAction p a) old P ->
      P (updSub p f old) (g (readSubTreeState p old)).
  Proof.
    intros k' p a old f g P Hr H.
    apply (proj1 (evalActionPropGen_liftAction p a old _)) in H; exact (Hr _ _ _ H).
  Qed.

  (* A lifted sub-action, by its `SemAction` (the new sub-state is a fresh variable) *)
  Lemma fw_liftSem :
    forall {k k'} s (p : NodePath t) (a : Action type (getNode p) k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (LetAction s (liftAction p a) cont) old P ->
      exists sub' r, SemAction (subEnv p env old) a (readSubTreeState p old) sub' r /\
                evalActionPropGen env (cont r) (writeSubTreeState p old sub') P.
  Proof.
    intros k k' s p a cont old P H.
    apply fw_lift in H.
    destruct (evalActionPropGen_to_SemAction a _ _ H) as [sub' [r [Hs HP]]].
    exists sub', r; split; [exact Hs | exact HP].
  Qed.

  (* `If c Then (liftAction p a)`: some update of `p`'s sub-state *)
  Lemma fw_ifLiftAny :
    forall {k k'} s (c : Expr type Bool) (p : NodePath t) (a : Action type (getNode p) k') (e : Expr type k')
           (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (IfElse s c (liftAction p a) (Return e) cont) old P ->
      exists sub' r, evalActionPropGen env (cont r) (writeSubTreeState p old sub') P.
  Proof.
    intros k k' s c p a e cont old P H; cbn [evalActionPropGen] in H.
    destruct (evalExpr c).
    - apply (proj1 (evalActionPropGen_liftAction p a old _)) in H.
      destruct (evalActionPropGen_to_SemAction a _ _ H) as [sub' [r [_ HP]]].
      exists sub', r; exact HP.
    - exists (readSubTreeState p old), (evalExpr e).
      rewrite writeSubTreeState_readSubTreeState; exact H.
  Qed.

  (* Any `If`: the state after it is a fresh variable, given by the branch taken *)
  Lemma fw_ifJoin :
    forall {k k'} s (c : Expr type Bool) (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
      evalActionPropGen env (IfElse s c tb fb cont) old P ->
      exists old' r, SemAction env (if evalExpr c then tb else fb) old old' r /\
                evalActionPropGen env (cont r) old' P.
  Proof.
    intros k k' s c tb fb cont old P H; cbn [evalActionPropGen] in H.
    destruct (evalExpr c); exact (evalActionPropGen_to_SemAction _ _ _ H).
  Qed.
End Forward.

(* A read-only action, from its `SemAction` characterization *)
Lemma read_of_sem :
  forall {t : Tree Elem} {k} (a : Action type t k) (g : TS t -> type k),
    (forall env' sub sub' r, SemAction env' a sub sub' r -> sub' = sub /\ r = g sub) ->
    forall env' sub Q, evalActionPropGen env' a sub Q -> Q sub (g sub).
Proof.
  intros t k a g Hs env' sub Q H.
  destruct (evalActionPropGen_to_SemAction a sub Q H) as [sub' [r [Ha HQ]]].
  destruct (Hs env' sub sub' r Ha) as [-> ->]; exact HQ.
Qed.

(* An updating action, from its `SemAction` characterization *)
Lemma upd_of_sem :
  forall {t : Tree Elem} {k} (a : Action type t k) (f : TS t -> TS t) (g : TS t -> type k),
    (forall env' sub sub' r, SemAction env' a sub sub' r -> sub' = f sub /\ r = g sub) ->
    forall env' sub Q, evalActionPropGen env' a sub Q -> Q (f sub) (g sub).
Proof.
  intros t k a f g Hs env' sub Q H.
  destruct (evalActionPropGen_to_SemAction a sub Q H) as [sub' [r [Ha HQ]]].
  destruct (Hs env' sub sub' r Ha) as [-> ->]; exact HQ.
Qed.

(* --- 2. The mulDiv Interface, per Mode --- *)

Section MulDivIfc.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.

  Local Abbreviation MDT := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).

  (* `isFull` of the request FIFO a Mul / a Div goes to *)
  Definition mdFullMul (smd : TS MDT) : bool :=
    match mulDivMode as m
      return TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) -> bool
    with
    | PipelinedMul_IterDiv => fun s => Zmod.eqb (fifo_size s.(Fst).(Fst)) (Zmod.of_Z _ (Z.of_nat mulCapacity))
    | IterMul_SeparateIterDiv => fun s => Zmod.eqb (fifo_size s.(Fst).(Fst)) (Zmod.of_Z _ (Z.of_nat mulCapacity))
    | IterMul_SharedIterDiv => fun s => Zmod.eqb (fifo_size s.(Fst)) (Zmod.of_Z _ (Z.of_nat mulCapacity))
    end smd.

  Definition mdFullDiv (smd : TS MDT) : bool :=
    match mulDivMode as m
      return TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) -> bool
    with
    | PipelinedMul_IterDiv => fun s => Zmod.eqb (fifo_size s.(Snd).(Fst).(Fst)) (Zmod.of_Z _ (Z.of_nat divCapacity))
    | IterMul_SeparateIterDiv => fun s => Zmod.eqb (fifo_size s.(Snd).(Fst).(Fst)) (Zmod.of_Z _ (Z.of_nat divCapacity))
    | IterMul_SharedIterDiv => fun s => Zmod.eqb (fifo_size s.(Fst)) (Zmod.of_Z _ (Z.of_nat mulCapacity))
    end smd.

  Lemma mdFullMul_sem :
    forall env (smd smd' : TS MDT) r,
      SemAction env (@mulDivIsFullMul mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode type) smd smd' r ->
      smd' = smd /\ r = mdFullMul smd.
  Proof.
    intros env smd smd' r H; rewrite SemAction_iff_evalActionPropGen in H.
    unfold mdFullMul, mulDivIsFullMul in *; revert smd smd' r env H; destruct mulDivMode; intros smd smd' r env H;
      rewrite !evalActionPropGen_liftAction in H; cbn [evalActionPropGen isFull] in H;
      destruct H as [<- <-]; split; reflexivity.
  Qed.

  Lemma mdFullDiv_sem :
    forall env (smd smd' : TS MDT) r,
      SemAction env (@mulDivIsFullDiv mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode type) smd smd' r ->
      smd' = smd /\ r = mdFullDiv smd.
  Proof.
    intros env smd smd' r H; rewrite SemAction_iff_evalActionPropGen in H.
    unfold mdFullDiv, mulDivIsFullDiv in *; revert smd smd' r env H; destruct mulDivMode; intros smd smd' r env H;
      rewrite !evalActionPropGen_liftAction in H; cbn [evalActionPropGen isFull] in H;
      destruct H as [<- <-]; split; reflexivity.
  Qed.

  (* `enq` on a FIFO under a lift: the tree index is `getNode p`, so give `cap k` explicitly *)
  Local Ltac md_enq H :=
    match type of H with
    | context [@ShiftFifo.enq ?c ?kk _ _] => rewrite (evalActionPropGen_enq_iff c kk) in H
    end.

  (* The requests the enqueue actions build *)
  Definition mulReqV (dst : type RegIdx) (op1 : type Addr) (mOp : type MulOp) : type MulReq :=
    evalExpr (STRUCT { "dstIdx" ::= #dst ; "op1" ::= #op1 ; "mulOp" ::= #mOp } : Expr type MulReq).
  Definition divReqV (dst : type RegIdx) (op1 : type Addr) (dOp : type DivOp) : type DivReq :=
    evalExpr (STRUCT { "dstIdx" ::= #dst ; "op1" ::= #op1 ; "divOp" ::= #dOp } : Expr type DivReq).
  Definition mulDivReqV (dst : type RegIdx) (op1 : type Addr) (mdOp : type MulDivUnion) : type MulDivReq :=
    evalExpr (STRUCT { "dstIdx" ::= #dst ; "op1" ::= #op1 ; "mulDivOp" ::= #mdOp } : Expr type MulDivReq).
  Definition mulUnionV (mOp : type MulOp) : type MulDivUnion :=
    evalExpr (UNION (MulDivType, "Mul" ::= #mOp) : Expr type MulDivUnion).
  Definition divUnionV (dOp : type DivOp) : type MulDivUnion :=
    evalExpr (UNION (MulDivType, "Div" ::= #dOp) : Expr type MulDivUnion).

  (* `enqMul` / `enqDiv` on the mulDiv subtree *)
  Definition mdEnqMul (dst : type RegIdx) (op1 : type Addr) (mOp : type MulOp) (smd : TS MDT) : TS MDT :=
    match mulDivMode as m
      return TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) ->
             TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m)
    with
    | PipelinedMul_IterDiv =>
        fun s => ((fifoEnqState s.(Fst).(Fst) (mulReqV dst op1 mOp) ,, s.(Fst).(Snd)) ,, s.(Snd))
    | IterMul_SeparateIterDiv =>
        fun s => ((fifoEnqState s.(Fst).(Fst) (mulReqV dst op1 mOp) ,, s.(Fst).(Snd)) ,, s.(Snd))
    | IterMul_SharedIterDiv =>
        fun s => (fifoEnqState s.(Fst) (mulDivReqV dst op1 (mulUnionV mOp)) ,, s.(Snd))
    end smd.

  Definition mdEnqDiv (dst : type RegIdx) (op1 : type Addr) (dOp : type DivOp) (smd : TS MDT) : TS MDT :=
    match mulDivMode as m
      return TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) ->
             TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m)
    with
    | PipelinedMul_IterDiv =>
        fun s => (s.(Fst) ,, ((fifoEnqState s.(Snd).(Fst).(Fst) (divReqV dst op1 dOp) ,, s.(Snd).(Fst).(Snd)) ,, s.(Snd).(Snd)))
    | IterMul_SeparateIterDiv =>
        fun s => (s.(Fst) ,, ((fifoEnqState s.(Snd).(Fst).(Fst) (divReqV dst op1 dOp) ,, s.(Snd).(Fst).(Snd)) ,, s.(Snd).(Snd)))
    | IterMul_SharedIterDiv =>
        fun s => (fifoEnqState s.(Fst) (mulDivReqV dst op1 (divUnionV dOp)) ,, s.(Snd))
    end smd.

  Lemma mdEnqMul_sem :
    forall dst op1 mOp env (smd smd' : TS MDT) r,
      SemAction env (@mulDivEnqMul mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode type dst op1 mOp)
        smd smd' r ->
      smd' = mdEnqMul dst op1 mOp smd /\ r = Zmod.zero.
  Proof.
    intros dst op1 mOp env smd smd' r H; rewrite SemAction_iff_evalActionPropGen in H.
    unfold mdEnqMul, mulDivEnqMul in *; revert smd smd' r env H; destruct mulDivMode; intros smd smd' r env H;
      cbn [evalActionPropGen] in H; rewrite !evalActionPropGen_liftAction in H;
      md_enq H; destruct H as [<- <-]; split; reflexivity.
  Qed.

  Lemma mdEnqDiv_sem :
    forall dst op1 dOp env (smd smd' : TS MDT) r,
      SemAction env (@mulDivEnqDiv mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode type dst op1 dOp)
        smd smd' r ->
      smd' = mdEnqDiv dst op1 dOp smd /\ r = Zmod.zero.
  Proof.
    intros dst op1 dOp env smd smd' r H; rewrite SemAction_iff_evalActionPropGen in H.
    unfold mdEnqDiv, mulDivEnqDiv in *; revert smd smd' r env H; destruct mulDivMode; intros smd smd' r env H;
      cbn [evalActionPropGen] in H; rewrite !evalActionPropGen_liftAction in H;
      md_enq H; destruct H as [<- <-]; split; reflexivity.
  Qed.
End MulDivIfc.

(* --- 3. What the Stage Computes from the ALU Output (mirrors the stage's `Let`s) --- *)

Definition aluIsSeq (aluOut : type AluOutUnion) : bool :=
  let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
  evalExpr (#aluOp `? "Sequential").

Definition aluIsMul (aluOut : type AluOutUnion) : bool :=
  let aluOp    : type AluOpUnion      := evalExpr (##aluOut`"Op") in
  let isSeq    : type Bool                 := evalExpr (#aluOp `? "Sequential") in
  let seqOp    : type SequentialUnion := evalExpr (#aluOp `! "Sequential") in
  let isMulDiv : type Bool                 := evalExpr (And [ #isSeq ; #seqOp `? "MulDiv" ]) in
  let mulDivOp : type MulDivUnion     := evalExpr (#seqOp `! "MulDiv") in
  evalExpr (And [ #isMulDiv ; #mulDivOp `? "Mul" ]).

Definition aluIsDiv (aluOut : type AluOutUnion) : bool :=
  let aluOp    : type AluOpUnion      := evalExpr (##aluOut`"Op") in
  let isSeq    : type Bool                 := evalExpr (#aluOp `? "Sequential") in
  let seqOp    : type SequentialUnion := evalExpr (#aluOp `! "Sequential") in
  let isMulDiv : type Bool                 := evalExpr (And [ #isSeq ; #seqOp `? "MulDiv" ]) in
  let mulDivOp : type MulDivUnion     := evalExpr (#seqOp `! "MulDiv") in
  evalExpr (And [ #isMulDiv ; #mulDivOp `? "Div" ]).

Definition aluIsExc (aluOut : type AluOutUnion) : bool :=
  let aluOp    : type AluOpUnion         := evalExpr (##aluOut`"Op") in
  let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
  let isNonSeq : type Bool                    := evalExpr (#aluOp `? "NonSequential") in
  evalExpr (And [ #isNonSeq ; #nonSeqOp `? "Exception" ]).

Definition aluIsMemOrFence (aluOut : type AluOutUnion) : bool :=
  let aluOp    : type AluOpUnion         := evalExpr (##aluOut`"Op") in
  let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
  let isNonSeq : type Bool                    := evalExpr (#aluOp `? "NonSequential") in
  let isNoExc  : type Bool                    := evalExpr (And [ #isNonSeq ; #nonSeqOp `? "NoException" ]) in
  let noExc    : type NoExceptionUnion   := evalExpr (#nonSeqOp `! "NoException") in
  evalExpr (And [ #isNoExc ; #noExc `? "DataMem" ]).

Definition aluIsVirtCsr (aluOut : type AluOutUnion) : bool :=
  let aluOp      : type AluOpUnion              := evalExpr (##aluOut`"Op") in
  let nonSeqOp   : type NonSequentialUnion      := evalExpr (#aluOp `! "NonSequential") in
  let isNonSeq   : type Bool                         := evalExpr (#aluOp `? "NonSequential") in
  let isNoExc    : type Bool                         := evalExpr (And [ #isNonSeq ; #nonSeqOp `? "NoException" ]) in
  let noExc      : type NoExceptionUnion        := evalExpr (#nonSeqOp `! "NoException") in
  let isCfScrCsr : type Bool                         := evalExpr (And [ #isNoExc ; #noExc `? "CfScrCsr" ]) in
  let cfScrCsr   : type CfScrCsrUnion           := evalExpr (#noExc `! "CfScrCsr") in
  let isScrCsr   : type Bool                         := evalExpr (And [ #isCfScrCsr ; #cfScrCsr `? "ScrCsr" ]) in
  let scrCsr     : type ScrCsrPayload           := evalExpr (#cfScrCsr `! "ScrCsr") in
  let sDest      : type (TaggedUnion ScrCsrIdx) := evalExpr (##scrCsr`"SpecialDest") in
  let isCsr      : type Bool                         := evalExpr (And [ #isScrCsr ; #sDest `? "Csr" ]) in
  let csrIdx     : type (Bit CsrIdxSz)          := evalExpr (#sDest `! "Csr") in
  evalExpr (And [ #isCsr ; @csrIdxIsVirtual type csrIdx ]).

(* The stall guards of the sequential and the non-sequential branches *)
Definition seqGuardV (isMul isDiv mulFull divFull : type Bool) : bool :=
  evalExpr (And [ Or [ Not #isMul ; Not #mulFull ] ; Or [ Not #isDiv ; Not #divFull ] ]).

Definition nonSeqGuardV (isMemOrFence dmFull isVirtCsr dmEmpty noWr : type Bool) : bool :=
  evalExpr (And [ Or [ Not #isMemOrFence ; Not #dmFull ] ; Or [ Not #isVirtCsr ; And [ #dmEmpty ; #noWr ] ] ]).

(* The redirect test of the non-sequential branch *)
Definition execRedirect (aluOut : type AluOutUnion) (execOut : type ExecuteOut) (predPc : type Addr) : bool :=
  let isExc           : type Bool                    := aluIsExc aluOut in
  let nextPcc         : type FullECapWithTag    := evalExpr (##execOut`"nextPcc") in
  let cfOpt           : type (Option CfPayload) := evalExpr (##execOut`"cf") in
  let hasCf           : type Bool                    := evalExpr (#cfOpt`"valid") in
  let cf              : type CfPayload          := evalExpr (#cfOpt`"data") in
  let committedNextPc : type Addr               := evalExpr (##nextPcc`"addr") in
  let capChanged      : type Bool                    := evalExpr (And [ #hasCf ; ##cf`"capChanged" ]) in
  evalExpr (Or [ #isExc ; #capChanged ; ##execOut`"isFenceIRq" ; Not (Eq #committedNextPc #predPc) ]).

(* The mulDiv operation of a valid mulDiv output: Mul or Div, and the two payloads *)
Definition mdIsMul (mdOp : type MulDivUnion) : bool := evalExpr ((Var type MulDivUnion mdOp) `? "Mul").
Definition mdMulOf (mdOp : type MulDivUnion) : type MulOp := evalExpr ((Var type MulDivUnion mdOp) `! "Mul").
Definition mdDivOf (mdOp : type MulDivUnion) : type DivOp := evalExpr ((Var type MulDivUnion mdOp) `! "Div").

(* ExecuteOut = { mulDiv; dataMem; cf; isFenceIRq; nextPcc } *)
Definition execCf (x : type ExecuteOut) : type (Option CfPayload) := x.(Snd).(Snd).(Fst).
Definition execIsFenceIRq (x : type ExecuteOut) : bool := x.(Snd).(Snd).(Snd).(Fst).

(* The request the stage enqueues into dataMem for ALU output `a` and execute output `x` *)
Definition execDmReq (a : type AluOutUnion) (x : type ExecuteOut) : type MemFenceReq :=
  (aluDstIdx a ,, ((aluDstVal a).(Snd).(Snd).(Fst) ,, (optData (execDataMem x) ,, tt))).

(* --- 4. The Branches of the Execute Stage --- *)

Section ExecImpl.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable clint : @ClintInstance implRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable envI : Env (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STAGE :=
    (@aluAndExecuteNonDeferredStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions clint revI plic type).

  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA :=
    (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemA :=
    (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchA :=
    (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA :=
    (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecA :=
    (iExec pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA :=
    (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iD2aA :=
    (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecEpochA :=
    (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA :=
    (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation daLiveA :=
    (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation D2AF s1 := (decode_toAluFifo decodeCapacity (iDecodeA s1)).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  Local Abbreviation NPCORE :=
    (Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  (* The three memory reads of the stage, on the impl memory subtree *)
  Lemma meip_sem :
    forall env m m' b,
      SemAction env (Impl.implPlicAction plic (@plicMeip (S (S (length (collectIrqActions implRegions)))) type)) m m' b ->
      m' = m /\ b = plicMeipOf (implPlicState pre post revBase revPfB revPfA plic m.(Fst)).
  Proof.
    intros env m m' b H.
    unfold Impl.implPlicAction, implNthRegionAction, implRegionsNthRegionAction, liftToImplRegion in H.
    apply SemAction_liftAction_iff in H as [rg' [H ->]].
    apply SemAction_genNthRegionAction_iff in H as [y' [H ->]].
    apply SemAction_liftAction_iff in H as [x' [H ->]].
    rewrite SemAction_iff_evalActionPropGen in H; cbn [evalActionPropGen] in H.
    destruct H as [<- <-].
    split; [| reflexivity].
    destruct m as [rg ms].
    rewrite !writeSubTreeState_readSubTreeState, updRegionStateAt_regionStateAt, writeSubTreeState_readSubTreeState; reflexivity.
  Qed.

  Lemma mtip_sem :
    forall env m m' b,
      SemAction env (Impl.implClintAction clint (readClintMtip type)) m m' b ->
      m' = m /\ b = clintSampled (implClintState pre post revBase revPfB revPfA clint m.(Fst)).
  Proof.
    intros env m m' b H.
    unfold Impl.implClintAction, implNthRegionAction, implRegionsNthRegionAction, liftToImplRegion in H.
    apply SemAction_liftAction_iff in H as [rg' [H ->]].
    apply SemAction_genNthRegionAction_iff in H as [y' [H ->]].
    apply SemAction_liftAction_iff in H as [x' [H ->]].
    rewrite SemAction_iff_evalActionPropGen in H; cbn [evalActionPropGen] in H.
    destruct H as [<- <-].
    split; [| reflexivity].
    destruct m as [rg ms].
    rewrite !writeSubTreeState_readSubTreeState, updRegionStateAt_regionStateAt, writeSubTreeState_readSubTreeState; reflexivity.
  Qed.

  (* `mem_noWriteRq` of the memory interface: no store of the core is pending *)
  Lemma noWriteRq_sem :
    forall env m m' b,
      SemAction env (@implMemNoCoreWrite implRegions type) m m' b ->
      m' = m /\ b = noCoreWrM implRegions m.
  Proof.
    intros env m m' b H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemNoCoreWrite, implMemNoPendingWrite, implMemNoWriteRq, implMemNoPortWriteRq, toAction in H.
    cbn [evalActionPropGen] in H.
    apply noPortWrite_wp in H; cbn [evalActionPropGen] in H.
    destruct H as [<- <-]; split; reflexivity.
  Qed.

  Lemma decode_withToAluFifo_eta :
    forall sd, decode_withToAluFifo decodeCapacity sd (decode_toAluFifo decodeCapacity sd) = sd.
  Proof. reflexivity. Qed.

  Lemma dm_withInputFifo_eta :
    forall dm, dm_withInputFifo dataMemCapacity dm (dm_inputFifo dataMemCapacity dm) = dm.
  Proof. reflexivity. Qed.

  (* What the stage's step reads, in the relation's accessors *)
  Definition stHead (s1 : IState) : type (Option DecodeToAluEntry) := fifoFirstVal (D2AF s1).

  (* The impl stutters: none of the parts the relation reads changes *)
  Definition ExecStutter (s1 s1' : IState) : Prop :=
    iRfA s1' = iRfA s1 /\ iWbA s1' = iWbA s1 /\ iMemA s1' = iMemA s1 /\ iFetchA s1' = iFetchA s1 /\
    iDecodeA s1' = iDecodeA s1 /\ iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1 /\
    iExecEpochA s1' = iExecEpochA s1 /\ iFenceIPendingA s1' = iFenceIPendingA s1 /\
    ex_redirect (iExecA s1') = ex_redirect (iExecA s1).

  (* A redirect of the stage not applied yet *)
  Definition stRedir (s1 : IState) : bool := ex_redirValid (iExecA s1).

  (* The epoch the stage compares entries with: a pending redirect already counts *)
  Definition stPendE (s1 : IState) : type Epoch :=
    evalExpr (FromBit Epoch (ToBit (k := Bool) (Var type Bool (stRedir s1)))).
  Definition stEff (s1 : IState) : type Epoch :=
    evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; Var type Epoch (stPendE s1) ]).

  Lemma stEff_false : forall s1, stRedir s1 = false -> stEff s1 = iExecEpochA s1.
  Proof.
    intros s1 H; unfold stEff, stPendE; rewrite H.
    change (Zmod.add (Zmod.add Zmod.zero (iExecEpochA s1)) Zmod.zero = iExecEpochA s1).
    rewrite Zmod.add_0_l, Zmod.add_0_r; reflexivity.
  Qed.

  Lemma stEff_true :
    forall s1, stRedir s1 = true ->
      stEff s1 = evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]).
  Proof. intros s1 H; unfold stEff, stPendE; rewrite H; reflexivity. Qed.

  Local Abbreviation iPlicA :=
    (iPlic pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA plic).
  Local Abbreviation iClintA :=
    (iClint pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clint).
  Local Abbreviation iPccA :=
    (iPcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* The other values the stage reads or computes *)
  Definition stJ (s1 : IState) : type DecodeToAluEntry := (stHead s1).(Fst).
  Definition stMeip (s1 : IState) : bool := plicMeipOf (iPlicA s1).
  Definition stMtip (s1 : IState) : bool := clintSampled (iClintA s1).
  Definition stInt (s1 : IState) : bool := evalIsInterruptPending pcAddrInit (stMeip s1) (stMtip s1) (iRfA s1).
  Definition stDmFull (s1 : IState) : bool :=
    Zmod.eqb (fifo_size (dm_inputFifo dataMemCapacity (iDmA s1))) (Zmod.of_Z _ (Z.of_nat dataMemCapacity)).
  Definition stDmEmpty (s1 : IState) : bool :=
    andb (Zmod.eqb (fifo_size (dm_inputFifo dataMemCapacity (iDmA s1))) Zmod.zero)
         (Zmod.eqb ((dm_state dataMemCapacity (iDmA s1)).(Snd)) Zmod.zero).
  (* no store of the core is pending (`implMemNoCoreWrite`) *)
  Definition stNoWr (s1 : IState) : bool := noCoreWrM implRegions (iMemA s1).
  Definition stMulFull (s1 : IState) : bool := mdFullMul mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1).
  Definition stDivFull (s1 : IState) : bool := mdFullDiv mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1).
  Definition stAluOut (s1 : IState) : type AluOutUnion := evalAluOut (iPccA s1) (daAluIn (stJ s1)).
  Definition stWb (s1 : IState) :=
    evalSetDstWaitBits (aluInWritesCd (daAluIn (stJ s1))) (aluInCd (daAluIn (stJ s1))) false (iWbA s1).

  (* The values the step uses: its own reads in the first slot of a cycle, the hand-off in a later
   * slot (`aluAndExecuteNonDeferred`). A later slot sees no head while an interrupt line is up. *)
  Definition stFirst (s1 : IState) : bool := ex_firstSlot (iExecA s1).
  Definition stHand (s1 : IState) : type ExecHandoff := ex_handoff (iExecA s1).
  Definition stLaterHead (s1 : IState) : type (Option DecodeToAluEntry) :=
    ((hoHead (stHand s1)).(Fst) ,,
     (andb (hoHead (stHand s1)).(Snd).(Fst) (negb (orb (stMeip s1) (stMtip s1))) ,, tt)).
  Definition stHeadE (s1 : IState) : type (Option DecodeToAluEntry) :=
    if stFirst s1 then stHead s1 else stLaterHead s1.
  Definition stPccE (s1 : IState) : type FullECapWithTag :=
    if stFirst s1 then iPccA s1 else hoPcc (stHand s1).
  Definition stRedirE (s1 : IState) : bool := if stFirst s1 then stRedir s1 else hoRedir (stHand s1).
  Definition stDmFullE (s1 : IState) : bool := if stFirst s1 then stDmFull s1 else hoDmFull (stHand s1).
  (* not handed off: a later slot takes them as false *)
  Definition stDmEmptyE (s1 : IState) : bool := andb (stFirst s1) (stDmEmpty s1).
  Definition stNoWrE (s1 : IState) : bool := andb (stFirst s1) (stNoWr s1).
  Definition stIntE (s1 : IState) : bool := andb (stFirst s1) (stInt s1).
  Definition stPendEE (s1 : IState) : type Epoch :=
    evalExpr (FromBit Epoch (ToBit (k := Bool) (Var type Bool (stRedirE s1)))).
  Definition stEffE (s1 : IState) : type Epoch :=
    evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; Var type Epoch (stPendEE s1) ]).
  Definition stJE (s1 : IState) : type DecodeToAluEntry := (stHeadE s1).(Fst).
  Definition stAluOutE (s1 : IState) : type AluOutUnion := evalAluOut (stPccE s1) (daAluIn (stJE s1)).
  Definition stWbE (s1 : IState) :=
    evalSetDstWaitBits (aluInWritesCd (daAluIn (stJE s1))) (aluInCd (daAluIn (stJE s1))) false (iWbA s1).

  Lemma stEffE_false : forall s1, stRedirE s1 = false -> stEffE s1 = iExecEpochA s1.
  Proof.
    intros s1 H; unfold stEffE, stPendEE; rewrite H.
    change (Zmod.add (Zmod.add Zmod.zero (iExecEpochA s1)) Zmod.zero = iExecEpochA s1).
    rewrite Zmod.add_0_l, Zmod.add_0_r; reflexivity.
  Qed.

  (* In the first slot the step uses its own reads *)
  Lemma stE_first :
    forall s1, stFirst s1 = true ->
      stHeadE s1 = stHead s1 /\ stPccE s1 = iPccA s1 /\ stRedirE s1 = stRedir s1 /\
      stDmFullE s1 = stDmFull s1 /\ stDmEmptyE s1 = stDmEmpty s1 /\ stNoWrE s1 = stNoWr s1 /\
      stIntE s1 = stInt s1.
  Proof.
    intros s1 H; unfold stHeadE, stPccE, stRedirE, stDmFullE, stDmEmptyE, stNoWrE, stIntE; rewrite H.
    repeat split; reflexivity.
  Qed.

  (* A later slot sees a head only while no interrupt line is up *)
  Lemma stLaterHead_valid :
    forall s1, (stLaterHead s1).(Snd).(Fst) = true ->
      (hoHead (stHand s1)).(Snd).(Fst) = true /\ stMeip s1 = false /\ stMtip s1 = false.
  Proof.
    intros s1 H; unfold stLaterHead in H; cbn [Fst Snd] in H.
    destruct ((hoHead (stHand s1)).(Snd).(Fst)), (stMeip s1), (stMtip s1); cbn in H;
      first [discriminate H | repeat split; reflexivity].
  Qed.

  Ltac exec_open H :=
    rewrite SemAction_iff_evalActionPropGen in H;
    unfold aluAndExecuteNonDeferredStage in H;
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H;
    unfold aluAndExecuteNonDeferred in H;
    cbn [decode_first decode_deq implDecodeIfc dataMem_isFull dataMem_isEmpty dataMem_enq implDataMemIfc
         mem_noWriteRq implMemIfc mulDiv_isFullMul mulDiv_isFullDiv mulDiv_enqMul mulDiv_enqDiv implMulDivIfc] in H.

  (* The reads and writes of the stage.  Each keeps the state term linear: reads leave it
   * unchanged, writes wrap it in a folded `updSub`. *)
  Ltac exec_canProceed H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecuteCanProceed _ _) HQ_)]; cbv beta in H.
  (* `firstSlot` and the hand-off: read, then cleared *)
  Ltac exec_hand H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readFirstSlot _ _) HQ_)]; cbv beta in H;
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readHandoff _ _) HQ_)]; cbv beta in H;
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_clearFirstSlot _ _) HQ_)]; cbv beta in H;
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_clearHandoff _ _) HQ_)]; cbv beta in H.
  Ltac exec_r_clear H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_clearExecuteCanProceed _ _) HQ_)]; cbv beta in H.
  Ltac exec_r_head H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_decodeFirst decodeCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_first_iff decodeCapacity DecodeToAluEntry _ _ _)) in HQ_;
       cbv beta in HQ_; rewrite decode_withToAluFifo_eta in HQ_; exact HQ_]; cbv beta in H.
  Ltac exec_r_dmFull H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_dataMemIsFull dataMemCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_isFull_raw dataMemCapacity MemFenceReq _ _ _)) in HQ_;
       cbv beta in HQ_; rewrite dm_withInputFifo_eta in HQ_; exact HQ_]; cbv beta in H.
  Ltac exec_r_dmEmpty H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_dataMemIsEmpty dataMemCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_isEmpty_raw dataMemCapacity MemFenceReq _ _ _)) in HQ_;
       cbv beta in HQ_; rewrite dm_withInputFifo_eta in HQ_; exact HQ_]; cbv beta in H.
  Ltac exec_r_noWr H :=
    eapply fw_liftRead in H; [| exact (read_of_sem _ _ noWriteRq_sem)]; cbv beta in H.
  Ltac exec_r_mulFull H :=
    eapply fw_liftRead in H;
    [| exact (read_of_sem _ _ (mdFullMul_sem mulCapacity divCapacity mulStages divStages mulDivMode))]; cbv beta in H.
  Ltac exec_r_divFull H :=
    eapply fw_liftRead in H;
    [| exact (read_of_sem _ _ (mdFullDiv_sem mulCapacity divCapacity mulStages divStages mulDivMode))]; cbv beta in H.
  Ltac exec_r_epoch H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecEpoch _ _) HQ_)]; cbv beta in H.
  Ltac exec_r_redir H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_redirectPending _ _) HQ_)]; cbv beta in H.
  (* the PCC read, as `readPcc` (the unifier does not see `evalExpr $0 = Zmod.zero` next to the ALU) *)
  Ltac exec_r_pcc H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; apply (proj1 (evalActionPropGen_readRegsList _ _ _ _)) in HQ_;
       rewrite (readPcc_idx0 pcAddrInit) in HQ_; exact HQ_]; cbv beta in H.
  Ltac exec_r_meip H :=
    eapply fw_liftRead in H; [| exact (read_of_sem _ _ meip_sem)]; cbv beta in H.
  Ltac exec_r_mtip H :=
    eapply fw_liftRead in H; [| exact (read_of_sem _ _ mtip_sem)]; cbv beta in H.
  Ltac exec_r_int H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_isInterruptPending pcAddrInit _ _ _ _) HQ_)];
    cbv beta in H.
  Ltac exec_reads H :=
    exec_r_clear H; exec_r_head H; exec_r_dmFull H; exec_r_dmEmpty H; exec_r_noWr H; exec_r_redir H;
    exec_r_pcc H; exec_r_meip H; exec_r_mtip H; exec_r_int H; exec_r_mulFull H; exec_r_divFull H;
    exec_r_epoch H.

  (* `decode_deq`, inside a block *)
  Ltac exec_deq H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_decodeDeq decodeCapacity _ _)) in HQ_;
       apply (proj1 (evalActionPropGen_deq_iff decodeCapacity DecodeToAluEntry _ _ _)) in HQ_;
       cbv beta in HQ_; exact HQ_]; cbv beta in H.
  (* `setDstWaitBits`, last in a block *)
  Ltac exec_wbLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setDstWaitBits _ _ _ _ _) HQ_)]; cbv beta in H.
  (* the other writes, inside a block *)
  Ltac exec_setCp H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setExecuteCanProceed _ _) HQ_)]; cbv beta in H.
  Ltac exec_handW H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_writeHandoff _ _ _) HQ_)]; cbv beta in H.
  Ltac exec_pccW H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; apply (proj1 (evalActionPropGen_writeRegsList _ _ _ _ _)) in HQ_;
       rewrite (writePcc_idx0 pcAddrInit) in HQ_; exact HQ_]; cbv beta in H.
  Ltac exec_epochW H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_writeExecEpoch _ _ _) HQ_)]; cbv beta in H.
  Ltac exec_clrStr H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_clearStraddle pcAddrInit fetchCapacity instCapacity _ _) HQ_)]; cbv beta in H.
  Ltac exec_wrPc H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_writeFetchPc pcAddrInit fetchCapacity instCapacity _ _ _) HQ_)]; cbv beta in H.
  Ltac exec_setRedir H :=
    eapply fw_liftUpd in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setRedirect _ _ _) HQ_)]; cbv beta in H.
  (* an execute sub-action on the register file: fresh `rfMid` and output *)
  Tactic Notation "exec_sem" hyp(H) ident(rfMid) ident(out) ident(Hex) :=
    apply fw_liftSem in H; destruct H as [rfMid [out [Hex H]]]; cbv beta in H;
    apply (proj1 (SemAction_noRecvTree_env _ defaultEnv _ _ _ _ (noRecv_rfTree pcAddrInit))) in Hex.

  (* the `Let`s and the ALU between the reads and the first test (syntactic dispatch: a failing
   * `apply` would try to evaluate the ALU) *)
  Ltac exec_lets H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (LetExp _ _ _) _ _ => apply fw_letExp in H
            end; cbv beta in H).
  (* the ALU (`LetL aluOut <- wrappedAlu pcc pkg`): its value becomes a fresh variable *)
  Ltac exec_alu H :=
    lazymatch type of H with
    | evalActionPropGen _ (LetAction _ (toAction _ _) _) _ _ =>
        let a := fresh "aluOut" in let Ea := fresh "Ealu" in
        apply fw_letLGen in H; destruct H as [a [Ea H]]; cbv beta in H
    end.
  (* the `Let`s choosing between the step's own reads and the hand-off: bound to their names *)
  Ltac exec_letV H K v := apply (fw_letExpV (k' := K) _ _ _ _ _ _ v) in H; [cbv beta in H | reflexivity].
  Ltac exec_handLets H s1 :=
    exec_letV H (Option DecodeToAluEntry) (hoHead (stHand s1));
    exec_letV H (Option DecodeToAluEntry) (stLaterHead s1);
    exec_letV H (Option DecodeToAluEntry) (stHeadE s1);
    exec_letV H FullECapWithTag (stPccE s1); exec_letV H Bool (stRedirE s1); exec_letV H Bool (stDmFullE s1);
    exec_letV H Bool (stDmEmptyE s1); exec_letV H Bool (stNoWrE s1); exec_letV H Bool (stIntE s1).
  Ltac exec_lets2 H := exec_lets H; exec_alu H; exec_lets H.
  (* the ALU variable is `stAluOutE s1` (compared through its arguments only) *)
  Ltac exec_aluEq s1 :=
    match goal with
    | Ea : ?a = evalLetExpr _ |- _ => change (a = stAluOutE s1) in Ea
    end.

  (* `Retv` after a branch *)
  Ltac exec_ret H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (Return _) _ _ => apply fw_return in H
            | evalActionPropGen _ (LetAction _ _ _) _ _ => apply fw_letAction in H
            end; cbv beta in H).

  (* the common prefix: `canProceed`, the hand-off, the reads, the `Let`s, the valid and the epoch
   * tests *)
  Ltac exec_prefix H Hcp Hrd Hv Hlive :=
    exec_open H; exec_canProceed H; exec_hand H;
    apply fw_ifTrue in H; [| exact Hcp];
    exec_reads H;
    lazymatch type of Hrd with stRedirE ?s = false => exec_handLets H s end;
    exec_lets2 H;
    apply fw_ifTrue in H; [| exact Hv];
    apply fw_ifFalse in H;
    [| lazymatch type of Hlive with ?l = true => lazymatch type of Hrd with stRedirE ?s = false =>
         change (negb (Zmod.eqb (daExecEpoch (stHeadE s).(Fst)) (stEffE s)) = false);
         rewrite (stEffE_false s Hrd); change (negb l = false); rewrite Hlive; reflexivity end end].

  Lemma impl_noCanProceed :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = false ->
      ExecStutter s1 s1' /\ ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' H Hcp.
    exec_open H. exec_canProceed H. exec_hand H.
    apply fw_ifFalse in H; [| exact Hcp]. exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; first [reflexivity | exact Hcp].
  Qed.

  Lemma impl_noHead :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true ->
      (stHeadE s1).(Snd).(Fst) = false ->
      ExecStutter s1 s1' /\ ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' H Hcp Hv.
    exec_open H. exec_canProceed H. exec_hand H.
    apply fw_ifTrue in H; [| exact Hcp].
    exec_reads H.
    exec_handLets H s1.
    exec_lets2 H.
    apply fw_ifFalse in H; [| exact Hv]. exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; reflexivity.
  Qed.

  Lemma impl_stale :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true ->
      (stHeadE s1).(Snd).(Fst) = true ->
      Zmod.eqb (daExecEpoch (stHeadE s1).(Fst)) (stEffE s1) = false ->
      iRfA s1' = iRfA s1 /\
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn (stHeadE s1).(Fst))) (aluInCd (daAluIn (stHeadE s1).(Fst)))
                   false (iWbA s1) /\
      iMemA s1' = iMemA s1 /\ iFetchA s1' = iFetchA s1 /\ D2AF s1' = fifoDeqState (D2AF s1) /\
      iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1 /\
      iExecEpochA s1' = iExecEpochA s1 /\ iFenceIPendingA s1' = iFenceIPendingA s1 /\
      ex_redirect (iExecA s1') = ex_redirect (iExecA s1) /\ ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' H Hcp Hv Hst.
    exec_open H. exec_canProceed H. exec_hand H.
    apply fw_ifTrue in H; [| exact Hcp].
    exec_reads H.
    exec_handLets H s1.
    exec_lets2 H.
    apply fw_ifTrue in H; [| exact Hv].
    apply fw_ifTrue in H; [| change (negb (Zmod.eqb (daExecEpoch (stHeadE s1).(Fst)) (stEffE s1)) = true); rewrite Hst; reflexivity].
    exec_deq H. exec_wbLast H.
    exec_ret H.
    destruct H as [<- _]; repeat split; reflexivity.
  Qed.

  (* Interrupt pending, but the data memory is busy: stall *)
  Lemma impl_intStall :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> stRedirE s1 = false ->
      (stHeadE s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadE s1).(Fst) = true ->
      stIntE s1 = true ->
      andb (stDmEmptyE s1) (stNoWrE s1) = false ->
      ExecStutter s1 s1' /\ ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' H Hcp Hrd Hv Hlive Hint Hq.
    exec_prefix H Hcp Hrd Hv Hlive.
    apply fw_ifTrue in H; [| exact Hint].
    apply fw_ifFalse in H; [| exact Hq].
    exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; reflexivity.
  Qed.

  (* Sequential, but the mulDiv request FIFO is full: stall *)
  Lemma impl_seqStall :
    forall (s1 s1' : IState) (a : type AluOutUnion),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> stRedirE s1 = false ->
      (stHeadE s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadE s1).(Fst) = true ->
      stIntE s1 = false ->
      a = stAluOutE s1 ->
      aluIsSeq a = true ->
      seqGuardV (aluIsMul a) (aluIsDiv a) (stMulFull s1) (stDivFull s1) = false ->
      ExecStutter s1 s1' /\ ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' a H Hcp Hrd Hv Hlive Hint Ha Hseq Hg.
    exec_prefix H Hcp Hrd Hv Hlive.
    exec_aluEq s1. rewrite <- Ha in Ealu. rewrite <- Ealu in Hseq, Hg.
    apply fw_ifFalse in H; [| exact Hint].
    apply fw_ifTrue in H; [| exact Hseq].
    apply fw_ifFalse in H; [| exact Hg].
    exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; reflexivity.
  Qed.

  (* Non-sequential, but the data memory is full or busy: stall *)
  Lemma impl_nonSeqStall :
    forall (s1 s1' : IState) (a : type AluOutUnion),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> stRedirE s1 = false ->
      (stHeadE s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadE s1).(Fst) = true ->
      stIntE s1 = false ->
      a = stAluOutE s1 ->
      aluIsSeq a = false ->
      nonSeqGuardV (aluIsMemOrFence a) (stDmFullE s1) (aluIsVirtCsr a) (stDmEmptyE s1) (stNoWrE s1) = false ->
      ExecStutter s1 s1' /\ ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' a H Hcp Hrd Hv Hlive Hint Ha Hseq Hg.
    exec_prefix H Hcp Hrd Hv Hlive.
    exec_aluEq s1. rewrite <- Ha in Ealu. rewrite <- Ealu in Hseq, Hg.
    apply fw_ifFalse in H; [| exact Hint].
    apply fw_ifFalse in H; [| exact Hseq].
    apply fw_ifFalse in H; [| exact Hg].
    exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; reflexivity.
  Qed.

  (* Interrupt: take it *)
  Lemma impl_interrupt :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> stRedirE s1 = false ->
      (stHeadE s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadE s1).(Fst) = true ->
      stIntE s1 = true ->
      andb (stDmEmptyE s1) (stNoWrE s1) = true ->
      exists rfMid execOut,
        SemAction defaultEnv (@executeInterrupt pcAddrInit type (stPccE s1) (stMeip s1) (stMtip s1))
          (iRfA s1) rfMid execOut /\
        iRfA s1' = writePcc pcAddrInit (defNextPcc execOut) rfMid /\
        iWbA s1' = stWbE s1 /\
        iMemA s1' = iMemA s1 /\
        iFetchA s1' = iFetchA s1 /\
        D2AF s1' = fifoDeqState (D2AF s1) /\
        iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1 /\
        iExecEpochA s1' = iExecEpochA s1 /\
        iFenceIPendingA s1' = iFenceIPendingA s1 /\
        ex_redirect (iExecA s1') = redirOf (defNextPcc execOut) /\
        ex_canProceed (iExecA s1') = false.
  Proof.
    intros s1 s1' H Hcp Hrd Hv Hlive Hint Hq.
    exec_prefix H Hcp Hrd Hv Hlive.
    apply fw_ifTrue in H; [| exact Hint].
    apply fw_ifTrue in H; [| exact Hq].
    exec_deq H.
    exec_sem H rfMid execOut Hex.
    exec_lets H. exec_pccW H. exec_lets H. exec_setRedir H. exec_wbLast H.
    exec_ret H.
    destruct H as [<- _].
    exists rfMid, execOut; split; [exact Hex |].
    repeat split; reflexivity.
  Qed.

  (* the last action of a block: enqMul / enqDiv, the fetch PC write, fence.i pending, dataMem enq *)
  Ltac exec_mulLast H :=
    eapply fw_liftUpdLast in H;
    [| exact (upd_of_sem _ _ _ (mdEnqMul_sem mulCapacity divCapacity mulStages divStages mulDivMode _ _ _))];
    cbv beta in H.
  Ltac exec_divLast H :=
    eapply fw_liftUpdLast in H;
    [| exact (upd_of_sem _ _ _ (mdEnqDiv_sem mulCapacity divCapacity mulStages divStages mulDivMode _ _ _))];
    cbv beta in H.
  Ltac exec_wrPcLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_;
       exact (proj1 (evalActionPropGen_writeFetchPc pcAddrInit fetchCapacity instCapacity _ _ _) HQ_)]; cbv beta in H.
  Ltac exec_setRedirLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setRedirect _ _ _) HQ_)]; cbv beta in H.
  Ltac exec_setFipLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_setFenceIPending _ _) HQ_)]; cbv beta in H.
  Ltac exec_dmEnqLast H :=
    eapply fw_liftUpdLast in H;
    [| intros env_ sub_ Q_ HQ_;
       apply (proj1 (evalActionPropGen_dataMemEnq dataMemCapacity _ _ _ _ _)) in HQ_; cbv zeta in HQ_;
       apply (proj1 (evalActionPropGen_enq_iff dataMemCapacity MemFenceReq _ _ _ _)) in HQ_;
       cbv beta in HQ_; exact HQ_]; cbv beta in H.
  (* the conclusions, one equation at a time (`split` on an equation would try `eq_refl` by
   * unification, which is slow) *)
  Ltac exec_close := repeat (lazymatch goal with |- _ /\ _ => split; [reflexivity |] end); reflexivity.
  (* an `If` without `Else` whose condition is false *)
  Ltac exec_skip H := apply fw_return in H; cbv beta in H.

  (* The PCC a sequential commit writes, in the action's own form (`pcc` with `addr := predPc`) *)
  Definition stNextPccE (s1 : IState) : type FullECapWithTag :=
    evalExpr ((Var type FullECapWithTag (stPccE s1)) `{ "addr" <- Var type Addr (daPredPc (stJE s1)) }).

  Lemma stNextPccE_eq : forall s1, stNextPccE s1 = pccWithAddr (stPccE s1) (daPredPc (stJE s1)).
  Proof. intros s1; unfold stNextPccE; destruct (stPccE s1) as [t [e [a []]]]; reflexivity. Qed.

  (* The hand-off a sequential commit leaves for the next slot *)
  Definition stHandOut (s1 : IState) : type ExecHandoff :=
    (fifoFirstVal (fifoDeqState (D2AF s1)) ,, (stNextPccE s1 ,,
     (stRedirE s1 ,, (stDmFullE s1 ,, tt)))).

  (* Sequential: execute, write the PCC with the predicted PC and the hand-off, then the mulDiv
   * enqueue or the wait-bit clear *)
  Lemma impl_seq :
    forall (s1 s1' : IState) (a : type AluOutUnion),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> stRedirE s1 = false ->
      (stHeadE s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadE s1).(Fst) = true ->
      stIntE s1 = false ->
      a = stAluOutE s1 ->
      aluIsSeq a = true ->
      seqGuardV (aluIsMul a) (aluIsDiv a) (stMulFull s1) (stDivFull s1) = true ->
      exists rfMid mdOpt,
        SemAction defaultEnv (@executeSequential pcAddrInit type (stPccE s1) a) (iRfA s1) rfMid mdOpt /\
        iRfA s1' = writePcc pcAddrInit (stNextPccE s1) rfMid /\
        iMemA s1' = iMemA s1 /\ iFetchA s1' = iFetchA s1 /\
        D2AF s1' = fifoDeqState (D2AF s1) /\
        iDmA s1' = iDmA s1 /\
        iExecEpochA s1' = iExecEpochA s1 /\ iFenceIPendingA s1' = iFenceIPendingA s1 /\
        ex_redirect (iExecA s1') = ex_redirect (iExecA s1) /\
        ex_canProceed (iExecA s1') = true /\ ex_firstSlot (iExecA s1') = false /\
        ex_handoff (iExecA s1') = stHandOut s1 /\
        (if optValid mdOpt
         then iWbA s1' = iWbA s1 /\
              iMdA s1' = (if mdIsMul (optData mdOpt)
                          then mdEnqMul mulCapacity divCapacity mulStages divStages mulDivMode
                                 (aluDstIdx a) (aluDstVal a).(Snd).(Snd).(Fst) (mdMulOf (optData mdOpt)) (iMdA s1)
                          else mdEnqDiv mulCapacity divCapacity mulStages divStages mulDivMode
                                 (aluDstIdx a) (aluDstVal a).(Snd).(Snd).(Fst) (mdDivOf (optData mdOpt)) (iMdA s1))
         else iWbA s1' = stWbE s1 /\ iMdA s1' = iMdA s1).
  Proof.
    intros s1 s1' a H Hcp Hrd Hv Hlive Hint Ha Hseq Hg.
    exec_prefix H Hcp Hrd Hv Hlive.
    exec_aluEq s1. rewrite <- Ha in Ealu. subst aluOut.
    apply fw_ifFalse in H; [| exact Hint].
    apply fw_ifTrue in H; [| exact Hseq].
    apply fw_ifTrue in H; [| exact Hg].
    exec_setCp H. exec_deq H.
    exec_sem H rfMid mdOpt Hex.
    exec_lets H. exec_pccW H.
    exec_r_head H. exec_lets H. exec_handW H.
    exists rfMid, mdOpt; split; [exact Hex |].
    (* the leaves as their own constants, so this `Qed` checks only the common prefix *)
    apply fw_ifTF in H; destruct H as [[Hmv H] | [Hmv H]].
    - assert (Ev : optValid mdOpt = true) by exact Hmv.
      exec_lets H.
      apply fw_ifTF in H; destruct H as [[Hmul H] | [Hmul H]].
      + assert (Em : mdIsMul (optData mdOpt) = true) by exact Hmul.
        abstract (exec_lets H; exec_mulLast H; exec_ret H;
                  destruct H as [<- _]; rewrite Ev, Em; exec_close).
      + assert (Em : mdIsMul (optData mdOpt) = false) by exact Hmul.
        abstract (exec_lets H; exec_divLast H; exec_ret H;
                  destruct H as [<- _]; rewrite Ev, Em; exec_close).
    - assert (Ev : optValid mdOpt = false) by exact Hmv.
      abstract (exec_wbLast H; exec_ret H; destruct H as [<- _]; rewrite Ev; exec_close).
  Qed.

  (* a leaf of the non-sequential branch, as its own constant *)
  Ltac ns_leaf H Hred Hfi Hdm a execOut s1 :=
    let Er := fresh "Er" in let Ef := fresh "Ef" in let Ed := fresh "Ed" in
    abstract (first [exec_lets H; exec_dmEnqLast H | exec_wbLast H];
      exec_ret H; destruct H as [<- _];
      first [assert (Er : execRedirect a execOut (daPredPc (stJE s1)) = true) by exact Hred
            | assert (Er : execRedirect a execOut (daPredPc (stJE s1)) = false) by exact Hred];
      first [assert (Ef : execIsFenceIRq execOut = true) by exact Hfi
            | assert (Ef : execIsFenceIRq execOut = false) by exact Hfi];
      first [assert (Ed : optValid (execDataMem execOut) = true) by exact Hdm
            | assert (Ed : optValid (execDataMem execOut) = false) by exact Hdm];
      rewrite Er, Ef, Ed; exec_close).

  (* Non-sequential: execute, write the PCC, update the predictor (any update), then the
   * redirect, the fence.i flag, and the dataMem enqueue or the wait-bit clear *)
  Lemma impl_nonSeq :
    forall (s1 s1' : IState) (a : type AluOutUnion),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> stRedirE s1 = false ->
      (stHeadE s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadE s1).(Fst) = true ->
      stIntE s1 = false ->
      a = stAluOutE s1 ->
      aluIsSeq a = false ->
      nonSeqGuardV (aluIsMemOrFence a) (stDmFullE s1) (aluIsVirtCsr a) (stDmEmptyE s1) (stNoWrE s1) = true ->
      exists rfMid execOut,
        SemAction defaultEnv (@executeNonSequential pcAddrInit type (stPccE s1) (stMeip s1) (stMtip s1) a)
          (iRfA s1) rfMid execOut /\
        iRfA s1' = writePcc pcAddrInit (defNextPcc execOut) rfMid /\
        iMemA s1' = iMemA s1 /\
        D2AF s1' = fifoDeqState (D2AF s1) /\
        iMdA s1' = iMdA s1 /\
        iExecEpochA s1' = iExecEpochA s1 /\ iFetchA s1' = iFetchA s1 /\
        ex_redirect (iExecA s1') =
          (if execRedirect a execOut (daPredPc (stJE s1))
           then redirOf (defNextPcc execOut)
           else ex_redirect (iExecA s1)) /\
        iFenceIPendingA s1' = (if execIsFenceIRq execOut then true else iFenceIPendingA s1) /\
        ex_canProceed (iExecA s1') = false /\
        (if optValid (execDataMem execOut)
         then iWbA s1' = iWbA s1 /\
              iDmA s1' = dm_withInputFifo dataMemCapacity (iDmA s1)
                           (fifoEnqState (dm_inputFifo dataMemCapacity (iDmA s1)) (execDmReq a execOut))
         else iWbA s1' = stWbE s1 /\ iDmA s1' = iDmA s1).
  Proof.
    intros s1 s1' a H Hcp Hrd Hv Hlive Hint Ha Hseq Hg.
    exec_prefix H Hcp Hrd Hv Hlive.
    exec_aluEq s1. rewrite <- Ha in Ealu. subst aluOut.
    apply fw_ifFalse in H; [| exact Hint].
    apply fw_ifFalse in H; [| exact Hseq].
    apply fw_ifTrue in H; [| exact Hg].
    exec_deq H.
    exec_sem H rfMid execOut Hex.
    exec_lets H. exec_pccW H. exec_lets H.
    apply fw_ifLiftAny in H; destruct H as [bp1 [r1 H]]; cbv beta in H.
    apply fw_ifLiftAny in H; destruct H as [bp2 [r2 H]]; cbv beta in H.
    exists rfMid, execOut; split; [exact Hex |].
    (* the three tests, then the leaves, each its own constant (this `Qed` checks the prefix) *)
    apply fw_ifTF in H; destruct H as [[Hred H] | [Hred H]].
    - exec_lets H; exec_setRedirLast H.
      apply fw_ifTF in H; destruct H as [[Hfi H] | [Hfi H]].
      + exec_setFipLast H; exec_lets H.
        apply fw_ifTF in H; destruct H as [[Hdm H] | [Hdm H]].
        * ns_leaf H Hred Hfi Hdm a execOut s1.
        * ns_leaf H Hred Hfi Hdm a execOut s1.
      + exec_skip H; exec_lets H.
        apply fw_ifTF in H; destruct H as [[Hdm H] | [Hdm H]].
        * ns_leaf H Hred Hfi Hdm a execOut s1.
        * ns_leaf H Hred Hfi Hdm a execOut s1.
    - exec_skip H.
      apply fw_ifTF in H; destruct H as [[Hfi H] | [Hfi H]].
      + exec_setFipLast H; exec_lets H.
        apply fw_ifTF in H; destruct H as [[Hdm H] | [Hdm H]].
        * ns_leaf H Hred Hfi Hdm a execOut s1.
        * ns_leaf H Hred Hfi Hdm a execOut s1.
      + exec_skip H; exec_lets H.
        apply fw_ifTF in H; destruct H as [[Hdm H] | [Hdm H]].
        * ns_leaf H Hred Hfi Hdm a execOut s1.
        * ns_leaf H Hred Hfi Hdm a execOut s1.
  Qed.

End ExecImpl.

