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

  Lemma noWriteRq_sem :
    forall env m m' b,
      SemAction env (@implMemNoPendingWrite implRegions type) m m' b ->
      m' = m /\ b = andb (negb (msWriteRq m.(Snd).(Fst))) (noPortWriteB implRegions m.(Fst)).
  Proof.
    intros env m m' b H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemNoPendingWrite, implMemNoWriteRq, implMemNoPortWriteRq, toAction in H.
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
    iExecEpochA s1' = iExecEpochA s1 /\ iFenceIPendingA s1' = iFenceIPendingA s1.

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
  Definition stNoWr (s1 : IState) : bool :=
    andb (negb (msWriteRq (iMemA s1).(Snd).(Fst))) (noPortWriteB implRegions (iMemA s1).(Fst)).
  Definition stMulFull (s1 : IState) : bool := mdFullMul mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1).
  Definition stDivFull (s1 : IState) : bool := mdFullDiv mulCapacity divCapacity mulStages divStages mulDivMode (iMdA s1).
  Definition stAluOut (s1 : IState) : type AluOutUnion := evalAluOut (iPccA s1) (daAluIn (stJ s1)).
  Definition stWb (s1 : IState) :=
    evalSetDstWaitBits (aluInWritesCd (daAluIn (stJ s1))) (aluInCd (daAluIn (stJ s1))) false (iWbA s1).

  Ltac exec_open H :=
    rewrite SemAction_iff_evalActionPropGen in H;
    unfold aluAndExecuteNonDeferredStage in H;
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in H;
    unfold aluAndExecuteNonDeferred in H;
    cbn [decode_first decode_deq implDecodeIfc dataMem_isFull dataMem_isEmpty dataMem_enq implDataMemIfc
         mem_noWriteRq implMemIfc mulDiv_isFullMul mulDiv_isFullDiv mulDiv_enqMul mulDiv_enqDiv implMulDivIfc
         fetch_clearStraddle fetch_writeFetchPc implFetchIfc] in H.

  (* The reads and writes of the stage.  Each keeps the state term linear: reads leave it
   * unchanged, writes wrap it in a folded `updSub`. *)
  Ltac exec_canProceed H :=
    eapply fw_liftRead in H;
    [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readExecuteCanProceed _ _) HQ_)]; cbv beta in H.
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
    exec_r_clear H; exec_r_head H; exec_r_dmFull H; exec_r_dmEmpty H; exec_r_noWr H; exec_r_mulFull H;
    exec_r_divFull H; exec_r_epoch H; exec_r_pcc H; exec_r_meip H; exec_r_mtip H; exec_r_int H.

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
  Ltac exec_lets2 H := exec_lets H; exec_alu H; exec_lets H.
  (* the ALU variable is `stAluOut s1` (compared through its arguments only) *)
  Ltac exec_aluEq s1 :=
    match goal with
    | Ea : ?a = evalLetExpr (@wrappedAlu _ ?p ?k) |- _ =>
        let Ep := fresh in let Ek := fresh in
        assert (Ep : p = iPccA s1) by reflexivity;
        assert (Ek : k = daAluIn (stJ s1)) by reflexivity;
        rewrite Ep, Ek in Ea; clear Ep Ek; change (a = stAluOut s1) in Ea
    end.

  (* `Retv` after a branch *)
  Ltac exec_ret H :=
    repeat (lazymatch type of H with
            | evalActionPropGen _ (Return _) _ _ => apply fw_return in H
            | evalActionPropGen _ (LetAction _ _ _) _ _ => apply fw_letAction in H
            end; cbv beta in H).

  (* the common prefix: `canProceed`, the reads, the `Let`s, the valid and the epoch tests *)
  Ltac exec_prefix H Hcp Hv Hlive :=
    exec_open H; exec_canProceed H;
    apply fw_ifTrue in H; [| exact Hcp];
    exec_reads H; exec_lets2 H;
    apply fw_ifTrue in H; [| exact Hv];
    apply fw_ifFalse in H;
    [| lazymatch type of Hlive with ?l = true => change (negb l = false); rewrite Hlive; reflexivity end].

  Lemma impl_noCanProceed :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = false ->
      s1' = s1.
  Proof.
    intros s1 s1' H Hcp.
    exec_open H. exec_canProceed H.
    apply fw_ifFalse in H; [| exact Hcp]. exec_ret H.
    destruct H as [<- _]; reflexivity.
  Qed.

  Lemma impl_noHead :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true ->
      (stHead s1).(Snd).(Fst) = false ->
      ExecStutter s1 s1'.
  Proof.
    intros s1 s1' H Hcp Hv.
    exec_open H. exec_canProceed H.
    apply fw_ifTrue in H; [| exact Hcp].
    exec_r_clear H. exec_r_head H. exec_r_dmFull H. exec_r_dmEmpty H. exec_r_noWr H. exec_r_mulFull H.
    exec_r_divFull H. exec_r_epoch H. exec_r_pcc H. exec_r_meip H. exec_r_mtip H. exec_r_int H.
    exec_lets2 H.
    apply fw_ifFalse in H; [| exact Hv]. exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; reflexivity.
  Qed.

  Lemma impl_stale :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true ->
      (stHead s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHead s1).(Fst) = false ->
      iRfA s1' = iRfA s1 /\
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn (stHead s1).(Fst))) (aluInCd (daAluIn (stHead s1).(Fst)))
                   false (iWbA s1) /\
      iMemA s1' = iMemA s1 /\ iFetchA s1' = iFetchA s1 /\ D2AF s1' = fifoDeqState (D2AF s1) /\
      iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1 /\
      iExecEpochA s1' = iExecEpochA s1 /\ iFenceIPendingA s1' = iFenceIPendingA s1.
  Proof.
    intros s1 s1' H Hcp Hv Hst.
    exec_open H. exec_canProceed H.
    apply fw_ifTrue in H; [| exact Hcp].
    exec_reads H.
    exec_lets2 H.
    apply fw_ifTrue in H; [| exact Hv].
    apply fw_ifTrue in H; [| change (negb (daLiveA s1 (stHead s1).(Fst)) = true); rewrite Hst; reflexivity].
    exec_deq H. exec_wbLast H.
    exec_ret H.
    destruct H as [<- _]; repeat split; reflexivity.
  Qed.

  (* Interrupt pending, but the data memory is busy: stall *)
  Lemma impl_intStall :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true ->
      (stHead s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHead s1).(Fst) = true ->
      stInt s1 = true ->
      andb (stDmEmpty s1) (stNoWr s1) = false ->
      ExecStutter s1 s1'.
  Proof.
    intros s1 s1' H Hcp Hv Hlive Hint Hq.
    exec_prefix H Hcp Hv Hlive.
    apply fw_ifTrue in H; [| exact Hint].
    apply fw_ifFalse in H; [| exact Hq].
    exec_ret H.
    destruct H as [<- _]; unfold ExecStutter; repeat split; reflexivity.
  Qed.

  (* Sequential, but the mulDiv request FIFO is full: stall *)
  Lemma impl_seqStall :
    forall (s1 s1' : IState) (a : type AluOutUnion),
      SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true ->
      (stHead s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHead s1).(Fst) = true ->
      stInt s1 = false ->
      a = stAluOut s1 ->
      aluIsSeq a = true ->
      seqGuardV (aluIsMul a) (aluIsDiv a) (stMulFull s1) (stDivFull s1) = false ->
      ExecStutter s1 s1'.
  Proof.
    intros s1 s1' a H Hcp Hv Hlive Hint Ha Hseq Hg.
    exec_prefix H Hcp Hv Hlive.
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
      ex_canProceed (iExecA s1) = true ->
      (stHead s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHead s1).(Fst) = true ->
      stInt s1 = false ->
      a = stAluOut s1 ->
      aluIsSeq a = false ->
      nonSeqGuardV (aluIsMemOrFence a) (stDmFull s1) (aluIsVirtCsr a) (stDmEmpty s1) (stNoWr s1) = false ->
      ExecStutter s1 s1'.
  Proof.
    intros s1 s1' a H Hcp Hv Hlive Hint Ha Hseq Hg.
    exec_prefix H Hcp Hv Hlive.
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
      ex_canProceed (iExecA s1) = true ->
      (stHead s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHead s1).(Fst) = true ->
      stInt s1 = true ->
      andb (stDmEmpty s1) (stNoWr s1) = true ->
      exists rfMid execOut,
        SemAction defaultEnv (@executeInterrupt pcAddrInit type (iPccA s1) (stMeip s1) (stMtip s1))
          (iRfA s1) rfMid execOut /\
        iRfA s1' = writePcc pcAddrInit (defNextPcc execOut) rfMid /\
        iWbA s1' = stWb s1 /\
        iMemA s1' = iMemA s1 /\
        iFetchA s1' = fetch_withPc pcAddrInit fetchCapacity instCapacity
                        (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1)
                           (getDefault (Option StraddleHalf)))
                        (defNextPcc execOut).(Snd).(Snd).(Fst) /\
        D2AF s1' = fifoDeqState (D2AF s1) /\
        iDmA s1' = iDmA s1 /\ iMdA s1' = iMdA s1 /\
        iExecEpochA s1' = evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]) /\
        iFenceIPendingA s1' = iFenceIPendingA s1.
  Proof.
    intros s1 s1' H Hcp Hv Hlive Hint Hq.
    exec_prefix H Hcp Hv Hlive.
    apply fw_ifTrue in H; [| exact Hint].
    apply fw_ifTrue in H; [| exact Hq].
    exec_deq H.
    exec_sem H rfMid execOut Hex.
    exec_lets H. exec_pccW H. exec_lets H. exec_epochW H. exec_clrStr H. exec_wrPc H. exec_wbLast H.
    exec_ret H.
    destruct H as [<- _].
    exists rfMid, execOut; split; [exact Hex |].
    repeat split; reflexivity.
  Qed.

End ExecImpl.

