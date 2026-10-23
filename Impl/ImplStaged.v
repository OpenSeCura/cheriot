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

(*
 * Generic Staged Hardware Controllers & Inductive Verification Framework (`ImplStaged.v`).
 *
 * Completely independent of any specific arithmetic operation (such as Multiply or Divide).
 *
 * Given any computation decomposed into `n` stages:
 *   `f(x) = finishFn (stepFn^n (initFn x))`
 * where:
 *   - `initFn   : forall ty, ty InpK -> LetExpr ty StateK`   (`f_1`)
 *   - `stepFn   : forall ty, ty StateK -> LetExpr ty StateK` (`f_m`)
 *   - `finishFn : forall ty, ty StateK -> LetExpr ty OutK`   (`f_n`)
 *   - `specFn   : forall ty, ty InpK -> LetExpr ty OutK`     (`f`)
 *
 * This module provides:
 *   1. `StageValAt initFn stepFn m inp`: the `m`-step accumulator value `stepFn^m (initFn inp)`.
 *   2. `StageValAt_inv` & `StageValAt_spec_correct`:
 *      A generic inductive proof that if a step-indexed invariant `StageInv m inp v` holds
 *      at `m = 0` (`initFn`), steps from `m` to `S m` (`stepFn`), and implies
 *      `evalLetExpr (finishFn v) = evalLetExpr (specFn inp)` at `m = n`, then:
 *        `evalLetExpr (finishFn type (StageValAt initFn stepFn n inp)) = evalLetExpr (specFn type inp)`.
 *   3. Generic Iterative (`stagedIterTree`) and Pipelined (`stagedPipeTree`) hardware
 *      controllers and their step-by-step hardware transition theorems:
 *      - Base step (`m = 0`): Enqueue initializes accumulator/stage-0 to `StageValAt initFn stepFn 0 inp`.
 *      - Inductive step (`m -> S m`): Stepping iterator or advancing pipeline stage `m` updates
 *        the value from `v = StageValAt initFn stepFn m inp` to
 *        `evalLetExpr (stepFn type v) = StageValAt initFn stepFn (S m) inp`.
 *      - Finish step (`m = n`): Finishing from `v = StageValAt initFn stepFn n inp` enqueues
 *        `evalLetExpr (finishFn type v) = evalLetExpr (specFn type inp)` into the output FIFO,
 *        which `first` then returns as `Some (evalLetExpr (specFn type inp))`.
 *)

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Export ShiftFifoLemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Definition _type_univ_anchor : Kind -> Type := type.

(* ===========================================================================
 * 1. GENERIC STAGED COMPUTATION (`StageValAt`) AND INDUCTIVE SPEC PROOF
 * =========================================================================== *)

Fixpoint StageValAt {InpK StateK : Kind}
  (initFn : forall (ty : Kind -> Type), ty InpK -> LetExpr ty StateK)
  (stepFn : forall (ty : Kind -> Type), ty StateK -> LetExpr ty StateK)
  (m : nat) (inp : type InpK) : type StateK :=
  match m with
  | 0%nat => evalLetExpr (initFn type inp)
  | S m'  => evalLetExpr (stepFn type (StageValAt initFn stepFn m' inp))
  end.

Section GenericStagedSpecCorrectness.
  Variable InpK StateK OutK : Kind.
  Variable initFn   : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn   : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn : forall ty, ty StateK -> LetExpr ty OutK.
  Variable specFn   : forall ty, ty InpK -> LetExpr ty OutK.

  (* Step-indexed invariant relating step `m`, original input `inp`, and accumulator `v` *)
  Variable StageInv : nat -> type InpK -> type StateK -> Prop.
  Variable targetSteps : type InpK -> nat.

  Hypothesis H_stage_init :
    forall inp : type InpK,
      StageInv 0%nat inp (evalLetExpr (initFn type inp)).

  Hypothesis H_stage_step :
    forall (m : nat) (inp : type InpK) (v : type StateK),
      (m < targetSteps inp)%nat ->
      StageInv m inp v ->
      StageInv (S m) inp (evalLetExpr (stepFn type v)).

  Hypothesis H_stage_finish :
    forall (inp : type InpK) (v : type StateK),
      StageInv (targetSteps inp) inp v ->
      evalLetExpr (finishFn type v) = evalLetExpr (specFn type inp).

  (* Generic theorem 1: At any step `m <= targetSteps inp`, the accumulator
   * `StageValAt initFn stepFn m inp` satisfies `StageInv m inp`. *)
  Theorem StageValAt_inv :
    forall (m : nat) (inp : type InpK),
      (m <= targetSteps inp)%nat ->
      StageInv m inp (StageValAt initFn stepFn m inp).
  Proof.
    induction m as [| m' IHm]; intros inp Hle; cbn [StageValAt].
    - apply H_stage_init.
    - apply H_stage_step; [lia | apply IHm; lia].
  Qed.

  (* Generic theorem 2: After `n = targetSteps inp` steps, applying `finishFn`
   * to `StageValAt initFn stepFn n inp` produces `evalLetExpr (specFn type inp)`. *)
  Theorem StageValAt_spec_correct :
    forall (inp : type InpK),
      evalLetExpr (finishFn type (StageValAt initFn stepFn (targetSteps inp) inp)) =
      evalLetExpr (specFn type inp).
  Proof.
    intros inp.
    apply H_stage_finish.
    apply StageValAt_inv.
    lia.
  Qed.

End GenericStagedSpecCorrectness.

(* ===========================================================================
 * 2. GENERIC ITERATIVE HARDWARE PROOF (SINGLE ACCUMULATOR, NO OUTPUT FIFO)
 * =========================================================================== *)

Definition iterStepsSz (num_stages : nat) : Z :=
  Z.max 1 (Z.log2_up (Z.of_nat num_stages + 1)).

Lemma iterStepsSz_pos : forall num_stages, 0 < iterStepsSz num_stages.
Proof.
  intros num_stages; unfold iterStepsSz; lia.
Qed.

Definition IterWorkState (num_stages : nat) (StateK : Kind) : Kind :=
  STRUCT_TYPE {
    "busy"     :: Bool ;
    "stepsRem" :: Bit (iterStepsSz num_stages) ;
    "state"    :: StateK
  }.

Section GenericIterativeHardwareProof.
  Variable dom : string.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Local Abbreviation stepsSz := (iterStepsSz num_stages).
  Variable numStepsFn : forall ty, ty InpK -> LetExpr ty (Bit stepsSz).
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.
  Variable specFn     : forall ty, ty InpK -> LetExpr ty OutK.

  Local Abbreviation WorkK := (IterWorkState num_stages StateK).

  (* Hardware state is JUST the single `work` register (`busy`, `stepsRem`, `state`). *)
  Definition stagedIterTree : Tree DomainElem :=
    Leaf "work" (dom, EReg (Build_Reg WorkK (Some (getDefault WorkK)) false)).

  Definition stagedWorkRegPath : RegPath stagedIterTree :=
    @Build_RegPath stagedIterTree tt I.

  Definition stagedIterCanEnq (ty : Kind -> Type) :
    Action ty stagedIterTree Bool :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      Return (Not (##w`"busy"))).

  Definition stagedIterEnq (ty : Kind -> Type) (inp : ty InpK) :
    Action ty stagedIterTree (Bit 0) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      If (Not (##w`"busy")) Then (
        LetL st0         : StateK      <- initFn ty inp ;
        LetL targetSteps : Bit stepsSz <- numStepsFn ty inp ;
        Let nextW : WorkK <- STRUCT {
          "busy"     ::= Const ty Bool true ;
          "stepsRem" ::= #targetSteps ;
          "state"    ::= #st0
        } ;
        WriteReg stagedWorkRegPath #nextW Retv
      ) Else (
        Retv
      ) ;
      Retv).

  Definition stagedIterStep (ty : Kind -> Type) :
    Action ty stagedIterTree (Bit 0) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      If (And [ ##w`"busy" ; isNotZero (##w`"stepsRem") ]) Then (
        Let curSt   : StateK <- ##w`"state" ;
        LetL nextSt : StateK <- stepFn ty curSt ;
        Let nextW : WorkK <- STRUCT {
          "busy"     ::= Const ty Bool true ;
          "stepsRem" ::= Sub (##w`"stepsRem") $1 ;
          "state"    ::= #nextSt
        } ;
        WriteReg stagedWorkRegPath #nextW Retv
      ) Else (
        Retv
      ) ;
      Retv).

  (* Reads directly from the accumulator when `busy && isZero stepsRem` *)
  Definition stagedIterFirst (ty : Kind -> Type) :
    Action ty stagedIterTree (Option OutK) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      Let lastSt  : StateK <- ##w`"state" ;
      LetL outVal : OutK   <- finishFn ty lastSt ;
      Return (ITE (And [ ##w`"busy" ; isZero (##w`"stepsRem") ])
                  (mkSome #outVal)
                  (mkNone ty))).

  (* Dequeues by clearing `busy <- false` *)
  Definition stagedIterDeq (ty : Kind -> Type) :
    Action ty stagedIterTree (Bit 0) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      If (And [ ##w`"busy" ; isZero (##w`"stepsRem") ]) Then (
        Let nextW : WorkK <- (##w `{ "busy" <- Const ty Bool false }) ;
        WriteReg stagedWorkRegPath #nextW Retv
      ) Else (
        Retv
      ) ;
      Retv).

  Definition stagedIterMod : Mod stagedIterTree :=
    fun ty => [ (dom, stagedIterStep ty) ].

  Definition IterTargetSteps (inp : type InpK) : nat :=
    Z.to_nat (Zmod.unsigned (evalLetExpr (numStepsFn type inp))).

  (* Step-indexed hardware state predicate:
   * At step `m`, the register `s` has `busy = true`, `stepsRem = IterTargetSteps inp - m`,
   * and `state = StageValAt initFn stepFn m inp`. *)
  Definition IterStateAtStep
    (inp : type InpK) (m : nat)
    (s : TreeState DomainElemState stagedIterTree) : Prop :=
    s @% "busy" = true /\
    (m <= IterTargetSteps inp)%nat /\
    Z.to_nat (Zmod.unsigned (s @% "stepsRem")) = (IterTargetSteps inp - m)%nat /\
    s @% "state" = StageValAt initFn stepFn m inp.

  Lemma unsigned_sub_ge : forall (w : Z) (a b : bits w),
    0 < w ->
    Zmod.unsigned b <= Zmod.unsigned a ->
    Zmod.unsigned (evalExpr (Sub (#a) (#b))) =
    Zmod.unsigned a - Zmod.unsigned b.
  Proof.
    intros w a b Hw Hle.
    cbn [evalExpr Sub fold_left map evalNot KindCustomInd].
    rewrite Zmod.add_0_l.
    rewrite !Zmod.unsigned_add.
    rewrite bits.unsigned_not' by lia.
    rewrite Z.ones_equiv; unfold Z.pred.
    unfold Zmod.one; rewrite Zmod.unsigned_of_Z.
    assert (H2w : 2 <= 2 ^ w).
    { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
    rewrite (Z.mod_small 1 (2 ^ w)) by lia.
    pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
    pose proof (bits.unsigned_range b ltac:(lia)) as Hb.
    rewrite Z.add_mod_idemp_l by lia.
    transitivity (((Zmod.unsigned a - Zmod.unsigned b) + 1 * 2 ^ w) mod 2 ^ w).
    { f_equal; lia. }
    rewrite Z.mod_add by lia.
    apply Z.mod_small; lia.
  Qed.

  Lemma evalExpr_Sub_Bit : forall w (a b : Expr type (Bit w)),
    0 < w ->
    Zmod.unsigned (evalExpr b) <= Zmod.unsigned (evalExpr a) ->
    Zmod.unsigned (evalExpr (Sub a b)) = Zmod.unsigned (evalExpr a) - Zmod.unsigned (evalExpr b).
  Proof.
    intros w a b Hw Hle.
    exact (unsigned_sub_ge w (evalExpr a) (evalExpr b) Hw Hle).
  Qed.

  (* Theorem 4A (Base step, `m = 0`):
   * If the iterative engine is idle (`busy = false`), enqueueing `inp` sets
   * the hardware state to step `m = 0` with accumulator `StageValAt initFn stepFn 0 inp`. *)
  Theorem Iter_Enq_Step0 :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedIterTree) ret,
      s @% "busy" = false ->
      SemAction (stagedIterEnq type inp) s s' ret ->
      IterStateAtStep inp 0%nat s'.
  Proof.
    intros inp [busy [stepsRem [st []]]] s' ret Hidle Hsem.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hidle.
    subst busy.
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedIterEnq, stagedWorkRegPath, stagedIterTree in Hinv.
    revert Hinv; cbn -[toAction stepsSz].
    rewrite evalActionPropGen_toAction; cbn -[toAction stepsSz].
    rewrite evalActionPropGen_toAction; cbn -[stepsSz]; intros [<- <-].
    unfold IterStateAtStep, IterTargetSteps; cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum StageValAt].
    split; [reflexivity | split; [lia | split; [lia | reflexivity]]].
  Qed.

  (* Theorem 4B (Inductive step, `m -> S m`):
   * If the iterative engine is at step `m < IterTargetSteps inp` with accumulator
   * `v = StageValAt initFn stepFn m inp`, then executing `stagedIterStep` advances
   * the hardware state to step `S m` with accumulator `StageValAt initFn stepFn (S m) inp`. *)
  Theorem Iter_Step_Inductive :
    forall (inp : type InpK) (m : nat) (s s' : TreeState DomainElemState stagedIterTree) ret,
      IterStateAtStep inp m s ->
      (m < IterTargetSteps inp)%nat ->
      SemAction (stagedIterStep type) s s' ret ->
      IterStateAtStep inp (S m) s'.
  Proof.
    intros inp m [busy [stepsRem [st []]]] s' ret
           [Hbusy [Hle [Hrem Hst]]] Hlt Hsem.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hbusy, Hrem, Hst.
    subst busy st.
    assert (Hsz_pos : 0 < stepsSz) by apply iterStepsSz_pos.
    assert (H2 : 2 <= 2 ^ stepsSz)
      by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
    assert (Hu1 : Zmod.unsigned (bits.of_Z stepsSz 1) = 1)
      by (rewrite bits.unsigned_of_Z, Z.mod_small by lia; reflexivity).
    assert (Hrem_pos : 1 <= Zmod.unsigned stepsRem).
    { pose proof (bits.unsigned_range stepsRem ltac:(lia)).
      assert ((1 <= Z.to_nat (Zmod.unsigned stepsRem))%nat) by lia.
      lia. }
    assert (Hnz : negb (Zmod.eqb stepsRem 0%Zmod) = true).
    { destruct (Zmod.eqb_spec stepsRem 0%Zmod) as [Hz | Hnz]; [| reflexivity].
      rewrite Hz, Zmod.unsigned_0 in Hrem_pos; lia. }
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedIterStep, stagedWorkRegPath, stagedIterTree in Hinv.
    revert Hinv; cbn -[toAction Sub stepsSz].
    change (negb (Zmod.eqb stepsRem (Zmod.of_Z (2 ^ stepsSz) 0))) with (negb (Zmod.eqb stepsRem 0%Zmod)).
    rewrite Hnz; cbn -[toAction Sub stepsSz].
    rewrite evalActionPropGen_toAction; cbn -[Sub stepsSz]; intros [<- <-].
    unfold IterStateAtStep; cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum StageValAt].
    split; [reflexivity | split; [lia | split; [| reflexivity]]].
    rewrite evalExpr_Sub_Bit; [| exact Hsz_pos | cbn -[stepsSz bits.of_Z]; rewrite Hu1; lia].
    cbn -[stepsSz bits.of_Z]; rewrite Hu1.
    rewrite Z2Nat.inj_sub by lia; change (Z.to_nat 1) with 1%nat.
    lia.
  Qed.

  (* Theorem 4C (Direct output read from accumulator at `m = IterTargetSteps inp`):
   * When `evalLetExpr (finishFn (StageValAt initFn stepFn (IterTargetSteps inp) inp)) = evalLetExpr (specFn inp)`
   * and the iterative engine reaches step `m = IterTargetSteps inp` (`stepsRem = 0`),
   * `stagedIterFirst` reads the accumulator directly and returns `Some (evalLetExpr (specFn type inp))`
   * with zero extra latency and no output FIFO. *)
  Theorem Iter_First_Spec :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedIterTree) optOut,
      evalLetExpr (finishFn type (StageValAt initFn stepFn (IterTargetSteps inp) inp)) =
        evalLetExpr (specFn type inp) ->
      IterStateAtStep inp (IterTargetSteps inp) s ->
      SemAction (stagedIterFirst type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type OutK (evalLetExpr (specFn type inp)))).
  Proof.
    intros inp [busy [stepsRem [st []]]] s' optOut Hspec
           [Hbusy [_ [Hrem Hst]]] Hsem.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hbusy, Hrem, Hst.
    subst busy st.
    assert (Hsz_pos : 0 < stepsSz) by apply iterStepsSz_pos.
    assert (Hz : Zmod.eqb stepsRem 0%Zmod = true).
    { destruct (Zmod.eqb_spec stepsRem 0%Zmod) as [_ | Hnz]; [reflexivity |].
      exfalso; apply Hnz, Zmod.unsigned_inj.
      pose proof (bits.unsigned_range stepsRem ltac:(lia)).
      rewrite Zmod.unsigned_0; lia. }
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedIterFirst, stagedWorkRegPath, stagedIterTree in Hinv.
    revert Hinv; cbn -[toAction mkSome mkNone stepsSz].
    change (Zmod.eqb stepsRem (Zmod.of_Z (2 ^ stepsSz) 0)) with (Zmod.eqb stepsRem 0%Zmod).
    rewrite Hz; cbn -[toAction mkSome mkNone stepsSz].
    rewrite evalActionPropGen_toAction; cbn -[mkSome mkNone stepsSz].
    intros [<- <-].
    rewrite Hspec.
    split; reflexivity.
  Qed.

  (* Theorem 4D (Dequeue clears `busy` at `m = IterTargetSteps inp`): *)
  Theorem Iter_Deq_Idle :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedIterTree) ret,
      IterStateAtStep inp (IterTargetSteps inp) s ->
      SemAction (stagedIterDeq type) s s' ret ->
      s' @% "busy" = false.
  Proof.
    intros inp [busy [stepsRem [st []]]] s' ret [Hbusy [_ [Hrem Hst]]] Hsem.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hbusy, Hrem, Hst.
    subst busy st.
    assert (Hsz_pos : 0 < stepsSz) by apply iterStepsSz_pos.
    assert (Hz : Zmod.eqb stepsRem 0%Zmod = true).
    { destruct (Zmod.eqb_spec stepsRem 0%Zmod) as [_ | Hnz]; [reflexivity |].
      exfalso; apply Hnz, Zmod.unsigned_inj.
      pose proof (bits.unsigned_range stepsRem ltac:(lia)).
      rewrite Zmod.unsigned_0; lia. }
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedIterDeq, stagedWorkRegPath, stagedIterTree in Hinv.
    revert Hinv; cbn -[stepsSz].
    change (Zmod.eqb stepsRem (Zmod.of_Z (2 ^ stepsSz) 0)) with (Zmod.eqb stepsRem 0%Zmod).
    rewrite Hz; cbn -[stepsSz]; intros [<- <-].
    reflexivity.
  Qed.

End GenericIterativeHardwareProof.

(* ===========================================================================
 * 5. GENERIC PIPELINED HARDWARE PROOF (NO EXTRA OUTPUT FIFO, NO FINISH RULE)
 * =========================================================================== *)

Section GenericPipelinedHardwareProof.
  Variable dom : string.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.
  Variable specFn     : forall ty, ty InpK -> LetExpr ty OutK.

  Fixpoint stagedStagesTail (n : nat) : list (Tree DomainElem) :=
    match n with
    | 0%nat => []
    | S m =>
        [ Node ("stages_" ++ hex_string_of_Z (Z.of_nat m))
               (fifoTree dom 1 StateK :: stagedStagesTail m) ]
    end.

  Definition stagedStagesTree (n : nat) : Tree DomainElem :=
    Node ("stages_" ++ hex_string_of_Z (Z.of_nat n))
         (fifoTree dom 1 StateK :: stagedStagesTail n).

  (* The pipeline tree is simply the chain of stage FIFOs `stagedStagesTree num_stages`
   * (no extra output FIFO and no extra latency cycle). *)
  Definition stagedPipeTree : Tree DomainElem :=
    stagedStagesTree num_stages.

  Fixpoint stagedLastFifo (n : nat) :
    TreeState DomainElemState (stagedStagesTree n) ->
    TreeState DomainElemState (fifoTree dom 1 StateK) :=
    match n return TreeState DomainElemState (stagedStagesTree n) ->
                   TreeState DomainElemState (fifoTree dom 1 StateK) with
    | 0%nat => fun s => s.(Fst)
    | S m   => fun s => stagedLastFifo m (s.(Snd).(Fst))
    end.

  Fixpoint stagedUpdateLastFifo (n : nat) :
    TreeState DomainElemState (stagedStagesTree n) ->
    TreeState DomainElemState (fifoTree dom 1 StateK) ->
    TreeState DomainElemState (stagedStagesTree n) :=
    match n return TreeState DomainElemState (stagedStagesTree n) ->
                   TreeState DomainElemState (fifoTree dom 1 StateK) ->
                   TreeState DomainElemState (stagedStagesTree n) with
    | 0%nat => fun _ f' => (f' ,, tt)
    | S m   => fun s f' => (s.(Fst) ,, (stagedUpdateLastFifo m (s.(Snd).(Fst)) f' ,, tt))
    end.

  Fixpoint stagedLiftLastStage {ty : Kind -> Type} {k : Kind}
    (n : nat)
    (a : Action ty (fifoTree dom 1 StateK) k) :
    Action ty (stagedStagesTree n) k :=
    match n with
    | 0%nat => liftAction child0Path a
    | S m   => liftAction child1Path (stagedLiftLastStage m a)
    end.

  Lemma evalActionPropGen_stagedLiftLastStage :
    forall (n : nat) {k : Kind}
           (a : Action type (fifoTree dom 1 StateK) k)
           (st : TreeState DomainElemState (stagedStagesTree n))
           (P : TreeState DomainElemState (stagedStagesTree n) -> type k -> Prop),
      evalActionPropGen (stagedLiftLastStage n a) st P <->
      evalActionPropGen a (stagedLastFifo n st) (fun f' v => P (stagedUpdateLastFifo n st f') v).
  Proof.
    induction n as [| m IHm]; intros k a st P;
      cbn [stagedLiftLastStage stagedLastFifo stagedUpdateLastFifo] in st, P |- *.
    - destruct st as [f0 []]; cbn [Fst Snd].
      unfold stagedStagesTree; cbn [stagedStagesTail].
      rewrite evalActionPropGen_liftAction_child0Path; reflexivity.
    - destruct st as [f_head [st_tail []]]; cbn [Fst Snd].
      unfold stagedStagesTree at 1; cbn [stagedStagesTail].
      rewrite evalActionPropGen_liftAction_child1Path.
      exact (IHm k a st_tail (fun f' v => P (f_head ,, (f' ,, tt)) v)).
  Qed.

  Definition stagedPipeCanEnq (ty : Kind -> Type) :
    Action ty stagedPipeTree Bool :=
    LetA full0 : Bool <- liftAction child0Path (@isFull dom 1 StateK ty) ;
    Return (Not #full0).

  Definition stagedPipeEnq (ty : Kind -> Type) (inp : ty InpK) :
    Action ty stagedPipeTree (Bit 0) :=
    LetL st0 : StateK <- initFn ty inp ;
    liftAction child0Path (@enq dom 1 StateK ty st0).

  Definition stagedPipeStepAdjacent (ty : Kind -> Type) (m : nat) :
    Action ty (stagedStagesTree (S m)) (Bit 0) :=
    LetA optIn : Option StateK <- liftAction child0Path (@first dom 1 StateK ty) ;
    LetA nextFull : Bool <-
      liftAction child1Path (liftAction child0Path (@isFull dom 1 StateK ty)) ;
    If (And [ #optIn`"valid" ; Not #nextFull ]) Then (
      Let curSt   : StateK <- #optIn`"data" ;
      LetL nextSt : StateK <- stepFn ty curSt ;
      LetA _ : Bit 0 <-
        liftAction child1Path (liftAction child0Path (@enq dom 1 StateK ty nextSt)) ;
      LetA _ : Bit 0 <- liftAction child0Path (@deq dom 1 StateK ty) ;
      Retv
    ) Else (
      Retv
    ) ;
    Retv.

  Fixpoint stagedPipeStageRulesChain (ty : Kind -> Type) (n : nat) :
    list (Action ty (stagedStagesTree n) (Bit 0)) :=
    match n with
    | 0%nat => []
    | S m =>
        stagedPipeStepAdjacent ty m ::
        map (fun r => liftAction child1Path r)
            (stagedPipeStageRulesChain ty m)
    end.

  Definition stagedPipeAllStageRules (ty : Kind -> Type) :
    list (Action ty stagedPipeTree (Bit 0)) :=
    stagedPipeStageRulesChain ty num_stages.

  Definition stagedPipeMod : Mod stagedPipeTree :=
    fun ty => map (fun r => (dom, r)) (stagedPipeAllStageRules ty).

  (* Reads directly from the final pipeline stage `stages_0` and applies `finishFn`
   * combinationally with zero extra latency. *)
  Definition stagedPipeFirst (ty : Kind -> Type) :
    Action ty stagedPipeTree (Option OutK) :=
    LetA optLast : Option StateK <-
      stagedLiftLastStage num_stages (@first dom 1 StateK ty) ;
    Let lastSt  : StateK <- #optLast`"data" ;
    LetL outVal : OutK   <- finishFn ty lastSt ;
    Return (ITE (#optLast`"valid")
                (mkSome #outVal)
                (mkNone ty)).

  (* Dequeues directly from the final pipeline stage `stages_0`. *)
  Definition stagedPipeDeq (ty : Kind -> Type) :
    Action ty stagedPipeTree (Bit 0) :=
    stagedLiftLastStage num_stages (@deq dom 1 StateK ty).

  (* Stage-indexed hardware FIFO predicate:
   * Stage `k` holds an active computation for `inp` iff its 1-element FIFO is full
   * (`fifo1_size = 1`) and its element equals `StageValAt initFn stepFn k inp`. *)
  Definition PipeStageAtStep
    (inp : type InpK) (k : nat)
    (f : TreeState DomainElemState (fifoTree dom 1 StateK)) : Prop :=
    fifo1_size f = Zmod.of_Z 2 1 /\
    fifo1_elem f = StageValAt initFn stepFn k inp.

  (* Theorem 5A (Base stage, `k = 0`):
   * If stage 0 is empty (`fifo1_size = 0`), enqueueing `inp` sets stage 0
   * to `PipeStageAtStep inp 0`. *)
  Theorem Pipe_Enq_Stage0 :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedPipeTree) ret,
      fifo1_size (s.(Fst)) = Zmod.of_Z 2 0 ->
      SemAction (stagedPipeEnq type inp) s s' ret ->
      PipeStageAtStep inp 0%nat (s'.(Fst)).
  Proof.
    intros inp [f0 st_rest] s' ret Hempty Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeEnq, stagedPipeTree, stagedStagesTree, PipeStageAtStep in Hempty, Hinv |- *.
    revert Hinv; cbn [evalActionPropGen Fst] in Hempty |- *.
    rewrite evalActionPropGen_toAction, evalActionPropGen_liftAction_child0Path,
            evalActionPropGen_fifo_enq, Hempty.
    cbn [negb Zmod.eqb]; intros [<- <-]; split; reflexivity.
  Qed.

  Lemma evalExpr_And2_Not : forall (a b : Expr type Bool),
    evalExpr (And [ a ; Not b ]) = andb (evalExpr a) (negb (evalExpr b)).
  Proof.
    intros a b; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b); reflexivity.
  Qed.

  Lemma evalExpr_mkSome_isSome : forall (v : type StateK),
    evalExpr ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v))))`"valid") = true.
  Proof.
    intros v; reflexivity.
  Qed.

  Lemma evalExpr_mkSome_data : forall (v : type StateK),
    evalExpr ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v))))`"data") = v.
  Proof.
    intros v; reflexivity.
  Qed.

  (* Theorem 5B (Inductive stage transition, `k -> S k`):
   * If the current stage satisfies `PipeStageAtStep inp k`
   * and the next stage is empty (`fifo1_size = 0`), executing `stagedPipeStepAdjacent m`
   * empties the current stage and establishes `PipeStageAtStep inp (S k)` on the next stage. *)
  Theorem Pipe_Step_Adjacent_Inductive :
    forall (inp : type InpK) (k m : nat)
           (st st' : TreeState DomainElemState (stagedStagesTree (S m))) ret,
      PipeStageAtStep inp k (st.(Fst)) ->
      fifo1_size (st.(Snd).(Fst).(Fst)) = Zmod.of_Z 2 0 ->
      SemAction (stagedPipeStepAdjacent type m) st st' ret ->
      fifo1_size (st'.(Fst)) = Zmod.of_Z 2 0 /\
      PipeStageAtStep inp (S k) (st'.(Snd).(Fst).(Fst)).
  Proof.
    intros inp k m [f_cur [[f_next st_tail] []]] st' ret [Hcur_full Hcur_val] Hnext_empty Hsem.
    unfold PipeStageAtStep.
    cbn [Fst Snd] in Hcur_full, Hcur_val, Hnext_empty.
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedPipeStepAdjacent, stagedStagesTree in Hinv.
    revert Hinv; cbn [stagedStagesTail evalActionPropGen].
    rewrite evalActionPropGen_liftAction_child0Path, (evalActionPropGen_fifo_first f_cur),
            Hcur_full, Hcur_val.
    change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [evalActionPropGen].
    rewrite evalActionPropGen_liftAction_child1Path,
            evalActionPropGen_liftAction_child0Path, (evalActionPropGen_fifo_isFull f_next), Hnext_empty.
    change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false.
    cbn [evalActionPropGen].
    rewrite evalExpr_And2_Not, evalExpr_mkSome_isSome.
    change (evalExpr (Var type Bool false)) with false.
    cbn [negb andb evalActionPropGen].
    rewrite evalExpr_mkSome_data; cbn [evalActionPropGen].
    rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
    rewrite evalActionPropGen_liftAction_child1Path,
            evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_enq, Hnext_empty.
    change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false.
    cbn [negb evalActionPropGen].
    rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_deq, Hcur_full.
    change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false.
    cbn [negb evalActionPropGen]; intros [<- <-]; repeat split; reflexivity.
  Qed.

  (* Theorem 5C (Direct pipeline output read at `k = num_stages`, zero extra latency):
   * When `evalLetExpr (finishFn (StageValAt initFn stepFn num_stages inp)) = evalLetExpr (specFn inp)`
   * and the final pipeline stage (`stagedLastFifo num_stages s`) satisfies `PipeStageAtStep inp num_stages`,
   * `stagedPipeFirst` reads the final stage, applies `finishFn` combinationally, and returns
   * `Some (evalLetExpr (specFn type inp))` without any extra `outFifo` or `Finish` rule. *)
  Theorem Pipe_First_Spec :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedPipeTree) optOut,
      evalLetExpr (finishFn type (StageValAt initFn stepFn num_stages inp)) =
        evalLetExpr (specFn type inp) ->
      PipeStageAtStep inp num_stages (stagedLastFifo num_stages s) ->
      SemAction (stagedPipeFirst type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type OutK (evalLetExpr (specFn type inp)))).
  Proof.
    intros inp s s' optOut Hspec [Hlast_full Hlast_val] Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeFirst, stagedPipeTree in s, s', Hinv.
    revert Hinv; cbn [evalActionPropGen].
    rewrite evalActionPropGen_stagedLiftLastStage,
            (evalActionPropGen_fifo_first (stagedLastFifo num_stages s)),
            Hlast_full, Hlast_val.
    change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [evalActionPropGen].
    rewrite evalExpr_mkSome_data; cbn [evalActionPropGen].
    rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
    assert (Hite : forall (v : type StateK) (out : type OutK),
              evalExpr (ITE ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v))))`"valid")
                            (mkSome (Var type OutK out))
                            (mkNone type)) =
              evalExpr (mkSome (Const type OutK out))).
    { intros v out; reflexivity. }
    rewrite Hite.
    assert (Hupd_id : forall (n : nat) (st : TreeState DomainElemState (stagedStagesTree n)),
              stagedUpdateLastFifo n st (stagedLastFifo n st) = st).
    { clear; induction n as [| m IHm]; intros st;
        [destruct st as [f0 []]; reflexivity
        | destruct st as [f_head [st_tail []]];
          cbn [stagedUpdateLastFifo stagedLastFifo Fst Snd]; rewrite IHm; reflexivity]. }
    rewrite Hupd_id, Hspec.
    intros [<- <-]; split; reflexivity.
  Qed.

  (* Theorem 5D (Pipeline output dequeue empties the final stage): *)
  Theorem Pipe_Deq_LastStage :
    forall (s s' : TreeState DomainElemState stagedPipeTree) ret,
      fifo1_size (stagedLastFifo num_stages s) = Zmod.of_Z 2 1 ->
      SemAction (stagedPipeDeq type) s s' ret ->
      fifo1_size (stagedLastFifo num_stages s') = Zmod.of_Z 2 0.
  Proof.
    intros s s' ret Hlast_full Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeDeq, stagedPipeTree in s, s', Hinv.
    revert Hinv.
    rewrite evalActionPropGen_stagedLiftLastStage, evalActionPropGen_fifo_deq, Hlast_full.
    change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [negb].
    intros [<- <-].
    assert (Hlast_upd : forall (n : nat) (st : TreeState DomainElemState (stagedStagesTree n)) f',
              stagedLastFifo n (stagedUpdateLastFifo n st f') = f').
    { clear; induction n as [| m IHm]; intros st f';
        [destruct st as [f0 []]; reflexivity
        | destruct st as [f_head [st_tail []]];
          cbn [stagedUpdateLastFifo stagedLastFifo Fst Snd]; apply IHm]. }
    rewrite Hlast_upd; reflexivity.
  Qed.

End GenericPipelinedHardwareProof.
