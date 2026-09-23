(*
 * Copyright (c) 2026 Peak AI / Google LLC
 *
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
From Guru Require Import Library Syntax Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Import Fifo.

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
 * 2. GENERIC 1-ELEMENT FIFO HELPERS AND SEMANTIC EVALUATION LEMMAS
 * =========================================================================== *)

Lemma Kind_eq_dec : forall k1 k2 : Kind, {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2.
  case_eq (Kind_eqb k1 k2); intros Heq; [left | right];
    pose proof (Kind_BoolSpec k1 k2) as Hspec;
    rewrite Heq in Hspec; inversion Hspec; assumption.
Qed.

Lemma Kind_eqb_refl : forall k : Kind, Kind_eqb k k = true.
Proof.
  intros k.
  destruct (Kind_BoolSpec k k) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
Qed.

Lemma Kind_uip_refl : forall (k : Kind) (pf : k = k), pf = eq_refl.
Proof.
  intros k pf.
  apply (UIP_dec Kind_eq_dec).
Qed.

Lemma eq_rect_Kind_refl : forall (k : Kind) (P : Kind -> Type) (v : P k) (pf : k = k),
  eq_rect k P v k pf = v.
Proof.
  intros k P v pf.
  rewrite (Kind_uip_refl k pf).
  reflexivity.
Qed.

Lemma Zmod_1_0 : forall x : Zmod 1, x = Zmod.zero.
Proof.
  intros x; apply Zmod.unsigned_inj; pose proof (Zmod.unsigned_pos_bound x eq_refl); rewrite Zmod.unsigned_0; lia.
Qed.

Definition fifo1_elem {dom : string} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) : type elemK :=
  f.(Fst).(Fst).

Definition fifo1_size {dom : string} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) : bits 1 :=
  f.(Snd).(Fst).

Definition mkFifo1 {dom : string} {elemK : Kind}
  (e : type elemK) (sz : bits 1) :
  TreeState DomainElemState (fifoTree dom 1 elemK) :=
  ((e ,, tt) ,, (sz ,, (Zmod.zero ,, tt))).

Lemma elemPathsWithKind_1 : forall dom (elemK : Kind),
  exists (rk : RegOfKind (t := fifoTree dom 1 elemK) elemK),
    elemPathsWithKind dom 1 elemK = [rk] /\
    rk.(rk_path).(regPath) = inl (inl tt).
Proof.
  intros dom elemK.
  unfold elemPathsWithKind, getTreeRegsOfKind.
  cbn -[Kind_eqb].
  pose (target_prop := Is_true (Kind_eqb elemK elemK)).
  set (mk_pf := fun pf : Kind_eqb elemK elemK = true =>
    (eq_rect_r (fun b' : bool => Is_true b') (I : Is_true true) pf : target_prop)).
  change (eq_rect_r (fun b' : bool => Is_true b') (I : Is_true true)) with mk_pf.
  generalize (eq_refl (Kind_eqb elemK elemK)).
  generalize mk_pf.
  rewrite (Kind_eqb_refl elemK).
  intros mk_pf' pf.
  eexists. split; reflexivity.
Qed.

Lemma evalActionPropGen_fifo_isFull : forall {dom elemK}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen (@isFull dom 1 elemK type) f P <->
  P f (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 1)).
Proof. reflexivity. Qed.

Lemma iff_f_equal2 : forall A B (P : A -> B -> Prop) x1 x2 y1 y2,
  x1 = x2 -> y1 = y2 -> (P x1 y1 <-> P x2 y2).
Proof. intros; subst; reflexivity. Qed.

Ltac destruct_ifs :=
  repeat match goal with
  | |- context [if ?c then _ else _] =>
      let H := fresh "Hif" in
      destruct c eqn:H
  end;
  try (exfalso; match goal with
       | H1 : ?x = true, H2 : ?y = false |- _ =>
           assert (x = y) by reflexivity; congruence
       end).

Lemma evalActionPropGen_fifo_deq : forall {dom elemK}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen (@deq dom 1 elemK type) f P <->
  P (if negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0))
     then mkFifo1 (fifo1_elem f) (evalExpr (Sub (Const type (Bit 1) (fifo1_size f)) $1))
     else f) Zmod.zero.
Proof.
  intros dom elemK [[e []] [sz [d []]]] P.
  unfold deq, fifo1_elem, fifo1_size, mkFifo1; simpl.
  destruct_ifs; simpl;
    [apply iff_f_equal2; [repeat f_equal; apply Zmod_1_0 | reflexivity] | reflexivity].
Qed.

Lemma evalActionPropGen_fifo_enq : forall {dom elemK} (val : type elemK)
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen (@enq dom 1 elemK type val) f P <->
  P (if negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 1))
     then mkFifo1 val (evalExpr (Add [Const type (Bit 1) (fifo1_size f); $1]))
     else f) Zmod.zero.
Proof.
  intros dom elemK val [[e []] [sz [d []]]] P.
  unfold enq, isFull, writeRegsList, fifo1_elem, fifo1_size, mkFifo1.
  destruct (elemPathsWithKind_1 dom elemK) as [[rk_p rk_pf] [Hpaths Hreg]].
  rewrite Hpaths.
  cbn -[writeTreeState readTreeState castStateRegInv].
  match goal with |- context [Zmod.eqb ?x (Zmod.of_Z 1 0)] => rewrite (Zmod_1_0 x) end.
  change (Zmod.eqb Zmod.zero (Zmod.of_Z 1 0)) with true; simpl.
  destruct_ifs; simpl; [| reflexivity].
  destruct rk_p as [rp rp_pf]; simpl in Hreg; subst rp.
  apply iff_f_equal2; [| reflexivity].
  cbn [writeTreeState castStateRegInv getRegFromPathTypeEq getRegFromElemTypeEq getLeafElem Fst Snd].
  rewrite eq_rect_Kind_refl; cbn [evalExpr]; rewrite (Zmod_1_0 d); reflexivity.
Qed.

Lemma evalActionPropGen_fifo_first : forall {dom elemK}
  (H_or_def : forall x : type elemK, evalOrBinary (getDefault elemK) x = x)
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen (@first dom 1 elemK type) f P <->
  P f (if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)
       then evalExpr (mkNone type)
       else evalExpr (mkSome (Const type elemK (fifo1_elem f)))).
Proof.
  intros dom elemK H_or_def [[e []] [sz [d []]]] P.
  unfold first, readRegsList, fifo1_elem, fifo1_size.
  destruct (elemPathsWithKind_1 dom elemK) as [[rk_p rk_pf] [Hpaths Hreg]].
  rewrite Hpaths.
  destruct rk_p as [rp rp_pf]; simpl in Hreg; subst rp.
  cbn -[evalOrBinary getDefault].
  rewrite (Zmod_1_0 d).
  change (Zmod.eqb Zmod.zero (Zmod.of_Z 1 0)) with true.
  apply iff_f_equal2; [reflexivity |].
  rewrite eq_rect_Kind_refl; cbn [evalExpr fold_left map ITE0]; rewrite H_or_def; reflexivity.
Qed.

Lemma some_tag_true_iff : forall {dom elemK} (f : TreeState DomainElemState (fifoTree dom 1 elemK)),
  evalExpr ((Const type (Option elemK)
              (if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)
               then evalExpr (mkNone type (k := elemK))
               else evalExpr (mkSome (Const type elemK (fifo1_elem f))))) `? "Some") =
  negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)).
Proof.
  intros dom elemK f; destruct (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)); reflexivity.
Qed.

Lemma some_data_extract : forall {dom elemK}
  (H_size : 0 <= kindSize elemK)
  (H_from_to : forall x : type elemK, @evalFromBit elemK (evalToBit x) = x)
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)),
  Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0) = false ->
  evalExpr ((Const type (Option elemK)
              (if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)
               then evalExpr (mkNone type (k := elemK))
               else evalExpr (mkSome (Const type elemK (fifo1_elem f))))) `! "Some") =
  fifo1_elem f.
Proof.
  intros dom elemK H_size H_from_to f Hne; rewrite Hne.
  cbn [evalExpr mkSome optionList Fst nth_pf finNum snd max_list map kindSize].
  rewrite <- (H_from_to (fifo1_elem f)) at 2; f_equal.
  apply Zmod.unsigned_inj.
  unfold Zmod.to_Z; change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  rewrite !Zmod.unsigned_of_Z.
  replace (Z.max 0 (Z.max (kindSize elemK) 0)) with (kindSize elemK) by lia.
  pose proof (bits.unsigned_range (evalToBit (fifo1_elem f)) H_size) as H_range.
  rewrite !(Z.mod_small _ _ H_range); reflexivity.
Qed.

Lemma some_tag_true_iff_var : forall {dom elemK} (f : TreeState DomainElemState (fifoTree dom 1 elemK)),
  evalExpr ((Var type (Option elemK)
              (if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)
               then evalExpr (mkNone type (k := elemK))
               else evalExpr (mkSome (Const type elemK (fifo1_elem f))))) `? "Some") =
  negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)).
Proof.
  intros dom elemK f; apply some_tag_true_iff.
Qed.

Lemma some_data_extract_var : forall {dom elemK}
  (H_size : 0 <= kindSize elemK)
  (H_from_to : forall x : type elemK, @evalFromBit elemK (evalToBit x) = x)
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)),
  Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0) = false ->
  evalExpr ((Var type (Option elemK)
              (if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)
               then evalExpr (mkNone type (k := elemK))
               else evalExpr (mkSome (Const type elemK (fifo1_elem f))))) `! "Some") =
  fifo1_elem f.
Proof.
  intros dom elemK H_size H_from_to f Hne; apply (some_data_extract H_size H_from_to f Hne).
Qed.

(* ===========================================================================
 * 3. GENERIC ACTION-LIFTING HELPERS
 * =========================================================================== *)

Fixpoint stagedLiftHead {ty : Kind -> Type} {name : string}
  {x : Tree DomainElem} {xs : list (Tree DomainElem)} {k : Kind}
  (a : Action ty x k) : Action ty (Node name (x :: xs)) k :=
  match a with
  | ReadReg s x_reg cont =>
      ReadReg s (@Build_RegPath (Node name (x :: xs)) (inl x_reg.(regPath)) x_reg.(regPathPf))
              (fun v => stagedLiftHead (cont v))
  | WriteReg x_reg v cont =>
      WriteReg (@Build_RegPath (Node name (x :: xs)) (inl x_reg.(regPath)) x_reg.(regPathPf)) v
               (stagedLiftHead cont)
  | ReadRqMem m i port cont =>
      ReadRqMem (@Build_MemPath (Node name (x :: xs)) (inl m.(memPath)) m.(memPathPf)) i port
                (stagedLiftHead cont)
  | ReadRpMem s m port cont =>
      ReadRpMem s (@Build_MemPath (Node name (x :: xs)) (inl m.(memPath)) m.(memPathPf)) port
                (fun v => stagedLiftHead (cont v))
  | WriteMem m i v cont =>
      WriteMem (@Build_MemPath (Node name (x :: xs)) (inl m.(memPath)) m.(memPathPf)) i v
               (stagedLiftHead cont)
  | Send p v cont =>
      Send (@Build_SendPath (Node name (x :: xs)) (inl p.(sendPath)) p.(sendPathPf)) v
           (stagedLiftHead cont)
  | Recv s p cont =>
      Recv s (@Build_RecvPath (Node name (x :: xs)) (inl p.(recvPath)) p.(recvPathPf))
           (fun v => stagedLiftHead (cont v))
  | LetExp s e cont =>
      LetExp s e (fun v => stagedLiftHead (cont v))
  | LetAction s a' cont =>
      LetAction s (stagedLiftHead a') (fun v => stagedLiftHead (cont v))
  | NonDet s k' cont =>
      NonDet s k' (fun v => stagedLiftHead (cont v))
  | IfElse s p a1 a2 cont =>
      IfElse s p (stagedLiftHead a1) (stagedLiftHead a2) (fun v => stagedLiftHead (cont v))
  | System sys cont =>
      System sys (stagedLiftHead cont)
  | Return e =>
      Return e
  end.

Fixpoint stagedLiftTail {ty : Kind -> Type} {name : string}
  {x : Tree DomainElem} {xs : list (Tree DomainElem)} {k : Kind}
  (a : Action ty (Node name xs) k) : Action ty (Node name (x :: xs)) k :=
  match a with
  | ReadReg s x_reg cont =>
      ReadReg s (@Build_RegPath (Node name (x :: xs)) (inr x_reg.(regPath)) x_reg.(regPathPf))
              (fun v => stagedLiftTail (cont v))
  | WriteReg x_reg v cont =>
      WriteReg (@Build_RegPath (Node name (x :: xs)) (inr x_reg.(regPath)) x_reg.(regPathPf)) v
               (stagedLiftTail cont)
  | ReadRqMem m i port cont =>
      ReadRqMem (@Build_MemPath (Node name (x :: xs)) (inr m.(memPath)) m.(memPathPf)) i port
                (stagedLiftTail cont)
  | ReadRpMem s m port cont =>
      ReadRpMem s (@Build_MemPath (Node name (x :: xs)) (inr m.(memPath)) m.(memPathPf)) port
                (fun v => stagedLiftTail (cont v))
  | WriteMem m i v cont =>
      WriteMem (@Build_MemPath (Node name (x :: xs)) (inr m.(memPath)) m.(memPathPf)) i v
               (stagedLiftTail cont)
  | Send p v cont =>
      Send (@Build_SendPath (Node name (x :: xs)) (inr p.(sendPath)) p.(sendPathPf)) v
           (stagedLiftTail cont)
  | Recv s p cont =>
      Recv s (@Build_RecvPath (Node name (x :: xs)) (inr p.(recvPath)) p.(recvPathPf))
           (fun v => stagedLiftTail (cont v))
  | LetExp s e cont =>
      LetExp s e (fun v => stagedLiftTail (cont v))
  | LetAction s a' cont =>
      LetAction s (stagedLiftTail a') (fun v => stagedLiftTail (cont v))
  | NonDet s k' cont =>
      NonDet s k' (fun v => stagedLiftTail (cont v))
  | IfElse s p a1 a2 cont =>
      IfElse s p (stagedLiftTail a1) (stagedLiftTail a2) (fun v => stagedLiftTail (cont v))
  | System sys cont =>
      System sys (stagedLiftTail cont)
  | Return e =>
      Return e
  end.

Lemma evalActionPropGen_toAction :
  forall {t k} (le : LetExpr type k) s P,
    evalActionPropGen (@toAction type t k le) s P <-> P s (evalLetExpr le).
Proof.
  intros t k le.
  induction le; intros s0 P; cbn [toAction evalActionPropGen evalLetExpr].
  - tauto.
  - apply IHle.
  - rewrite IHle. apply H.
  - destruct (evalExpr p); [rewrite IHle1 | rewrite IHle2]; apply H.
Qed.

Lemma evalActionPropGen_stagedLiftHead :
  forall {name x xs k} (a : @Action type x k) sx sxs P,
    evalActionPropGen (@stagedLiftHead type name x xs k a) (sx ,, sxs) P <->
    evalActionPropGen a sx (fun sx' r => P (sx' ,, sxs) r).
Proof.
  intros name x xs k a.
  induction a; intros sx sxs P;
    cbn -[castStateReg castStateRegInv castStateMem castStateMemInv
          castStateSend castStateSendInv castStateRecv castStateRecvInv];
    try tauto; try apply H; try apply IHa.
  - split; intros [v Hv]; exists v; apply H; exact Hv.
  - rewrite IHa. split; intros Ha; (eapply evalActionPropGen_mono; [| exact Ha]);
      intros s1 r1 Hs1; apply H; exact Hs1.
  - split; intros [v Hv]; exists v; apply H; exact Hv.
  - destruct (evalExpr p).
    + rewrite IHa1. split; intros Ha; (eapply evalActionPropGen_mono; [| exact Ha]);
        intros s1 r1 Hs1; apply H; exact Hs1.
    + rewrite IHa2. split; intros Ha; (eapply evalActionPropGen_mono; [| exact Ha]);
        intros s1 r1 Hs1; apply H; exact Hs1.
Qed.

Lemma evalActionPropGen_stagedLiftTail :
  forall {name x xs k} (a : @Action type (Node name xs) k) sx sxs P,
    evalActionPropGen (@stagedLiftTail type name x xs k a) (sx ,, sxs) P <->
    evalActionPropGen a sxs (fun sxs' r => P (sx ,, sxs') r).
Proof.
  intros name x xs k a.
  induction a; intros sx sxs P;
    cbn -[castStateReg castStateRegInv castStateMem castStateMemInv
          castStateSend castStateSendInv castStateRecv castStateRecvInv];
    try tauto; try apply H; try apply IHa.
  - split; intros [v Hv]; exists v; apply H; exact Hv.
  - rewrite IHa. split; intros Ha; (eapply evalActionPropGen_mono; [| exact Ha]);
      intros s1 r1 Hs1; apply H; exact Hs1.
  - split; intros [v Hv]; exists v; apply H; exact Hv.
  - destruct (evalExpr p).
    + rewrite IHa1. split; intros Ha; (eapply evalActionPropGen_mono; [| exact Ha]);
        intros s1 r1 Hs1; apply H; exact Hs1.
    + rewrite IHa2. split; intros Ha; (eapply evalActionPropGen_mono; [| exact Ha]);
        intros s1 r1 Hs1; apply H; exact Hs1.
Qed.

(* ===========================================================================
 * 4. GENERIC ITERATIVE HARDWARE PROOF (SINGLE ACCUMULATOR, NO OUTPUT FIFO)
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
  Local Notation stepsSz := (iterStepsSz num_stages).
  Variable numStepsFn : forall ty, ty InpK -> Expr ty (Bit stepsSz).
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.
  Variable specFn     : forall ty, ty InpK -> LetExpr ty OutK.

  Local Notation WorkK := (IterWorkState num_stages StateK).

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
        LetL st0 : StateK <- initFn ty inp ;
        Let nextW : WorkK <- STRUCT {
          "busy"     ::= Const ty Bool true ;
          "stepsRem" ::= numStepsFn ty inp ;
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
    Z.to_nat (Zmod.unsigned (evalExpr (numStepsFn type inp))).

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
      (0 <= kindSize OutK)%Z ->
      (forall x : type OutK, @evalFromBit OutK (evalToBit x) = x) ->
      evalLetExpr (finishFn type (StageValAt initFn stepFn (IterTargetSteps inp) inp)) =
        evalLetExpr (specFn type inp) ->
      IterStateAtStep inp (IterTargetSteps inp) s ->
      SemAction (stagedIterFirst type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type OutK (evalLetExpr (specFn type inp)))) /\
      evalExpr ((Const type (Option OutK) optOut) `? "Some") = true /\
      evalExpr ((Const type (Option OutK) optOut) `! "Some") = evalLetExpr (specFn type inp).
  Proof.
    intros inp [busy [stepsRem [st []]]] s' optOut Hsz Hfrom Hspec
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
    split; [reflexivity | split; [reflexivity | split]].
    - reflexivity.
    - exact (some_data_extract Hsz Hfrom
               (@mkFifo1 dom OutK (evalLetExpr (specFn type inp)) (Zmod.of_Z 2 1)) eq_refl).
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

  Hypothesis H_or_StateK : forall x : type StateK, evalOrBinary (getDefault StateK) x = x.
  Hypothesis H_sz_StateK : (0 <= kindSize StateK)%Z.
  Hypothesis H_fb_StateK : forall x : type StateK, @evalFromBit StateK (evalToBit x) = x.

  Fixpoint stagedStagesTree (n : nat) : Tree DomainElem :=
    match n with
    | 0%nat =>
        Node "stages_0" [ fifoTree dom 1 StateK ]
    | S m =>
        Node ("stages_" ++ hex_string_of_Z (Z.of_nat (S m)))
             [ fifoTree dom 1 StateK ;
               stagedStagesTree m ]
    end.

  (* The pipeline tree is simply the chain of stage FIFOs `stagedStagesTree num_stages`
   * (no extra output FIFO and no extra latency cycle). *)
  Definition stagedPipeTree : Tree DomainElem :=
    stagedStagesTree num_stages.

  Definition stagedHeadFifo (n : nat)
    (st : TreeState DomainElemState (stagedStagesTree n)) :
    TreeState DomainElemState (fifoTree dom 1 StateK) :=
    match n return TreeState DomainElemState (stagedStagesTree n) ->
                   TreeState DomainElemState (fifoTree dom 1 StateK) with
    | 0%nat => fun s => s.(Fst)
    | S _   => fun s => s.(Fst)
    end st.

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
    | 0%nat => stagedLiftHead a
    | S m   => stagedLiftTail (stagedLiftHead (stagedLiftLastStage m a))
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
      cbn [stagedLiftLastStage stagedStagesTree stagedLastFifo stagedUpdateLastFifo] in st, P |- *.
    - destruct st as [f0 []]; cbn [Fst Snd].
      rewrite evalActionPropGen_stagedLiftHead; reflexivity.
    - destruct st as [f_head [st_tail []]]; cbn [Fst Snd].
      rewrite evalActionPropGen_stagedLiftTail, evalActionPropGen_stagedLiftHead, IHm; reflexivity.
  Qed.

  Definition stagedPipeCanEnq (ty : Kind -> Type) :
    Action ty stagedPipeTree Bool :=
    LetA full0 : Bool <-
      match num_stages return Action ty (stagedStagesTree num_stages) Bool with
      | 0%nat => stagedLiftHead (@isFull dom 1 StateK ty)
      | S _   => stagedLiftHead (@isFull dom 1 StateK ty)
      end ;
    Return (Not #full0).

  Definition stagedPipeEnq (ty : Kind -> Type) (inp : ty InpK) :
    Action ty stagedPipeTree (Bit 0) :=
    LetL st0 : StateK <- initFn ty inp ;
    match num_stages return Action ty (stagedStagesTree num_stages) (Bit 0) with
    | 0%nat => stagedLiftHead (@enq dom 1 StateK ty st0)
    | S _   => stagedLiftHead (@enq dom 1 StateK ty st0)
    end.

  Definition stagedPipeStepAdjacent (ty : Kind -> Type) (m : nat) :
    Action ty (stagedStagesTree (S m)) (Bit 0) :=
    LetA optIn : Option StateK <- stagedLiftHead (@first dom 1 StateK ty) ;
    LetA nextFull : Bool <-
      stagedLiftTail (stagedLiftHead
        (match m return Action ty (stagedStagesTree m) Bool with
         | 0%nat => stagedLiftHead (@isFull dom 1 StateK ty)
         | S _   => stagedLiftHead (@isFull dom 1 StateK ty)
         end)) ;
    If (And [ #optIn `? "Some" ; Not #nextFull ]) Then (
      Let curSt   : StateK <- #optIn `! "Some" ;
      LetL nextSt : StateK <- stepFn ty curSt ;
      LetA _ : Bit 0 <-
        stagedLiftTail (stagedLiftHead
          (match m return Action ty (stagedStagesTree m) (Bit 0) with
           | 0%nat => stagedLiftHead (@enq dom 1 StateK ty nextSt)
           | S _   => stagedLiftHead (@enq dom 1 StateK ty nextSt)
           end)) ;
      LetA _ : Bit 0 <- stagedLiftHead (@deq dom 1 StateK ty) ;
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
        map (fun r => stagedLiftTail (stagedLiftHead r))
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
    Let lastSt  : StateK <- #optLast `! "Some" ;
    LetL outVal : OutK   <- finishFn ty lastSt ;
    Return (ITE (#optLast `? "Some")
                (mkSome #outVal)
                (mkNone ty)).

  (* Dequeues directly from the final pipeline stage `stages_0`. *)
  Definition stagedPipeDeq (ty : Kind -> Type) :
    Action ty stagedPipeTree (Bit 0) :=
    stagedLiftLastStage num_stages (@deq dom 1 StateK ty).

  (* Theorem 5A (Base stage, `k = 0`):
   * If stage 0 is empty (`fifo1_size = 0`), enqueueing `inp` sets stage 0
   * to `fifo1_size = 1` with element `StageValAt initFn stepFn 0 inp`. *)
  Theorem Pipe_Enq_Stage0 :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedPipeTree) ret,
      fifo1_size (stagedHeadFifo num_stages s) = Zmod.of_Z 2 0 ->
      SemAction (stagedPipeEnq type inp) s s' ret ->
      fifo1_size (stagedHeadFifo num_stages s') = Zmod.of_Z 2 1 /\
      fifo1_elem (stagedHeadFifo num_stages s') = StageValAt initFn stepFn 0 inp.
  Proof.
    intros inp s s' ret Hempty Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeEnq, stagedPipeTree in s, s', Hinv.
    revert Hinv; cbn [evalActionPropGen]; rewrite evalActionPropGen_toAction.
    destruct num_stages as [| m]; destruct s as [f0 st_rest];
      cbn [stagedStagesTree stagedHeadFifo Fst Snd] in Hempty |- *;
      rewrite evalActionPropGen_stagedLiftHead, evalActionPropGen_fifo_enq, Hempty;
      cbn [negb Zmod.eqb]; intros [<- <-]; split; reflexivity.
  Qed.

  Lemma evalExpr_And2_Not : forall (a b : Expr type Bool),
    evalExpr (And [ a ; Not b ]) = andb (evalExpr a) (negb (evalExpr b)).
  Proof.
    intros a b; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b); reflexivity.
  Qed.

  Lemma evalExpr_mkSome_isSome : forall (v : type StateK),
    evalExpr ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v)))) `? "Some") = true.
  Proof.
    intros v; reflexivity.
  Qed.

  Lemma evalExpr_mkSome_data : forall (v : type StateK),
    evalExpr ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v)))) `! "Some") = v.
  Proof.
    intros v.
    exact (some_data_extract_var H_sz_StateK H_fb_StateK (@mkFifo1 dom StateK v (Zmod.of_Z 2 1)) eq_refl).
  Qed.

  (* Theorem 5B (Inductive stage transition, `k -> S k`):
   * If the current stage holds `StageValAt initFn stepFn k inp` (`fifo1_size = 1`)
   * and the next stage is empty (`fifo1_size = 0`), executing `stagedPipeStepAdjacent m`
   * empties the current stage and sets the next stage to `StageValAt initFn stepFn (S k) inp`. *)
  Theorem Pipe_Step_Adjacent_Inductive :
    forall (inp : type InpK) (k m : nat)
           (st st' : TreeState DomainElemState (stagedStagesTree (S m))) ret,
      fifo1_size (st.(Fst)) = Zmod.of_Z 2 1 ->
      fifo1_elem (st.(Fst)) = StageValAt initFn stepFn k inp ->
      fifo1_size (stagedHeadFifo m (st.(Snd).(Fst))) = Zmod.of_Z 2 0 ->
      SemAction (stagedPipeStepAdjacent type m) st st' ret ->
      fifo1_size (st'.(Fst)) = Zmod.of_Z 2 0 /\
      fifo1_size (stagedHeadFifo m (st'.(Snd).(Fst))) = Zmod.of_Z 2 1 /\
      fifo1_elem (stagedHeadFifo m (st'.(Snd).(Fst))) = StageValAt initFn stepFn (S k) inp.
  Proof.
    intros inp k m [f_cur [st_next []]] st' ret Hcur_full Hcur_val Hnext_empty Hsem.
    cbn [Fst Snd] in Hcur_full, Hcur_val, Hnext_empty.
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedPipeStepAdjacent in Hinv.
    revert Hinv; cbn [stagedStagesTree evalActionPropGen].
    rewrite evalActionPropGen_stagedLiftHead, (evalActionPropGen_fifo_first H_or_StateK f_cur),
            Hcur_full, Hcur_val.
    change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [evalActionPropGen].
    destruct m as [| m']; destruct st_next as [f_next st_tail];
      cbn [stagedStagesTree stagedHeadFifo Fst Snd] in Hnext_empty |- *;
      rewrite evalActionPropGen_stagedLiftTail, evalActionPropGen_stagedLiftHead,
              evalActionPropGen_stagedLiftHead, (evalActionPropGen_fifo_isFull f_next), Hnext_empty;
      change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false;
      cbn [evalActionPropGen];
      rewrite evalExpr_And2_Not, evalExpr_mkSome_isSome;
      change (evalExpr (Var type Bool false)) with false;
      cbn [negb andb evalActionPropGen];
      rewrite evalExpr_mkSome_data;
      cbn [evalActionPropGen];
      rewrite evalActionPropGen_toAction; cbn [evalActionPropGen];
      rewrite evalActionPropGen_stagedLiftTail, evalActionPropGen_stagedLiftHead,
              evalActionPropGen_stagedLiftHead, evalActionPropGen_fifo_enq, Hnext_empty;
      change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false;
      cbn [negb evalActionPropGen];
      rewrite evalActionPropGen_stagedLiftHead, evalActionPropGen_fifo_deq, Hcur_full;
      change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false;
      cbn [negb evalActionPropGen]; intros [<- <-]; repeat split; reflexivity.
  Qed.

  (* Theorem 5C (Direct pipeline output read at `k = num_stages`, zero extra latency):
   * When `evalLetExpr (finishFn (StageValAt initFn stepFn num_stages inp)) = evalLetExpr (specFn inp)`
   * and the final pipeline stage (`stagedLastFifo num_stages s`) holds `StageValAt initFn stepFn num_stages inp`,
   * `stagedPipeFirst` reads the final stage, applies `finishFn` combinationally, and returns
   * `Some (evalLetExpr (specFn type inp))` without any extra `outFifo` or `Finish` rule. *)
  Theorem Pipe_First_Spec :
    forall (inp : type InpK) (s s' : TreeState DomainElemState stagedPipeTree) optOut,
      (0 <= kindSize OutK)%Z ->
      (forall x : type OutK, @evalFromBit OutK (evalToBit x) = x) ->
      evalLetExpr (finishFn type (StageValAt initFn stepFn num_stages inp)) =
        evalLetExpr (specFn type inp) ->
      fifo1_size (stagedLastFifo num_stages s) = Zmod.of_Z 2 1 ->
      fifo1_elem (stagedLastFifo num_stages s) = StageValAt initFn stepFn num_stages inp ->
      SemAction (stagedPipeFirst type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type OutK (evalLetExpr (specFn type inp)))) /\
      evalExpr ((Const type (Option OutK) optOut) `? "Some") = true /\
      evalExpr ((Const type (Option OutK) optOut) `! "Some") = evalLetExpr (specFn type inp).
  Proof.
    intros inp s s' optOut Hsz Hfrom Hspec Hlast_full Hlast_val Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeFirst, stagedPipeTree in s, s', Hinv.
    revert Hinv; cbn [evalActionPropGen].
    rewrite evalActionPropGen_stagedLiftLastStage,
            (evalActionPropGen_fifo_first H_or_StateK (stagedLastFifo num_stages s)),
            Hlast_full, Hlast_val.
    change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [evalActionPropGen].
    rewrite evalExpr_mkSome_data; cbn [evalActionPropGen].
    rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
    assert (Hite : forall (v : type StateK) (out : type OutK),
              evalExpr (ITE ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v)))) `? "Some")
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
    intros [<- <-].
    split; [reflexivity | split; [reflexivity | split]].
    - reflexivity.
    - exact (some_data_extract Hsz Hfrom
               (@mkFifo1 dom OutK (evalLetExpr (specFn type inp)) (Zmod.of_Z 2 1)) eq_refl).
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

(* ===========================================================================
 * 6. GENERIC 1-ELEMENT SPEC FIFO SIMULATION (`ActionSimulation`)
 *    Proves that `stagedIterTree` and `stagedPipeTree` directly simulate a
 *    1-element FIFO of `specFn` (`specFifoTree dom OutK := fifoTree dom 1 OutK`).
 * =========================================================================== *)

Lemma evalActionPropGen_sound_exists :
  forall {t k} (a : @Action type t k) old (P : TreeState DomainElemState t -> type k -> Prop),
    evalActionPropGen a old P ->
    exists new ret, SemAction a old new ret /\ P new ret.
Proof.
  intros t k a.
  induction a; intros old P Hprop;
    cbn -[castStateReg castStateRegInv castStateMem castStateMemInv
          castStateSend castStateSendInv castStateRecv castStateRecvInv] in Hprop.
  - destruct (H _ _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (IHa _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (IHa _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (H _ _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (IHa _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (IHa _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct Hprop as [recvVal Hprop].
    destruct (H recvVal _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (H _ _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (IHa _ _ Hprop) as [midState [midRet [Hsem1 Hcont]]].
    destruct (H midRet midState P Hcont) as [new [ret [Hsem2 HP]]].
    exists new, ret; split; [eapply SemLetAction; [exact Hsem1 | exact Hsem2] | exact HP].
  - destruct Hprop as [v Hprop].
    destruct (H v _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (evalExpr p) eqn:Hp.
    + destruct (IHa1 _ _ Hprop) as [midState [midRet [Hsem1 Hcont]]].
      destruct (H midRet midState P Hcont) as [new [ret [Hsem2 HP]]].
      exists new, ret; split; [| exact HP].
      eapply SemIfElse with (midState := midState) (midRet := midRet);
        [intros _; exact Hsem1 | intros Hc; congruence | exact Hsem2].
    + destruct (IHa2 _ _ Hprop) as [midState [midRet [Hsem1 Hcont]]].
      destruct (H midRet midState P Hcont) as [new [ret [Hsem2 HP]]].
      exists new, ret; split; [| exact HP].
      eapply SemIfElse with (midState := midState) (midRet := midRet);
        [intros Hc; congruence | intros _; exact Hsem1 | exact Hsem2].
  - destruct (IHa _ P Hprop) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - exists old, (evalExpr e); split; [econstructor; reflexivity | exact Hprop].
Qed.

Lemma evalActionPropGen_sound :
  forall {t k} (a : @Action type t k) old new ret,
    evalActionPropGen a old (fun new' ret' => new' = new /\ ret' = ret) ->
    SemAction a old new ret.
Proof.
  intros t k a old new ret Hprop.
  destruct (evalActionPropGen_sound_exists a old _ Hprop) as [new' [ret' [Hsem [-> ->]]]].
  exact Hsem.
Qed.

Definition ActionSimulation {TreeImpl TreeSpec : Tree DomainElem} {RetK : Kind}
  (R : TreeState DomainElemState TreeImpl -> TreeState DomainElemState TreeSpec -> Prop)
  (act_impl : Action type TreeImpl RetK)
  (act_spec : Action type TreeSpec RetK) : Prop :=
  forall s_u s_spec s_u' ret,
    R s_u s_spec ->
    SemAction act_impl s_u s_u' ret ->
    exists s_spec',
      SemAction act_spec s_spec s_spec' ret /\
      R s_u' s_spec'.

Definition specFifoTree (dom : string) (OutK : Kind) : Tree DomainElem :=
  fifoTree dom 1 OutK.

Definition specFifoEnq (dom : string) {InpK OutK : Kind}
  (specFn : forall ty, ty InpK -> LetExpr ty OutK)
  (ty : Kind -> Type) (inp : ty InpK) :
  Action ty (specFifoTree dom OutK) (Bit 0) :=
  LetL outVal : OutK <- specFn ty inp ;
  @enq dom 1 OutK ty outVal.

Definition specFifoFirst (dom : string) (OutK : Kind) (ty : Kind -> Type) :
  Action ty (specFifoTree dom OutK) (Option OutK) :=
  @first dom 1 OutK ty.

Definition specFifoDeq (dom : string) (OutK : Kind) (ty : Kind -> Type) :
  Action ty (specFifoTree dom OutK) (Bit 0) :=
  @deq dom 1 OutK ty.

Lemma bits1_sub_1_zero : forall (sz : bits 1),
  negb (Zmod.eqb sz (Zmod.of_Z 2 0)) = true ->
  evalExpr (Sub (Const type (Bit 1) sz) $1) = Zmod.of_Z 2 0.
Proof.
  intros sz Hne.
  pose proof (bits.unsigned_range sz ltac:(lia)) as Hrange.
  assert (Hu : Zmod.unsigned sz = 1).
  { destruct (Zmod.eqb_spec sz (Zmod.of_Z 2 0)) as [Heq | Hneq]; [discriminate Hne |].
    destruct (Z.eq_dec (Zmod.unsigned sz) 0) as [Hz | Hnz]; [| lia].
    exfalso; apply Hneq; rewrite <- (Zmod.of_Z_unsigned sz), Hz; reflexivity. }
  assert (Hsz : sz = Zmod.of_Z 2 1) by (rewrite <- (Zmod.of_Z_unsigned sz), Hu; reflexivity).
  subst sz; reflexivity.
Qed.

Section GenericIterSpecFifoSimulation.
  Variable dom : string.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Local Notation stepsSz := (iterStepsSz num_stages).
  Variable numStepsFn : forall ty, ty InpK -> Expr ty (Bit stepsSz).
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.
  Variable specFn     : forall ty, ty InpK -> LetExpr ty OutK.

  Hypothesis H_or_OutK : forall x : type OutK, evalOrBinary (getDefault OutK) x = x.

  Local Notation ITree := (stagedIterTree dom StateK num_stages).
  Local Notation STree := (specFifoTree dom OutK).

  Definition IterSpecFifoRel
    (s : TreeState DomainElemState ITree)
    (s_spec : TreeState DomainElemState STree) : Prop :=
    let isReady := andb (s @% "busy") (Zmod.eqb (s @% "stepsRem") 0%Zmod) in
    fifo1_size s_spec = (if isReady then Zmod.of_Z 2 1 else Zmod.of_Z 2 0) /\
    (isReady = true ->
     fifo1_elem s_spec = evalLetExpr (finishFn type (s @% "state")) /\
     exists inp : type InpK,
       evalLetExpr (finishFn type (s @% "state")) = evalLetExpr (specFn type inp)).

  Theorem IterSpecFifoRel_Init :
    IterSpecFifoRel (InitState ITree) (InitState STree).
  Proof.
    unfold IterSpecFifoRel; split; [reflexivity | intros H; discriminate H].
  Qed.

  Theorem IterSpecFifo_First_ActionSimulation :
    ActionSimulation IterSpecFifoRel
      (stagedIterFirst dom StateK OutK num_stages finishFn type)
      (specFifoFirst dom OutK type).
  Proof.
    unfold ActionSimulation; intros [busy [stepsRem [st []]]] s_spec s_u' ret [Hsz Hready] Hsem.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hsz, Hready.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedIterFirst, stagedWorkRegPath, stagedIterTree in Hinv.
    revert Hinv; cbn -[toAction mkSome mkNone stepsSz].
    change (Zmod.eqb stepsRem (Zmod.of_Z (2 ^ stepsSz) 0)) with (Zmod.eqb stepsRem 0%Zmod).
    rewrite evalActionPropGen_toAction; cbn -[mkSome mkNone stepsSz].
    intros [<- <-].
    exists s_spec; split.
    - apply evalActionPropGen_sound.
      unfold specFifoFirst, specFifoTree in s_spec |- *;
        rewrite (evalActionPropGen_fifo_first H_or_OutK s_spec).
      split; [reflexivity |].
      destruct (andb busy (Zmod.eqb stepsRem 0%Zmod)) eqn:Hr.
      + destruct (Hready eq_refl) as [Helem _].
        rewrite Hsz, Helem; reflexivity.
      + rewrite Hsz; reflexivity.
    - split; [exact Hsz | exact Hready].
  Qed.

  Theorem IterSpecFifo_Deq_ActionSimulation :
    ActionSimulation IterSpecFifoRel
      (stagedIterDeq dom StateK num_stages type)
      (specFifoDeq dom OutK type).
  Proof.
    unfold ActionSimulation; intros [busy [stepsRem [st []]]] s_spec s_u' ret [Hsz Hready] Hsem.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hsz, Hready.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedIterDeq, stagedWorkRegPath, stagedIterTree in Hinv.
    revert Hinv; cbn -[stepsSz].
    change (Zmod.eqb stepsRem (Zmod.of_Z (2 ^ stepsSz) 0)) with (Zmod.eqb stepsRem 0%Zmod).
    destruct (andb busy (Zmod.eqb stepsRem 0%Zmod)) eqn:Hr.
    - cbn -[stepsSz]; intros [<- <-].
      exists (@mkFifo1 dom OutK (fifo1_elem s_spec) (Zmod.of_Z 2 0)); split.
      + apply evalActionPropGen_sound; unfold specFifoDeq, specFifoTree in s_spec |- *;
          rewrite evalActionPropGen_fifo_deq.
        rewrite Hsz; split; reflexivity.
      + unfold IterSpecFifoRel; split; [reflexivity | intros H; discriminate H].
    - cbn -[stepsSz]; intros [<- <-].
      exists s_spec; split.
      + apply evalActionPropGen_sound; unfold specFifoDeq, specFifoTree in s_spec |- *;
          rewrite evalActionPropGen_fifo_deq.
        rewrite Hsz; split; reflexivity.
      + unfold IterSpecFifoRel; cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum].
        rewrite Hr; split; [exact Hsz | exact Hready].
  Qed.

  Theorem IterSpecFifo_Enq_Stutter :
    forall (inp : type InpK)
           (s_u : TreeState DomainElemState ITree)
           (s_spec : TreeState DomainElemState STree)
           (s_u' : TreeState DomainElemState ITree) ret,
      s_u @% "busy" = false ->
      (0 < IterTargetSteps InpK num_stages numStepsFn inp)%nat ->
      IterSpecFifoRel s_u s_spec ->
      SemAction (stagedIterEnq dom InpK StateK num_stages numStepsFn initFn type inp) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        IterSpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom InpK StateK num_stages numStepsFn initFn stepFn inp 0%nat s_u'.
  Proof.
    intros inp s_u s_spec s_u' ret Hidle Hpos [Hsz _] Hsem.
    rewrite Hidle in Hsz; cbn [andb] in Hsz.
    pose proof (Iter_Enq_Step0 dom InpK StateK num_stages numStepsFn initFn stepFn inp s_u s_u' ret Hidle Hsem)
      as Hstep0.
    pose proof (InversionActionPropGen Hsem) as Hinv.
    unfold stagedIterEnq, stagedWorkRegPath, stagedIterTree in Hinv.
    destruct s_u as [busy [stepsRem [st []]]];
      cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hidle;
      subst busy.
    revert Hinv; cbn -[toAction stepsSz]; rewrite evalActionPropGen_toAction; cbn -[stepsSz]; intros [_ <-].
    exists s_spec; split; [econstructor; reflexivity |].
    split; [| exact Hstep0].
    destruct Hstep0 as [Hbusy' [_ [Hrem' _]]].
    assert (Hz : Zmod.eqb (s_u' @% "stepsRem") 0%Zmod = false).
    { destruct (Zmod.eqb_spec (s_u' @% "stepsRem") 0%Zmod) as [Heq | _]; [| reflexivity].
      rewrite Heq, Zmod.unsigned_0 in Hrem'; lia. }
    unfold IterSpecFifoRel; rewrite Hbusy', Hz; cbn [andb].
    split; [exact Hsz | intros H; discriminate H].
  Qed.

  Theorem IterSpecFifo_Step_Stutter :
    forall (inp : type InpK) (m : nat)
           (s_u : TreeState DomainElemState ITree)
           (s_spec : TreeState DomainElemState STree)
           (s_u' : TreeState DomainElemState ITree) ret,
      IterStateAtStep dom InpK StateK num_stages numStepsFn initFn stepFn inp m s_u ->
      (S m < IterTargetSteps InpK num_stages numStepsFn inp)%nat ->
      IterSpecFifoRel s_u s_spec ->
      SemAction (stagedIterStep dom StateK num_stages stepFn type) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        IterSpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom InpK StateK num_stages numStepsFn initFn stepFn inp (S m) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hst Hlt [Hsz _] Hsem.
    assert (Hlt0 : (m < IterTargetSteps InpK num_stages numStepsFn inp)%nat) by lia.
    pose proof (Iter_Step_Inductive dom InpK StateK num_stages numStepsFn initFn stepFn inp m s_u s_u' ret Hst Hlt0 Hsem)
      as Hst'.
    destruct Hst as [Hbusy [_ [Hrem _]]].
    assert (Hz0 : Zmod.eqb (s_u @% "stepsRem") 0%Zmod = false).
    { destruct (Zmod.eqb_spec (s_u @% "stepsRem") 0%Zmod) as [Heq | _]; [| reflexivity].
      rewrite Heq, Zmod.unsigned_0 in Hrem; lia. }
    rewrite Hbusy, Hz0 in Hsz; cbn [andb] in Hsz.
    assert (Hret : ret = Zmod.zero)
      by (pose proof (bits.unsigned_range ret ltac:(lia)); apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia).
    subst ret.
    exists s_spec; split; [econstructor; reflexivity |].
    split; [| exact Hst'].
    destruct Hst' as [Hbusy' [_ [Hrem' _]]].
    assert (Hz' : Zmod.eqb (s_u' @% "stepsRem") 0%Zmod = false).
    { destruct (Zmod.eqb_spec (s_u' @% "stepsRem") 0%Zmod) as [Heq | _]; [| reflexivity].
      rewrite Heq, Zmod.unsigned_0 in Hrem'; lia. }
    unfold IterSpecFifoRel; rewrite Hbusy', Hz'; cbn [andb].
    split; [exact Hsz | intros H; discriminate H].
  Qed.

  Theorem IterSpecFifo_Step_Finish_ActionSimulation :
    forall (inp : type InpK) (m : nat)
           (s_u : TreeState DomainElemState ITree)
           (s_spec : TreeState DomainElemState STree)
           (s_u' : TreeState DomainElemState ITree) ret,
      evalLetExpr (finishFn type (StageValAt initFn stepFn (IterTargetSteps InpK num_stages numStepsFn inp) inp)) =
        evalLetExpr (specFn type inp) ->
      IterStateAtStep dom InpK StateK num_stages numStepsFn initFn stepFn inp m s_u ->
      S m = IterTargetSteps InpK num_stages numStepsFn inp ->
      IterSpecFifoRel s_u s_spec ->
      SemAction (stagedIterStep dom StateK num_stages stepFn type) s_u s_u' ret ->
      exists s_spec',
        SemAction (specFifoEnq dom specFn type inp) s_spec s_spec' ret /\
        IterSpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom InpK StateK num_stages numStepsFn initFn stepFn inp
          (IterTargetSteps InpK num_stages numStepsFn inp) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hspec Hst HSm [Hsz _] Hsem.
    assert (Hlt0 : (m < IterTargetSteps InpK num_stages numStepsFn inp)%nat) by lia.
    pose proof (Iter_Step_Inductive dom InpK StateK num_stages numStepsFn initFn stepFn inp m s_u s_u' ret Hst Hlt0 Hsem)
      as Hst'.
    rewrite HSm in Hst'.
    destruct Hst as [Hbusy [_ [Hrem _]]].
    assert (Hz0 : Zmod.eqb (s_u @% "stepsRem") 0%Zmod = false).
    { destruct (Zmod.eqb_spec (s_u @% "stepsRem") 0%Zmod) as [Heq | _]; [| reflexivity].
      rewrite Heq, Zmod.unsigned_0 in Hrem; lia. }
    rewrite Hbusy, Hz0 in Hsz; cbn [andb] in Hsz.
    assert (Hret : ret = Zmod.zero)
      by (pose proof (bits.unsigned_range ret ltac:(lia)); apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia).
    subst ret.
    exists (@mkFifo1 dom OutK (evalLetExpr (specFn type inp)) (Zmod.of_Z 2 1)).
    split.
    - apply evalActionPropGen_sound.
      unfold specFifoEnq, specFifoTree in s_spec |- *; cbn [evalActionPropGen]; rewrite evalActionPropGen_toAction.
      rewrite evalActionPropGen_fifo_enq, Hsz; split; reflexivity.
    - split; [| exact Hst'].
      destruct Hst' as [Hbusy' [_ [Hrem' Hval']]].
      assert (Hz' : Zmod.eqb (s_u' @% "stepsRem") 0%Zmod = true).
      { destruct (Zmod.eqb_spec (s_u' @% "stepsRem") 0%Zmod) as [_ | Hnz]; [reflexivity |].
        exfalso; apply Hnz, Zmod.unsigned_inj.
        pose proof (bits.unsigned_range (s_u' @% "stepsRem") ltac:(pose proof (iterStepsSz_pos num_stages); lia)).
        rewrite Zmod.unsigned_0; lia. }
      unfold IterSpecFifoRel; rewrite Hbusy', Hz'; cbn [andb fifo1_size fifo1_elem].
      split; [reflexivity | intros _].
      rewrite Hval', Hspec; split; [reflexivity | exists inp; reflexivity].
  Qed.

End GenericIterSpecFifoSimulation.

Section GenericPipeSpecFifoSimulation.
  Variable dom : string.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.
  Variable specFn     : forall ty, ty InpK -> LetExpr ty OutK.

  Hypothesis H_or_StateK : forall x : type StateK, evalOrBinary (getDefault StateK) x = x.
  Hypothesis H_sz_StateK : (0 <= kindSize StateK)%Z.
  Hypothesis H_fb_StateK : forall x : type StateK, @evalFromBit StateK (evalToBit x) = x.
  Hypothesis H_or_OutK   : forall x : type OutK, evalOrBinary (getDefault OutK) x = x.

  Local Notation PTree := (stagedPipeTree dom StateK num_stages).
  Local Notation STree := (specFifoTree dom OutK).

  Definition PipeSpecFifoRel
    (s : TreeState DomainElemState PTree)
    (s_spec : TreeState DomainElemState STree) : Prop :=
    let f_last := stagedLastFifo dom StateK num_stages s in
    let isReady := negb (Zmod.eqb (fifo1_size f_last) (Zmod.of_Z 2 0)) in
    fifo1_size s_spec = fifo1_size f_last /\
    (isReady = true ->
     fifo1_elem s_spec = evalLetExpr (finishFn type (fifo1_elem f_last)) /\
     exists inp : type InpK,
       evalLetExpr (finishFn type (fifo1_elem f_last)) = evalLetExpr (specFn type inp)).

  Theorem PipeSpecFifoRel_Init :
    PipeSpecFifoRel (InitState PTree) (InitState STree).
  Proof.
    unfold PipeSpecFifoRel.
    assert (Hlast0 : forall n, fifo1_size (stagedLastFifo dom StateK n (InitState (stagedStagesTree dom StateK n))) = Zmod.of_Z 2 0).
    { induction n as [| m IHm]; [reflexivity | exact IHm]. }
    rewrite Hlast0; split; [reflexivity | intros H; discriminate H].
  Qed.

  Theorem PipeSpecFifo_First_ActionSimulation :
    ActionSimulation PipeSpecFifoRel
      (stagedPipeFirst dom StateK OutK num_stages finishFn type)
      (specFifoFirst dom OutK type).
  Proof.
    unfold ActionSimulation; intros s_u s_spec s_u' ret [Hsz Hready] Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeFirst, stagedPipeTree in s_u, s_u', Hinv.
    revert Hinv; cbn [evalActionPropGen].
    rewrite (evalActionPropGen_stagedLiftLastStage dom StateK num_stages),
            (evalActionPropGen_fifo_first H_or_StateK (stagedLastFifo dom StateK num_stages s_u)).
    cbn [evalActionPropGen].
    assert (Hupd_id : forall (n : nat) (st : TreeState DomainElemState (stagedStagesTree dom StateK n)),
              stagedUpdateLastFifo dom StateK n st (stagedLastFifo dom StateK n st) = st).
    { clear; induction n as [| m IHm]; intros st;
        [destruct st as [f0 []]; reflexivity
        | destruct st as [f_head [st_tail []]];
          cbn [stagedUpdateLastFifo stagedLastFifo Fst Snd]; rewrite IHm; reflexivity]. }
    rewrite Hupd_id.
    destruct (Zmod.eqb (fifo1_size (stagedLastFifo dom StateK num_stages s_u)) (Zmod.of_Z 2 0)) eqn:Hemp;
      cbn [evalActionPropGen].
    - rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
      assert (Hite_none : forall (out : type OutK),
                evalExpr (ITE ((Var type (Option StateK) (evalExpr (mkNone type))) `? "Some")
                              (mkSome (Var type OutK out))
                              (mkNone type)) =
                evalExpr (mkNone type)).
      { intros out; reflexivity. }
      rewrite Hite_none; intros [<- <-].
      exists s_spec; split.
      + apply evalActionPropGen_sound; unfold specFifoFirst, specFifoTree in s_spec |- *;
          rewrite (evalActionPropGen_fifo_first H_or_OutK s_spec), Hsz, Hemp; split; reflexivity.
      + unfold PipeSpecFifoRel; rewrite Hemp; split; [exact Hsz | intros H; discriminate H].
    - rewrite (evalExpr_mkSome_data dom StateK H_sz_StateK H_fb_StateK); cbn [evalActionPropGen].
      rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
      assert (Hite_some : forall (v : type StateK) (out : type OutK),
                evalExpr (ITE ((Var type (Option StateK) (evalExpr (mkSome (Const type StateK v)))) `? "Some")
                              (mkSome (Var type OutK out))
                              (mkNone type)) =
                evalExpr (mkSome (Const type OutK out))).
      { intros v out; reflexivity. }
      rewrite Hite_some; intros [<- <-].
      destruct (Hready eq_refl) as [Helem Hex].
      exists s_spec; split.
      + apply evalActionPropGen_sound; unfold specFifoFirst, specFifoTree in s_spec |- *;
          rewrite (evalActionPropGen_fifo_first H_or_OutK s_spec), Hsz, Hemp, Helem; split; reflexivity.
      + unfold PipeSpecFifoRel; rewrite Hemp; split; [exact Hsz | intros _; split; [exact Helem | exact Hex]].
  Qed.

  Theorem PipeSpecFifo_Deq_ActionSimulation :
    ActionSimulation PipeSpecFifoRel
      (stagedPipeDeq dom StateK num_stages type)
      (specFifoDeq dom OutK type).
  Proof.
    unfold ActionSimulation; intros s_u s_spec s_u' ret [Hsz Hready] Hsem.
    pose proof (InversionActionPropGen Hsem) as Hinv; clear Hsem.
    unfold stagedPipeDeq, stagedPipeTree in s_u, s_u', Hinv.
    revert Hinv.
    rewrite (evalActionPropGen_stagedLiftLastStage dom StateK num_stages),
            evalActionPropGen_fifo_deq.
    intros [<- <-].
    assert (Hlast_upd : forall (n : nat) (st : TreeState DomainElemState (stagedStagesTree dom StateK n)) f',
              stagedLastFifo dom StateK n (stagedUpdateLastFifo dom StateK n st f') = f').
    { clear; induction n as [| m IHm]; intros st f';
        [destruct st as [f0 []]; reflexivity
        | destruct st as [f_head [st_tail []]];
          cbn [stagedUpdateLastFifo stagedLastFifo Fst Snd]; apply IHm]. }
    destruct (negb (Zmod.eqb (fifo1_size (stagedLastFifo dom StateK num_stages s_u)) (Zmod.of_Z 2 0))) eqn:Hne.
    - exists (@mkFifo1 dom OutK (fifo1_elem s_spec) (Zmod.of_Z 2 0)); split.
      + apply evalActionPropGen_sound; unfold specFifoDeq, specFifoTree in s_spec |- *;
          rewrite evalActionPropGen_fifo_deq.
        rewrite Hsz, Hne, (bits1_sub_1_zero _ Hne); split; reflexivity.
      + unfold PipeSpecFifoRel; rewrite Hlast_upd; cbn [fifo1_size].
        rewrite (bits1_sub_1_zero _ Hne); split; [reflexivity | intros H; discriminate H].
    - exists s_spec; split.
      + apply evalActionPropGen_sound; unfold specFifoDeq, specFifoTree in s_spec |- *;
          rewrite evalActionPropGen_fifo_deq.
        rewrite Hsz, Hne; split; reflexivity.
      + unfold PipeSpecFifoRel; rewrite Hlast_upd; rewrite Hne.
        split; [exact Hsz | intros H; discriminate H].
  Qed.

  Theorem PipeSpecFifo_Internal_Stutter :
    forall (act : Action type PTree (Bit 0))
           (s_u : TreeState DomainElemState PTree)
           (s_spec : TreeState DomainElemState STree)
           (s_u' : TreeState DomainElemState PTree) ret,
      stagedLastFifo dom StateK num_stages s_u' =
        stagedLastFifo dom StateK num_stages s_u ->
      PipeSpecFifoRel s_u s_spec ->
      SemAction act s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        PipeSpecFifoRel s_u' s_spec'.
  Proof.
    intros act s_u s_spec s_u' ret Hlast Hrel Hsem.
    assert (Hret : ret = Zmod.zero)
      by (pose proof (bits.unsigned_range ret ltac:(lia)); apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia).
    subst ret.
    exists s_spec; split; [econstructor; reflexivity |].
    unfold PipeSpecFifoRel in *; rewrite Hlast; exact Hrel.
  Qed.

  Theorem PipeSpecFifo_StepToLast_ActionSimulation :
    forall (inp : type InpK) (act : Action type PTree (Bit 0))
           (s_u : TreeState DomainElemState PTree)
           (s_spec : TreeState DomainElemState STree)
           (s_u' : TreeState DomainElemState PTree) ret,
      evalLetExpr (finishFn type (StageValAt initFn stepFn num_stages inp)) =
        evalLetExpr (specFn type inp) ->
      fifo1_size (stagedLastFifo dom StateK num_stages s_u) = Zmod.of_Z 2 0 ->
      stagedLastFifo dom StateK num_stages s_u' =
        @mkFifo1 dom StateK (StageValAt initFn stepFn num_stages inp) (Zmod.of_Z 2 1) ->
      PipeSpecFifoRel s_u s_spec ->
      SemAction act s_u s_u' ret ->
      exists s_spec',
        SemAction (specFifoEnq dom specFn type inp) s_spec s_spec' ret /\
        PipeSpecFifoRel s_u' s_spec'.
  Proof.
    intros inp act s_u s_spec s_u' ret Hspec Hemp Hlast' [Hsz _] Hsem.
    rewrite Hemp in Hsz.
    assert (Hret : ret = Zmod.zero)
      by (pose proof (bits.unsigned_range ret ltac:(lia)); apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia).
    subst ret.
    exists (@mkFifo1 dom OutK (evalLetExpr (specFn type inp)) (Zmod.of_Z 2 1)).
    split.
    - apply evalActionPropGen_sound.
      unfold specFifoEnq, specFifoTree in s_spec |- *; cbn [evalActionPropGen]; rewrite evalActionPropGen_toAction.
      rewrite evalActionPropGen_fifo_enq, Hsz; split; reflexivity.
    - unfold PipeSpecFifoRel; rewrite Hlast'; unfold mkFifo1, fifo1_size, fifo1_elem; cbn [Fst Snd].
      split; [reflexivity | intros _].
      rewrite Hspec; split; [reflexivity | exists inp; reflexivity].
  Qed.

End GenericPipeSpecFifoSimulation.
