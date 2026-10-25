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
From Cheriot Require Export Fifo.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

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

Definition fifo1_empty_first {dom : string} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) : type (Option elemK) :=
  evalExpr (mkNone type).

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

Lemma evalActionPropGen_fifo_isFull : forall {dom elemK} {env : Env (fifoTree dom 1 elemK)}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen env (@isFull dom 1 elemK type) f P <->
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

Lemma evalActionPropGen_fifo_deq : forall {dom elemK} {env : Env (fifoTree dom 1 elemK)}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen env (@deq dom 1 elemK type) f P <->
  P (if negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0))
     then mkFifo1 (fifo1_elem f) (evalExpr (Sub (Const type (Bit 1) (fifo1_size f)) $1))
     else f) Zmod.zero.
Proof.
  intros dom elemK env [[e []] [sz [d []]]] P.
  unfold deq, fifo1_elem, fifo1_size, mkFifo1; simpl.
  destruct_ifs; simpl;
    [apply iff_f_equal2; [repeat f_equal; apply Zmod_1_0 | reflexivity] | reflexivity].
Qed.

Lemma evalActionPropGen_fifo_enq : forall {dom elemK} {env : Env (fifoTree dom 1 elemK)} (val : type elemK)
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen env (@enq dom 1 elemK type val) f P <->
  P (if negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 1))
     then mkFifo1 val (evalExpr (Add [Const type (Bit 1) (fifo1_size f); $1]))
     else f) Zmod.zero.
Proof.
  intros dom elemK env val [[e []] [sz [d []]]] P.
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

Lemma evalActionPropGen_fifo_first : forall {dom elemK} {env : Env (fifoTree dom 1 elemK)}
  (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
  evalActionPropGen env (@first dom 1 elemK type) f P <->
  P f (if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)
       then fifo1_empty_first f
       else evalExpr (mkSome (Const type elemK (fifo1_elem f)))).
Proof.
  intros dom elemK env [[e []] [sz [d []]]] P.
  unfold first, readRegsList, fifo1_elem, fifo1_size, fifo1_empty_first.
  destruct (elemPathsWithKind_1 dom elemK) as [[rk_p rk_pf] [Hpaths Hreg]].
  rewrite Hpaths.
  destruct rk_p as [rp rp_pf]; simpl in Hreg; subst rp.
  cbn -[evalOrBinary getDefault].
  rewrite (Zmod_1_0 d).
  change (Zmod.eqb Zmod.zero (Zmod.of_Z 1 0)) with true.
  apply iff_f_equal2; [reflexivity |].
  rewrite eq_rect_Kind_refl; cbn [evalExpr fold_left map ITE0];
    rewrite evalOrBinary_getDefault_l; reflexivity.
Qed.
