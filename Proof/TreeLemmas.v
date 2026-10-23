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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Export SpecDefines ShiftFifo ShiftFifoLemmas ImplStaged ImplCommon.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. ACTION SEMANTICS (`SemAction`) <-> `evalActionPropGen`
 * =========================================================================== *)

Lemma evalActionPropGen_ext :
  forall {t : Tree DomainElem} {k : Kind} (a : @Action type t k)
         (old : TreeState DomainElemState t)
         (P1 P2 : TreeState DomainElemState t -> type k -> Prop),
    (forall s r, P1 s r <-> P2 s r) ->
    (evalActionPropGen a old P1 <-> evalActionPropGen a old P2).
Proof.
  intros t k a old P1 P2 Hiff.
  split; apply evalActionPropGen_mono; intros s r H; apply Hiff; exact H.
Qed.

Lemma evalActionPropGen_to_SemAction :
  forall {t : Tree DomainElem} {k : Kind} (a : @Action type t k)
         (old : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    evalActionPropGen a old P ->
    exists new ret, SemAction a old new ret /\ P new ret.
Proof.
  intros t k a.
  induction a; intros old P Heval; cbn [evalActionPropGen] in Heval.
  - destruct (H _ old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (H _ old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct Heval as [recvVal Heval].
    destruct (H recvVal _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (H (evalExpr e) old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa old _ Heval) as [midState [midRet [Hsem1 Heval2]]].
    destruct (H midRet midState P Heval2) as [new [ret [Hsem2 HP]]].
    exists new, ret; split; [econstructor; [exact Hsem1 | exact Hsem2] | exact HP].
  - destruct Heval as [v Heval].
    destruct (H v old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (evalExpr p) eqn:Hp.
    + destruct (IHa1 old _ Heval) as [midState [midRet [Hsem1 Heval2]]].
      destruct (H midRet midState P Heval2) as [new [ret [Hsem2 HP]]].
      exists new, ret; split; [| exact HP].
      eapply SemIfElse with (midState := midState) (midRet := midRet);
        [intros _; exact Hsem1 | intros Hfalse; congruence | exact Hsem2].
    + destruct (IHa2 old _ Heval) as [midState [midRet [Hsem1 Heval2]]].
      destruct (H midRet midState P Heval2) as [new [ret [Hsem2 HP]]].
      exists new, ret; split; [| exact HP].
      eapply SemIfElse with (midState := midState) (midRet := midRet);
        [intros Htrue; congruence | intros _; exact Hsem1 | exact Hsem2].
  - destruct (IHa old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - exists old, (evalExpr e); split; [constructor; reflexivity | exact Heval].
Qed.

Theorem SemAction_iff_evalActionPropGen :
  forall {t : Tree DomainElem} {k : Kind} (a : @Action type t k)
         (old new : TreeState DomainElemState t) (ret : type k),
    SemAction a old new ret <->
    evalActionPropGen a old (fun new' ret' => new' = new /\ ret' = ret).
Proof.
  intros t k a old new ret; split.
  - apply InversionActionPropGen.
  - intros Heval.
    destruct (evalActionPropGen_to_SemAction a old _ Heval) as [new' [ret' [Hsem [Hnew Hret]]]].
    subst; exact Hsem.
Qed.

(* ===========================================================================
 * 2. SUBTREE STATE READ / WRITE AND GENERAL `liftAction` LEMMAS
 * =========================================================================== *)

Fixpoint readSubTreeState_child {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p_child : NodeChildren t), TreeState f t -> TreeState f (getNodeChildren p_child) :=
  match t return forall (p_child : NodeChildren t), TreeState f t -> TreeState f (getNodeChildren p_child) with
  | Leaf _ _ => fun empty => match empty with end
  | Node _ children =>
      (fix loop (ls : list (Tree A)) :
         forall (p_list : NodePathList ls),
           TreeState f (Node "" ls) ->
           TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                           match l return NodePathList l -> Tree A with
                           | nil => fun empty => match empty with end
                           | x :: xs => fun p_sum =>
                               match p_sum with
                               | inl p_x =>
                                   match p_x with
                                   | inl _ => x
                                   | inr p_child => getNodeChildren p_child
                                   end
                               | inr p_xs => loop_node xs p_xs
                               end
                           end) ls p_list) :=
         match ls return
           forall (p_list : NodePathList ls),
             TreeState f (Node "" ls) ->
             TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                             match l return NodePathList l -> Tree A with
                             | nil => fun empty => match empty with end
                             | x :: xs => fun p_sum =>
                                 match p_sum with
                                 | inl p_x =>
                                     match p_x with
                                     | inl _ => x
                                     | inr p_child => getNodeChildren p_child
                                     end
                                 | inr p_xs => loop_node xs p_xs
                                 end
                             end) ls p_list)
         with
         | nil => fun empty => match empty with end
         | x :: xs => fun p_list s =>
             match p_list with
             | inl p_x =>
                 match p_x with
                 | inl _ => s.(Fst)
                 | inr p_child => @readSubTreeState_child A f x p_child s.(Fst)
                 end
             | inr p_xs => loop xs p_xs s.(Snd)
             end
         end) children
  end.

Definition readSubTreeState {A : Type} {f : A -> Type} {t : Tree A}
  (p : NodePath t) (s : TreeState f t) : TreeState f (getNode p) :=
  match p as p_ return TreeState f (getNode p_) with
  | inl _ => s
  | inr p_child => readSubTreeState_child p_child s
  end.

Fixpoint writeSubTreeState_child {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p_child : NodeChildren t),
    TreeState f t -> TreeState f (getNodeChildren p_child) -> TreeState f t :=
  match t return
    forall (p_child : NodeChildren t),
      TreeState f t -> TreeState f (getNodeChildren p_child) -> TreeState f t
  with
  | Leaf _ _ => fun empty => match empty with end
  | Node _ children =>
      (fix loop (ls : list (Tree A)) :
         forall (p_list : NodePathList ls),
           TreeState f (Node "" ls) ->
           TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                           match l return NodePathList l -> Tree A with
                           | nil => fun empty => match empty with end
                           | x :: xs => fun p_sum =>
                               match p_sum with
                               | inl p_x =>
                                   match p_x with
                                   | inl _ => x
                                   | inr p_child => getNodeChildren p_child
                                   end
                               | inr p_xs => loop_node xs p_xs
                               end
                           end) ls p_list) ->
           TreeState f (Node "" ls) :=
         match ls return
           forall (p_list : NodePathList ls),
             TreeState f (Node "" ls) ->
             TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                             match l return NodePathList l -> Tree A with
                             | nil => fun empty => match empty with end
                             | x :: xs => fun p_sum =>
                                 match p_sum with
                                 | inl p_x =>
                                     match p_x with
                                     | inl _ => x
                                     | inr p_child => getNodeChildren p_child
                                     end
                                 | inr p_xs => loop_node xs p_xs
                                 end
                             end) ls p_list) ->
             TreeState f (Node "" ls)
         with
         | nil => fun empty => match empty with end
         | x :: xs => fun p_list s v =>
             match p_list as p_list_ return
               TreeState f (match p_list_ with
                            | inl p_x =>
                                match p_x with
                                | inl _ => x
                                | inr p_child => getNodeChildren p_child
                                end
                            | inr p_xs => _
                            end) ->
               TreeState f (Node "" (x :: xs))
             with
             | inl p_x =>
                 match p_x as p_x_ return
                   TreeState f (match p_x_ with
                                | inl _ => x
                                | inr p_child => getNodeChildren p_child
                                end) ->
                   TreeState f (Node "" (x :: xs))
                 with
                 | inl _ => fun v_x => (v_x ,, s.(Snd))
                 | inr p_child => fun v_child => (@writeSubTreeState_child A f x p_child s.(Fst) v_child ,, s.(Snd))
                 end
             | inr p_xs => fun v_xs => (s.(Fst) ,, loop xs p_xs s.(Snd) v_xs)
             end v
         end) children
  end.

Definition writeSubTreeState {A : Type} {f : A -> Type} {t : Tree A}
  (p : NodePath t) (s : TreeState f t) (v : TreeState f (getNode p)) : TreeState f t :=
  match p as p_ return TreeState f (getNode p_) -> TreeState f t with
  | inl _ => fun v_root => v_root
  | inr p_child => fun v_child => writeSubTreeState_child p_child s v_child
  end v.

Fixpoint readSubTreeState_writeSubTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (v : TreeState f (getNode p)),
    readSubTreeState p (writeSubTreeState p s v) = v.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s v.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ exact (@readSubTreeState_writeSubTreeState_same A f c (inr p_c_child) s.(Fst) v).
        -- exact (IHcs p_cs s.(Snd) v).
Qed.

Fixpoint writeSubTreeState_writeSubTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (v1 v2 : TreeState f (getNode p)),
    writeSubTreeState p (writeSubTreeState p s v1) v2 = writeSubTreeState p s v2.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s v1 v2.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ f_equal.
              exact (@writeSubTreeState_writeSubTreeState_same A f c (inr p_c_child) s.(Fst) v1 v2).
        -- f_equal.
           exact (IHcs p_cs s.(Snd) v1 v2).
Qed.

Fixpoint writeSubTreeState_readSubTreeState {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t),
    writeSubTreeState p s (readSubTreeState p s) = s.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ exact (f_equal2 (@Build_Prod _ _) (@writeSubTreeState_readSubTreeState A f c (inr p_c_child) s.(Fst)) eq_refl).
        -- exact (f_equal2 (@Build_Prod _ _) eq_refl (IHcs p_cs s.(Snd))).
Qed.

Fixpoint getLeaf_embedLeafIntoPath_def {A : Type} {t : Tree A} :
  forall (p : NodePath t) (l : LeafPath (getNode p)),
    getLeaf (@embedLeafIntoPath _ t p l) = getLeaf l.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children l.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ change (embedLeafIntoPath_child (p_child:=p_c_child) l) with (embedLeafIntoPath (inr p_c_child) l).
              exact (@getLeaf_embedLeafIntoPath_def A c (inr p_c_child) l).
        -- exact (IHcs p_cs l).
Defined.

Fixpoint readTreeState_embedLeafIntoPath {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (l : LeafPath (getNode p)),
    readTreeState t s (@embedLeafIntoPath _ t p l) =
    eq_rect_r f (readTreeState (getNode p) (readSubTreeState p s) l) (getLeaf_embedLeafIntoPath_def p l).
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s l.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ change (embedLeafIntoPath_child (p_child:=p_c_child) l) with (embedLeafIntoPath (inr p_c_child) l).
              exact (@readTreeState_embedLeafIntoPath A f c (inr p_c_child) s.(Fst) l).
        -- exact (IHcs p_cs s.(Snd) l).
Qed.

Fixpoint writeTreeState_embedLeafIntoPath {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (l : LeafPath (getNode p))
         (v : f (getLeaf (@embedLeafIntoPath _ t p l))),
    writeTreeState t s (@embedLeafIntoPath _ t p l) v =
    writeSubTreeState p s
      (writeTreeState (getNode p) (readSubTreeState p s) l
         (eq_rect (getLeaf (@embedLeafIntoPath _ t p l)) f v (getLeaf l) (getLeaf_embedLeafIntoPath_def p l))).
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s l v.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ change (embedLeafIntoPath_child (p_child:=p_c_child) l) with (embedLeafIntoPath (inr p_c_child) l) in *.
              exact (f_equal2 (@Build_Prod _ _) (@writeTreeState_embedLeafIntoPath A f c (inr p_c_child) s.(Fst) l v) eq_refl).
        -- exact (f_equal2 (@Build_Prod _ _) eq_refl (IHcs p_cs s.(Snd) l v)).
Qed.

Lemma evalExpr_eq_rect_Kind :
  forall (k1 k2 : Kind) (pf : k1 = k2) (e : Expr type k1),
    evalExpr (eq_rect k1 (Expr type) e k2 pf) =
    eq_rect k1 type (evalExpr e) k2 pf.
Proof.
  intros k1 k2 pf e; destruct pf; reflexivity.
Qed.

Lemma evalExpr_eq_rect_nat_Bit :
  forall (n1 n2 : nat) (pf : n1 = n2) (e : Expr type (Bit (Z.log2_up (Z.of_nat n1)))),
    evalExpr (eq_rect n1 (fun s => Expr type (Bit (Z.log2_up (Z.of_nat s)))) e n2 pf) =
    eq_rect n1 (fun s => type (Bit (Z.log2_up (Z.of_nat s)))) (evalExpr e) n2 pf.
Proof.
  intros n1 n2 pf e; destruct pf; reflexivity.
Qed.

Lemma Zmod_to_Z_eq_rect_nat :
  forall (n1 n2 : nat) (pf : n1 = n2) (v : type (Bit (Z.log2_up (Z.of_nat n1)))),
    Zmod.to_Z (eq_rect n1 (fun s => type (Bit (Z.log2_up (Z.of_nat s)))) v n2 pf) =
    Zmod.to_Z v.
Proof.
  intros n1 n2 pf v; destruct pf; reflexivity.
Qed.

Lemma cast_reg_read_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RegPath (getNode p))
         (s : TreeState DomainElemState t),
    cast_reg p x (castStateReg (embedRegPath p x) (readTreeState t s (embedRegPath p x).(regPath))) =
    castStateReg x (readTreeState (getNode p) (readSubTreeState p s) x.(regPath)).
Proof.
  intros t p x s.
  unfold cast_reg, castStateReg, getRegFromPathTypeEq.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  rewrite readTreeState_embedLeafIntoPath.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(regPath)).
  generalize (regKind_embed p x).
  generalize (embedRegPath p x).(regPathPf).
  generalize x.(regPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(regPath)).
  unfold getRegFromPath, getRegFromPathUnsafe, getLeafElem.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk v; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getRegFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma write_reg_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RegPath (getNode p))
         (v : Expr type (regKind (getRegFromPath x)))
         (s : TreeState DomainElemState t),
    writeTreeState t s (embedRegPath p x).(regPath)
      (castStateRegInv (embedRegPath p x) (evalExpr (cast_reg_expr p x v))) =
    writeSubTreeState p s
      (writeTreeState (getNode p) (readSubTreeState p s) x.(regPath)
         (castStateRegInv x (evalExpr v))).
Proof.
  intros t p x v s.
  unfold cast_reg_expr.
  rewrite evalExpr_eq_rect_Kind.
  unfold castStateRegInv, getRegFromPathTypeEq.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  rewrite writeTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize (evalExpr v).
  generalize (regKind_embed p x).
  generalize (embedRegPath p x).(regPathPf).
  generalize x.(regPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(regPath)).
  unfold getRegFromPath, getRegFromPathUnsafe, getLeafElem.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk val; cbn [eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getRegFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma read_rq_mem_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : MemPath (getNode p))
         (i : Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x))))))
         (port : FinType (memPort (getMemFromPath x)))
         (s : TreeState DomainElemState t),
    (let arr := castStateMem (embedMemPath p x) (readTreeState t s (embedMemPath p x).(memPath)) in
     let val := nth (Z.to_nat (Zmod.to_Z (evalExpr (cast_mem_idx p x i)))) arr.(Fst).(tupleElems) (getDefault _) in
     writeTreeState t s (embedMemPath p x).(memPath)
       (castStateMemInv (embedMemPath p x) (arr.(Fst) ,, updSameTuple arr.(Snd) (cast_mem_port p x port) val))) =
    writeSubTreeState p s
      (let arr := castStateMem x (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)) in
       let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(memPath)
         (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) port val))).
Proof.
  intros t p x i port s.
  cbv zeta.
  unfold cast_mem_idx, cast_mem_port.
  rewrite evalExpr_eq_rect_nat_Bit, Zmod_to_Z_eq_rect_nat.
  set (idx := Z.to_nat (Zmod.to_Z (evalExpr i))); clearbody idx.
  unfold castStateMem, castStateMemInv, getMemFromPathTypeEq.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize port.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)).
  generalize (memPort_embed p x).
  generalize (embedMemPath p x).(memPathPf).
  generalize x.(memPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(memPath)).
  unfold getMemFromPath, getMemFromPathUnsafe, getLeafElem.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hport v port0; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_nat_refl.
  rewrite (getMemFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma cast_mem_read_rp_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : MemPath (getNode p))
         (port : FinType (memPort (getMemFromPath x)))
         (s : TreeState DomainElemState t),
    cast_mem p x
      (readSameTuple (castStateMem (embedMemPath p x) (readTreeState t s (embedMemPath p x).(memPath))).(Snd)
         (cast_mem_port p x port)) =
    readSameTuple (castStateMem x (readTreeState (getNode p) (readSubTreeState p s) x.(memPath))).(Snd) port.
Proof.
  intros t p x port s.
  unfold cast_mem, cast_mem_port, castStateMem, getMemFromPathTypeEq.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  rewrite readTreeState_embedLeafIntoPath.
  generalize port.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)).
  generalize (memKind_embed p x).
  generalize (memPort_embed p x).
  generalize (embedMemPath p x).(memPathPf).
  generalize x.(memPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(memPath)).
  unfold getMemFromPath, getMemFromPathUnsafe, getLeafElem.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hport Hk v port0; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl, eq_rect_nat_refl.
  rewrite (getMemFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma write_mem_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : MemPath (getNode p))
         (i : Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x))))))
         (v : Expr type (memKind (getMemFromPath x)))
         (s : TreeState DomainElemState t),
    (let arr := castStateMem (embedMemPath p x) (readTreeState t s (embedMemPath p x).(memPath)) in
     writeTreeState t s (embedMemPath p x).(memPath)
       (castStateMemInv (embedMemPath p x)
          (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr (cast_mem_idx p x i))))
             (evalExpr (cast_mem_expr p x v)) ,, arr.(Snd)))) =
    writeSubTreeState p s
      (let arr := castStateMem x (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(memPath)
         (castStateMemInv x
            (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd)))).
Proof.
  intros t p x i v s.
  cbv zeta.
  unfold cast_mem_idx, cast_mem_expr.
  rewrite evalExpr_eq_rect_nat_Bit, Zmod_to_Z_eq_rect_nat, evalExpr_eq_rect_Kind.
  set (idx := Z.to_nat (Zmod.to_Z (evalExpr i))); clearbody idx.
  unfold castStateMem, castStateMemInv, getMemFromPathTypeEq.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize (evalExpr v).
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)).
  generalize (memKind_embed p x).
  generalize (embedMemPath p x).(memPathPf).
  generalize x.(memPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(memPath)).
  unfold getMemFromPath, getMemFromPathUnsafe, getLeafElem.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk st_v val; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getMemFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma send_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : SendPath (getNode p))
         (v : Expr type (getSendKind x))
         (s : TreeState DomainElemState t),
    (let currentTrace := castStateSend (embedSendPath p x) (readTreeState t s (embedSendPath p x).(sendPath)) in
     writeTreeState t s (embedSendPath p x).(sendPath)
       (castStateSendInv (embedSendPath p x) (evalExpr (cast_send_expr p x v) :: currentTrace))) =
    writeSubTreeState p s
      (let currentTrace := castStateSend x (readTreeState (getNode p) (readSubTreeState p s) x.(sendPath)) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(sendPath)
         (castStateSendInv x (evalExpr v :: currentTrace))).
Proof.
  intros t p x v s.
  cbv zeta.
  unfold cast_send_expr.
  rewrite evalExpr_eq_rect_Kind.
  unfold castStateSend, castStateSendInv, getSendFromPathTypeEq.
  change (embedSendPath p x).(sendPath) with (@embedLeafIntoPath _ t p x.(sendPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize (evalExpr v).
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(sendPath)).
  generalize (sendKind_embed p x).
  generalize (embedSendPath p x).(sendPathPf).
  generalize x.(sendPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(sendPath)).
  unfold getSendKind, getSendKindFromPath, getLeafElem.
  change (embedSendPath p x).(sendPath) with (@embedLeafIntoPath _ t p x.(sendPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk st_v val; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getSendFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma recv_write_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RecvPath (getNode p))
         (recvVal : type (getRecvKind (embedRecvPath p x)))
         (s : TreeState DomainElemState t),
    (let currentTrace := castStateRecv (embedRecvPath p x) (readTreeState t s (embedRecvPath p x).(recvPath)) in
     writeTreeState t s (embedRecvPath p x).(recvPath)
       (castStateRecvInv (embedRecvPath p x) (recvVal :: currentTrace))) =
    writeSubTreeState p s
      (let currentTrace := castStateRecv x (readTreeState (getNode p) (readSubTreeState p s) x.(recvPath)) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(recvPath)
         (castStateRecvInv x (cast_recv p x recvVal :: currentTrace))).
Proof.
  intros t p x recvVal s.
  cbv zeta.
  unfold cast_recv, castStateRecv, castStateRecvInv, getRecvFromPathTypeEq.
  change (embedRecvPath p x).(recvPath) with (@embedLeafIntoPath _ t p x.(recvPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize recvVal.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(recvPath)).
  generalize (recvKind_embed p x).
  generalize (embedRecvPath p x).(recvPathPf).
  generalize x.(recvPathPf).
  generalize (getLeaf_embedLeafIntoPath_def p x.(recvPath)).
  unfold getRecvKind, getRecvKindFromPath, getLeafElem.
  change (embedRecvPath p x).(recvPath) with (@embedLeafIntoPath _ t p x.(recvPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk st_v rv; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getRecvFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Theorem evalActionPropGen_liftAction :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (a : @Action type (getNode p) k)
         (s : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    evalActionPropGen (@liftAction type t p k a) s P <->
    evalActionPropGen a (readSubTreeState p s) (fun sub' r => P (writeSubTreeState p s sub') r).
Proof.
  intros t p k a.
  induction a; intros s0 P; cbn [liftAction evalActionPropGen].
  - rewrite cast_reg_read_embed.
    apply H.
  - rewrite write_reg_embed, IHa, readSubTreeState_writeSubTreeState_same.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - rewrite read_rq_mem_embed, IHa, readSubTreeState_writeSubTreeState_same.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - rewrite cast_mem_read_rp_embed.
    apply H.
  - rewrite write_mem_embed, IHa, readSubTreeState_writeSubTreeState_same.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - rewrite send_embed, IHa, readSubTreeState_writeSubTreeState_same.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - split.
    + intros [recvVal Hrv].
      rewrite recv_write_embed, H, readSubTreeState_writeSubTreeState_same in Hrv.
      exists (cast_recv p x recvVal).
      revert Hrv; apply evalActionPropGen_mono.
      intros sub' r Hsub'; rewrite writeSubTreeState_writeSubTreeState_same in Hsub'; exact Hsub'.
    + intros [recvVal2 Hrv2].
      exists (eq_rect (getRecvKind x) type recvVal2 (getRecvKind (embedRecvPath p x)) (eq_sym (recvKind_embed p x))).
      rewrite recv_write_embed, H, readSubTreeState_writeSubTreeState_same.
      assert (Hcast :
        cast_recv p x (eq_rect (getRecvKind x) type recvVal2 (getRecvKind (embedRecvPath p x)) (eq_sym (recvKind_embed p x))) =
        recvVal2).
      { unfold cast_recv; generalize (recvKind_embed p x) recvVal2; intros Hk rv; destruct Hk; reflexivity. }
      rewrite Hcast.
      revert Hrv2; apply evalActionPropGen_mono.
      intros sub' r Hsub'; rewrite writeSubTreeState_writeSubTreeState_same; exact Hsub'.
  - apply H.
  - rewrite IHa.
    apply evalActionPropGen_ext; intros sub_mid midRet.
    rewrite H, readSubTreeState_writeSubTreeState_same.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - split; intros [v Hv]; exists v; apply H; exact Hv.
  - destruct (evalExpr p0).
    + rewrite IHa1.
      apply evalActionPropGen_ext; intros sub_mid midRet.
      rewrite H, readSubTreeState_writeSubTreeState_same.
      apply evalActionPropGen_ext; intros sub' r.
      rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
    + rewrite IHa2.
      apply evalActionPropGen_ext; intros sub_mid midRet.
      rewrite H, readSubTreeState_writeSubTreeState_same.
      apply evalActionPropGen_ext; intros sub' r.
      rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - apply IHa.
  - rewrite writeSubTreeState_readSubTreeState; reflexivity.
Qed.

Theorem SemAction_liftAction_iff :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (a : @Action type (getNode p) k)
         (old new : TreeState DomainElemState t) (ret : type k),
    SemAction (@liftAction type t p k a) old new ret <->
    exists sub',
      SemAction a (readSubTreeState p old) sub' ret /\
      new = writeSubTreeState p old sub'.
Proof.
  intros t p k a old new ret.
  rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
  split.
  - intros Heval.
    destruct (evalActionPropGen_to_SemAction a (readSubTreeState p old) _ Heval)
      as [sub' [ret' [Hsem [Hnew Hret]]]].
    subst ret'.
    exists sub'; split; [exact Hsem | symmetry; exact Hnew].
  - intros [sub' [Hsem Hnew]].
    subst new.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    eapply evalActionPropGen_mono; [| exact Hsem].
    intros sub'' r [Hsub Hr]; subst; split; reflexivity.
Qed.

(* ===========================================================================
 * 3. `readRegsList` / `writeRegsList` EVALUATION & REGISTER-BANK LEMMAS
 * =========================================================================== *)

Definition readRegOfKind {t : Tree DomainElem} {k : Kind}
  (rk : RegOfKind (t:=t) k) (s : TreeState DomainElemState t) : type k :=
  eq_rect (regKind (getRegFromPath rk.(rk_path))) type
    (castStateReg rk.(rk_path) (readTreeState t s rk.(rk_path).(regPath)))
    k (Kind_eqb_eq _ _ rk.(rk_pf)).

Definition writeRegOfKind {t : Tree DomainElem} {k : Kind}
  (rk : RegOfKind (t:=t) k) (val : type k)
  (s : TreeState DomainElemState t) : TreeState DomainElemState t :=
  let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
  writeTreeState t s rk.(rk_path).(regPath)
    (castStateRegInv rk.(rk_path) (eq_rect k type val _ (eq_sym pf_eq))).

Fixpoint evalWriteRegsListHelper (curr : nat) {k sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz) (newVal : type k)
  (s : TreeState DomainElemState t) : TreeState DomainElemState t :=
  match paths with
  | nil => s
  | rk :: rest =>
      let s' := if @isEq (Bit sz) idx (Zmod.of_Z _ (Z.of_nat curr))
                then writeRegOfKind rk newVal s
                else s in
      evalWriteRegsListHelper (S curr) rest idx newVal s'
  end.

Definition evalWriteRegsList {k sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz) (newVal : type k)
  (s : TreeState DomainElemState t) : TreeState DomainElemState t :=
  evalWriteRegsListHelper 0 paths idx newVal s.

Fixpoint evalReadRegsListHelper (curr : nat) {k} (acc : list (type k)) {sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz)
  (s : TreeState DomainElemState t) : type k :=
  match paths with
  | nil => fold_left (@evalOrBinary k) acc (getDefault k)
  | rk :: rest =>
      let v := readRegOfKind rk s in
      let iteVal := if @isEq (Bit sz) idx (Zmod.of_Z _ (Z.of_nat curr)) then v else getDefault k in
      evalReadRegsListHelper (S curr) (iteVal :: acc) rest idx s
  end.

Definition evalReadRegsList {k sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz)
  (s : TreeState DomainElemState t) : type k :=
  evalReadRegsListHelper 0 nil paths idx s.

Lemma evalActionPropGen_writeRegsListHelper :
  forall {k sz t} (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx : Expr type (Bit sz)) (newVal : Expr type k)
         (s : TreeState DomainElemState t) P,
    evalActionPropGen (@writeRegsListHelper type curr k sz t paths idx newVal) s P <->
    P (evalWriteRegsListHelper curr paths (evalExpr idx) (evalExpr newVal) s) Zmod.zero.
Proof.
  intros k sz t paths.
  induction paths as [| rk rest IH]; intros curr idx newVal s P;
    cbn [writeRegsListHelper evalWriteRegsListHelper evalActionPropGen evalExpr].
  - reflexivity.
  - unfold writeRegOfKind.
    rewrite evalExpr_eq_rect_Kind.
    destruct (@isEq (Bit sz) (evalExpr idx) (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)));
      cbn [evalActionPropGen]; apply IH.
Qed.

Theorem evalActionPropGen_writeRegsList :
  forall {k sz t} (paths : list (RegOfKind (t:=t) k))
         (idx : Expr type (Bit sz)) (newVal : Expr type k)
         (s : TreeState DomainElemState t) P,
    evalActionPropGen (@writeRegsList type k sz t paths idx newVal) s P <->
    P (evalWriteRegsList paths (evalExpr idx) (evalExpr newVal) s) Zmod.zero.
Proof.
  intros k sz t paths idx newVal s P.
  apply evalActionPropGen_writeRegsListHelper.
Qed.

Lemma evalActionPropGen_readRegsListHelper :
  forall {k sz t} (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (Expr type k)) (idx : Expr type (Bit sz))
         (s : TreeState DomainElemState t) P,
    evalActionPropGen (@readRegsListHelper type curr k acc sz t paths idx) s P <->
    P s (evalReadRegsListHelper curr (map (@evalExpr k) acc) paths (evalExpr idx) s).
Proof.
  intros k sz t paths.
  induction paths as [| rk rest IH]; intros curr acc idx s P;
    cbn [readRegsListHelper evalReadRegsListHelper evalActionPropGen evalExpr].
  - reflexivity.
  - rewrite IH.
    unfold readRegOfKind.
    cbn [map evalExpr].
    reflexivity.
Qed.

Theorem evalActionPropGen_readRegsList :
  forall {k sz t} (paths : list (RegOfKind (t:=t) k))
         (idx : Expr type (Bit sz))
         (s : TreeState DomainElemState t) P,
    evalActionPropGen (@readRegsList type k sz t paths idx) s P <->
    P s (evalReadRegsList paths (evalExpr idx) s).
Proof.
  intros k sz t paths idx s P.
  exact (evalActionPropGen_readRegsListHelper paths 0 nil idx s P).
Qed.

Lemma readRegOfKind_embed :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (rk : RegOfKind (t := getNode p) k)
         (s : TreeState DomainElemState t),
    readRegOfKind (embedRegOfKind p rk) s = readRegOfKind rk (readSubTreeState p s).
Proof.
  intros t p k rk s.
  unfold readRegOfKind.
  pose proof (cast_reg_read_embed p rk.(rk_path) s) as Hcast.
  unfold cast_reg in Hcast.
  rewrite <- Hcast.
  change (embedRegOfKind p rk).(rk_path) with (embedRegPath p rk.(rk_path)).
  generalize (castStateReg (embedRegPath p rk.(rk_path))
                (readTreeState t s (embedRegPath p rk.(rk_path)).(regPath))).
  generalize (Kind_eqb_eq (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))) k (embedRegOfKind p rk).(rk_pf)).
  generalize (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)).
  generalize (regKind_embed p rk.(rk_path)).
  generalize (regKind (getRegFromPath rk.(rk_path))).
  generalize (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))).
  intros k1 k2 Hemb Hk2 Hk1 v.
  destruct Hemb; destruct Hk2; cbn [eq_rect].
  rewrite eq_rect_Kind_refl; reflexivity.
Qed.

Lemma writeRegOfKind_embed :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (rk : RegOfKind (t := getNode p) k) (val : type k)
         (s : TreeState DomainElemState t),
    writeRegOfKind (embedRegOfKind p rk) val s =
    writeSubTreeState p s (writeRegOfKind rk val (readSubTreeState p s)).
Proof.
  intros t p k rk val s.
  unfold writeRegOfKind.
  change (embedRegOfKind p rk).(rk_path) with (embedRegPath p rk.(rk_path)).
  set (w := eq_rect k type val (regKind (getRegFromPath rk.(rk_path)))
              (eq_sym (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)))).
  pose proof (write_reg_embed p rk.(rk_path) (Const type _ w) s) as Hwr.
  cbn [evalExpr] in Hwr.
  rewrite <- Hwr.
  f_equal; f_equal.
  unfold cast_reg_expr; rewrite evalExpr_eq_rect_Kind; cbn [evalExpr].
  subst w.
  generalize (Kind_eqb_eq (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))) k (embedRegOfKind p rk).(rk_pf)).
  generalize (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)).
  generalize (regKind_embed p rk.(rk_path)).
  generalize (regKind (getRegFromPath rk.(rk_path))).
  generalize (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))).
  intros k1 k2 Hemb Hk2 Hk1.
  destruct Hemb; destruct Hk2; cbn [eq_rect eq_sym].
  rewrite eq_rect_Kind_refl; reflexivity.
Qed.

Lemma evalWriteRegsListHelper_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k)) (curr : nat)
         (idx : bits sz) (val : type k) (s : TreeState DomainElemState t),
    evalWriteRegsListHelper curr (map (embedRegOfKind p) paths) idx val s =
    writeSubTreeState p s (evalWriteRegsListHelper curr paths idx val (readSubTreeState p s)).
Proof.
  intros t p k sz paths.
  induction paths as [| rk rest IH]; intros curr idx val s; cbn [map evalWriteRegsListHelper].
  - symmetry; apply writeSubTreeState_readSubTreeState.
  - destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite writeRegOfKind_embed, IH, readSubTreeState_writeSubTreeState_same, writeSubTreeState_writeSubTreeState_same.
      reflexivity.
    + apply IH.
Qed.

Theorem evalWriteRegsList_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k))
         (idx : bits sz) (val : type k) (s : TreeState DomainElemState t),
    evalWriteRegsList (map (embedRegOfKind p) paths) idx val s =
    writeSubTreeState p s (evalWriteRegsList paths idx val (readSubTreeState p s)).
Proof.
  intros t p k sz paths idx val s.
  apply evalWriteRegsListHelper_map_embedRegOfKind.
Qed.

Lemma evalReadRegsListHelper_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz) (s : TreeState DomainElemState t),
    evalReadRegsListHelper curr acc (map (embedRegOfKind p) paths) idx s =
    evalReadRegsListHelper curr acc paths idx (readSubTreeState p s).
Proof.
  intros t p k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx s; cbn [map evalReadRegsListHelper].
  - reflexivity.
  - rewrite readRegOfKind_embed; apply IH.
Qed.

Theorem evalReadRegsList_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k))
         (idx : bits sz) (s : TreeState DomainElemState t),
    evalReadRegsList (map (embedRegOfKind p) paths) idx s =
    evalReadRegsList paths idx (readSubTreeState p s).
Proof.
  intros t p k sz paths idx s.
  apply evalReadRegsListHelper_map_embedRegOfKind.
Qed.

Fixpoint readTreeState_writeTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p : LeafPath t) (v : f (getLeaf p)),
    readTreeState t (writeTreeState t s p v) p = v.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - reflexivity.
  - revert s p v.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p.
    + destruct p as [p_c | p_cs]; simpl.
      * exact (@readTreeState_writeTreeState_same A f c s.(Fst) p_c v).
      * exact (IHcs s.(Snd) p_cs v).
Qed.

Fixpoint readTreeState_writeTreeState_other {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p1 p2 : LeafPath t) (v : f (getLeaf p2)),
    p1 <> p2 ->
    readTreeState t (writeTreeState t s p2 v) p1 = readTreeState t s p1.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - exfalso; apply H; destruct p1, p2; reflexivity.
  - revert s p1 p2 v H.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p1.
    + destruct p1 as [p1_c | p1_cs], p2 as [p2_c | p2_cs]; simpl; try reflexivity.
      * apply (@readTreeState_writeTreeState_other A f c s.(Fst) p1_c p2_c v).
        intro Heq; apply H; subst; reflexivity.
      * apply (IHcs s.(Snd) p1_cs p2_cs v).
        intro Heq; apply H; subst; reflexivity.
Qed.

Fixpoint writeTreeState_writeTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p : LeafPath t) (v1 v2 : f (getLeaf p)),
    writeTreeState t (writeTreeState t s p v1) p v2 = writeTreeState t s p v2.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - reflexivity.
  - revert s p v1 v2.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p.
    + destruct p as [p_c | p_cs]; simpl; f_equal.
      * exact (@writeTreeState_writeTreeState_same A f c s.(Fst) p_c v1 v2).
      * exact (IHcs s.(Snd) p_cs v1 v2).
Qed.

Fixpoint writeTreeState_writeTreeState_comm {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p1 p2 : LeafPath t) (v1 : f (getLeaf p1)) (v2 : f (getLeaf p2)),
    p1 <> p2 ->
    writeTreeState t (writeTreeState t s p1 v1) p2 v2 =
    writeTreeState t (writeTreeState t s p2 v2) p1 v1.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - exfalso; apply H; destruct p1, p2; reflexivity.
  - revert s p1 p2 v1 v2 H.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p1.
    + destruct p1 as [p1_c | p1_cs], p2 as [p2_c | p2_cs]; simpl; try reflexivity.
      * f_equal; apply (@writeTreeState_writeTreeState_comm A f c s.(Fst) p1_c p2_c v1 v2).
        intro Heq; apply H; subst; reflexivity.
      * f_equal; apply (IHcs s.(Snd) p1_cs p2_cs v1 v2).
        intro Heq; apply H; subst; reflexivity.
Qed.

Lemma castStateReg_castStateRegInv :
  forall {t : Tree DomainElem} (x : RegPath t) (v : type (regKind (getRegFromPath x))),
    castStateReg x (castStateRegInv x v) = v.
Proof.
  intros t x v.
  unfold castStateReg, castStateRegInv.
  generalize (getRegFromPathTypeEq x) v.
  intros H v0; destruct H; reflexivity.
Qed.

Lemma readRegOfKind_writeRegOfKind_same :
  forall {t : Tree DomainElem} {k : Kind} (rk : RegOfKind (t:=t) k)
         (v : type k) (s : TreeState DomainElemState t),
    readRegOfKind rk (writeRegOfKind rk v s) = v.
Proof.
  intros t k rk v s.
  unfold readRegOfKind, writeRegOfKind.
  rewrite readTreeState_writeTreeState_same, castStateReg_castStateRegInv.
  generalize (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)).
  generalize (regKind (getRegFromPath rk.(rk_path))).
  intros k0 Hk; destruct Hk; reflexivity.
Qed.

Lemma readRegOfKind_writeRegOfKind_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind}
         (rk1 : RegOfKind (t:=t) k1) (rk2 : RegOfKind (t:=t) k2)
         (v : type k2) (s : TreeState DomainElemState t),
    rk1.(rk_path).(regPath) <> rk2.(rk_path).(regPath) ->
    readRegOfKind rk1 (writeRegOfKind rk2 v s) = readRegOfKind rk1 s.
Proof.
  intros t k1 k2 rk1 rk2 v s Hneq.
  unfold readRegOfKind, writeRegOfKind.
  rewrite (readTreeState_writeTreeState_other s rk1.(rk_path).(regPath) rk2.(rk_path).(regPath) _ Hneq).
  reflexivity.
Qed.

Lemma writeRegOfKind_writeRegOfKind_same :
  forall {t : Tree DomainElem} {k : Kind} (rk : RegOfKind (t:=t) k)
         (v1 v2 : type k) (s : TreeState DomainElemState t),
    writeRegOfKind rk v2 (writeRegOfKind rk v1 s) = writeRegOfKind rk v2 s.
Proof.
  intros t k rk v1 v2 s.
  unfold writeRegOfKind.
  apply writeTreeState_writeTreeState_same.
Qed.

Lemma writeRegOfKind_writeRegOfKind_comm :
  forall {t : Tree DomainElem} {k1 k2 : Kind}
         (rk1 : RegOfKind (t:=t) k1) (rk2 : RegOfKind (t:=t) k2)
         (v1 : type k1) (v2 : type k2) (s : TreeState DomainElemState t),
    rk1.(rk_path).(regPath) <> rk2.(rk_path).(regPath) ->
    writeRegOfKind rk2 v2 (writeRegOfKind rk1 v1 s) =
    writeRegOfKind rk1 v1 (writeRegOfKind rk2 v2 s).
Proof.
  intros t k1 k2 rk1 rk2 v1 v2 s Hneq.
  unfold writeRegOfKind.
  apply writeTreeState_writeTreeState_comm; exact Hneq.
Qed.

Lemma Zmod_or_0_r : forall w (x : bits w),
  Zmod.or x Zmod.zero = x.
Proof.
  intros w x; apply Zmod.unsigned_inj; rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_r; reflexivity.
Qed.

Lemma evalBinaryArray_or_default_r :
  forall (k : Kind) (IHk : forall x : type k, evalOrBinary x (getDefault k) = x)
         (n : nat) (elems : list (type k)) (pf1 : Is_true (Nat.eqb (length elems) n))
         (pf2 : Is_true (Nat.eqb (length (repeat (getDefault k) n)) n)),
    evalBinaryArray (@evalOrBinary k)
      (@Build_SameTuple (type k) n elems pf1)
      (@Build_SameTuple (type k) n (repeat (getDefault k) n) pf2) =
    @Build_SameTuple (type k) n elems pf1.
Proof.
  intros k IHk.
  induction n as [| m IHm]; intros elems pf1 pf2.
  - destruct elems; [| contradiction].
    destruct pf1; reflexivity.
  - destruct elems as [| x xs]; [contradiction |].
    cbn -[evalOrBinary getDefault].
    rewrite IHk, IHm.
    reflexivity.
Qed.

Theorem evalOrBinary_getDefault_r :
  forall (k : Kind) (x : type k),
    evalOrBinary x (getDefault k) = x.
Proof.
  induction k using KindCustomInd; intros x.
  - apply orb_false_r.
  - apply Zmod_or_0_r.
  - induction ls as [| [fname fk] xs IHxs].
    + destruct x; reflexivity.
    + destruct X as [Hx Hxs]; destruct x as [xf xs_val].
      cbn [evalOrBinary evalBinary KindCustomInd getDefault DiffTupleDefault evalBinaryStruct Fst Snd].
      f_equal; [apply Hx | apply (IHxs Hxs)].
  - destruct x as [elems pf1].
    unfold evalOrBinary, evalBinary; cbn [KindCustomInd getDefault SameTupleDefault];
      fold (@evalBinary orb (fun n0 : Z => @Zmod.or (2 ^ n0)) k);
      fold (@evalOrBinary k).
    apply (@evalBinaryArray_or_default_r k IHk).
  - destruct x as [f s].
    cbn [evalOrBinary evalBinary KindCustomInd getDefault Fst Snd].
    rewrite !Zmod_or_0_r; reflexivity.
Qed.

Lemma fold_left_evalOrBinary_default :
  forall {k : Kind} (acc : list (type k)) (init : type k),
    Forall (fun x => x = getDefault k) acc ->
    fold_left (@evalOrBinary k) acc init = init.
Proof.
  intros k acc init Hacc.
  revert init.
  induction Hacc as [| x rest Hx Hrest IH]; intros init; cbn [fold_left].
  - reflexivity.
  - subst x; rewrite evalOrBinary_getDefault_r; apply IH.
Qed.

Lemma evalWriteRegsListHelper_writeRegOfKind_comm :
  forall {t : Tree DomainElem} {k1 k2 : Kind} {sz : Z}
         (rk : RegOfKind (t:=t) k1) (paths : list (RegOfKind (t:=t) k2))
         (curr : nat) (idx : bits sz) (v1 : type k1) (v2 : type k2)
         (s : TreeState DomainElemState t),
    Forall (fun rk' => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) paths ->
    evalWriteRegsListHelper curr paths idx v2 (writeRegOfKind rk v1 s) =
    writeRegOfKind rk v1 (evalWriteRegsListHelper curr paths idx v2 s).
Proof.
  intros t k1 k2 sz rk paths.
  induction paths as [| rk0 rest IH]; intros curr idx v1 v2 s Hfor; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - inversion Hfor as [| ? ? Hneq Hrest]; subst.
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite (writeRegOfKind_writeRegOfKind_comm rk rk0 v1 v2 s Hneq).
      apply IH; exact Hrest.
    + apply IH; exact Hrest.
Qed.

Lemma readRegOfKind_evalWriteRegsListHelper_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind} {sz : Z}
         (rk : RegOfKind (t:=t) k1) (paths : list (RegOfKind (t:=t) k2))
         (curr : nat) (idx : bits sz) (v : type k2) (s : TreeState DomainElemState t),
    Forall (fun rk' => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) paths ->
    readRegOfKind rk (evalWriteRegsListHelper curr paths idx v s) =
    readRegOfKind rk s.
Proof.
  intros t k1 k2 sz rk paths.
  induction paths as [| rk0 rest IH]; intros curr idx v s Hfor; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - inversion Hfor as [| ? ? Hneq Hrest]; subst.
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite (IH (S curr) idx v _ Hrest).
      apply (readRegOfKind_writeRegOfKind_other rk rk0 v s Hneq).
    + apply (IH (S curr) idx v s Hrest).
Qed.

Lemma evalReadRegsListHelper_writeRegOfKind_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind} {sz : Z}
         (rk : RegOfKind (t:=t) k2) (paths : list (RegOfKind (t:=t) k1))
         (curr : nat) (acc : list (type k1)) (idx : bits sz) (v : type k2)
         (s : TreeState DomainElemState t),
    Forall (fun rk' => rk'.(rk_path).(regPath) <> rk.(rk_path).(regPath)) paths ->
    evalReadRegsListHelper curr acc paths idx (writeRegOfKind rk v s) =
    evalReadRegsListHelper curr acc paths idx s.
Proof.
  intros t k1 k2 sz rk paths.
  induction paths as [| rk0 rest IH]; intros curr acc idx v s Hfor; cbn [evalReadRegsListHelper].
  - reflexivity.
  - inversion Hfor as [| ? ? Hneq Hrest]; subst.
    rewrite (readRegOfKind_writeRegOfKind_other rk0 rk v s Hneq).
    apply IH; exact Hrest.
Qed.

Lemma not_In_map_regPath_Forall :
  forall {t : Tree DomainElem} {k : Kind}
         (rk : RegOfKind (t:=t) k) (rest : list (RegOfKind (t:=t) k)),
    ~ In rk.(rk_path).(regPath) (map (fun r : RegOfKind k => r.(rk_path).(regPath)) rest) ->
    Forall (fun rk' : RegOfKind k => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) rest /\
    Forall (fun rk' : RegOfKind k => rk'.(rk_path).(regPath) <> rk.(rk_path).(regPath)) rest.
Proof.
  intros t k rk rest Hnin.
  induction rest as [| r rs IH]; cbn [map In] in *.
  - split; constructor.
  - destruct (IH (fun H => Hnin (or_intror H))) as [HF1 HF2].
    split; constructor; auto.
Qed.

Lemma isEq_Bit_true_iff :
  forall {sz : Z} (a b : bits sz),
    @isEq (Bit sz) a b = true <-> a = b.
Proof.
  intros sz a b; apply Zmod.eqb_eq.
Qed.

Lemma evalWriteRegsListHelper_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    evalWriteRegsListHelper curr paths idx v2 (evalWriteRegsListHelper curr paths idx v1 s) =
    evalWriteRegsListHelper curr paths idx v2 s.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr idx v1 v2 s Hnd; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - cbn [map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct (not_In_map_regPath_Forall rk rest Hnin) as [HF1 _].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx v1 v1 s HF1).
      rewrite writeRegOfKind_writeRegOfKind_same.
      rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx v2 v2 _ HF1).
      rewrite (IH (S curr) idx v1 v2 s Hnd_rest).
      symmetry; apply (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx v2 v2 s HF1).
    + apply IH; exact Hnd_rest.
Qed.

Theorem evalWriteRegsList_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    evalWriteRegsList paths idx v2 (evalWriteRegsList paths idx v1 s) =
    evalWriteRegsList paths idx v2 s.
Proof.
  intros t k sz paths idx v1 v2 s Hnd.
  apply evalWriteRegsListHelper_same; exact Hnd.
Qed.

Lemma evalWriteRegsListHelper_comm :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx1 idx2 : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalWriteRegsListHelper curr paths idx2 v2 (evalWriteRegsListHelper curr paths idx1 v1 s) =
    evalWriteRegsListHelper curr paths idx1 v1 (evalWriteRegsListHelper curr paths idx2 v2 s).
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr idx1 idx2 v1 v2 s Hnd Hneq; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - cbn [map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct (not_In_map_regPath_Forall rk rest Hnin) as [HF1 _].
    destruct (@isEq (Bit sz) idx1 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq1;
    destruct (@isEq (Bit sz) idx2 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq2.
    + apply isEq_Bit_true_iff in Heq1; apply isEq_Bit_true_iff in Heq2; subst; exfalso; apply Hneq; reflexivity.
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx1 v1 v1 s HF1).
      rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v1 v2 _ HF1).
      rewrite (IH (S curr) idx1 idx2 v1 v2 s Hnd_rest Hneq).
      symmetry; apply (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx1 v1 v1 _ HF1).
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v2 v2 s HF1).
      rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx1 v2 v1 _ HF1).
      rewrite <- (IH (S curr) idx1 idx2 v1 v2 s Hnd_rest Hneq).
      apply (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v2 v2 _ HF1).
    + apply IH; [exact Hnd_rest | exact Hneq].
Qed.

Theorem evalWriteRegsList_comm :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx1 idx2 : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalWriteRegsList paths idx2 v2 (evalWriteRegsList paths idx1 v1 s) =
    evalWriteRegsList paths idx1 v1 (evalWriteRegsList paths idx2 v2 s).
Proof.
  intros t k sz paths idx1 idx2 v1 v2 s Hnd Hneq.
  apply evalWriteRegsListHelper_comm; [exact Hnd | exact Hneq].
Qed.

Lemma evalReadRegsListHelper_evalWriteRegsListHelper_other :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (type k)) (idx1 idx2 : bits sz) (v : type k)
         (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalReadRegsListHelper curr acc paths idx1 (evalWriteRegsListHelper curr paths idx2 v s) =
    evalReadRegsListHelper curr acc paths idx1 s.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx1 idx2 v s Hnd Hneq;
    cbn [evalReadRegsListHelper evalWriteRegsListHelper].
  - reflexivity.
  - cbn [map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct (not_In_map_regPath_Forall rk rest Hnin) as [HF1 HF2].
    destruct (@isEq (Bit sz) idx1 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq1;
    destruct (@isEq (Bit sz) idx2 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq2.
    + apply isEq_Bit_true_iff in Heq1; apply isEq_Bit_true_iff in Heq2; subst; exfalso; apply Hneq; reflexivity.
    + rewrite (readRegOfKind_evalWriteRegsListHelper_other rk rest (S curr) idx2 v s HF1).
      apply (IH (S curr) _ idx1 idx2 v s Hnd_rest Hneq).
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v v s HF1).
      rewrite (evalReadRegsListHelper_writeRegOfKind_other rk rest (S curr) _ idx1 v _ HF2).
      apply (IH (S curr) _ idx1 idx2 v s Hnd_rest Hneq).
    + apply (IH (S curr) _ idx1 idx2 v s Hnd_rest Hneq).
Qed.

Theorem evalReadRegsList_evalWriteRegsList_other :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx1 idx2 : bits sz) (v : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalReadRegsList paths idx1 (evalWriteRegsList paths idx2 v s) =
    evalReadRegsList paths idx1 s.
Proof.
  intros t k sz paths idx1 idx2 v s Hnd Hneq.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_other; [exact Hnd | exact Hneq].
Qed.

Lemma isEq_Bit_of_Z_neq :
  forall {sz : Z} (idx : bits sz) (curr : nat),
    (Z.of_nat curr < 2 ^ sz)%Z ->
    Zmod.to_Z idx <> Z.of_nat curr ->
    @isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)) = false.
Proof.
  intros sz idx curr Hlt Hneq.
  destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq; [| reflexivity].
  apply isEq_Bit_true_iff in Heq; subst idx.
  rewrite Zmod.to_Z_of_Z, Z.mod_small in Hneq by lia.
  exfalso; apply Hneq; reflexivity.
Qed.

Lemma isEq_Bit_of_Z_eq :
  forall {sz : Z} (idx : bits sz) (curr : nat),
    Zmod.to_Z idx = Z.of_nat curr ->
    @isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)) = true.
Proof.
  intros sz idx curr Heq.
  apply isEq_Bit_true_iff.
  rewrite <- Heq, Zmod.of_Z_to_Z; reflexivity.
Qed.

Lemma evalWriteRegsListHelper_above :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx : bits sz) (v : type k) (s : TreeState DomainElemState t),
    (Zmod.to_Z idx < Z.of_nat curr)%Z ->
    (Z.of_nat (curr + length paths) <= 2 ^ sz)%Z ->
    evalWriteRegsListHelper curr paths idx v s = s.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr idx v s Hlt Hpow; cbn [evalWriteRegsListHelper length] in *.
  - reflexivity.
  - rewrite isEq_Bit_of_Z_neq by lia.
    apply IH; lia.
Qed.

Lemma evalReadRegsListHelper_above :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz) (s : TreeState DomainElemState t),
    (Zmod.to_Z idx < Z.of_nat curr)%Z ->
    (Z.of_nat (curr + length paths) <= 2 ^ sz)%Z ->
    evalReadRegsListHelper curr acc paths idx s =
    fold_left (@evalOrBinary k) acc (getDefault k).
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx s Hlt Hpow; cbn [evalReadRegsListHelper length] in *.
  - reflexivity.
  - rewrite isEq_Bit_of_Z_neq by lia.
    rewrite IH by lia.
    cbn [fold_left]; rewrite evalOrBinary_getDefault_l; reflexivity.
Qed.

Lemma evalReadRegsListHelper_evalWriteRegsListHelper_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz) (v : type k)
         (s : TreeState DomainElemState t),
    (Z.of_nat curr <= Zmod.to_Z idx < Z.of_nat (curr + length paths))%Z ->
    (Z.of_nat (curr + length paths) <= 2 ^ sz)%Z ->
    Forall (fun x => x = getDefault k) acc ->
    evalReadRegsListHelper curr acc paths idx (evalWriteRegsListHelper curr paths idx v s) = v.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx v s Hbound Hpow Hacc;
    cbn [evalReadRegsListHelper evalWriteRegsListHelper length] in *.
  - lia.
  - destruct (Z.eq_dec (Zmod.to_Z idx) (Z.of_nat curr)) as [Heq | Hneq].
    + rewrite (isEq_Bit_of_Z_eq idx curr Heq).
      rewrite evalWriteRegsListHelper_above by lia.
      rewrite readRegOfKind_writeRegOfKind_same.
      rewrite evalReadRegsListHelper_above by lia.
      cbn [fold_left].
      rewrite evalOrBinary_getDefault_l.
      apply fold_left_evalOrBinary_default; exact Hacc.
    + rewrite isEq_Bit_of_Z_neq by lia.
      apply IH; [lia | lia | constructor; [reflexivity | exact Hacc]].
Qed.

Theorem evalReadRegsList_evalWriteRegsList_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx : bits sz) (v : type k) (s : TreeState DomainElemState t),
    (0 < 2 ^ sz)%Z ->
    Z.of_nat (length paths) = (2 ^ sz)%Z ->
    evalReadRegsList paths idx (evalWriteRegsList paths idx v s) = v.
Proof.
  intros t k sz paths idx v s Hpos Hlen.
  pose proof (Zmod.unsigned_pos_bound idx Hpos) as Hbound.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_same; [lia | lia | constructor].
Qed.

Fixpoint leafPath_id {A : Type} {t : Tree A} : LeafPath t -> list bool :=
  match t return LeafPath t -> list bool with
  | Leaf _ _ => fun _ => nil
  | Node _ children =>
      (fix loop (ls : list (Tree A)) : LeafPath (Node "" ls) -> list bool :=
         match ls return LeafPath (Node "" ls) -> list bool with
         | nil => fun empty => match empty with end
         | x :: xs => fun p =>
             match p with
             | inl px => false :: @leafPath_id A x px
             | inr pxs => true :: loop xs pxs
             end
         end) children
  end.

Lemma NoDup_map_inv :
  forall {A B : Type} (f : A -> B) (ls : list A),
    NoDup (map f ls) ->
    NoDup ls.
Proof.
  intros A B f ls Hnd.
  induction ls as [| x xs IH]; cbn [map] in *; constructor.
  - inversion Hnd as [| ? ? Hnin _]; intros Hin.
    apply Hnin, in_map; exact Hin.
  - inversion Hnd as [| ? ? _ Hnd']; apply IH; exact Hnd'.
Qed.

Lemma NoDup_regPath_of_leafPath_id :
  forall {t : Tree DomainElem} {k : Kind} (paths : list (RegOfKind (t:=t) k)),
    NoDup (map (fun r : RegOfKind k => leafPath_id r.(rk_path).(regPath)) paths) ->
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths).
Proof.
  intros t k paths Hnd.
  apply (NoDup_map_inv (@leafPath_id DomainElem t)).
  rewrite map_map; exact Hnd.
Qed.

(* ===========================================================================
 * 4. REGISTER-BANK HELPER DEFINITIONS & LEMMAS FOR `rfTree`
 * =========================================================================== *)

Definition updGpr (dom : string) (pcAddrInit : Z)
  (idx : bits RegIdxSzReal) (val : type FullECapWithTag)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : TreeState DomainElemState (rfTree dom pcAddrInit) :=
  evalWriteRegsList (gprPathsWithKind dom pcAddrInit) idx val rf.

Definition readGpr (dom : string) (pcAddrInit : Z)
  (idx : bits RegIdxSzReal)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : type FullECapWithTag :=
  evalReadRegsList (gprPathsWithKind dom pcAddrInit) idx rf.

Definition updScr (dom : string) (pcAddrInit : Z)
  (idx : bits ScrIdxSz) (val : type FullECapWithTag)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : TreeState DomainElemState (rfTree dom pcAddrInit) :=
  evalWriteRegsList (scrPathsWithKind dom pcAddrInit) idx val rf.

Definition readScr (dom : string) (pcAddrInit : Z)
  (idx : bits ScrIdxSz)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : type FullECapWithTag :=
  evalReadRegsList (scrPathsWithKind dom pcAddrInit) idx rf.

Definition updCsr (dom : string) (pcAddrInit : Z)
  (idx : bits CsrIdxSz) (val : type (Bit Xlen))
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : TreeState DomainElemState (rfTree dom pcAddrInit) :=
  evalWriteRegsList (csrPathsWithKind dom pcAddrInit) idx val rf.

Definition readCsr (dom : string) (pcAddrInit : Z)
  (idx : bits CsrIdxSz)
  (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
  : type (Bit Xlen) :=
  evalReadRegsList (csrPathsWithKind dom pcAddrInit) idx rf.

Definition is_child0_reg {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inl _ => true
  | inr _ => false
  end.

Definition is_child1_reg {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: c1 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inr (inl _) => true
  | _ => false
  end.

Definition is_child2_reg {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inr (inr (inl _)) => true
  | _ => false
  end.

Lemma writeRegOfKind_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    is_child0_reg r = true ->
    (writeRegOfKind r val s1).(Snd) = s1.(Snd) /\
    (s1.(Fst) = s2.(Fst) ->
     (writeRegOfKind r val s1).(Fst) = (writeRegOfKind r val s2).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 cs k r val s1 s2 Hc0.
  unfold is_child0_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) w).(Snd) = s1.(Snd) /\
          (s1.(Fst) = s2.(Fst) ->
           (writeTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) =
           (writeTreeState (Node name (c0 :: cs)) s2 r.(rk_path).(regPath) w).(Fst) /\
           readTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: cs)) s2 r.(rk_path).(regPath))) as [H1 H2].
  { split; [exact H1 | intros Hfst; destruct (H2 Hfst) as [H3 H4]; split; [exact H3 | rewrite H4; reflexivity]]. }
  clearbody w; revert Hc0 w; generalize (r.(rk_path).(regPath)); intros [p0 | p_rest] Hc0 w; [| discriminate Hc0].
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | intros Hfst; rewrite Hfst; split; reflexivity].
Qed.

Lemma writeRegOfKind_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: c1 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    is_child1_reg r = true ->
    (writeRegOfKind r val s1).(Fst) = s1.(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Snd) = s1.(Snd).(Snd) /\
    (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
     (writeRegOfKind r val s1).(Snd).(Fst) = (writeRegOfKind r val s2).(Snd).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 c1 cs k r val s1 s2 Hc1.
  unfold is_child1_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) = s1.(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd) = s1.(Snd).(Snd) /\
          (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
           (writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Fst) =
           (writeTreeState (Node name (c0 :: c1 :: cs)) s2 r.(rk_path).(regPath) w).(Snd).(Fst) /\
           readTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: c1 :: cs)) s2 r.(rk_path).(regPath))) as [H1 [H2 H3]].
  { split; [exact H1 | split; [exact H2 | intros Hsf; destruct (H3 Hsf) as [H4 H5]; split; [exact H4 | rewrite H5; reflexivity]]]. }
  clearbody w; revert Hc1 w; generalize (r.(rk_path).(regPath)); intros [p0 | [p1 | p_rest]] Hc1 w; try discriminate Hc1.
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | split; [reflexivity | intros Hsf; rewrite Hsf; split; reflexivity]].
Qed.

Lemma writeRegOfKind_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    is_child2_reg r = true ->
    (writeRegOfKind r val s1).(Fst) = s1.(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Fst) = s1.(Snd).(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
    (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
     (writeRegOfKind r val s1).(Snd).(Snd).(Fst) = (writeRegOfKind r val s2).(Snd).(Snd).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 c1 c2 cs k r val s1 s2 Hc2.
  unfold is_child2_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) = s1.(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Fst) = s1.(Snd).(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
          (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
           (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd).(Fst) =
           (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s2 r.(rk_path).(regPath) w).(Snd).(Snd).(Fst) /\
           readTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: c1 :: c2 :: cs)) s2 r.(rk_path).(regPath))) as [H1 [H2 [H3 H4]]].
  { split; [exact H1 | split; [exact H2 | split; [exact H3 | intros Hssf; destruct (H4 Hssf) as [H5 H6]; split; [exact H5 | rewrite H6; reflexivity]]]]. }
  clearbody w; revert Hc2 w; generalize (r.(rk_path).(regPath)); intros [p0 | [p1 | [p2 | p_rest]]] Hc2 w; try discriminate Hc2.
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | split; [reflexivity | split; [reflexivity | intros Hssf; rewrite Hssf; split; reflexivity]]].
Qed.

Lemma evalWriteRegsListHelper_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Snd) = s1.(Snd) /\
    (s1.(Fst) = s2.(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Fst)).
Proof.
  intros name c0 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | exact id].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child0 r val s1 s2 Hr) as [Hsnd Hfst].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest) as [IHsnd IHfst].
      split; [rewrite IHsnd; exact Hsnd | intros Heq; apply IHfst, Hfst, Heq].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg paths = true ->
    s1.(Fst) = s2.(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child0 r (getDefault k) s1 s2 Hr) as [_ Hfst].
    destruct (Hfst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma evalWriteRegsListHelper_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    forallb is_child1_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Fst) = s1.(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd) = s1.(Snd).(Snd) /\
    (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Snd).(Fst)).
Proof.
  intros name c0 c1 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | split; [reflexivity | exact id]].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child1 r val s1 s2 Hr) as [Hfst [Hsndsnd Hsndfst]].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest)
        as [IHfst [IHsndsnd IHsndfst]].
      split; [rewrite IHfst; exact Hfst | split; [rewrite IHsndsnd; exact Hsndsnd | intros Heq; apply IHsndfst, Hsndfst, Heq]].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    forallb is_child1_reg paths = true ->
    s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 c1 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child1 r (getDefault k) s1 s2 Hr) as [_ [_ Hsndfst]].
    destruct (Hsndfst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma evalWriteRegsListHelper_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    forallb is_child2_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Fst) = s1.(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Fst) = s1.(Snd).(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
    (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Snd).(Snd).(Fst)).
Proof.
  intros name c0 c1 c2 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | split; [reflexivity | split; [reflexivity | exact id]]].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child2 r val s1 s2 Hr) as [Hfst [Hsndfst [Hsnd3 Hsnd2fst]]].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest)
        as [IHfst [IHsndfst [IHsnd3 IHsnd2fst]]].
      split; [rewrite IHfst; exact Hfst |
        split; [rewrite IHsndfst; exact Hsndfst |
          split; [rewrite IHsnd3; exact Hsnd3 |
            intros Heq; apply IHsnd2fst, Hsnd2fst, Heq]]].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    forallb is_child2_reg paths = true ->
    s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 c1 c2 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child2 r (getDefault k) s1 s2 Hr) as [_ [_ [_ Hsnd2fst]]].
    destruct (Hsnd2fst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma gprPaths_all_child0 :
  forall dom pcAddrInit,
    forallb is_child0_reg (gprPathsWithKind dom pcAddrInit) = true.
Proof.
  reflexivity.
Qed.

Lemma scrPaths_all_child1 :
  forall dom pcAddrInit,
    forallb is_child1_reg (scrPathsWithKind dom pcAddrInit) = true.
Proof.
  reflexivity.
Qed.

Lemma csrPaths_all_child2 :
  forall dom pcAddrInit,
    forallb is_child2_reg (csrPathsWithKind dom pcAddrInit) = true.
Proof.
  reflexivity.
Qed.

(* --- Cross-bank projections & frame lemmas --- *)

Lemma updGpr_Snd :
  forall dom pcAddrInit idx val rf,
    (updGpr dom pcAddrInit idx val rf).(Snd) = rf.(Snd).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (evalWriteRegsListHelper_child0 (gprPathsWithKind dom pcAddrInit) 0 idx val rf rf
                  (gprPaths_all_child0 dom pcAddrInit))).
Qed.

Lemma updGpr_Fst_ext :
  forall dom pcAddrInit idx val rf1 rf2,
    rf1.(Fst) = rf2.(Fst) ->
    (updGpr dom pcAddrInit idx val rf1).(Fst) = (updGpr dom pcAddrInit idx val rf2).(Fst).
Proof.
  intros dom pcAddrInit idx val rf1 rf2 Heq.
  exact (proj2 (evalWriteRegsListHelper_child0 (gprPathsWithKind dom pcAddrInit) 0 idx val rf1 rf2
                  (gprPaths_all_child0 dom pcAddrInit)) Heq).
Qed.

Lemma readGpr_Fst_ext :
  forall dom pcAddrInit idx rf1 rf2,
    rf1.(Fst) = rf2.(Fst) ->
    readGpr dom pcAddrInit idx rf1 = readGpr dom pcAddrInit idx rf2.
Proof.
  intros dom pcAddrInit idx rf1 rf2 Heq.
  exact (evalReadRegsListHelper_child0 (gprPathsWithKind dom pcAddrInit) 0 nil idx rf1 rf2
           (gprPaths_all_child0 dom pcAddrInit) Heq).
Qed.

Lemma updScr_Fst :
  forall dom pcAddrInit idx val rf,
    (updScr dom pcAddrInit idx val rf).(Fst) = rf.(Fst).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (evalWriteRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                  (scrPaths_all_child1 dom pcAddrInit))).
Qed.

Lemma updScr_Snd_Snd :
  forall dom pcAddrInit idx val rf,
    (updScr dom pcAddrInit idx val rf).(Snd).(Snd) = rf.(Snd).(Snd).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (proj2 (evalWriteRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                         (scrPaths_all_child1 dom pcAddrInit)))).
Qed.

Lemma updScr_Snd_Fst_ext :
  forall dom pcAddrInit idx val rf1 rf2,
    rf1.(Snd).(Fst) = rf2.(Snd).(Fst) ->
    (updScr dom pcAddrInit idx val rf1).(Snd).(Fst) = (updScr dom pcAddrInit idx val rf2).(Snd).(Fst).
Proof.
  intros dom pcAddrInit idx val rf1 rf2 Heq.
  exact (proj2 (proj2 (evalWriteRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 idx val rf1 rf2
                         (scrPaths_all_child1 dom pcAddrInit))) Heq).
Qed.

Lemma readScr_Snd_Fst_ext :
  forall dom pcAddrInit idx rf1 rf2,
    rf1.(Snd).(Fst) = rf2.(Snd).(Fst) ->
    readScr dom pcAddrInit idx rf1 = readScr dom pcAddrInit idx rf2.
Proof.
  intros dom pcAddrInit idx rf1 rf2 Heq.
  exact (evalReadRegsListHelper_child1 (scrPathsWithKind dom pcAddrInit) 0 nil idx rf1 rf2
           (scrPaths_all_child1 dom pcAddrInit) Heq).
Qed.

Lemma updCsr_Fst :
  forall dom pcAddrInit idx val rf,
    (updCsr dom pcAddrInit idx val rf).(Fst) = rf.(Fst).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                  (csrPaths_all_child2 dom pcAddrInit))).
Qed.

Lemma updCsr_Snd_Fst :
  forall dom pcAddrInit idx val rf,
    (updCsr dom pcAddrInit idx val rf).(Snd).(Fst) = rf.(Snd).(Fst).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (proj2 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                         (csrPaths_all_child2 dom pcAddrInit)))).
Qed.

Lemma updCsr_Snd_Snd_Snd :
  forall dom pcAddrInit idx val rf,
    (updCsr dom pcAddrInit idx val rf).(Snd).(Snd).(Snd) = rf.(Snd).(Snd).(Snd).
Proof.
  intros dom pcAddrInit idx val rf.
  exact (proj1 (proj2 (proj2 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf rf
                                (csrPaths_all_child2 dom pcAddrInit))))).
Qed.

Lemma updCsr_Snd_Snd_Fst_ext :
  forall dom pcAddrInit idx val rf1 rf2,
    rf1.(Snd).(Snd).(Fst) = rf2.(Snd).(Snd).(Fst) ->
    (updCsr dom pcAddrInit idx val rf1).(Snd).(Snd).(Fst) = (updCsr dom pcAddrInit idx val rf2).(Snd).(Snd).(Fst).
Proof.
  intros dom pcAddrInit idx val rf1 rf2 Heq.
  exact (proj2 (proj2 (proj2 (evalWriteRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 idx val rf1 rf2
                                (csrPaths_all_child2 dom pcAddrInit)))) Heq).
Qed.

Lemma readCsr_Snd_Snd_Fst_ext :
  forall dom pcAddrInit idx rf1 rf2,
    rf1.(Snd).(Snd).(Fst) = rf2.(Snd).(Snd).(Fst) ->
    readCsr dom pcAddrInit idx rf1 = readCsr dom pcAddrInit idx rf2.
Proof.
  intros dom pcAddrInit idx rf1 rf2 Heq.
  exact (evalReadRegsListHelper_child2 (csrPathsWithKind dom pcAddrInit) 0 nil idx rf1 rf2
           (csrPaths_all_child2 dom pcAddrInit) Heq).
Qed.

Lemma rfTree_state_eq :
  forall {dom pcAddrInit} (rf1 rf2 : TreeState DomainElemState (rfTree dom pcAddrInit)),
    rf1.(Fst) = rf2.(Fst) ->
    rf1.(Snd).(Fst) = rf2.(Snd).(Fst) ->
    rf1.(Snd).(Snd).(Fst) = rf2.(Snd).(Snd).(Fst) ->
    rf1 = rf2.
Proof.
  intros dom pcAddrInit [g1 [s1 [c1 []]]] [g2 [s2 [c2 []]]] Hg Hs Hc.
  cbn [Fst Snd] in *; subst; reflexivity.
Qed.

(* --- Cross-bank commutativity --- *)

Theorem updGpr_updScr_comm :
  forall dom pcAddrInit gprIdx gprVal scrIdx scrVal rf,
    updGpr dom pcAddrInit gprIdx gprVal (updScr dom pcAddrInit scrIdx scrVal rf) =
    updScr dom pcAddrInit scrIdx scrVal (updGpr dom pcAddrInit gprIdx gprVal rf).
Proof.
  intros dom pcAddrInit gprIdx gprVal scrIdx scrVal rf.
  apply rfTree_state_eq.
  - rewrite updScr_Fst; apply updGpr_Fst_ext, updScr_Fst.
  - rewrite !updGpr_Snd; symmetry; apply updScr_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
  - rewrite !updGpr_Snd, !updScr_Snd_Snd, !updGpr_Snd; reflexivity.
Qed.

Theorem updGpr_updCsr_comm :
  forall dom pcAddrInit gprIdx gprVal csrIdx csrVal rf,
    updGpr dom pcAddrInit gprIdx gprVal (updCsr dom pcAddrInit csrIdx csrVal rf) =
    updCsr dom pcAddrInit csrIdx csrVal (updGpr dom pcAddrInit gprIdx gprVal rf).
Proof.
  intros dom pcAddrInit gprIdx gprVal csrIdx csrVal rf.
  apply rfTree_state_eq.
  - rewrite updCsr_Fst; apply updGpr_Fst_ext, updCsr_Fst.
  - rewrite !updGpr_Snd, !updCsr_Snd_Fst, !updGpr_Snd; reflexivity.
  - rewrite !updGpr_Snd; symmetry; apply updCsr_Snd_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
Qed.

Theorem updScr_updCsr_comm :
  forall dom pcAddrInit scrIdx scrVal csrIdx csrVal rf,
    updScr dom pcAddrInit scrIdx scrVal (updCsr dom pcAddrInit csrIdx csrVal rf) =
    updCsr dom pcAddrInit csrIdx csrVal (updScr dom pcAddrInit scrIdx scrVal rf).
Proof.
  intros dom pcAddrInit scrIdx scrVal csrIdx csrVal rf.
  apply rfTree_state_eq.
  - rewrite !updScr_Fst, !updCsr_Fst, !updScr_Fst; reflexivity.
  - rewrite updCsr_Snd_Fst; apply updScr_Snd_Fst_ext, updCsr_Snd_Fst.
  - rewrite !updScr_Snd_Snd; symmetry; apply updCsr_Snd_Snd_Fst_ext; rewrite updScr_Snd_Snd; reflexivity.
Qed.

(* --- Cross-bank read-over-write invariance --- *)

Theorem readScr_updGpr :
  forall dom pcAddrInit scrIdx gprIdx gprVal rf,
    readScr dom pcAddrInit scrIdx (updGpr dom pcAddrInit gprIdx gprVal rf) =
    readScr dom pcAddrInit scrIdx rf.
Proof.
  intros; apply readScr_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
Qed.

Theorem readCsr_updGpr :
  forall dom pcAddrInit csrIdx gprIdx gprVal rf,
    readCsr dom pcAddrInit csrIdx (updGpr dom pcAddrInit gprIdx gprVal rf) =
    readCsr dom pcAddrInit csrIdx rf.
Proof.
  intros; apply readCsr_Snd_Snd_Fst_ext; rewrite updGpr_Snd; reflexivity.
Qed.

Theorem readGpr_updScr :
  forall dom pcAddrInit gprIdx scrIdx scrVal rf,
    readGpr dom pcAddrInit gprIdx (updScr dom pcAddrInit scrIdx scrVal rf) =
    readGpr dom pcAddrInit gprIdx rf.
Proof.
  intros; apply readGpr_Fst_ext, updScr_Fst.
Qed.

Theorem readGpr_updCsr :
  forall dom pcAddrInit gprIdx csrIdx csrVal rf,
    readGpr dom pcAddrInit gprIdx (updCsr dom pcAddrInit csrIdx csrVal rf) =
    readGpr dom pcAddrInit gprIdx rf.
Proof.
  intros; apply readGpr_Fst_ext, updCsr_Fst.
Qed.

Theorem readScr_updCsr :
  forall dom pcAddrInit scrIdx csrIdx csrVal rf,
    readScr dom pcAddrInit scrIdx (updCsr dom pcAddrInit csrIdx csrVal rf) =
    readScr dom pcAddrInit scrIdx rf.
Proof.
  intros; apply readScr_Snd_Fst_ext, updCsr_Snd_Fst.
Qed.

Theorem readCsr_updScr :
  forall dom pcAddrInit csrIdx scrIdx scrVal rf,
    readCsr dom pcAddrInit csrIdx (updScr dom pcAddrInit scrIdx scrVal rf) =
    readCsr dom pcAddrInit csrIdx rf.
Proof.
  intros; apply readCsr_Snd_Snd_Fst_ext; rewrite updScr_Snd_Snd; reflexivity.
Qed.

(* --- Same-bank GPR, SCR, and CSR read-over-write and write-over-write lemmas --- *)

Lemma NoDup_gprPathsWithKind :
  forall dom pcAddrInit,
    NoDup (map (fun r : RegOfKind FullECapWithTag => r.(rk_path).(regPath))
               (gprPathsWithKind dom pcAddrInit)).
Proof.
  intros dom pcAddrInit.
  apply NoDup_regPath_of_leafPath_id.
  cbn [gprPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

Lemma NoDup_scrPathsWithKind :
  forall dom pcAddrInit,
    NoDup (map (fun r : RegOfKind FullECapWithTag => r.(rk_path).(regPath))
               (scrPathsWithKind dom pcAddrInit)).
Proof.
  intros dom pcAddrInit.
  apply NoDup_regPath_of_leafPath_id.
  cbn [scrPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

Lemma NoDup_csrPathsWithKind :
  forall dom pcAddrInit,
    NoDup (map (fun r : RegOfKind (Bit Xlen) => r.(rk_path).(regPath))
               (csrPathsWithKind dom pcAddrInit)).
Proof.
  intros dom pcAddrInit.
  apply NoDup_regPath_of_leafPath_id.
  cbn [csrPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

Theorem updGpr_same :
  forall dom pcAddrInit idx v1 v2 rf,
    updGpr dom pcAddrInit idx v2 (updGpr dom pcAddrInit idx v1 rf) =
    updGpr dom pcAddrInit idx v2 rf.
Proof.
  intros dom pcAddrInit idx v1 v2 rf; unfold updGpr.
  apply evalWriteRegsList_same, NoDup_gprPathsWithKind.
Qed.

Theorem updGpr_comm :
  forall dom pcAddrInit idx1 idx2 v1 v2 rf,
    idx1 <> idx2 ->
    updGpr dom pcAddrInit idx2 v2 (updGpr dom pcAddrInit idx1 v1 rf) =
    updGpr dom pcAddrInit idx1 v1 (updGpr dom pcAddrInit idx2 v2 rf).
Proof.
  intros dom pcAddrInit idx1 idx2 v1 v2 rf Hneq; unfold updGpr.
  apply evalWriteRegsList_comm; [apply NoDup_gprPathsWithKind | exact Hneq].
Qed.

Theorem readGpr_updGpr_other :
  forall dom pcAddrInit idx1 idx2 v rf,
    idx1 <> idx2 ->
    readGpr dom pcAddrInit idx1 (updGpr dom pcAddrInit idx2 v rf) =
    readGpr dom pcAddrInit idx1 rf.
Proof.
  intros dom pcAddrInit idx1 idx2 v rf Hneq; unfold readGpr, updGpr.
  apply evalReadRegsList_evalWriteRegsList_other; [apply NoDup_gprPathsWithKind | exact Hneq].
Qed.

Theorem readGpr_updGpr_same :
  forall dom pcAddrInit idx v rf,
    readGpr dom pcAddrInit idx (updGpr dom pcAddrInit idx v rf) = v.
Proof.
  intros dom pcAddrInit idx v rf; unfold readGpr, updGpr.
  apply evalReadRegsList_evalWriteRegsList_same; reflexivity.
Qed.

Theorem updScr_same :
  forall dom pcAddrInit idx v1 v2 rf,
    updScr dom pcAddrInit idx v2 (updScr dom pcAddrInit idx v1 rf) =
    updScr dom pcAddrInit idx v2 rf.
Proof.
  intros dom pcAddrInit idx v1 v2 rf; unfold updScr.
  apply evalWriteRegsList_same, NoDup_scrPathsWithKind.
Qed.

Theorem updScr_comm :
  forall dom pcAddrInit idx1 idx2 v1 v2 rf,
    idx1 <> idx2 ->
    updScr dom pcAddrInit idx2 v2 (updScr dom pcAddrInit idx1 v1 rf) =
    updScr dom pcAddrInit idx1 v1 (updScr dom pcAddrInit idx2 v2 rf).
Proof.
  intros dom pcAddrInit idx1 idx2 v1 v2 rf Hneq; unfold updScr.
  apply evalWriteRegsList_comm; [apply NoDup_scrPathsWithKind | exact Hneq].
Qed.

Theorem readScr_updScr_other :
  forall dom pcAddrInit idx1 idx2 v rf,
    idx1 <> idx2 ->
    readScr dom pcAddrInit idx1 (updScr dom pcAddrInit idx2 v rf) =
    readScr dom pcAddrInit idx1 rf.
Proof.
  intros dom pcAddrInit idx1 idx2 v rf Hneq; unfold readScr, updScr.
  apply evalReadRegsList_evalWriteRegsList_other; [apply NoDup_scrPathsWithKind | exact Hneq].
Qed.

Theorem updCsr_same :
  forall dom pcAddrInit idx v1 v2 rf,
    updCsr dom pcAddrInit idx v2 (updCsr dom pcAddrInit idx v1 rf) =
    updCsr dom pcAddrInit idx v2 rf.
Proof.
  intros dom pcAddrInit idx v1 v2 rf; unfold updCsr.
  apply evalWriteRegsList_same, NoDup_csrPathsWithKind.
Qed.

Theorem updCsr_comm :
  forall dom pcAddrInit idx1 idx2 v1 v2 rf,
    idx1 <> idx2 ->
    updCsr dom pcAddrInit idx2 v2 (updCsr dom pcAddrInit idx1 v1 rf) =
    updCsr dom pcAddrInit idx1 v1 (updCsr dom pcAddrInit idx2 v2 rf).
Proof.
  intros dom pcAddrInit idx1 idx2 v1 v2 rf Hneq; unfold updCsr.
  apply evalWriteRegsList_comm; [apply NoDup_csrPathsWithKind | exact Hneq].
Qed.

Theorem readCsr_updCsr_other :
  forall dom pcAddrInit idx1 idx2 v rf,
    idx1 <> idx2 ->
    readCsr dom pcAddrInit idx1 (updCsr dom pcAddrInit idx2 v rf) =
    readCsr dom pcAddrInit idx1 rf.
Proof.
  intros dom pcAddrInit idx1 idx2 v rf Hneq; unfold readCsr, updCsr.
  apply evalReadRegsList_evalWriteRegsList_other; [apply NoDup_csrPathsWithKind | exact Hneq].
Qed.

Theorem readScr_updScr_same :
  forall dom pcAddrInit idx v rf,
    Zmod.to_Z idx < 5 ->
    readScr dom pcAddrInit idx (updScr dom pcAddrInit idx v rf) = v.
Proof.
  intros dom pcAddrInit idx v rf Hlt; unfold readScr, updScr, evalReadRegsList, evalWriteRegsList.
  pose proof (Zmod.unsigned_pos_bound idx eq_refl) as Hb.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_same;
    [change (length (scrPathsWithKind dom pcAddrInit)) with 5%nat; lia
    | change (length (scrPathsWithKind dom pcAddrInit)) with 5%nat; change (2 ^ ScrIdxSz) with 8; lia
    | constructor].
Qed.

Theorem readCsr_updCsr_same :
  forall dom pcAddrInit idx v rf,
    Zmod.to_Z idx < 10 ->
    readCsr dom pcAddrInit idx (updCsr dom pcAddrInit idx v rf) = v.
Proof.
  intros dom pcAddrInit idx v rf Hlt; unfold readCsr, updCsr, evalReadRegsList, evalWriteRegsList.
  pose proof (Zmod.unsigned_pos_bound idx eq_refl) as Hb.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_same;
    [change (length (csrPathsWithKind dom pcAddrInit)) with 10%nat; lia
    | change (length (csrPathsWithKind dom pcAddrInit)) with 10%nat; change (2 ^ CsrIdxSz) with 16; lia
    | constructor].
Qed.

(* ===========================================================================
 * 5. `ShiftFifo` EVALUATION LEMMAS FOR `fifoTree dom depth elemK`
 * =========================================================================== *)

Definition fifo_elems {dom : string} {depth : nat} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom depth elemK))
  : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)) :=
  f.(Fst).

Definition fifo_size {dom : string} {depth : nat} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom depth elemK))
  : bits (Z.log2_up (Z.of_nat (depth + 1))) :=
  f.(Snd).(Fst).

Definition mkFifo {dom : string} {depth : nat} {elemK : Kind}
  (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
  (sz : bits (Z.log2_up (Z.of_nat (depth + 1))))
  : TreeState DomainElemState (fifoTree dom depth elemK) :=
  (elems ,, (sz ,, tt)).

Lemma mkFifo_eta :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)),
    mkFifo (fifo_elems f) (fifo_size f) = f.
Proof.
  intros dom depth elemK [elems [sz []]]; reflexivity.
Qed.

Lemma fifo_elems_mkFifo :
  forall {dom depth elemK}
         (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
         (sz : bits (Z.log2_up (Z.of_nat (depth + 1)))),
    fifo_elems (mkFifo elems sz) = elems.
Proof.
  reflexivity.
Qed.

Lemma fifo_size_mkFifo :
  forall {dom depth elemK}
         (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
         (sz : bits (Z.log2_up (Z.of_nat (depth + 1)))),
    fifo_size (mkFifo elems sz) = sz.
Proof.
  reflexivity.
Qed.

Fixpoint evalShiftElems {t : Tree DomainElem} {k : Kind}
  (ps : list (RegOfKind (t:=t) k)) (s : TreeState DomainElemState t)
  : TreeState DomainElemState t :=
  match ps with
  | [] => s
  | [_] => s
  | rkCurr :: ((rkNext :: _) as rest) =>
      let nextVal := readRegOfKind rkNext s in
      evalShiftElems rest (writeRegOfKind rkCurr nextVal s)
  end.

Lemma evalShiftElems_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (ps : list (RegOfKind (t := getNode p) k))
         (s : TreeState DomainElemState t),
    evalShiftElems (map (embedRegOfKind p) ps) s =
    writeSubTreeState p s (evalShiftElems ps (readSubTreeState p s)).
Proof.
  intros t p k ps.
  induction ps as [| rkCurr rest IH]; intros s.
  - cbn [map evalShiftElems]; symmetry; apply writeSubTreeState_readSubTreeState.
  - destruct rest as [| rkNext rest'].
    + cbn [map evalShiftElems]; symmetry; apply writeSubTreeState_readSubTreeState.
    + change (evalShiftElems (map (embedRegOfKind p) (rkCurr :: rkNext :: rest')) s)
        with (evalShiftElems (map (embedRegOfKind p) (rkNext :: rest'))
                (writeRegOfKind (embedRegOfKind p rkCurr)
                  (readRegOfKind (embedRegOfKind p rkNext) s) s)).
      change (evalShiftElems (rkCurr :: rkNext :: rest') (readSubTreeState p s))
        with (evalShiftElems (rkNext :: rest')
                (writeRegOfKind rkCurr
                  (readRegOfKind rkNext (readSubTreeState p s))
                  (readSubTreeState p s))).
      rewrite readRegOfKind_embed, writeRegOfKind_embed, IH,
              readSubTreeState_writeSubTreeState_same, writeSubTreeState_writeSubTreeState_same.
      reflexivity.
Qed.

Definition fifo_head_elem {dom : string} {depth : nat} {elemK : Kind}
  (f : TreeState DomainElemState (fifoTree dom depth elemK)) : type elemK :=
  match elemPathsWithKind dom depth elemK with
  | [] => getDefault elemK
  | rk0 :: _ => readRegOfKind rk0 f
  end.

Definition fifo_enq_elems {dom : string} {depth : nat} {elemK : Kind}
  (idx : bits (Z.log2_up (Z.of_nat (depth + 1)))) (val : type elemK)
  (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
  : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)) :=
  evalWriteRegsList (getTreeRegsOfKind elemK (Node "elems" (elemLeaves dom depth elemK))) idx val elems.

Definition fifo_shift_elems {dom : string} {depth : nat} {elemK : Kind}
  (elems : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)))
  : TreeState DomainElemState (Node "elems" (elemLeaves dom depth elemK)) :=
  evalShiftElems (getTreeRegsOfKind elemK (Node "elems" (elemLeaves dom depth elemK))) elems.

Lemma evalWriteRegsList_elemPathsWithKind :
  forall {dom depth elemK}
         (idx : bits (Z.log2_up (Z.of_nat (depth + 1)))) (val : type elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)),
    evalWriteRegsList (elemPathsWithKind dom depth elemK) idx val f =
    mkFifo (fifo_enq_elems idx val (fifo_elems f)) (fifo_size f).
Proof.
  intros dom depth elemK idx val [elems [sz []]].
  unfold elemPathsWithKind, fifo_enq_elems, fifo_elems, fifo_size, mkFifo.
  rewrite evalWriteRegsList_map_embedRegOfKind.
  reflexivity.
Qed.

Lemma evalShiftElems_elemPathsWithKind :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)),
    evalShiftElems (elemPathsWithKind dom depth elemK) f =
    mkFifo (fifo_shift_elems (fifo_elems f)) (fifo_size f).
Proof.
  intros dom depth elemK [elems [sz []]].
  unfold elemPathsWithKind, fifo_shift_elems, fifo_elems, fifo_size, mkFifo.
  rewrite evalShiftElems_map_embedRegOfKind.
  reflexivity.
Qed.

Lemma evalActionPropGen_readElemReg :
  forall {dom depth elemK} (rk : RegOfKind (t := fifoTree dom depth elemK) elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@readElemReg dom depth elemK type rk) f P <->
    P f (readRegOfKind rk f).
Proof.
  reflexivity.
Qed.

Lemma evalActionPropGen_writeElemReg :
  forall {dom depth elemK} (rk : RegOfKind (t := fifoTree dom depth elemK) elemK)
         (newVal : Expr type elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@writeElemReg dom depth elemK type rk newVal) f P <->
    P (writeRegOfKind rk (evalExpr newVal) f) Zmod.zero.
Proof.
  intros dom depth elemK rk newVal f P.
  unfold writeElemReg, writeRegOfKind; cbn [evalActionPropGen evalExpr].
  rewrite evalExpr_eq_rect_Kind; reflexivity.
Qed.

Lemma evalActionPropGen_shiftElems :
  forall {dom depth elemK} (ps : list (RegOfKind (t := fifoTree dom depth elemK) elemK))
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@shiftElems dom depth elemK type ps) f P <->
    P (evalShiftElems ps f) Zmod.zero.
Proof.
  intros dom depth elemK ps.
  induction ps as [| rkCurr rest IH]; intros f P.
  - reflexivity.
  - destruct rest as [| rkNext rest'].
    + reflexivity.
    + change (@shiftElems dom depth elemK type (rkCurr :: rkNext :: rest'))
        with (LetAction "nextVal" (@readElemReg dom depth elemK type rkNext)
                (fun nextVal =>
                   LetAction "" (@writeElemReg dom depth elemK type rkCurr (Var type elemK nextVal))
                     (fun _ => @shiftElems dom depth elemK type (rkNext :: rest')))).
      cbn [evalActionPropGen].
      rewrite evalActionPropGen_readElemReg, evalActionPropGen_writeElemReg.
      apply IH.
Qed.

Theorem evalActionPropGen_ShiftFifo_isFull :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@isFull dom depth elemK type) f P <->
    P f (Zmod.eqb (fifo_size f)
                  (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) (Z.of_nat depth))).
Proof.
  reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_isEmpty :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@isEmpty dom depth elemK type) f P <->
    P f (Zmod.eqb (fifo_size f) Zmod.zero).
Proof.
  reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_first :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@first dom depth elemK type) f P <->
    P f (fifo_head_elem f ,, (negb (Zmod.eqb (fifo_size f) Zmod.zero) ,, tt)).
Proof.
  intros dom depth elemK f P.
  unfold first, fifo_head_elem, fifo_size.
  cbn [evalActionPropGen evalExpr].
  destruct (elemPathsWithKind dom depth elemK) as [| rk0 rest]; reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_enq :
  forall {dom depth elemK} (val : type elemK)
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@enq dom depth elemK type val) f P <->
    P (if negb (Zmod.eqb (fifo_size f)
                         (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) (Z.of_nat depth)))
       then mkFifo (fifo_enq_elems (fifo_size f) val (fifo_elems f))
                   (evalExpr (Add [Const type (Bit (Z.log2_up (Z.of_nat (depth + 1)))) (fifo_size f); $1]))
       else f) Zmod.zero.
Proof.
  intros dom depth elemK val [elems [sz []]] P.
  unfold enq, isFull, fifo_size, fifo_elems.
  cbn -[writeRegsList elemPathsWithKind].
  destruct (Zmod.eqb sz (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) (Z.of_nat depth))); cbn [negb].
  - reflexivity.
  - rewrite evalActionPropGen_writeRegsList; cbn [evalExpr].
    rewrite evalWriteRegsList_elemPathsWithKind; reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_deq :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@deq dom depth elemK type) f P <->
    P (if negb (Zmod.eqb (fifo_size f) Zmod.zero)
       then mkFifo (fifo_shift_elems (fifo_elems f))
                   (evalExpr (Sub (Const type (Bit (Z.log2_up (Z.of_nat (depth + 1)))) (fifo_size f)) $1))
       else f) Zmod.zero.
Proof.
  intros dom depth elemK [elems [sz []]] P.
  unfold deq, fifo_size, fifo_elems.
  cbn -[shiftElems elemPathsWithKind Sub].
  destruct (Zmod.eqb sz Zmod.zero); cbn [negb].
  - reflexivity.
  - rewrite evalActionPropGen_shiftElems.
    rewrite evalShiftElems_elemPathsWithKind; reflexivity.
Qed.

Theorem evalActionPropGen_ShiftFifo_clear :
  forall {dom depth elemK}
         (f : TreeState DomainElemState (fifoTree dom depth elemK)) P,
    evalActionPropGen (@clear dom depth elemK type) f P <->
    P (mkFifo (fifo_elems f) (Zmod.of_Z (2 ^ Z.log2_up (Z.of_nat (depth + 1))) 0)) Zmod.zero.
Proof.
  intros dom depth elemK [elems [sz []]] P.
  reflexivity.
Qed.

(* --- Depth-1 specializations complementing `ShiftFifoLemmas.v` --- *)

Theorem evalActionPropGen_fifo_isEmpty :
  forall {dom elemK}
         (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
    evalActionPropGen (@isEmpty dom 1 elemK type) f P <->
    P f (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0)).
Proof.
  reflexivity.
Qed.

Theorem evalActionPropGen_fifo_clear :
  forall {dom elemK}
         (f : TreeState DomainElemState (fifoTree dom 1 elemK)) P,
    evalActionPropGen (@clear dom 1 elemK type) f P <->
    P (mkFifo1 (fifo1_elem f) (Zmod.of_Z 2 0)) Zmod.zero.
Proof.
  intros dom elemK [[e []] [sz []]] P.
  reflexivity.
Qed.


