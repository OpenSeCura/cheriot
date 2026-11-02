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

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu.
From Cheriot.Proof Require Import StateRel RefGhost RefCoreRel RefReplay RefExecAux RefBits.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * EVEN PCs
 * ===========================================================================
 * `pcAligned a`: bit 0 of `a` is clear. An address with bit 0 cleared is even (`pcAligned_clear`),
 * an even address plus an instruction size is even (`pcAligned_seq`), so the next PCC of an
 * interrupt, a trap and a non-sequential instruction is even when the current one is
 * (`Alu.v` clears bit 0 of every jump target, of `mtcc` and of `mepcc`). *)

Lemma pcAligned_iff : forall a : type Addr, pcAligned a <-> Zmod.to_Z a mod 2 = 0.
Proof.
  intros a; unfold pcAligned; split; intros H.
  - apply (f_equal Zmod.to_Z) in H; rewrite Zmod.unsigned_0 in H.
    rewrite (to_Z_TruncLsb (AddrSz - 1) 1 (Var type Addr a)) in H; exact H.
  - apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0.
    rewrite (to_Z_TruncLsb (AddrSz - 1) 1 (Var type Addr a)); exact H.
Qed.

Lemma pcAligned_clear :
  forall a : type Addr,
    pcAligned (evalExpr ({< TruncMsb (AddrSz - 1) 1 (Var type Addr a), Const type (Bit 1) Zmod.zero >})).
Proof.
  intros a; unfold pcAligned; cbn [evalExpr].
  rewrite Zmod_firstn_app by (cbv; congruence).
  reflexivity.
Qed.

Lemma pcAligned_seq :
  forall (a : type Addr) (c : bool),
    pcAligned a ->
    pcAligned (evalExpr (Add [ Var type Addr a ;
                               ITE (Var type Bool c) ($(CompInstSz / 8) : Expr type Addr) $(InstSz / 8) ])).
Proof.
  intros a c H; apply pcAligned_iff in H; apply pcAligned_iff.
  rewrite to_Z_Add2.
  rewrite to_Z_Var.
  match goal with |- (?x mod ?m) mod 2 = 0 =>
    rewrite (Z.mod_mod_divide x m 2) by (exists (m / 2); reflexivity)
  end.
  rewrite Zplus_mod, H; destruct c; reflexivity.
Qed.

(* The leaves of `executeNonSequential` and `handleTrap`, in the actions' syntax *)
Lemma pcAligned_upd :
  forall v : type FullECapWithTag,
    pcAligned (evalExpr (#v `{ "addr" <- {< TruncMsb (AddrSz - 1) 1 (##v`"addr"),
                                            Const type (Bit 1) Zmod.zero >} })).(Snd).(Snd).(Fst).
Proof. intros v; exact (pcAligned_clear v.(Snd).(Snd).(Fst)). Qed.

Lemma pcAligned_target :
  forall cur np : type FullECapWithTag,
    pcAligned np.(Snd).(Snd).(Fst) ->
    pcAligned (evalExpr (#cur `{ "tag" <- ##np`"tag" } `{ "addr" <- ##np`"addr" })).(Snd).(Snd).(Fst).
Proof. intros cur np H; exact H. Qed.

Lemma pcAligned_seqPcc :
  forall (pcc : type FullECapWithTag) (c : bool),
    pcAligned pcc.(Snd).(Snd).(Fst) ->
    pcAligned (evalExpr (#pcc `{ "addr" <- Add [ ##pcc`"addr" ; ITE #c $(CompInstSz / 8) $(InstSz / 8) ] }))
      .(Snd).(Snd).(Fst).
Proof. intros pcc c H; exact (pcAligned_seq pcc.(Snd).(Snd).(Fst) c H). Qed.

Lemma pcAligned_ite :
  forall (c : bool) (t f : type FullECapWithTag),
    pcAligned t.(Snd).(Snd).(Fst) -> pcAligned f.(Snd).(Snd).(Fst) ->
    pcAligned (evalExpr (ITE (Var type Bool c) (Var type FullECapWithTag t) (Var type FullECapWithTag f))).(Snd).(Snd).(Fst).
Proof. intros [|] t f Ht Hf; [exact Ht | exact Hf]. Qed.

Lemma evalExpr_Var_eq : forall k (x : type k), evalExpr (Var type k x) = x.
Proof. reflexivity. Qed.

(* The next PCC of the execute output the actions build *)
Lemma defNextPcc_struct :
  forall (e1 : Expr type (Option MulDivUnion)) (e2 : Expr type (Option MemFenceUnion))
         (e3 : Expr type (Option CfPayload)) (e4 : Expr type Bool) (e5 : Expr type FullECapWithTag),
    defNextPcc (evalExpr (STRUCT { "mulDiv" ::= e1 ; "dataMem" ::= e2 ; "cf" ::= e3 ;
                                   "isFenceIRq" ::= e4 ; "nextPcc" ::= e5 } : Expr type ExecuteOut)) =
    evalExpr e5.
Proof. reflexivity. Qed.

Lemma allReturns_ret :
  forall {t : Tree Elem} {k : Kind} (e : Expr type k) (Q : type k -> Prop),
    Q (evalExpr e) -> @allReturns t k (Return e) Q.
Proof. intros t k e Q H; exact H. Qed.

Lemma allReturns_IfElse_both :
  forall {t : Tree Elem} {k1 k2 : Kind} (nm : string) (p : Expr type Bool)
         (tb fb : Action type t k1) (cont : type k1 -> Action type t k2) (Q : type k2 -> Prop),
    allReturns tb (fun v => allReturns (cont v) Q) ->
    allReturns fb (fun v => allReturns (cont v) Q) ->
    allReturns (IfElse nm p tb fb cont) Q.
Proof. intros t k1 k2 nm p tb fb cont Q Ht Hf; cbn [allReturns]; destruct (evalExpr p); assumption. Qed.

Section ExecEven.
  Variable pcAddrInit : Z.

  (* Step to the returned values; sub-actions whose value is not the result are skipped *)
  Local Ltac even_steps :=
    repeat (lazymatch goal with
            | |- allReturns (LetExp _ _ _) _ => simple apply allReturns_step_letexp
            | |- allReturns (LetAction _ _ _) _ => simple apply allReturns_step_let; intros ?
            | |- allReturns (IfElse _ _ _ _ _) _ => simple apply allReturns_IfElse_both
            | |- allReturns (Return _) _ => simple apply allReturns_ret
            | |- allReturns _ _ => simple apply allReturns_any; intros ?
            end; cbv beta).

  Local Ltac even_leaf Hpc :=
    repeat rewrite evalExpr_Var_eq; rewrite defNextPcc_struct; repeat rewrite evalExpr_Var_eq;
    unfold Alu.getSeqPcc;
    repeat (lazymatch goal with
            | |- pcAligned (evalExpr (ITE _ _ _)).(Snd).(Snd).(Fst) => apply pcAligned_ite
            | |- pcAligned (evalExpr (UpdateStruct (UpdateStruct _ _ _) _ _)).(Snd).(Snd).(Fst) =>
                apply pcAligned_target
            | |- pcAligned (evalExpr (UpdateStruct _ _ (Add _))).(Snd).(Snd).(Fst) =>
                apply pcAligned_seqPcc; exact Hpc
            | |- pcAligned (evalExpr (UpdateStruct _ _ _)).(Snd).(Snd).(Fst) => apply pcAligned_upd
            | |- pcAligned (evalExpr (Var _ _ ?x)).(Snd).(Snd).(Fst) => rewrite evalExpr_Var_eq
            end).

  Lemma executeInterrupt_nextPcc_even :
    forall {env : Env (rfTree pcAddrInit)} pcc meip mtip (rf rf' : RfState pcAddrInit) out,
      SemAction env (@executeInterrupt pcAddrInit type pcc meip mtip) rf rf' out ->
      pcAligned (defNextPcc out).(Snd).(Snd).(Fst).
  Proof.
    intros env pcc meip mtip rf rf' out Hsem.
    refine (allReturns_SemAction _ rf rf' out (fun r => pcAligned (defNextPcc r).(Snd).(Snd).(Fst)) _ Hsem).
    unfold executeInterrupt, handleTrap; even_steps.
    apply pcAligned_clear.
  Qed.

  Lemma executeNonSequential_nextPcc_even :
    forall {env : Env (rfTree pcAddrInit)} pcc meip mtip aluOut (rf rf' : RfState pcAddrInit) out,
      pcAligned pcc.(Snd).(Snd).(Fst) ->
      SemAction env (@executeNonSequential pcAddrInit type pcc meip mtip aluOut) rf rf' out ->
      pcAligned (defNextPcc out).(Snd).(Snd).(Fst).
  Proof.
    intros env pcc meip mtip aluOut rf rf' out Hpc Hsem.
    refine (allReturns_SemAction _ rf rf' out (fun r => pcAligned (defNextPcc r).(Snd).(Snd).(Fst)) _ Hsem).
    unfold executeNonSequential, handleTrap; even_steps; even_leaf Hpc.
  Qed.
End ExecEven.
