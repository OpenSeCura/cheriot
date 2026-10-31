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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics HelperLemmas.
From Cheriot Require Import SpecDefines SpecDevice.
From Cheriot.Proof Require Import RefCoreRel RefRevTable.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.

(* Bit-level facts about line accesses:
 * 1. the values of a few more bit operations;
 * 2. an access crosses its line only when its bytes run past the line's end (`crossesB_false`),
 *    so a single byte (`crossesB_byte`) and a capability at a capability-aligned address
 *    (`crossesB_scanFull`) never cross. *)

(* --- 1. Values of Bit Operations --- *)

Lemma to_Z_TruncLsb : forall msb lsb (e : Expr type (Bit (lsb + msb))),
  Zmod.to_Z (evalExpr (TruncLsb msb lsb e)) = Zmod.to_Z (evalExpr e) mod 2 ^ lsb.
Proof. intros msb lsb e; cbn [evalExpr]; unfold Zmod.firstn; apply Zmod.unsigned_of_Z. Qed.

Lemma to_Z_Add2 : forall n (a b : Expr type (Bit n)),
  Zmod.to_Z (evalExpr (Add [a; b])) = (Zmod.to_Z (evalExpr a) + Zmod.to_Z (evalExpr b)) mod 2 ^ n.
Proof.
  intros n a b; cbn [evalExpr map fold_left].
  rewrite !Zmod.unsigned_add, Zmod.unsigned_0, Z.add_0_l, Zmod.mod_unsigned; reflexivity.
Qed.

Lemma to_Z_Sll : forall n m (a : Expr type (Bit n)) (b : Expr type (Bit m)),
  Zmod.to_Z (evalExpr (Sll a b)) = Z.shiftl (Zmod.to_Z (evalExpr a)) (Zmod.to_Z (evalExpr b)) mod 2 ^ n.
Proof. intros n m a b; cbn [evalExpr]; apply Zmod.unsigned_slu. Qed.

Lemma to_Z_Var : forall n (x : bits n), Zmod.to_Z (evalExpr (Var type (Bit n) x)) = Zmod.to_Z x.
Proof. reflexivity. Qed.

(* --- 2. Accesses That Stay in Their Line --- *)

Lemma LgLineBytes_val : 2 ^ LgLineBytes = 32.
Proof. reflexivity. Qed.

(* An access of `2^sz` bytes at `a` crosses its line only when it runs past the line's end *)
Lemma crossesB_false : forall (a : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)),
  Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz <= 2 ^ LgLineBytes ->
  crossesB a sz = false.
Proof.
  intros a sz H.
  rewrite LgLineBytes_val in H.
  assert (Hs : 0 <= Zmod.to_Z sz < 4) by exact (Zmod.unsigned_pos_bound sz ltac:(cbv; reflexivity)).
  pose proof (Zmod.unsigned_pos_bound a ltac:(cbv; reflexivity)) as Ha.
  unfold crossesB, memCrossesLine, memLineOffset.
  match goal with |- evalExpr (FromBit Bool ?e) = false =>
    change (Zmod.eqb (evalExpr e) Zmod.one = false) end.
  unfold Zmod.eqb.
  match goal with |- context [evalExpr (TruncMsb 1 LgLineBytes ?x)] =>
    change (evalExpr (TruncMsb 1 LgLineBytes x)) with (Zmod_lastn 1 (evalExpr x)) end.
  rewrite to_Z_lastn' by (cbv; congruence).
  rewrite to_Z_Sub by (cbv; congruence).
  rewrite to_Z_Add2, to_Z_Sll.
  rewrite !to_Z_ZeroExtend by (cbv; congruence).
  rewrite to_Z_TruncLsb.
  rewrite !to_Z_Var.
  change (Zmod.to_Z (evalExpr ($1 : Expr type (Bit (LgLineBytes + 1))))) with 1.
  rewrite Z.shiftl_1_l.
  rewrite LgLineBytes_val.
  change (2 ^ (LgLineBytes + 1)) with 64.
  change (2 ^ LgLineBytes) with 32.
  change (Zmod.to_Z (@Zmod.one (2 ^ 1))) with 1.
  match goal with |- context [2 ^ ?t mod 64] =>
    assert (Ht : 0 <= t < 4) by exact Hs;
    assert (Hp : 1 <= 2 ^ t <= 8)
      by (destruct Ht as [Ht0 Ht1]; split;
          [apply (Z.pow_le_mono_r 2 0 t); lia | change 8 with (2 ^ 3); apply Z.pow_le_mono_r; lia]);
    rewrite (Z.mod_small (2 ^ t) 64) by lia
  end.
  match goal with |- context [?u mod 32 + 2 ^ ?t] =>
    assert (Hu : u mod 32 + 2 ^ t <= 32) by exact H;
    pose proof (Z.mod_pos_bound u 32 ltac:(lia)) as Hlo;
    rewrite (Z.mod_small (u mod 32 + 2 ^ t) 64) by lia;
    rewrite (Z.mod_small (u mod 32 + 2 ^ t - 1) 64) by lia;
    rewrite Z.div_small by lia
  end.
  reflexivity.
Qed.

(* A single byte never crosses *)
Lemma crossesB_byte : forall a, crossesB a byteSz = false.
Proof.
  intros a; apply crossesB_false.
  change (Zmod.to_Z byteSz) with 0; rewrite LgLineBytes_val.
  cbn [Z.pow].
  match goal with |- ?u mod 32 + 1 <= 32 => pose proof (Z.mod_pos_bound u 32 ltac:(lia)); lia end.
Qed.

(* The value of a capability-aligned address *)
Lemma to_Z_scanFull : forall sa, Zmod.to_Z (scanFull sa) = Zmod.to_Z sa * 2 ^ LgNumBytesFullCapSz.
Proof.
  intros sa; unfold scanFull; cbn [evalExpr].
  assert (HL : 0 <= LgNumBytesFullCapSz <= AddrSz) by (cbv; split; congruence).
  etransitivity; [apply bits.unsigned_app; cbv; congruence |].
  rewrite bits.unsigned_app by (cbv; congruence).
  rewrite !Zmod.unsigned_0, !Z.shiftl_0_l, !Z.lor_0_l.
  rewrite Z.add_0_l, Z.shiftl_mul_pow2 by (cbv; congruence); reflexivity.
Qed.

(* A capability at a capability-aligned address never crosses *)
Lemma crossesB_scanFull : forall sa, crossesB (scanFull sa) capSz = false.
Proof.
  intros sa; apply crossesB_false.
  rewrite to_Z_scanFull, LgLineBytes_val.
  change (Zmod.to_Z capSz) with 3.
  change (2 ^ LgNumBytesFullCapSz) with 8.
  change (2 ^ 3) with 8.
  match goal with |- (?x * 8) mod 32 + 8 <= 32 =>
    pose proof (Z.mod_pos_bound (x * 8) 32 ltac:(lia));
    pose proof (Z.div_mod (x * 8) 32 ltac:(lia));
    lia
  end.
Qed.
