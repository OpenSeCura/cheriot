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
From Cheriot.Proof Require Import RefConsts RefCoreRel RefRevTable.

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

(* The value of a constant *)
Lemma to_Z_const : forall n z, Zmod.to_Z (evalExpr ($z : Expr type (Bit n))) = z mod 2 ^ n.
Proof. intros n z; cbn [evalExpr]; apply Zmod.unsigned_of_Z. Qed.

(* An access of `2^sz` bytes at `a` crosses its line only when it runs past the line's end *)
Lemma crossesB_false : forall (a : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)),
  Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz <= 2 ^ LgLineBytes ->
  crossesB a sz = false.
Proof.
  intros a sz H.
  pose proof (size_pow_bound (Zmod.to_Z sz) (Zmod.unsigned_pos_bound sz ltac:(reflexivity))) as Hp.
  pose proof capBytes_le_lineBytes as Hcl.
  pose proof lineBytes_pos as Hlb.
  pose proof (Z.mod_pos_bound (Zmod.to_Z a) (2 ^ LgLineBytes) Hlb) as Hlo.
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
  rewrite to_Z_TruncLsb, !to_Z_Var, !to_Z_const.
  change (Zmod.to_Z (@Zmod.one (2 ^ 1))) with 1.
  rewrite lineBytes_succ.
  rewrite (Z.mod_small 1) by lia.
  rewrite Z.shiftl_1_l.
  rewrite (Z.mod_small (2 ^ Zmod.to_Z sz)) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz)) by lia.
  rewrite (Z.mod_small (Zmod.to_Z a mod 2 ^ LgLineBytes + 2 ^ Zmod.to_Z sz - 1)) by lia.
  rewrite Z.div_small by lia.
  reflexivity.
Qed.

(* A single byte never crosses *)
Lemma crossesB_byte : forall a, crossesB a byteSz = false.
Proof.
  intros a; apply crossesB_false.
  change (Zmod.to_Z byteSz) with 0; rewrite Z.pow_0_r.
  pose proof lineBytes_pos; pose proof (Z.mod_pos_bound (Zmod.to_Z a) (2 ^ LgLineBytes) ltac:(lia)); lia.
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
  rewrite to_Z_scanFull.
  change (Zmod.to_Z capSz) with LgNumBytesFullCapSz.
  rewrite lineBytes_split.
  pose proof capBytes_pos; pose proof lineTags_pos.
  rewrite Z.mul_mod_distr_r by lia.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) (2 ^ LgNumLineTags) ltac:(lia)).
  nia.
Qed.
