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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits SpecDevice.
From Cheriot Require Import ImplCommon ImplDevice ImplFetch.
From Cheriot.Proof Require Import RefCoreRel RefFetch.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* Milestone 6, bit facts of instruction fetch: the expansion of a compressed instruction keeps its
 * low two bits (so `isCompressed` agrees before and after `preDecode`), and the all-zero word
 * expands to itself (a prefaulted fetch reads the default packet). *)

Lemma preDecode_zero : evalLetExpr (@preDecode type (Zmod.zero : type Inst)) = Zmod.zero.
Proof. vm_compute. reflexivity. Qed.

Lemma low2_q0 : forall raw : type Inst,
  evalExpr (TruncLsb (InstSz - 2) 2 (Var type Inst (evalLetExpr (@expandQuadrant0 type raw)))) = Zmod.zero.
Proof.
  intros raw. unfold expandQuadrant0. cbn [evalLetExpr]. cbn [evalExpr].
  rewrite Zmod_firstn_app by (cbv; congruence). reflexivity.
Qed.

Lemma low2_q1 : forall raw : type Inst,
  evalExpr (TruncLsb (InstSz - 2) 2 (Var type Inst (evalLetExpr (@expandQuadrant1 type raw)))) = Zmod.of_Z _ 1.
Proof.
  intros raw. unfold expandQuadrant1. cbn [evalLetExpr]. cbn [evalExpr].
  rewrite Zmod_firstn_app by (cbv; congruence). reflexivity.
Qed.

Lemma low2_q2 : forall raw : type Inst,
  evalExpr (TruncLsb (InstSz - 2) 2 (Var type Inst (evalLetExpr (@expandQuadrant2 type raw)))) = Zmod.of_Z _ 2.
Proof.
  intros raw. unfold expandQuadrant2. cbn [evalLetExpr]. cbn [evalExpr].
  rewrite Zmod_firstn_app by (cbv; congruence). reflexivity.
Qed.

Lemma bits2_cases : forall q : bits 2, q = Zmod.of_Z _ 0 \/ q = Zmod.of_Z _ 1 \/ q = Zmod.of_Z _ 2 \/ q = Zmod.of_Z _ 3.
Proof.
  intros q. destruct (bits.unsigned_range q ltac:(lia)) as [H0 H1].
  assert (H1' : (Zmod.unsigned q < 4)%Z) by exact H1.
  assert (Hq : q = Zmod.of_Z _ (Zmod.unsigned q)) by (symmetry; apply Zmod.of_Z_unsigned).
  assert (Zmod.unsigned q = 0 \/ Zmod.unsigned q = 1 \/ Zmod.unsigned q = 2 \/ Zmod.unsigned q = 3)%Z as [E | [E | [E | E]]] by lia;
    rewrite E in Hq; [left | right; left | right; right; left | right; right; right]; exact Hq.
Qed.


Lemma constExtract_low2 : forall raw : type Inst,
  evalExpr (ConstExtract 30 2 0 (Var type Inst raw)) = Zmod.firstn 2 raw.
Proof.
  intros raw; cbn [evalExpr ConstExtract]; unfold Zmod_lastn.
  apply Zmod.unsigned_inj; rewrite Zmod.unsigned_of_Z, Z.shiftr_0_r.
  apply Z.mod_small; exact (bits.unsigned_range (Zmod.firstn 2 raw) ltac:(lia)).
Qed.

Lemma orI_0l : forall x : type Inst, @evalOrBinary Inst Zmod.zero x = x.
Proof. intros x; exact (evalOrBinary_getDefault_l Inst x). Qed.
Lemma orI_0r : forall x : type Inst, @evalOrBinary Inst x Zmod.zero = x.
Proof. intros x; exact (evalOrBinary_getDefault_r Inst x). Qed.
Lemma orB_eq : forall a b : bool, @evalOrBinary Bool a b = orb a b.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma preDecode_low2 : forall raw : type Inst,
  Zmod.firstn 2 (evalLetExpr (@preDecode type raw)) = Zmod.firstn 2 raw.
Proof.
  intros raw.
  pose proof (low2_q0 raw) as L0; pose proof (low2_q1 raw) as L1; pose proof (low2_q2 raw) as L2.
  cbn [evalExpr] in L0, L1, L2.
  unfold preDecode. cbn [evalLetExpr]. cbn [evalExpr].
  rewrite constExtract_low2.
  revert L0 L1 L2.
  generalize (evalLetExpr (expandQuadrant0 (ty:=type) raw)) as q0.
  generalize (evalLetExpr (expandQuadrant1 (ty:=type) raw)) as q1.
  generalize (evalLetExpr (expandQuadrant2 (ty:=type) raw)) as q2.
  intros q2 q1 q0 L0 L1 L2.
  remember (Zmod.firstn 2 raw) as q eqn:Eq.
  unfold caseDefault; cbn [evalExpr map fold_left].
  destruct (bits2_cases q) as [-> | [-> | [-> | ->]]]; cbn -[Zmod.firstn evalOrBinary];
    rewrite ?orI_0l, ?orI_0r.
  - exact L0.
  - exact L1.
  - exact L2.
  - exact (eq_sym Eq).
Qed.

(* `isCompressed` before and after the expansion *)
Lemma preDecode_isCompressed : forall raw : type Inst,
  evalExpr (@isCompressed type (evalLetExpr (@preDecode type raw))) = evalExpr (@isCompressed type raw).
Proof.
  intros raw; unfold isCompressed, isAllOnes; cbn [evalExpr].
  exact (f_equal (fun q : bits 2 => @evalNot Bool (@isEq (Bit 2) q (InvDefault (Bit 2)))) (preDecode_low2 raw)).
Qed.

Lemma parcelAddr_self : forall pc : type Addr,
  pcAligned pc -> parcelAddrOf (lineAddrOf pc) (evalExpr (@getPacketParcel type pc)) = pc.
Proof.
  intros pc Hal. unfold pcAligned in Hal; unfold parcelAddrOf, lineAddrOf, getParcelAddr, getPacketParcel, memLineAddr.
  cbn [evalExpr] in Hal |- *.
  rewrite Zmod_lastn_app by (cbv; congruence).
  assert (Hlow : Zmod.app (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits (LgLineBytes - LgFetchParcels)))
                   (Zmod_lastn LgFetchParcels (Zmod.firstn LgLineBytes pc)) = Zmod.firstn LgLineBytes pc).
  { rewrite <- (Zmod_app_firstn_lastn (LgLineBytes - LgFetchParcels) LgFetchParcels (Zmod.firstn LgLineBytes pc))
      at 2 by (cbv; congruence).
    f_equal.
    apply Zmod.unsigned_inj.
    rewrite bits.unsigned_app by (cbv; congruence).
    rewrite !bits.unsigned_firstn by (cbv; congruence).
    assert (H1 : (Zmod.unsigned pc mod 2 ^ 1 = 0)%Z).
    { apply (f_equal Zmod.unsigned) in Hal. rewrite bits.unsigned_firstn in Hal by lia. exact Hal. }
    rewrite Z.mod_mod_divide by (exists (2 ^ (LgLineBytes - 1))%Z; cbv; reflexivity).
    change (LgLineBytes - LgFetchParcels)%Z with 1%Z. rewrite H1. reflexivity. }
  etransitivity; [exact (f_equal (fun x => Zmod.app x (Zmod_lastn (AddrSz - LgLineBytes) pc)) Hlow) |].
  exact (Zmod_app_firstn_lastn LgLineBytes (AddrSz - LgLineBytes) pc ltac:(cbv; congruence) ltac:(cbv; congruence)).
Qed.

Lemma lineAddr_unsigned : forall pc : type Addr,
  Zmod.unsigned (lineAddrOf pc) =
  Z.lor (Zmod.unsigned (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits LgLineBytes)))
        (Z.shiftl (Zmod.unsigned (Zmod_lastn (AddrSz - LgLineBytes) pc)) LgLineBytes).
Proof.
  intros pc; unfold lineAddrOf, memLineAddr; cbn [evalExpr].
  exact (bits.unsigned_app (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits LgLineBytes))
           (Zmod_lastn (AddrSz - LgLineBytes) pc) ltac:(cbv; congruence) ltac:(cbv; congruence)).
Qed.

(* The line address of `pc`, as a number: `pc` rounded down to a multiple of the line size *)
Lemma lineAddr_div : forall pc : type Addr,
  Zmod.unsigned (lineAddrOf pc) = (Zmod.unsigned pc / 2 ^ LgLineBytes * 2 ^ LgLineBytes)%Z.
Proof.
  intros pc; rewrite lineAddr_unsigned.
  change (Zmod.unsigned (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits LgLineBytes))) with 0%Z.
  rewrite Z.lor_0_l, Z.shiftl_mul_pow2 by (cbv; congruence).
  unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by (cbv; congruence).
  f_equal; apply Z.mod_small.
  pose proof (bits.unsigned_range pc ltac:(cbv; congruence)) as [H0 H1].
  assert (Hp : (0 < 2 ^ LgLineBytes)%Z) by (apply Z.pow_pos_nonneg; [lia | cbv; congruence]).
  split; [apply Z.div_pos; [exact H0 | exact Hp] |].
  apply Z.div_lt_upper_bound; [exact Hp |].
  rewrite <- Z.pow_add_r by (cbv; congruence).
  replace (LgLineBytes + (AddrSz - LgLineBytes))%Z with AddrSz by lia; exact H1.
Qed.
