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
From Guru Require Import Library Syntax Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Import SpecDefines SpecMulDiv Fifo ImplMulDiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * PART 0: FOUNDATIONAL BITVECTOR (Zmod) AND KIND UIP LEMMAS
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
  rewrite (Kind_uip_refl pf).
  reflexivity.
Qed.

Lemma eq_rect_r_Kind_refl : forall (k : Kind) (P : Kind -> Type) (v : P k) (pf : k = k),
  eq_rect_r P v pf = v.
Proof.
  intros k P v pf.
  unfold eq_rect_r.
  rewrite (Kind_uip_refl (eq_sym pf)).
  reflexivity.
Qed.

Lemma land_shiftl_small : forall x y n,
  0 <= n -> 0 <= x < 2 ^ n -> Z.land x (y * 2 ^ n) = 0.
Proof.
  intros x y n Hn Hx.
  apply Z.bits_inj_iff'; intros k Hk.
  rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_le_dec k n) as [Hlt | Hge].
  - rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r y (k - n)) by lia.
    destruct (Z.testbit x k); reflexivity.
  - assert (Hxk : Z.testbit x k = false).
    { apply Z.testbit_false; [lia |].
      replace (x / 2 ^ k) with 0; [reflexivity |].
      symmetry; apply Z.div_small; split; [lia |].
      eapply Z.lt_le_trans; [apply Hx | apply Z.pow_le_mono_r; lia]. }
    rewrite Hxk; reflexivity.
Qed.
Arguments land_shiftl_small x y [n] _ _.

Lemma lor_shiftl_small : forall x y n,
  0 <= n -> 0 <= x < 2 ^ n -> Z.lor x (Z.shiftl y n) = x + y * 2 ^ n.
Proof.
  intros x y n Hn Hx.
  rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.add_lor_land x (y * 2 ^ n)) as Hadd.
  rewrite (land_shiftl_small x y Hn Hx) in Hadd.
  lia.
Qed.
Arguments lor_shiftl_small x y [n] _ _.

Lemma lor_mul2_bit : forall q b,
  0 <= q -> 0 <= b < 2 -> Z.lor (2 * q) b = 2 * q + b.
Proof.
  intros q b Hq Hb.
  rewrite Z.lor_comm.
  replace (2 * q) with (Z.shiftl q 1) at 1 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl_small b q (n := 1)) by lia.
  change (2 ^ 1) with 2.
  lia.
Qed.

Lemma unsigned_app_arith : forall (n m : Z) (a : bits n) (b : bits m),
  0 <= n -> 0 <= m ->
  Zmod.unsigned (Zmod.app a b) = Zmod.unsigned a + Zmod.unsigned b * 2 ^ n.
Proof.
  intros n m a b Hn Hm.
  rewrite bits.unsigned_app by lia.
  apply lor_shiftl_small; [lia | apply bits.unsigned_range; lia].
Qed.

Lemma unsigned_app_zero_hi : forall (n m : Z) (a : bits n),
  0 <= n -> 0 <= m ->
  Zmod.unsigned (Zmod.app a (Zmod.zero : bits m)) = Zmod.unsigned a.
Proof.
  intros n m a Hn Hm.
  rewrite unsigned_app_arith by lia.
  rewrite Zmod.unsigned_0.
  lia.
Qed.

Unset Implicit Arguments.

Lemma unsigned_firstn : forall (n w : Z) (a : bits w),
  0 <= n ->
  Zmod.unsigned (@Zmod.firstn n w a) = Zmod.unsigned a mod 2 ^ n.
Proof.
  intros n w a Hn.
  unfold Zmod.firstn.
  rewrite Zmod.unsigned_of_Z.
  reflexivity.
Qed.

Lemma firstn_app_exact : forall (d : Z) (q r : bits d),
  0 <= d ->
  @Zmod.firstn d (d + d) (Zmod.app q r) = q.
Proof.
  intros d q r Hd.
  apply Zmod.unsigned_inj.
  rewrite unsigned_firstn by lia.
  rewrite unsigned_app_arith by lia.
  rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)); lia).
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  apply Z.mod_small; lia.
Qed.

Lemma lastn_app_exact : forall (d : Z) (q r : bits d),
  0 <= d ->
  Zmod_lastn d (Zmod.app q r) = r.
Proof.
  intros d q r Hd.
  apply Zmod.unsigned_inj.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (d + d - d) with d by lia.
  rewrite unsigned_app_arith by lia.
  rewrite Z.div_add by (pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)); lia).
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  pose proof (bits.unsigned_range r ltac:(lia)) as Hr.
  rewrite (Z.div_small (Zmod.unsigned q) (2 ^ d)) by lia.
  rewrite Z.add_0_l.
  apply Z.mod_small; lia.
Qed.

Lemma div_pow2_step : forall (M i : Z),
  0 <= i ->
  M / 2 ^ i = 2 * (M / 2 ^ (i + 1)) + (M / 2 ^ i) mod 2.
Proof.
  intros M i Hi.
  replace (2 ^ (i + 1)) with (2 ^ i * 2) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; ring).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  apply Z_div_mod_eq_full.
Qed.

Lemma pow2_gt_lin : forall d : Z,
  0 <= d -> d < 2 ^ d.
Proof.
  intros d Hd.
  apply Z.pow_gt_lin_r; lia.
Qed.

Lemma neg1_mod_pow2 : forall w : Z,
  0 < w -> (-1) mod 2 ^ w = 2 ^ w - 1.
Proof.
  intros w Hw.
  assert (Hpos : 0 < 2 ^ w) by (apply Z.pow_pos_nonneg; lia).
  symmetry.
  apply (Zmod_unique (-1) (2 ^ w) (-1) (2 ^ w - 1)); lia.
Qed.

Lemma unsigned_and_m1_l : forall (w : Z) (x : bits w),
  0 < w ->
  Zmod.and (InvDefault (Bit w)) x = x.
Proof.
  intros w x Hw.
  apply Zmod.unsigned_inj.
  change (InvDefault (Bit w)) with (Zmod.of_Z (2 ^ w) (-1)).
  rewrite Zmod.unsigned_and, Zmod.unsigned_of_Z.
  assert (Hones : (-1) mod 2 ^ w = Z.ones w).
  { rewrite Z.ones_equiv. unfold Z.pred.
    rewrite (neg1_mod_pow2 w Hw). lia. }
  rewrite Hones.
  rewrite Z.land_comm, Z.land_ones by lia.
  pose proof (bits.unsigned_range x ltac:(lia)) as Hx.
  rewrite !(Z.mod_small (Zmod.unsigned x) (2 ^ w)) by lia.
  reflexivity.
Qed.

Lemma unsigned_extract_bit : forall (d : Z) (x : bits d) (i : nat),
  0 < d ->
  Z.of_nat i < d ->
  Zmod.unsigned (evalExpr (And [ Srl (#x) (Var type (Bit d) (bits.of_Z d (Z.of_nat i))) ; $1 ])) =
  (Zmod.unsigned x / 2 ^ (Z.of_nat i)) mod 2.
Proof.
  intros d x i Hd Hi.
  cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd].
  rewrite unsigned_and_m1_l by lia.
  rewrite Zmod.unsigned_and.
  change (Zmod.to_Z (Zmod.of_Z (2 ^ d) (Z.of_nat i))) with (Zmod.unsigned (Zmod.of_Z (2 ^ d) (Z.of_nat i))).
  rewrite Zmod.unsigned_of_Z.
  pose proof (pow2_gt_lin d ltac:(lia)) as HpowD.
  rewrite (Z.mod_small (Z.of_nat i) (2 ^ d)) by lia.
  rewrite Zmod.unsigned_sru by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Zmod.unsigned_of_Z.
  assert (H2D : 2 <= 2 ^ d).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  rewrite (Z.mod_small 1 (2 ^ d)) by lia.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 1) with 2.
  pose proof (Z.mod_pos_bound (Zmod.unsigned x / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hmod2.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

(* Option B Shift-and-Extract Lemmas *)
Lemma sll_1_iter_mod : forall {d : Z} (op1 shiftOp : bits d) (k : nat),
  0 < d ->
  Zmod.unsigned shiftOp = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
  Zmod.unsigned (evalExpr (Sll (#shiftOp) (Const type (Bit 1) (bits.of_Z 1 1)))) =
  (Zmod.unsigned op1 * 2 ^ (Z.of_nat (S k))) mod 2 ^ d.
Proof.
  intros d op1 shiftOp k Hd Hshift.
  cbn [evalExpr].
  change (Zmod.to_Z (Zmod.of_Z (2 ^ 1) 1)) with 1.
  rewrite Zmod.unsigned_slu by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2.
  rewrite Hshift.
  rewrite Z.mul_mod_idemp_l by (pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)); lia).
  f_equal.
  replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
  rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.
  ring.
Qed.

Lemma unsigned_extract_msb_shifted : forall (input_width k : nat) (op1 shiftOp : bits (Z.of_nat input_width)),
  (k < input_width)%nat ->
  let d := Z.of_nat input_width in
  let i := (input_width - 1 - k)%nat in
  Zmod.unsigned shiftOp = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
  Zmod.unsigned (evalExpr (And [ Srl (#shiftOp) (Var type (Bit d) (bits.of_Z d (d - 1))) ; $1 ])) =
  (Zmod.unsigned op1 / 2 ^ (Z.of_nat i)) mod 2.
Proof.
  intros input_width k op1 shiftOp Hk d i Hshift.
  subst d i.
  replace (Z.of_nat input_width - 1) with (Z.of_nat (input_width - 1)%nat) by lia.
  rewrite (@unsigned_extract_bit (Z.of_nat input_width) shiftOp (input_width - 1)%nat ltac:(lia) ltac:(lia)).
  rewrite <- !Z.testbit_spec' by lia.
  f_equal.
  rewrite Hshift.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftl_spec by lia.
  f_equal.
  lia.
Qed.

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

Lemma slu_1_eq_mul_2 : forall (w : Z) (x : bits w),
  0 < w ->
  Zmod.slu x 1 = Zmod.mul (Zmod.of_Z (2 ^ w) 2) x.
Proof.
  intros w x Hw.
  apply Zmod.unsigned_inj.
  rewrite Zmod.unsigned_slu by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2.
  rewrite Zmod.unsigned_mul, Zmod.unsigned_of_Z.
  rewrite Z.mul_mod_idemp_l by (pose proof (Z.pow_pos_nonneg 2 w ltac:(lia) ltac:(lia)); lia).
  f_equal; ring.
Qed.

Lemma evalExpr_Neg_unsigned : forall {w : Z} (x : bits w),
  0 < w ->
  Zmod.unsigned (evalExpr (Neg (Var type (Bit w) x))) = (- Zmod.unsigned x) mod 2 ^ w.
Proof.
  intros w x Hw.
  cbn [evalExpr Neg fold_left map evalNot KindCustomInd].
  rewrite Zmod.add_0_l.
  rewrite !Zmod.unsigned_add, bits.unsigned_not' by lia.
  rewrite Z.ones_equiv; unfold Z.pred.
  unfold Zmod.one; rewrite Zmod.unsigned_of_Z.
  assert (2 <= 2 ^ w) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small 1 (2 ^ w)) by lia.
  transitivity ((- Zmod.unsigned x + 1 * 2 ^ w) mod 2 ^ w).
  { f_equal; lia. }
  apply Z.mod_add; lia.
Qed.

Lemma evalExpr_Neg_zero : forall {w : Z},
  0 < w ->
  evalExpr (Neg (Var type (Bit w) 0%Zmod)) = 0%Zmod.
Proof.
  intros w Hw.
  apply Zmod.unsigned_inj.
  rewrite evalExpr_Neg_unsigned by lia.
  rewrite Zmod.unsigned_0.
  rewrite Z.mod_0_l by (pose proof (Z.pow_pos_nonneg 2 w ltac:(lia) ltac:(lia)); lia).
  reflexivity.
Qed.

Lemma evalExpr_Neg_involutive : forall {w : Z} (x : bits w),
  0 < w ->
  evalExpr (Neg (Var type (Bit w) (evalExpr (Neg (Var type (Bit w) x))))) = x.
Proof.
  intros w x Hw.
  apply Zmod.unsigned_inj.
  rewrite !evalExpr_Neg_unsigned by lia.
  pose proof (bits.unsigned_range x ltac:(lia)) as Hx.
  destruct (Z.eq_dec (Zmod.unsigned x) 0) as [Hz | Hnz].
  - rewrite Hz.
    rewrite !Z.mod_0_l by lia.
    reflexivity.
  - assert (H1 : (- Zmod.unsigned x) mod 2 ^ w = 2 ^ w - Zmod.unsigned x).
    { transitivity ((2 ^ w - Zmod.unsigned x + (-1) * 2 ^ w) mod 2 ^ w).
      - f_equal; lia.
      - rewrite Z.mod_add by lia. apply Z.mod_small; lia. }
    rewrite H1.
    transitivity ((Zmod.unsigned x + (-1) * 2 ^ w) mod 2 ^ w).
    { f_equal; lia. }
    rewrite Z.mod_add by lia.
    apply Z.mod_small; lia.
Qed.

(* ===========================================================================
 * PART 1: PURE COMBINATIONAL STAGE ARITHMETIC (`Mul`, `Div`, `Shared`)
 * =========================================================================== *)

Section ParameterizedStageArithmetic.
  Variable input_width : nat.
  Hypothesis H_width_pos : (0 < input_width)%nat.

  Local Notation d := (dataLen input_width).

  Lemma d_pos : 0 < d.
  Proof. unfold dataLen; lia. Qed.

  Lemma d_add_d_pos : 0 < d + d.
  Proof. pose proof d_pos; lia. Qed.

  Lemma d_add_1_pos : 0 < d + 1.
  Proof. pose proof d_pos; lia. Qed.

  (* --- 1A. Option B Multiplier Step Arithmetic --- *)

  Lemma mulMultiStep_add :
    forall (c1 c2 : nat) (shiftOp1 : bits d) (extOp2 mulAcc : bits (d + d)),
      evalLetExpr (@mulMultiStep input_width type (c1 + c2)%nat shiftOp1 extOp2 mulAcc) =
      let mid := evalLetExpr (@mulMultiStep input_width type c1 shiftOp1 extOp2 mulAcc) in
      evalLetExpr (@mulMultiStep input_width type c2 (mid @% "shiftOp") extOp2 (mid @% "mulAcc")).
  Proof.
    induction c1 as [| c1' IH]; intros c2 shiftOp1 extOp2 mulAcc.
    - simpl. reflexivity.
    - simpl. apply IH.
  Qed.

  Lemma mulBitStep_step :
    forall (k : nat) (op1 shiftOp1 : bits d) (extOp2 mulAcc : bits (d + d)) (c : Z),
      (k < input_width)%nat ->
      Zmod.unsigned shiftOp1 = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
      mulAcc = Zmod.mul (Zmod.of_Z (2 ^ (d + d)) (c * 2 ^ (Z.of_nat k) + Zmod.unsigned op1 / 2 ^ (d - Z.of_nat k))) extOp2 ->
      let out := evalLetExpr (@mulBitStep input_width type shiftOp1 extOp2 mulAcc) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned op1 * 2 ^ (Z.of_nat (S k))) mod 2 ^ d /\
      out @% "mulAcc" =
        Zmod.mul (Zmod.of_Z (2 ^ (d + d)) (c * 2 ^ (Z.of_nat (S k)) + Zmod.unsigned op1 / 2 ^ (d - Z.of_nat (S k)))) extOp2.
  Proof.
    intros k op1 shiftOp1 extOp2 mulAcc c Hk Hshift Hacc out; unfold out; clear out.
    pose proof d_pos as Hd.
    pose proof d_add_d_pos as Hdd.
    set (i := (input_width - 1 - k)%nat).
    assert (HiZ : Z.of_nat i < d) by (unfold d, i; lia).
    assert (Hi_eq1 : d - 1 - Z.of_nat i = Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq2 : Z.of_nat i + 1 = d - Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq3 : d - Z.of_nat i = Z.of_nat (S k)) by (unfold d, i; lia).
    assert (Hi_eq4 : Z.of_nat i = d - Z.of_nat (S k)) by (unfold d, i; lia).
    cbn [evalLetExpr mulBitStep].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd].
    change (evalExpr (Const type (Bit d) (bits.of_Z d (d - 1)))) with (bits.of_Z d (d - 1)).
    split.
    - apply (sll_1_iter_mod op1 shiftOp1 k Hd Hshift).
    - set (mulBit_D := evalExpr (And [ Srl (#shiftOp1) (Var type (Bit d) (bits.of_Z d (d - 1))) ; $1 ])).
      pose proof (@unsigned_extract_msb_shifted input_width k op1 shiftOp1 Hk Hshift) as Hbit.
      fold d i mulBit_D in Hbit.
      set (b := (Zmod.unsigned op1 / 2 ^ Z.of_nat i) mod 2).
      fold b in Hbit.
      pose proof (Z.mod_pos_bound (Zmod.unsigned op1 / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hb_bound.
      fold b in Hb_bound.
      assert (H_shift1 : Zmod.to_Z (Zmod.of_Z (2 ^ 1) 1) = 1) by reflexivity.
      assert (H_accShift : evalExpr (Sll (#mulAcc) (Const type (Bit 1) (bits.of_Z 1 1))) =
                           Zmod.mul (Zmod.of_Z (2 ^ (d + d)) 2) mulAcc).
      { cbn [evalExpr]. rewrite H_shift1. apply slu_1_eq_mul_2; lia. }
      rewrite <- Hi_eq4, <- Hi_eq3.
      rewrite <- Hi_eq2, <- Hi_eq1 in Hacc.
      assert (H_top_eq : c * 2 ^ (d - Z.of_nat i) + Zmod.unsigned op1 / 2 ^ Z.of_nat i =
                         2 * (c * 2 ^ (d - 1 - Z.of_nat i) + Zmod.unsigned op1 / 2 ^ (Z.of_nat i + 1)) + b).
      { replace (d - Z.of_nat i) with ((d - 1 - Z.of_nat i) + 1) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 1) with 2.
        pose proof (div_pow2_step (Zmod.unsigned op1) (Z.of_nat i) ltac:(lia)) as Hdiv.
        fold b in Hdiv.
        lia. }
      rewrite H_top_eq, H_accShift, Hacc.
      assert (H_bit_bool : evalExpr (isNotZero (#mulBit_D)) = negb (Z.eqb b 0)).
      { cbn [evalExpr isNotZero isZero evalNot isEq KindCustomInd getDefault].
        f_equal.
        destruct (Zmod.eqb_spec mulBit_D (0%Zmod : bits d)) as [Heq | Hne].
        - rewrite Heq, Zmod.unsigned_0 in Hbit.
          symmetry; apply Z.eqb_eq; lia.
        - destruct (Z.eqb_spec b 0) as [Hb0 | Hbne]; [| reflexivity].
          exfalso; apply Hne; apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia. }
      rewrite H_bit_bool.
      set (X := c * 2 ^ (d - 1 - Z.of_nat i) + Zmod.unsigned op1 / 2 ^ (Z.of_nat i + 1)) in *.
      assert (Hb_cases : b = 0 \/ b = 1) by lia.
      destruct Hb_cases as [Hb0 | Hb1]; [rewrite Hb0 | rewrite Hb1];
        cbn [negb Z.eqb evalExpr Fst Snd snd mapDiffTuple fold_left map evalBinary KindCustomInd getDefault].
      + rewrite Z.add_0_r, Zmod.of_Z_mul, Zmod.mul_assoc. reflexivity.
      + rewrite !Zmod.add_0_l.
        apply Zmod.unsigned_inj.
        rewrite Zmod.unsigned_add, !Zmod.unsigned_mul, !Zmod.unsigned_of_Z.
        rewrite !Z.mul_mod_idemp_l, !Z.mul_mod_idemp_r, !Z.add_mod_idemp_l by lia.
        f_equal; ring.
  Qed.

  Theorem mulMultiStep_loop_invariant :
    forall (k : nat) (op1 : bits d) (extOp2 initMulAcc : bits (d + d)) (c : Z),
      (k <= input_width)%nat ->
      initMulAcc = Zmod.mul (Zmod.of_Z (2 ^ (d + d)) c) extOp2 ->
      let out := evalLetExpr (@mulMultiStep input_width type k op1 extOp2 initMulAcc) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d /\
      out @% "mulAcc" =
        Zmod.mul (Zmod.of_Z (2 ^ (d + d)) (c * 2 ^ (Z.of_nat k) + Zmod.unsigned op1 / 2 ^ (d - Z.of_nat k))) extOp2.
  Proof.
    induction k as [| k' IH]; intros op1 extOp2 initMulAcc c Hk Hinit out; unfold out; clear out.
    - simpl.
      cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd].
      change (evalExpr (Const type (Bit d) (bits.of_Z d (d - 1)))) with (bits.of_Z d (d - 1)).
      replace (Z.of_nat 0) with 0 by reflexivity.
      replace (d - 0) with d by lia.
      change (2 ^ 0) with 1.
      rewrite !Z.mul_1_r.
      pose proof d_pos as Hd.
      pose proof (bits.unsigned_range op1 ltac:(lia)) as Hop1.
      rewrite (Z.mod_small (Zmod.unsigned op1) (2 ^ d)) by lia.
      rewrite (Z.div_small (Zmod.unsigned op1) (2 ^ d)) by lia.
      rewrite Z.add_0_r.
      split; [reflexivity | exact Hinit].
    - assert (Hk' : (k' <= input_width)%nat) by lia.
      destruct (IH op1 extOp2 initMulAcc c Hk' Hinit) as [Hshift_k Hacc_k].
      replace (S k') with (k' + 1)%nat by lia.
      rewrite mulMultiStep_add.
      set (mid := evalLetExpr (@mulMultiStep input_width type k' op1 extOp2 initMulAcc)) in *.
      change (evalLetExpr (@mulMultiStep input_width type 1 (mid @% "shiftOp") extOp2 (mid @% "mulAcc")))
        with (evalLetExpr (@mulBitStep input_width type (mid @% "shiftOp") extOp2 (mid @% "mulAcc"))).
      replace (k' + 1)%nat with (S k') by lia.
      apply (mulBitStep_step k' op1 (mid @% "shiftOp") extOp2 (mid @% "mulAcc") c ltac:(lia) Hshift_k Hacc_k).
  Qed.

  (* --- 1B. Option B Divider Step Arithmetic --- *)

  Lemma divMultiStep_add :
    forall (c1 c2 : nat) (shiftMag1 mag2 rem quot : bits d),
      evalLetExpr (@divMultiStep input_width type (c1 + c2)%nat shiftMag1 mag2 rem quot) =
      let mid := evalLetExpr (@divMultiStep input_width type c1 shiftMag1 mag2 rem quot) in
      evalLetExpr (@divMultiStep input_width type c2 (mid @% "shiftOp") mag2 (mid @% "rem") (mid @% "quot")).
  Proof.
    induction c1 as [| c1' IH]; intros c2 shiftMag1 mag2 rem quot.
    - simpl. reflexivity.
    - simpl (@divMultiStep input_width type (S c1' + c2)%nat shiftMag1 mag2 rem quot).
      simpl (@divMultiStep input_width type (S c1') shiftMag1 mag2 rem quot).
      cbn [evalLetExpr].
      apply IH.
  Qed.

  Lemma divBitStep_pos :
    forall (k : nat) (mag1 shiftMag1 mag2 rem quot : bits d),
      (k < input_width)%nat ->
      0 < Zmod.unsigned mag2 ->
      Zmod.unsigned shiftMag1 = (Zmod.unsigned mag1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
      Zmod.unsigned quot * Zmod.unsigned mag2 + Zmod.unsigned rem =
        Zmod.unsigned mag1 / 2 ^ (d - Z.of_nat k) ->
      Zmod.unsigned rem < Zmod.unsigned mag2 ->
      Zmod.unsigned quot < 2 ^ (Z.of_nat k) ->
      let out := evalLetExpr (@divBitStep input_width type shiftMag1 mag2 rem quot) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned mag1 * 2 ^ (Z.of_nat (S k))) mod 2 ^ d /\
      Zmod.unsigned (out @% "quot") * Zmod.unsigned mag2 + Zmod.unsigned (out @% "rem") =
        Zmod.unsigned mag1 / 2 ^ (d - Z.of_nat (S k)) /\
      Zmod.unsigned (out @% "rem") < Zmod.unsigned mag2 /\
      Zmod.unsigned (out @% "quot") < 2 ^ (Z.of_nat (S k)).
  Proof.
    intros k mag1 shiftMag1 mag2 rem quot Hk Hmag2_pos Hshift Hinv Hrem_lt Hquot_lt out; unfold out; clear out.
    pose proof d_pos as Hd.
    set (i := (input_width - 1 - k)%nat).
    assert (HiZ : Z.of_nat i < d) by (unfold d, i; lia).
    assert (Hi_eq1 : d - 1 - Z.of_nat i = Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq2 : Z.of_nat i + 1 = d - Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq3 : d - Z.of_nat i = Z.of_nat (S k)) by (unfold d, i; lia).
    assert (Hi_eq4 : Z.of_nat i = d - Z.of_nat (S k)) by (unfold d, i; lia).
    cbn [evalLetExpr divBitStep].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd].
    change (evalExpr (Const type (Bit d) (bits.of_Z d (d - 1)))) with (bits.of_Z d (d - 1)).
    split; [apply (sll_1_iter_mod mag1 shiftMag1 k Hd Hshift) |].
    set (bit_i_D := evalExpr (And [ Srl (Var type (Bit d) shiftMag1) (Var type (Bit d) (bits.of_Z d (d - 1))) ; $1 ])).
    pose proof (@unsigned_extract_msb_shifted input_width k mag1 shiftMag1 Hk Hshift) as Hbit.
    fold d i bit_i_D in Hbit.
    set (b := (Zmod.unsigned mag1 / 2 ^ Z.of_nat i) mod 2).
    fold b in Hbit.
    pose proof (Z.mod_pos_bound (Zmod.unsigned mag1 / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hb_bound.
    fold b in Hb_bound.
    pose proof (bits.unsigned_range rem ltac:(lia)) as Hrem_range.
    pose proof (bits.unsigned_range quot ltac:(lia)) as Hquot_range.
    pose proof (bits.unsigned_range mag2 ltac:(lia)) as Hmag2_range.
    pose proof (div_pow2_step (Zmod.unsigned mag1) (Z.of_nat i) ltac:(lia)) as Hdiv_step.
    fold b in Hdiv_step.
    rewrite <- Hi_eq1 in Hquot_lt.
    rewrite <- Hi_eq2 in Hinv.
    rewrite <- Hi_eq4, <- Hi_eq3.
    set (remShift := evalExpr (Or [ Sll (ZeroExtend 1 (Var type (Bit d) rem)) (Const type (Bit 1) (bits.of_Z 1 1)) ;
                                    ZeroExtend 1 (Var type (Bit d) bit_i_D) ])).
    assert (H_remShift : Zmod.unsigned remShift = 2 * Zmod.unsigned rem + b).
    { subst remShift.
      cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd ZeroExtend getDefault].
      change (Zmod.to_Z (bits.of_Z 1 1)) with 1.
      rewrite !bits.unsigned_or, Zmod.unsigned_0, !Z.lor_0_l.
      rewrite Zmod.unsigned_slu by lia.
      rewrite !unsigned_app_zero_hi by lia.
      rewrite Z.shiftl_mul_pow2 by lia.
      change (2 ^ 1) with 2.
      assert (2 ^ (d + 1) = 2 * 2 ^ d) by (rewrite Z.pow_add_r by lia; ring).
      rewrite (Z.mod_small (Zmod.unsigned rem * 2) (2 ^ (d + 1))) by lia.
      rewrite Hbit.
      replace (Zmod.unsigned rem * 2) with (2 * Zmod.unsigned rem) by ring.
      rewrite lor_mul2_bit by lia.
      reflexivity. }
    set (mag2Ext := evalExpr (ZeroExtend 1 (Var type (Bit d) mag2))).
    assert (H_mag2Ext : Zmod.unsigned mag2Ext = Zmod.unsigned mag2).
    { subst mag2Ext; cbn [evalExpr ZeroExtend]; apply unsigned_app_zero_hi; lia. }
    set (ge := evalExpr (Uge (Var type (Bit (d + 1)) remShift) (Var type (Bit (d + 1)) mag2Ext))).
    assert (H_ge_iff : ge = true <-> Zmod.unsigned mag2 <= 2 * Zmod.unsigned rem + b).
    { subst ge; cbn [evalExpr Uge evalNot].
      change (Zmod.to_Z remShift) with (Zmod.unsigned remShift).
      change (Zmod.to_Z mag2Ext) with (Zmod.unsigned mag2Ext).
      rewrite H_remShift, H_mag2Ext, Bool.negb_true_iff, Z.ltb_ge; tauto. }
    assert (H_ge_false_iff : ge = false <-> 2 * Zmod.unsigned rem + b < Zmod.unsigned mag2).
    { subst ge; cbn [evalExpr Uge evalNot].
      change (Zmod.to_Z remShift) with (Zmod.unsigned remShift).
      change (Zmod.to_Z mag2Ext) with (Zmod.unsigned mag2Ext).
      rewrite H_remShift, H_mag2Ext, Bool.negb_false_iff, Z.ltb_lt; tauto. }
    set (quotShift := evalExpr (Sll (Var type (Bit d) quot) (Const type (Bit 1) (bits.of_Z 1 1)))).
    assert (H_pow_step : 2 ^ (d - Z.of_nat i) = 2 * 2 ^ (d - 1 - Z.of_nat i)).
    { replace (d - Z.of_nat i) with ((d - 1 - Z.of_nat i) + 1) by lia.
      rewrite Z.pow_add_r by lia; ring. }
    assert (H_pow_bound : 2 ^ (d - 1 - Z.of_nat i) * 2 <= 2 ^ d).
    { replace (2 ^ (d - 1 - Z.of_nat i) * 2) with (2 ^ (d - Z.of_nat i)) by lia.
      apply Z.pow_le_mono_r; lia. }
    assert (H_quotShift : Zmod.unsigned quotShift = 2 * Zmod.unsigned quot).
    { subst quotShift; cbn [evalExpr].
      change (Zmod.to_Z (bits.of_Z 1 1)) with 1.
      rewrite Zmod.unsigned_slu by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2.
      rewrite (Z.mod_small (Zmod.unsigned quot * 2) (2 ^ d)) by lia; lia. }
    cbn [evalExpr Fst Snd snd mapDiffTuple].
    fold remShift mag2Ext ge quotShift.
    destruct ge eqn:Hge.
    - assert (Hge_le : Zmod.unsigned mag2 <= 2 * Zmod.unsigned rem + b) by (apply H_ge_iff; reflexivity).
      cbn [evalExpr ITE0 fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
      rewrite unsigned_firstn by lia.
      rewrite unsigned_sub_ge by lia.
      rewrite H_remShift, H_mag2Ext.
      assert (H_sub_lt : 2 * Zmod.unsigned rem + b - Zmod.unsigned mag2 < Zmod.unsigned mag2) by lia.
      rewrite (Z.mod_small (2 * Zmod.unsigned rem + b - Zmod.unsigned mag2) (2 ^ d)) by lia.
      rewrite !bits.unsigned_or, Zmod.unsigned_0, !Z.lor_0_l, H_quotShift.
      rewrite Zmod.unsigned_of_Z.
      assert (2 <= 2 ^ d) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
      rewrite (Z.mod_small 1 (2 ^ d)) by lia.
      rewrite lor_mul2_bit by lia.
      split; [| split]; lia.
    - assert (Hge_lt : 2 * Zmod.unsigned rem + b < Zmod.unsigned mag2) by (apply H_ge_false_iff; reflexivity).
      cbn [evalExpr ITE0].
      rewrite unsigned_firstn by lia.
      rewrite H_remShift, H_quotShift.
      rewrite (Z.mod_small (2 * Zmod.unsigned rem + b) (2 ^ d)) by lia.
      split; [| split]; lia.
  Qed.

  Lemma divBitStep_zero :
    forall (k : nat) (mag1 shiftMag1 mag2 rem quot : bits d),
      (k < input_width)%nat ->
      Zmod.unsigned mag2 = 0 ->
      Zmod.unsigned shiftMag1 = (Zmod.unsigned mag1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
      Zmod.unsigned rem = Zmod.unsigned mag1 / 2 ^ (d - Z.of_nat k) ->
      Zmod.unsigned quot = 2 ^ (Z.of_nat k) - 1 ->
      let out := evalLetExpr (@divBitStep input_width type shiftMag1 mag2 rem quot) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned mag1 * 2 ^ (Z.of_nat (S k))) mod 2 ^ d /\
      Zmod.unsigned (out @% "rem") = Zmod.unsigned mag1 / 2 ^ (d - Z.of_nat (S k)) /\
      Zmod.unsigned (out @% "quot") = 2 ^ (Z.of_nat (S k)) - 1.
  Proof.
    intros k mag1 shiftMag1 mag2 rem quot Hk Hmag2_0 Hshift Hrem Hquot out; unfold out; clear out.
    pose proof d_pos as Hd.
    set (i := (input_width - 1 - k)%nat).
    assert (HiZ : Z.of_nat i < d) by (unfold d, i; lia).
    assert (Hi_eq1 : d - 1 - Z.of_nat i = Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq2 : Z.of_nat i + 1 = d - Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq3 : d - Z.of_nat i = Z.of_nat (S k)) by (unfold d, i; lia).
    assert (Hi_eq4 : Z.of_nat i = d - Z.of_nat (S k)) by (unfold d, i; lia).
    cbn [evalLetExpr divBitStep].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd].
    change (evalExpr (Const type (Bit d) (bits.of_Z d (d - 1)))) with (bits.of_Z d (d - 1)).
    split; [apply (sll_1_iter_mod mag1 shiftMag1 k Hd Hshift) |].
    set (bit_i_D := evalExpr (And [ Srl (Var type (Bit d) shiftMag1) (Var type (Bit d) (bits.of_Z d (d - 1))) ; $1 ])).
    pose proof (@unsigned_extract_msb_shifted input_width k mag1 shiftMag1 Hk Hshift) as Hbit.
    fold d i bit_i_D in Hbit.
    set (b := (Zmod.unsigned mag1 / 2 ^ Z.of_nat i) mod 2).
    fold b in Hbit.
    pose proof (Z.mod_pos_bound (Zmod.unsigned mag1 / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hb_bound.
    fold b in Hb_bound.
    pose proof (bits.unsigned_range rem ltac:(lia)) as Hrem_range.
    pose proof (bits.unsigned_range mag1 ltac:(lia)) as Hmag1_range.
    pose proof (div_pow2_step (Zmod.unsigned mag1) (Z.of_nat i) ltac:(lia)) as Hdiv_step.
    fold b in Hdiv_step.
    rewrite <- Hi_eq1 in Hquot.
    rewrite <- Hi_eq2 in Hrem.
    rewrite <- Hi_eq4, <- Hi_eq3.
    assert (H_div_bound : Zmod.unsigned mag1 / 2 ^ Z.of_nat i < 2 ^ d).
    { assert (1 <= 2 ^ Z.of_nat i) by (replace 1 with (2 ^ 0) by reflexivity; apply Z.pow_le_mono_r; lia).
      assert (Zmod.unsigned mag1 / 2 ^ Z.of_nat i <= Zmod.unsigned mag1) by (apply Z.div_le_upper_bound; nia).
      lia. }
    set (remShift := evalExpr (Or [ Sll (ZeroExtend 1 (Var type (Bit d) rem)) (Const type (Bit 1) (bits.of_Z 1 1)) ;
                                    ZeroExtend 1 (Var type (Bit d) bit_i_D) ])).
    assert (H_remShift : Zmod.unsigned remShift = 2 * Zmod.unsigned rem + b).
    { subst remShift.
      cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd ZeroExtend getDefault].
      change (Zmod.to_Z (bits.of_Z 1 1)) with 1.
      rewrite !bits.unsigned_or, Zmod.unsigned_0, !Z.lor_0_l.
      rewrite Zmod.unsigned_slu by lia.
      rewrite !unsigned_app_zero_hi by lia.
      rewrite Z.shiftl_mul_pow2 by lia.
      change (2 ^ 1) with 2.
      assert (2 ^ (d + 1) = 2 * 2 ^ d) by (rewrite Z.pow_add_r by lia; ring).
      rewrite (Z.mod_small (Zmod.unsigned rem * 2) (2 ^ (d + 1))) by lia.
      rewrite Hbit.
      replace (Zmod.unsigned rem * 2) with (2 * Zmod.unsigned rem) by ring.
      rewrite lor_mul2_bit by lia.
      reflexivity. }
    set (mag2Ext := evalExpr (ZeroExtend 1 (Var type (Bit d) mag2))).
    assert (H_mag2Ext : Zmod.unsigned mag2Ext = 0).
    { subst mag2Ext; cbn [evalExpr ZeroExtend]; rewrite unsigned_app_zero_hi by lia; exact Hmag2_0. }
    set (ge := evalExpr (Uge (Var type (Bit (d + 1)) remShift) (Var type (Bit (d + 1)) mag2Ext))).
    assert (H_ge_true : ge = true).
    { subst ge; cbn [evalExpr Uge evalNot].
      change (Zmod.to_Z remShift) with (Zmod.unsigned remShift).
      change (Zmod.to_Z mag2Ext) with (Zmod.unsigned mag2Ext).
      rewrite H_remShift, H_mag2Ext, Bool.negb_true_iff, Z.ltb_ge; lia. }
    set (quotShift := evalExpr (Sll (Var type (Bit d) quot) (Const type (Bit 1) (bits.of_Z 1 1)))).
    assert (H_pow_step : 2 ^ (d - Z.of_nat i) = 2 * 2 ^ (d - 1 - Z.of_nat i)).
    { replace (d - Z.of_nat i) with ((d - 1 - Z.of_nat i) + 1) by lia.
      rewrite Z.pow_add_r by lia; ring. }
    assert (H_pow_bound : 2 ^ (d - 1 - Z.of_nat i) * 2 <= 2 ^ d).
    { replace (2 ^ (d - 1 - Z.of_nat i) * 2) with (2 ^ (d - Z.of_nat i)) by lia.
      apply Z.pow_le_mono_r; lia. }
    pose proof (Z.pow_pos_nonneg 2 (d - 1 - Z.of_nat i) ltac:(lia) ltac:(lia)).
    assert (H_quotShift : Zmod.unsigned quotShift = 2 * Zmod.unsigned quot).
    { subst quotShift; cbn [evalExpr].
      change (Zmod.to_Z (bits.of_Z 1 1)) with 1.
      rewrite Zmod.unsigned_slu by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2.
      rewrite (Z.mod_small (Zmod.unsigned quot * 2) (2 ^ d)) by lia; lia. }
    cbn [evalExpr Fst Snd snd mapDiffTuple].
    fold remShift mag2Ext ge quotShift.
    rewrite H_ge_true.
    cbn [evalExpr ITE0 fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
    rewrite unsigned_firstn by lia.
    rewrite unsigned_sub_ge by lia.
    rewrite H_remShift, H_mag2Ext, Z.sub_0_r.
    rewrite (Z.mod_small (2 * Zmod.unsigned rem + b) (2 ^ d)) by lia.
    rewrite !bits.unsigned_or, Zmod.unsigned_0, !Z.lor_0_l, H_quotShift.
    rewrite Zmod.unsigned_of_Z.
    assert (2 <= 2 ^ d) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
    rewrite (Z.mod_small 1 (2 ^ d)) by lia.
    rewrite lor_mul2_bit by lia.
    split; lia.
  Qed.

  Lemma divMultiStep_loop_invariant :
    forall (k : nat) (mag1 mag2 : bits d),
      (k <= input_width)%nat ->
      let out := evalLetExpr (@divMultiStep input_width type k mag1 mag2 0%Zmod 0%Zmod) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned mag1 * 2 ^ (Z.of_nat k)) mod 2 ^ d /\
      (0 < Zmod.unsigned mag2 ->
       Zmod.unsigned (out @% "quot") * Zmod.unsigned mag2 + Zmod.unsigned (out @% "rem") =
         Zmod.unsigned mag1 / 2 ^ (d - Z.of_nat k) /\
       Zmod.unsigned (out @% "rem") < Zmod.unsigned mag2 /\
       Zmod.unsigned (out @% "quot") < 2 ^ (Z.of_nat k)) /\
      (Zmod.unsigned mag2 = 0 ->
       Zmod.unsigned (out @% "rem") = Zmod.unsigned mag1 / 2 ^ (d - Z.of_nat k) /\
       Zmod.unsigned (out @% "quot") = 2 ^ (Z.of_nat k) - 1).
  Proof.
    induction k as [| k' IH]; intros mag1 mag2 Hk out; unfold out; clear out.
    - cbn [divMultiStep evalLetExpr].
      cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum Fst Snd mapDiffTuple].
      cbn [evalExpr Fst Snd snd mapDiffTuple].
      replace (Z.of_nat 0) with 0 by reflexivity.
      replace (d - 0) with d by lia.
      change (2 ^ 0) with 1.
      rewrite !Z.mul_1_r.
      pose proof d_pos as Hd.
      pose proof (bits.unsigned_range mag1 ltac:(lia)) as Hmag1.
      rewrite (Z.mod_small (Zmod.unsigned mag1) (2 ^ d)) by lia.
      rewrite (Z.div_small (Zmod.unsigned mag1) (2 ^ d)) by lia.
      rewrite !Zmod.unsigned_0.
      split; [reflexivity | split; intros Hmag2; lia].
    - assert (Hk' : (k' <= input_width)%nat) by lia.
      specialize (IH mag1 mag2 Hk') as [Hshift_k [Hpos_k Hzero_k]].
      replace (S k') with (k' + 1)%nat by lia.
      rewrite divMultiStep_add.
      set (mid := evalLetExpr (@divMultiStep input_width type k' mag1 mag2 0%Zmod 0%Zmod)) in *.
      change (evalLetExpr (@divMultiStep input_width type 1 (mid @% "shiftOp") mag2 (mid @% "rem") (mid @% "quot")))
        with (evalLetExpr (@divBitStep input_width type (mid @% "shiftOp") mag2 (mid @% "rem") (mid @% "quot"))).
      replace (k' + 1)%nat with (S k') by lia.
      destruct (Z.eq_dec (Zmod.unsigned mag2) 0) as [Hz | Hnz].
      + specialize (Hzero_k Hz) as [Hr_k Hq_k].
        pose proof (divBitStep_zero k' mag1 (mid @% "shiftOp") mag2 (mid @% "rem") (mid @% "quot")
                      ltac:(lia) Hz Hshift_k Hr_k Hq_k) as [Hsh' [Hr' Hq']].
        split; [exact Hsh' | split; [intros Hpos; lia | intros _; split; [exact Hr' | exact Hq']]].
      + assert (Hpos : 0 < Zmod.unsigned mag2) by (pose proof (bits.unsigned_range mag2 ltac:(pose proof d_pos; lia)); lia).
        specialize (Hpos_k Hpos) as [Hinv_k [Hr_lt Hq_lt]].
        pose proof (divBitStep_pos k' mag1 (mid @% "shiftOp") mag2 (mid @% "rem") (mid @% "quot")
                      ltac:(lia) Hpos Hshift_k Hinv_k Hr_lt Hq_lt) as [Hsh' [Hinv' [Hr' Hq']]].
        split; [exact Hsh' | split; [intros _; exact (conj Hinv' (conj Hr' Hq')) | intros Hz; lia]].
  Qed.

  (* --- 1C. Full-Width Evaluation at `k = input_width` --- *)

  Lemma evalExpr_Sub_unsigned : forall (w : Z) (a b : bits w),
    0 < w ->
    Zmod.unsigned (evalExpr (Sub (#a) (#b))) =
    (Zmod.unsigned a - Zmod.unsigned b) mod 2 ^ w.
  Proof.
    intros w a b Hw.
    cbn [evalExpr Sub fold_left map evalNot KindCustomInd].
    rewrite Zmod.add_0_l.
    rewrite !Zmod.unsigned_add.
    rewrite bits.unsigned_not' by lia.
    rewrite Z.ones_equiv; unfold Z.pred.
    unfold Zmod.one; rewrite Zmod.unsigned_of_Z.
    assert (H2w : 2 <= 2 ^ w) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
    rewrite (Z.mod_small 1 (2 ^ w)) by lia.
    pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
    pose proof (bits.unsigned_range b ltac:(lia)) as Hb.
    rewrite Z.add_mod_idemp_l by lia.
    transitivity (((Zmod.unsigned a - Zmod.unsigned b) + 1 * 2 ^ w) mod 2 ^ w).
    { f_equal; lia. }
    apply Z.mod_add; lia.
  Qed.

  Lemma mod_mul_pow2_add : forall a x P : Z,
    0 < P ->
    (a + (x mod P) * P) mod (P * P) = (a + x * P) mod (P * P).
  Proof.
    intros a x P HP.
    replace (x mod P) with (x - (x / P) * P) by (pose proof (Z.div_mod x P ltac:(lia)); lia).
    replace (a + (x - (x / P) * P) * P) with ((a + x * P) + (- (x / P)) * (P * P)) by ring.
    apply Z.mod_add; nia.
  Qed.

  Lemma unsigned_mulMultiStep_at_width :
    forall (op1 op2 : bits d),
      let extOp2 := evalExpr (ZeroExtend d (Var type (Bit d) op2)) in
      let out := evalLetExpr (@mulMultiStep input_width type input_width op1 extOp2 0%Zmod) in
      Zmod.unsigned (out @% "mulAcc") = Zmod.unsigned op1 * Zmod.unsigned op2.
  Proof.
    intros op1 op2 extOp2 out.
    pose proof d_pos as Hd.
    pose proof d_add_d_pos as Hdd.
    assert (H_init : (0%Zmod : bits (d + d)) = Zmod.mul (Zmod.of_Z (2 ^ (d + d)) 0) extOp2).
    { change (Zmod.of_Z (2 ^ (d + d)) 0) with (0%Zmod : bits (d + d)).
      rewrite Zmod.mul_0_l; reflexivity. }
    pose proof (proj2 (mulMultiStep_loop_invariant input_width op1 extOp2 0%Zmod 0 (Nat.le_refl _) H_init)) as Hmul.
    fold out in Hmul.
    change (Z.of_nat input_width) with d in Hmul.
    replace (d - d) with 0 in Hmul by lia.
    change (2 ^ 0) with 1 in Hmul.
    rewrite Z.div_1_r, Z.mul_0_l, Z.add_0_l in Hmul.
    rewrite Hmul.
    rewrite Zmod.unsigned_mul, Zmod.unsigned_of_Z.
    unfold extOp2; cbn [evalExpr ZeroExtend]; rewrite unsigned_app_arith by lia.
    rewrite Zmod.unsigned_0, Z.mul_0_l, Z.add_0_r.
    pose proof (bits.unsigned_range op1 ltac:(lia)) as Hop1.
    pose proof (bits.unsigned_range op2 ltac:(lia)) as Hop2.
    assert (H_pow2D : 2 ^ (d + d) = 2 ^ d * 2 ^ d) by (apply Z.pow_add_r; lia).
    rewrite (Z.mod_small (Zmod.unsigned op1) (2 ^ (d + d))) by nia.
    apply Z.mod_small; nia.
  Qed.

  Theorem mulApproach3_fullProd_eq :
    forall (op1Signed op2Signed : bool) (op1 op2 : bits d),
      let op1Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op1))) in
      let op2Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op2))) in
      let neg1   := evalExpr (And [ Var type Bool op1Signed ; Var type Bool op1Neg ]) in
      let neg2   := evalExpr (And [ Var type Bool op2Signed ; Var type Bool op2Neg ]) in
      let subOp2 := evalExpr (ITE (Var type Bool neg1) (Var type (Bit d) op2) $0) in
      let subOp1 := evalExpr (ITE (Var type Bool neg2) (Var type (Bit d) op1) $0) in
      let hiCorr := evalExpr (Add [ Var type (Bit d) subOp2 ; Var type (Bit d) subOp1 ]) in
      let extOp2 := evalExpr (ZeroExtend d (Var type (Bit d) op2)) in
      let out    := evalLetExpr (@mulMultiStep input_width type input_width op1 extOp2 0%Zmod) in
      let uProd  := out @% "mulAcc" in
      let uHi    := evalExpr (TruncMsb d d (Var type (Bit (d + d)) uProd)) in
      let uLo    := evalExpr (TruncLsb d d (Var type (Bit (d + d)) uProd)) in
      let sHi    := evalExpr (Sub (Var type (Bit d) uHi) (Var type (Bit d) hiCorr)) in
      evalExpr (Concat (Var type (Bit d) sHi) (Var type (Bit d) uLo)) =
      evalLetExpr (SpecMul op1Signed op2Signed op1 op2).
  Proof.
    intros op1Signed op2Signed op1 op2 op1Neg op2Neg neg1 neg2 subOp2 subOp1 hiCorr extOp2 out uProd uHi uLo sHi.
    pose proof d_pos as Hd.
    pose proof d_add_d_pos as Hdd.
    assert (H_pow2D : 2 ^ (d + d) = 2 ^ d * 2 ^ d) by (apply Z.pow_add_r; lia).
    pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)) as HP.
    pose proof (bits.unsigned_range op1 ltac:(lia)) as Hop1.
    pose proof (bits.unsigned_range op2 ltac:(lia)) as Hop2.
    assert (HuProd : Zmod.unsigned uProd = Zmod.unsigned op1 * Zmod.unsigned op2)
      by exact (unsigned_mulMultiStep_at_width op1 op2).
    apply Zmod.unsigned_inj.
    (* Left-hand side: Concat sHi uLo *)
    cbn [evalExpr]; rewrite unsigned_app_arith by lia.
    pose proof (bits.unsigned_range uLo ltac:(lia)) as HuLo_r.
    pose proof (bits.unsigned_range sHi ltac:(lia)) as HsHi_r.
    rewrite <- (Z.mod_small (Zmod.unsigned uLo + Zmod.unsigned sHi * 2 ^ d) (2 ^ d * 2 ^ d)) by nia.
    unfold sHi; rewrite (evalExpr_Sub_unsigned d uHi hiCorr Hd).
    rewrite mod_mul_pow2_add by lia.
    unfold hiCorr; cbn [evalExpr fold_left map]; rewrite Zmod.add_0_l, Zmod.unsigned_add.
    replace (Zmod.unsigned uLo + (Zmod.unsigned uHi - (Zmod.unsigned subOp2 + Zmod.unsigned subOp1) mod 2 ^ d) * 2 ^ d)
       with ((Zmod.unsigned uLo + Zmod.unsigned uHi * 2 ^ d) + (- ((Zmod.unsigned subOp2 + Zmod.unsigned subOp1) mod 2 ^ d)) * 2 ^ d) by ring.
    replace (- ((Zmod.unsigned subOp2 + Zmod.unsigned subOp1) mod 2 ^ d))
       with (- (Zmod.unsigned subOp2 + Zmod.unsigned subOp1) + ((Zmod.unsigned subOp2 + Zmod.unsigned subOp1) / 2 ^ d) * 2 ^ d)
      by (pose proof (Z.div_mod (Zmod.unsigned subOp2 + Zmod.unsigned subOp1) (2 ^ d) ltac:(lia)); lia).
    replace ((Zmod.unsigned uLo + Zmod.unsigned uHi * 2 ^ d) +
             (- (Zmod.unsigned subOp2 + Zmod.unsigned subOp1) + ((Zmod.unsigned subOp2 + Zmod.unsigned subOp1) / 2 ^ d) * 2 ^ d) * 2 ^ d)
       with (((Zmod.unsigned uLo + Zmod.unsigned uHi * 2 ^ d) - (Zmod.unsigned subOp2 + Zmod.unsigned subOp1) * 2 ^ d) +
             ((Zmod.unsigned subOp2 + Zmod.unsigned subOp1) / 2 ^ d) * (2 ^ d * 2 ^ d)) by ring.
    rewrite Z.mod_add by nia.
    assert (HuLo_Hi : Zmod.unsigned uLo + Zmod.unsigned uHi * 2 ^ d = Zmod.unsigned uProd).
    { unfold uLo, uHi; cbn [evalExpr].
      rewrite unsigned_firstn by lia.
      unfold Zmod_lastn; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by lia.
      replace (d + d - d) with d by lia.
      rewrite (Z.mod_small (Zmod.unsigned uProd / 2 ^ d) (2 ^ d)) by (rewrite HuProd; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; nia).
      pose proof (Z.div_mod (Zmod.unsigned uProd) (2 ^ d) ltac:(lia)); lia. }
    rewrite HuLo_Hi, HuProd.
    (* Right-hand side: PureMultiplyFull / SpecMul *)
    unfold PureMultiplyFull, SpecMul; cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.mul_1_l, Zmod.unsigned_mul.
    set (b1 := if neg1 then 1 else 0).
    set (b2 := if neg2 then 1 else 0).
    assert (Hsub2 : Zmod.unsigned subOp2 = b1 * Zmod.unsigned op2).
    { unfold subOp2, b1; destruct neg1; cbn [evalExpr ITE0]; [lia | rewrite Zmod.unsigned_0; lia]. }
    assert (Hsub1 : Zmod.unsigned subOp1 = b2 * Zmod.unsigned op1).
    { unfold subOp1, b2; destruct neg2; cbn [evalExpr ITE0]; [lia | rewrite Zmod.unsigned_0; lia]. }
    rewrite Hsub2, Hsub1.
    assert (Hext1 :
      Zmod.unsigned (evalExpr (ITE (Var type Bool op1Signed)
                                   (SignExtend d (Var type (Bit d) op1))
                                   (ZeroExtend d (Var type (Bit d) op1)))) =
      Zmod.unsigned op1 + b1 * (2 ^ d - 1) * 2 ^ d).
    { unfold b1, neg1, op1Neg.
      cbn [evalExpr SignExtend ZeroExtend evalNot evalAndBinary evalBinary fold_left map KindCustomInd InvDefault].
      destruct op1Signed, (evalExpr (msbIsZero (Var type (Bit d) op1)));
        cbn [andb negb evalExpr ITE0]; rewrite unsigned_app_arith by lia.
      - rewrite Zmod.unsigned_0; lia.
      - change (InvDefault (Bit d)) with (Zmod.of_Z (2 ^ d) (-1)).
        rewrite Zmod.unsigned_of_Z, (neg1_mod_pow2 d Hd); lia.
      - rewrite Zmod.unsigned_0; lia.
      - rewrite Zmod.unsigned_0; lia. }
    assert (Hext2 :
      Zmod.unsigned (evalExpr (ITE (Var type Bool op2Signed)
                                   (SignExtend d (Var type (Bit d) op2))
                                   (ZeroExtend d (Var type (Bit d) op2)))) =
      Zmod.unsigned op2 + b2 * (2 ^ d - 1) * 2 ^ d).
    { unfold b2, neg2, op2Neg.
      cbn [evalExpr SignExtend ZeroExtend evalNot evalAndBinary evalBinary fold_left map KindCustomInd InvDefault].
      destruct op2Signed, (evalExpr (msbIsZero (Var type (Bit d) op2)));
        cbn [andb negb evalExpr ITE0]; rewrite unsigned_app_arith by lia.
      - rewrite Zmod.unsigned_0; lia.
      - change (InvDefault (Bit d)) with (Zmod.of_Z (2 ^ d) (-1)).
        rewrite Zmod.unsigned_of_Z, (neg1_mod_pow2 d Hd); lia.
      - rewrite Zmod.unsigned_0; lia.
      - rewrite Zmod.unsigned_0; lia. }
    cbn [evalExpr] in Hext1, Hext2.
    rewrite Hext1, Hext2, H_pow2D.
    replace ((Zmod.unsigned op1 + b1 * (2 ^ d - 1) * 2 ^ d) *
             (Zmod.unsigned op2 + b2 * (2 ^ d - 1) * 2 ^ d))
       with ((Zmod.unsigned op1 * Zmod.unsigned op2 - (b1 * Zmod.unsigned op2 + b2 * Zmod.unsigned op1) * 2 ^ d) +
             (b1 * Zmod.unsigned op2 + b2 * Zmod.unsigned op1 + b1 * b2 * (2 ^ d - 1) * (2 ^ d - 1)) * (2 ^ d * 2 ^ d)) by ring.
    rewrite Z.mod_add by nia.
    reflexivity.
  Qed.

  Theorem divMultiStep_at_width :
    forall (mag1 mag2 : bits d),
      let out := evalLetExpr (@divMultiStep input_width type input_width mag1 mag2 0%Zmod 0%Zmod) in
      out @% "quot" = evalExpr (Div (Var type (Bit d) mag1) (Var type (Bit d) mag2)) /\
      out @% "rem"  = evalExpr (Rem (Var type (Bit d) mag1) (Var type (Bit d) mag2)).
  Proof.
    intros mag1 mag2 out.
    pose proof d_pos as Hd.
    pose proof (divMultiStep_loop_invariant input_width mag1 mag2 (Nat.le_refl _))
      as [_ [Hdiv_pos Hdiv_zero]].
    fold out in Hdiv_pos, Hdiv_zero.
    change (Z.of_nat input_width) with d in Hdiv_pos, Hdiv_zero.
    replace (d - d) with 0 in Hdiv_pos, Hdiv_zero by lia.
    change (2 ^ 0) with 1 in Hdiv_pos, Hdiv_zero.
    rewrite !Z.div_1_r in Hdiv_pos, Hdiv_zero.
    pose proof (bits.unsigned_range mag1 ltac:(lia)) as Hmag1_range.
    pose proof (bits.unsigned_range mag2 ltac:(lia)) as Hmag2_range.
    split.
    - cbn [evalExpr].
      destruct (Z.eq_dec (Zmod.unsigned mag2) 0) as [Hz | Hnz].
      + assert (Hmag2_0 : mag2 = 0%Zmod) by (apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; exact Hz).
        rewrite Hmag2_0, Zmod.udiv_0_r.
        apply Zmod.unsigned_inj.
        specialize (Hdiv_zero Hz) as [_ Hq0].
        rewrite Hq0.
        unfold Zmod.opp, Zmod.one.
        rewrite Zmod.unsigned_sub, Zmod.unsigned_0, Zmod.unsigned_of_Z.
        assert (2 <= 2 ^ d) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
        rewrite (Z.mod_small 1 (2 ^ d)) by lia.
        replace (0 - 1) with (-1) by lia.
        rewrite (neg1_mod_pow2 d Hd); reflexivity.
      + apply Zmod.unsigned_inj.
        rewrite Zmod.unsigned_udiv_nonneg by lia.
        assert (Hpos : 0 < Zmod.unsigned mag2) by lia.
        specialize (Hdiv_pos Hpos) as [Hqr [Hr_lt Hq_lt]].
        pose proof (bits.unsigned_range (out @% "quot") ltac:(lia)) as Hq_range.
        pose proof (bits.unsigned_range (out @% "rem") ltac:(lia)) as Hr_range.
        eapply Z.div_unique with (r := Zmod.unsigned (out @% "rem")); [left; lia | lia].
    - cbn [evalExpr].
      destruct (Z.eq_dec (Zmod.unsigned mag2) 0) as [Hz | Hnz].
      + assert (Hmag2_0 : mag2 = 0%Zmod) by (apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; exact Hz).
        rewrite Hmag2_0, Zmod.umod_0_r.
        apply Zmod.unsigned_inj.
        specialize (Hdiv_zero Hz) as [Hr0 _]; exact Hr0.
      + apply Zmod.unsigned_inj.
        rewrite Zmod.unsigned_umod.
        assert (Hpos : 0 < Zmod.unsigned mag2) by lia.
        specialize (Hdiv_pos Hpos) as [Hqr [Hr_lt Hq_lt]].
        pose proof (bits.unsigned_range (out @% "quot") ltac:(lia)) as Hq_range.
        pose proof (bits.unsigned_range (out @% "rem") ltac:(lia)) as Hr_range.
        eapply Z.mod_unique with (q := Zmod.unsigned (out @% "quot")); [left; lia | lia].
  Qed.

  (* --- 1D. Multi-Stage Composition for `mulStageStep` and `divStageStep` --- *)

  Definition MulStageStateAt (kBits : nat) (inp : type (MulInput d)) : type (MulStageState d) :=
    let s0 := evalLetExpr (@mulInitStage input_width type inp) in
    let core := evalLetExpr (@mulMultiStep input_width type kBits
                              (s0 @% "shiftOp") (s0 @% "extOp2") (s0 @% "mulAcc")) in
    evalExpr ((Const type (MulStageState d) s0)
      `{ "shiftOp" <- Const type (Bit d)       (core @% "shiftOp") }
      `{ "mulAcc"   <- Const type (Bit (d + d)) (core @% "mulAcc") }).

  Lemma MulStageStateAt_0 : forall inp,
    MulStageStateAt 0 inp = evalLetExpr (@mulInitStage input_width type inp).
  Proof.
    intros inp; unfold MulStageStateAt.
    set (s0 := evalLetExpr (@mulInitStage input_width type inp)).
    destruct s0 as [f1 [f2 [f3 [f4 [f5 []]]]]]; reflexivity.
  Qed.

  Lemma MulStageStateAt_step : forall kBits bps inp,
    evalLetExpr (@mulStageStep input_width type bps (MulStageStateAt kBits inp)) =
    MulStageStateAt (kBits + bps)%nat inp.
  Proof.
    intros kBits bps inp; unfold MulStageStateAt.
    set (s0 := evalLetExpr (@mulInitStage input_width type inp)).
    rewrite (mulMultiStep_add kBits bps).
    destruct s0 as [f1 [f2 [f3 [f4 [f5 []]]]]]; reflexivity.
  Qed.

  Lemma evalLetExpr_mulInitStage : forall (inp : type (MulInput d)),
    let isHigh    := inp @% "isHigh" in
    let op1Signed := inp @% "op1Signed" in
    let op2Signed := inp @% "op2Signed" in
    let op1       := inp @% "op1" in
    let op2       := inp @% "op2" in
    let op1Neg    := evalExpr (Not (msbIsZero (Var type (Bit d) op1))) in
    let op2Neg    := evalExpr (Not (msbIsZero (Var type (Bit d) op2))) in
    let neg1      := evalExpr (And [ Var type Bool op1Signed ; Var type Bool op1Neg ]) in
    let neg2      := evalExpr (And [ Var type Bool op2Signed ; Var type Bool op2Neg ]) in
    let subOp2    := evalExpr (ITE (Var type Bool neg1) (Var type (Bit d) op2) $0) in
    let subOp1    := evalExpr (ITE (Var type Bool neg2) (Var type (Bit d) op1) $0) in
    let hiCorr    := evalExpr (Add [ Var type (Bit d) subOp2 ; Var type (Bit d) subOp1 ]) in
    let extOp2    := evalExpr (ZeroExtend d (Var type (Bit d) op2)) in
    evalLetExpr (@mulInitStage input_width type inp) =
    (isHigh ,, (hiCorr ,, (op1 ,, (extOp2 ,, (0%Zmod ,, tt))))).
  Proof.
    intros inp; reflexivity.
  Qed.

  Lemma evalLetExpr_PureMulOut : forall (inp : type (MulInput d)),
    let isHigh    := inp @% "isHigh" in
    let op1Signed := inp @% "op1Signed" in
    let op2Signed := inp @% "op2Signed" in
    let op1       := inp @% "op1" in
    let op2       := inp @% "op2" in
    let fullProd  := evalLetExpr (@SpecMul d type op1Signed op2Signed op1 op2) in
    let res       := evalExpr (ITE (Var type Bool isHigh)
                                   (TruncMsb d d (Var type (Bit (d + d)) fullProd))
                                   (TruncLsb d d (Var type (Bit (d + d)) fullProd))) in
    evalLetExpr (@PureMulOut d type inp) = (fullProd ,, (res ,, tt)).
  Proof.
    intros inp; reflexivity.
  Qed.

  Local Opaque SpecMul.

  Theorem MulFinish_PureMulOut_correct : forall inp,
    evalLetExpr (@mulFinishStage input_width type (MulStageStateAt input_width inp)) =
    evalLetExpr (@PureMulOut d type inp).
  Proof.
    intros inp.
    pose proof d_pos as Hd.
    rewrite evalLetExpr_PureMulOut.
    unfold MulStageStateAt.
    rewrite evalLetExpr_mulInitStage.
    pose proof (mulApproach3_fullProd_eq (inp @% "op1Signed") (inp @% "op2Signed") (inp @% "op1") (inp @% "op2")) as Hprod.
    cbv zeta in Hprod.
    cbn [evalExpr] in Hprod.
    unfold mulFinishStage.
    cbn [evalLetExpr].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple
         updDiffTuple finNum Fst Snd mapDiffTuple] in *.
    cbn [evalExpr Fst Snd snd mapDiffTuple] in *.
    rewrite <- Hprod.
    rewrite firstn_app_exact by lia.
    rewrite lastn_app_exact by lia.
    reflexivity.
  Qed.

  Definition DivStageStateAt (kBits : nat) (inp : type (DivInput d)) : type (DivStageState d) :=
    let s0 := evalLetExpr (@divInitStage input_width type inp) in
    let core := evalLetExpr (@divMultiStep input_width type kBits
                              (s0 @% "shiftOp") (s0 @% "mag2") (s0 @% "rem") (s0 @% "quot")) in
    evalExpr ((Const type (DivStageState d) s0)
      `{ "shiftOp" <- Const type (Bit d) (core @% "shiftOp") }
      `{ "rem"       <- Const type (Bit d) (core @% "rem") }
      `{ "quot"      <- Const type (Bit d) (core @% "quot") }).

  Lemma DivStageStateAt_0 : forall inp,
    DivStageStateAt 0 inp = evalLetExpr (@divInitStage input_width type inp).
  Proof.
    intros inp; unfold DivStageStateAt.
    set (s0 := evalLetExpr (@divInitStage input_width type inp)).
    destruct s0 as [f1 [f2 [f3 [f4 [f5 [f6 [f7 []]]]]]]]; reflexivity.
  Qed.

  Lemma DivStageStateAt_step : forall kBits bps inp,
    evalLetExpr (@divStageStep input_width type bps (DivStageStateAt kBits inp)) =
    DivStageStateAt (kBits + bps)%nat inp.
  Proof.
    intros kBits bps inp; unfold DivStageStateAt.
    set (s0 := evalLetExpr (@divInitStage input_width type inp)).
    rewrite (divMultiStep_add kBits bps).
    destruct s0 as [f1 [f2 [f3 [f4 [f5 [f6 [f7 []]]]]]]]; reflexivity.
  Qed.

  Lemma evalLetExpr_divInitStage : forall (inp : type (DivInput d)),
    let isUnsigned := inp @% "isUnsigned" in
    let isRem := inp @% "isRem" in
    let op1 := inp @% "op1" in
    let op2 := inp @% "op2" in
    let op1Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op1))) in
    let op2Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op2))) in
    let op2Zero := evalExpr (isZero (Var type (Bit d) op2)) in
    let remNeg := evalExpr (And [ Not (Var type Bool isUnsigned) ; Var type Bool op1Neg ]) in
    let mag1 := evalExpr (ITE (Var type Bool remNeg)
                              (Neg (Var type (Bit d) op1)) (Var type (Bit d) op1)) in
    let mag2 := evalExpr (ITE (And [ Not (Var type Bool isUnsigned) ; Var type Bool op2Neg ])
                              (Neg (Var type (Bit d) op2)) (Var type (Bit d) op2)) in
    let quotNeg := evalExpr (And [ Not (Var type Bool isUnsigned) ;
                                   Not (Var type Bool op2Zero) ;
                                   Xor [ Var type Bool op1Neg ; Var type Bool op2Neg ] ]) in
    evalLetExpr (@divInitStage input_width type inp) =
    (isRem ,, (quotNeg ,, (remNeg ,, (mag1 ,, (mag2 ,, (0%Zmod ,, (0%Zmod ,, tt))))))).
  Proof.
    intros inp; reflexivity.
  Qed.

  Theorem DivFinish_PureDivOut_correct : forall inp,
    evalLetExpr (@divFinishStage input_width type (DivStageStateAt input_width inp)) =
    evalLetExpr (@PureDivOut d type inp).
  Proof.
    intros inp.
    pose proof d_pos as Hd.
    unfold DivStageStateAt.
    rewrite evalLetExpr_divInitStage.
    set (isUnsigned := inp @% "isUnsigned").
    set (isRem := inp @% "isRem").
    set (op1 := inp @% "op1").
    set (op2 := inp @% "op2").
    set (op1Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op1)))).
    set (op2Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op2)))).
    set (op2Zero := evalExpr (isZero (Var type (Bit d) op2))).
    set (remNeg := evalExpr (And [ Not (Var type Bool isUnsigned) ; Var type Bool op1Neg ])).
    set (mag1 := evalExpr (ITE (Var type Bool remNeg)
                               (Neg (Var type (Bit d) op1)) (Var type (Bit d) op1))).
    set (mag2 := evalExpr (ITE (And [ Not (Var type Bool isUnsigned) ; Var type Bool op2Neg ])
                               (Neg (Var type (Bit d) op2)) (Var type (Bit d) op2))).
    pose proof (divMultiStep_at_width mag1 mag2) as [Hquot Hrem].
    unfold divFinishStage, PureDivOut, PureDivide, SpecDiv.
    cbn [evalLetExpr].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple
         updDiffTuple finNum Fst Snd mapDiffTuple] in *.
    fold isUnsigned isRem op1 op2 op1Neg op2Neg op2Zero remNeg mag1 mag2.
    rewrite Hquot, Hrem.
    cbn [evalExpr Fst Snd snd mapDiffTuple].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple
         updDiffTuple finNum Fst Snd mapDiffTuple].
    fold isUnsigned isRem op1 op2 op1Neg op2Neg op2Zero remNeg mag1 mag2.
    f_equal.
    f_equal.
    f_equal.
    { unfold mag1, mag2, remNeg, op1Neg, op2Neg, op2Zero.
      destruct isUnsigned, (evalExpr (msbIsZero (Var type (Bit d) op1))),
               (evalExpr (msbIsZero (Var type (Bit d) op2)));
        cbn [andb negb xorb evalExpr ITE0 fold_left map evalAndBinary evalXorBinary evalNot evalBinary KindCustomInd InvDefault getDefault];
        rewrite ?Bool.andb_false_r;
        reflexivity. }
    f_equal.
    f_equal.
    destruct op2Zero eqn:Hz.
    - assert (Hop2_0 : op2 = 0%Zmod).
      { subst op2Zero; cbn [evalExpr isZero isEq KindCustomInd getDefault] in Hz.
        destruct (Zmod.eqb_spec op2 0%Zmod); [assumption | discriminate]. }
      assert (Hmag2_0 : mag2 = 0%Zmod).
      { unfold mag2; rewrite Hop2_0; cbn [evalExpr ITE0].
        destruct isUnsigned, op2Neg;
          cbn [andb negb xorb evalExpr fold_left map evalAndBinary evalNot evalBinary KindCustomInd InvDefault];
          try apply (evalExpr_Neg_zero Hd); reflexivity. }
      assert (Hm1 : ((- (1))%Zmod : bits d) = InvDefault (Bit d)).
      { apply Zmod.unsigned_inj; unfold Zmod.opp, Zmod.one.
        change (InvDefault (Bit d)) with (Zmod.of_Z (2 ^ d) (-1)).
        rewrite Zmod.unsigned_sub, Zmod.unsigned_0, !Zmod.unsigned_of_Z.
        assert (2 <= 2 ^ d) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
        rewrite (Z.mod_small 1 (2 ^ d)) by lia; reflexivity. }
      rewrite Hmag2_0, Zmod.udiv_0_r, Zmod.umod_0_r, Hm1.
      unfold mag1, remNeg.
      destruct isUnsigned, op1Neg, op2Neg, isRem;
        cbn [andb negb xorb evalExpr ITE0 fold_left map evalAndBinary evalXorBinary evalNot evalBinary KindCustomInd InvDefault getDefault];
        try apply (evalExpr_Neg_involutive op1 Hd); reflexivity.
    - unfold mag1, mag2; unfold remNeg; unfold op1Neg, op2Neg; cbn [evalExpr].
      destruct isUnsigned, (evalExpr (msbIsZero (Var type (Bit d) op1))),
               (evalExpr (msbIsZero (Var type (Bit d) op2))), isRem; reflexivity.
  Qed.

  (* --- 1E. Shared-Accumulator Iterative Engine (`SharedStageStateAt`) --- *)

  Definition projSharedMulInp (inp : type (SharedInput d)) : type (MulInput d) :=
    evalExpr (STRUCT {
      "isHigh"    ::= Const type Bool    (inp @% "isHigh") ;
      "op1Signed" ::= Const type Bool    (inp @% "op1Signed") ;
      "op2Signed" ::= Const type Bool    (inp @% "op2Signed") ;
      "op1"       ::= Const type (Bit d) (inp @% "op1") ;
      "op2"       ::= Const type (Bit d) (inp @% "op2")
    }).

  Definition projSharedDivInp (inp : type (SharedInput d)) : type (DivInput d) :=
    evalExpr (STRUCT {
      "isUnsigned" ::= Const type Bool    (inp @% "isUnsigned") ;
      "isRem"      ::= Const type Bool    (inp @% "isRem") ;
      "op1"        ::= Const type (Bit d) (inp @% "op1") ;
      "op2"        ::= Const type (Bit d) (inp @% "op2")
    }).

  Definition SharedStageStateAt (kSteps mul_bps div_bps : nat) (inp : type (SharedInput d)) :
    type (SharedStageState d) :=
    let s0 := evalLetExpr (@sharedInitStage input_width type inp) in
    if inp @% "isMul" then
      let ms := MulStageStateAt (kSteps * mul_bps)%nat (projSharedMulInp inp) in
      evalExpr ((Const type (SharedStageState d) s0)
        `{ "acc"     <- Const type (Bit (d + d)) (ms @% "mulAcc") }
        `{ "shiftOp" <- Const type (Bit d)       (ms @% "shiftOp") })
    else
      let ds := DivStageStateAt (kSteps * div_bps)%nat (projSharedDivInp inp) in
      evalExpr ((Const type (SharedStageState d) s0)
        `{ "acc"     <- Concat (Const type (Bit d) (ds @% "rem")) (Const type (Bit d) (ds @% "quot")) }
        `{ "shiftOp" <- Const type (Bit d) (ds @% "shiftOp") }).

  Lemma app_0_0 : Zmod.app (0%Zmod : bits d) (0%Zmod : bits d) = (0%Zmod : bits (d + d)).
  Proof.
    pose proof d_pos as Hd.
    apply Zmod.unsigned_inj.
    rewrite unsigned_app_arith by lia.
    rewrite !Zmod.unsigned_0; lia.
  Qed.

  Lemma evalLetExpr_mulInitStage_tuple :
    forall (isHigh op1Signed op2Signed : bool) (op1 op2 : bits d),
      let op1Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op1))) in
      let op2Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op2))) in
      let mulNeg1 := evalExpr (And [ Var type Bool op1Signed ; Var type Bool op1Neg ]) in
      let mulNeg2 := evalExpr (And [ Var type Bool op2Signed ; Var type Bool op2Neg ]) in
      let subOp2 := evalExpr (ITE (Var type Bool mulNeg1) (Var type (Bit d) op2) $0) in
      let subOp1 := evalExpr (ITE (Var type Bool mulNeg2) (Var type (Bit d) op1) $0) in
      let hiCorr := evalExpr (Add [ Var type (Bit d) subOp2 ; Var type (Bit d) subOp1 ]) in
      let extOp2 := evalExpr (ZeroExtend d (Var type (Bit d) op2)) in
      evalLetExpr (@mulInitStage input_width type ((isHigh ,, (op1Signed ,, (op2Signed ,, (op1 ,, (op2 ,, tt))))) : type (MulInput d))) =
      (isHigh ,, (hiCorr ,, (op1 ,, (extOp2 ,, (0%Zmod ,, tt))))).
  Proof. intros; reflexivity. Qed.

  Lemma evalLetExpr_divInitStage_tuple :
    forall (isUnsigned isRem : bool) (op1 op2 : bits d),
      let op1Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op1))) in
      let op2Neg := evalExpr (Not (msbIsZero (Var type (Bit d) op2))) in
      let remNeg := evalExpr (And [ Not (Var type Bool isUnsigned) ; Var type Bool op1Neg ]) in
      let mag1 := evalExpr (ITE (Var type Bool remNeg)
                                (Neg (Var type (Bit d) op1)) (Var type (Bit d) op1)) in
      let mag2 := evalExpr (ITE (And [ Not (Var type Bool isUnsigned) ; Var type Bool op2Neg ])
                                (Neg (Var type (Bit d) op2)) (Var type (Bit d) op2)) in
      let quotNeg := evalExpr (And [ Not (Var type Bool isUnsigned) ;
                                     Not (isZero (Var type (Bit d) op2)) ;
                                     Xor [ Var type Bool op1Neg ; Var type Bool op2Neg ] ]) in
      evalLetExpr (@divInitStage input_width type ((isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))) : type (DivInput d))) =
      (isRem ,, (quotNeg ,, (remNeg ,, (mag1 ,, (mag2 ,, (0%Zmod ,, (0%Zmod ,, tt))))))).
  Proof. intros; reflexivity. Qed.

  Lemma evalLetExpr_sharedInitStage_tuple :
    forall (isMul isHigh op1Signed op2Signed isUnsigned isRem : bool) (op1 op2 : bits d),
      let op1Neg      := evalExpr (Not (msbIsZero (Var type (Bit d) op1))) in
      let op2Neg      := evalExpr (Not (msbIsZero (Var type (Bit d) op2))) in
      let mulNeg1     := evalExpr (And [ Var type Bool op1Signed ; Var type Bool op1Neg ]) in
      let mulNeg2     := evalExpr (And [ Var type Bool op2Signed ; Var type Bool op2Neg ]) in
      let subOp2      := evalExpr (ITE (Var type Bool mulNeg1) (Var type (Bit d) op2) $0) in
      let subOp1      := evalExpr (ITE (Var type Bool mulNeg2) (Var type (Bit d) op1) $0) in
      let hiCorr      := evalExpr (Add [ Var type (Bit d) subOp2 ; Var type (Bit d) subOp1 ]) in
      let remNeg      := evalExpr (And [ Not (Var type Bool isUnsigned) ; Var type Bool op1Neg ]) in
      let mag1        := evalExpr (ITE (Var type Bool remNeg)
                                       (Neg (Var type (Bit d) op1)) (Var type (Bit d) op1)) in
      let mag2        := evalExpr (ITE (And [ Not (Var type Bool isUnsigned) ; Var type Bool op2Neg ])
                                       (Neg (Var type (Bit d) op2)) (Var type (Bit d) op2)) in
      let quotNeg     := evalExpr (And [ Not (Var type Bool isUnsigned) ;
                                         Not (isZero (Var type (Bit d) op2)) ;
                                         Xor [ Var type Bool op1Neg ; Var type Bool op2Neg ] ]) in
      let isHighOrRem := if isMul then isHigh else isRem in
      let initShiftOp := if isMul then op1 else mag1 in
      let initExtOp2  := evalExpr (ZeroExtend d (Var type (Bit d) (if isMul then op2 else mag2))) in
      evalLetExpr (@sharedInitStage input_width type
        ((isMul ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d))) =
      (isMul ,, (isHighOrRem ,, (quotNeg ,, (remNeg ,, (hiCorr ,, (initShiftOp ,, (initExtOp2 ,, (0%Zmod ,, tt)))))))).
  Proof. intros; reflexivity. Qed.

  Local Ltac fold_shared_inits op1 op2 op1Signed op2Signed isUnsigned :=
    set (op1Neg     := evalExpr (Not (msbIsZero (Var type (Bit d) op1)))) in *;
    set (op2Neg     := evalExpr (Not (msbIsZero (Var type (Bit d) op2)))) in *;
    set (mulNeg1    := evalExpr (And [ Var type Bool op1Signed ; Var type Bool op1Neg ])) in *;
    set (mulNeg2    := evalExpr (And [ Var type Bool op2Signed ; Var type Bool op2Neg ])) in *;
    set (subOp2     := evalExpr (ITE (Var type Bool mulNeg1) (Var type (Bit d) op2) $0)) in *;
    set (subOp1     := evalExpr (ITE (Var type Bool mulNeg2) (Var type (Bit d) op1) $0)) in *;
    set (hiCorr     := evalExpr (Add [ Var type (Bit d) subOp2 ; Var type (Bit d) subOp1 ])) in *;
    set (remNeg     := evalExpr (And [ Not (Var type Bool isUnsigned) ; Var type Bool op1Neg ])) in *;
    set (mag1       := evalExpr (ITE (Var type Bool remNeg)
                                     (Neg (Var type (Bit d) op1)) (Var type (Bit d) op1))) in *;
    set (mag2       := evalExpr (ITE (And [ Not (Var type Bool isUnsigned) ; Var type Bool op2Neg ])
                                     (Neg (Var type (Bit d) op2)) (Var type (Bit d) op2))) in *;
    set (quotNeg    := evalExpr (And [ Not (Var type Bool isUnsigned) ;
                                       Not (isZero (Var type (Bit d) op2)) ;
                                       Xor [ Var type Bool op1Neg ; Var type Bool op2Neg ] ])) in *;
    try set (mCore  := evalLetExpr (@mulMultiStep input_width type _ _ _ _)) in *;
    try set (dCore  := evalLetExpr (@divMultiStep input_width type _ _ _ _ _)) in *.

  Local Ltac simp_goal_struct :=
    cbn [ZeroExtend evalExpr Fst Snd snd mapDiffTuple];
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple
         updDiffTuple finNum Fst Snd mapDiffTuple];
    cbn [ZeroExtend evalExpr Fst Snd snd mapDiffTuple];
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple
         updDiffTuple finNum Fst Snd mapDiffTuple].

  Lemma projSharedMulInp_tuple : forall isMul isHigh op1Signed op2Signed isUnsigned isRem op1 op2,
    projSharedMulInp ((isMul ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d)) =
    ((isHigh ,, (op1Signed ,, (op2Signed ,, (op1 ,, (op2 ,, tt))))) : type (MulInput d)).
  Proof. intros; reflexivity. Qed.

  Lemma projSharedDivInp_tuple : forall isMul isHigh op1Signed op2Signed isUnsigned isRem op1 op2,
    projSharedDivInp ((isMul ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d)) =
    ((isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))) : type (DivInput d)).
  Proof. intros; reflexivity. Qed.

  Lemma eta_MulStageState : forall (ms : type (MulStageState d)),
    ((ms @% "isHigh" ,, (ms @% "hiCorr" ,, (ms @% "shiftOp" ,, (ms @% "extOp2" ,, (ms @% "mulAcc" ,, tt)))))
      : type (MulStageState d)) = ms.
  Proof.
    intros [f1 [f2 [f3 [f4 [f5 []]]]]]; reflexivity.
  Qed.

  Lemma eta_DivStageState : forall (ds : type (DivStageState d)),
    ((ds @% "isRem" ,, (ds @% "quotNeg" ,, (ds @% "remNeg" ,,
      (ds @% "shiftOp" ,, (ds @% "mag2" ,, (ds @% "rem" ,, (ds @% "quot" ,, tt)))))))
      : type (DivStageState d)) = ds.
  Proof.
    intros [f1 [f2 [f3 [f4 [f5 [f6 [f7 []]]]]]]]; reflexivity.
  Qed.

  Local Opaque PureMultiply PureDivide SpecMul SpecDiv mulMultiStep divMultiStep.

  Lemma SharedStageStateAt_mul_eq :
    forall kSteps mul_bps div_bps isHigh op1Signed op2Signed isUnsigned isRem (op1 op2 : bits d),
      let inp := ((true ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d)) in
      let s0  := evalLetExpr (@sharedInitStage input_width type inp) in
      let ms  := MulStageStateAt (kSteps * mul_bps)%nat (projSharedMulInp inp) in
      SharedStageStateAt kSteps mul_bps div_bps inp =
      ((true ,, (ms @% "isHigh" ,, (s0 @% "quotNeg" ,, (s0 @% "remNeg" ,,
        (ms @% "hiCorr" ,, (ms @% "shiftOp" ,, (ms @% "extOp2" ,, (ms @% "mulAcc" ,, tt)))))))) : type (SharedStageState d)).
  Proof.
    intros kSteps mul_bps div_bps isHigh op1Signed op2Signed isUnsigned isRem op1 op2 inp s0 ms.
    unfold SharedStageStateAt, ms, MulStageStateAt, s0, inp.
    rewrite projSharedMulInp_tuple.
    rewrite evalLetExpr_sharedInitStage_tuple, evalLetExpr_mulInitStage_tuple.
    fold_shared_inits op1 op2 op1Signed op2Signed isUnsigned.
    reflexivity.
  Qed.

  Lemma SharedStageStateAt_div_eq :
    forall kSteps mul_bps div_bps isHigh op1Signed op2Signed isUnsigned isRem (op1 op2 : bits d),
      let inp := ((false ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d)) in
      let s0  := evalLetExpr (@sharedInitStage input_width type inp) in
      let ds  := DivStageStateAt (kSteps * div_bps)%nat (projSharedDivInp inp) in
      SharedStageStateAt kSteps mul_bps div_bps inp =
      ((false ,, (ds @% "isRem" ,, (ds @% "quotNeg" ,, (ds @% "remNeg" ,,
        (s0 @% "hiCorr" ,, (ds @% "shiftOp" ,, (evalExpr (ZeroExtend d (Var type (Bit d) (ds @% "mag2"))) ,,
          (Zmod.app (ds @% "quot") (ds @% "rem") ,, tt)))))))) : type (SharedStageState d)).
  Proof.
    intros kSteps mul_bps div_bps isHigh op1Signed op2Signed isUnsigned isRem op1 op2 inp s0 ds.
    unfold SharedStageStateAt, ds, DivStageStateAt, s0, inp.
    rewrite projSharedDivInp_tuple.
    rewrite evalLetExpr_sharedInitStage_tuple, evalLetExpr_divInitStage_tuple.
    fold_shared_inits op1 op2 op1Signed op2Signed isUnsigned.
    reflexivity.
  Qed.

  Lemma sharedStageStep_mul_eq :
    forall mul_bps div_bps (quotNeg remNeg : bool) (ms : type (MulStageState d)),
      let nms := evalLetExpr (@mulStageStep input_width type mul_bps ms) in
      evalLetExpr (@sharedStageStep input_width type mul_bps div_bps
        ((true ,, (ms @% "isHigh" ,, (quotNeg ,, (remNeg ,,
          (ms @% "hiCorr" ,, (ms @% "shiftOp" ,, (ms @% "extOp2" ,, (ms @% "mulAcc" ,, tt)))))))) : type (SharedStageState d))) =
      ((true ,, (nms @% "isHigh" ,, (quotNeg ,, (remNeg ,,
        (nms @% "hiCorr" ,, (nms @% "shiftOp" ,, (nms @% "extOp2" ,, (nms @% "mulAcc" ,, tt)))))))) : type (SharedStageState d)).
  Proof.
    intros mul_bps div_bps quotNeg remNeg [f1 [f2 [f3 [f4 [f5 []]]]]]; reflexivity.
  Qed.

  Lemma sharedStageStep_div_eq :
    forall mul_bps div_bps (hiCorr : bits d) (ds : type (DivStageState d)),
      let nds := evalLetExpr (@divStageStep input_width type div_bps ds) in
      evalLetExpr (@sharedStageStep input_width type mul_bps div_bps
        ((false ,, (ds @% "isRem" ,, (ds @% "quotNeg" ,, (ds @% "remNeg" ,,
          (hiCorr ,, (ds @% "shiftOp" ,, (evalExpr (ZeroExtend d (Var type (Bit d) (ds @% "mag2"))) ,,
            (Zmod.app (ds @% "quot") (ds @% "rem") ,, tt)))))))) : type (SharedStageState d))) =
      ((false ,, (nds @% "isRem" ,, (nds @% "quotNeg" ,, (nds @% "remNeg" ,,
        (hiCorr ,, (nds @% "shiftOp" ,, (evalExpr (ZeroExtend d (Var type (Bit d) (nds @% "mag2"))) ,,
          (Zmod.app (nds @% "quot") (nds @% "rem") ,, tt)))))))) : type (SharedStageState d)).
  Proof.
    intros mul_bps div_bps hiCorr [f1 [f2 [f3 [f4 [f5 [f6 [f7 []]]]]]]] nds; subst nds.
    pose proof d_pos as Hd.
    unfold sharedStageStep, divStageStep; cbn [evalLetExpr].
    simp_goal_struct.
    rewrite !firstn_app_exact by lia.
    rewrite !lastn_app_exact by lia.
    reflexivity.
  Qed.

  Lemma sharedFinishStage_mul_eq :
    forall (quotNeg remNeg : bool) (ms : type (MulStageState d)),
      evalLetExpr (@sharedFinishStage input_width type
        ((true ,, (ms @% "isHigh" ,, (quotNeg ,, (remNeg ,,
          (ms @% "hiCorr" ,, (ms @% "shiftOp" ,, (ms @% "extOp2" ,, (ms @% "mulAcc" ,, tt)))))))) : type (SharedStageState d))) =
      (((evalLetExpr (@mulFinishStage input_width type ms)) @% "res") ,, tt).
  Proof.
    intros quotNeg remNeg [[|] [f2 [f3 [f4 [f5 []]]]]]; reflexivity.
  Qed.

  Lemma sharedFinishStage_div_eq :
    forall (hiCorr : bits d) (extOp2 : bits (d + d)) (ds : type (DivStageState d)),
      evalLetExpr (@sharedFinishStage input_width type
        ((false ,, (ds @% "isRem" ,, (ds @% "quotNeg" ,, (ds @% "remNeg" ,,
          (hiCorr ,, (ds @% "shiftOp" ,, (extOp2 ,,
            (Zmod.app (ds @% "quot") (ds @% "rem") ,, tt)))))))) : type (SharedStageState d))) =
      (((evalLetExpr (@divFinishStage input_width type ds)) @% "res") ,, tt).
  Proof.
    intros hiCorr extOp2 [f1 [f2 [f3 [f4 [f5 [f6 [f7 []]]]]]]];
      pose proof d_pos as Hd;
      unfold sharedFinishStage, divFinishStage; cbn [evalLetExpr];
      simp_goal_struct;
      rewrite ?firstn_app_exact by lia;
      rewrite ?lastn_app_exact by lia;
      reflexivity.
  Qed.

  Lemma SharedStageStateAt_0 : forall mul_bps div_bps inp,
    SharedStageStateAt 0 mul_bps div_bps inp = evalLetExpr (@sharedInitStage input_width type inp).
  Proof.
    intros mul_bps div_bps [[|] [isHigh [op1Signed [op2Signed [isUnsigned [isRem [op1 [op2 []]]]]]]]].
    - unfold SharedStageStateAt; change (0 * mul_bps)%nat with 0%nat; rewrite MulStageStateAt_0; reflexivity.
    - rewrite SharedStageStateAt_div_eq; change (0 * div_bps)%nat with 0%nat; rewrite DivStageStateAt_0.
      rewrite evalLetExpr_sharedInitStage_tuple, projSharedDivInp_tuple, evalLetExpr_divInitStage_tuple.
      fold_shared_inits op1 op2 op1Signed op2Signed isUnsigned.
      simp_goal_struct; rewrite app_0_0; reflexivity.
  Qed.

  Lemma SharedStageStateAt_step : forall kSteps mul_bps div_bps inp,
    evalLetExpr (@sharedStageStep input_width type mul_bps div_bps (SharedStageStateAt kSteps mul_bps div_bps inp)) =
    SharedStageStateAt (S kSteps) mul_bps div_bps inp.
  Proof.
    intros kSteps mul_bps div_bps [[|] [isHigh [op1Signed [op2Signed [isUnsigned [isRem [op1 [op2 []]]]]]]]].
    - rewrite (SharedStageStateAt_mul_eq kSteps), (SharedStageStateAt_mul_eq (S kSteps)).
      rewrite sharedStageStep_mul_eq, MulStageStateAt_step.
      replace (S kSteps * mul_bps)%nat with (kSteps * mul_bps + mul_bps)%nat by lia.
      reflexivity.
    - rewrite (SharedStageStateAt_div_eq kSteps), (SharedStageStateAt_div_eq (S kSteps)).
      rewrite sharedStageStep_div_eq, DivStageStateAt_step.
      replace (S kSteps * div_bps)%nat with (kSteps * div_bps + div_bps)%nat by lia.
      reflexivity.
  Qed.

  Theorem SharedFinish_PureSharedOut_correct :
    forall mul_stages div_stages mul_bps div_bps (inp : type (SharedInput d)),
      (mul_stages * mul_bps = input_width)%nat ->
      (div_stages * div_bps = input_width)%nat ->
      let targetSteps := if inp @% "isMul" then mul_stages else div_stages in
      evalLetExpr (@sharedFinishStage input_width type
                     (SharedStageStateAt targetSteps mul_bps div_bps inp)) =
      evalLetExpr (@PureSharedOut d type inp).
  Proof.
    intros mul_stages div_stages mul_bps div_bps
           [[|] [isHigh [op1Signed [op2Signed [isUnsigned [isRem [op1 [op2 []]]]]]]]]
           Hmul_w Hdiv_w targetSteps;
      unfold targetSteps; clear targetSteps.
    - change (if ((true ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d)) @% "isMul"
              then mul_stages else div_stages) with mul_stages.
      rewrite SharedStageStateAt_mul_eq, sharedFinishStage_mul_eq, Hmul_w, MulFinish_PureMulOut_correct.
      reflexivity.
    - change (if ((false ,, (isHigh ,, (op1Signed ,, (op2Signed ,, (isUnsigned ,, (isRem ,, (op1 ,, (op2 ,, tt)))))))) : type (SharedInput d)) @% "isMul"
              then mul_stages else div_stages) with div_stages.
      rewrite SharedStageStateAt_div_eq, sharedFinishStage_div_eq, Hdiv_w, DivFinish_PureDivOut_correct.
      reflexivity.
  Qed.

End ParameterizedStageArithmetic.

(* --- 1F. Equivalence of `PureDivide` with `SpecMulDiv.Divide` at `Xlen = 32` --- *)

Theorem PureDivide_eq_SpecDivide :
  forall (isUnsigned isRem : bool) (op1 op2 : bits Xlen),
    evalLetExpr (@PureDivide Xlen type isUnsigned isRem op1 op2) =
    evalLetExpr (@Divide type isUnsigned isRem op1 op2).
Proof.
  intros isUnsigned isRem op1 op2; reflexivity.
Qed.




(* ===========================================================================
 * PART 2: STAGE-VALUE BRIDGE LEMMAS (`StageValAt` -> `PureMulOut` / `PureDivOut` / `PureSharedOut`)
 * =========================================================================== *)

Lemma Zmod_or_0_l : forall w (x : bits w),
  Zmod.or Zmod.zero x = x.
Proof.
  intros w x; apply Zmod.unsigned_inj; rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l; reflexivity.
Qed.

Lemma evalOrBinary_MulStageState : forall d (x : type (MulStageState d)),
  evalOrBinary (getDefault (MulStageState d)) x = x.
Proof.
  intros d [isHigh [acc [shiftOp [op2 [hiCorr []]]]]];
    unfold evalOrBinary, evalBinary, getDefault; cbn.
  destruct isHigh; repeat rewrite Zmod_or_0_l; reflexivity.
Qed.

Lemma kindSize_MulStageState_nonneg : forall d,
  (0 <= d)%Z -> (0 <= kindSize (MulStageState d))%Z.
Proof.
  intros d Hd; cbn [MulStageState kindSize fst snd]; lia.
Qed.

Lemma firstn_app_gen : forall (w1 w2 : Z) (q : bits w1) (r : bits w2),
  0 <= w1 -> 0 <= w2 ->
  @Zmod.firstn w1 (w1 + w2) (Zmod.app q r) = q.
Proof.
  intros w1 w2 q r Hw1 Hw2.
  apply Zmod.unsigned_inj.
  rewrite unsigned_firstn by lia.
  rewrite unsigned_app_arith by lia.
  rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 w1 ltac:(lia) ltac:(lia)); lia).
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  apply Z.mod_small; lia.
Qed.

Lemma lastn_app_gen : forall (w1 w2 : Z) (q : bits w1) (r : bits w2),
  0 <= w1 -> 0 <= w2 ->
  Zmod_lastn w2 (Zmod.app q r) = r.
Proof.
  intros w1 w2 q r Hw1 Hw2.
  apply Zmod.unsigned_inj.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (w1 + w2 - w2) with w1 by lia.
  rewrite unsigned_app_arith by lia.
  rewrite Z.div_add by (pose proof (Z.pow_pos_nonneg 2 w1 ltac:(lia) ltac:(lia)); lia).
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  pose proof (bits.unsigned_range r ltac:(lia)) as Hr.
  rewrite (Z.div_small (Zmod.unsigned q) (2 ^ w1)) by lia.
  rewrite Z.add_0_l.
  apply Z.mod_small; lia.
Qed.

Local Arguments evalFromBitStruct [ls]%_list_scope !helps vals%_Zmod_scope.

Lemma evalFromBitStruct_cons :
  forall (x : string * Kind) (xs : list (string * Kind))
         (f_to : type (snd x) -> bits (kindSize (snd x)))
         (fs_to : DiffTuple (fun y => type (snd y) -> bits (kindSize (snd y))) xs)
         (f_from : bits (kindSize (snd x)) -> type (snd x))
         (fs_from : DiffTuple (fun y => bits (kindSize (snd y)) -> type (snd y)) xs)
         (vh : type (snd x)) (vt : type (Struct xs)),
    (0 <= kindSize (Struct xs))%Z ->
    (0 <= kindSize (snd x))%Z ->
    f_from (f_to vh) = vh ->
    @evalFromBitStruct xs fs_from (@evalToBitStruct xs fs_to vt) = vt ->
    @evalFromBitStruct (x :: xs) (Build_Prod f_from fs_from)
      (@evalToBitStruct (x :: xs) (Build_Prod f_to fs_to) (Build_Prod vh vt)) =
    Build_Prod vh vt.
Proof.
  intros x xs f_to fs_to f_from fs_from vh vt Hw1 Hw2 Hh Ht.
  cbn [evalToBitStruct evalFromBitStruct Fst Snd].
  f_equal.
  - transitivity (f_from (f_to vh));
      [f_equal; apply (lastn_app_gen (kindSize (Struct xs)) (kindSize (snd x))); assumption | exact Hh].
  - transitivity (@evalFromBitStruct xs fs_from (@evalToBitStruct xs fs_to vt));
      [f_equal; apply (firstn_app_gen (kindSize (Struct xs)) (kindSize (snd x))); assumption | exact Ht].
Qed.

Lemma evalFromBit_evalToBit_MulStageState :
  forall d, (0 <= d)%Z ->
    forall (x : type (MulStageState d)),
      @evalFromBit (MulStageState d) (evalToBit x) = x.
Proof.
  intros d Hd [[|] [acc [shiftOp [op2 [hiCorr []]]]]];
    cbv [evalToBit evalFromBit KindCustomInd MulStageState];
    repeat (apply evalFromBitStruct_cons;
            [ cbn [kindSize fst snd]; lia
            | cbn [kindSize fst snd]; lia
            | reflexivity
            | ]);
    reflexivity.
Qed.

Lemma evalOrBinary_MulOutput : forall d (x : type (MulOutput d)),
  evalOrBinary (getDefault (MulOutput d)) x = x.
Proof.
  intros d [f1 [f2 []]]; unfold evalOrBinary, evalBinary, getDefault; cbn.
  repeat rewrite Zmod_or_0_l; reflexivity.
Qed.

Lemma evalOrBinary_DivOutput : forall d (x : type (DivOutput d)),
  evalOrBinary (getDefault (DivOutput d)) x = x.
Proof.
  intros d [f1 [f2 [f3 [f4 [f5 []]]]]]; unfold evalOrBinary, evalBinary, getDefault; cbn.
  repeat rewrite Zmod_or_0_l; reflexivity.
Qed.

Lemma evalOrBinary_SharedOutput : forall d (x : type (SharedOutput d)),
  evalOrBinary (getDefault (SharedOutput d)) x = x.
Proof.
  intros d [f1 []]; unfold evalOrBinary, evalBinary, getDefault; cbn.
  repeat rewrite Zmod_or_0_l; reflexivity.
Qed.

Lemma iterStepsSz_unsigned_nat : forall (k n : nat),
  (k <= n)%nat ->
  Z.to_nat (Zmod.unsigned (bits.of_Z (iterStepsSz n) (Z.of_nat k))) = k.
Proof.
  intros k n Hle.
  assert (Hpow : Z.of_nat k < 2 ^ iterStepsSz n).
  { unfold iterStepsSz.
    assert (Hpos : 0 < Z.of_nat n + 1) by lia.
    destruct (Z.eq_dec (Z.of_nat n + 1) 1) as [Heq1 | Hne1].
    - assert (k = 0)%nat by lia; subst k; cbn; lia.
    - assert (Hgt1 : 1 < Z.of_nat n + 1) by lia.
      pose proof (proj2 (Z.log2_up_spec (Z.of_nat n + 1) Hgt1)) as Hup.
      assert (Hle_max : Z.log2_up (Z.of_nat n + 1) <= Z.max 1 (Z.log2_up (Z.of_nat n + 1))) by lia.
      pose proof (Z.pow_le_mono_r 2 (Z.log2_up (Z.of_nat n + 1)) (Z.max 1 (Z.log2_up (Z.of_nat n + 1))) ltac:(lia) Hle_max) as Hmono.
      lia. }
  replace (Zmod.unsigned (bits.of_Z (iterStepsSz n) (Z.of_nat k))) with (Z.of_nat k)
    by (symmetry; unfold bits.of_Z; apply Zmod.unsigned_of_Z_small; lia).
  apply Nat2Z.id.
Qed.

Lemma IterTargetSteps_mulStepsConst : forall input_width mul_stages (inp : type (MulInput (dataLen input_width))),
  IterTargetSteps (MulInput (dataLen input_width)) mul_stages
    (@mulStepsConst input_width mul_stages) inp = mul_stages.
Proof.
  intros input_width mul_stages inp.
  unfold IterTargetSteps, mulStepsConst; cbn -[iterStepsSz bits.of_Z].
  apply iterStepsSz_unsigned_nat; lia.
Qed.

Lemma IterTargetSteps_divStepsConst : forall input_width div_stages (inp : type (DivInput (dataLen input_width))),
  IterTargetSteps (DivInput (dataLen input_width)) div_stages
    (@divStepsConst input_width div_stages) inp = div_stages.
Proof.
  intros input_width div_stages inp.
  unfold IterTargetSteps, divStepsConst; cbn -[iterStepsSz bits.of_Z].
  apply iterStepsSz_unsigned_nat; lia.
Qed.

Lemma IterTargetSteps_sharedStepsFn : forall input_width mul_stages div_stages (inp : type (SharedInput (dataLen input_width))),
  IterTargetSteps (SharedInput (dataLen input_width)) (Nat.max mul_stages div_stages)
    (@sharedStepsFn input_width mul_stages div_stages) inp =
  if inp @% "isMul" then mul_stages else div_stages.
Proof.
  intros input_width mul_stages div_stages inp.
  unfold IterTargetSteps, sharedStepsFn; cbn -[iterStepsSz bits.of_Z].
  destruct (Fst inp); apply iterStepsSz_unsigned_nat; lia.
Qed.

Lemma StageValAt_Mul : forall input_width bps k inp,
  StageValAt (@mulInitStage input_width) (fun ty st => @mulStageStep input_width ty bps st) k inp =
  MulStageStateAt input_width (k * bps)%nat inp.
Proof.
  intros input_width bps k inp.
  induction k as [| k' IH]; cbn [StageValAt].
  - symmetry; apply MulStageStateAt_0.
  - rewrite IH, MulStageStateAt_step; f_equal; lia.
Qed.

Lemma StageValAt_Div : forall input_width bps k inp,
  StageValAt (@divInitStage input_width) (fun ty st => @divStageStep input_width ty bps st) k inp =
  DivStageStateAt input_width (k * bps)%nat inp.
Proof.
  intros input_width bps k inp.
  induction k as [| k' IH]; cbn [StageValAt].
  - symmetry; apply DivStageStateAt_0.
  - rewrite IH, DivStageStateAt_step; f_equal; lia.
Qed.

Lemma StageValAt_Shared : forall input_width mul_bps div_bps k inp,
  (0 < input_width)%nat ->
  StageValAt (@sharedInitStage input_width)
    (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st) k inp =
  SharedStageStateAt input_width k mul_bps div_bps inp.
Proof.
  intros input_width mul_bps div_bps k inp Hw.
  induction k as [| k' IH]; cbn [StageValAt].
  - symmetry; apply (SharedStageStateAt_0 input_width Hw).
  - rewrite IH, SharedStageStateAt_step by exact Hw; reflexivity.
Qed.

Theorem PureMulOut_mulProd_eq_SpecMul :
  forall d (inp : type (MulInput d)),
    (evalLetExpr (@PureMulOut d type inp)) @% "mulProd" =
    evalLetExpr (@SpecMul d type (inp @% "op1Signed") (inp @% "op2Signed")
                                 (inp @% "op1") (inp @% "op2")).
Proof.
  intros d [isHigh [op1Signed [op2Signed [op1 [op2 []]]]]]; reflexivity.
Qed.

Theorem PureDivOut_quot_rem_eq_SpecDiv :
  forall d (inp : type (DivInput d)),
    let isSigned := negb (inp @% "isUnsigned") in
    let spec := evalLetExpr (@SpecDiv d type isSigned isSigned (inp @% "op1") (inp @% "op2")) in
    (evalLetExpr (@PureDivOut d type inp)) @% "quot" = spec @% "quot" /\
    (evalLetExpr (@PureDivOut d type inp)) @% "rem"  = spec @% "rem".
Proof.
  intros d [[|] [isRem [op1 [op2 []]]]]; split; reflexivity.
Qed.

Theorem PipelinedMul_StageValAt_PureMulOut :
  forall input_width mul_stages (inp : type (MulInput (dataLen input_width))),
    let d := dataLen input_width in
    let mul_bps := (input_width / mul_stages)%nat in
    (0 < input_width)%nat ->
    (mul_stages * mul_bps = input_width)%nat ->
    evalLetExpr (@mulFinishStage input_width type
      (StageValAt (@mulInitStage input_width)
                  (fun ty st => @mulStageStep input_width ty mul_bps st)
                  mul_stages inp)) =
    evalLetExpr (@PureMulOut d type inp).
Proof.
  intros input_width mul_stages inp d mul_bps Hw Hmul_w; subst d mul_bps.
  rewrite StageValAt_Mul, Hmul_w, (MulFinish_PureMulOut_correct input_width Hw); reflexivity.
Qed.

Theorem IterMul_StageValAt_PureMulOut :
  forall input_width mul_stages (inp : type (MulInput (dataLen input_width))),
    let d := dataLen input_width in
    let mul_bps := (input_width / mul_stages)%nat in
    (0 < input_width)%nat ->
    (mul_stages * mul_bps = input_width)%nat ->
    evalLetExpr (@mulFinishStage input_width type
      (StageValAt (@mulInitStage input_width)
                  (fun ty st => @mulStageStep input_width ty mul_bps st)
                  (IterTargetSteps (MulInput d) mul_stages (@mulStepsConst input_width mul_stages) inp)
                  inp)) =
    evalLetExpr (@PureMulOut d type inp).
Proof.
  intros input_width mul_stages inp d mul_bps Hw Hmul_w; subst d mul_bps.
  rewrite IterTargetSteps_mulStepsConst, StageValAt_Mul, Hmul_w, (MulFinish_PureMulOut_correct input_width Hw);
    reflexivity.
Qed.

Theorem IterDiv_StageValAt_PureDivOut :
  forall input_width div_stages (inp : type (DivInput (dataLen input_width))),
    let d := dataLen input_width in
    let div_bps := (input_width / div_stages)%nat in
    (0 < input_width)%nat ->
    (div_stages * div_bps = input_width)%nat ->
    evalLetExpr (@divFinishStage input_width type
      (StageValAt (@divInitStage input_width)
                  (fun ty st => @divStageStep input_width ty div_bps st)
                  (IterTargetSteps (DivInput d) div_stages (@divStepsConst input_width div_stages) inp)
                  inp)) =
    evalLetExpr (@PureDivOut d type inp).
Proof.
  intros input_width div_stages inp d div_bps Hw Hdiv_w; subst d div_bps.
  rewrite IterTargetSteps_divStepsConst, StageValAt_Div, Hdiv_w, (DivFinish_PureDivOut_correct input_width Hw);
    reflexivity.
Qed.

Theorem SharedIterMulDiv_StageValAt_PureSharedOut :
  forall input_width mul_stages div_stages (inp : type (SharedInput (dataLen input_width))),
    let d := dataLen input_width in
    let mul_bps := (input_width / mul_stages)%nat in
    let div_bps := (input_width / div_stages)%nat in
    let max_stages := Nat.max mul_stages div_stages in
    (0 < input_width)%nat ->
    (mul_stages * mul_bps = input_width)%nat ->
    (div_stages * div_bps = input_width)%nat ->
    evalLetExpr (@sharedFinishStage input_width type
      (StageValAt (@sharedInitStage input_width)
                  (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st)
                  (IterTargetSteps (SharedInput d) max_stages (@sharedStepsFn input_width mul_stages div_stages) inp)
                  inp)) =
    evalLetExpr (@PureSharedOut d type inp).
Proof.
  intros input_width mul_stages div_stages inp d mul_bps div_bps max_stages Hw Hmul_w Hdiv_w;
    subst d mul_bps div_bps max_stages.
  rewrite IterTargetSteps_sharedStepsFn, (StageValAt_Shared input_width _ _ _ _ Hw).
  rewrite (SharedFinish_PureSharedOut_correct input_width Hw mul_stages div_stages _ _ _ Hmul_w Hdiv_w);
    reflexivity.
Qed.

(* ===========================================================================
 * PART 3: 1-ELEMENT FIFO SPECIFICATION SIMULATION FOR ALL MULDIV UNITS
 *
 * Every Mul/Div implementation unit (`PipelinedMul`, `IterMul`, `IterDiv`,
 * `SharedIterMulDiv`) is proved to simulate a 1-element FIFO (`specFifoTree`)
 * holding the output of `PureMulOut`, `PureDivOut`, or `PureSharedOut`
 * via `ActionSimulation` (`SemAction` equivalence).
 * =========================================================================== *)

Section ConcreteSpecFifoSimulation.
  Variable dom : string.
  Variable input_width mul_stages div_stages : nat.

  Local Notation d := (dataLen input_width).
  Local Notation mul_bps := (input_width / mul_stages)%nat.
  Local Notation div_bps := (input_width / div_stages)%nat.
  Local Notation max_stages := (Nat.max mul_stages div_stages).

  (* --- Spec 1-Element Enqueue Actions for Mul, Div, and Shared Mul/Div --- *)

  Definition specMulFifoEnq (ty : Kind -> Type) (inp : ty (MulInput d)) :
    Action ty (specFifoTree dom (MulOutput d)) (Bit 0) :=
    specFifoEnq dom (@PureMulOut d) ty inp.

  Definition specDivFifoEnq (ty : Kind -> Type) (inp : ty (DivInput d)) :
    Action ty (specFifoTree dom (DivOutput d)) (Bit 0) :=
    specFifoEnq dom (@PureDivOut d) ty inp.

  Definition specSharedFifoEnq (ty : Kind -> Type) (inp : ty (SharedInput d)) :
    Action ty (specFifoTree dom (SharedOutput d)) (Bit 0) :=
    specFifoEnq dom (@PureSharedOut d) ty inp.

  (* --- 3A. `PipelinedMul` Simulates `specFifoTree dom (MulOutput d)` --- *)

  Definition PipelinedMul_SpecFifoRel
    (s_u : TreeState DomainElemState (unannotMulPipeTree dom input_width mul_stages))
    (s_spec : TreeState DomainElemState (specFifoTree dom (MulOutput d))) : Prop :=
    PipeSpecFifoRel dom (MulInput d) (MulStageState d) (MulOutput d) mul_stages
      (@mulFinishStage input_width) (@PureMulOut d) s_u s_spec.

  Theorem PipelinedMul_SpecFifoRel_Init :
    PipelinedMul_SpecFifoRel
      (InitState (unannotMulPipeTree dom input_width mul_stages))
      (InitState (specFifoTree dom (MulOutput d))).
  Proof.
    apply PipeSpecFifoRel_Init.
  Qed.

  Theorem PipelinedMul_First_ActionSimulation :
    ActionSimulation PipelinedMul_SpecFifoRel
      (@unannotMulPipeFirst dom input_width mul_stages type)
      (specFifoFirst dom (MulOutput d) type).
  Proof.
    apply PipeSpecFifo_First_ActionSimulation.
    - apply evalOrBinary_MulStageState.
    - apply kindSize_MulStageState_nonneg; unfold dataLen; lia.
    - apply evalFromBit_evalToBit_MulStageState; unfold dataLen; lia.
    - apply evalOrBinary_MulOutput.
  Qed.

  Theorem PipelinedMul_Deq_ActionSimulation :
    ActionSimulation PipelinedMul_SpecFifoRel
      (@unannotMulPipeDeq dom input_width mul_stages type)
      (specFifoDeq dom (MulOutput d) type).
  Proof.
    apply PipeSpecFifo_Deq_ActionSimulation.
  Qed.

  Theorem PipelinedMul_StepToLast_ActionSimulation :
    forall (inp : type (MulInput d))
           (act : Action type (unannotMulPipeTree dom input_width mul_stages) (Bit 0))
           s_u s_spec s_u' ret,
      (0 < input_width)%nat ->
      (mul_stages * mul_bps = input_width)%nat ->
      fifo1_size (stagedLastFifo dom (MulStageState d) mul_stages s_u) = Zmod.of_Z 2 0 ->
      stagedLastFifo dom (MulStageState d) mul_stages s_u' =
        @mkFifo1 dom (MulStageState d)
          (StageValAt (@mulInitStage input_width)
                      (fun ty st => @mulStageStep input_width ty mul_bps st)
                      mul_stages inp)
          (Zmod.of_Z 2 1) ->
      PipelinedMul_SpecFifoRel s_u s_spec ->
      SemAction act s_u s_u' ret ->
      exists s_spec',
        SemAction (specMulFifoEnq type inp) s_spec s_spec' ret /\
        PipelinedMul_SpecFifoRel s_u' s_spec'.
  Proof.
    intros inp act s_u s_spec s_u' ret Hw Hmul_w Hemp Hlast' Hrel Hsem.
    eapply PipeSpecFifo_StepToLast_ActionSimulation;
      [apply (PipelinedMul_StageValAt_PureMulOut input_width mul_stages inp Hw Hmul_w)
      | exact Hemp | exact Hlast' | exact Hrel | exact Hsem].
  Qed.

  (* --- 3B. `IterMul` Simulates `specFifoTree dom (MulOutput d)` --- *)

  Definition IterMul_SpecFifoRel
    (s_u : TreeState DomainElemState (unannotMulIterTree dom input_width mul_stages))
    (s_spec : TreeState DomainElemState (specFifoTree dom (MulOutput d))) : Prop :=
    IterSpecFifoRel dom (MulInput d) (MulStageState d) (MulOutput d) mul_stages
      (@mulFinishStage input_width) (@PureMulOut d) s_u s_spec.

  Theorem IterMul_SpecFifoRel_Init :
    IterMul_SpecFifoRel
      (InitState (unannotMulIterTree dom input_width mul_stages))
      (InitState (specFifoTree dom (MulOutput d))).
  Proof.
    apply IterSpecFifoRel_Init.
  Qed.

  Theorem IterMul_First_ActionSimulation :
    ActionSimulation IterMul_SpecFifoRel
      (@unannotMulIterFirst dom input_width mul_stages type)
      (specFifoFirst dom (MulOutput d) type).
  Proof.
    apply IterSpecFifo_First_ActionSimulation, evalOrBinary_MulOutput.
  Qed.

  Theorem IterMul_Deq_ActionSimulation :
    ActionSimulation IterMul_SpecFifoRel
      (@unannotMulIterDeq dom input_width mul_stages type)
      (specFifoDeq dom (MulOutput d) type).
  Proof.
    apply IterSpecFifo_Deq_ActionSimulation.
  Qed.

  Theorem IterMul_Enq_Stutter_ActionSimulation :
    forall (inp : type (MulInput d))
           (s_u : TreeState DomainElemState (unannotMulIterTree dom input_width mul_stages))
           s_spec s_u' ret,
      s_u @% "busy" = false ->
      (0 < mul_stages)%nat ->
      IterMul_SpecFifoRel s_u s_spec ->
      SemAction (@unannotMulIterEnq dom input_width mul_stages type inp) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        IterMul_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (MulInput d) (MulStageState d) mul_stages
          (@mulStepsConst input_width mul_stages)
          (@mulInitStage input_width)
          (fun ty st => @mulStageStep input_width ty mul_bps st)
          inp 0%nat s_u'.
  Proof.
    intros inp s_u s_spec s_u' ret Hidle Hpos Hrel Hsem.
    eapply IterSpecFifo_Enq_Stutter;
      [exact Hidle | rewrite IterTargetSteps_mulStepsConst; exact Hpos | exact Hrel | exact Hsem].
  Qed.

  Theorem IterMul_Step_Stutter_ActionSimulation :
    forall (inp : type (MulInput d)) (m : nat) s_u s_spec s_u' ret,
      IterStateAtStep dom (MulInput d) (MulStageState d) mul_stages
        (@mulStepsConst input_width mul_stages)
        (@mulInitStage input_width)
        (fun ty st => @mulStageStep input_width ty mul_bps st)
        inp m s_u ->
      (S m < mul_stages)%nat ->
      IterMul_SpecFifoRel s_u s_spec ->
      SemAction (@unannotMulIterStepRule dom input_width mul_stages type) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        IterMul_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (MulInput d) (MulStageState d) mul_stages
          (@mulStepsConst input_width mul_stages)
          (@mulInitStage input_width)
          (fun ty st => @mulStageStep input_width ty mul_bps st)
          inp (S m) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hst Hlt Hrel Hsem.
    eapply IterSpecFifo_Step_Stutter;
      [exact Hst | rewrite IterTargetSteps_mulStepsConst; exact Hlt | exact Hrel | exact Hsem].
  Qed.

  Theorem IterMul_Finish_ActionSimulation :
    forall (inp : type (MulInput d)) (m : nat) s_u s_spec s_u' ret,
      (0 < input_width)%nat ->
      (mul_stages * mul_bps = input_width)%nat ->
      IterStateAtStep dom (MulInput d) (MulStageState d) mul_stages
        (@mulStepsConst input_width mul_stages)
        (@mulInitStage input_width)
        (fun ty st => @mulStageStep input_width ty mul_bps st)
        inp m s_u ->
      S m = mul_stages ->
      IterMul_SpecFifoRel s_u s_spec ->
      SemAction (@unannotMulIterStepRule dom input_width mul_stages type) s_u s_u' ret ->
      exists s_spec',
        SemAction (specMulFifoEnq type inp) s_spec s_spec' ret /\
        IterMul_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (MulInput d) (MulStageState d) mul_stages
          (@mulStepsConst input_width mul_stages)
          (@mulInitStage input_width)
          (fun ty st => @mulStageStep input_width ty mul_bps st)
          inp (IterTargetSteps (MulInput d) mul_stages (@mulStepsConst input_width mul_stages) inp) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hw Hmul_w Hst HSm Hrel Hsem.
    eapply IterSpecFifo_Step_Finish_ActionSimulation;
      [apply (IterMul_StageValAt_PureMulOut input_width mul_stages inp Hw Hmul_w)
      | exact Hst
      | rewrite IterTargetSteps_mulStepsConst; exact HSm
      | exact Hrel
      | exact Hsem].
  Qed.

  (* --- 3C. `IterDiv` Simulates `specFifoTree dom (DivOutput d)` --- *)

  Definition IterDiv_SpecFifoRel
    (s_u : TreeState DomainElemState (unannotDivIterTree dom input_width div_stages))
    (s_spec : TreeState DomainElemState (specFifoTree dom (DivOutput d))) : Prop :=
    IterSpecFifoRel dom (DivInput d) (DivStageState d) (DivOutput d) div_stages
      (@divFinishStage input_width) (@PureDivOut d) s_u s_spec.

  Theorem IterDiv_SpecFifoRel_Init :
    IterDiv_SpecFifoRel
      (InitState (unannotDivIterTree dom input_width div_stages))
      (InitState (specFifoTree dom (DivOutput d))).
  Proof.
    apply IterSpecFifoRel_Init.
  Qed.

  Theorem IterDiv_First_ActionSimulation :
    ActionSimulation IterDiv_SpecFifoRel
      (@unannotDivIterFirst dom input_width div_stages type)
      (specFifoFirst dom (DivOutput d) type).
  Proof.
    apply IterSpecFifo_First_ActionSimulation, evalOrBinary_DivOutput.
  Qed.

  Theorem IterDiv_Deq_ActionSimulation :
    ActionSimulation IterDiv_SpecFifoRel
      (@unannotDivIterDeq dom input_width div_stages type)
      (specFifoDeq dom (DivOutput d) type).
  Proof.
    apply IterSpecFifo_Deq_ActionSimulation.
  Qed.

  Theorem IterDiv_Enq_Stutter_ActionSimulation :
    forall (inp : type (DivInput d))
           (s_u : TreeState DomainElemState (unannotDivIterTree dom input_width div_stages))
           s_spec s_u' ret,
      s_u @% "busy" = false ->
      (0 < div_stages)%nat ->
      IterDiv_SpecFifoRel s_u s_spec ->
      SemAction (@unannotDivIterEnq dom input_width div_stages type inp) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        IterDiv_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (DivInput d) (DivStageState d) div_stages
          (@divStepsConst input_width div_stages)
          (@divInitStage input_width)
          (fun ty st => @divStageStep input_width ty div_bps st)
          inp 0%nat s_u'.
  Proof.
    intros inp s_u s_spec s_u' ret Hidle Hpos Hrel Hsem.
    eapply IterSpecFifo_Enq_Stutter;
      [exact Hidle | rewrite IterTargetSteps_divStepsConst; exact Hpos | exact Hrel | exact Hsem].
  Qed.

  Theorem IterDiv_Step_Stutter_ActionSimulation :
    forall (inp : type (DivInput d)) (m : nat) s_u s_spec s_u' ret,
      IterStateAtStep dom (DivInput d) (DivStageState d) div_stages
        (@divStepsConst input_width div_stages)
        (@divInitStage input_width)
        (fun ty st => @divStageStep input_width ty div_bps st)
        inp m s_u ->
      (S m < div_stages)%nat ->
      IterDiv_SpecFifoRel s_u s_spec ->
      SemAction (@unannotDivIterStepRule dom input_width div_stages type) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        IterDiv_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (DivInput d) (DivStageState d) div_stages
          (@divStepsConst input_width div_stages)
          (@divInitStage input_width)
          (fun ty st => @divStageStep input_width ty div_bps st)
          inp (S m) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hst Hlt Hrel Hsem.
    eapply IterSpecFifo_Step_Stutter;
      [exact Hst | rewrite IterTargetSteps_divStepsConst; exact Hlt | exact Hrel | exact Hsem].
  Qed.

  Theorem IterDiv_Finish_ActionSimulation :
    forall (inp : type (DivInput d)) (m : nat) s_u s_spec s_u' ret,
      (0 < input_width)%nat ->
      (div_stages * div_bps = input_width)%nat ->
      IterStateAtStep dom (DivInput d) (DivStageState d) div_stages
        (@divStepsConst input_width div_stages)
        (@divInitStage input_width)
        (fun ty st => @divStageStep input_width ty div_bps st)
        inp m s_u ->
      S m = div_stages ->
      IterDiv_SpecFifoRel s_u s_spec ->
      SemAction (@unannotDivIterStepRule dom input_width div_stages type) s_u s_u' ret ->
      exists s_spec',
        SemAction (specDivFifoEnq type inp) s_spec s_spec' ret /\
        IterDiv_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (DivInput d) (DivStageState d) div_stages
          (@divStepsConst input_width div_stages)
          (@divInitStage input_width)
          (fun ty st => @divStageStep input_width ty div_bps st)
          inp (IterTargetSteps (DivInput d) div_stages (@divStepsConst input_width div_stages) inp) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hw Hdiv_w Hst HSm Hrel Hsem.
    eapply IterSpecFifo_Step_Finish_ActionSimulation;
      [apply (IterDiv_StageValAt_PureDivOut input_width div_stages inp Hw Hdiv_w)
      | exact Hst
      | rewrite IterTargetSteps_divStepsConst; exact HSm
      | exact Hrel
      | exact Hsem].
  Qed.

  (* --- 3D. `SharedIterMulDiv` Simulates `specFifoTree dom (SharedOutput d)` --- *)

  Definition SharedIterMulDiv_SpecFifoRel
    (s_u : TreeState DomainElemState (unannotSharedIterTree dom input_width mul_stages div_stages))
    (s_spec : TreeState DomainElemState (specFifoTree dom (SharedOutput d))) : Prop :=
    IterSpecFifoRel dom (SharedInput d) (SharedStageState d) (SharedOutput d) max_stages
      (@sharedFinishStage input_width) (@PureSharedOut d) s_u s_spec.

  Theorem SharedIterMulDiv_SpecFifoRel_Init :
    SharedIterMulDiv_SpecFifoRel
      (InitState (unannotSharedIterTree dom input_width mul_stages div_stages))
      (InitState (specFifoTree dom (SharedOutput d))).
  Proof.
    apply IterSpecFifoRel_Init.
  Qed.

  Theorem SharedIterMulDiv_First_ActionSimulation :
    ActionSimulation SharedIterMulDiv_SpecFifoRel
      (@unannotSharedIterFirst dom input_width mul_stages div_stages type)
      (specFifoFirst dom (SharedOutput d) type).
  Proof.
    apply IterSpecFifo_First_ActionSimulation, evalOrBinary_SharedOutput.
  Qed.

  Theorem SharedIterMulDiv_Deq_ActionSimulation :
    ActionSimulation SharedIterMulDiv_SpecFifoRel
      (@unannotSharedIterDeq dom input_width mul_stages div_stages type)
      (specFifoDeq dom (SharedOutput d) type).
  Proof.
    apply IterSpecFifo_Deq_ActionSimulation.
  Qed.

  Theorem SharedIterMulDiv_Enq_Stutter_ActionSimulation :
    forall (inp : type (SharedInput d))
           (s_u : TreeState DomainElemState (unannotSharedIterTree dom input_width mul_stages div_stages))
           s_spec s_u' ret,
      s_u @% "busy" = false ->
      (0 < if inp @% "isMul" then mul_stages else div_stages)%nat ->
      SharedIterMulDiv_SpecFifoRel s_u s_spec ->
      SemAction (@unannotSharedIterEnq dom input_width mul_stages div_stages type inp) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        SharedIterMulDiv_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (SharedInput d) (SharedStageState d) max_stages
          (@sharedStepsFn input_width mul_stages div_stages)
          (@sharedInitStage input_width)
          (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st)
          inp 0%nat s_u'.
  Proof.
    intros inp s_u s_spec s_u' ret Hidle Hpos Hrel Hsem.
    eapply IterSpecFifo_Enq_Stutter;
      [exact Hidle | rewrite IterTargetSteps_sharedStepsFn; exact Hpos | exact Hrel | exact Hsem].
  Qed.

  Theorem SharedIterMulDiv_Step_Stutter_ActionSimulation :
    forall (inp : type (SharedInput d)) (m : nat) s_u s_spec s_u' ret,
      IterStateAtStep dom (SharedInput d) (SharedStageState d) max_stages
        (@sharedStepsFn input_width mul_stages div_stages)
        (@sharedInitStage input_width)
        (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st)
        inp m s_u ->
      (S m < if inp @% "isMul" then mul_stages else div_stages)%nat ->
      SharedIterMulDiv_SpecFifoRel s_u s_spec ->
      SemAction (@unannotSharedIterStepRule dom input_width mul_stages div_stages type) s_u s_u' ret ->
      exists s_spec',
        SemAction (Return (Const type (Bit 0) Zmod.zero)) s_spec s_spec' ret /\
        SharedIterMulDiv_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (SharedInput d) (SharedStageState d) max_stages
          (@sharedStepsFn input_width mul_stages div_stages)
          (@sharedInitStage input_width)
          (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st)
          inp (S m) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hst Hlt Hrel Hsem.
    eapply IterSpecFifo_Step_Stutter;
      [exact Hst | rewrite IterTargetSteps_sharedStepsFn; exact Hlt | exact Hrel | exact Hsem].
  Qed.

  Theorem SharedIterMulDiv_Finish_ActionSimulation :
    forall (inp : type (SharedInput d)) (m : nat) s_u s_spec s_u' ret,
      (0 < input_width)%nat ->
      (mul_stages * mul_bps = input_width)%nat ->
      (div_stages * div_bps = input_width)%nat ->
      IterStateAtStep dom (SharedInput d) (SharedStageState d) max_stages
        (@sharedStepsFn input_width mul_stages div_stages)
        (@sharedInitStage input_width)
        (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st)
        inp m s_u ->
      S m = (if inp @% "isMul" then mul_stages else div_stages) ->
      SharedIterMulDiv_SpecFifoRel s_u s_spec ->
      SemAction (@unannotSharedIterStepRule dom input_width mul_stages div_stages type) s_u s_u' ret ->
      exists s_spec',
        SemAction (specSharedFifoEnq type inp) s_spec s_spec' ret /\
        SharedIterMulDiv_SpecFifoRel s_u' s_spec' /\
        IterStateAtStep dom (SharedInput d) (SharedStageState d) max_stages
          (@sharedStepsFn input_width mul_stages div_stages)
          (@sharedInitStage input_width)
          (fun ty st => @sharedStageStep input_width ty mul_bps div_bps st)
          inp (IterTargetSteps (SharedInput d) max_stages (@sharedStepsFn input_width mul_stages div_stages) inp) s_u'.
  Proof.
    intros inp m s_u s_spec s_u' ret Hw Hmul_w Hdiv_w Hst HSm Hrel Hsem.
    eapply IterSpecFifo_Step_Finish_ActionSimulation;
      [apply (SharedIterMulDiv_StageValAt_PureSharedOut input_width mul_stages div_stages inp Hw Hmul_w Hdiv_w)
      | exact Hst
      | rewrite IterTargetSteps_sharedStepsFn; exact HSm
      | exact Hrel
      | exact Hsem].
  Qed.

End ConcreteSpecFifoSimulation.
