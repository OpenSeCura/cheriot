From Stdlib Require Import List String Ascii ZArith Znumtheory Zmod Zmod.Bits Lia Bool.
From Guru Require Import Library Syntax Semantics Notations MergeFold.
From Cheriot Require Import SpecDefines FunctionalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.


(* ========================================================================= *)
(* PRIMARY ARCHITECTURAL INVARIANTS                                          *)
(*                                                                           *)
(* These 4 core properties define the CHERI capability parameters:          *)
(*   1. Base width from compressed top:      CapBSz = CapcTSz + 1            *)
(*   2. Address width is power of exponent:  2 ^ ExpSz = AddrSz              *)
(*   3. Mantissa fits inside address:        2 < CapBSz < AddrSz             *)
(*   4. Maximum exponent definition:         Emax = 2 ^ ExpSz - CapcTSz      *)
(*                                                                           *)
(* ONLY these 4 theorems unfold definitions from SpecDefines.                *)
(* Every other property in the entire codebase is derived purely from them.  *)
(* ========================================================================= *)

Theorem invariant_CapBSz_eq : CapBSz = CapcTSz + 1.
Proof. unfold CapBSz, CapcTSz. reflexivity. Qed.

Theorem invariant_two_pow_ExpSz_eq_AddrSz : 2 ^ ExpSz = AddrSz.
Proof. unfold ExpSz, LgAddrSz, AddrSz, Xlen. reflexivity. Qed.

Theorem invariant_CapBSz_bounds : 2 < CapBSz < AddrSz.
Proof. unfold CapBSz, CapcTSz, AddrSz, Xlen. lia. Qed.

Theorem invariant_Emax_def : Emax = 2 ^ ExpSz - CapcTSz.
Proof.
  change Emax with (2^ExpSz - CapcTSz).
  reflexivity.
Qed.

(* ========================================================================= *)
(* DERIVED ARCHITECTURAL THEOREMS                                            *)
(* Proved purely from the 4 invariants above (NO unfolding of constants).    *)
(* ========================================================================= *)

Theorem CapBSz_gt_2 : 2 < CapBSz.
Proof. pose proof invariant_CapBSz_bounds; lia. Qed.

Theorem CapBSz_lt_AddrSz : CapBSz < AddrSz.
Proof. pose proof invariant_CapBSz_bounds; lia. Qed.

Theorem AddrSz_gt_3 : 3 < AddrSz.
Proof. pose proof invariant_CapBSz_bounds; lia. Qed.

Theorem AddrSz_gt_1 : 1 < AddrSz.
Proof. pose proof AddrSz_gt_3; lia. Qed.

Theorem AddrSz_pos : 0 < AddrSz.
Proof. pose proof AddrSz_gt_1; lia. Qed.

Theorem AddrSz_nonneg : 0 <= AddrSz.
Proof. pose proof AddrSz_pos; lia. Qed.

Theorem ExpSz_pos : 0 < ExpSz.
Proof.
  destruct (Z_le_gt_dec ExpSz 0) as [Hle | Hgt]; [ | lia ].
  assert (2^ExpSz <= 1).
  { destruct (Z.eq_dec ExpSz 0) as [Heq | Hlt].
    - rewrite Heq. rewrite Z.pow_0_r. lia.
    - assert (ExpSz < 0) by lia.
      rewrite Z.pow_neg_r by lia. lia. }
  rewrite invariant_two_pow_ExpSz_eq_AddrSz in H.
  pose proof AddrSz_gt_3.
  lia.
Qed.

Theorem ExpSz_nonneg : 0 <= ExpSz.
Proof. pose proof ExpSz_pos; lia. Qed.

Theorem two_pow_ExpSz_eq_AddrSz : 2 ^ ExpSz = AddrSz.
Proof. exact invariant_two_pow_ExpSz_eq_AddrSz. Qed.

Theorem Emax_eq_AddrSz_add_1_sub_CapBSz : Emax = AddrSz + 1 - CapBSz.
Proof.
  rewrite invariant_Emax_def.
  rewrite invariant_two_pow_ExpSz_eq_AddrSz.
  pose proof invariant_CapBSz_eq.
  lia.
Qed.

Theorem CapBSz_pos : 0 < CapBSz.
Proof. pose proof CapBSz_gt_2; lia. Qed.

Theorem CapBSz_ge_2 : 2 <= CapBSz.
Proof. pose proof CapBSz_gt_2; lia. Qed.

Theorem AddrSz_sub_CapBSz_pos : 0 < AddrSz - CapBSz.
Proof. pose proof CapBSz_lt_AddrSz; lia. Qed.

Theorem AddrSz_sub_CapBSz_nonneg : 0 <= AddrSz - CapBSz.
Proof. pose proof CapBSz_lt_AddrSz; lia. Qed.

Theorem two_pow_ExpSz_pos : 0 < 2 ^ ExpSz.
Proof. rewrite two_pow_ExpSz_eq_AddrSz; apply AddrSz_pos. Qed.

Theorem two_pow_AddrSz_pos : 0 < 2 ^ AddrSz.
Proof. apply Z.pow_pos_nonneg; [ lia | pose proof AddrSz_pos; lia ]. Qed.

Theorem two_pow_CapBSz_pos : 0 < 2 ^ CapBSz.
Proof. apply Z.pow_pos_nonneg; [ lia | pose proof CapBSz_pos; lia ]. Qed.

Theorem two_pow_AddrSz_add_1_pos : 0 < 2 ^ (AddrSz + 1).
Proof. apply Z.pow_pos_nonneg; [ lia | pose proof AddrSz_pos; lia ]. Qed.

Theorem two_pow_AddrSz_add_1_gt_1 : 1 < 2 ^ (AddrSz + 1).
Proof.
  assert (Hpos: 1 <= AddrSz + 1) by (pose proof AddrSz_pos; lia).
  assert (2^1 <= 2^(AddrSz + 1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Theorem two_pow_AddrSz_add_2_pos : 0 < 2 ^ (AddrSz + 2).
Proof. apply Z.pow_pos_nonneg; [ lia | pose proof AddrSz_pos; lia ]. Qed.

Theorem Emax_minus_1_eq_AddrSz_sub_CapBSz : Emax - 1 = AddrSz - CapBSz.
Proof. rewrite Emax_eq_AddrSz_add_1_sub_CapBSz; lia. Qed.

Theorem Emax_nonneg : 0 <= Emax.
Proof. rewrite Emax_eq_AddrSz_add_1_sub_CapBSz; pose proof CapBSz_lt_AddrSz; lia. Qed.

Theorem Emax_lt_AddrSz : Emax < AddrSz.
Proof. rewrite Emax_eq_AddrSz_add_1_sub_CapBSz; pose proof CapBSz_gt_2; lia. Qed.

(* ========================================================================= *)
(* ARITHMETIC & BIT-VECTOR UTILITIES                                         *)
(* Modular arithmetic, bit-level properties, leading zero bounds, and Ltac.  *)
(* ========================================================================= *)

Theorem mod_neg1_m : forall m, 1 < m -> (-1) mod m = m - 1.
Proof.
  intros m Hm.
  rewrite (Z.mod_unique (-1) m (-1) (m - 1)); [ reflexivity | lia | ring ].
Qed.

Lemma multiple : forall x n k,
  0 <= n <= k ->
  ((x * 2^n) mod 2^k) mod 2^n = 0.
Proof.
  intros.
  assert (Hpos: 0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(k - n)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^k) with (2^(k - n) * 2^n) by (rewrite <- Z.pow_add_r; try lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r; try lia.
  rewrite Z.mul_mod; try lia.
  rewrite Z.mod_same; try lia.
  rewrite Z.mul_0_r.
  apply Z.mod_0_l; try lia.
Qed.

Lemma bounds_E_nonneg : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  0 <= Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))).
Proof.
  intros. unfold Zmod.to_Z.
  pose proof (bits.unsigned_range (evalExpr (get_E_from_cE (bounds@%"cE"))) ltac:(apply ExpSz_nonneg)) as [H0 H1].
  exact H0.
Qed.

Lemma add_0_r_bits : forall {n} (accum: bits n),
  0 < n ->
  (accum + 0)%Zmod = accum.
Proof.
  intros n accum Hn.
  apply Zmod.unsigned_inj.
  rewrite Zmod.unsigned_add.
  change (0%Zmod : bits n) with (Zmod.zero : bits n).
  rewrite Zmod.unsigned_0.
  rewrite Z.add_0_r.
  rewrite Z.mod_small.
  - reflexivity.
  - apply bits.unsigned_range; lia.
Qed.

Lemma unsigned_add_1_bits : forall {n} (accum: bits n),
  0 < n ->
  Zmod.unsigned accum + 1 < 2^n ->
  Zmod.unsigned (accum + 1)%Zmod = Zmod.unsigned accum + 1.
Proof.
  intros n accum Hn Hlt.
  rewrite Zmod.unsigned_add.
  change (1%Zmod : bits n) with (Zmod.one : bits n).
  rewrite Zmod.unsigned_1.
  assert (Hpos: 0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.mod_small 1 (2^n)) by (pose proof (Z.pow_le_mono_r 2 1 n ltac:(lia) ltac:(lia)); lia).
  rewrite Z.mod_small; [ reflexivity | ].
  pose proof (bits.unsigned_range accum ltac:(lia)) as [H0 H1].
  lia.
Qed.

Lemma countLeadingZerosLoop_bound : forall {ni no} arr count over (accum: bits no),
  0 < no ->
  0 <= Zmod.unsigned accum ->
  Zmod.unsigned accum + Z.of_nat count < 2^no ->
  Zmod.unsigned (evalLetExpr (@countLeadingZerosLoop type ni no arr count over accum)) <= Zmod.unsigned accum + Z.of_nat count.
Proof.
  intros ni no arr count.
  induction count as [| m IHm]; intros over accum Hno Hacc Hbound.
  - simpl. unfold evalLetExpr. simpl. lia.
  - simpl. unfold evalLetExpr. simpl.
    cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr
         mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit] in *.
    fold evalLetExpr.
    rewrite Nat2Z.inj_succ in Hbound.
    unfold Z.succ in Hbound.
    destruct (over || _)%bool.
    + rewrite !Zmod.add_0_l.
      rewrite add_0_r_bits by lia.
      assert (Hstep: Zmod.unsigned accum + Z.of_nat m < 2^no) by lia.
      generalize (IHm true accum Hno Hacc Hstep); intros Hih.
      change (PosDef.Pos.of_succ_nat m) with (Pos.of_succ_nat m).
      replace (Z.pos (Pos.of_succ_nat m)) with (Z.succ (Z.of_nat m)) by (symmetry; apply Nat2Z.inj_succ).
      unfold Z.succ.
      match type of Hih with | ?L <= ?R => match goal with | |- ?L <= ?R2 =>
        assert (H_le: R <= R2) by (apply Z.add_le_mono_l; lia);
        exact (Z.le_trans _ _ _ Hih H_le)
      end end.
    + rewrite !Zmod.add_0_l.
      assert (Hbound1: Zmod.unsigned accum + 1 < 2^no) by lia.
      assert (Hmod: Zmod.unsigned (accum + 1)%Zmod = Zmod.unsigned accum + 1) by (apply unsigned_add_1_bits; lia).
      assert (Hacc': 0 <= Zmod.unsigned (accum + 1)%Zmod) by (rewrite Hmod; lia).
      assert (Hstep: Zmod.unsigned (accum + 1)%Zmod + Z.of_nat m < 2^no) by (rewrite Hmod; lia).
      generalize (IHm false (accum + 1)%Zmod Hno Hacc' Hstep); intros Hih.
      rewrite Hmod in Hih.
      change (PosDef.Pos.of_succ_nat m) with (Pos.of_succ_nat m).
      replace (Z.pos (Pos.of_succ_nat m)) with (Z.succ (Z.of_nat m)) by (symmetry; apply Nat2Z.inj_succ).
      unfold Z.succ.
      match type of Hih with | ?L <= ?R => match goal with | |- ?L <= ?R2 =>
        assert (H_le: R <= R2); [
          apply Z.eq_le_incl;
          rewrite <- Z.add_assoc, (Z.add_comm 1 (Z.of_nat m));
          reflexivity
        | exact (Z.le_trans _ _ _ Hih H_le) ]
      end end.
Qed.

Lemma countLeadingZerosLoop_bound_ExpSz : forall ni arr count over (accum: bits ExpSz),
  0 <= Zmod.unsigned accum ->
  Zmod.unsigned accum + Z.of_nat count < AddrSz ->
  Zmod.unsigned (evalLetExpr (@countLeadingZerosLoop type ni ExpSz arr count over accum)) <= Zmod.unsigned accum + Z.of_nat count.
Proof.
  intros ni arr count over accum Hacc Hbound.
  apply countLeadingZerosLoop_bound.
  - apply ExpSz_pos.
  - exact Hacc.
  - rewrite two_pow_ExpSz_eq_AddrSz. exact Hbound.
Qed.

Lemma countLeadingZerosLoop_bound_CapBSz : forall (arr: @Expr type (Array (Z.to_nat (AddrSz - CapBSz)) Bool)) accum,
  Zmod.unsigned accum = 0 ->
  Zmod.unsigned (evalLetExpr (@countLeadingZerosLoop type (Z.to_nat (AddrSz - CapBSz)) ExpSz arr (Z.to_nat (AddrSz - CapBSz)) false accum)) <= AddrSz - CapBSz.
Proof.
  intros arr accum H_zero.
  assert (H_acc: 0 <= Zmod.unsigned accum) by (rewrite H_zero; lia).
  assert (H_bound: Zmod.unsigned accum + Z.of_nat (Z.to_nat (AddrSz - CapBSz)) < AddrSz).
  { rewrite H_zero. rewrite Z2Nat.id by (pose proof AddrSz_sub_CapBSz_nonneg; lia).
    pose proof CapBSz_pos. lia. }
  pose proof (@countLeadingZerosLoop_bound_ExpSz (Z.to_nat (AddrSz - CapBSz)) arr (Z.to_nat (AddrSz - CapBSz)) false accum H_acc H_bound) as Hloop.
  rewrite H_zero in Hloop.
  rewrite Z2Nat.id in Hloop by (pose proof AddrSz_sub_CapBSz_nonneg; lia).
  exact Hloop.
Qed.

Lemma countLeadingZerosLoop_bound_CapBSz_0 : forall (arr: @Expr type (Array (Z.to_nat (AddrSz - CapBSz)) Bool)),
  Zmod.unsigned (evalLetExpr (@countLeadingZerosLoop type (Z.to_nat (AddrSz - CapBSz)) ExpSz arr (Z.to_nat (AddrSz - CapBSz)) false 0%Zmod)) <= AddrSz - CapBSz.
Proof.
  intros. apply countLeadingZerosLoop_bound_CapBSz.
  change (0%Zmod : bits ExpSz) with (Zmod.zero : bits ExpSz). apply Zmod.unsigned_0.
Qed.

Lemma bits_ExpSz_range : forall (b: bits ExpSz),
  0 <= Zmod.unsigned b <= AddrSz - 1.
Proof.
  intros b.
  pose proof (bits.unsigned_range b ltac:(apply ExpSz_nonneg)) as [H1 H2].
  rewrite two_pow_ExpSz_eq_AddrSz in H2.
  lia.
Qed.

Lemma not_bitsExpSz_val : forall (b: bits ExpSz),
  Zmod.unsigned (Zmod.not b) = AddrSz - 1 - Zmod.unsigned b.
Proof.
  intros b.
  rewrite bits.unsigned_not'.
  rewrite Z.ones_equiv.
  unfold Z.pred.
  replace (2 ^ ExpSz + -1) with (AddrSz - 1) by (rewrite two_pow_ExpSz_eq_AddrSz; ring).
  reflexivity.
Qed.

Ltac solve_unsigned_nonneg :=
  match goal with
  | |- 0 <= Zmod.unsigned ?X =>
      destruct (Zmod.unsigned_range X) as [[Hpos _] | [H_zero | [H_neg1 H_neg2]]];
      [ exact Hpos
      | revert H_zero;
        first [ generalize two_pow_ExpSz_pos; intros ? ?; lia
              | generalize two_pow_CapBSz_pos; intros ? ?; lia
              | generalize two_pow_AddrSz_pos; intros ? ?; lia
              | generalize two_pow_AddrSz_add_1_pos; intros ? ?; lia ]
      | pose proof (Z.lt_le_trans _ _ _ H_neg1 H_neg2) as Hlt;
        revert Hlt;
        first [ generalize two_pow_ExpSz_pos; intros ? ?; lia
              | generalize two_pow_CapBSz_pos; intros ? ?; lia
              | generalize two_pow_AddrSz_pos; intros ? ?; lia
              | generalize two_pow_AddrSz_add_1_pos; intros ? ?; lia ] ]
  end.

Ltac solve_lia :=
  intros;
  first [ solve_unsigned_nonneg
        | pose proof AddrSz_pos;
          pose proof ExpSz_pos;
          pose proof CapBSz_pos;
          pose proof CapBSz_lt_AddrSz;
          pose proof two_pow_ExpSz_pos;
          pose proof two_pow_AddrSz_pos;
          pose proof two_pow_CapBSz_pos;
          pose proof two_pow_AddrSz_add_1_pos;
          repeat match goal with
          | H : _ \/ _ \/ _ |- _ => destruct H as [[? ?]|[?|[? ?]]]
          end;
          try solve_unsigned_nonneg;
          lia ].

(* ========================================================================= *)
(* EXPONENT COMPUTATION & MASKING LEMMAS                                     *)
(* Semantic evaluation of e_init, bitwise shift/mask operations, and cE.     *)
(* ========================================================================= *)

Lemma e_init_val : forall (clz: bits ExpSz),
  Zmod.unsigned clz <= AddrSz - CapBSz ->
  Zmod.unsigned (Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)) =
  (AddrSz - CapBSz) - Zmod.unsigned clz.
Proof.
  intros clz Hclz.
  rewrite Zmod.unsigned_add.
  rewrite not_bitsExpSz_val.
  rewrite Zmod.unsigned_of_Z.
  pose proof (bits.unsigned_range clz ltac:(apply ExpSz_nonneg)) as [H1 H2].
  rewrite (Z.mod_small (AddrSz + 1 - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
  rewrite (Z.mod_unique (AddrSz + 1 - CapBSz + (AddrSz - 1 - Zmod.unsigned clz)) (2^ExpSz) 1 ((AddrSz - CapBSz) - Zmod.unsigned clz)).
  - reflexivity.
  - pose proof two_pow_ExpSz_eq_AddrSz. pose proof CapBSz_pos. pose proof CapBSz_lt_AddrSz. lia.
  - pose proof two_pow_ExpSz_eq_AddrSz. lia.
Qed.

Lemma e_init_plus_one_val : forall (clz: bits ExpSz),
  Zmod.unsigned clz <= AddrSz - CapBSz ->
  Zmod.unsigned (Zmod.add (Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)) (Zmod.one : bits ExpSz)) =
  (if Zmod.unsigned clz =? 0 then (AddrSz + 1 - CapBSz) else (AddrSz + 1 - CapBSz) - Zmod.unsigned clz).
Proof.
  intros clz Hclz.
  rewrite Zmod.unsigned_add.
  rewrite (e_init_val Hclz).
  change (Zmod.unsigned (Zmod.one : bits ExpSz)) with 1.
  destruct (Zmod.unsigned clz =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz; rewrite Hz.
    replace (AddrSz - CapBSz - 0 + 1) with (AddrSz + 1 - CapBSz) by lia.
    rewrite (Z.mod_small (AddrSz + 1 - CapBSz) (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
    reflexivity.
  - apply Z.eqb_neq in Hz.
    replace (AddrSz - CapBSz - Zmod.unsigned clz + 1) with ((AddrSz + 1 - CapBSz) - Zmod.unsigned clz) by lia.
    pose proof (bits.unsigned_range clz ltac:(apply ExpSz_nonneg)) as [H1 H2].
    rewrite (Z.mod_small ((AddrSz + 1 - CapBSz) - Zmod.unsigned clz) (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
    reflexivity.
Qed.

Lemma and_slu_mask_raw : forall b e,
  0 <= e ->
  0 <= b ->
  Z.land b (Z.shiftl (-1) e) = (b / 2^e) * 2^e.
Proof.
  intros.
  apply Z.bits_inj_iff'. intros k Hk.
  rewrite Z.land_spec.
  destruct (Z_lt_le_dec k e) as [Hlt | Hle].
  - (* k < e *)
    rewrite Z.shiftl_spec; try lia.
    rewrite (Z.testbit_neg_r (-1) (k - e)); try lia.
    symmetry.
    rewrite <- Z.shiftl_mul_pow2; try lia.
    rewrite Z.shiftl_spec; try lia.
    rewrite (Z.testbit_neg_r (b / 2^e) (k - e)); try lia.
  - (* k >= e *)
    rewrite Z.shiftl_spec; try lia.
    assert (-1 = Z.lnot 0) by reflexivity.
    rewrite H1. rewrite Z.lnot_spec; try lia.
    rewrite Z.testbit_0_l. simpl.
    assert (H_testbit_true: forall x, x && true = x) by (intros; destruct x; reflexivity).
    rewrite H_testbit_true.
    symmetry.
    rewrite <- Z.shiftl_mul_pow2; try lia.
    rewrite Z.shiftl_spec; try lia.
    assert (k - e >= 0) by lia.
    rewrite <- Z.shiftr_div_pow2; try lia.
    rewrite Z.shiftr_spec; try lia.
    f_equal. lia.
Qed.

Lemma and_slu_mask : forall (b: bits (AddrSz+1)) (e: Z),
  0 <= e <= AddrSz - 1 ->
  Zmod.unsigned (Zmod.and b (Zmod.slu (bits.of_Z (AddrSz+1) (-1)) e)) =
  (Zmod.unsigned b / 2^e) * 2^e.
Proof.
  intros.
  rewrite Zmod.unsigned_and.
  rewrite Zmod.unsigned_slu.
  rewrite Zmod.unsigned_of_Z.
  rewrite <- and_slu_mask_raw; try lia.
  apply Z.bits_inj_iff'. intros k Hk.
  destruct (Z_lt_le_dec k (AddrSz + 1)) as [Hlt | Hle].
  - (* k < AddrSz + 1 *)
    rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.land_spec.
    rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.shiftl_spec; try lia.
    destruct (Z_lt_le_dec k e) as [Hlte | Hgee].
    + rewrite (Z.testbit_neg_r (-1) (k - e)) by lia.
      rewrite (Z.testbit_neg_r (-1 mod 2^(AddrSz + 1)) (k - e)) by lia.
      reflexivity.
    + rewrite !Z.mod_pow2_bits_low; try lia.
      reflexivity.
  - (* k >= AddrSz + 1 *)
    assert (H_b: Z.testbit (Zmod.unsigned b) k = false).
    { apply Z.testbit_false; try lia. replace (Zmod.unsigned b / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      pose proof (bits.unsigned_range b ltac:(pose proof AddrSz_pos; lia)) as [H1 H2].
      split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    assert (H_lhs: Z.testbit (Z.land (Zmod.unsigned b) (Z.shiftl (-1 mod 2 ^ (AddrSz + 1)) e mod 2 ^ (AddrSz + 1)) mod 2 ^ (AddrSz + 1)) k = false).
    { apply Z.testbit_false; try lia. replace (Z.land (Zmod.unsigned b) (Z.shiftl (-1 mod 2 ^ (AddrSz + 1)) e mod 2 ^ (AddrSz + 1)) mod 2 ^ (AddrSz + 1) / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      assert (H_pos: 0 < 2^(AddrSz + 1)) by (apply two_pow_AddrSz_add_1_pos).
      generalize (Z.mod_pos_bound (Z.land (Zmod.unsigned b) (Z.shiftl (-1 mod 2^(AddrSz + 1)) e mod 2^(AddrSz + 1))) (2^(AddrSz + 1)) H_pos).
      intros [H1 H2]. split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    rewrite H_lhs.
    rewrite Z.land_spec.
    rewrite H_b. simpl. reflexivity.
  - pose proof (bits.unsigned_range b ltac:(pose proof AddrSz_pos; lia)). lia.
Qed.


Lemma and_all_ones : forall (b: bits (AddrSz+1)),
  Zmod.to_Z (Zmod.and (bits.of_Z (AddrSz+1) (-1)) b) = Zmod.to_Z b.
Proof.
  intros.
  rewrite Zmod.unsigned_and.
  rewrite Zmod.unsigned_of_Z.
  assert (H_ones: (-1) mod 2^(AddrSz + 1) = Z.ones (AddrSz + 1)).
  { rewrite Z.ones_equiv. unfold Z.pred.
    rewrite mod_neg1_m.
    - ring.
    - apply two_pow_AddrSz_add_1_gt_1. }
  rewrite H_ones.
  apply Z.bits_inj_iff'. intros k Hk.
  destruct (Z_lt_le_dec k (AddrSz + 1)) as [Hlt | Hle].
  - rewrite Z.mod_pow2_bits_low; try lia.
    rewrite Z.land_spec.
    rewrite (Z.ones_spec_low (AddrSz + 1) k) by lia.
    rewrite andb_true_l. reflexivity.
  - assert (H_b: Z.testbit (Zmod.unsigned b) k = false).
    { apply Z.testbit_false; try lia. replace (Zmod.unsigned b / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      pose proof (bits.unsigned_range b ltac:(pose proof AddrSz_pos; lia)) as [H1 H2].
      split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    assert (H_lhs: Z.testbit (Z.land (Z.ones (AddrSz + 1)) (Zmod.unsigned b) mod 2^(AddrSz + 1)) k = false).
    { apply Z.testbit_false; try lia. replace (Z.land (Z.ones (AddrSz + 1)) (Zmod.unsigned b) mod 2^(AddrSz + 1) / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      assert (H_pos: 0 < 2^(AddrSz + 1)) by (apply two_pow_AddrSz_add_1_pos).
      generalize (Z.mod_pos_bound (Z.land (Z.ones (AddrSz + 1)) (Zmod.unsigned b)) (2^(AddrSz + 1)) H_pos).
      intros [H1 H2]. split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    rewrite H_lhs. rewrite H_b. reflexivity.
Qed.

Lemma to_Z_app_0 : forall (n : Z) (b : bits n),
  0 <= n ->
  Zmod.to_Z (Zmod.app b (0%Zmod : bits 1)) = Zmod.to_Z b.
Proof.
  intros n b Hn.
  unfold Zmod.to_Z, Zmod.app.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  rewrite Zmod.unsigned_of_Z.
  change (Zmod.unsigned (0%Zmod : bits 1)) with 0.
  rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite Z.mod_small; [ reflexivity | ].
  generalize (Zmod.unsigned_range b).
  intros [[H1 H2] | [H1 | [H1 H2]]]; try lia.
  split; try lia.
  assert (0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
  assert (2^n < 2^(n + 1)).
  { replace (n + 1) with (Z.succ n) by lia.
    rewrite Z.pow_succ_r; lia. }
  lia.
Qed.

Lemma cE_decode_id : forall (ef : bits ExpSz) (cond : bool),
  ef <> Zmod.of_Z (2^ExpSz) (-1) ->
  (if Zmod.eqb (if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z (2^ExpSz) (-1) else ef) (Zmod.of_Z (2^ExpSz) (-1))
   then (0%Zmod : bits ExpSz)
   else (if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z (2^ExpSz) (-1) else ef)) = ef.
Proof.
  intros ef cond Hef_ne.
  destruct (Zmod.eqb_spec (if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z (2^ExpSz) (-1) else ef) (Zmod.of_Z (2^ExpSz) (-1))) as [H_eq | H_neq].
  - destruct (Zmod.eqb ef 0 && cond)%bool eqn:H_and.
    + apply andb_true_iff in H_and as [H_ef0 H_cond].
      apply Zmod.eqb_eq in H_ef0. subst ef.
      reflexivity.
    + congruence.
  - destruct (Zmod.eqb ef 0 && cond)%bool eqn:H_and.
    + congruence.
    + reflexivity.
Qed.


Lemma bounds_base_math_abstract : forall (base : bits AddrSz) (ef : bits ExpSz) (cond : bool),
  ef <> Zmod.of_Z (2^ExpSz) (-1) ->
  let cE : bits ExpSz := if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z (2^ExpSz) (-1) else ef in
  let ef_decoded := Zmod.to_Z (evalExpr (get_E_from_cE cE)) in
  let outBase := Zmod.and (Zmod.and (bits.of_Z (AddrSz + 1) (-1)) (Zmod.app base (0%Zmod : bits 1))) (Zmod.slu (bits.of_Z (AddrSz + 1) (-1)) (Zmod.to_Z ef)) in
  Zmod.to_Z outBase = (Zmod.to_Z base / 2^ef_decoded) * 2^ef_decoded.
Proof.
  intros base ef cond Hne cE ef_decoded outBase.
  subst cE ef_decoded outBase.
  cbn [evalExpr get_E_from_cE isAllOnes InvDefault isEq KindCustomInd].
  rewrite and_slu_mask by apply bits_ExpSz_range.
  rewrite and_all_ones.
  rewrite (to_Z_app_0 (n := AddrSz)); [ | apply AddrSz_nonneg ].
  unfold Zmod.to_Z.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  rewrite cE_decode_id by exact Hne.
  reflexivity.
Qed.

Fixpoint evalLetPropGen {k} (le: LetExpr type k) (P: type k -> Prop) : Prop :=
  match le with
  | RetE e => P (evalExpr e)
  | SystemE ls cont => evalLetPropGen cont P
  | LetEx s k' le cont => forall (res : type k'), res = evalLetExpr le -> evalLetPropGen (cont res) P
  | IfElseE s p k' t f cont =>
      if evalExpr p then forall (res : type k'), res = evalLetExpr t -> evalLetPropGen (cont res) P
                    else forall (res : type k'), res = evalLetExpr f -> evalLetPropGen (cont res) P
  end.

Lemma evalLetPropGen_sound :
  forall {k} (le: LetExpr type k) P,
    evalLetPropGen le P -> P (evalLetExpr le).
Proof.
  fix evalLetPropGen_sound 2.
  intros k le P H.
  destruct le as [e | ls cont | s k' le1 cont | s p k' t f cont].
  - exact H.
  - apply (evalLetPropGen_sound _ cont P H).
  - apply (evalLetPropGen_sound _ (cont (evalLetExpr le1)) P (H (evalLetExpr le1) eq_refl)).
  - simpl in H. simpl.
    destruct (evalExpr p).
    + apply (evalLetPropGen_sound _ (cont (evalLetExpr t)) P (H (evalLetExpr t) eq_refl)).
    + apply (evalLetPropGen_sound _ (cont (evalLetExpr f)) P (H (evalLetExpr f) eq_refl)).
Qed.

(* ========================================================================= *)
(* BOUNDS CIRCUIT SEMANTICS: BASE & TOP EXTRACTION                           *)
(* Proves that Bounds extracts base as floor(base / 2^ef) * 2^ef and         *)
(* bounds the resulting top address.                                         *)
(* ========================================================================= *)

Lemma bounds_base_math : forall (base length : bits AddrSz) (isRoundDown : bool) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"base") = (Zmod.to_Z base / 2^ef) * 2^ef.
Proof.
  intros base length isRoundDown bounds Hbounds.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst outBase cram cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)).
  apply (@bounds_base_math_abstract base ef cond).
  intro Heq.
  assert (H_ef_bound : Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
  { subst ef.
    destruct isRoundDown.
    - subst e_roundDown pick_b.
      cbn [evalLetExpr evalExpr].
      subst e_init.
      cbn [evalLetExpr evalExpr fold_left map evalNot].
      rewrite Zmod.add_0_l.
      assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
      { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
      pose proof (e_init_val Hclz_bound) as He_val.
      pose proof (bits.unsigned_range clz ltac:(apply ExpSz_nonneg)) as [H1 H2].
      change (evalNot clz) with (Zmod.not clz).
      change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
      destruct (_ <? _) eqn:H_slt.
      + apply Z.ltb_lt in H_slt.
        rewrite He_val in H_slt.
        clear -H_slt H1.
        lia.
      + rewrite He_val.
        clear -H1.
        lia.
    - subst e_normal.
      cbn [evalLetExpr evalExpr].
      destruct isESaturated.
      + rewrite Zmod.unsigned_of_Z.
        rewrite (Z.mod_small (AddrSz + 1 - CapBSz) (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
        lia.
      + cbn [evalLetExpr evalExpr] in HisESaturated.
        apply eq_sym in HisESaturated.
        apply Z.ltb_ge in HisESaturated.
        rewrite Zmod.unsigned_of_Z in HisESaturated.
        rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) in HisESaturated by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
        lia.
  }
  rewrite Heq in H_ef_bound.
  change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
  rewrite Zmod.unsigned_of_Z in H_ef_bound.
  rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
  rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
  pose proof CapBSz_gt_2.
  lia.
Qed.

Lemma div_add_exact : forall b len e,
  0 <= e ->
  0 <= b ->
  0 <= len ->
  b / 2^e + (len + (b mod 2^e) + 2^e - 1) / 2^e = (b + len + 2^e - 1) / 2^e.
Proof.
  intros.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.div_mod b (2^e)) at 3; try lia.
  replace (2^e * (b / 2^e) + b mod 2^e + len + 2^e - 1) with
    ((b / 2^e) * 2^e + (len + b mod 2^e + 2^e - 1)) by lia.
  rewrite Z_div_plus_full_l with (b := 2^e); lia.
Qed.

Lemma bounds_top_rel : forall base length isRoundDown B,
  B = evalLetExpr (Bounds (ty:=type) base length isRoundDown) ->
  Zmod.to_Z (B@%"top") = (Zmod.to_Z (B@%"base") + Zmod.to_Z (B@%"length")) mod 2^(AddrSz + 2).
Proof.
  intros base length isRoundDown B HB.
  subst B.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  rewrite HoutTop.
  cbn [evalLetExpr evalExpr fold_left map snd].
  rewrite Zmod.add_0_l.
  rewrite Zmod.unsigned_add.
  cbn [evalExpr ZeroExtend ZeroExtendTo].
  unfold Zmod.app, Zmod.zero.
  rewrite !Zmod.unsigned_of_Z.
  replace (AddrSz + 2 - (AddrSz + 1)) with 1 by lia.
  change (2 ^ 1) with 2.
  change (0 mod 2) with 0.
  rewrite !Z.shiftl_0_l, !Z.lor_0_r.
  replace (AddrSz + 1 + 1) with (AddrSz + 2) by lia.
  rewrite <- Z.add_mod by (pose proof two_pow_AddrSz_add_2_pos; lia).
  reflexivity.
Qed.

Lemma div_add_ge : forall y r c,
  0 < c ->
  0 <= y ->
  0 <= r ->
  y / c <= (y + r + c - 1) / c.
Proof.
  intros.
  apply Z.div_le_mono; lia.
Qed.

Lemma unsigned_app_zero : forall (n m : Z) (b : bits n),
  0 <= n -> 0 <= m ->
  Zmod.unsigned (Zmod.app b (Zmod.zero : bits m)) = Zmod.unsigned b.
Proof.
  intros n m b Hn Hm.
  unfold Zmod.app.
  rewrite Zmod.unsigned_of_Z.
  rewrite Zmod.unsigned_0.
  rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite Z.mod_small; [reflexivity|].
  generalize (Zmod.unsigned_range b).
  intros [[H1 H2] | [H1 | [H1 H2]]]; try lia.
  split; try lia.
  assert (2^n <= 2^(n + m)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma unsigned_firstn : forall (n w : Z) (a : bits w),
  0 <= n ->
  Zmod.unsigned (@Zmod.firstn n w a) = Zmod.unsigned a mod 2^n.
Proof.
  intros n w a Hn.
  unfold Zmod.firstn.
  rewrite Zmod.unsigned_of_Z.
  reflexivity.
Qed.

Lemma unsigned_sru_pos : forall (w : Z) (x : bits w) (n : Z),
  0 <= n ->
  Zmod.unsigned (Zmod.sru x n) = Z.shiftr (Zmod.unsigned x) n.
Proof.
  intros.
  apply Zmod.unsigned_sru; lia.
Qed.

Lemma to_Z_nonneg : forall {sz} (w : bits sz), 0 <= sz -> 0 <= Zmod.to_Z w.
Proof.
  intros sz w Hsz.
  assert (Hpos: 0 < 2^sz) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Zmod.unsigned_pos_bound w Hpos) as [H0 H1].
  exact H0.
Qed.

Lemma bounds_top_le_add : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z (bounds@%"top") <= Zmod.to_Z (bounds@%"base") + Zmod.to_Z (bounds@%"length").
Proof.
  intros base length isRoundDown bounds HB.
  pose proof (bounds_top_rel HB) as H_top.
  rewrite H_top.
  apply Zmod_le.
  - apply two_pow_AddrSz_add_2_pos.
  - pose proof (@to_Z_nonneg (AddrSz + 1) (bounds@%"base") ltac:(pose proof AddrSz_pos; lia)).
    pose proof (@to_Z_nonneg (AddrSz + 1) (bounds@%"length") ltac:(pose proof AddrSz_pos; lia)).
    lia.
Qed.

Lemma bounds_top_from_base_len : forall (top base_val len_val b len ef : Z),
  0 <= ef ->
  0 <= b ->
  0 <= len ->
  top <= base_val + len_val ->
  base_val = (b / 2^ef) * 2^ef ->
  len_val <= ((len + (b mod 2^ef) + 2^ef - 1) / 2^ef) * 2^ef ->
  top <= ((b + len + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
  intros top base_val len_val b len ef Hef Hb Hlen_pos Htop Hbase Hlen.
  rewrite Hbase in Htop.
  eapply Z.le_trans; [ exact Htop | ].
  eapply Z.le_trans.
  - apply Z.add_le_mono_l; exact Hlen.
  - rewrite <- Z.mul_add_distr_r.
    apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
    rewrite (@div_add_exact b len ef Hef Hb Hlen_pos).
    lia.
Qed.

Lemma roundUp_no_ovf_math : forall len b e,
  0 <= e ->
  0 <= b ->
  0 <= len ->
  len / 2^e + (b mod 2^e + len mod 2^e + 2^e - 1) / 2^e =
  (len + b mod 2^e + 2^e - 1) / 2^e.
Proof.
  intros len b e Hef Hb Hlen.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  replace (b mod 2^e + len mod 2^e + 2^e - 1) with (b mod 2^e + (len mod 2^e) + 2^e - 1) by lia.
  apply (@div_add_exact len (b mod 2^e) e Hef Hlen).
  apply Z.mod_pos_bound; exact Hpos.
Qed.

(* ========================================================================= *)
(* LEADING ZEROS ANALYSIS & HARDWARE BIT-ARRAY BRIDGE                        *)
(* Bridges Kami array indexing to Z.testbit and analyzes countLeadingZeros.  *)
(* ========================================================================= *)

Lemma unsigned_lastn_AddrSz_sub_CapBSz : forall (x : bits AddrSz),
  Zmod.unsigned (Zmod_lastn (AddrSz - CapBSz) x) = Zmod.unsigned x / 2^CapBSz.
Proof.
  intros x.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z x) with (Zmod.unsigned x).
  replace (AddrSz - (AddrSz - CapBSz)) with CapBSz by lia.
  rewrite Z.shiftr_div_pow2 by (pose proof CapBSz_pos; lia).
  apply Z.mod_small.
  assert (Hpos: 0 < 2^CapBSz) by (apply two_pow_CapBSz_pos).
  pose proof (bits.unsigned_range x ltac:(pose proof AddrSz_pos; lia)) as [Hx0 Hx1].
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [exact Hpos | ].
    assert (Hpow: 2^AddrSz = 2^CapBSz * 2^(AddrSz - CapBSz)).
    { replace AddrSz with (CapBSz + (AddrSz - CapBSz)) at 1 by lia.
      rewrite Z.pow_add_r by (pose proof CapBSz_pos; pose proof AddrSz_sub_CapBSz_nonneg; lia).
      reflexivity. }
    rewrite Hpow in Hx1.
    rewrite Z.mul_comm.
    exact Hx1.
Qed.

Lemma testbit_true_ge_pow2 : forall (a k : Z),
  0 <= a ->
  0 <= k ->
  Z.testbit a k = true ->
  2^k <= a.
Proof.
  intros a k Ha Hk Hbit.
  apply Z.testbit_true in Hbit; [ | lia ].
  destruct (Z.eq_dec (a / 2^k) 0) as [Hz | Hnz].
  - rewrite Hz in Hbit; discriminate.
  - assert (0 <= a / 2^k) by (apply Z.div_pos; lia).
    assert (1 <= a / 2^k) by lia.
    assert (Hmul: 1 * 2^k <= (a / 2^k) * 2^k).
    { apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | lia ]. }
    rewrite Z.mul_1_l in Hmul.
    eapply Z.le_trans; [ exact Hmul | ].
    rewrite Z.mul_comm.
    apply Z.mul_div_le; apply Z.pow_pos_nonneg; lia.
Qed.

Lemma countLeadingZerosLoop_over_true : forall ni no arr count (accum : bits no),
  evalLetExpr (@countLeadingZerosLoop type ni no arr count true accum) = accum.
Proof.
  induction count as [| m IHm]; intros accum.
  - reflexivity.
  - simpl.
    cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr
         mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit] in *.
    fold evalLetExpr.
    rewrite !Zmod.add_0_l.
    rewrite Zmod.add_0_r.
    apply IHm.
Qed.

Lemma NatZ_mul_nonneg : forall (m : nat) (k : Z),
  0 <= k ->
  0 <= NatZ_mul m k.
Proof.
  induction m as [| m' IHm']; intros k Hk.
  - simpl. lia.
  - pose proof (IHm' k Hk). simpl NatZ_mul. lia.
Qed.

Lemma unsigned_lastn_1_array : forall (m : nat) (w : bits (kindSize (Array (S m) Bool))),
  @Zmod.unsigned (2 ^ (kindSize (Array m Bool))) (@Zmod_lastn (NatZ_mul m 1) (kindSize (Array (S m) Bool)) w) = (Zmod.unsigned w) / 2.
Proof.
  intros m w.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  match goal with
  | |- context [Z.shiftr _ ?s] => replace s with 1 by (cbn [kindSize NatZ_mul]; lia)
  end.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^1) with 2.
  assert (Hpos_powS: 0 < 2^(kindSize (Array (S m) Bool))) by (apply Z.pow_pos_nonneg; [ lia | apply NatZ_mul_nonneg; lia ]).
  pose proof (Zmod.unsigned_pos_bound w Hpos_powS) as [H0 H1].
  apply Z.mod_small.
  split.
  - apply Z.div_pos; lia.
  - assert (Hpow: 2^(kindSize (Array (S m) Bool)) = 2 * 2^(kindSize (Array m Bool))).
    { change (kindSize (Array (S m) Bool)) with (1 + NatZ_mul m 1).
      change (kindSize (Array m Bool)) with (NatZ_mul m 1).
      rewrite (Z.pow_add_r 2 1 (NatZ_mul m 1)) by (try lia; apply NatZ_mul_nonneg; lia).
      change (2^1) with 2.
      ring. }
    rewrite Hpow in H1.
    apply Z.div_lt_upper_bound; [ lia | exact H1 ].
Qed.

Lemma evalFromBitArray_cons : forall (m : nat) (f : type (Bit (kindSize Bool)) -> bool) (w : bits (kindSize (Array (S m) Bool))),
  tupleElems (@evalFromBitArray (S m) Bool f w) =
  (f (Zmod.firstn (kindSize Bool) w)) :: tupleElems (@evalFromBitArray m Bool f (Zmod_lastn (NatZ_mul m (kindSize Bool)) w)).
Proof.
  intros. reflexivity.
Qed.

Lemma evalFromBitArray_nth : forall (n : nat) (w : bits (kindSize (Array n Bool))) (i : nat) (d : bool),
  (i < n)%nat ->
  nth i (tupleElems (@evalFromBitArray n Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w)) d =
  Z.testbit (Zmod.unsigned w) (Z.of_nat i).
Proof.
  induction n as [| m IHm]; intros w i d Hi.
  - lia.
  - destruct i as [| j].
    + rewrite evalFromBitArray_cons.
      simpl nth.
      change (kindSize Bool) with 1.
      change (Z.of_nat 0) with 0.
      destruct (Z.testbit (Zmod.unsigned w) 0) eqn:Hbit.
      * apply Z.testbit_true in Hbit; [ | lia ].
        rewrite Z.pow_0_r in Hbit.
        rewrite Z.div_1_r in Hbit.
        change (Zmod.unsigned w mod Z.pow_pos 2 1) with (Zmod.unsigned w mod 2).
        rewrite Hbit.
        reflexivity.
      * apply Z.testbit_false in Hbit; [ | lia ].
        rewrite Z.pow_0_r in Hbit.
        rewrite Z.div_1_r in Hbit.
        assert (Hmod: Zmod.unsigned w mod 2 = 0).
        { assert (0 <= Zmod.unsigned w mod 2 < 2) by (apply Z.mod_pos_bound; lia). lia. }
        change (Zmod.unsigned w mod Z.pow_pos 2 1) with (Zmod.unsigned w mod 2).
        rewrite Hmod.
        reflexivity.
    + rewrite evalFromBitArray_cons.
      simpl nth.
      rewrite (IHm _ j d) by lia.
      match goal with
      | |- context [Z.testbit ?sub (Z.of_nat j)] =>
          replace sub with (Zmod.unsigned w / 2) by (symmetry; apply unsigned_lastn_1_array)
      end.
      rewrite Z.div2_bits by lia.
      rewrite Nat2Z.inj_succ.
      reflexivity.
Qed.

Lemma nth_pf_nth : forall A (ls : list A) (i : nat) (pf : Is_true (i <? Datatypes.length ls)%nat) (d : A),
  @nth_pf A ls i pf = nth i ls d.
Proof.
  induction ls as [| x xs IHxs]; intros i pf d.
  - simpl in pf. contradiction.
  - destruct i as [| j].
    + reflexivity.
    + simpl nth. apply IHxs.
Qed.

Lemma readSameTuple_nth : forall A (n : nat) (vals : SameTuple A n) (p : FinType n) (d : A),
  readSameTuple vals p = nth (finNum p) (tupleElems vals) d.
Proof.
  intros. unfold readSameTuple. apply nth_pf_nth.
Qed.

Lemma eval_readNatToFinType_mkBoolArray : forall (w : bits (AddrSz - CapBSz)) (i : nat),
  (i < Z.to_nat (AddrSz - CapBSz))%nat ->
  evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) w))) i) =
  Z.testbit (Zmod.unsigned w) (Z.of_nat i).
Proof.
  intros w i.
  let sz := eval compute in (Z.to_nat (AddrSz - CapBSz)) in
  repeat (destruct i as [| i]; [
    intro Hlt; unfold readNatToFinType, mkBoolArray;
    change (Z.to_nat (AddrSz - CapBSz)) with sz;
    change (_ <? sz)%nat with true;
    cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit
         evalOrBinary orb getDefault];
    rewrite readSameTuple_nth with (d := false);
    change (evalFromBit (k:=Array sz Bool) w)
      with (@evalFromBitArray sz Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w);
    cbn [finNum];
    rewrite evalFromBitArray_nth by lia;
    reflexivity
  | ]);
  intro Hlt;
  change (Z.to_nat (AddrSz - CapBSz)) with sz in Hlt; lia.
Qed.

Lemma countLeadingZerosLoop_step : forall ni no arr count (accum : bits no),
  evalLetExpr (@countLeadingZerosLoop type ni no arr (S count) false accum) =
  let b := evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) count) in
  if b
  then accum
  else evalLetExpr (@countLeadingZerosLoop type ni no arr count false (@Zmod.add (2^no) accum (@Zmod.one (2^no)))).
Proof.
  intros ni no arr count accum.
  simpl countLeadingZerosLoop.
  cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
       finNum Fst Snd evalExpr
       mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit
       evalOrBinary orb getDefault].
  fold evalLetExpr.
  destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) count)) eqn:Hb.
  - rewrite countLeadingZerosLoop_over_true.
    change (if true then Zmod.zero else Zmod.one) with (Zmod.zero (2^no)).
    rewrite !Zmod.add_0_l.
    rewrite Zmod.add_0_r.
    reflexivity.
  - change (if false then Zmod.zero else Zmod.one) with (Zmod.one (2^no)).
    rewrite !Zmod.add_0_l.
    reflexivity.
Qed.

Lemma countLeadingZerosLoop_ge_pow2 : forall (w : bits (AddrSz - CapBSz)) (count : nat) (accum : bits ExpSz),
  (count <= Z.to_nat (AddrSz - CapBSz))%nat ->
  Zmod.unsigned accum = (AddrSz - CapBSz - Z.of_nat count) ->
  Zmod.unsigned (evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) w)) count false accum)) <= AddrSz - CapBSz - 1 ->
  2^(AddrSz - CapBSz - 1 - Zmod.unsigned (evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) w)) count false accum))) <= Zmod.unsigned w.
Proof.
  induction count as [| count' IHcount']; intros accum Hcount Haccum Hle.
  - simpl countLeadingZerosLoop in *; cbn [evalLetExpr evalExpr] in Hle; rewrite Haccum in Hle; change (Z.of_nat 0) with 0 in Hle; lia.
  - rewrite countLeadingZerosLoop_step in *.
    rewrite eval_readNatToFinType_mkBoolArray in * by lia.
    destruct (Z.testbit (Zmod.unsigned w) (Z.of_nat count')) eqn:Hbit.
    + cbv zeta iota in *.
      assert (Hpos: 0 < 2^(AddrSz - CapBSz)) by (apply Z.pow_pos_nonneg; pose proof AddrSz_sub_CapBSz_pos; lia).
      pose proof (Zmod.unsigned_pos_bound w Hpos) as [H0 H1].
      apply testbit_true_ge_pow2.
      * exact H0.
      * lia.
      * rewrite Haccum.
        replace (AddrSz - CapBSz - 1 - (AddrSz - CapBSz - Z.of_nat (S count'))) with (Z.of_nat count') by lia.
        exact Hbit.
    + cbv zeta iota in *.
      apply IHcount'.
      * lia.
      * rewrite unsigned_add_1_bits; [ | apply ExpSz_pos | ].
        { rewrite Haccum. lia. }
        rewrite Haccum.
        rewrite two_pow_ExpSz_eq_AddrSz.
        pose proof CapBSz_pos. lia.
      * exact Hle.
Qed.

Lemma clz_ge_pow2 : forall (w : bits (AddrSz - CapBSz)) (clz : bits ExpSz),
  clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) w)) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero) ->
  Zmod.unsigned clz <= AddrSz - CapBSz - 1 ->
  2^(AddrSz - CapBSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned w.
Proof.
  intros w clz Hclz Hclz_bound.
  subst clz.
  assert (H_zero: Zmod.unsigned (Zmod.zero : bits ExpSz) = 0) by apply Zmod.unsigned_0.
  apply (@countLeadingZerosLoop_ge_pow2 w (Z.to_nat (AddrSz - CapBSz)) Zmod.zero); [ lia | | exact Hclz_bound ].
  rewrite H_zero.
  rewrite Z2Nat.id by (pose proof AddrSz_sub_CapBSz_nonneg; lia).
  lia.
Qed.

Lemma length_ge_pow2_clz : forall (length: bits AddrSz) (clz: bits ExpSz),
  clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero) ->
  Zmod.unsigned clz <= AddrSz - CapBSz - 1 ->
  2^(AddrSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned length.
Proof.
  intros length clz Hclz Hclz_bound.
  pose proof (@clz_ge_pow2 (Zmod_lastn (AddrSz - CapBSz) length) clz Hclz Hclz_bound) as Hw.
  pose proof (unsigned_lastn_AddrSz_sub_CapBSz length) as Hlastn.
  replace (AddrSz - 1 - Zmod.unsigned clz) with (CapBSz + (AddrSz - CapBSz - 1 - Zmod.unsigned clz)) by ring.
  rewrite Z.pow_add_r by (pose proof (bits_ExpSz_range clz); pose proof CapBSz_pos; lia).
  assert (Hlen_div: 2^CapBSz * (Zmod.unsigned length / 2^CapBSz) <= Zmod.unsigned length).
  { apply Z.mul_div_le. apply two_pow_CapBSz_pos. }
  rewrite <- Hlastn in Hlen_div.
  eapply Z.le_trans; [ | exact Hlen_div ].
  apply Z.mul_le_mono_nonneg_l; [ pose proof two_pow_CapBSz_pos; lia | exact Hw ].
Qed.

Lemma d_ge_pow2_CapBSz_sub_1 : forall (len : Z) (clz : Z),
  0 <= clz <= AddrSz - CapBSz - 1 ->
  2^(AddrSz - 1 - clz) <= len ->
  let e_init := AddrSz - CapBSz - clz in
  2^(CapBSz - 1) <= len / 2^e_init.
Proof.
  intros len clz Hclz Hlen e_init.
  subst e_init.
  assert (Hpos: 0 < 2^(AddrSz - CapBSz - clz)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_step: 2^(AddrSz - 1 - clz) = 2^(CapBSz - 1) * 2^(AddrSz - CapBSz - clz)).
  { replace (AddrSz - 1 - clz) with ((CapBSz - 1) + (AddrSz - CapBSz - clz)) by (pose proof CapBSz_pos; lia).
    rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). reflexivity. }
  rewrite Hpow_step in Hlen.
  apply Z.div_le_lower_bound; [ exact Hpos | ].
  rewrite Z.mul_comm.
  exact Hlen.
Qed.

(* ========================================================================= *)
(* ROUNDDOWN & ROUNDUP INTERMEDIATE PROPERTIES                               *)
(* Establishes bounds_roundDown_length_le and bounds_length_roundUp_le.      *)
(* ========================================================================= *)

Lemma bounds_roundDown_length_le : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length true) ->
  Zmod.to_Z (bounds@%"length") <= Zmod.to_Z length.
Proof.
  intros base length bounds Hbounds.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst outLen cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  unfold Zmod.to_Z.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (bits_ExpSz_range clz) as [H1 H2].
  destruct pick_b.
  - (* pick_b = true: mf = 2^CapBSz - 1, ef = e_b *)
    subst ef mf e_roundDown m_roundDown.
    cbn [snd evalExpr evalLetExpr].
    rewrite Zmod.unsigned_slu.
    rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
    rewrite Z.shiftl_mul_pow2 by solve_unsigned_nonneg.
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.mul_nonneg_nonneg; [ solve_unsigned_nonneg | apply Z.pow_nonneg; lia ].
      - apply two_pow_AddrSz_add_1_pos. }
    cbn.
    change (Zmod.unsigned (Zmod.of_Z (2^CapBSz) (-1))) with (2^CapBSz - 1).
    assert (Heb_min: 0 <= Zmod.unsigned e_b) by solve_unsigned_nonneg.
    assert (Hpos_eb: 0 <= 2^(Zmod.unsigned e_b)) by (apply Z.pow_nonneg; lia).
    cbn [evalLetExpr evalExpr] in Hpick_b.
    apply eq_sym in Hpick_b.
    apply Z.ltb_lt in Hpick_b.
    subst e_init.
    cbn [evalLetExpr evalExpr fold_left map evalNot] in Hpick_b.
    rewrite Zmod.add_0_l in Hpick_b.
    change (evalNot clz) with (Zmod.not clz) in Hpick_b.
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) in Hpick_b.
    rewrite He_val in Hpick_b.
    assert (Heb_bound: Zmod.unsigned e_b <= AddrSz - CapBSz - 1) by lia.
    assert (Hclz_bound': Zmod.unsigned clz <= AddrSz - CapBSz - 1) by lia.
    assert (Hlen_pow: 2 ^ (AddrSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned length).
    { apply length_ge_pow2_clz.
      - subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray.
      - exact Hclz_bound'. }
    assert (Hbound: (2^CapBSz - 1) * 2^(Zmod.unsigned e_b) <= 2^(CapBSz - 1 + Zmod.unsigned e_b + 1) - 2^(Zmod.unsigned e_b)).
    { replace (CapBSz - 1 + Zmod.unsigned e_b + 1) with (CapBSz + Zmod.unsigned e_b) by lia.
      rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia).
      ring_simplify. lia. }
    assert (Hle_step: 2^(CapBSz - 1 + Zmod.unsigned e_b + 1) - 2^(Zmod.unsigned e_b) <= Zmod.unsigned length).
    { assert (CapBSz - 1 + Zmod.unsigned e_b + 1 <= AddrSz - 1 - Zmod.unsigned clz) by lia.
      assert (2^(CapBSz - 1 + Zmod.unsigned e_b + 1) <= 2^(AddrSz - 1 - Zmod.unsigned clz)).
      { apply Z.pow_le_mono_r; lia. }
      lia. }
    eapply Z.le_trans; [ exact Hbound | exact Hle_step ].
  - (* pick_b = false: mf = TruncLsb 1 CapBSz d, ef = e_init *)
    subst ef mf e_roundDown m_roundDown.
    cbn [snd evalExpr evalLetExpr].
    rewrite Zmod.unsigned_slu.
    rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
    rewrite Z.shiftl_mul_pow2 by solve_unsigned_nonneg.
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.mul_nonneg_nonneg; [ solve_unsigned_nonneg | apply Z.pow_nonneg; lia ].
      - apply two_pow_AddrSz_add_1_pos. }
    subst d.
    cbn [evalLetExpr evalExpr].
    assert (Hpow_pos: 0 < 2^(Zmod.unsigned e_init)).
    { apply Z.pow_pos_nonneg; [ lia | solve_unsigned_nonneg ]. }
    eapply Z.le_trans with (m := (Zmod.unsigned length / 2^(Zmod.unsigned e_init)) * 2^(Zmod.unsigned e_init)).
    + apply Z.mul_le_mono_nonneg_r; [ lia | ].
      eapply Z.le_trans.
      * rewrite unsigned_firstn by solve_lia.
        apply Z.mod_le.
        -- apply (@to_Z_nonneg (CapBSz + 1) _); pose proof CapBSz_pos; lia.
        -- apply two_pow_CapBSz_pos.
      * eapply Z.le_trans.
        -- rewrite unsigned_firstn by solve_lia.
           apply Z.mod_le; [ solve_unsigned_nonneg | apply two_pow_AddrSz_pos ].
        -- rewrite unsigned_sru_pos by (pose proof (bits.unsigned_range e_init ltac:(pose proof ExpSz_nonneg; lia)); lia).
           rewrite Z.shiftr_div_pow2 by (pose proof (bits.unsigned_range e_init ltac:(pose proof ExpSz_nonneg; lia)); lia).
           apply Z.le_refl.
    + pose proof (Z.mul_div_le (Zmod.unsigned length) (2^(Zmod.unsigned e_init)) Hpow_pos).
      lia.
Qed.

Lemma bounds_length_roundDown_le : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length true) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"length") <= ((Zmod.to_Z length + (Zmod.to_Z base mod 2^ef) + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
  intros base length bounds HB ef.
  pose proof (bounds_roundDown_length_le HB) as Hle.
  pose proof (bounds_E_nonneg HB) as Hef.
  assert (Hpos: 0 < 2^ef) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod (Zmod.to_Z length + (Zmod.to_Z base mod 2^ef) + 2^ef - 1) (2^ef) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (Zmod.to_Z length + (Zmod.to_Z base mod 2^ef) + 2^ef - 1) (2^ef) Hpos) as Hmod.
  pose proof (Z.mod_pos_bound (Zmod.to_Z base) (2^ef) Hpos).
  lia.
Qed.


Lemma ceil_div_eq : forall (s d : Z),
  0 <= s ->
  0 < d ->
  s / d + (if s mod d =? 0 then 0 else 1) = (s + d - 1) / d.
Proof.
  intros s d Hs Hd.
  assert (Hne: d <> 0) by lia.
  pose proof (Z.div_mod s d Hne) as Hdm.
  pose proof (Z.mod_pos_bound s d Hd) as [Hmod0 Hmod1].
  destruct (s mod d =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero.
    replace (s + d - 1) with ((d - 1) + (s / d) * d) by lia.
    rewrite Z.div_add by lia.
    rewrite (Z.div_small (d - 1) d) by lia.
    lia.
  - apply Z.eqb_neq in Hzero.
    assert (Hmod_pos: 1 <= s mod d) by lia.
    replace (s + d - 1) with ((s mod d - 1) + (s / d + 1) * d) by lia.
    rewrite Z.div_add by lia.
    rewrite (Z.div_small (s mod d - 1) d) by lia.
    lia.
Qed.

Lemma carry_bound_math : forall (b_mod l_mod e_val : Z) (carry : bool),
  0 <= b_mod < 2^e_val ->
  0 <= l_mod < 2^e_val ->
  0 <= e_val ->
  (carry = true -> (b_mod + l_mod) mod 2^e_val <> 0) ->
  (b_mod + l_mod) / 2^e_val + (if carry then 1 else 0) <=
  (b_mod + l_mod + 2^e_val - 1) / 2^e_val.
Proof.
  intros b_mod l_mod e_val carry Hb Hl He Hc.
  assert (Hpos: 0 < 2^e_val) by (apply Z.pow_pos_nonneg; lia).
  assert (Hs_nonneg: 0 <= b_mod + l_mod) by lia.
  rewrite <- (ceil_div_eq Hs_nonneg Hpos).
  destruct carry.
  - assert (Hne: (b_mod + l_mod) mod 2^e_val <> 0) by (apply Hc; reflexivity).
    destruct ((b_mod + l_mod) mod 2^e_val =? 0) eqn:Hz.
    + apply Z.eqb_eq in Hz; contradiction.
    + lia.
  - destruct ((b_mod + l_mod) mod 2^e_val =? 0); lia.
Qed.

Lemma unsigned_if_one_zero : forall (b : bool),
  Zmod.unsigned (if b then (Zmod.one : bits 1) else (Zmod.zero : bits 1)) <= (if b then 1 else 0).
Proof.
  intros b; destruct b.
  - change (if true then (Zmod.one : bits 1) else (Zmod.zero : bits 1)) with (Zmod.one : bits 1).
    rewrite Zmod.unsigned_1.
    change (2^1) with 2.
    rewrite Z.mod_small by lia.
    lia.
  - change (if false then (Zmod.one : bits 1) else (Zmod.zero : bits 1)) with (Zmod.zero : bits 1).
    rewrite Zmod.unsigned_0.
    lia.
Qed.

Lemma test_land_ones : forall a e,
  0 <= e ->
  Z.land a (2^e - 1) = a mod 2^e.
Proof.
  intros a e He.
  change (2^e - 1) with (Z.pred (2^e)).
  rewrite <- Z.ones_equiv.
  apply Z.land_ones.
  exact He.
Qed.

Lemma not_slu_minus1_mask : forall (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  Zmod.unsigned (Zmod.not (Zmod.slu (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)) e)) = 2^e - 1.
Proof.
  intros e He.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  unfold Zmod.not.
  rewrite Zmod.unsigned_of_Z.
  rewrite Zmod.unsigned_slu.
  rewrite Zmod.unsigned_of_Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_Msz: 0 < 2^(AddrSz + 2 - CapBSz)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_e_le_Msz: 2^e <= 2^(AddrSz + 2 - CapBSz)) by (apply Z.pow_le_mono_r; lia).
  assert (Hpow_Msz_gt1: 1 < 2^(AddrSz + 2 - CapBSz)) by (apply Z.pow_gt_1; lia).
  rewrite mod_neg1_m by lia.
  set (Msz := 2^(AddrSz + 2 - CapBSz)).
  replace ((Msz - 1) * 2^e) with (Msz * (2^e - 1) + (Msz - 2^e)) by ring.
  assert (Hr_pos: 0 <= Msz - 2^e < Msz) by (subst Msz; lia).
  rewrite <- (Z.mod_unique_pos (Msz * (2^e - 1) + (Msz - 2^e)) Msz (2^e - 1) (Msz - 2^e)); [ | exact Hr_pos | ring ].
  unfold Z.lnot, Z.pred.
  replace (- (Msz - 2^e) + -1) with (Msz * (-1) + (2^e - 1)) by ring.
  rewrite <- (Z.mod_unique_pos (Msz * (-1) + (2^e - 1)) Msz (-1) (2^e - 1)); [ reflexivity | subst Msz; lia | ring ].
Qed.

Lemma and_mask_e : forall (w : bits (AddrSz + 2 - CapBSz)) (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  Zmod.unsigned (Zmod.and w (Zmod.not (Zmod.slu (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)) e))) =
  Zmod.unsigned w mod 2^e.
Proof.
  intros w e He.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  rewrite Zmod.unsigned_and.
  rewrite not_slu_minus1_mask by exact He.
  rewrite test_land_ones by exact (proj1 He).
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_le: 2^e <= 2^(AddrSz + 2 - CapBSz)) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound (Zmod.unsigned w) (2^e) Hpow_pos) as [Hmod0 Hmod1].
  apply Z.mod_small.
  lia.
Qed.

Lemma and_minus1_mask : forall (w : bits (AddrSz + 2 - CapBSz)),
  Zmod.unsigned (Zmod.and (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)) w) = Zmod.unsigned w.
Proof.
  intros w.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  pose proof (bits.unsigned_range w ltac:(lia)) as [Hw0 Hw1].
  rewrite Zmod.unsigned_and.
  rewrite Zmod.unsigned_of_Z.
  assert (Hpow_gt1: 1 < 2^(AddrSz + 2 - CapBSz)) by (apply Z.pow_gt_1; lia).
  rewrite mod_neg1_m by lia.
  change (2^(AddrSz + 2 - CapBSz) - 1) with (Z.pred (2^(AddrSz + 2 - CapBSz))).
  rewrite <- Z.ones_equiv.
  rewrite Z.land_comm.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_mod by lia.
  apply Z.mod_small.
  lia.
Qed.

Lemma mod_mod_mask_e : forall (z e : Z),
  0 <= e <= AddrSz - CapBSz ->
  (z mod 2^(AddrSz + 2 - CapBSz)) mod 2^e = z mod 2^e.
Proof.
  intros z e He.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_div: Z.divide (2^e) (2^(AddrSz + 2 - CapBSz))).
  { replace (AddrSz + 2 - CapBSz) with (e + (AddrSz + 2 - CapBSz - e)) by lia.
    rewrite Z.pow_add_r by lia.
    exists (2^(AddrSz + 2 - CapBSz - e)). ring. }
  rewrite (Z.mod_mod_divide z (2^(AddrSz + 2 - CapBSz)) (2^e) Hpow_div) by lia.
  reflexivity.
Qed.

Lemma unsigned_base_masked_mod : forall (base : bits AddrSz) (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  Zmod.unsigned (Zmod.and (Zmod.and (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)) (Zmod.firstn (AddrSz + 2 - CapBSz) base))
                    (Zmod.not (Zmod.slu (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)) e))) =
  Zmod.unsigned base mod 2^e.
Proof.
  intros base e He.
  rewrite and_mask_e by exact He.
  rewrite and_minus1_mask.
  rewrite (unsigned_firstn (n:=AddrSz + 2 - CapBSz)).
  2: { pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2. lia. }
  rewrite mod_mod_mask_e by exact He.
  reflexivity.
Qed.

Lemma unsigned_sum_masked_div_le : forall (base length : bits AddrSz) (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  let Msz := AddrSz + 2 - CapBSz in
  let base_masked := Zmod.and (Zmod.and (Zmod.of_Z (2^Msz) (-1)) (Zmod.firstn Msz base))
                              (Zmod.not (Zmod.slu (Zmod.of_Z (2^Msz) (-1)) e)) in
  let length_masked := Zmod.and (Zmod.and (Zmod.of_Z (2^Msz) (-1)) (Zmod.firstn Msz length))
                                (Zmod.not (Zmod.slu (Zmod.of_Z (2^Msz) (-1)) e)) in
  Zmod.unsigned (@Zmod.firstn 2 Msz (Zmod.sru (base_masked + length_masked) e)) <=
  (Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e) / 2^e.
Proof.
  intros base length e He Msz base_masked length_masked.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  assert (HMsz2: 2 <= Msz) by (subst Msz; lia).
  assert (HMsz_pos: 0 < Msz) by (subst Msz; lia).
  eapply Z.le_trans.
  { rewrite (@unsigned_firstn 2 Msz) by lia.
    apply Z.mod_le.
    - apply (@to_Z_nonneg Msz); lia.
    - change (2^2) with 4; lia. }
  rewrite Zmod.unsigned_sru.
  rewrite (Z.shiftr_div_pow2 _ e (proj1 He)).
  apply Z.div_le_mono.
  - apply Z.pow_pos_nonneg; lia.
  - rewrite Zmod.unsigned_add.
    eapply Z.le_trans.
    + apply Z.mod_le.
      * apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg Msz); lia.
      * apply Z.pow_pos_nonneg; lia.
    + subst base_masked length_masked Msz.
      rewrite !unsigned_base_masked_mod by exact He.
      apply Z.le_refl.
  - exact (proj1 He).
Qed.

Lemma carry_true_implies_rem_nonneg : forall (base length : bits AddrSz) (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  let Msz := AddrSz + 2 - CapBSz in
  let base_masked := Zmod.and (Zmod.and (Zmod.of_Z (2^Msz) (-1)) (Zmod.firstn Msz base))
                              (Zmod.not (Zmod.slu (Zmod.of_Z (2^Msz) (-1)) e)) in
  let length_masked := Zmod.and (Zmod.and (Zmod.of_Z (2^Msz) (-1)) (Zmod.firstn Msz length))
                                (Zmod.not (Zmod.slu (Zmod.of_Z (2^Msz) (-1)) e)) in
  let sum_masked := (base_masked + length_masked)%Zmod in
  let mask_e := Zmod.not (Zmod.slu (Zmod.of_Z (2^Msz) (-1)) e) in
  negb (Zmod.eqb (Zmod.and (Zmod.and (Zmod.of_Z (2^Msz) (-1)) sum_masked) mask_e) (Zmod.zero : bits Msz)) = true ->
  (Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e) mod 2^e <> 0.
Proof.
  intros base length e He Msz base_masked length_masked sum_masked mask_e Hc.
  apply Bool.negb_true_iff in Hc.
  intro Hrem.
  assert (Heq: Zmod.and (Zmod.and (Zmod.of_Z (2^Msz) (-1)) sum_masked) mask_e = Zmod.zero).
  { apply Zmod.unsigned_inj.
    rewrite Zmod.unsigned_0.
    subst mask_e sum_masked.
    rewrite and_mask_e by exact He.
    rewrite and_minus1_mask.
    rewrite Zmod.unsigned_add.
    rewrite mod_mod_mask_e by exact He.
    subst base_masked length_masked Msz.
    rewrite !unsigned_base_masked_mod by exact He.
    exact Hrem. }
  rewrite Heq in Hc.
  rewrite Zmod.eqb_refl in Hc.
  discriminate.
Qed.

Lemma mod_pow2_le : forall b e,
  0 <= b ->
  0 <= e ->
  b mod 2^e <= b mod (2 * 2^e).
Proof.
  intros b e Hb He.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv: (2^e | 2 * 2^e)) by (exists 2; ring).
  replace (b mod 2^e) with ((b mod (2 * 2^e)) mod 2^e).
  - apply Z.mod_le.
    + apply Z.mod_pos_bound; lia.
    + exact Hpos.
  - rewrite (Z.mod_mod_divide b (2 * 2^e) (2^e) Hdiv) by lia.
    reflexivity.
Qed.

Lemma roundUp_ovf_math : forall (l b e : Z),
  0 <= e ->
  0 <= l ->
  0 <= b ->
  2^CapBSz <= (l + b mod 2^e + 2^e - 1) / 2^e ->
  2^(CapBSz - 1) <= (l + b mod (2^(e + 1)) + 2^(e + 1) - 1) / (2^(e + 1)).
Proof.
  intros l b e He Hl Hb Hcap.
  pose proof CapBSz_pos.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(e + 1)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^(e + 1)) with (2 * 2^e) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hpow_step: 2^(CapBSz - 1) * 2 = 2^CapBSz).
  { replace CapBSz with ((CapBSz - 1) + 1) at 2 by lia.
    rewrite Z.pow_add_r by lia. ring. }
  assert (Hge: 2^CapBSz * 2^e <= l + b mod 2^e + 2^e - 1).
  { assert (Hcap_mul: 2^CapBSz * 2^e <= ((l + b mod 2^e + 2^e - 1) / 2^e) * 2^e)
      by (apply Z.mul_le_mono_nonneg_r; [ lia | exact Hcap ]).
    pose proof (Z.mul_div_le (l + b mod 2^e + 2^e - 1) (2^e) Hpos). lia. }
  pose proof (@mod_pow2_le b e Hb He) as Hmod_le.
  assert (Hnum: 2^(CapBSz - 1) * (2 * 2^e) <= l + b mod (2 * 2^e) + 2 * 2^e - 1).
  { replace (2^(CapBSz - 1) * (2 * 2^e)) with ((2^(CapBSz - 1) * 2) * 2^e) by ring.
    rewrite Hpow_step. lia. }
  rewrite (Z.mul_comm (2^(CapBSz - 1)) (2 * 2^e)) in Hnum.
  apply Z.div_le_lower_bound; [ lia | exact Hnum ].
Qed.

Lemma land_shiftl_small : forall x y n,
  0 <= n -> 0 <= x < 2^n -> Z.land x (y * 2^n) = 0.
Proof.
  intros x y n Hn Hx.
  apply Z.bits_inj_iff'; intros k Hk.
  rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_le_dec k n) as [Hlt | Hge].
  - rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r y (k - n)) by lia.
    destruct (Z.testbit x k); reflexivity.
  - assert (Hxk: Z.testbit x k = false).
    { apply Z.testbit_false; try lia.
      assert (Hdiv: x / 2^k = 0).
      { apply Z.div_small; split; try lia.
        eapply Z.lt_le_trans; [ apply Hx | apply Z.pow_le_mono_r; lia ]. }
      rewrite Hdiv; reflexivity. }
    rewrite Hxk; reflexivity.
Qed.

Lemma lor_shiftl_small : forall x y n,
  0 <= n -> 0 <= x < 2^n -> Z.lor x (Z.shiftl y n) = x + y * 2^n.
Proof.
  intros x y n Hn Hx.
  rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.add_lor_land x (y * 2^n)) as Hadd.
  assert (Hland : Z.land x (y * 2^n) = 0) by (apply land_shiftl_small; assumption).
  rewrite Hland in Hadd.
  lia.
Qed.

Lemma unsigned_app_arith : forall (n m : Z) (a : bits n) (b : bits m),
  0 <= n -> 0 <= m ->
  Zmod.unsigned (Zmod.app a b) = Zmod.unsigned a + Zmod.unsigned b * 2^n.
Proof.
  intros n m a b Hn Hm.
  rewrite bits.unsigned_app by lia.
  apply lor_shiftl_small; auto.
  apply bits.unsigned_range; lia.
Qed.

Lemma unsigned_app_CapBSz_sub_1_val : forall (b : bool),
  Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) (if b then (Zmod.one : bits 1) else (Zmod.zero : bits 1)))
                          (Zmod.of_Z (2^(CapBSz - 1)) (2^(CapBSz - 2)) : bits (CapBSz - 1))) =
  2^(CapBSz - 1) + (if b then 1 else 0).
Proof.
  intros b.
  pose proof CapBSz_ge_2.
  rewrite unsigned_app_arith by lia.
  rewrite unsigned_app_arith by lia.
  change (Zmod.unsigned (Zmod.zero : bits 0)) with 0.
  change (2^0) with 1.
  replace (2^(0 + 1)) with 2 by reflexivity.
  assert (Hstep: 2 ^ (CapBSz - 2) * 2 = 2 ^ (CapBSz - 1)).
  { rewrite Z.mul_comm.
    rewrite <- (Z.pow_succ_r 2 (CapBSz - 2)) by lia.
    replace (Z.succ (CapBSz - 2)) with (CapBSz - 1) by lia.
    reflexivity. }
  destruct b.
  - change (Zmod.unsigned (Zmod.one : bits 1)) with 1.
    rewrite Zmod.unsigned_of_Z.
    rewrite Z.mod_small by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite Hstep.
    lia.
  - change (Zmod.unsigned (Zmod.zero : bits 1)) with 0.
    rewrite Zmod.unsigned_of_Z.
    rewrite Z.mod_small by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite Hstep.
    lia.
Qed.

Lemma roundUp_ovf_math_inc : forall (l b e : Z),
  0 <= e ->
  0 <= l ->
  0 <= b ->
  2^CapBSz <= (l + b mod 2^e + 2^e - 1) / 2^e ->
  b mod (2 * 2^e) >= b mod 2^e + 2^e ->
  2^(CapBSz - 1) + 1 <= (l + b mod (2^(e + 1)) + 2^(e + 1) - 1) / (2^(e + 1)).
Proof.
  intros l b e He Hl Hb Hcap Hbe.
  pose proof CapBSz_pos.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(e + 1)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^(e + 1)) with (2 * 2^e) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hpow_step: 2^(CapBSz - 1) * 2 = 2^CapBSz).
  { replace CapBSz with ((CapBSz - 1) + 1) at 2 by lia.
    rewrite Z.pow_add_r by lia. ring. }
  assert (Hge: 2^CapBSz * 2^e <= l + b mod 2^e + 2^e - 1).
  { assert (Hcap_mul: 2^CapBSz * 2^e <= ((l + b mod 2^e + 2^e - 1) / 2^e) * 2^e)
      by (apply Z.mul_le_mono_nonneg_r; [ lia | exact Hcap ]).
    pose proof (Z.mul_div_le (l + b mod 2^e + 2^e - 1) (2^e) Hpos). lia. }
  assert (Hnum: (2^(CapBSz - 1) + 1) * (2 * 2^e) <= l + b mod (2 * 2^e) + 2 * 2^e - 1).
  { replace ((2^(CapBSz - 1) + 1) * (2 * 2^e)) with ((2^(CapBSz - 1) * 2) * 2^e + 2 * 2^e) by ring.
    rewrite Hpow_step.
    lia. }
  rewrite (Z.mul_comm (2^(CapBSz - 1) + 1) (2 * 2^e)) in Hnum.
  apply Z.div_le_lower_bound; [ lia | exact Hnum ].
Qed.

Lemma roundUp_ovf_math_odd : forall (l b e : Z),
  0 <= e ->
  0 <= l ->
  0 <= b ->
  2^CapBSz + 1 <= (l + b mod 2^e + 2^e - 1) / 2^e ->
  2^(CapBSz - 1) + 1 <= (l + b mod (2^(e + 1)) + 2^(e + 1) - 1) / (2^(e + 1)).
Proof.
  intros l b e He Hl Hb Hcap.
  pose proof CapBSz_pos.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(e + 1)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^(e + 1)) with (2 * 2^e) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hpow_step: 2^(CapBSz - 1) * 2 = 2^CapBSz).
  { replace CapBSz with ((CapBSz - 1) + 1) at 2 by lia.
    rewrite Z.pow_add_r by lia. ring. }
  assert (Hge: (2^CapBSz + 1) * 2^e <= l + b mod 2^e + 2^e - 1).
  { assert (Hcap_mul: (2^CapBSz + 1) * 2^e <= ((l + b mod 2^e + 2^e - 1) / 2^e) * 2^e)
      by (apply Z.mul_le_mono_nonneg_r; [ lia | exact Hcap ]).
    pose proof (Z.mul_div_le (l + b mod 2^e + 2^e - 1) (2^e) Hpos). lia. }
  pose proof (@mod_pow2_le b e Hb He) as Hmod_le.
  assert (Hnum: (2^(CapBSz - 1) + 1) * (2 * 2^e) <= l + b mod (2 * 2^e) + 2 * 2^e - 1).
  { replace ((2^(CapBSz - 1) + 1) * (2 * 2^e)) with ((2^(CapBSz - 1) * 2) * 2^e + 2 * 2^e) by ring.
    rewrite Hpow_step.
    lia. }
  rewrite (Z.mul_comm (2^(CapBSz - 1) + 1) (2 * 2^e)) in Hnum.
  apply Z.div_le_lower_bound; [ lia | exact Hnum ].
Qed.

Lemma unsigned_lastn_1_CapBSz_plus1 : forall (x : bits (CapBSz + 1)),
  Zmod.unsigned (Zmod_lastn 1 x) = Zmod.unsigned x / 2^CapBSz.
Proof.
  intros x.
  pose proof CapBSz_pos.
  pose proof (bits.unsigned_range x ltac:(lia)) as [Hx0 Hx1].
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z x) with (Zmod.unsigned x).
  replace (CapBSz + 1 - 1) with CapBSz by ring.
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.mod_small.
  assert (Hpow_step: 2^(CapBSz + 1) = 2 * 2^CapBSz).
  { rewrite Z.pow_add_r by lia. ring. }
  rewrite Hpow_step in Hx1.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma lastn_1_CapBSz_plus1_eq_1 : forall (x : bits (CapBSz + 1)),
  Zmod.eqb (Zmod_lastn 1 x) (Zmod.one : bits 1) = true ->
  2^CapBSz <= Zmod.unsigned x.
Proof.
  intros x H.
  apply Zmod.eqb_eq in H.
  apply (f_equal Zmod.unsigned) in H.
  rewrite unsigned_lastn_1_CapBSz_plus1 in H.
  rewrite Zmod.unsigned_1 in H.
  change (2^1) with 2 in H.
  rewrite Z.mod_small in H by lia.
  assert (Zmod.unsigned x / 2^CapBSz = 1) by exact H.
  pose proof CapBSz_pos.
  assert (Hpos: 0 < 2^CapBSz) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mul_div_le (Zmod.unsigned x) (2^CapBSz) Hpos).
  pose proof (bits.unsigned_range x ltac:(lia)). lia.
Qed.

Lemma unsigned_firstn_1 : forall (n : Z) (x : bits n),
  0 < n ->
  Zmod.unsigned (Zmod.firstn 1 x) = Zmod.unsigned x mod 2.
Proof.
  intros n x Hn.
  unfold Zmod.firstn.
  rewrite Zmod.unsigned_of_Z.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z x) with (Zmod.unsigned x).
  change (2^1) with 2.
  reflexivity.
Qed.

Lemma odd_ge_pow2_implies_ge_succ : forall z k : Z,
  0 < k ->
  2^k <= z ->
  z mod 2 = 1 ->
  2^k + 1 <= z.
Proof.
  intros z k Hk Hge Hodd.
  assert (Hz: z = 2^k \/ 2^k + 1 <= z \/ z < 2^k) by lia.
  destruct Hz as [-> | [H | H]]; [ | exact H | lia ].
  assert (Hdiv: (2 | 2^k)).
  { replace k with (1 + (k - 1)) by lia.
    rewrite Z.pow_add_r by lia.
    exists (2^(k - 1)). ring. }
  apply Z.mod0_divide in Hdiv.
  rewrite Hdiv in Hodd; discriminate.
Qed.

Lemma firstn_1_CapBSz_plus1_eq_1 : forall (x : bits (CapBSz + 1)),
  Zmod.eqb (Zmod.firstn 1 x) (Zmod.one : bits 1) = true ->
  2^CapBSz <= Zmod.unsigned x ->
  2^CapBSz + 1 <= Zmod.unsigned x.
Proof.
  intros x Hlsb Hge.
  apply Zmod.eqb_eq in Hlsb.
  apply (f_equal Zmod.unsigned) in Hlsb.
  pose proof CapBSz_pos.
  assert (Hpos: 0 < CapBSz + 1) by lia.
  rewrite (unsigned_firstn_1 (n:=CapBSz + 1) x Hpos) in Hlsb.
  rewrite Zmod.unsigned_1 in Hlsb.
  change (2^1) with 2 in Hlsb.
  change (1 mod 2) with 1 in Hlsb.
  apply (odd_ge_pow2_implies_ge_succ CapBSz_pos Hge Hlsb).
Qed.

Lemma testbit_true_mod_pow2_ge : forall (b e : Z),
  0 <= e ->
  0 <= b ->
  Z.testbit b e = true ->
  b mod (2 * 2^e) >= b mod 2^e + 2^e.
Proof.
  intros b e He Hb Hbit.
  apply Z.testbit_true in Hbit; [ | lia ].
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod b (2^e) ltac:(lia)) as Hdiv.
  pose proof (Z.div_mod (b / 2^e) 2 ltac:(lia)) as Hdiv2.
  rewrite (Z.mod_eq b (2 * 2^e)) by lia.
  rewrite (Z.mul_comm 2 (2^e)).
  rewrite <- (Z.div_div b (2^e) 2) by lia.
  pose proof (Z.mod_pos_bound b (2^e) Hpos).
  nia.
Qed.

Lemma readNatToFinType_evalFromBitArray_AddrSz : forall (w : bits AddrSz) (i : nat),
  (i < Z.to_nat (AddrSz + 1 - CapBSz))%nat ->
  readNatToFinType false (readSameTuple (@evalFromBitArray (Z.to_nat AddrSz) Bool (fun v => Zmod.eqb v Zmod.one) w)) i =
  Z.testbit (Zmod.unsigned w) (Z.of_nat i).
Proof.
  intros w i.
  let asz := eval compute in (Z.to_nat AddrSz) in
  let sz := eval compute in (Z.to_nat (AddrSz + 1 - CapBSz)) in
  repeat (destruct i as [| i]; [
    intro Hlt; unfold readNatToFinType;
    change (PosDef.Pos.to_nat (Pos.of_succ_nat (Z.to_nat AddrSz - 1))) with asz;
    change (_ <? Z.to_nat AddrSz)%nat with true;
    cbn [readDiffTuple finNum Fst Snd evalFromBit evalOrBinary orb getDefault];
    rewrite readSameTuple_nth with (d := false);
    cbn [finNum]; rewrite evalFromBitArray_nth by (change (Z.to_nat AddrSz) with asz; lia); reflexivity
  | ]);
  intro Hlt; change (Z.to_nat (AddrSz + 1 - CapBSz)) with sz in Hlt; lia.
Qed.

Lemma bounds_length_roundUp_le : forall base length bounds,
  bounds = evalLetExpr (Bounds base length false) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"length") <= ((Zmod.to_Z length + (Zmod.to_Z base mod 2^ef) + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
  intros base length bounds Hbounds.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst outLen cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (e_init_plus_one_val Hclz_bound) as He_plus1_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (He_init_val: Zmod.unsigned e_init = (AddrSz - CapBSz) - Zmod.unsigned clz).
  { rewrite He_init_eq. exact He_val. }
  assert (He_init_plus1_val: Zmod.unsigned (Zmod.add e_init 1) =
    if Zmod.unsigned clz =? 0 then AddrSz + 1 - CapBSz else (AddrSz + 1 - CapBSz) - Zmod.unsigned clz).
  { rewrite He_init_eq. exact He_plus1_val. }
  pose proof CapBSz_pos.
  pose proof CapBSz_lt_AddrSz.
  assert (He_nonneg: 0 <= (AddrSz - CapBSz) - Zmod.unsigned clz) by lia.
  assert (Hb_nonneg: 0 <= Zmod.unsigned base) by solve_unsigned_nonneg.
  assert (Hlen_nonneg: 0 <= Zmod.unsigned length) by solve_unsigned_nonneg.
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
    { subst ef e_normal.
      cbn [evalLetExpr evalExpr].
      destruct isESaturated eqn:Hsat.
      - rewrite (Zmod.unsigned_of_Z (m:=2^ExpSz) (AddrSz + 1 - CapBSz)).
        rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
        rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
        rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
        lia.
      - subst e_unsat.
        cbn [evalLetExpr evalExpr fold_left map].
        rewrite Zmod.add_0_l.
        destruct isOverflow.
        + change (evalExpr $1) with (bits.of_Z ExpSz 1).
          change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
          rewrite He_init_plus1_val.
          destruct (Zmod.unsigned clz =? 0); lia.
        + change (evalExpr $0) with (bits.of_Z ExpSz 0).
          rewrite Zmod.add_0_r.
          rewrite He_init_val.
          lia. }
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  subst ef mf.
  cbn [evalLetExpr evalExpr].
  rewrite Zmod.unsigned_slu.
  rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
  rewrite Z.shiftl_mul_pow2 by solve_unsigned_nonneg.
  eapply Z.le_trans.
  { apply Z.mod_le.
    - apply Z.mul_nonneg_nonneg; [ solve_unsigned_nonneg | apply Z.pow_nonneg; lia ].
    - apply two_pow_AddrSz_add_1_pos. }
  apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
  subst m_normal e_normal.
  cbn [evalLetExpr evalExpr].
  destruct isOverflow eqn:Hovf_is.
  - (* isOverflow = true *)
    subst m_ovf e_unsat.
    cbn [evalLetExpr evalExpr fold_left map evalToBit KindCustomInd].
    rewrite unsigned_app_CapBSz_sub_1_val.
    subst isESaturated.
    set (E_ovf := (e_init + bits.of_Z ExpSz 1)%Zmod) in |- *.
    change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz) in E_ovf.
    assert (HE_ovf_val: Zmod.unsigned E_ovf = if Zmod.unsigned clz =? 0 then AddrSz + 1 - CapBSz else (AddrSz + 1 - CapBSz) - Zmod.unsigned clz).
    { subst E_ovf. rewrite He_init_eq. exact He_plus1_val. }
    unfold Ugt in *; cbn [evalLetExpr evalExpr fold_left map].
    rewrite !Zmod.add_0_l.
    change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
    fold E_ovf in |- *.
    rewrite HE_ovf_val in |- *.
    destruct (Zmod.unsigned clz =? 0) eqn:Hclz0.
    + (* clz = 0 *)
      assert (Hlt: (Zmod.unsigned (bits.of_Z ExpSz (AddrSz - CapBSz)) <? AddrSz + 1 - CapBSz) = true) by reflexivity.
      rewrite Hlt; clear Hlt.
      change (if true then ?A else ?B) with A.
      change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
      rewrite Zmod.unsigned_of_Z.
      rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
      rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
      rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
      destruct inc_ovf eqn:Hinc_val.
      * change (if true then 1 else 0) with 1.
        symmetry in Hinc_ovf.
        cbn [evalLetExpr evalExpr fold_left map evalOrBinary getDefault] in Hinc_ovf.
        apply orb_true_iff in Hinc_ovf.
        destruct Hinc_ovf as [Hlsb | Hbe].
        -- replace (AddrSz + 1 - CapBSz) with ((AddrSz - CapBSz) - Zmod.unsigned clz + 1) by lia.
           apply roundUp_ovf_math_odd; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
           symmetry in HisOverflow.
           cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
           pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_raw.
           cbn [evalOrBinary evalBinary orb KindCustomInd] in Hlsb.
           rewrite Hlsb in Hm_raw_lsb.
           symmetry in Hm_raw_lsb.
           cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in Hm_raw_lsb.
           pose proof (firstn_1_CapBSz_plus1_eq_1 Hm_raw_lsb Hovf_raw) as Hovf_odd_raw.
           eapply Z.le_trans; [ exact Hovf_odd_raw | ].
           eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
             (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
           { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
             rewrite !Zmod.add_0_l.
             rewrite Zmod.unsigned_add.
             eapply Z.le_trans.
             { apply Z.mod_le.
               - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
               - try apply Z.pow_pos_nonneg; lia. }
             apply Z.add_le_mono.
             + subst d. cbn [evalLetExpr evalExpr].
               eapply Z.le_trans.
               - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
                 apply Z.mod_le.
                 * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
                 * try apply Z.pow_pos_nonneg; lia.
               - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
                 rewrite He_init_val.
                 rewrite Z.shiftr_div_pow2 by exact He_nonneg.
                 apply Z.le_refl.
             + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
               rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
               rewrite !Zmod.add_0_l.
               rewrite Zmod.unsigned_add.
               eapply Z.le_trans.
               { apply Z.mod_le.
                 - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                 - change (2^2) with 4; lia. }
               subst iFloor lost_sum.
               cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
               rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
               eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                             Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                            (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
               { apply Z.add_le_mono.
                 - subst sum_mod_e base_mod_e length_mod_e mask_e.
                   cbn [evalLetExpr evalExpr fold_left map].
                   rewrite !Zmod.add_0_l.
                   rewrite He_init_val.
                   apply unsigned_sum_masked_div_le.
                   split; [ exact He_nonneg | lia ].
                 - apply unsigned_if_one_zero. }
               apply carry_bound_math.
               * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * exact He_nonneg.
               * intros Hc.
                 apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
                 -- split; [ exact He_nonneg | lia ].
                 -- subst sum_mod_e base_mod_e length_mod_e mask_e.
                    cbn [evalLetExpr evalExpr fold_left map] in Hc.
                    rewrite !Zmod.add_0_l in Hc.
                    rewrite He_init_val in Hc.
                    exact Hc. }
           rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
           apply Z.le_refl.
        -- replace (AddrSz + 1 - CapBSz) with ((AddrSz - CapBSz) - Zmod.unsigned clz + 1) by lia.
           apply roundUp_ovf_math_inc; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
           symmetry in HisOverflow.
           cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
           pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_raw.
           eapply Z.le_trans; [ exact Hovf_raw | ].
           eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
             (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
           { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
             rewrite !Zmod.add_0_l.
             rewrite Zmod.unsigned_add.
             eapply Z.le_trans.
             { apply Z.mod_le.
               - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
               - try apply Z.pow_pos_nonneg; lia. }
             apply Z.add_le_mono.
             + subst d. cbn [evalLetExpr evalExpr].
               eapply Z.le_trans.
               - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
                 apply Z.mod_le.
                 * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
                 * try apply Z.pow_pos_nonneg; lia.
               - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
                 rewrite He_init_val.
                 rewrite Z.shiftr_div_pow2 by exact He_nonneg.
                 apply Z.le_refl.
             + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
               rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
               rewrite !Zmod.add_0_l.
               rewrite Zmod.unsigned_add.
               eapply Z.le_trans.
               { apply Z.mod_le.
                 - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                 - change (2^2) with 4; lia. }
               subst iFloor lost_sum.
               cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
               rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
               eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                             Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                            (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
               { apply Z.add_le_mono.
                 - subst sum_mod_e base_mod_e length_mod_e mask_e.
                   cbn [evalLetExpr evalExpr fold_left map].
                   rewrite !Zmod.add_0_l.
                   rewrite He_init_val.
                   apply unsigned_sum_masked_div_le.
                   split; [ exact He_nonneg | lia ].
                 - apply unsigned_if_one_zero. }
               apply carry_bound_math.
               * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * exact He_nonneg.
               * intros Hc.
                 apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
                 -- split; [ exact He_nonneg | lia ].
                 -- subst sum_mod_e base_mod_e length_mod_e mask_e.
                    cbn [evalLetExpr evalExpr fold_left map] in Hc.
                    rewrite !Zmod.add_0_l in Hc.
                    rewrite He_init_val in Hc.
                    exact Hc. }
           rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
           apply Z.le_refl.
        ++ subst b_e. cbn [evalLetExpr evalExpr mkBoolArray evalFromBit evalFromBitArray] in Hbe.
           rewrite He_init_val in Hbe.
           change (evalFromBit (k:=Array (Z.to_nat AddrSz) Bool) base) with (@evalFromBitArray (Z.to_nat AddrSz) Bool (fun v => Zmod.eqb v Zmod.one) base) in Hbe.
           assert (Hlt_top: (Z.to_nat (AddrSz - CapBSz - Zmod.unsigned clz) < Z.to_nat (AddrSz + 1 - CapBSz))%nat).
           { apply Nat2Z.inj_lt; rewrite !Z2Nat.id by (pose proof CapBSz_lt_AddrSz; lia); lia. }
           rewrite readNatToFinType_evalFromBitArray_AddrSz in Hbe by exact Hlt_top.
           rewrite Z2Nat.id in Hbe by exact He_nonneg.
           apply testbit_true_mod_pow2_ge; [ exact He_nonneg | exact Hb_nonneg | exact Hbe ].
      * change (if false then 1 else 0) with 0.
        rewrite Z.add_0_r.
        apply Z.eqb_eq in Hclz0.
        replace (AddrSz + 1 - CapBSz) with ((AddrSz - CapBSz) - Zmod.unsigned clz + 1) by lia.
        apply roundUp_ovf_math; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
        symmetry in HisOverflow.
        cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
        pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_raw.
        eapply Z.le_trans; [ exact Hovf_raw | ].
        eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
          (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
        { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
          rewrite !Zmod.add_0_l.
          rewrite Zmod.unsigned_add.
          eapply Z.le_trans.
          { apply Z.mod_le.
            - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
            - try apply Z.pow_pos_nonneg; lia. }
          apply Z.add_le_mono.
          + subst d. cbn [evalLetExpr evalExpr].
            eapply Z.le_trans.
            - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
              apply Z.mod_le.
              * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
              * try apply Z.pow_pos_nonneg; lia.
            - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
              rewrite He_init_val.
              rewrite Z.shiftr_div_pow2 by exact He_nonneg.
              apply Z.le_refl.
          + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
            rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
            rewrite !Zmod.add_0_l.
            rewrite Zmod.unsigned_add.
            eapply Z.le_trans.
            { apply Z.mod_le.
              - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
              - change (2^2) with 4; lia. }
            subst iFloor lost_sum.
            cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
            rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
            eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                          Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                         (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
            { apply Z.add_le_mono.
              - subst sum_mod_e base_mod_e length_mod_e mask_e.
                cbn [evalLetExpr evalExpr fold_left map].
                rewrite !Zmod.add_0_l.
                rewrite He_init_val.
                apply unsigned_sum_masked_div_le.
                split; [ exact He_nonneg | lia ].
              - apply unsigned_if_one_zero. }
            apply carry_bound_math.
            * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * exact He_nonneg.
            * intros Hc.
              apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
              -- split; [ exact He_nonneg | lia ].
              -- subst sum_mod_e base_mod_e length_mod_e mask_e.
                 cbn [evalLetExpr evalExpr fold_left map] in Hc.
                 rewrite !Zmod.add_0_l in Hc.
                 rewrite He_init_val in Hc.
                 exact Hc. }
        rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
        apply Z.le_refl.
    + (* clz > 0 *)
      change (Zmod.unsigned (bits.of_Z ExpSz (AddrSz - CapBSz))) with (AddrSz - CapBSz).
      assert (Hsat: (AddrSz - CapBSz <? (AddrSz + 1 - CapBSz) - Zmod.unsigned clz) = false).
      { apply Z.ltb_ge. destruct (Z.eqb_spec (Zmod.unsigned clz) 0); [ congruence | pose proof (Zmod.unsigned_range clz); lia ]. }
      rewrite Hsat.
      change (if false then ?A else ?B) with B.
      rewrite HE_ovf_val.
      destruct inc_ovf eqn:Hinc_val.
      * change (if true then 1 else 0) with 1.
        symmetry in Hinc_ovf.
        cbn [evalLetExpr evalExpr fold_left map evalOrBinary getDefault] in Hinc_ovf.
        apply orb_true_iff in Hinc_ovf.
        destruct Hinc_ovf as [Hlsb | Hbe].
        -- replace ((AddrSz + 1 - CapBSz) - Zmod.unsigned clz) with ((AddrSz - CapBSz) - Zmod.unsigned clz + 1) by lia.
           apply roundUp_ovf_math_odd; [ exact He_nonneg | exact Hlen_nonneg | exact Hb_nonneg | ].
           symmetry in HisOverflow.
           cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
           pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_raw.
           cbn [evalOrBinary evalBinary orb KindCustomInd] in Hlsb.
           rewrite Hlsb in Hm_raw_lsb.
           symmetry in Hm_raw_lsb.
           cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in Hm_raw_lsb.
           pose proof (firstn_1_CapBSz_plus1_eq_1 Hm_raw_lsb Hovf_raw) as Hovf_odd_raw.
           eapply Z.le_trans; [ exact Hovf_odd_raw | ].
           eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
             (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
           { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
             rewrite !Zmod.add_0_l.
             rewrite Zmod.unsigned_add.
             eapply Z.le_trans.
             { apply Z.mod_le.
               - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
               - try apply Z.pow_pos_nonneg; lia. }
             apply Z.add_le_mono.
             + subst d. cbn [evalLetExpr evalExpr].
               eapply Z.le_trans.
               - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
                 apply Z.mod_le.
                 * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
                 * try apply Z.pow_pos_nonneg; lia.
               - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
                 rewrite He_init_val.
                 rewrite Z.shiftr_div_pow2 by exact He_nonneg.
                 apply Z.le_refl.
             + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
               rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
               rewrite !Zmod.add_0_l.
               rewrite Zmod.unsigned_add.
               eapply Z.le_trans.
               { apply Z.mod_le.
                 - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                 - change (2^2) with 4; lia. }
               subst iFloor lost_sum.
               cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
               rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
               eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                             Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                            (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
               { apply Z.add_le_mono.
                 - subst sum_mod_e base_mod_e length_mod_e mask_e.
                   cbn [evalLetExpr evalExpr fold_left map].
                   rewrite !Zmod.add_0_l.
                   rewrite He_init_val.
                   apply unsigned_sum_masked_div_le.
                   split; [ exact He_nonneg | lia ].
                 - apply unsigned_if_one_zero. }
               apply carry_bound_math.
               * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * exact He_nonneg.
               * intros Hc.
                 apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
                 -- split; [ exact He_nonneg | lia ].
                 -- subst sum_mod_e base_mod_e length_mod_e mask_e.
                    cbn [evalLetExpr evalExpr fold_left map] in Hc.
                    rewrite !Zmod.add_0_l in Hc.
                    rewrite He_init_val in Hc.
                    exact Hc. }
           rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
           apply Z.le_refl.
        -- replace ((AddrSz + 1 - CapBSz) - Zmod.unsigned clz) with ((AddrSz - CapBSz) - Zmod.unsigned clz + 1) by lia.
           apply roundUp_ovf_math_inc; [ exact He_nonneg | exact Hlen_nonneg | exact Hb_nonneg | | ].
           ++ symmetry in HisOverflow.
              cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
              pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_raw.
              eapply Z.le_trans; [ exact Hovf_raw | ].
              eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
              { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
                rewrite !Zmod.add_0_l.
                rewrite Zmod.unsigned_add.
                eapply Z.le_trans.
                { apply Z.mod_le.
                  - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
                  - try apply Z.pow_pos_nonneg; lia. }
                apply Z.add_le_mono.
                + subst d. cbn [evalLetExpr evalExpr].
                  eapply Z.le_trans.
                  - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
                    apply Z.mod_le.
                    * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
                    * try apply Z.pow_pos_nonneg; lia.
                  - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
                    rewrite He_init_val.
                    rewrite Z.shiftr_div_pow2 by exact He_nonneg.
                    apply Z.le_refl.
                + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
                  rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
                  rewrite !Zmod.add_0_l.
                  rewrite Zmod.unsigned_add.
                  eapply Z.le_trans.
                  { apply Z.mod_le.
                    - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                    - change (2^2) with 4; lia. }
                  subst iFloor lost_sum.
                  cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
                  rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
                  eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                                Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                               (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
                  { apply Z.add_le_mono.
                    - subst sum_mod_e base_mod_e length_mod_e mask_e.
                      cbn [evalLetExpr evalExpr fold_left map].
                      rewrite !Zmod.add_0_l.
                      rewrite He_init_val.
                      apply unsigned_sum_masked_div_le.
                      split; [ exact He_nonneg | lia ].
                    - apply unsigned_if_one_zero. }
                  apply carry_bound_math.
                  * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                    apply Z.mod_pos_bound; exact Hpow_pos.
                  * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
                    apply Z.mod_pos_bound; exact Hpow_pos.
                  * exact He_nonneg.
                  * intros Hc.
                    apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
                    -- split; [ exact He_nonneg | lia ].
                    -- subst sum_mod_e base_mod_e length_mod_e mask_e.
                       cbn [evalLetExpr evalExpr fold_left map] in Hc.
                       rewrite !Zmod.add_0_l in Hc.
                       rewrite He_init_val in Hc.
                       exact Hc. }
              rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
              apply Z.le_refl.
           ++ subst b_e. cbn [evalLetExpr evalExpr mkBoolArray evalFromBit evalFromBitArray] in Hbe.
              rewrite He_init_val in Hbe.
              change (evalFromBit (k:=Array (Z.to_nat AddrSz) Bool) base) with (@evalFromBitArray (Z.to_nat AddrSz) Bool (fun v => Zmod.eqb v Zmod.one) base) in Hbe.
              assert (Hlt_top: (Z.to_nat (AddrSz - CapBSz - Zmod.unsigned clz) < Z.to_nat (AddrSz + 1 - CapBSz))%nat).
              { apply Nat2Z.inj_lt; rewrite !Z2Nat.id by (pose proof CapBSz_lt_AddrSz; lia); lia. }
              rewrite readNatToFinType_evalFromBitArray_AddrSz in Hbe by exact Hlt_top.
              rewrite Z2Nat.id in Hbe by exact He_nonneg.
              apply testbit_true_mod_pow2_ge; [ exact He_nonneg | exact Hb_nonneg | exact Hbe ].
      * change (if false then 1 else 0) with 0.
        rewrite Z.add_0_r.
        replace ((AddrSz + 1 - CapBSz) - Zmod.unsigned clz) with ((AddrSz - CapBSz) - Zmod.unsigned clz + 1) by lia.
        apply roundUp_ovf_math; [ exact He_nonneg | exact Hlen_nonneg | exact Hb_nonneg | ].
        symmetry in HisOverflow.
        cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
        pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_raw.
        eapply Z.le_trans; [ exact Hovf_raw | ].
        eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
          (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
        { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
          rewrite !Zmod.add_0_l.
          rewrite Zmod.unsigned_add.
          eapply Z.le_trans.
          { apply Z.mod_le.
            - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
            - try apply Z.pow_pos_nonneg; lia. }
          apply Z.add_le_mono.
          + subst d. cbn [evalLetExpr evalExpr].
            eapply Z.le_trans.
            - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
              apply Z.mod_le.
              * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
              * try apply Z.pow_pos_nonneg; lia.
            - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
              rewrite He_init_val.
              rewrite Z.shiftr_div_pow2 by exact He_nonneg.
              apply Z.le_refl.
          + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
            rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
            rewrite !Zmod.add_0_l.
            rewrite Zmod.unsigned_add.
            eapply Z.le_trans.
            { apply Z.mod_le.
              - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
              - change (2^2) with 4; lia. }
            subst iFloor lost_sum.
            cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
            rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
            eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                          Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                         (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
            { apply Z.add_le_mono.
              - subst sum_mod_e base_mod_e length_mod_e mask_e.
                cbn [evalLetExpr evalExpr fold_left map].
                rewrite !Zmod.add_0_l.
                rewrite He_init_val.
                apply unsigned_sum_masked_div_le.
                split; [ exact He_nonneg | lia ].
              - apply unsigned_if_one_zero. }
            apply carry_bound_math.
            * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * exact He_nonneg.
            * intros Hc.
              apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
              -- split; [ exact He_nonneg | lia ].
              -- subst sum_mod_e base_mod_e length_mod_e mask_e.
                 cbn [evalLetExpr evalExpr fold_left map] in Hc.
                 rewrite !Zmod.add_0_l in Hc.
                 rewrite He_init_val in Hc.
                 exact Hc. }
        rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
        apply Z.le_refl.
  - (* isOverflow = false *)
    subst e_unsat.
    cbn [evalLetExpr evalExpr fold_left map].
    rewrite !Zmod.add_0_l.
    change (evalExpr $0) with (bits.of_Z ExpSz 0).
    rewrite Zmod.add_0_r.
    subst isESaturated.
    unfold Ugt in *; cbn [evalLetExpr evalExpr fold_left map].
    rewrite !Zmod.add_0_l.
    change (bits.of_Z ExpSz 0) with (Zmod.zero : bits ExpSz).
    rewrite !Zmod.add_0_r.
    change (evalExpr $(AddrSz - CapBSz)) with (bits.of_Z ExpSz (AddrSz - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    rewrite Zmod.unsigned_of_Z.
    rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
    rewrite He_init_val.
    assert (Hsat: (AddrSz - CapBSz <? (AddrSz - CapBSz) - Zmod.unsigned clz) = false).
    { apply Z.ltb_ge. lia. }
    rewrite Hsat.
    change (if false then ?A else ?B) with B.
    rewrite He_init_val.
    subst m_raw.
    cbn [evalLetExpr evalExpr fold_left map].
    rewrite !Zmod.add_0_l.
    eapply Z.le_trans.
    { rewrite (unsigned_firstn (n:=CapBSz)) by solve_lia.
      apply Z.mod_le.
      - apply (@to_Z_nonneg (CapBSz + 1)); solve_lia.
      - apply two_pow_CapBSz_pos. }
    rewrite Zmod.unsigned_add.
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
      - try apply Z.pow_pos_nonneg; lia. }
    eapply Z.le_trans with (m := Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
      (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) + 2^((AddrSz - CapBSz) - Zmod.unsigned clz) - 1) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
    { apply Z.add_le_mono.
      + subst d. cbn [evalLetExpr evalExpr].
        eapply Z.le_trans.
        - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
          apply Z.mod_le.
          * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
          * try apply Z.pow_pos_nonneg; lia.
        - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
          rewrite He_init_val.
          rewrite Z.shiftr_div_pow2 by exact He_nonneg.
          apply Z.le_refl.
      + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
        rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
        rewrite !Zmod.add_0_l.
        rewrite Zmod.unsigned_add.
        eapply Z.le_trans.
        { apply Z.mod_le.
          - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
          - change (2^2) with 4; lia. }
        subst iFloor lost_sum.
        cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
        rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
        eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                      Zmod.unsigned length mod 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) / 2^((AddrSz - CapBSz) - Zmod.unsigned clz) +
                                     (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0)).
        { apply Z.add_le_mono.
          - subst sum_mod_e base_mod_e length_mod_e mask_e.
            cbn [evalLetExpr evalExpr fold_left map].
            rewrite !Zmod.add_0_l.
            rewrite He_init_val.
            apply unsigned_sum_masked_div_le.
            split; [ exact He_nonneg | lia ].
          - apply unsigned_if_one_zero. }
        apply carry_bound_math.
        * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
          apply Z.mod_pos_bound; exact Hpow_pos.
        * assert (Hpow_pos: 0 < 2^((AddrSz - CapBSz) - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
          apply Z.mod_pos_bound; exact Hpow_pos.
        * exact He_nonneg.
        * intros Hc.
          apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=(AddrSz - CapBSz) - Zmod.unsigned clz)).
          -- split; [ exact He_nonneg | lia ].
          -- subst sum_mod_e base_mod_e length_mod_e mask_e.
             cbn [evalLetExpr evalExpr fold_left map] in Hc.
             rewrite !Zmod.add_0_l in Hc.
             rewrite He_init_val in Hc.
             exact Hc. }
    rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) ((AddrSz - CapBSz) - Zmod.unsigned clz) He_nonneg Hb_nonneg Hlen_nonneg).
    apply Z.le_refl.
Qed.

Lemma bounds_top_math : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"top") <= ((Zmod.to_Z base + Zmod.to_Z length + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
  intros base length isRoundDown bounds HB ef.
  subst ef.
  unfold Zmod.to_Z in *.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m) in *.
  assert (Hbase_ge0: 0 <= Zmod.unsigned base) by (apply (@to_Z_nonneg AddrSz base); pose proof AddrSz_pos; lia).
  assert (Hlen_ge0: 0 <= Zmod.unsigned length) by (apply (@to_Z_nonneg AddrSz length); pose proof AddrSz_pos; lia).
  eapply (@bounds_top_from_base_len (Zmod.unsigned (bounds@%"top")) (Zmod.unsigned (bounds@%"base")) (Zmod.unsigned (bounds@%"length")) (Zmod.unsigned base) (Zmod.unsigned length) (Zmod.unsigned (evalExpr (get_E_from_cE (bounds@%"cE"))))).
  + apply bounds_E_nonneg with (base:=base) (length:=length) (isRoundDown:=isRoundDown); exact HB.
  + exact Hbase_ge0.
  + exact Hlen_ge0.
  + apply bounds_top_le_add with (base:=base) (length:=length) (isRoundDown:=isRoundDown); exact HB.
  + apply bounds_base_math with (base:=base) (length:=length) (isRoundDown:=isRoundDown); exact HB.
  + destruct isRoundDown.
    * apply (bounds_length_roundDown_le (base:=base) (length:=length) (bounds:=bounds)); exact HB.
    * apply (bounds_length_roundUp_le (base:=base) (length:=length) (bounds:=bounds)); exact HB.
Qed.

(* ========================================================================= *)
(* CAPABILITY BOUNDS ALIGNMENT MULTIPLES                                     *)
(* Establishes that decoded capability base and top are multiples of         *)
(* 2^ECorrected, and proves floor/ceil monotonicity lemmas.                  *)
(* ========================================================================= *)

Lemma ecap_base_multiple : forall cap addr ecap,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  let ECorrected := Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))) in
  Zmod.to_Z (ecap@%"base") mod 2^ECorrected = 0.
Proof.
  intros. subst ECorrected. subst ecap.
  unfold DecodeCap, get_base_top_from_ECorrected_T_B, evalLetExpr, get_ECorrected_from_E, get_E_from_cE.
  cbn -[Zmod.to_Z Zmod.unsigned Zmod.add Zmod.mul Zmod.sub Zmod.sru Zmod.slu Z.pow Z.add Z.mul Z.sub Z.div Z.rem Z.modulo Zmod.slice Zmod.firstn Zmod_lastn Z.shiftr Z.shiftl Zmod.and Zmod.or Zmod.xor Z.lor Z.land].
  change Zmod.Private_to_Z with Zmod.unsigned.
  match goal with
  | |- Zmod.unsigned (Zmod.slu ?X (Zmod.unsigned ?Y)) mod 2^(Zmod.unsigned ?Y) = 0 =>
      rewrite Zmod.unsigned_slu;
      pose proof (bits_ExpSz_range Y) as Hbounds
  end.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply multiple.
  pose proof AddrSz_pos; lia.
Qed.

Lemma ecap_top_multiple : forall cap addr ecap,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  let ECorrected := Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))) in
  Zmod.to_Z (ecap@%"top") mod 2^ECorrected = 0.
Proof.
  intros. subst ECorrected. subst ecap.
  unfold DecodeCap, get_base_top_from_ECorrected_T_B, evalLetExpr, get_ECorrected_from_E, get_E_from_cE.
  cbn -[Zmod.to_Z Zmod.unsigned Zmod.add Zmod.mul Zmod.sub Zmod.sru Zmod.slu Z.pow Z.add Z.mul Z.sub Z.div Z.rem Z.modulo Zmod.slice Zmod.firstn Zmod_lastn Z.shiftr Z.shiftl Zmod.and Zmod.or Zmod.xor Z.lor Z.land].
  change Zmod.Private_to_Z with Zmod.unsigned.
  match goal with
  | |- Zmod.unsigned (Zmod.slu ?X (Zmod.unsigned ?Y)) mod 2^(Zmod.unsigned ?Y) = 0 =>
      rewrite Zmod.unsigned_slu;
      pose proof (bits_ExpSz_range Y) as Hbounds
  end.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply multiple.
  pose proof AddrSz_pos; lia.
Qed.


Lemma ecap_E_nonneg : forall cap addr ecap,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  0 <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))))).
Proof.
  intros. unfold Zmod.to_Z.
  assert (H_pos: 0 < 2 ^ ExpSz) by reflexivity.
  destruct (Zmod.unsigned_range (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))))) as [[H0 H1] | [H0 | [H0 H1]]].
  - exact H0.
  - lia.
  - lia.
Qed.

(** [multiple_divides]:
    Divisibility transfer: since e1 <= e2, any multiple of 2^e2 is also a
    multiple of 2^e1. *)
Lemma multiple_divides : forall e1 e2 x,
  0 <= e1 <= e2 ->
  x mod 2^e2 = 0 ->
  x mod 2^e1 = 0.
Proof.
  intros.
  assert (2^e2 = 2^e1 * 2^(e2 - e1)).
  { rewrite <- Z.pow_add_r; try lia. f_equal. lia. }
  rewrite H1 in H0.
  apply Z.div_exact in H0.
  - rewrite H0.
    assert (2 ^ e1 * 2 ^ (e2 - e1) * (x / (2 ^ e1 * 2 ^ (e2 - e1))) = (2 ^ (e2 - e1) * (x / (2 ^ e1 * 2 ^ (e2 - e1)))) * 2 ^ e1) as H3 by lia.
    rewrite H3.
    apply Z_mod_mult.
  - assert (2 > 0) by lia. assert (0 < 2^e2) by (apply Z.pow_pos_nonneg; lia).
    rewrite <- H1.
    assert (0 < 2^e2) by lia. lia.
Qed.

(** [floor_geq]:
    Floor monotonicity: if b >= ecap_b and ecap_b is aligned to 2^eb,
    then floor(b / 2^eb) * 2^eb >= ecap_b. *)
Lemma floor_geq : forall b eb ecap_b,
  0 <= eb ->
  b >= ecap_b ->
  ecap_b mod 2^eb = 0 ->
  (b / 2^eb) * 2^eb >= ecap_b.
Proof.
  intros.
  assert (0 < 2^eb) by (assert (2 > 0) by lia; apply Z.pow_pos_nonneg; lia).
  assert (2^eb > 0) by lia.
  apply Z.div_exact in H1; try lia.
  rewrite H1.
  assert ( (ecap_b / 2^eb) * 2^eb <= (b / 2^eb) * 2^eb ).
  { apply Z.mul_le_mono_nonneg_r; try lia. apply Z.div_le_mono; lia. }
  lia.
Qed.

(** [ceil_leq]:
    Ceiling monotonicity: if bl <= ecap_top and ecap_top is aligned to 2^eb,
    then ceil((bl + 2^eb - 1) / 2^eb) * 2^eb <= ecap_top. *)
Lemma ceil_leq : forall bl eb ecap_top,
  0 <= eb ->
  bl <= ecap_top ->
  ecap_top mod 2^eb = 0 ->
  (((bl + 2^eb - 1) / 2^eb) * 2^eb <= ecap_top).
Proof.
  intros.
  assert (0 < 2^eb) by (assert (2 > 0) by lia; apply Z.pow_pos_nonneg; lia).
  assert (2^eb > 0) by lia.
  apply Z.div_exact in H1; try lia.
  rewrite H1.
  assert ( (((bl + 2^eb - 1) / 2^eb) * 2^eb) <= (2^eb * (ecap_top / 2^eb)) ).
  { rewrite Z.mul_comm with (n:=2^eb).
    apply Z.mul_le_mono_nonneg_r; try lia.
    assert (bl + 2 ^ eb - 1 <= 2 ^ eb * (ecap_top / 2 ^ eb) + 2 ^ eb - 1) by lia.
    assert ((bl + 2 ^ eb - 1) / 2 ^ eb <= (2 ^ eb * (ecap_top / 2 ^ eb) + 2 ^ eb - 1) / 2 ^ eb).
    { apply Z.div_le_mono; lia. }
    assert ((2 ^ eb * (ecap_top / 2 ^ eb) + 2 ^ eb - 1) / 2 ^ eb = ecap_top / 2 ^ eb).
    { assert (2 ^ eb * (ecap_top / 2 ^ eb) + 2 ^ eb - 1 = (2 ^ eb - 1) + (ecap_top / 2 ^ eb) * 2 ^ eb) as H6 by lia.
      rewrite H6.
      rewrite Z_div_plus; try lia.
      assert ((2^eb - 1) / 2^eb = 0).
      { apply Z.div_small; lia. }
      lia.
    }
    lia.
  }
  lia.
Qed.

Lemma pow2_width sz (w: bits sz): sz >= 0 -> Zmod.to_Z w < Z.pow 2 sz.
Proof.
  intros.
  destruct (Zmod.unsigned_range w) as [[H0 H1] | [H0 | [H0 H1]]].
  - auto.
  - exfalso.
    apply Z.pow_eq_0 in H0; try discriminate.
    lia.
  - lia.
Qed.


(* ========================================================================= *)
(* EXPONENT CONTAINMENT & SPAN BOUND (bounds_E_le_ecap_ECorrected)           *)
(*                                                                           *)
(* Proves that Bounds never selects an exponent higher than the parent       *)
(* capability's corrected exponent (ECorrected). Established from 3 facts:   *)
(*   1. A decoded capability spans <= 2^CapBSz - 1 slots at its own exponent *)
(*      (ecap_span_le).                                                      *)
(*   2. A contained request is therefore <= 2^CapBSz - 1 slots once aligned  *)
(*      (aligned_request_width_le).                                          *)
(*   3. Bounds never selects an exponent above one at which the request      *)
(*      fits (bounds_E_le_aligned_width).                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Bit-vector value helpers                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma unsigned_bit_le_1 : forall (h : bits 1), 0 <= Zmod.unsigned h <= 1.
Proof.
  intros h. pose proof (bits.unsigned_range h ltac:(lia)) as Hr.
  assert (H2 : 2 ^ 1 = 2) by reflexivity. lia.
Qed.

Lemma unsigned_nonzero : forall (n : Z) (x : bits n),
  Zmod.eqb x 0 = false -> Zmod.unsigned x <> 0.
Proof.
  intros n x Hx Hcontra.
  assert (x = 0%Zmod).
  { apply Zmod.unsigned_inj. rewrite Hcontra, Zmod.unsigned_0. reflexivity. }
  subst x. rewrite (proj2 (Zmod.eqb_eq _ _)) in Hx by reflexivity. discriminate.
Qed.

Lemma unsigned_sub_bit_AddrSz_sub_CapBSz : forall (x : bits (AddrSz - CapBSz)) (h : bits 1),
  Zmod.unsigned x <> 0 ->
  Zmod.unsigned (0 + x + Zmod.not (Zmod.app h (0 : bits (AddrSz - CapBSz - 1))) + 1)%Zmod
    = Zmod.unsigned x - Zmod.unsigned h.
Proof.
  intros x h Hx.
  pose proof (bits.unsigned_range x ltac:(pose proof AddrSz_sub_CapBSz_pos; lia)) as Hxr.
  pose proof (unsigned_bit_le_1 h) as Hhr.
  rewrite !Zmod.unsigned_add.
  rewrite bits.unsigned_not'.
  rewrite unsigned_app_arith by (pose proof AddrSz_sub_CapBSz_pos; lia).
  rewrite !Zmod.unsigned_0, Zmod.unsigned_1.
  rewrite Z.ones_equiv.
  assert (Hp : 2 ^ (1 + (AddrSz - CapBSz - 1)) = 2 ^ (AddrSz - CapBSz)).
  { replace (1 + (AddrSz - CapBSz - 1)) with (AddrSz - CapBSz) by lia. reflexivity. }
  rewrite Hp.
  assert (Hpos : 0 < 2 ^ (AddrSz - CapBSz)) by (apply Z.pow_pos_nonneg; pose proof AddrSz_sub_CapBSz_nonneg; lia).
  rewrite (Z.mod_small 1) by (pose proof (Z.pow_gt_1 2 (AddrSz - CapBSz)); pose proof AddrSz_sub_CapBSz_pos; lia).
  rewrite (Z.mod_small (0 + Zmod.unsigned x)) by lia.
  rewrite !Z.add_mod_idemp_l by lia.
  replace (0 + Zmod.unsigned x +
           (Z.pred (2 ^ (AddrSz - CapBSz)) - (Zmod.unsigned h + 0 * 2 ^ 1)) + 1)
     with (Zmod.unsigned x - Zmod.unsigned h + 1 * 2 ^ (AddrSz - CapBSz)) by lia.
  rewrite Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Arithmetic core of the span bound                                         *)
(* ------------------------------------------------------------------------- *)

Lemma pow_split : forall x y, 0 <= x -> 0 <= y -> 2^x * 2^y = 2^(x + y).
Proof. intros. rewrite <- Z.pow_add_r by lia. reflexivity. Qed.

Lemma span_arith : forall (e a A ATB ut Tu Bu : Z),
  0 <= e <= AddrSz + 1 - CapBSz ->
  0 <= a < 2^AddrSz ->
  A = a / 2^(e + CapBSz) ->
  0 <= ATB <= A ->
  0 <= Tu < 2^CapBSz -> 0 <= Bu < 2^CapBSz ->
  (ut = 1 /\ Tu < Bu) \/ (ut = 0 /\ Bu <= Tu) ->
  Z.shiftl (0 + Tu * 1 + ((0 + ATB + ut) mod 2^(AddrSz - CapBSz)) * 2^CapBSz + 0 * 2^AddrSz) e mod 2^(AddrSz + 2)
  - Z.shiftl (0 + Bu * 1 + ATB * 2^CapBSz + 0 * 2^AddrSz) e mod 2^(AddrSz + 1) <= (2^CapBSz - 1) * 2^e.
Proof.
  intros e a A ATB ut Tu Bu He Ha HA HATB HT HB Hut.
  pose proof CapBSz_pos.
  pose proof CapBSz_lt_AddrSz.
  assert (Hp : 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hd : 0 < 2^(e + CapBSz)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hd_eq : 2^(e + CapBSz) = 2^CapBSz * 2^e).
  { rewrite <- pow_split by lia. ring. }
  assert (HAnn : 0 <= A) by (subst A; apply Z.div_pos; lia).
  assert (HAd : A * 2^(e + CapBSz) <= a).
  { subst A. pose proof (Z.mul_div_le a (2^(e+CapBSz)) Hd). lia. }
  assert (He_top : e = AddrSz + 1 - CapBSz -> A = 0).
  { intros Hee. rewrite HA. apply Z.div_small. split; try lia.
    assert (2^AddrSz <= 2^(e + CapBSz)); [ apply Z.pow_le_mono_r; lia | lia ]. }
  assert (Hbig : e <= AddrSz - CapBSz -> 2^CapBSz * (A + 1) * 2^e <= 2^AddrSz).
  { intros Hle_mid.
    assert (Hprod : 2^(e + CapBSz) * 2^(AddrSz - CapBSz - e) = 2^AddrSz).
    { rewrite pow_split by lia. f_equal. lia. }
    assert (Hprod' : 2^(AddrSz - CapBSz - e) * 2^(e + CapBSz) = 2^AddrSz) by (rewrite <- Hprod; ring).
    assert (HA1 : A + 1 <= 2^(AddrSz - CapBSz - e)).
    { assert (A < 2^(AddrSz - CapBSz - e)); [ | lia ].
      rewrite HA. apply Z.div_lt_upper_bound; lia. }
    assert (Hstep : (A + 1) * 2^(e + CapBSz) <= 2^(AddrSz - CapBSz - e) * 2^(e + CapBSz)).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    rewrite Hprod' in Hstep.
    rewrite Hd_eq in Hstep.
    replace (2^CapBSz * (A + 1) * 2^e) with ((A + 1) * (2^CapBSz * 2^e)) by ring.
    exact Hstep. }
  assert (Hsmall : e <= AddrSz - CapBSz -> 2^(e + CapBSz) <= 2^AddrSz)
    by (intros; apply Z.pow_le_mono_r; lia).
  rewrite !Z.shiftl_mul_pow2 by lia.
  destruct (Z_lt_le_dec (ATB + ut) (2^(AddrSz - CapBSz))) as [Hnowrap | Hwrap].
  - (* no wrap of the reconstructed top mantissa: exact arithmetic *)
    assert (Hutn : 0 <= ut <= 1) by lia.
    rewrite (Z.mod_small (0 + ATB + ut)) by lia.
    assert (HVB : (0 + Bu * 1 + ATB * 2^CapBSz + 0 * 2^AddrSz) * 2^e < 2^(AddrSz + 1)).
    { assert (H33 : 2^(AddrSz + 1) = 2 * 2^AddrSz).
      { replace (AddrSz + 1) with (Z.succ AddrSz) by lia. rewrite Z.pow_succ_r by lia. ring. }
      destruct (Z.eq_dec e (AddrSz + 1 - CapBSz)) as [Hee | Hee].
      - assert (ATB = 0) by (pose proof (He_top Hee); lia).
        assert (Hstep : (0 + Bu * 1 + ATB * 2^CapBSz + 0 * 2^AddrSz) * 2^e < 2^CapBSz * 2^e)
          by (apply Z.mul_lt_mono_pos_r; lia).
        rewrite <- Hd_eq in Hstep.
        assert (H2e_CapBSz : 2^(e + CapBSz) = 2^(AddrSz + 1)) by (rewrite Hee; f_equal; lia). lia.
      - assert (Hstep : (0 + Bu * 1 + ATB * 2^CapBSz + 0 * 2^AddrSz) * 2^e < (2^CapBSz * (A + 1)) * 2^e).
        { apply Z.mul_lt_mono_pos_r; [ lia | ].
          replace (2^CapBSz * (A + 1)) with (A * 2^CapBSz + 2^CapBSz) by ring.
          assert (ATB * 2^CapBSz <= A * 2^CapBSz) by (apply Z.mul_le_mono_nonneg_r; lia).
          lia. }
        assert (2^CapBSz * (A + 1) * 2^e <= 2^AddrSz) by (apply Hbig; lia). lia. }
    assert (HVT : (0 + Tu * 1 + (0 + ATB + ut) * 2^CapBSz + 0 * 2^AddrSz) * 2^e < 2^(AddrSz + 2)).
    { assert (Hpow_AddrSz_add_2 : 2^(AddrSz + 2) = 4 * 2^AddrSz).
      { replace (AddrSz + 2) with (AddrSz + 1 + 1) by lia.
        rewrite !Z.pow_add_r by lia. ring. }
      destruct (Z.eq_dec e (AddrSz + 1 - CapBSz)) as [Hee | Hee].
      - assert (ATB = 0) by (pose proof (He_top Hee); lia).
        assert (Hstep : (0 + Tu * 1 + (0 + ATB + ut) * 2^CapBSz + 0 * 2^AddrSz) * 2^e < (2 * 2^CapBSz) * 2^e)
          by (apply Z.mul_lt_mono_pos_r; lia).
        assert (Hd2 : (2 * 2^CapBSz) * 2^e = 2 * 2^(e + CapBSz)) by (rewrite Hd_eq; ring).
        assert (H2e_CapBSz : 2 * 2^(e + CapBSz) = 2^(AddrSz + 2)).
        { rewrite Hee. replace (AddrSz + 1 - CapBSz + CapBSz) with (AddrSz + 1) by lia.
          replace (AddrSz + 2) with (Z.succ (AddrSz + 1)) by lia.
          rewrite Z.pow_succ_r by lia. ring. }
        lia.
      - assert (Hstep : (0 + Tu * 1 + (0 + ATB + ut) * 2^CapBSz + 0 * 2^AddrSz) * 2^e
                        < (2^CapBSz * (A + 1) + 2^CapBSz) * 2^e).
        { apply Z.mul_lt_mono_pos_r; [ lia | ].
          replace (2^CapBSz * (A + 1) + 2^CapBSz) with (A * 2^CapBSz + 2 * 2^CapBSz) by ring.
          replace ((0 + ATB + ut) * 2^CapBSz) with (ATB * 2^CapBSz + ut * 2^CapBSz) by ring.
          assert (ATB * 2^CapBSz <= A * 2^CapBSz) by (apply Z.mul_le_mono_nonneg_r; lia).
          assert (ut * 2^CapBSz <= 1 * 2^CapBSz) by (apply Z.mul_le_mono_nonneg_r; lia).
          lia. }
        assert (Hexp : (2^CapBSz * (A + 1) + 2^CapBSz) * 2^e = 2^CapBSz * (A + 1) * 2^e + 2^(e + CapBSz))
          by (rewrite Hd_eq; ring).
        assert (2^CapBSz * (A + 1) * 2^e <= 2^AddrSz) by (apply Hbig; lia).
        assert (2^(e + CapBSz) <= 2^AddrSz) by (apply Hsmall; lia). lia. }
    rewrite (Z.mod_small ((0 + Tu * 1 + (0 + ATB + ut) * 2^CapBSz + 0 * 2^AddrSz) * 2^e)) by
      (split; [ apply Z.mul_nonneg_nonneg; lia | exact HVT ]).
    rewrite (Z.mod_small ((0 + Bu * 1 + ATB * 2^CapBSz + 0 * 2^AddrSz) * 2^e)) by
      (split; [ apply Z.mul_nonneg_nonneg; lia | exact HVB ]).
    replace ((0 + Tu * 1 + (0 + ATB + ut) * 2^CapBSz + 0 * 2^AddrSz) * 2^e
             - (0 + Bu * 1 + ATB * 2^CapBSz + 0 * 2^AddrSz) * 2^e)
       with ((Tu - Bu + 2^CapBSz * ut) * 2^e) by ring.
    apply Z.mul_le_mono_nonneg_r; [ lia | ].
    destruct Hut as [[Hut1 Ht] | [Hut0 Ht]]; subst ut; lia.
  - (* wrap: only possible when e = 0, and then the decoded top is below the decoded base *)
    assert (Hutn : 0 <= ut <= 1) by lia.
    assert (He0 : e = 0).
    { destruct (Z.eq_dec e 0) as [| Hne]; auto.
      exfalso.
      assert (HAsmall : 2 * A < 2^(AddrSz - CapBSz)).
      { assert (H2Cap : 0 < 2^CapBSz) by (apply Z.pow_pos_nonneg; lia).
        assert (Hpow_split : 2^(AddrSz - CapBSz) * 2^CapBSz = 2^AddrSz).
        { rewrite pow_split by lia. replace (AddrSz - CapBSz + CapBSz) with AddrSz by lia. reflexivity. }
        assert (Hgrow : 2 * 2^CapBSz <= 2^(e + CapBSz)).
        { replace (2 * 2^CapBSz) with (2^(CapBSz + 1)).
          - apply Z.pow_le_mono_r; lia.
          - replace (CapBSz + 1) with (Z.succ CapBSz) by lia.
            rewrite Z.pow_succ_r by lia. ring. }
        assert (Hstep : (2 * A) * 2^CapBSz <= A * 2^(e + CapBSz)).
        { replace ((2 * A) * 2^CapBSz) with (A * (2 * 2^CapBSz)) by ring.
          apply Z.mul_le_mono_nonneg_l; lia. }
        assert (Hstep2 : (2 * A) * 2^CapBSz < 2^(AddrSz - CapBSz) * 2^CapBSz).
        { rewrite Hpow_split. lia. }
        apply <- (Z.mul_lt_mono_pos_r (2^CapBSz)) in Hstep2; [ | exact H2Cap ].
        exact Hstep2. }
      assert (2 <= 2^(AddrSz - CapBSz)).
      { change 2 with (2^1). apply Z.pow_le_mono_r; lia. }
      lia. }
    subst e.
    assert (HAmax : A <= 2^(AddrSz - CapBSz) - 1).
    { assert (A < 2^(AddrSz - CapBSz)); [ | lia ].
      rewrite HA.
      replace (0 + CapBSz) with CapBSz by lia.
      apply Z.div_lt_upper_bound.
      - apply Z.pow_pos_nonneg; lia.
      - rewrite pow_split by lia.
        replace (CapBSz + (AddrSz - CapBSz)) with AddrSz by lia.
        lia. }
    assert (HATBv : ATB = 2^(AddrSz - CapBSz) - 1 /\ ut = 1) by (split; lia).
    destruct HATBv as [HATBv Hutv]. rewrite HATBv, Hutv.
    replace (0 + (2^(AddrSz - CapBSz) - 1) + 1) with (2^(AddrSz - CapBSz)) by lia.
    rewrite Z_mod_same_full.
    change (2^0) with 1.
    rewrite (Z.mod_small ((0 + Tu * 1 + 0 * 2^CapBSz + 0 * 2^AddrSz) * 1)) by
      (split; [ lia | assert (2^CapBSz < 2^(AddrSz + 2)) by (apply Z.pow_lt_mono_r; lia); lia ]).
    rewrite (Z.mod_small ((0 + Bu * 1 + (2^(AddrSz - CapBSz) - 1) * 2^CapBSz + 0 * 2^AddrSz) * 1)) by
      (split; [ lia | assert (Bu + (2^(AddrSz - CapBSz) - 1) * 2^CapBSz < 2^AddrSz) by
        (assert (Bu < 2^CapBSz) by lia;
         replace ((2^(AddrSz - CapBSz) - 1) * 2^CapBSz) with (2^(AddrSz - CapBSz) * 2^CapBSz - 2^CapBSz) by ring;
         rewrite pow_split by lia;
         replace (AddrSz - CapBSz + CapBSz) with AddrSz by lia; lia);
       assert (2^AddrSz < 2^(AddrSz + 1)) by (apply Z.pow_lt_mono_r; lia); lia ]).
    lia.
Qed.

Lemma unsigned_bit_if : forall (c : bool),
  Zmod.unsigned (if c then 1%Zmod else 0%Zmod : bits 1) = if c then 1 else 0.
Proof. intros [];reflexivity. Qed.

Lemma app_0_val : forall (t : bits 1),
  Zmod.unsigned (Zmod.app t (0 : bits (AddrSz - CapBSz - 1))) = Zmod.unsigned t.
Proof.
  intros t.
  assert (Hpos : 0 <= AddrSz - CapBSz - 1) by (pose proof AddrSz_sub_CapBSz_pos; lia).
  pose proof (bits.unsigned_app t (0 : bits (AddrSz - CapBSz - 1)) ltac:(lia) Hpos) as Happ.
  rewrite Happ.
  rewrite Zmod.unsigned_0, Z.shiftl_0_l, Z.lor_0_r.
  reflexivity.
Qed.

Lemma aTopT_val : forall (X : bits (AddrSz - CapBSz)) (t : bits 1),
  Zmod.unsigned (0 + X + Zmod.app t (0 : bits (AddrSz - CapBSz - 1)))%Zmod
    = (0 + Zmod.unsigned X + Zmod.unsigned t) mod 2^(AddrSz - CapBSz).
Proof.
  intros X t.
  assert (Hpos : 0 < 2 ^ (AddrSz - CapBSz)) by (apply Z.pow_pos_nonneg; pose proof AddrSz_sub_CapBSz_nonneg; lia).
  rewrite !Zmod.unsigned_add.
  rewrite app_0_val.
  rewrite !Zmod.unsigned_0.
  rewrite Z.add_mod_idemp_l by lia.
  reflexivity.
Qed.

Lemma aTopB_bound : forall (aTop : bits (AddrSz - CapBSz)) (h : bits 1) (X : bits (AddrSz - CapBSz)),
  X = (if negb (Zmod.eqb aTop 0)
       then (0 + aTop + Zmod.not (Zmod.app h (0 : bits (AddrSz - CapBSz - 1))) + 1)%Zmod
       else 0%Zmod) ->
  0 <= Zmod.unsigned X <= Zmod.unsigned aTop.
Proof.
  intros aTop h X HX.
  pose proof (bits.unsigned_range aTop ltac:(pose proof AddrSz_sub_CapBSz_pos; lia)) as Har.
  pose proof (unsigned_bit_le_1 h) as Hhr.
  destruct (Zmod.eqb aTop 0) eqn:Haz; cbn [negb] in HX; subst X.
  - rewrite Zmod.unsigned_0. lia.
  - assert (Hne : Zmod.unsigned aTop <> 0)
      by (apply unsigned_nonzero with (n := (AddrSz - CapBSz)); exact Haz).
    rewrite unsigned_sub_bit_AddrSz_sub_CapBSz by exact Hne.
    lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Decoded span bound                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma base_top_shape : forall (addr : type Addr) (EC : type (Bit ExpSz))
                              (T : type (Bit CapBSz)) (B : type (Bit CapBSz)),
  Zmod.unsigned EC <= AddrSz + 1 - CapBSz ->
  let bt := evalLetExpr (get_base_top_from_ECorrected_T_B addr EC T B) in
  Zmod.to_Z (bt@%"top") - Zmod.to_Z (bt@%"base") <= (2^CapBSz - 1) * 2^(Zmod.to_Z EC).
Proof.
  intros addr EC T B HEC bt. subst bt.
  unfold get_base_top_from_ECorrected_T_B, evalLetExpr.
  cbn -[Zmod.to_Z Zmod.unsigned Zmod.add Zmod.mul Zmod.sub Zmod.sru Zmod.slu Z.pow Z.add Z.mul Z.sub Z.div Z.rem Z.modulo Zmod.slice Zmod.firstn Zmod_lastn Z.shiftr Z.shiftl Zmod.and Zmod.or Zmod.xor Z.lor Z.land].
  change Zmod.Private_to_Z with Zmod.unsigned.
  set (e := Zmod.unsigned EC) in *.
  set (am := Zmod.sru addr e) in *.
  rewrite !Zmod.unsigned_slu.
  rewrite !unsigned_app_arith by (pose proof AddrSz_pos; pose proof CapBSz_pos; pose proof AddrSz_sub_CapBSz_pos; lia).
  rewrite !Zmod.unsigned_0.
  change (2 ^ 0) with 1.
  replace (0 + CapBSz) with CapBSz by lia.
  replace (CapBSz + (AddrSz - CapBSz) + (AddrSz + 2 - (CapBSz + (AddrSz - CapBSz)))) with (AddrSz + 2) by lia.
  replace (CapBSz + (AddrSz - CapBSz) + (AddrSz + 1 - (CapBSz + (AddrSz - CapBSz)))) with (AddrSz + 1) by lia.
  replace (CapBSz + (AddrSz - CapBSz)) with AddrSz by lia.
  (* basic ranges *)
  assert (He0 : 0 <= e).
  { unfold e. pose proof (bits_ExpSz_range EC). lia. }
  assert (Hae : 0 <= Zmod.unsigned addr < 2 ^ AddrSz).
  { apply (bits.unsigned_range (n := AddrSz)). apply AddrSz_nonneg. }
  pose proof (bits.unsigned_range T ltac:(pose proof CapBSz_pos; lia)) as HTr.
  pose proof (bits.unsigned_range B ltac:(pose proof CapBSz_pos; lia)) as HBr.
  (* value of the decoded address high word *)
  assert (Haval : Zmod.unsigned (Zmod_lastn (AddrSz - CapBSz) am) = Zmod.unsigned addr / 2 ^ (e + CapBSz)).
  { unfold am. rewrite unsigned_lastn_AddrSz_sub_CapBSz.
    rewrite unsigned_sru_pos by (pose proof AddrSz_pos; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hpe : 0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
    assert (Hpow : 2 ^ e * 2 ^ CapBSz = 2 ^ (e + CapBSz)).
    { rewrite <- pow_split by (pose proof CapBSz_pos; lia). reflexivity. }
    rewrite Z.div_div by (pose proof two_pow_CapBSz_pos; lia).
    rewrite Hpow. reflexivity. }
  (* reconstructed top mantissa *)
  rewrite aTopT_val.
  rewrite !unsigned_bit_if.
  match goal with
  | |- context [ Zmod.unsigned ?X * 2 ^ CapBSz ] => remember X as ATBx eqn:HATBx
  end.
  assert (HATBr : 0 <= Zmod.unsigned ATBx <= Zmod.unsigned (Zmod_lastn (AddrSz - CapBSz) am)).
  { eapply aTopB_bound. exact HATBx. }
  eapply span_arith with (a := Zmod.unsigned addr) (A := Zmod.unsigned addr / 2 ^ (e + CapBSz)).
  - lia.
  - exact Hae.
  - reflexivity.
  - rewrite <- Haval. exact HATBr.
  - lia.
  - lia.
  - destruct (Zmod.unsigned T <? Zmod.unsigned B) eqn:Ht.
    + left. split; [ reflexivity | apply Z.ltb_lt; exact Ht ].
    + right. split; [ reflexivity | apply Z.ltb_ge; exact Ht ].
Qed.

(* ------------------------------------------------------------------------- *)
(* Connecting the span bound to DecodeCap                                    *)
(* ------------------------------------------------------------------------- *)

Lemma ECorrected_le_Emax : forall (cap : type Cap),
  Zmod.unsigned (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))) <= Emax.
Proof.
  intros cap.
  unfold get_ECorrected_from_E, get_E_from_cE.
  cbn -[Zmod.unsigned Zmod.to_Z Z.pow].
  change Zmod.Private_to_Z with Zmod.unsigned.
  assert (HEmax : Zmod.unsigned (Zmod.of_Z (2^ExpSz) Emax) = Emax).
  { rewrite Zmod.unsigned_of_Z.
    apply Z.mod_small.
    pose proof two_pow_ExpSz_eq_AddrSz.
    pose proof Emax_nonneg. pose proof Emax_lt_AddrSz. lia. }
  rewrite HEmax.
  match goal with
  | |- context [ if ?c then _ else _ ] => destruct c eqn:Hb
  end.
  - lia.
  - apply negb_false_iff in Hb. apply Z.ltb_lt in Hb. lia.
Qed.

Lemma decode_base_top : forall (cap : type Cap) (addr : type Addr),
  let EC := evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))) in
  let T := evalLetExpr (get_T_from_cE_cT_B (cap@%"cE") (cap@%"cT") (cap@%"B")) in
  let bt := evalLetExpr (get_base_top_from_ECorrected_T_B addr EC T (cap@%"B")) in
  (evalLetExpr (DecodeCap cap addr))@%"base" = bt@%"base" /\
  (evalLetExpr (DecodeCap cap addr))@%"top" = bt@%"top".
Proof.
  intros. split; reflexivity.
Qed.

Lemma ecap_span_le : forall cap addr ecap,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  let ECorrected := Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))) in
  Zmod.to_Z (ecap@%"top") - Zmod.to_Z (ecap@%"base") <= (2^CapBSz - 1) * 2^ECorrected.
Proof.
  intros cap addr ecap Hecap EC. subst ecap EC.
  destruct (decode_base_top cap addr) as [Hb Ht].
  cbn zeta in Hb, Ht.
  rewrite Hb, Ht.
  apply base_top_shape.
  rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
  apply ECorrected_le_Emax.
Qed.

(* ------------------------------------------------------------------------- *)
(* Aligned containment width                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma mod_le_self_pos : forall x d,
  0 <= x -> 0 < d -> x mod d <= x.
Proof.
  intros x d Hx Hd.
  destruct (Z_lt_le_dec x d) as [Hlt | Hge].
  - rewrite Z.mod_small; lia.
  - pose proof (Z.mod_pos_bound x d Hd) as [_ Hmod_lt].
    lia.
Qed.

Lemma aligned_request_width_le : forall e cap_base cap_top base length span,
  0 <= e ->
  cap_base mod 2^e = 0 ->
  cap_base <= base ->
  base + length <= cap_top ->
  0 <= length ->
  cap_top - cap_base <= span ->
  base mod 2^e + length <= span.
Proof.
  intros e cap_base cap_top base length span He Hcap_mod Hcap_le Htop Hlen Hspan.
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdelta_nonneg: 0 <= base - cap_base) by lia.
  assert (Hbase_mod: base mod 2^e = (base - cap_base) mod 2^e).
  { replace base with (cap_base + (base - cap_base)) at 1 by lia.
    rewrite Z.add_mod by lia.
    rewrite Hcap_mod.
    rewrite Z.add_0_l.
    rewrite Z.mod_mod by lia.
    reflexivity. }
  rewrite Hbase_mod.
  pose proof (mod_le_self_pos Hdelta_nonneg Hpow_pos) as Hdelta_mod_le.
  lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Arithmetic core of the no-overflow argument                               *)
(* ------------------------------------------------------------------------- *)

Lemma no_ovf_arith : forall (p B0 L iF lost : Z),
  0 < p ->
  0 <= B0 < p ->
  0 <= L ->
  B0 + L <= (2^CapBSz - 1) * p ->
  0 <= iF ->
  iF <= (B0 + L mod p) / p ->
  0 <= lost <= 1 ->
  (lost = 1 -> (B0 + L mod p) mod p <> 0) ->
  L / p + iF + lost <= 2^CapBSz - 1.
Proof.
  intros p B0 L iF lost Hp HB0 HL Hwidth HiF0 HiF Hlost Hlost1.
  pose proof (Z.div_mod L p ltac:(lia)) as HLdm.
  pose proof (Z.mod_pos_bound L p Hp) as Hr.
  set (q := L / p) in *.
  set (r := L mod p) in *.
  set (s := B0 + r) in *.
  pose proof (Z.div_mod s p ltac:(lia)) as Hsdm.
  pose proof (Z.mod_pos_bound s p Hp) as Hsr.
  assert (Hqs : q * p + s <= (2^CapBSz - 1) * p) by lia.
  assert (Hfp : (s / p) * p <= s) by lia.
  destruct (Z.eq_dec lost 1) as [Hl1 | Hl0].
  - assert (Hne : s mod p <> 0) by (apply Hlost1; exact Hl1).
    assert (Hge1 : 1 <= s mod p) by lia.
    assert (Hstep : (q + s / p) * p <= (2^CapBSz - 1) * p - 1) by nia.
    assert (q + s / p <= 2^CapBSz - 2) by (pose proof two_pow_CapBSz_pos; nia).
    lia.
  - assert (Hstep : (q + s / p) * p <= (2^CapBSz - 1) * p) by nia.
    assert (q + s / p <= 2^CapBSz - 1) by (pose proof two_pow_CapBSz_pos; nia).
    lia.
Qed.

Lemma bounds_E_le_aligned_width : forall base length isRoundDown bounds e,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  0 <= e <= AddrSz - CapBSz ->
  Zmod.to_Z base mod 2^e + Zmod.to_Z length <= (2^CapBSz - 1) * 2^e ->
  Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) <= e.
Proof.
  intros base length isRoundDown bounds e Hbounds He Hwidth.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  unfold Zmod.to_Z in *.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m) in *.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (e_init_plus_one_val Hclz_bound) as He_plus1_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (He_init_val: Zmod.unsigned e_init = (AddrSz - CapBSz) - Zmod.unsigned clz).
  { rewrite He_init_eq. exact He_val. }
  assert (He_init_plus1_val: Zmod.unsigned (Zmod.add e_init 1) =
    if Zmod.unsigned clz =? 0 then AddrSz + 1 - CapBSz else (AddrSz + 1 - CapBSz) - Zmod.unsigned clz).
  { rewrite He_init_eq. exact He_plus1_val. }
  pose proof CapBSz_pos.
  pose proof CapBSz_lt_AddrSz.
  assert (He_nonneg: 0 <= (AddrSz - CapBSz) - Zmod.unsigned clz) by lia.
  assert (Hb_nonneg: 0 <= Zmod.unsigned base) by solve_unsigned_nonneg.
  assert (Hlen_nonneg: 0 <= Zmod.unsigned length) by solve_unsigned_nonneg.
  assert (Hpow_e : 0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hbmod : 0 <= Zmod.unsigned base mod 2 ^ e) by (apply Z.mod_pos_bound; lia).
  assert (Heinit_le : (AddrSz - CapBSz) - Zmod.unsigned clz <= e).
  { destruct (Z_le_gt_dec ((AddrSz - CapBSz) - Zmod.unsigned clz) e) as [Hle | Hgt]; auto.
    exfalso.
    assert (Hclz_bound' : Zmod.unsigned clz <= AddrSz - CapBSz - 1) by lia.
    assert (Hlen_ge : 2^(AddrSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned length).
    { apply length_ge_pow2_clz.
      - subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray.
      - exact Hclz_bound'. }
    assert (Hpow_e_CapBSz : 2 ^ (e + CapBSz) <= 2 ^ (AddrSz - 1 - Zmod.unsigned clz)).
    { apply Z.pow_le_mono_r; lia. }
    rewrite Z.pow_add_r in Hpow_e_CapBSz by lia.
    lia. }
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
    { subst ef.
      destruct isRoundDown.
      - subst e_roundDown pick_b.
        cbn [evalLetExpr evalExpr].
        subst e_init.
        cbn [evalLetExpr evalExpr fold_left map evalNot].
        rewrite Zmod.add_0_l.
        change (evalNot clz) with (Zmod.not clz).
        change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
        destruct (_ <? _) eqn:H_slt.
        + apply Z.ltb_lt in H_slt.
          rewrite He_val in H_slt.
          lia.
        + rewrite He_val.
          lia.
      - subst e_normal.
        cbn [evalLetExpr evalExpr].
        destruct isESaturated eqn:Hsat.
        + rewrite (Zmod.unsigned_of_Z (m:=2^ExpSz) (AddrSz + 1 - CapBSz)).
          rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
          rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
          rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
          lia.
        + subst e_unsat.
          cbn [evalLetExpr evalExpr fold_left map].
          rewrite Zmod.add_0_l.
          destruct isOverflow.
          * change (evalExpr $1) with (bits.of_Z ExpSz 1).
            change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
            rewrite He_init_plus1_val.
            destruct (Zmod.unsigned clz =? 0); lia.
          * change (evalExpr $0) with (bits.of_Z ExpSz 0).
            rewrite Zmod.add_0_r.
            rewrite He_init_val.
            lia. }
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  subst ef.
  destruct isRoundDown.
  - subst e_roundDown.
    cbn [evalLetExpr evalExpr].
    destruct pick_b.
    + cbn [evalLetExpr evalExpr] in Hpick_b |- *.
      apply eq_sym in Hpick_b.
      apply Z.ltb_lt in Hpick_b.
      rewrite He_init_val in Hpick_b.
      lia.
    + rewrite He_init_val.
      exact Heinit_le.
  - subst e_normal.
    cbn [evalLetExpr evalExpr].
    destruct isOverflow eqn:Hovf.
    + (* isOverflow = true *)
      assert (Hlt : (AddrSz - CapBSz) - Zmod.unsigned clz < e).
      { destruct (Z.eq_dec ((AddrSz - CapBSz) - Zmod.unsigned clz) e) as [Heq | Hne].
        2: lia.
        exfalso.
        symmetry in HisOverflow.
        cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
        pose proof (lastn_1_CapBSz_plus1_eq_1 HisOverflow) as Hovf_lastn.
        assert (Hm_raw_le: Zmod.unsigned m_raw <= Zmod.unsigned length / 2^e +
          ((Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e) / 2^e +
          (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0))).
        { subst m_raw. cbn [evalLetExpr evalExpr fold_left map].
          rewrite !Zmod.add_0_l.
          rewrite Zmod.unsigned_add.
          eapply Z.le_trans.
          { apply Z.mod_le.
            - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg (CapBSz + 1)); pose proof CapBSz_pos; lia.
            - try apply Z.pow_pos_nonneg; lia. }
          apply Z.add_le_mono.
          + subst d. cbn [evalLetExpr evalExpr].
            eapply Z.le_trans.
            - rewrite (unsigned_firstn (n:=CapBSz + 1)) by (pose proof CapBSz_pos; lia).
              apply Z.mod_le.
              * apply (@to_Z_nonneg AddrSz); pose proof AddrSz_pos; lia.
              * try apply Z.pow_pos_nonneg; lia.
            - rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
              rewrite He_init_val.
              rewrite Heq.
              rewrite Z.shiftr_div_pow2 by lia.
              apply Z.le_refl.
          + subst iCeil. cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
            rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
            rewrite !Zmod.add_0_l.
            rewrite Zmod.unsigned_add.
            eapply Z.le_trans.
            { apply Z.mod_le.
              - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
              - change (2^2) with 4; lia. }
            subst iFloor lost_sum.
            cbn [evalLetExpr evalExpr fold_left map ZeroExtendTo evalToBit isNotZero].
            rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
            apply Z.add_le_mono.
            - subst sum_mod_e base_mod_e length_mod_e mask_e.
              cbn [evalLetExpr evalExpr fold_left map].
              rewrite !Zmod.add_0_l.
              rewrite He_init_val.
              rewrite Heq.
              apply unsigned_sum_masked_div_le.
              split; [ lia | lia ].
            - apply unsigned_if_one_zero. }
        assert (Hno_ovf: Zmod.unsigned length / 2^e +
          (Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e) / 2^e +
          (if negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0) then 1 else 0) <= 2^CapBSz - 1).
        { eapply no_ovf_arith with (B0 := Zmod.unsigned base mod 2^e).
          - exact Hpow_e.
          - split; [ exact Hbmod | apply Z.mod_pos_bound; exact Hpow_e ].
          - exact Hlen_nonneg.
          - exact Hwidth.
          - apply Z.div_pos; [ | exact Hpow_e ].
            apply Z.add_nonneg_nonneg; [ exact Hbmod | apply Z.mod_pos_bound; exact Hpow_e ].
          - apply Z.le_refl.
          - destruct (negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0)); lia.
          - intros Hlost1.
            destruct (negb (Zmod.eqb (evalExpr (And [#sum_mod_e; #mask_e])) 0)) eqn:Hcond; [ | discriminate ].
            apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=e)).
            + split; [ lia | lia ].
            + subst sum_mod_e base_mod_e length_mod_e mask_e.
              cbn [evalLetExpr evalExpr fold_left map] in Hcond.
              rewrite !Zmod.add_0_l in Hcond.
              rewrite He_init_val in Hcond.
              rewrite Heq in Hcond.
              exact Hcond. }
        lia. }
      assert (Hclz_nz: Zmod.unsigned clz <> 0) by lia.
      apply Z.eqb_neq in Hclz_nz.
      subst isESaturated.
      unfold Ugt.
      cbn [evalLetExpr evalExpr fold_left map].
      subst e_unsat.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite !Zmod.add_0_l.
      change (evalExpr $1) with (bits.of_Z ExpSz 1).
      change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
      rewrite He_init_plus1_val.
      rewrite Hclz_nz.
      change (evalExpr $(AddrSz - CapBSz)) with (bits.of_Z ExpSz (AddrSz - CapBSz)).
      change (bits.of_Z ExpSz (AddrSz - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz - CapBSz)).
      rewrite Zmod.unsigned_of_Z.
      rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
      assert (Hsat: (AddrSz - CapBSz <? (AddrSz + 1 - CapBSz) - Zmod.unsigned clz) = false).
      { apply Z.ltb_ge. lia. }
      rewrite Hsat.
      change (if false then ?A else ?B) with B.
      rewrite He_init_plus1_val.
      rewrite Hclz_nz.
      lia.
    + (* isOverflow = false *)
      subst isESaturated e_unsat.
      unfold Ugt.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite !Zmod.add_0_l.
      change (evalExpr $0) with (bits.of_Z ExpSz 0).
      rewrite Zmod.add_0_r.
      change (evalExpr $(AddrSz - CapBSz)) with (bits.of_Z ExpSz (AddrSz - CapBSz)).
      change (bits.of_Z ExpSz (AddrSz - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz - CapBSz)).
      rewrite Zmod.unsigned_of_Z.
      rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
      rewrite He_init_val.
      assert (Hsat: (AddrSz - CapBSz <? (AddrSz - CapBSz) - Zmod.unsigned clz) = false).
      { apply Z.ltb_ge. lia. }
      rewrite Hsat.
      change (if false then ?A else ?B) with B.
      rewrite He_init_val.
      exact Heinit_le.
Qed.

(* ------------------------------------------------------------------------- *)
(* Selected exponent never exceeds saturation bound (bounds_E_le_Emax)       *)
(* ------------------------------------------------------------------------- *)

Lemma bounds_E_le_Emax : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) <= Emax.
Proof.
  intros base length isRoundDown bounds Hbounds.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  unfold Zmod.to_Z in *.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m) in *.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (e_init_plus_one_val Hclz_bound) as He_plus1_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (He_init_val: Zmod.unsigned e_init = (AddrSz - CapBSz) - Zmod.unsigned clz).
  { rewrite He_init_eq. exact He_val. }
  assert (He_init_plus1_val: Zmod.unsigned (Zmod.add e_init 1) =
    if Zmod.unsigned clz =? 0 then AddrSz + 1 - CapBSz else (AddrSz + 1 - CapBSz) - Zmod.unsigned clz).
  { rewrite He_init_eq. exact He_plus1_val. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof CapBSz_pos.
  pose proof CapBSz_lt_AddrSz.
  assert (H_ef_bound: Zmod.unsigned ef <= Emax).
  { rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
    subst ef.
    destruct isRoundDown.
    - subst e_roundDown pick_b.
      cbn [evalLetExpr evalExpr].
      subst e_init.
      cbn [evalLetExpr evalExpr fold_left map evalNot].
      rewrite Zmod.add_0_l.
      change (evalNot clz) with (Zmod.not clz).
      change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
      destruct (_ <? _) eqn:H_slt.
      + apply Z.ltb_lt in H_slt.
        rewrite He_val in H_slt.
        lia.
      + rewrite He_val.
        lia.
    - subst e_normal.
      cbn [evalLetExpr evalExpr].
      destruct isESaturated eqn:Hsat.
      + rewrite (Zmod.unsigned_of_Z (m:=2^ExpSz) (AddrSz + 1 - CapBSz)).
        rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
        rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
        rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
        lia.
      + subst e_unsat.
        cbn [evalLetExpr evalExpr fold_left map].
        rewrite Zmod.add_0_l.
        destruct isOverflow.
        * change (evalExpr $1) with (bits.of_Z ExpSz 1).
          change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
          rewrite He_init_plus1_val.
          destruct (Zmod.unsigned clz =? 0); lia.
        * change (evalExpr $0) with (bits.of_Z ExpSz 0).
          rewrite Zmod.add_0_r.
          rewrite He_init_val.
          lia. }
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    rewrite Emax_eq_AddrSz_add_1_sub_CapBSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  exact H_ef_bound.
Qed.

(* ------------------------------------------------------------------------- *)
(* Exponent comparison: bounds_E_le_ecap_ECorrected                          *)
(* ------------------------------------------------------------------------- *)

Lemma bounds_E_le_ecap_ECorrected :
  forall cap addr base length isRoundDown ecap bounds,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\
    Zmod.to_Z base + Zmod.to_Z length <= Zmod.to_Z (ecap@%"top") ->
  Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE")))
    <= Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))).
Proof.
  intros cap addr base length isRoundDown ecap bounds Hecap Hbounds [Hge Hle].
  pose proof (@ECorrected_le_Emax cap) as HECmax.
  pose proof (@ecap_E_nonneg cap addr ecap Hecap) as HEC0.
  destruct (Z.eq_dec
              (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))
              Emax) as [HEmax | Hne].
  - rewrite HEmax. eapply bounds_E_le_Emax. exact Hbounds.
  - eapply bounds_E_le_aligned_width.
    + exact Hbounds.
    + unfold Zmod.to_Z in *. rewrite <- Emax_minus_1_eq_AddrSz_sub_CapBSz. lia.
    + eapply aligned_request_width_le with
        (cap_base := Zmod.to_Z (ecap@%"base")) (cap_top := Zmod.to_Z (ecap@%"top")).
      * unfold Zmod.to_Z in *. lia.
      * eapply ecap_base_multiple. exact Hecap.
      * lia.
      * lia.
      * apply (@to_Z_nonneg AddrSz). apply AddrSz_nonneg.
      * eapply ecap_span_le. exact Hecap.
Qed.

(* ========================================================================= *)
(* Final Complete Theorem: BoundsMonotonic                                   *)
(* ========================================================================= *)

Theorem BoundsMonotonic cap addr base length isRoundDown:
  let ecap : type ECap := evalLetExpr (DecodeCap cap addr) in
  let bounds : type BoundsRes := evalLetExpr (Bounds base length isRoundDown) in
  (Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z base + Zmod.to_Z length <= Zmod.to_Z (ecap@%"top")) ->
  (Zmod.to_Z (bounds@%"base") >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (bounds@%"top") <= Zmod.to_Z (ecap@%"top")).
Proof.
  intros ecap bounds H_in_bounds.
  destruct H_in_bounds as [H_base_ge H_top_le].

  assert (H_no_wrap : Zmod.to_Z base + Zmod.to_Z length < Z.pow 2 (AddrSz + 1)).
  { assert (Hb_lt : Zmod.to_Z base < Z.pow 2 AddrSz) by (apply pow2_width; pose proof AddrSz_pos; lia).
    assert (Hl_lt : Zmod.to_Z length < Z.pow 2 AddrSz) by (apply pow2_width; pose proof AddrSz_pos; lia).
    replace (Z.pow 2 (AddrSz + 1)) with (2 * Z.pow 2 AddrSz)
      by (rewrite Z.pow_add_r by (pose proof AddrSz_pos; lia); ring).
    lia.
  }

  assert (H_E_nonneg : 0 <= Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE")))).
  { eapply bounds_E_nonneg with (base:=base) (length:=length) (isRoundDown:=isRoundDown); reflexivity. }

  assert (H_ecap_E_nonneg : 0 <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))).
  { eapply ecap_E_nonneg with (cap:=cap) (addr:=addr); reflexivity. }

  assert (HE : Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))).
  { eapply bounds_E_le_ecap_ECorrected with (cap:=cap) (addr:=addr) (base:=base) (length:=length) (isRoundDown:=isRoundDown).
    - reflexivity.
    - reflexivity.
    - split; assumption.
  }

  assert (H_base_math: Zmod.to_Z (bounds@%"base") = (Zmod.to_Z base / 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))))) * 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))))) by (eapply bounds_base_math with (base:=base) (length:=length) (isRoundDown:=isRoundDown); reflexivity).

  assert (H_top_math: Zmod.to_Z (bounds@%"top") <= ((Zmod.to_Z base + Zmod.to_Z length + 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE")))) - 1) / 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))))) * 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))))).
  { eapply bounds_top_math with (base:=base) (length:=length) (isRoundDown:=isRoundDown); auto. }

  assert (H_ecap_base: Zmod.to_Z (ecap@%"base") mod 2^((Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))) = 0) by (eapply ecap_base_multiple with (cap:=cap) (addr:=addr); reflexivity).

  assert (H_ecap_top: Zmod.to_Z (ecap@%"top") mod 2^((Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))) = 0) by (eapply ecap_top_multiple with (cap:=cap) (addr:=addr); reflexivity).

  assert (H_ecap_base_mod_eb: Zmod.to_Z (ecap@%"base") mod 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE")))) = 0).
  { eapply multiple_divides; try eassumption; lia. }

  assert (H_ecap_top_mod_eb: Zmod.to_Z (ecap@%"top") mod 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE")))) = 0).
  { eapply multiple_divides; try eassumption; lia. }

  split.
  - rewrite H_base_math.
    apply floor_geq; try eassumption; eauto.
  - eapply Z.le_trans.
    + apply H_top_math.
    + apply ceil_leq; try eassumption; eauto.
Qed.

(* ========================================================================= *)
(* COMMON BOUNDS PROPERTIES (ROUNDUP & ROUNDDOWN)                            *)
(* Shared properties of the Bounds functional unit output:                   *)
(*   - Top equals base plus length (bounds_top_eq)                           *)
(*   - Base floor containment: bounds.base <= base (bounds_base_le)          *)
(*   - Length representation: bounds.length = m * 2^e (bounds_length_m_e)   *)
(*   - Minimality of top bound (bounds_roundUp_min)                          *)
(* ========================================================================= *)

Lemma bounds_top_eq : forall (base length : bits AddrSz) (isRoundDown : bool) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z (bounds@%"top") = Zmod.to_Z (bounds@%"base") + Zmod.to_Z (bounds@%"length").
Proof.
  intros base length isRoundDown bounds HB.
  pose proof (bounds_top_rel HB) as H_top.
  rewrite H_top.
  apply Z.mod_small.
  assert (Hb: 0 <= Zmod.to_Z (bounds@%"base") < 2^(AddrSz + 1)).
  { unfold Zmod.to_Z. change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
    apply (bits.unsigned_range (bounds@%"base") ltac:(pose proof AddrSz_pos; lia)). }
  assert (Hl: 0 <= Zmod.to_Z (bounds@%"length") < 2^(AddrSz + 1)).
  { unfold Zmod.to_Z. change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
    apply (bits.unsigned_range (bounds@%"length") ltac:(pose proof AddrSz_pos; lia)). }
  split.
  - lia.
  - replace (2^(AddrSz + 2)) with (2 * 2^(AddrSz + 1)).
    + lia.
    + replace (AddrSz + 2) with (Z.succ (AddrSz + 1)) by lia.
      rewrite Z.pow_succ_r; [ ring | pose proof AddrSz_pos; lia ].
Qed.

Lemma bounds_base_le : forall (base length : bits AddrSz) (isRoundDown : bool) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z (bounds@%"base") <= Zmod.to_Z base.
Proof.
  intros base length isRoundDown bounds HB.
  pose proof (bounds_base_math HB) as Hbase.
  rewrite Hbase.
  assert (Hpos: 0 < 2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))))).
  { apply Z.pow_pos_nonneg; [ lia | apply bounds_E_nonneg with (base:=base) (length:=length) (isRoundDown:=isRoundDown); exact HB ]. }
  pose proof (Z.mul_div_le (Zmod.to_Z base) (2^(Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))))) Hpos).
  lia.
Qed.

Lemma bounds_roundUp_min : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length false) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"top") - 2^ef < Zmod.to_Z base + Zmod.to_Z length.
Proof.
  intros base length bounds HB ef.
  pose proof (bounds_top_math HB) as Htop.
  change (let ef0 := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
          Zmod.to_Z (bounds@%"top") <= ((Zmod.to_Z base + Zmod.to_Z length + 2^ef0 - 1) / 2^ef0) * 2^ef0)
    with (Zmod.to_Z (bounds@%"top") <= ((Zmod.to_Z base + Zmod.to_Z length + 2^ef - 1) / 2^ef) * 2^ef) in Htop.
  pose proof (bounds_E_nonneg HB) as Hef.
  assert (Hpos: 0 < 2^ef).
  { apply Z.pow_pos_nonneg; [ lia | exact Hef ]. }
  pose proof (Z.mul_div_le (Zmod.to_Z base + Zmod.to_Z length + 2^ef - 1) (2^ef) Hpos) as Hdiv.
  lia.
Qed.

Lemma ceil_sum_mod_ge : forall sum_mod e,
  0 <= e ->
  0 <= sum_mod ->
  (sum_mod / 2^e + (if (sum_mod mod 2^e =? 0) then 0 else 1)) * 2^e >= sum_mod.
Proof.
  intros sum_mod e He Hsum.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod sum_mod (2^e) (ltac:(lia))) as Hdiv.
  pose proof (Z.mod_pos_bound sum_mod (2^e) Hpos) as Hmod.
  destruct (sum_mod mod 2^e =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. lia.
  - apply Z.eqb_neq in Hz. lia.
Qed.

Lemma base_div_pow2_succ : forall b e,
  0 <= e ->
  (b / 2^(e + 1)) * 2^(e + 1) = (b / 2^e) * 2^e - ((b / 2^e) mod 2) * 2^e.
Proof.
  intros b e He.
  replace (2^(e + 1)) with (2^e * 2) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.div_div by lia.
  rewrite (Z.div_mod (b / 2^e) 2) at 2 by lia.
  ring.
Qed.

Lemma roundUp_ovf_ge : forall (m_raw : Z) (b_e : Z) (inc_ovf : bool),
  (m_raw = 2^CapBSz \/ m_raw = 2^CapBSz + 1) ->
  (b_e = 0 \/ b_e = 1) ->
  inc_ovf = (m_raw mod 2 =? 1) || (b_e =? 1) ->
  let m := 2^(CapBSz - 1) + (if inc_ovf then 1 else 0) in
  m_raw <= 2 * m - b_e.
Proof.
  intros m_raw b_e inc_ovf Hraw Hbe Hinc m.
  subst m.
  pose proof CapBSz_pos.
  assert (Hpow_step: 2 * 2^(CapBSz - 1) = 2^CapBSz).
  { replace CapBSz with (Z.succ (CapBSz - 1)) at 2 by lia.
    rewrite Z.pow_succ_r by lia. ring. }
  assert (Hmod2: 2^CapBSz mod 2 = 0).
  { rewrite <- Hpow_step. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
  assert (Hmod2_succ: (2^CapBSz + 1) mod 2 = 1).
  { replace (2^CapBSz + 1) with (1 + 2^(CapBSz - 1) * 2) by (rewrite <- Hpow_step; ring).
    rewrite Z.mod_add by lia. reflexivity. }
  destruct Hraw as [Hraw | Hraw]; destruct Hbe as [Hbe | Hbe];
  subst m_raw b_e; rewrite Hinc; cbn;
  try rewrite Hmod2; try rewrite Hmod2_succ; cbn; lia.
Qed.

Lemma roundUp_ovf_ge_general : forall (m_raw : Z) (b_e : Z) (inc_ovf : bool) (m : Z),
  m_raw <= 2^CapBSz + 1 ->
  (b_e = 0 \/ b_e = 1) ->
  m = 2^(CapBSz - 1) + (if inc_ovf then 1 else 0) ->
  inc_ovf = (m_raw mod 2 =? 1) || (b_e =? 1) ->
  m_raw <= 2 * m - b_e.
Proof.
  intros m_raw b_e inc_ovf m Hraw_le Hbe Hm Hinc.
  subst m.
  pose proof CapBSz_pos.
  assert (Hpow_step: 2 * 2^(CapBSz - 1) = 2^CapBSz).
  { replace CapBSz with (Z.succ (CapBSz - 1)) at 2 by lia.
    rewrite Z.pow_succ_r by lia. ring. }
  assert (Hcases: m_raw <= 2^CapBSz - 1 \/ m_raw = 2^CapBSz \/ m_raw = 2^CapBSz + 1) by lia.
  destruct Hcases as [Hsmall | [Heq1 | Heq2]].
  - destruct Hbe as [Hbe | Hbe]; subst b_e; destruct inc_ovf; rewrite ?Hpow_step; lia.
  - apply (roundUp_ovf_ge (or_introl Heq1) Hbe Hinc).
  - apply (roundUp_ovf_ge (or_intror Heq2) Hbe Hinc).
Qed.

Lemma roundUp_step2_math : forall (b len e d base_mod_e len_mod_e iCeil m_raw : Z),
  0 <= e ->
  0 <= len ->
  0 <= b ->
  0 <= base_mod_e ->
  0 <= len_mod_e ->
  base_mod_e < 2^e ->
  len_mod_e < 2^e ->
  b = (b / 2^e) * 2^e + base_mod_e ->
  len = d * 2^e + len_mod_e ->
  m_raw = d + iCeil ->
  (base_mod_e + len_mod_e <= iCeil * 2^e) ->
  b + len <= (b / 2^e) * 2^e + m_raw * 2^e.
Proof.
  intros b len e d base_mod_e len_mod_e iCeil m_raw
         He Hlen Hb Hbm Hlm Hbm_lt Hlm_lt Hb_eq Hlen_eq Hm_raw Hceil.
  rewrite Hlen_eq, Hm_raw.
  rewrite Hb_eq at 1.
  replace (((b / 2^e) * 2^e + base_mod_e) + (d * 2^e + len_mod_e)) with (((b / 2^e) * 2^e + d * 2^e) + (base_mod_e + len_mod_e)) by ring.
  replace ((b / 2^e) * 2^e + (d + iCeil) * 2^e) with (((b / 2^e) * 2^e + d * 2^e) + iCeil * 2^e) by ring.
  apply Z.add_le_mono_l.
  exact Hceil.
Qed.

Lemma roundUp_step3_ovf_math : forall (c1_base b_e e m m_raw : Z),
  0 <= e ->
  (m_raw <= 2 * m - b_e) ->
  c1_base + m_raw * 2^e <= (c1_base - b_e * 2^e) + m * (2 * 2^e).
Proof.
  intros c1_base b_e e m m_raw He Hcov.
  assert (Hpos: 0 <= 2^e) by (apply Z.pow_nonneg; lia).
  replace (m * (2 * 2^e)) with ((2 * m) * 2^e) by ring.
  replace ((c1_base - b_e * 2^e) + 2 * m * 2^e) with (c1_base + (2 * m - b_e) * 2^e) by ring.
  apply Z.add_le_mono_l.
  apply Z.mul_le_mono_nonneg_r; [ exact Hpos | exact Hcov ].
Qed.

Lemma bounds_roundDown_top_le : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length true) ->
  Zmod.to_Z (bounds@%"top") <= Zmod.to_Z base + Zmod.to_Z length.
Proof.
  intros base length bounds HB.
  pose proof (bounds_top_eq HB) as Htop.
  rewrite Htop.
  pose proof (bounds_base_le HB) as Hbase.
  pose proof (bounds_roundDown_length_le HB) as Hlen.
  lia.
Qed.

Lemma bounds_length_m_e : forall (base length : bits AddrSz) (isRoundDown : bool) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  let e := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  let m := Zmod.to_Z (bounds@%"m") in
  let outLength := Zmod.to_Z (bounds@%"length") in
  outLength = m * 2^e.
Proof.
  intros base length isRoundDown bounds HB.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst outLen cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (e_init_plus_one_val Hclz_bound) as He_plus1_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
  { subst ef.
    cbn [evalLetExpr evalExpr].
    destruct isRoundDown.
    - subst e_roundDown.
      cbn [evalLetExpr evalExpr].
      destruct pick_b.
      + cbn [evalLetExpr evalExpr] in Hpick_b.
        apply eq_sym in Hpick_b.
        apply Z.ltb_lt in Hpick_b.
        rewrite He_init_eq, He_val in Hpick_b.
        lia.
      + rewrite He_init_eq, He_val. lia.
    - subst e_normal.
      cbn [evalLetExpr evalExpr].
      destruct isESaturated eqn:Hsat.
      + rewrite (Zmod.unsigned_of_Z (m:=2^ExpSz) (AddrSz + 1 - CapBSz)).
        rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
        rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
        rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
        lia.
      + subst e_unsat.
        cbn [evalLetExpr evalExpr fold_left map].
        rewrite Zmod.add_0_l.
        destruct isOverflow.
        * change (evalExpr $1) with (bits.of_Z ExpSz 1).
          change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
          rewrite He_init_eq.
          rewrite He_plus1_val.
          destruct (Zmod.unsigned clz =? 0); lia.
        * change (evalExpr $0) with (bits.of_Z ExpSz 0).
          rewrite Zmod.add_0_r.
          rewrite He_init_eq, He_val.
          lia. }
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  cbn [evalLetExpr evalExpr].
  unfold Zmod.to_Z.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  rewrite Zmod.unsigned_slu.
  rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
  rewrite Z.shiftl_mul_pow2 by solve_unsigned_nonneg.
  apply Z.mod_small.
  assert (Hmf_range: 0 <= Zmod.unsigned mf < 2^CapBSz).
  { apply (bits.unsigned_range mf). pose proof CapBSz_pos. lia. }
  assert (Hef_min: 0 <= Zmod.unsigned ef) by (pose proof (bits_ExpSz_range ef); lia).
  split.
  - apply Z.mul_nonneg_nonneg; [ lia | apply Z.pow_nonneg; lia ].
  - eapply Z.lt_le_trans with (m := 2^CapBSz * 2^(Zmod.unsigned ef)).
    + apply Z.mul_lt_mono_pos_r; [ apply Z.pow_pos_nonneg; lia | lia ].
    + eapply Z.le_trans with (m := 2^CapBSz * 2^(AddrSz + 1 - CapBSz)).
      * apply Z.mul_le_mono_nonneg_l; [ pose proof two_pow_CapBSz_pos; lia | apply Z.pow_le_mono_r; lia ].
      * replace (2^CapBSz * 2^(AddrSz + 1 - CapBSz)) with (2^(CapBSz + (AddrSz + 1 - CapBSz))).
        -- replace (CapBSz + (AddrSz + 1 - CapBSz)) with (AddrSz + 1) by lia. lia.
        -- rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). ring.
Qed.


(* ========================================================================= *)
(* ROUNDUP SPECIFICATION: COVERING & NORMALIZATION HELPERS                   *)
(* Arithmetic and bitwise lemmas supporting RoundUp covering and             *)
(* mantissa normalization properties.                                        *)
(* ========================================================================= *)

Lemma testbit_false_lt_pow2 : forall (a k : Z),
  0 <= a ->
  0 <= k ->
  a < 2^(k + 1) ->
  Z.testbit a k = false ->
  a < 2^k.
Proof.
  intros a k Ha Hk Hlt Hbit.
  apply Z.testbit_false in Hbit; [ | lia ].
  assert (Hdiv: a / 2^k < 2).
  { apply Z.div_lt_upper_bound; [ apply Z.pow_pos_nonneg; lia | ].
    replace (2^k * 2) with (2^(k + 1)).
    - exact Hlt.
    - rewrite Z.pow_add_r by lia. ring. }
  assert (Hdiv_ge: 0 <= a / 2^k) by (apply Z.div_pos; lia).
  assert (Hdiv_0: a / 2^k = 0).
  { pose proof (Z.div_mod (a / 2^k) 2 ltac:(lia)) as Hdm.
    rewrite Hbit in Hdm.
    destruct (a / 2^k =? 0) eqn:Heq.
    - apply Z.eqb_eq in Heq. exact Heq.
    - apply Z.eqb_neq in Heq. lia. }
  destruct (Z_lt_le_dec a (2^k)) as [Hsmall | Hlarge]; [ exact Hsmall | ].
  assert (1 <= a / 2^k) by (apply Z.div_le_lower_bound; [ apply Z.pow_pos_nonneg; lia | lia ]).
  lia.
Qed.

Lemma countLeadingZerosLoop_lt_pow2 : forall (w : bits (AddrSz - CapBSz)) (count : nat) (accum : bits ExpSz),
  (count <= Z.to_nat (AddrSz - CapBSz))%nat ->
  Zmod.unsigned accum = (AddrSz - CapBSz - Z.of_nat count) ->
  Zmod.unsigned w < 2^(Z.of_nat count) ->
  Zmod.unsigned w < 2^(AddrSz - CapBSz - Zmod.unsigned (evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) w)) count false accum))).
Proof.
  induction count as [| count' IHcount']; intros accum Hcount Haccum Hw_lt.
  - simpl countLeadingZerosLoop.
    cbn [evalLetExpr evalExpr].
    rewrite Haccum.
    change (Z.of_nat 0) with 0 in *.
    replace (AddrSz - CapBSz - (AddrSz - CapBSz - 0)) with 0 by lia.
    exact Hw_lt.
  - rewrite countLeadingZerosLoop_step.
    rewrite eval_readNatToFinType_mkBoolArray by lia.
    destruct (Z.testbit (Zmod.unsigned w) (Z.of_nat count')) eqn:Hbit.
    + cbv zeta iota.
      rewrite Haccum.
      replace (AddrSz - CapBSz - (AddrSz - CapBSz - Z.of_nat (S count'))) with (Z.of_nat (S count')) by lia.
      exact Hw_lt.
    + cbv zeta iota.
      apply IHcount'.
      * lia.
      * rewrite unsigned_add_1_bits; [ | apply ExpSz_pos | ].
        { rewrite Haccum. lia. }
        rewrite Haccum.
        rewrite two_pow_ExpSz_eq_AddrSz.
        pose proof CapBSz_pos. lia.
      * apply testbit_false_lt_pow2.
        -- pose proof (bits.unsigned_range w ltac:(pose proof AddrSz_sub_CapBSz_pos; lia)). lia.
        -- lia.
        -- replace (Z.of_nat count' + 1) with (Z.of_nat (S count')) by lia.
           exact Hw_lt.
        -- exact Hbit.
Qed.

Lemma clz_lt_pow2 : forall (w : bits (AddrSz - CapBSz)) (clz : bits ExpSz),
  clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) w)) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero) ->
  Zmod.unsigned w < 2^(AddrSz - CapBSz - Zmod.unsigned clz).
Proof.
  intros w clz Hclz.
  subst clz.
  assert (H_zero: Zmod.unsigned (Zmod.zero : bits ExpSz) = 0) by apply Zmod.unsigned_0.
  apply (@countLeadingZerosLoop_lt_pow2 w (Z.to_nat (AddrSz - CapBSz)) Zmod.zero); [ lia | | ].
  - rewrite H_zero.
    rewrite Z2Nat.id by (pose proof AddrSz_sub_CapBSz_nonneg; lia).
    lia.
  - rewrite Z2Nat.id by (pose proof AddrSz_sub_CapBSz_nonneg; lia).
    apply (bits.unsigned_range w).
    pose proof AddrSz_sub_CapBSz_pos. lia.
Qed.

Lemma length_div_e0_lt_CapBSz : forall (length : bits AddrSz) (clz : bits ExpSz),
  clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero) ->
  Zmod.unsigned clz <= AddrSz - CapBSz ->
  Zmod.unsigned length / 2^(AddrSz - CapBSz - Zmod.unsigned clz) < 2^CapBSz.
Proof.
  intros length clz Hclz Hclz_bound.
  pose proof CapBSz_pos.
  pose proof AddrSz_pos.
  pose proof (bits_ExpSz_range clz) as [Hclz_ge0 _].
  assert (He0_pos: 0 < 2^(AddrSz - CapBSz - Zmod.unsigned clz)).
  { apply Z.pow_pos_nonneg; lia. }
  apply Z.div_lt_upper_bound; [ exact He0_pos | ].
  destruct (Zmod.unsigned clz =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz.
    rewrite Hz.
    replace (AddrSz - CapBSz - 0) with (AddrSz - CapBSz) by lia.
    replace (2^(AddrSz - CapBSz) * 2^CapBSz) with (2^AddrSz) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    apply (bits.unsigned_range length ltac:(lia)).
  - pose proof (@clz_lt_pow2 (Zmod_lastn (AddrSz - CapBSz) length) clz Hclz) as Hw_lt.
    pose proof (unsigned_lastn_AddrSz_sub_CapBSz length) as Hlastn.
    rewrite Hlastn in Hw_lt.
    pose proof (Z.div_mod (Zmod.unsigned length) (2^CapBSz) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (Zmod.unsigned length) (2^CapBSz) ltac:(pose proof two_pow_CapBSz_pos; lia)) as Hmb.
    assert (Hdiv_le: Zmod.unsigned length / 2^CapBSz <= 2^(AddrSz - CapBSz - Zmod.unsigned clz) - 1) by lia.
    assert (Hmul_le: (Zmod.unsigned length / 2^CapBSz) * 2^CapBSz <= (2^(AddrSz - CapBSz - Zmod.unsigned clz) - 1) * 2^CapBSz).
    { apply Z.mul_le_mono_nonneg_r; [ lia | exact Hdiv_le ]. }
    replace ((2^(AddrSz - CapBSz - Zmod.unsigned clz) - 1) * 2^CapBSz)
      with (2^(AddrSz - CapBSz - Zmod.unsigned clz) * 2^CapBSz - 2^CapBSz) in Hmul_le by ring.
    rewrite <- Z.pow_add_r in Hmul_le by lia.
    replace (AddrSz - CapBSz - Zmod.unsigned clz + CapBSz) with (AddrSz - Zmod.unsigned clz) in Hmul_le by ring.
    assert (Hlen_lt_pow: Zmod.unsigned length < 2^(AddrSz - Zmod.unsigned clz)) by lia.
    replace (2^(AddrSz - CapBSz - Zmod.unsigned clz) * 2^CapBSz)
      with (2^(AddrSz - Zmod.unsigned clz)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    exact Hlen_lt_pow.
Qed.

Lemma lastn_1_CapBSz_plus1_eq_0 : forall (x : bits (CapBSz + 1)),
  Zmod.eqb (Zmod_lastn 1 x) (Zmod.one : bits 1) = false ->
  Zmod.unsigned x < 2^CapBSz.
Proof.
  intros x H.
  pose proof (@unsigned_lastn_1_CapBSz_plus1 x) as Hlastn.
  pose proof (bits.unsigned_range x ltac:(pose proof CapBSz_pos; lia)) as [Hx0 Hx1].
  destruct (Z_lt_le_dec (Zmod.unsigned x) (2^CapBSz)) as [Hlt | Hge]; [ exact Hlt | ].
  exfalso.
  assert (Hdiv: Zmod.unsigned x / 2^CapBSz = 1).
  { pose proof CapBSz_pos.
    assert (2^(CapBSz + 1) = 2 * 2^CapBSz) by (rewrite Z.pow_add_r by lia; ring).
    assert (1 <= Zmod.unsigned x / 2^CapBSz) by (apply Z.div_le_lower_bound; [ apply Z.pow_pos_nonneg; lia | lia ]).
    assert (Zmod.unsigned x / 2^CapBSz < 2) by (apply Z.div_lt_upper_bound; [ apply Z.pow_pos_nonneg; lia | lia ]).
    lia. }
  rewrite <- Hlastn in Hdiv.
  assert (Heq: Zmod_lastn 1 x = (Zmod.one : bits 1)).
  { apply Zmod.unsigned_inj.
    rewrite Hdiv, Zmod.unsigned_1.
    change (2^1) with 2.
    rewrite Z.mod_small by lia.
    reflexivity. }
  rewrite Heq in H.
  rewrite Zmod.eqb_refl in H.
  discriminate H.
Qed.

(* ========================================================================= *)
(* ROUNDUP PROPERTY 4: MANTISSA NORMALIZATION                                *)
(* Lemma bounds_roundUp_m_norm:                                              *)
(* Proves that if exponent e > 0, the top bit of m is 1:                    *)
(*   e > 0 -> 2^(CapBSz - 1) <= m                                            *)
(* ========================================================================= *)

Lemma bounds_roundUp_m_norm : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length false) ->
  let e := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  let m := Zmod.to_Z (bounds@%"m") in
  e > 0 -> 2^(CapBSz - 1) <= m.
Proof.
  intros base length bounds HB.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (e_init_plus_one_val Hclz_bound) as He_plus1_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
  { subst ef e_normal.
    cbn [evalLetExpr evalExpr].
    destruct isESaturated eqn:Hsat.
    - rewrite (Zmod.unsigned_of_Z (m:=2^ExpSz) (AddrSz + 1 - CapBSz)).
      rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
      rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
      rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
      lia.
    - subst e_unsat.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite Zmod.add_0_l.
      destruct isOverflow.
      + change (evalExpr $1) with (bits.of_Z ExpSz 1).
        change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
        rewrite He_init_eq.
        rewrite He_plus1_val.
        destruct (Zmod.unsigned clz =? 0); lia.
      + change (evalExpr $0) with (bits.of_Z ExpSz 0).
        rewrite Zmod.add_0_r.
        rewrite He_init_eq, He_val.
        lia. }
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  intros He_pos.
  destruct isOverflow eqn:Hovf.
  - assert (Hmf_val: mf = m_ovf).
    { rewrite Hmf, Hm_normal. cbn [evalLetExpr evalExpr]. reflexivity. }
    rewrite Hmf_val.
    subst m_ovf.
    cbn [evalLetExpr evalExpr fold_left map evalToBit KindCustomInd].
    rewrite unsigned_app_CapBSz_sub_1_val.
    destruct inc_ovf; lia.
  - assert (Hmf_val: mf = Zmod.firstn CapBSz m_raw).
    { rewrite Hmf, Hm_normal. reflexivity. }
    rewrite Hmf_val.
    assert (He_fin_val: Zmod.unsigned ef = (AddrSz - CapBSz) - Zmod.unsigned clz).
    { rewrite Hef, He_normal.
      subst isESaturated e_unsat.
      unfold Ugt.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite !Zmod.add_0_l.
      change (evalExpr $0) with (bits.of_Z ExpSz 0).
      rewrite Zmod.add_0_r.
      change (evalExpr $(AddrSz - CapBSz)) with (bits.of_Z ExpSz (AddrSz - CapBSz)).
      change (bits.of_Z ExpSz (AddrSz - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz - CapBSz)).
      rewrite Zmod.unsigned_of_Z.
      rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
      rewrite He_init_eq, He_val.
      assert (Hsat: (AddrSz - CapBSz <? (AddrSz - CapBSz) - Zmod.unsigned clz) = false).
      { apply Z.ltb_ge. lia. }
      rewrite Hsat.
      change (if false then ?A else ?B) with B.
      lia. }
    assert (Hraw_lt: Zmod.unsigned m_raw < 2^CapBSz).
    { symmetry in HisOverflow.
      cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
      apply (lastn_1_CapBSz_plus1_eq_0 HisOverflow). }
    rewrite unsigned_firstn by (pose proof CapBSz_pos; lia).
    rewrite (Z.mod_small (Zmod.unsigned m_raw) (2^CapBSz)) by (pose proof (bits.unsigned_range m_raw ltac:(pose proof CapBSz_pos; lia)); lia).
    rewrite Hm_raw.
    cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
    rewrite !Zmod.add_0_l.
    rewrite Zmod.unsigned_add.
    rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by (pose proof CapBSz_ge_2; lia).
    assert (Hclz_bound': Zmod.unsigned clz <= AddrSz - CapBSz - 1).
    { rewrite He_fin_val in He_pos. lia. }
    assert (Hlen_pow: 2^(AddrSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned length).
    { apply length_ge_pow2_clz.
      - subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray.
      - exact Hclz_bound'. }
    assert (Hd_ge: 2^(CapBSz - 1) <= Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
    { apply (@d_ge_pow2_CapBSz_sub_1 (Zmod.unsigned length) (Zmod.unsigned clz)); [ lia | exact Hlen_pow ]. }
    subst d.
    cbn [evalLetExpr evalExpr].
    rewrite unsigned_firstn by (pose proof CapBSz_pos; pose proof CapBSz_lt_AddrSz; lia).
    rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
    rewrite He_init_eq, He_val.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hd_bound: 0 <= Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz) < 2^(CapBSz + 1)).
    { split; [ apply Z.div_pos; lia | ].
      assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
      { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
      pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
      assert (Hpow_step: 2^(CapBSz + 1) = 2 * 2^CapBSz).
      { rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). ring. }
      rewrite Hpow_step. pose proof two_pow_CapBSz_pos. lia. }
    rewrite (Z.mod_small (Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz))) by exact Hd_bound.
    assert (Hi_range: 0 <= Zmod.unsigned iCeil < 4).
    { split; [ apply (@to_Z_nonneg 2); lia | ].
      apply Zmod.unsigned_pos_bound. change (2^2) with 4; lia. }
    assert (Hpow_step: 2^(CapBSz + 1) = 2 * 2^CapBSz).
    { rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). ring. }
    assert (Hsum_bound: 0 <= Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned iCeil < 2^(CapBSz + 1)).
    { pose proof CapBSz_ge_2. pose proof CapBSz_pos.
      split.
      - apply Z.add_nonneg_nonneg; [ apply Z.div_pos; lia | lia ].
      - rewrite Hpow_step.
        assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
        { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
        pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
        assert (4 <= 2^CapBSz) by (change 4 with (2^2); apply Z.pow_le_mono_r; lia).
        lia. }
    rewrite (Z.mod_small (Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz) + Zmod.unsigned iCeil)) by exact Hsum_bound.
    lia.
Qed.

(* ========================================================================= *)
(* ROUNDUP PROPERTY 2b HELPERS: COVERING ARITHMETIC                          *)
(* Mask arithmetic and bitwise reasoning establishing that the computed      *)
(* bounds cover the requested range: outBase + outLength >= base + length.   *)
(* ========================================================================= *)

Lemma unsigned_mask_e_eq : forall (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  let Msz := AddrSz + 2 - CapBSz in
  Zmod.not (Zmod.slu (Zmod.of_Z (2^Msz) (-1)) e) =
  (Zmod.sub (Zmod.slu (Zmod.one : bits Msz) e) (Zmod.one : bits Msz)).
Proof.
  intros e He Msz.
  subst Msz.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  apply Zmod.unsigned_inj.
  rewrite not_slu_minus1_mask by exact He.
  rewrite Zmod.unsigned_sub.
  rewrite Zmod.unsigned_slu.
  rewrite Zmod.unsigned_1.
  rewrite Z.shiftl_1_l by lia.
  rewrite (Z.mod_small (2^e)).
  2: {
    assert (0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
    split; [ lia | ].
    apply Z.pow_lt_mono_r; lia.
  }
  rewrite (Z.mod_small (2^e - 1)).
  2: {
    assert (0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
    split; [ lia | ].
    assert (2^e <= 2^(AddrSz + 2 - CapBSz)) by (apply Z.pow_le_mono_r; lia).
    lia.
  }
  reflexivity.
Qed.

Lemma circuit_base_mod_e_val : forall (base : bits AddrSz) (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  let Msz := AddrSz + 2 - CapBSz in
  let mask_e := Zmod.sub (Zmod.slu (Zmod.one : bits Msz) e) (Zmod.one : bits Msz) in
  Zmod.unsigned (Zmod.and (Zmod.firstn Msz base) mask_e) = Zmod.unsigned base mod 2^e.
Proof.
  intros base e He Msz mask_e.
  subst mask_e Msz.
  rewrite <- (unsigned_mask_e_eq He).
  rewrite and_mask_e by exact He.
  rewrite unsigned_firstn by (pose proof CapBSz_lt_AddrSz; pose proof CapBSz_ge_2; lia).
  apply mod_mod_mask_e.
  exact He.
Qed.

Lemma circuit_iCeil_ge_sum_mod : forall (base length : bits AddrSz) (e : Z),
  0 <= e <= AddrSz - CapBSz ->
  let Msz := AddrSz + 2 - CapBSz in
  let mask_e := Zmod.sub (Zmod.slu (Zmod.one : bits Msz) e) (Zmod.one : bits Msz) in
  let base_mod_e := Zmod.and (Zmod.firstn Msz base) mask_e in
  let length_mod_e := Zmod.and (Zmod.firstn Msz length) mask_e in
  let sum_mod_e := (base_mod_e + length_mod_e)%Zmod in
  let iFloor := Zmod.firstn 2 (Zmod.sru sum_mod_e e) in
  let lost_sum := Zmod.and sum_mod_e mask_e in
  let iCeil := (iFloor +
                Zmod.app (if negb (Zmod.eqb lost_sum 0) then (Zmod.one : bits 1) else (Zmod.zero : bits 1)) (Zmod.zero : bits 1))%Zmod in
  Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e <= (Zmod.unsigned iCeil) * 2^e /\
  Zmod.unsigned iCeil <= 2.
Proof.
  intros base length e He Msz mask_e base_mod_e length_mod_e sum_mod_e iFloor lost_sum iCeil.
  pose proof CapBSz_lt_AddrSz. pose proof CapBSz_ge_2.
  assert (He_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hbase_val: Zmod.unsigned base_mod_e = Zmod.unsigned base mod 2^e).
  { subst base_mod_e mask_e Msz. apply circuit_base_mod_e_val; exact He. }
  assert (Hlen_val: Zmod.unsigned length_mod_e = Zmod.unsigned length mod 2^e).
  { subst length_mod_e mask_e Msz. apply circuit_base_mod_e_val; exact He. }
  assert (Hbase_bound: 0 <= Zmod.unsigned base_mod_e < 2^e).
  { rewrite Hbase_val. apply Z.mod_pos_bound; exact He_pos. }
  assert (Hlen_bound: 0 <= Zmod.unsigned length_mod_e < 2^e).
  { rewrite Hlen_val. apply Z.mod_pos_bound; exact He_pos. }
  assert (Hsum_bound: 0 <= Zmod.unsigned base_mod_e + Zmod.unsigned length_mod_e < 2^Msz).
  { assert (Hpow_le: 2^e <= 2^(AddrSz - CapBSz)) by (apply Z.pow_le_mono_r; lia).
    assert (Hpow_step: 2^Msz = 4 * 2^(AddrSz - CapBSz)).
    { subst Msz. replace (AddrSz + 2 - CapBSz) with ((AddrSz - CapBSz) + 2) by lia.
      rewrite Z.pow_add_r by lia. ring. }
    lia. }
  assert (Hsum_val: Zmod.unsigned sum_mod_e = Zmod.unsigned base_mod_e + Zmod.unsigned length_mod_e).
  { subst sum_mod_e.
    rewrite Zmod.unsigned_add.
    apply Z.mod_small.
    exact Hsum_bound. }
  assert (Hlost_val: Zmod.unsigned lost_sum = (Zmod.unsigned sum_mod_e) mod 2^e).
  { subst lost_sum mask_e Msz.
    rewrite <- (unsigned_mask_e_eq He).
    apply and_mask_e.
    exact He. }
  assert (Hfloor_val: Zmod.unsigned iFloor = (Zmod.unsigned sum_mod_e) / 2^e).
  { subst iFloor.
    rewrite unsigned_firstn by lia.
    rewrite Zmod.unsigned_sru by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    apply Z.mod_small.
    assert (Zmod.unsigned sum_mod_e < 2 * 2^e) by lia.
    assert (Zmod.unsigned sum_mod_e / 2^e < 2).
    { apply Z.div_lt_upper_bound; [ exact He_pos | lia ]. }
    assert (0 <= Zmod.unsigned sum_mod_e / 2^e) by (apply Z.div_pos; lia).
    change (2^2) with 4.
    lia. }
  assert (H_one: Zmod.unsigned (Zmod.one : bits 1) = 1) by reflexivity.
  assert (H_zero: Zmod.unsigned (Zmod.zero : bits 1) = 0) by apply Zmod.unsigned_0.
  assert (Hdiv_ge0: 0 <= Zmod.unsigned sum_mod_e / 2^e) by (apply Z.div_pos; lia).
  assert (Hdiv_lt2: Zmod.unsigned sum_mod_e / 2^e < 2).
  { apply Z.div_lt_upper_bound; [ exact He_pos | lia ]. }
  assert (Hceil_ge: (Zmod.unsigned sum_mod_e) <= (Zmod.unsigned iCeil) * 2^e /\ Zmod.unsigned iCeil <= 2).
  { subst iCeil.
    rewrite Zmod.unsigned_add.
    rewrite (unsigned_app_zero (n:=1) (m:=1)) by lia.
    rewrite Hfloor_val.
    destruct (negb (Zmod.eqb lost_sum 0)) eqn:Hlost_b.
    - change (if true then (Zmod.one : bits 1) else (Zmod.zero : bits 1)) with (Zmod.one : bits 1).
      rewrite H_one.
      rewrite (Z.mod_small (Zmod.unsigned sum_mod_e / 2^e + 1)) by (change (2^2) with 4; lia).
      pose proof (Z.div_mod (Zmod.unsigned sum_mod_e) (2^e) ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound (Zmod.unsigned sum_mod_e) (2^e) He_pos) as Hmb.
      lia.
    - change (if false then (Zmod.one : bits 1) else (Zmod.zero : bits 1)) with (Zmod.zero : bits 1).
      rewrite H_zero.
      rewrite Z.add_0_r.
      rewrite (Z.mod_small (Zmod.unsigned sum_mod_e / 2^e)) by (change (2^2) with 4; lia).
      apply Bool.negb_false_iff in Hlost_b.
      apply Zmod.eqb_eq in Hlost_b.
      assert (Hlost_0: Zmod.unsigned lost_sum = 0).
      { rewrite Hlost_b. apply Zmod.unsigned_0. }
      rewrite Hlost_val in Hlost_0.
      pose proof (Z.div_mod (Zmod.unsigned sum_mod_e) (2^e) ltac:(lia)) as Hdm.
      rewrite Hlost_0 in Hdm.
      lia. }
  destruct Hceil_ge as [Hge Hle].
  split.
  - rewrite <- Hbase_val, <- Hlen_val.
    rewrite <- Hsum_val.
    exact Hge.
  - exact Hle.
Qed.

Lemma b_e_testbit : forall (base : bits AddrSz) (e : bits ExpSz),
  Zmod.unsigned e <= AddrSz - CapBSz ->
  (if evalExpr ((mkBoolArray AddrSz #base) @[ #e ]) then 1 else 0) =
  (Zmod.unsigned base / 2^(Zmod.unsigned e)) mod 2.
Proof.
  intros base e He.
  pose proof CapBSz_lt_AddrSz.
  pose proof (bits_ExpSz_range e) as [He_min _].
  cbn [evalExpr mkBoolArray evalFromBit evalFromBitArray].
  change (evalFromBit (k:=Array (Z.to_nat AddrSz) Bool) base)
    with (@evalFromBitArray (Z.to_nat AddrSz) Bool (fun v => Zmod.eqb v Zmod.one) base).
  assert (Hlt_top: (Z.to_nat (Zmod.unsigned e) < Z.to_nat (AddrSz + 1 - CapBSz))%nat).
  { apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia. }
  rewrite readNatToFinType_evalFromBitArray_AddrSz by exact Hlt_top.
  rewrite Z2Nat.id by lia.
  destruct (Z.testbit (Zmod.unsigned base) (Zmod.unsigned e)) eqn:Hb.
  - apply Z.testbit_true in Hb; [ | lia ].
    rewrite Hb. reflexivity.
  - apply Z.testbit_false in Hb; [ | lia ].
    rewrite Hb. reflexivity.
Qed.

Lemma firstn_1_eqb_one : forall (n : Z) (x : bits n),
  0 < n ->
  Zmod.eqb (Zmod.firstn 1 x) (Zmod.one : bits 1) = (Zmod.unsigned x mod 2 =? 1).
Proof.
  intros n x Hn.
  destruct (Zmod.eqb_spec (Zmod.firstn 1 x) (Zmod.one : bits 1)) as [H1 | H1].
  - apply (f_equal Zmod.unsigned) in H1.
    unfold Zmod.firstn in H1.
    rewrite Zmod.unsigned_of_Z in H1.
    unfold Zmod.to_Z in H1.
    change (Zmod.Private_to_Z x) with (Zmod.unsigned x) in H1.
    change (2^1) with 2 in H1.
    change (Zmod.unsigned (Zmod.one : bits 1)) with 1 in H1.
    rewrite H1. reflexivity.
  - destruct (Zmod.unsigned x mod 2 =? 1) eqn:H2; [ exfalso | reflexivity ].
    apply Z.eqb_eq in H2. apply H1.
    apply Zmod.unsigned_inj.
    unfold Zmod.firstn.
    rewrite Zmod.unsigned_of_Z.
    unfold Zmod.to_Z.
    change (Zmod.Private_to_Z x) with (Zmod.unsigned x).
    change (2^1) with 2.
    change (Zmod.unsigned (Zmod.one : bits 1)) with 1.
    exact H2.
Qed.

(* ========================================================================= *)
(* ROUNDUP PROPERTY 2b: RANGE COVERING                                       *)
(* Lemma bounds_roundUp_covering:                                            *)
(* Proves that the allocated bounds cover the requested range:              *)
(*   outBase + outLength >= base + length                                    *)
(* ========================================================================= *)

Lemma bounds_roundUp_covering :
  forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length false) ->
  let outBase := Zmod.to_Z (bounds@%"base") in
  let outLength := Zmod.to_Z (bounds@%"length") in
  outBase + outLength >= Zmod.to_Z base + Zmod.to_Z length.
Proof.
  intros base length bounds HB outBase outLength.
  pose proof (bounds_base_math (isRoundDown:=false) HB) as Hbase_eq.
  pose proof (bounds_length_m_e (isRoundDown:=false) HB) as Hlen_eq.
  subst outBase outLength.
  rewrite Hbase_eq, Hlen_eq.
  clear Hbase_eq Hlen_eq.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (e_init_plus_one_val Hclz_bound) as He_plus1_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
  { subst ef e_normal.
    cbn [evalLetExpr evalExpr].
    destruct isESaturated eqn:Hsat.
    - rewrite (Zmod.unsigned_of_Z (m:=2^ExpSz) (AddrSz + 1 - CapBSz)).
      rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
      rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
      rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
      lia.
    - subst e_unsat.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite Zmod.add_0_l.
      destruct isOverflow.
      + change (evalExpr $1) with (bits.of_Z ExpSz 1).
        change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
        rewrite He_init_eq.
        rewrite He_plus1_val.
        destruct (Zmod.unsigned clz =? 0); lia.
      + change (evalExpr $0) with (bits.of_Z ExpSz 0).
        rewrite Zmod.add_0_r.
        rewrite He_init_eq, He_val.
        lia. }
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  pose proof CapBSz_pos.
  pose proof CapBSz_lt_AddrSz.
  pose proof (bits.unsigned_range base ltac:(lia)) as [Hb0 Hb1].
  pose proof (bits.unsigned_range length ltac:(lia)) as [Hlen0 Hlen1].
  assert (He_nonneg: 0 <= AddrSz - CapBSz - Zmod.unsigned clz) by lia.
  assert (Hpow_einit: 0 < 2^(AddrSz - CapBSz - Zmod.unsigned clz)) by (apply Z.pow_pos_nonneg; lia).
  set (e0 := AddrSz - CapBSz - Zmod.unsigned clz).
  assert (He0_eq: Zmod.unsigned e_init = e0).
  { subst e0. rewrite He_init_eq. exact He_val. }
  assert (Hd_val: Zmod.unsigned d = Zmod.unsigned length / 2^e0).
  { subst d. cbn [evalLetExpr evalExpr].
    rewrite unsigned_firstn by (pose proof CapBSz_pos; pose proof CapBSz_lt_AddrSz; lia).
    rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
    rewrite He_init_eq, He_val.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
    { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
    pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
    assert (Hpow_step: 2^(CapBSz + 1) = 2 * 2^CapBSz).
    { rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). ring. }
    assert (Hd_bound: 0 <= Zmod.unsigned length / 2 ^ e0 < 2^(CapBSz + 1)).
    { split; [ apply Z.div_pos; lia | ].
      subst e0. eapply Z.lt_le_trans; [ exact Hd_lt | ]. rewrite Hpow_step; pose proof two_pow_CapBSz_pos; lia. }
    subst e0.
    rewrite (Z.mod_small (Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz))) by exact Hd_bound.
    reflexivity. }
  assert (Hraw_eq: Zmod.unsigned m_raw = Zmod.unsigned length / 2^e0 + Zmod.unsigned iCeil).
  { rewrite Hm_raw.
    cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit].
    rewrite !Zmod.add_0_l.
    rewrite Zmod.unsigned_add.
    rewrite (unsigned_app_zero (n:=2) (m:=CapBSz - 1)) by lia.
    rewrite Hd_val.
    assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
    { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
    pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
    assert (Hi_range: 0 <= Zmod.unsigned iCeil < 4).
    { split; [ apply (@to_Z_nonneg 2); lia | ].
      apply Zmod.unsigned_pos_bound. change (2^2) with 4; lia. }
    assert (Hpow_step: 2^(CapBSz + 1) = 2 * 2^CapBSz).
    { rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). ring. }
    assert (Hsum_bound: 0 <= Zmod.unsigned length / 2 ^ e0 + Zmod.unsigned iCeil < 2^(CapBSz + 1)).
    { pose proof CapBSz_ge_2. pose proof CapBSz_pos.
      split.
      - apply Z.add_nonneg_nonneg; [ apply Z.div_pos; lia | lia ].
      - rewrite Hpow_step.
        assert (4 <= 2^CapBSz) by (change 4 with (2^2); apply Z.pow_le_mono_r; lia).
        subst e0. lia. }
    rewrite (Z.mod_small (Zmod.unsigned length / 2 ^ e0 + Zmod.unsigned iCeil)) by exact Hsum_bound.
    reflexivity. }
  assert (Hceil_both: (Zmod.unsigned base mod 2^e0 + Zmod.unsigned length mod 2^e0 <= Zmod.unsigned iCeil * 2^e0) /\
                      (Zmod.unsigned iCeil <= 2)).
  { rewrite HiCeil.
    cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalToBit isNotZero].
    rewrite !Zmod.add_0_l.
    assert (Hmask_eq': mask_e = Zmod.not (Zmod.slu (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)) e0)).
    { rewrite Hmask_e. cbn [evalLetExpr evalExpr fold_left map].
      rewrite He0_eq. reflexivity. }
    assert (Hmask_sub: mask_e = Zmod.sub (Zmod.slu (Zmod.one : bits (AddrSz + 2 - CapBSz)) e0) (Zmod.one : bits (AddrSz + 2 - CapBSz))).
    { rewrite Hmask_eq'. apply unsigned_mask_e_eq. subst e0; lia. }
    rewrite HiFloor, Hlost_sum.
    rewrite Hsum_mod_e, Hbase_mod_e, Hlength_mod_e, Hmask_sub.
    cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalBinary evalAndBinary KindCustomInd InvDefault isEq isZero isNotZero evalNot evalToBit getDefault].
    rewrite !Zmod.add_0_l.
    assert (Hand1: forall w, Zmod.and (bits.of_Z (AddrSz + 2 - CapBSz) (-1)) w = w).
    { intros w. apply Zmod.unsigned_inj.
      change (bits.of_Z (AddrSz + 2 - CapBSz) (-1)) with (Zmod.of_Z (2^(AddrSz + 2 - CapBSz)) (-1)).
      apply and_minus1_mask. }
    rewrite !Hand1.
    rewrite He0_eq.
    apply circuit_iCeil_ge_sum_mod.
    subst e0. lia. }
  destruct Hceil_both as [Hceil_ge HiCeil_le2].
  assert (Hstep2: Zmod.unsigned base + Zmod.unsigned length <=
                  (Zmod.unsigned base / 2^e0) * 2^e0 + Zmod.unsigned m_raw * 2^e0).
  { rewrite Hraw_eq.
    apply (roundUp_step2_math (b:=Zmod.unsigned base) (len:=Zmod.unsigned length) (e:=e0)
                              (d:=Zmod.unsigned length / 2^e0)
                              (base_mod_e:=Zmod.unsigned base mod 2^e0)
                              (len_mod_e:=Zmod.unsigned length mod 2^e0)
                              (iCeil:=Zmod.unsigned iCeil)
                              (m_raw:=Zmod.unsigned length / 2^e0 + Zmod.unsigned iCeil)).
    - lia.
    - lia.
    - lia.
    - apply Z.mod_pos_bound; exact Hpow_einit.
    - apply Z.mod_pos_bound; exact Hpow_einit.
    - apply Z.mod_pos_bound; exact Hpow_einit.
    - apply Z.mod_pos_bound; exact Hpow_einit.
    - rewrite (Z.div_mod (Zmod.unsigned base) (2^e0) ltac:(lia)) at 1; ring.
    - rewrite (Z.div_mod (Zmod.unsigned length) (2^e0) ltac:(lia)) at 1; ring.
    - reflexivity.
    - exact Hceil_ge. }
  apply Z.le_ge.
  destruct isOverflow eqn:Hovf.
  - (* isOverflow = true *)
    assert (Hef_val: Zmod.unsigned ef = e0 + 1).
    { rewrite Hef, He_normal.
      subst isESaturated e_unsat.
      unfold Ugt.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite !Zmod.add_0_l.
      change (evalExpr $1) with (bits.of_Z ExpSz 1).
      change (bits.of_Z ExpSz 1) with (Zmod.one : bits ExpSz).
      rewrite He_init_eq, He_plus1_val.
      change (evalExpr $(AddrSz - CapBSz)) with (bits.of_Z ExpSz (AddrSz - CapBSz)).
      change (bits.of_Z ExpSz (AddrSz - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz - CapBSz)).
      rewrite Zmod.unsigned_of_Z.
      rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
      destruct (Zmod.unsigned clz =? 0) eqn:Hz.
      + apply Z.eqb_eq in Hz.
        assert (Hsat: (AddrSz - CapBSz <? AddrSz + 1 - CapBSz) = true) by reflexivity.
        rewrite Hsat.
        change (if true then ?A else ?B) with A.
        change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
        change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
        rewrite Zmod.unsigned_of_Z.
        rewrite <- Emax_eq_AddrSz_add_1_sub_CapBSz.
        rewrite (Z.mod_small Emax (2^ExpSz)) by (pose proof two_pow_ExpSz_eq_AddrSz; pose proof Emax_nonneg; pose proof Emax_lt_AddrSz; lia).
        rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
        subst e0. rewrite Hz. lia.
      + apply Z.eqb_neq in Hz.
        assert (Hsat: (AddrSz - CapBSz <? (AddrSz + 1 - CapBSz) - Zmod.unsigned clz) = false).
        { apply Z.ltb_ge. lia. }
        rewrite Hsat.
        change (if false then ?A else ?B) with B.
        subst e0. lia. }
    assert (Hmf_val: mf = m_ovf).
    { rewrite Hmf, Hm_normal. reflexivity. }
    rewrite Hef_val, Hmf_val.
    eapply Z.le_trans; [ exact Hstep2 | ].
    assert (He0_ge0: 0 <= e0) by (unfold e0; lia).
    rewrite (@base_div_pow2_succ (Zmod.unsigned base) e0 He0_ge0).
    replace (2^(e0 + 1)) with (2 * 2^e0) by (rewrite Z.pow_add_r by lia; ring).
    assert (Hb_e_val: (if b_e then 1 else 0) = (Zmod.unsigned base / 2^e0) mod 2).
    { rewrite Hb_e.
      cbn [evalLetExpr].
      rewrite b_e_testbit by (rewrite He0_eq; subst e0; lia).
      rewrite He0_eq. reflexivity. }
    assert (Hinc_val: inc_ovf = (Zmod.unsigned m_raw mod 2 =? 1) || ((Zmod.unsigned base / 2^e0) mod 2 =? 1)).
    { rewrite Hinc_ovf.
      cbn [evalLetExpr evalExpr fold_left map evalOrBinary getDefault].
      rewrite Hm_raw_lsb.
      cbn [evalLetExpr evalExpr evalFromBit KindCustomInd].
      rewrite firstn_1_eqb_one by (unfold CapBSz; lia).
      assert (Hb_bool: b_e = ((Zmod.unsigned base / 2^e0) mod 2 =? 1)).
      { pose proof (Z.mod_pos_bound (Zmod.unsigned base / 2^e0) 2 ltac:(lia)).
        destruct b_e; rewrite <- Hb_e_val; destruct ((Zmod.unsigned base / 2^e0) mod 2); reflexivity || lia. }
      rewrite Hb_bool. reflexivity. }
    subst m_ovf.
    cbn [evalLetExpr evalExpr fold_left map evalToBit KindCustomInd].
    rewrite unsigned_app_CapBSz_sub_1_val.
    destruct inc_ovf eqn:Hinc_bool.
    + change (if true then 1 else 0) with 1.
      assert (Hcov: Zmod.unsigned m_raw <= 2 * (2^(CapBSz - 1) + 1) - (Zmod.unsigned base / 2^e0) mod 2).
      { apply roundUp_ovf_ge_general with (inc_ovf:=true); [ | | reflexivity | exact Hinc_val ].
        - rewrite Hraw_eq.
          assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
          { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
          pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
          change (AddrSz - CapBSz - Zmod.unsigned clz) with e0 in Hd_lt.
          lia.
        - pose proof (Z.mod_pos_bound (Zmod.unsigned base / 2^e0) 2 ltac:(lia)). lia. }
      apply roundUp_step3_ovf_math; [ subst e0; lia | exact Hcov ].
    + change (if false then 1 else 0) with 0.
      assert (Hcov: Zmod.unsigned m_raw <= 2 * (2^(CapBSz - 1) + 0) - (Zmod.unsigned base / 2^e0) mod 2).
      { apply roundUp_ovf_ge_general with (inc_ovf:=false); [ | | reflexivity | exact Hinc_val ].
        - rewrite Hraw_eq.
          assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
          { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
          pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
          change (AddrSz - CapBSz - Zmod.unsigned clz) with e0 in Hd_lt.
          lia.
        - pose proof (Z.mod_pos_bound (Zmod.unsigned base / 2^e0) 2 ltac:(lia)). lia. }
      apply roundUp_step3_ovf_math; [ subst e0; lia | exact Hcov ].
  - (* isOverflow = false *)
    assert (Hef_val: Zmod.unsigned ef = e0).
    { rewrite Hef, He_normal.
      subst isESaturated e_unsat.
      unfold Ugt.
      cbn [evalLetExpr evalExpr fold_left map].
      rewrite !Zmod.add_0_l.
      change (evalExpr $0) with (bits.of_Z ExpSz 0).
      rewrite Zmod.add_0_r.
      change (evalExpr $(AddrSz - CapBSz)) with (bits.of_Z ExpSz (AddrSz - CapBSz)).
      change (bits.of_Z ExpSz (AddrSz - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz - CapBSz)).
      rewrite Zmod.unsigned_of_Z.
      rewrite (Z.mod_small (AddrSz - CapBSz) (2^ExpSz)) by (rewrite two_pow_ExpSz_eq_AddrSz; pose proof CapBSz_ge_2; pose proof CapBSz_lt_AddrSz; lia).
      rewrite He_init_eq, He_val.
      assert (Hsat: (AddrSz - CapBSz <? (AddrSz - CapBSz) - Zmod.unsigned clz) = false).
      { apply Z.ltb_ge. lia. }
      rewrite Hsat.
      rewrite He_val. reflexivity. }
    assert (Hmf_val: mf = Zmod.firstn CapBSz m_raw).
    { rewrite Hmf, Hm_normal. reflexivity. }
    rewrite Hef_val, Hmf_val.
    assert (Hraw_lt: Zmod.unsigned m_raw < 2^CapBSz).
    { symmetry in HisOverflow.
      cbn [evalLetExpr evalExpr evalFromBit KindCustomInd] in HisOverflow.
      apply (lastn_1_CapBSz_plus1_eq_0 HisOverflow). }
    pose proof CapBSz_pos.
    pose proof (bits.unsigned_range m_raw ltac:(lia)) as [Hm0 Hm1].
    rewrite unsigned_firstn by lia.
    rewrite (Z.mod_small (Zmod.unsigned m_raw) (2^CapBSz)) by lia.
    exact Hstep2.
Qed.

(* ========================================================================= *)
(* Final Complete Theorem: BoundsRoundUpProperties                           *)
(* ========================================================================= *)

Theorem BoundsRoundUpProperties :
  forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length false) ->
  let e := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  let m := Zmod.to_Z (bounds@%"m") in
  let outBase := Zmod.to_Z (bounds@%"base") in
  let outLength := Zmod.to_Z (bounds@%"length") in
  (* 1) outBase = floor(base / 2^e) * 2^e <= base *)
  outBase = (Zmod.to_Z base / 2^e) * 2^e /\
  outBase <= Zmod.to_Z base /\
  (* 2) outLength = m * 2^e, and outBase + outLength >= base + length *)
  outLength = m * 2^e /\
  outBase + outLength >= Zmod.to_Z base + Zmod.to_Z length /\
  (* 3) outBase + (m - 1) * 2^e < base + length *)
  outBase + (m - 1) * 2^e < Zmod.to_Z base + Zmod.to_Z length /\
  (* 4) MSB of m is 1 unless e is 0 *)
  (e > 0 -> 2^(CapBSz - 1) <= m).
Proof.
  intros base length bounds HB e m outBase outLength.
  pose proof (bounds_roundUp_min HB) as Hmin.
  pose proof (bounds_top_eq (isRoundDown:=false) HB) as Htop_eq.
  pose proof (bounds_length_m_e (isRoundDown:=false) HB) as Hlen_m_e.
  repeat split.
  - apply (bounds_base_math (isRoundDown:=false) HB).
  - apply (bounds_base_le (isRoundDown:=false) HB).
  - exact Hlen_m_e.
  - apply (bounds_roundUp_covering HB).
  - subst e m outBase outLength.
    assert (Hsub: forall a b c : Z, a + (b - 1) * c = (a + b * c) - c) by (intros; ring).
    rewrite Hsub, <- Hlen_m_e, <- Htop_eq. exact Hmin.
  - apply (bounds_roundUp_m_norm HB).
Qed.

(* ========================================================================= *)
(* ROUNDDOWN SPECIFICATION & TRAILING ZEROS ANALYSIS                         *)
(* Analyzes countTrailingZeros hardware loop and establishes exact base      *)
(* preservation and length containment for RoundDown mode.                   *)
(* ========================================================================= *)

Lemma testbit_low_zeros_mod : forall (a : Z) (k : Z),
  0 <= k ->
  (forall i, 0 <= i < k -> Z.testbit a i = false) ->
  a mod 2^k = 0.
Proof.
  intros a k Hk Hzeros.
  assert (Hpos: 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound a (2^k) Hpos) as [Hmod_ge0 Hmod_lt].
  destruct (a mod 2^k =? 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. exact Heq.
  - apply Z.eqb_neq in Heq.
    assert (Hcontra: a mod 2^k = 0).
    { apply Z.bits_inj_0.
      intros n.
      destruct (Z_lt_le_dec n 0) as [Hneg | Hnonneg].
      - apply Z.testbit_neg_r; lia.
      - destruct (Z_lt_le_dec n k) as [Hlt | Hge].
        + rewrite Z.mod_pow2_bits_low by lia.
          apply Hzeros; lia.
        + apply Z.testbit_false; [ lia | ].
          assert (Hdiv: (a mod 2^k) / 2^n = 0).
          { apply Z.div_small.
            split; [ lia | ].
            eapply Z.lt_le_trans; [ exact Hmod_lt | ].
            apply Z.pow_le_mono_r; lia. }
          rewrite Hdiv.
          apply Zmod_0_l. }
    contradiction.
Qed.

Lemma countTrailingZerosLoop_over_true : forall ni no arr count idx accum,
  evalLetExpr (@countTrailingZerosLoop type ni no arr idx count true accum) = accum.
Proof.
  intros ni no arr count.
  induction count as [| count' IHcount']; intros idx accum.
  - reflexivity.
  - simpl countTrailingZerosLoop.
    cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr
         mapDiffTuple snd evalAndBinary fold_left map InvDefault evalFromBit
         evalOrBinary orb getDefault].
    fold evalLetExpr.
    rewrite IHcount'.
    change (if true then Zmod.zero else Zmod.one) with (Zmod.zero (2^no)).
    rewrite !Zmod.add_0_l.
    rewrite Zmod.add_0_r.
    reflexivity.
Qed.

Lemma countTrailingZerosLoop_step : forall ni no arr count idx (accum : bits no),
  evalLetExpr (@countTrailingZerosLoop type ni no arr idx (S count) false accum) =
  let b := evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) idx) in
  if b
  then accum
  else evalLetExpr (@countTrailingZerosLoop type ni no arr (S idx) count false (@Zmod.add (2^no) accum (@Zmod.one (2^no)))).
Proof.
  intros ni no arr count idx accum.
  simpl countTrailingZerosLoop.
  cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
       finNum Fst Snd evalExpr
       mapDiffTuple snd evalAndBinary fold_left map InvDefault evalFromBit
       evalOrBinary orb getDefault].
  fold evalLetExpr.
  destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) idx)) eqn:Hb.
  - rewrite countTrailingZerosLoop_over_true.
    change (if true then Zmod.zero else Zmod.one) with (Zmod.zero (2^no)).
    rewrite !Zmod.add_0_l.
    rewrite Zmod.add_0_r.
    reflexivity.
  - change (if false then Zmod.zero else Zmod.one) with (Zmod.one (2^no)).
    rewrite !Zmod.add_0_l.
    reflexivity.
Qed.

Lemma eval_readNatToFinType_mkBoolArray_AddrSz : forall (w : bits AddrSz) (i : nat),
  (i < Z.to_nat AddrSz)%nat ->
  evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst (mkBoolArray AddrSz (Var type (Bit AddrSz) w))) i) =
  Z.testbit (Zmod.unsigned w) (Z.of_nat i).
Proof.
  intros w i.
  let asz := eval compute in (Z.to_nat AddrSz) in
  repeat (destruct i as [| i]; [
    intro Hlt; unfold readNatToFinType, mkBoolArray;
    change (Z.to_nat AddrSz) with asz in Hlt;
    change (Z.to_nat AddrSz) with asz;
    change (_ <? asz)%nat with true;
    cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit
         evalOrBinary orb getDefault];
    rewrite readSameTuple_nth with (d := false);
    change (evalFromBit (k:=Array asz Bool) w)
      with (@evalFromBitArray asz Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w);
    cbn [finNum];
    rewrite evalFromBitArray_nth by lia;
    reflexivity
  | ]);
  intro Hlt; change (Z.to_nat AddrSz) with asz in Hlt; lia.
Qed.

Lemma countTrailingZerosLoop_testbit_false : forall (base : bits AddrSz) (count : nat) (idx : nat) (accum : bits ExpSz),
  (idx + count <= Z.to_nat AddrSz)%nat ->
  (idx < Z.to_nat AddrSz)%nat ->
  Zmod.unsigned accum = Z.of_nat idx ->
  let res := evalLetExpr (@countTrailingZerosLoop type (Z.to_nat AddrSz) ExpSz (mkBoolArray AddrSz (Var type (Bit AddrSz) base)) idx count false accum) in
  Z.of_nat idx < Zmod.unsigned res ->
  forall i, Z.of_nat idx <= i < Zmod.unsigned res ->
  Z.testbit (Zmod.unsigned base) i = false.
Proof.
  intros base count.
  induction count as [| count' IHcount']; intros idx accum Hbound Hidx_lt Haccum res Hres_gt i Hi.
  - simpl countTrailingZerosLoop in res.
    cbn [evalLetExpr evalExpr] in res.
    subst res. rewrite Haccum in Hres_gt. lia.
  - subst res.
    rewrite countTrailingZerosLoop_step in Hres_gt, Hi.
    destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst (mkBoolArray AddrSz (Var type (Bit AddrSz) base))) idx)) eqn:Hbeq.
    + cbn zeta iota in Hres_gt.
      rewrite Haccum in Hres_gt. lia.
    + cbn zeta iota in Hres_gt, Hi.
      assert (Hb_test: Z.testbit (Zmod.unsigned base) (Z.of_nat idx) = false).
      { rewrite <- Hbeq.
        rewrite eval_readNatToFinType_mkBoolArray_AddrSz by exact Hidx_lt.
        reflexivity. }
      assert (Hidx_cases: (S idx < Z.to_nat AddrSz)%nat \/ S idx = Z.to_nat AddrSz) by lia.
      destruct Hidx_cases as [Hidx_next_lt | Hidx_next_eq].
      * assert (Haccum_next: Zmod.unsigned (accum + 1)%Zmod = Z.of_nat (S idx)).
        { rewrite Zmod.unsigned_add.
          rewrite Haccum.
          unfold Zmod.one.
          rewrite Zmod.unsigned_of_Z.
          rewrite Zplus_mod_idemp_r.
          rewrite two_pow_ExpSz_eq_AddrSz.
          assert (Hidx_z: 0 <= Z.of_nat idx + 1 < AddrSz).
          { pose proof AddrSz_pos.
            split; [ lia | ].
            apply Nat2Z.inj_lt in Hidx_next_lt.
            rewrite Nat2Z.inj_succ in Hidx_next_lt.
            rewrite Z2Nat.id in Hidx_next_lt by lia.
            lia. }
          rewrite (Z.mod_small (Z.of_nat idx + 1) AddrSz) by exact Hidx_z.
          lia. }
        assert (Hbound': (S idx + count' <= Z.to_nat AddrSz)%nat) by lia.
        destruct (Z.eq_dec i (Z.of_nat idx)) as [Heq | Hneq].
        -- subst i. exact Hb_test.
        -- apply (IHcount' (S idx) (accum + 1)%Zmod Hbound' Hidx_next_lt Haccum_next).
           ++ rewrite Nat2Z.inj_succ. lia.
           ++ rewrite Nat2Z.inj_succ. lia.
      * (* S idx = Z.to_nat AddrSz: count' must be 0 because idx + S count' <= Z.to_nat AddrSz *)
        assert (Hcount0: count' = 0%nat) by lia.
        subst count'.
        assert (Hres_eq: evalLetExpr (@countTrailingZerosLoop type (Z.to_nat AddrSz) ExpSz
                            (mkBoolArray AddrSz (Var type (Bit AddrSz) base))
                            (S idx) 0 false (accum + 1)%Zmod) = (accum + 1)%Zmod) by reflexivity.
        rewrite Hres_eq in Hres_gt.
        assert (Haccum_0: Zmod.unsigned (accum + 1)%Zmod = 0).
        { rewrite Zmod.unsigned_add.
          rewrite Haccum.
          unfold Zmod.one.
          rewrite Zmod.unsigned_of_Z.
          rewrite Zplus_mod_idemp_r.
          assert (Hidx_val: Z.of_nat idx + 1 = AddrSz).
          { apply (f_equal Z.of_nat) in Hidx_next_eq.
            rewrite Nat2Z.inj_succ in Hidx_next_eq.
            rewrite Z2Nat.id in Hidx_next_eq by (pose proof AddrSz_nonneg; lia).
            exact Hidx_next_eq. }
          rewrite Hidx_val.
          rewrite two_pow_ExpSz_eq_AddrSz.
          apply Z_mod_same_full. }
        rewrite Haccum_0 in Hres_gt.
        lia.
Qed.

Lemma ctz_base_mod_pow2_zero : forall (base : bits AddrSz) (e_b : bits ExpSz),
  e_b = evalLetExpr (countTrailingZerosArray (mkBoolArray AddrSz (Var type (Bit AddrSz) base)) ExpSz) ->
  Zmod.unsigned base mod 2^(Zmod.unsigned e_b) = 0.
Proof.
  intros base e_b He_b.
  rewrite evalLetExpr_countTrailingZerosArray in He_b.
  assert (Hbound: (0 + Z.to_nat AddrSz <= Z.to_nat AddrSz)%nat) by lia.
  assert (Hidx_lt: (0 < Z.to_nat AddrSz)%nat) by (pose proof AddrSz_pos; lia).
  assert (Haccum: Zmod.unsigned (Zmod.zero : bits ExpSz) = Z.of_nat 0) by apply Zmod.unsigned_0.
  destruct (Zmod.unsigned e_b =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. rewrite Hz.
    change (2^0) with 1. apply Zmod_1_r.
  - apply Z.eqb_neq in Hz.
    pose proof (bits.unsigned_range e_b ltac:(apply ExpSz_nonneg)) as [Heb0 _].
    assert (Hgt: Z.of_nat 0 < Zmod.unsigned e_b) by lia.
    pose proof (@countTrailingZerosLoop_testbit_false base (Z.to_nat AddrSz) 0%nat (Zmod.zero : bits ExpSz) Hbound Hidx_lt Haccum) as Hfalse.
    rewrite <- He_b in Hfalse.
    apply testbit_low_zeros_mod; [ lia | ].
    intros i Hi.
    apply (Hfalse Hgt i).
    lia.
Qed.

Lemma bounds_roundDown_base_eq : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length true) ->
  let outBase := Zmod.to_Z (bounds@%"base") in
  outBase = Zmod.to_Z base.
Proof.
  intros base length bounds HB.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst outBase cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
  { subst ef e_roundDown.
    cbn [evalLetExpr evalExpr].
    destruct pick_b.
    - cbn [evalLetExpr evalExpr] in Hpick_b.
      apply eq_sym in Hpick_b.
      apply Z.ltb_lt in Hpick_b.
      rewrite He_init_eq, He_val in Hpick_b.
      lia.
    - rewrite He_init_eq, He_val. lia. }
  subst cram.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary evalBinary KindCustomInd].
  cbn [snd evalExpr].
  rewrite and_slu_mask by apply bits_ExpSz_range.
  rewrite and_all_ones.
  rewrite (to_Z_app_0 (n := AddrSz)); [ | apply AddrSz_nonneg ].
  unfold Zmod.to_Z.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  assert (H_ef_le_eb: Zmod.unsigned ef <= Zmod.unsigned e_b).
  { subst ef e_roundDown.
    cbn [evalLetExpr evalExpr].
    destruct pick_b.
    - lia.
    - cbn [evalLetExpr evalExpr] in Hpick_b.
      apply eq_sym in Hpick_b.
      apply Z.ltb_ge in Hpick_b. lia. }
  pose proof (bits.unsigned_range ef ltac:(apply ExpSz_nonneg)) as [Hef0 _].
  pose proof (ctz_base_mod_pow2_zero He_b) as Hctz.
  pose proof (multiple_divides (conj Hef0 H_ef_le_eb) Hctz) as Hbase_mod.
  pose proof (Z.div_mod (Zmod.unsigned base) (2^(Zmod.unsigned ef)) ltac:(apply Z.pow_nonzero; lia)) as Hdm.
  rewrite Hbase_mod in Hdm.
  lia.
Qed.

Lemma bounds_roundDown_m_norm : forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length true) ->
  let e := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  let m := Zmod.to_Z (bounds@%"m") in
  e > 0 -> 2^(CapBSz - 1) <= m.
Proof.
  intros base length bounds HB.
  subst bounds.
  apply evalLetPropGen_sound.
  cbn [evalLetPropGen Bounds].
  cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum].
  intros lenTrunc HlenTrunc
         clz Hclz
         e_init He_init
         d Hd
         mask_e Hmask_e
         base_mod_e Hbase_mod_e
         length_mod_e Hlength_mod_e
         sum_mod_e Hsum_mod_e
         iFloor HiFloor
         lost_sum Hlost_sum
         iCeil HiCeil
         m_raw Hm_raw
         b_e Hb_e
         isOverflow HisOverflow
         e_unsat He_unsat
         isESaturated HisESaturated
         e_normal He_normal
         m_raw_lsb Hm_raw_lsb
         inc_ovf Hinc_ovf
         m_ovf Hm_ovf
         m_normal Hm_normal
         e_b He_b
         pick_b Hpick_b
         e_roundDown He_roundDown
         m_roundDown Hm_roundDown
         ef Hef
         mf Hmf
         cram Hcram
         outBase HoutBase
         outLen HoutLen
         outTop HoutTop
         cE HcE
         mask_ef Hmask_ef
         base_mod_ef Hbase_mod_ef
         length_mod_ef Hlength_mod_ef.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (bits_ExpSz_range clz) as [Hclz_min Hclz_max].
  pose proof (e_init_val Hclz_bound) as He_val.
  assert (He_init_eq: e_init = Zmod.add (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) (Zmod.not clz)).
  { rewrite He_init. cbn [evalLetExpr evalExpr fold_left map].
    rewrite Zmod.add_0_l.
    change (evalNot clz) with (Zmod.not clz).
    change (evalExpr $(AddrSz + 1 - CapBSz)) with (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)).
    change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
    reflexivity. }
  assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
  { subst ef e_roundDown.
    cbn [evalLetExpr evalExpr].
    destruct pick_b.
    - cbn [evalLetExpr evalExpr] in Hpick_b.
      apply eq_sym in Hpick_b.
      apply Z.ltb_lt in Hpick_b.
      rewrite He_init_eq, He_val in Hpick_b.
      lia.
    - rewrite He_init_eq, He_val. lia. }
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    rewrite Heq in H_ef_bound.
    change (bits.of_Z ExpSz (-1)) with (Zmod.of_Z (2^ExpSz) (-1)) in H_ef_bound.
    rewrite Zmod.unsigned_of_Z in H_ef_bound.
    rewrite mod_neg1_m in H_ef_bound by (pose proof two_pow_ExpSz_pos; pose proof two_pow_ExpSz_eq_AddrSz; pose proof AddrSz_gt_1; lia).
    rewrite two_pow_ExpSz_eq_AddrSz in H_ef_bound.
    pose proof CapBSz_gt_2.
    lia. }
  cbn [snd evalExpr evalAndBinary evalBinary KindCustomInd].
  rewrite andb_true_l.
  rewrite cE_decode_id by exact Hef_ne.
  intros He_pos.
  unfold Zmod.to_Z in *.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m) in *.
  subst ef mf e_roundDown m_roundDown.
  cbn [evalLetExpr evalExpr].
  destruct pick_b.
  - change (InvDefault (Bit CapBSz)) with (bits.of_Z CapBSz (-1)).
    change (bits.of_Z CapBSz (-1)) with (Zmod.of_Z (2^CapBSz) (-1)).
    rewrite Zmod.unsigned_of_Z.
    assert (Hpow_gt1: 1 < 2^CapBSz) by (pose proof CapBSz_ge_2; change 1 with (2^0); apply Z.pow_lt_mono_r; lia).
    rewrite mod_neg1_m by exact Hpow_gt1.
    pose proof CapBSz_pos.
    assert (2^(CapBSz - 1) < 2^CapBSz) by (apply Z.pow_lt_mono_r; lia).
    lia.
  - subst d.
    cbn [evalLetExpr evalExpr].
    rewrite unsigned_firstn by (pose proof CapBSz_pos; lia).
    rewrite unsigned_firstn by (pose proof CapBSz_pos; pose proof CapBSz_lt_AddrSz; lia).
    rewrite Zmod.unsigned_sru by solve_unsigned_nonneg.
    rewrite He_init_eq, He_val.
    rewrite Z.shiftr_div_pow2 by lia.
    cbn [evalLetExpr evalExpr] in He_pos.
    assert (Hclz_bound': Zmod.unsigned clz <= AddrSz - CapBSz - 1).
    { rewrite He_init_eq, He_val in He_pos. lia. }
    assert (Hlen_pow: 2^(AddrSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned length).
    { apply length_ge_pow2_clz.
      - subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray.
      - exact Hclz_bound'. }
    assert (Hd_ge: 2^(CapBSz - 1) <= Zmod.unsigned length / 2^((AddrSz - CapBSz) - Zmod.unsigned clz)).
    { apply (@d_ge_pow2_CapBSz_sub_1 (Zmod.unsigned length) (Zmod.unsigned clz)); [ lia | exact Hlen_pow ]. }
    assert (Hclz_expr: clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray (AddrSz - CapBSz) (Var type (Bit (AddrSz - CapBSz)) (Zmod_lastn (AddrSz - CapBSz) length))) (Z.to_nat (AddrSz - CapBSz)) false Zmod.zero)).
    { subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray. }
    pose proof (@length_div_e0_lt_CapBSz length clz Hclz_expr Hclz_bound) as Hd_lt.
    assert (Hd_bound: 0 <= Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz) < 2^(CapBSz + 1)).
    { split; [ apply Z.div_pos; lia | ].
      assert (Hpow_step: 2^(CapBSz + 1) = 2 * 2^CapBSz).
      { rewrite Z.pow_add_r by (pose proof CapBSz_pos; lia). ring. }
      rewrite Hpow_step. pose proof two_pow_CapBSz_pos. lia. }
    rewrite (Z.mod_small (Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz))) by exact Hd_bound.
    rewrite (Z.mod_small (Zmod.unsigned length / 2 ^ ((AddrSz - CapBSz) - Zmod.unsigned clz))) by lia.
    exact Hd_ge.
Qed.

(* ========================================================================= *)
(* Final Complete Theorem: BoundsRoundDownProperties                         *)
(* ========================================================================= *)

Theorem BoundsRoundDownProperties :
  forall (base length : bits AddrSz) (bounds : type BoundsRes),
  bounds = evalLetExpr (Bounds base length true) ->
  let e := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  let m := Zmod.to_Z (bounds@%"m") in
  let outBase := Zmod.to_Z (bounds@%"base") in
  let outLength := Zmod.to_Z (bounds@%"length") in
  (* 1) outBase = requested base *)
  outBase = Zmod.to_Z base /\
  (* 2) outLength = m * 2^e, and outLength <= requested length *)
  outLength = m * 2^e /\
  outLength <= Zmod.to_Z length /\
  (* 3) MSB of m is 1 unless e is 0 *)
  (e > 0 -> 2^(CapBSz - 1) <= m).
Proof.
  intros base length bounds HB e m outBase outLength.
  repeat split.
  - apply (bounds_roundDown_base_eq HB).
  - apply (bounds_length_m_e (isRoundDown:=true) HB).
  - apply (bounds_roundDown_length_le HB).
  - apply (bounds_roundDown_m_norm HB).
Qed.

Print Assumptions BoundsMonotonic.
Print Assumptions BoundsRoundUpProperties.
Print Assumptions BoundsRoundDownProperties.
