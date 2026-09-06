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


(** * Architectural Constant Relations and Basic Properties
    These theorems capture the relations between architectural parameters
    (AddrSz, ExpSz, CapBSz, CapcTSz, Emax).
    Throughout the rest of this file, these constants are NEVER unfolded directly;
    instead, their properties and relationships are invoked via these theorems. *)

Theorem AddrSz_pos : 0 < AddrSz.
Proof. unfold AddrSz, Xlen. lia. Qed.

Theorem AddrSz_nonneg : 0 <= AddrSz.
Proof. pose proof AddrSz_pos. lia. Qed.

Theorem AddrSz_gt_1 : 1 < AddrSz.
Proof. unfold AddrSz, Xlen. lia. Qed.

Theorem mod_neg1_m : forall m, 1 < m -> (-1) mod m = m - 1.
Proof.
  intros m Hm.
  rewrite (Z.mod_unique (-1) m (-1) (m - 1)); [ reflexivity | lia | ring ].
Qed.

Theorem ExpSz_pos : 0 < ExpSz.
Proof. unfold ExpSz, LgAddrSz, AddrSz, Xlen. lia. Qed.

Theorem ExpSz_nonneg : 0 <= ExpSz.
Proof. pose proof ExpSz_pos. lia. Qed.

Theorem CapBSz_eq : CapBSz = CapcTSz + 1.
Proof. unfold CapBSz, CapcTSz. reflexivity. Qed.

Theorem CapBSz_pos : 0 < CapBSz.
Proof. unfold CapBSz, CapcTSz. lia. Qed.

Theorem CapBSz_ge_2 : 2 <= CapBSz.
Proof. unfold CapBSz, CapcTSz. lia. Qed.

Theorem CapBSz_gt_2 : 2 < CapBSz.
Proof. unfold CapBSz, CapcTSz. lia. Qed.

Theorem CapBSz_lt_AddrSz : CapBSz < AddrSz.
Proof. unfold CapBSz, CapcTSz, AddrSz, Xlen. lia. Qed.

Theorem AddrSz_sub_CapBSz_pos : 0 < AddrSz - CapBSz.
Proof. pose proof CapBSz_lt_AddrSz. lia. Qed.

Theorem AddrSz_sub_CapBSz_nonneg : 0 <= AddrSz - CapBSz.
Proof. pose proof CapBSz_lt_AddrSz. lia. Qed.

Theorem two_pow_ExpSz_eq_AddrSz : 2 ^ ExpSz = AddrSz.
Proof. unfold ExpSz, LgAddrSz, AddrSz, Xlen. reflexivity. Qed.

Theorem two_pow_ExpSz_pos : 0 < 2 ^ ExpSz.
Proof. rewrite two_pow_ExpSz_eq_AddrSz. apply AddrSz_pos. Qed.

Theorem two_pow_AddrSz_pos : 0 < 2 ^ AddrSz.
Proof. apply Z.pow_pos_nonneg; [lia | pose proof AddrSz_pos; lia]. Qed.

Theorem two_pow_CapBSz_pos : 0 < 2 ^ CapBSz.
Proof. apply Z.pow_pos_nonneg; [lia | pose proof CapBSz_pos; lia]. Qed.

Theorem two_pow_AddrSz_add_1_pos : 0 < 2 ^ (AddrSz + 1).
Proof. apply Z.pow_pos_nonneg; [lia | pose proof AddrSz_pos; lia]. Qed.

Theorem two_pow_AddrSz_add_1_gt_1 : 1 < 2 ^ (AddrSz + 1).
Proof. unfold AddrSz, Xlen. reflexivity. Qed.

Theorem two_pow_AddrSz_add_2_pos : 0 < 2 ^ (AddrSz + 2).
Proof. apply Z.pow_pos_nonneg; [lia | pose proof AddrSz_pos; lia]. Qed.

Theorem Emax_eq : Emax = 2 ^ ExpSz - CapcTSz.
Proof. unfold Emax, ExpSz, LgAddrSz, AddrSz, Xlen, CapcTSz. reflexivity. Qed.

Theorem Emax_eq_AddrSz_sub_CapcTSz : Emax = AddrSz - CapcTSz.
Proof. rewrite <- two_pow_ExpSz_eq_AddrSz. apply Emax_eq. Qed.

Theorem Emax_eq_AddrSz_add_1_sub_CapBSz : Emax = AddrSz + 1 - CapBSz.
Proof.
  rewrite CapBSz_eq.
  rewrite Emax_eq_AddrSz_sub_CapcTSz.
  lia.
Qed.

Theorem Emax_minus_1_eq_AddrSz_sub_CapBSz : Emax - 1 = AddrSz - CapBSz.
Proof.
  rewrite Emax_eq_AddrSz_add_1_sub_CapBSz.
  lia.
Qed.

Theorem Emax_pos : 0 < Emax.
Proof. unfold Emax, ExpSz, LgAddrSz, AddrSz, Xlen, CapcTSz. lia. Qed.

Theorem Emax_nonneg : 0 <= Emax.
Proof. pose proof Emax_pos. lia. Qed.

Theorem Emax_lt_AddrSz : Emax < AddrSz.
Proof. unfold Emax, ExpSz, LgAddrSz, AddrSz, Xlen, CapcTSz. lia. Qed.

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

Fixpoint evalLetProp {k} (le: LetExpr type k) (P: type k -> Prop) : Prop :=
  match le with
  | RetE e => P (evalExpr e)
  | SystemE ls cont => evalLetProp cont P
  | LetEx s k' le cont => let t := evalLetExpr le in evalLetProp (cont t) P
  | IfElseE s p k' t f cont =>
      if evalExpr p then evalLetProp (cont (evalLetExpr t)) P
                    else evalLetProp (cont (evalLetExpr f)) P
  end.

Lemma evalLetProp_sound : forall {k} (le: LetExpr type k) (P: type k -> Prop),
  evalLetProp le P -> P (evalLetExpr le).
Proof.
  fix evalLetProp_sound 2.
  intros k le P H.
  destruct le as [ e | ls cont | s k' le1 cont | s p k' t f cont ].
  - exact H.
  - apply (evalLetProp_sound _ cont P H).
  - apply (evalLetProp_sound _ (cont (evalLetExpr le1)) P H).
  - simpl in H. simpl.
    destruct (evalExpr p).
    + apply (evalLetProp_sound _ (cont (evalLetExpr t)) P H).
    + apply (evalLetProp_sound _ (cont (evalLetExpr f)) P H).
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

Lemma bounds_base_math : forall base length isRoundDown bounds,
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
         cE HcE.
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
  apply evalLetProp_sound.
  cbn [evalLetProp Bounds countLeadingZerosArray countLeadingZerosLoop countTrailingZerosArray countTrailingZerosLoop].
  cbv [readDiffTupleStr getFinStructOption getFinStruct forceOption readDiffTuple nth_pf fst snd
       String.eqb Ascii.eqb Bool.eqb mapDiffTuple finNum finLt Fst Snd].
  cbn [evalExpr evalAndBinary evalBinary KindCustomInd mapDiffTuple Fst Snd].
  cbn [evalExpr].
  match goal with
  | |- Zmod.to_Z ?t = (Zmod.to_Z ?b + Zmod.to_Z ?l) mod _ =>
      set (TOP := t) in *; set (BASE := b) in *; set (LEN := l) in *
  end.
  clearbody BASE LEN.
  unfold TOP.
  cbn [evalLetExpr evalExpr fold_left map].
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

Lemma roundDown_pick_b_math : forall len base_mod ef,
  0 <= ef ->
  0 <= base_mod ->
  2^CapBSz * 2^ef <= len ->
  2^CapBSz - 1 <= (len + base_mod + 2^ef - 1) / 2^ef.
Proof.
  intros len base_mod ef Hef Hbase Hlen.
  assert (Hpos: 0 < 2^ef) by (apply Z.pow_pos_nonneg; lia).
  assert (Hge: (2^CapBSz - 1) * 2^ef <= len + base_mod + 2^ef - 1).
  { replace ((2^CapBSz - 1) * 2^ef) with (2^CapBSz * 2^ef - 2^ef) by ring.
    lia. }
  rewrite (Z.mul_comm (2^CapBSz - 1) (2^ef)) in Hge.
  apply Z.div_le_lower_bound; [ exact Hpos | exact Hge ].
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

Lemma pow2_ef_le_length_clz : forall (len : Z) (ef clz : Z),
  0 <= ef ->
  0 <= clz <= AddrSz - CapBSz ->
  ef <= AddrSz - CapBSz - 1 - clz ->
  2^(AddrSz - 1 - clz) <= len ->
  2^CapBSz * 2^ef <= len.
Proof.
  intros len ef clz Hef Hclz Hef_le Hlen.
  rewrite <- Z.pow_add_r by (pose proof CapBSz_pos; lia).
  eapply Z.le_trans; [ | exact Hlen ].
  apply Z.pow_le_mono_r; lia.
Qed.

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
  do 23 (destruct i as [| i]; [
    intro Hlt; unfold readNatToFinType, mkBoolArray;
    change (Z.to_nat (AddrSz - CapBSz)) with 23%nat;
    change (_ <? 23)%nat with true;
    cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit
         evalOrBinary orb getDefault];
    rewrite readSameTuple_nth with (d := false);
    change (evalFromBit (k:=Array 23 Bool) w)
      with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w);
    cbn [finNum];
    rewrite evalFromBitArray_nth by lia;
    reflexivity
  | ]).
  intro Hlt; change (Z.to_nat (AddrSz - CapBSz)) with 23%nat in Hlt; lia.
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

Lemma bounds_length_roundDown_le : forall base length bounds,
  bounds = evalLetExpr (Bounds base length true) ->
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
         cE HcE.
  cbn [mapDiffTuple Fst Snd evalExpr].
  subst outLen cE.
  cbn [evalLetExpr evalExpr fold_left map ZeroExtend ZeroExtendTo evalAndBinary get_E_from_cE isAllOnes isZero InvDefault isEq KindCustomInd getDefault].
  set (cond := evalExpr (isNotZero (TruncMsb 1 (CapBSz - 1) #mf))).
  clearbody cond.
  assert (Hclz_bound: Zmod.unsigned clz <= AddrSz - CapBSz).
  { subst clz. rewrite evalLetExpr_countLeadingZerosArray. apply countLeadingZerosLoop_bound_CapBSz_0. }
  pose proof (e_init_val Hclz_bound) as He_val.
  pose proof (bits_ExpSz_range clz) as [H1 H2].
  assert (Hef_ne: ef <> bits.of_Z ExpSz (-1)).
  { intro Heq.
    assert (H_ef_bound: Zmod.unsigned ef <= AddrSz + 1 - CapBSz).
    { subst ef e_roundDown pick_b.
      cbn [evalLetExpr evalExpr].
      subst e_init.
      cbn [evalLetExpr evalExpr fold_left map evalNot].
      rewrite Zmod.add_0_l.
      change (evalNot clz) with (Zmod.not clz).
      change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)).
      destruct (_ <? _) eqn:H_slt.
      + apply Z.ltb_lt in H_slt.
        rewrite He_val in H_slt.
        clear -H_slt H1.
        lia.
      + rewrite He_val.
        clear -H1.
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
  destruct pick_b.
  - (* pick_b = true: mf = 511, ef = e_b *)
    subst ef mf e_roundDown m_roundDown.
    cbn [evalLetExpr evalExpr].
    rewrite Zmod.unsigned_slu.
    rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
    rewrite Z.shiftl_mul_pow2 by solve_unsigned_nonneg.
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.mul_nonneg_nonneg; [ solve_unsigned_nonneg | apply Z.pow_nonneg; lia ].
      - apply two_pow_AddrSz_add_1_pos. }
    apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
    cbn.
    change (Zmod.unsigned (Zmod.of_Z (2^CapBSz) (-1))) with (2^CapBSz - 1).
    assert (Heb_min: 0 <= Zmod.unsigned e_b) by solve_unsigned_nonneg.
    apply roundDown_pick_b_math.
    + exact Heb_min.
    + apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; [ lia | exact Heb_min ].
    + cbn [evalLetExpr evalExpr] in Hpick_b.
      apply eq_sym in Hpick_b.
      apply Z.ltb_lt in Hpick_b.
      subst e_init.
      cbn [evalLetExpr evalExpr fold_left map evalNot] in Hpick_b.
      rewrite Zmod.add_0_l in Hpick_b.
      change (evalNot clz) with (Zmod.not clz) in Hpick_b.
      change (bits.of_Z ExpSz (AddrSz + 1 - CapBSz)) with (Zmod.of_Z (2^ExpSz) (AddrSz + 1 - CapBSz)) in Hpick_b.
      rewrite He_val in Hpick_b.
      assert (Hclz_range: 0 <= Zmod.unsigned clz <= AddrSz - CapBSz) by lia.
      assert (Hclz_bound': Zmod.unsigned clz <= AddrSz - CapBSz - 1) by lia.
      assert (Hlen_pow: 2 ^ (AddrSz - 1 - Zmod.unsigned clz) <= Zmod.unsigned length).
      { apply length_ge_pow2_clz.
        - subst clz lenTrunc. apply evalLetExpr_countLeadingZerosArray.
        - exact Hclz_bound'. }
      apply (@pow2_ef_le_length_clz (Zmod.unsigned length) (Zmod.unsigned e_b) (Zmod.unsigned clz));
        [ lia | exact Hclz_range | lia | exact Hlen_pow ].
  - (* pick_b = false: mf = TruncLsb 1 CapBSz d, ef = e_init *)
    subst ef mf e_roundDown m_roundDown.
    cbn [evalLetExpr evalExpr].
    rewrite Zmod.unsigned_slu.
    rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
    rewrite Z.shiftl_mul_pow2 by solve_unsigned_nonneg.
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.mul_nonneg_nonneg; [ solve_unsigned_nonneg | apply Z.pow_nonneg; lia ].
      - apply two_pow_AddrSz_add_1_pos. }
    apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
    subst d.
    cbn [evalLetExpr evalExpr].
    eapply Z.le_trans.
    { rewrite unsigned_firstn by solve_lia.
      apply Z.mod_le.
      - apply (@to_Z_nonneg (CapBSz + 1) _); pose proof CapBSz_pos; lia.
      - apply two_pow_CapBSz_pos. }
    eapply Z.le_trans.
    { rewrite unsigned_firstn by solve_lia.
      apply Z.mod_le; [ solve_unsigned_nonneg | apply two_pow_AddrSz_pos ]. }
    rewrite unsigned_sru_pos by solve_unsigned_nonneg.
    rewrite Z.shiftr_div_pow2 by solve_unsigned_nonneg.
    apply div_add_ge.
    * apply Z.pow_pos_nonneg; [ lia | solve_unsigned_nonneg ].
    * solve_unsigned_nonneg.
    * apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; [ lia | solve_unsigned_nonneg ].
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
  change (Z.to_nat (AddrSz + 1 - CapBSz)) with 24%nat.
  do 24 (destruct i as [| i]; [
    intro Hlt; unfold readNatToFinType;
    change (PosDef.Pos.to_nat (Pos.of_succ_nat (Z.to_nat AddrSz - 1))) with 32%nat;
    change (_ <? Z.to_nat AddrSz)%nat with true;
    cbn [readDiffTuple finNum Fst Snd evalFromBit evalOrBinary orb getDefault];
    rewrite readSameTuple_nth with (d := false);
    cbn [finNum]; rewrite evalFromBitArray_nth by (change (Z.to_nat AddrSz) with 32%nat; lia); reflexivity
  | ]).
  intro Hlt; change (Z.to_nat (AddrSz + 1 - CapBSz)) with 24%nat in Hlt; lia.
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
         cE HcE.
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
    unfold Sgt in *; cbn [evalLetExpr evalExpr fold_left map].
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
    unfold Sgt in *; cbn [evalLetExpr evalExpr fold_left map].
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

(* Step 2: Since e_br <= E, 2^e_br divides 2^E. *)
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

(* Step 3: bounds.base = floor(base / 2^e_br) * 2^e_br >= ecap.base *)
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

(* Step 4: bounds.top <= ceil((base + length) / 2^e_br) * 2^e_br <= ecap.top *)
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


(* ====================================================================
   Proof of bounds_E_le_ecap_ECorrected.

   The lemma below used to be admitted above the arithmetic helper
   lemmas.  It is proved here, after the helpers it depends on, from
   three facts: a decoded capability spans at most 511 slots at its
   own exponent (ecap_span_le), a contained request is therefore no
   wider than 511 slots once aligned (aligned_request_width_le), and
   Bounds never selects an exponent above one at which the request
   fits (bounds_E_le_aligned_width).
   ==================================================================== *)

(** * Bit-vector value helpers *)

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

(** * Arithmetic core of the span bound *)

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

(** * Decoded span bound *)

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

(** * Connecting the span bound to DecodeCap *)

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

(** * Aligned containment width (proof-plan step 2) *)

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

(** * Arithmetic core of the no-overflow argument *)

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
         cE HcE.
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
      unfold Sgt.
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
      unfold Sgt.
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

(** * The selected exponent never exceeds the saturation bound *)

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
         cE HcE.
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

(** * The exponent comparison behind BoundsMonotonic *)

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
