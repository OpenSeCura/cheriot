From Stdlib Require Import List String Ascii ZArith Znumtheory Zmod Lia Bool.
From Guru Require Import Library Syntax Semantics Notations.
From Cheriot Require Import SpecDefines AluLatest.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Ltac z3_simplify := *)
(*   cbn -[ *)
(*     (* ========================================== *)
(*        Arrays and Loops (Syntax.v) *)
(*        ========================================== *) *)
(*     countLeadingZerosArray countTrailingZerosArray *)
(*     countLeadingZerosLoop countTrailingZerosLoop countOnesArray *)
(*     mkBoolArray *)

(*     (* ========================================== *)
(*        ZArith (BinIntDef.v + ZArith) *)
(*        ========================================== *) *)
(*     (* Core operations *) *)
(*     Z.add Z.sub Z.mul Z.div Z.modulo Z.quot Z.rem Z.pow Z.opp Z.succ Z.pred *)
(*     Z.square *)

(*     (* Comparisons *) *)
(*     Z.geb Z.leb Z.eqb Z.gtb Z.ltb *)
(*     Z.ge Z.le Z.gt Z.lt Z.eq Z.compare *)
(*     Z.max Z.min *)

(*     (* Bitwise *) *)
(*     Z.land Z.lor Z.lxor Z.ldiff Z.shiftl Z.shiftr Z.testbit *)
(*     Z.setbit Z.clearbit Z.lnot *)

(*     (* Misc / Types *) *)
(*     Z.abs Z.sgn Z.log2 Z.log2_up Z.even Z.odd Z.to_nat Z.of_nat *)
(*     Z.to_N Z.of_N Z.gcd Z.ggcd Z.sqrt Z.quot2 Z.iter *)

(*     (* ========================================== *)
(*        Zmod (ZmodDef.v) *)
(*        ========================================== *) *)
(*     (* Core arithmetic *) *)
(*     Zmod.add Zmod.sub Zmod.mul Zmod.udiv Zmod.umod Zmod.squot Zmod.srem *)
(*     Zmod.opp Zmod.inv Zmod.mdiv Zmod.pow Zmod.abs *)

(*     (* Bitwise *) *)
(*     Zmod.and Zmod.or Zmod.xor Zmod.not Zmod.ndn *)

(*     (* Shifts and slicing *) *)
(*     Zmod.slu Zmod.sru Zmod.srs *)
(*     Zmod.app Zmod.firstn Zmod.skipn Zmod.slice *)

(*     (* Equality and Constants *) *)
(*     Zmod.eqb Zmod.zero Zmod.one *)

(*     (* Conversions and Extracted states *) *)
(*     Zmod.to_Z Zmod.of_Z Zmod.of_small_Z Zmod.signed *)
(*     Zmod.elements Zmod.positives Zmod.negatives Zmod.invertibles *)
(*   ]. *)

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
  assert (H_pos: 0 < 2 ^ ExpSz) by reflexivity.
  destruct (Zmod.unsigned_range (evalExpr (get_E_from_cE (bounds@%"cE")))) as [[H0 H1] | [H0 | [H0 H1]]].
  - exact H0.
  - lia.
  - lia.
Qed.

Lemma add_0_r_bits5 : forall (accum: bits 5),
  (accum + 0)%Zmod = accum.
Proof.
  intros.
  apply Zmod.unsigned_inj.
  rewrite Zmod.unsigned_add.
  change (0%Zmod) with (Zmod.of_Z 32 0).
  rewrite Zmod.unsigned_of_Z.
  rewrite Z.mod_0_l by lia.
  rewrite Z.add_0_r.
  rewrite Z.mod_small.
  - reflexivity.
  - generalize (Zmod.unsigned_range accum); intros [H | [H | H]]; lia.
Qed.

Lemma unsigned_add_1_bits5 : forall (accum: bits 5),
  Zmod.unsigned accum + 1 < 32 ->
  Zmod.unsigned (accum + 1)%Zmod = Zmod.unsigned accum + 1.
Proof.
  intros accum H.
  rewrite Zmod.unsigned_add.
  change (1%Zmod) with (Zmod.of_Z 32 1).
  rewrite Zmod.unsigned_of_Z.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mod_small; [ reflexivity | ].
  generalize (Zmod.unsigned_range accum); intros [H0 | [H0 | H0]]; lia.
Qed.

Lemma countLeadingZerosLoop_bound_5 : forall ni arr count over (accum: bits 5),
  0 <= Zmod.unsigned accum ->
  Zmod.unsigned accum + Z.of_nat count < 32 ->
  Zmod.unsigned (evalLetExpr (@countLeadingZerosLoop type ni 5 arr count over accum)) <= Zmod.unsigned accum + Z.of_nat count.
Proof.
  induction count as [| m IHm]; intros over accum Hacc Hbound.
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
      rewrite add_0_r_bits5.
      assert (Hstep: Zmod.unsigned accum + Z.of_nat m < 32) by lia.
      generalize (IHm true accum Hacc Hstep); intros Hih.
      change (PosDef.Pos.of_succ_nat m) with (Pos.of_succ_nat m).
      replace (Z.pos (Pos.of_succ_nat m)) with (Z.succ (Z.of_nat m)) by (symmetry; apply Nat2Z.inj_succ).
      unfold Z.succ.
      match type of Hih with | ?L <= ?R => match goal with | |- ?L <= ?R2 =>
        assert (H_le: R <= R2) by (apply Z.add_le_mono_l; lia);
        exact (Z.le_trans _ _ _ Hih H_le)
      end end.
    + rewrite !Zmod.add_0_l.
      assert (Hbound1: Zmod.unsigned accum + 1 < 32) by lia.
      assert (Hmod: Zmod.unsigned (accum + 1)%Zmod = Zmod.unsigned accum + 1) by (apply unsigned_add_1_bits5; lia).
      assert (Hacc': 0 <= Zmod.unsigned (accum + 1)%Zmod) by (rewrite Hmod; lia).
      assert (Hstep: Zmod.unsigned (accum + 1)%Zmod + Z.of_nat m < 32) by (rewrite Hmod; lia).
      generalize (IHm false (accum + 1)%Zmod Hacc' Hstep); intros Hih.
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

Lemma countTrailingZerosLoop_bound_5 : forall ni arr count idx over (accum: bits 5),
  0 <= Zmod.unsigned accum ->
  Zmod.unsigned accum + Z.of_nat count < 32 ->
  Zmod.unsigned (evalLetExpr (@countTrailingZerosLoop type ni 5 arr idx count over accum)) <= Zmod.unsigned accum + Z.of_nat count.
Proof.
  induction count as [| m IHm]; intros idx over accum Hacc Hbound.
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
      rewrite add_0_r_bits5.
      assert (Hstep: Zmod.unsigned accum + Z.of_nat m < 32) by lia.
      generalize (IHm (S idx) true accum Hacc Hstep); intros Hih.
      change (PosDef.Pos.of_succ_nat m) with (Pos.of_succ_nat m).
      replace (Z.pos (Pos.of_succ_nat m)) with (Z.succ (Z.of_nat m)) by (symmetry; apply Nat2Z.inj_succ).
      unfold Z.succ.
      match type of Hih with | ?L <= ?R => match goal with | |- ?L <= ?R2 =>
        assert (H_le: R <= R2) by (apply Z.add_le_mono_l; lia);
        exact (Z.le_trans _ _ _ Hih H_le)
      end end.
    + rewrite !Zmod.add_0_l.
      assert (Hbound1: Zmod.unsigned accum + 1 < 32) by lia.
      assert (Hmod: Zmod.unsigned (accum + 1)%Zmod = Zmod.unsigned accum + 1) by (apply unsigned_add_1_bits5; lia).
      assert (Hacc': 0 <= Zmod.unsigned (accum + 1)%Zmod) by (rewrite Hmod; lia).
      assert (Hstep: Zmod.unsigned (accum + 1)%Zmod + Z.of_nat m < 32) by (rewrite Hmod; lia).
      generalize (IHm (S idx) false (accum + 1)%Zmod Hacc' Hstep); intros Hih.
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

Lemma countLeadingZerosArray_bound_5 : forall ni (arr: @Expr type (Array ni Bool)),
  (ni < 32)%nat ->
  Zmod.unsigned (evalLetExpr (@countLeadingZerosArray type ni arr 5)) <= Z.of_nat ni.
Proof.
  intros ni arr Hni.
  unfold countLeadingZerosArray.
  cbn [evalLetExpr evalExpr].
  assert (H_zero: Zmod.unsigned (0%Zmod : bits 5) = 0).
  { change (0%Zmod : bits 5) with (Zmod.of_Z 32 0). rewrite Zmod.unsigned_of_Z. reflexivity. }
  assert (H_acc: 0 <= Zmod.unsigned (0%Zmod : bits 5)) by (rewrite H_zero; lia).
  assert (H_bound: Zmod.unsigned (0%Zmod : bits 5) + Z.of_nat ni < 32) by (rewrite H_zero; lia).
  pose proof (@countLeadingZerosLoop_bound_5 ni arr ni false 0%Zmod H_acc H_bound) as Hloop.
  rewrite H_zero in Hloop.
  lia.
Qed.

Lemma bits_ExpSz_range : forall (b: bits ExpSz),
  0 <= Zmod.unsigned b <= 31.
Proof.
  intros b.
  generalize (Zmod.unsigned_range b).
  unfold ExpSz.
  change (2^5) with 32.
  intros [[H1 H2] | [H1 | [H1 H2]]]; lia.
Qed.

Lemma not_bits5_val : forall (b: bits 5),
  Zmod.unsigned (Zmod.not b) = 31 - Zmod.unsigned b.
Proof.
  intros b.
  unfold Zmod.not.
  rewrite Zmod.unsigned_of_Z.
  generalize (Zmod.unsigned_range b).
  unfold Z.lnot, Z.pred, ExpSz.
  change (2^5) with 32 in *.
  intros [[H1 H2] | [H1 | [H1 H2]]];
  [ symmetry; apply Z.mod_unique with (q := -1); lia | lia | lia ].
Qed.

Ltac solve_lia :=
  intros;
  change Xlen with 32 in *;
  change CapBSz with 9 in *; change AddrSz with 32 in *;
  change ExpSz with 5 in *;
  repeat match goal with
  | H : _ \/ _ \/ _ |- _ => destruct H as [[? ?]|[?|[? ?]]]
  end;
  repeat match goal with
  | H: context [2^32] |- _ => change (2^32) with 4294967296 in H
  | H: context [2^33] |- _ => change (2^33) with 8589934592 in H
  | H: context [2^34] |- _ => change (2^34) with 17179869184 in H
  | H: context [2^9] |- _ => change (2^9) with 512 in H
  | H: context [2^5] |- _ => change (2^5) with 32 in H
  | |- context [2^32] => change (2^32) with 4294967296
  | |- context [2^33] => change (2^33) with 8589934592
  | |- context [2^34] => change (2^34) with 17179869184
  | |- context [2^9] => change (2^9) with 512
  | |- context [2^5] => change (2^5) with 32
  end;
  lia.

Lemma e_init_not_31 : forall ni (arr: @Expr type (Array ni Bool)),
  (ni <= 23)%nat ->
  (0 + Zmod.of_Z 32 24 + Zmod.not (evalLetExpr (@countLeadingZerosLoop type ni 5 arr ni false 0%Zmod)))%Zmod <> Zmod.of_Z 32 (-1).
Proof.
  intros ni arr Hni H_eq.
  apply Nat2Z.inj_le in Hni.
  assert (H_zero: Zmod.unsigned (0%Zmod : bits 5) = 0).
  { change (0%Zmod : bits 5) with (Zmod.of_Z 32 0). rewrite Zmod.unsigned_of_Z. reflexivity. }
  assert (H_acc: 0 <= Zmod.unsigned (0%Zmod : bits 5)) by (rewrite H_zero; lia).
  assert (H_bound: Zmod.unsigned (0%Zmod : bits 5) + Z.of_nat ni < 32) by (rewrite H_zero; lia).
  pose proof (@countLeadingZerosLoop_bound_5 ni arr ni false 0%Zmod H_acc H_bound) as Hloop.
  rewrite H_zero in Hloop.
  apply (f_equal (@Zmod.unsigned 32)) in H_eq.
  rewrite !Zmod.unsigned_add in H_eq.
  rewrite not_bits5_val in H_eq.
  rewrite !Zmod.unsigned_of_Z in H_eq.
  change (24 mod 32) with 24 in H_eq.
  change ((-1) mod 32) with 31 in H_eq.
  change (Zmod.unsigned 0) with 0 in H_eq.
  change ((0 + 24) mod 32) with 24 in H_eq.
  set (z := Zmod.unsigned (evalLetExpr (countLeadingZerosLoop 5 arr ni false 0%Zmod))) in *.
  assert (Hz_range: 0 <= z <= 31) by (apply bits_ExpSz_range).
  assert (Hz_le: z <= 23) by lia.
  assert (Hmod: (24 + (31 - z)) mod 32 = 23 - z) by (symmetry; apply Z.mod_unique with (q := 1); lia).
  rewrite Hmod in H_eq.
  lia.
Qed.

Lemma e_init_val : forall (clz: bits 5),
  Zmod.unsigned clz <= 24 ->
  Zmod.unsigned (Zmod.add (Zmod.of_Z 32 25) (Zmod.not clz)) = 24 - Zmod.unsigned clz.
Proof.
  intros clz Hclz.
  rewrite Zmod.unsigned_add.
  rewrite not_bits5_val.
  rewrite Zmod.unsigned_of_Z.
  generalize (Zmod.unsigned_range clz).
  change (25 mod 32) with 25.
  intros [[H1 H2] | [H1 | [H1 H2]]];
  unfold ExpSz in *; change (2^5) with 32 in *;
  [ symmetry; apply Z.mod_unique with (q := 1); lia | lia | lia ].
Qed.

Lemma e_init_24_val : forall (clz: bits 5),
  Zmod.unsigned clz <= 23 ->
  Zmod.unsigned (Zmod.add (Zmod.of_Z 32 24) (Zmod.not clz)) = 23 - Zmod.unsigned clz.
Proof.
  intros clz Hclz.
  rewrite Zmod.unsigned_add.
  rewrite not_bits5_val.
  rewrite Zmod.unsigned_of_Z.
  generalize (Zmod.unsigned_range clz).
  change (24 mod 32) with 24.
  intros [[H1 H2] | [H1 | [H1 H2]]];
  unfold ExpSz in *; change (2^5) with 32 in *;
  [ symmetry; apply Z.mod_unique with (q := 1); lia | lia | lia ].
Qed.

Lemma e_init_24_plus_one_val : forall (clz: bits 5),
  Zmod.unsigned clz <= 23 ->
  Zmod.unsigned (Zmod.add (Zmod.add (Zmod.of_Z 32 24) (Zmod.not clz)) (Zmod.one : bits 5)) =
  (if Zmod.unsigned clz =? 0 then 24 else 24 - Zmod.unsigned clz).
Proof.
  intros clz Hclz.
  rewrite Zmod.unsigned_add.
  rewrite (e_init_24_val Hclz).
  change (Zmod.unsigned (Zmod.one : bits 5)) with 1.
  destruct (Zmod.unsigned clz =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz; rewrite Hz. reflexivity.
  - apply Z.eqb_neq in Hz.
    replace (23 - Zmod.unsigned clz + 1) with (24 - Zmod.unsigned clz) by lia.
    rewrite Z.mod_small.
    + reflexivity.
    + pose proof (Zmod.unsigned_range clz) as [[H1 H2] | [H1 | [H1 H2]]]; lia.
Qed.

Lemma bounds_E_bound : forall (bounds: type BoundsRes),
  0 <= Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) <= 31.
Proof.
  intros.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z ?x) with (Zmod.unsigned x).
  apply bits_ExpSz_range.
Qed.

Lemma ecap_E_bound : forall (cap: type Cap),
  0 <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))))) <= 31.
Proof.
  intros cap.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z ?x) with (Zmod.unsigned x).
  apply bits_ExpSz_range.
Qed.

Lemma ef_le_ECorrected_arith : forall (clz ef e_init ECorrected : Z),
  0 <= clz <= 18 ->
  e_init = 18 - clz ->
  ef <= e_init + 1 ->
  clz >= 19 - ECorrected ->
  0 <= ECorrected ->
  ef <= ECorrected.
Proof.
  intros.
  lia.
Qed.

Lemma bounds_E_le_ecap_len : forall (eb e_cap : Z),
  0 <= eb <= 31 ->
  0 <= e_cap <= 31 ->
  2^(eb + 12) <= 2^(e_cap + 12) ->
  eb <= e_cap.
Proof.
  intros eb e_cap Heb He_cap Hpow.
  apply Z.pow_le_mono_r_iff in Hpow; try lia.
Qed.

Lemma bounds_E_le_ecap_ECorrected : forall cap addr base length isRoundDown ecap bounds,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z base + Zmod.to_Z length <= Zmod.to_Z (ecap@%"top") ->
  Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))))).
Proof.
  intros cap addr base length isRoundDown ecap bounds H_ecap H_bounds [H_base_ge H_top_le].
  pose proof (bounds_E_bound bounds) as [Hb_min Hb_max].
  pose proof (ecap_E_bound cap) as [He_min He_max].
  unfold Zmod.to_Z in *.
  change (Zmod.Private_to_Z ?x) with (Zmod.unsigned x) in *.
  generalize (bits_ExpSz_range (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))))).
  intros [H_e1 H_e2].
  destruct (Z_le_gt_dec (Zmod.unsigned (evalExpr (get_E_from_cE (bounds@%"cE")))) (Zmod.unsigned (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))).
  - exact l.
  - admit.
Admitted.

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
  0 <= e <= 31 ->
  Zmod.unsigned (Zmod.and b (Zmod.slu (bits.of_Z (AddrSz+1) (-1)) e)) =
  (Zmod.unsigned b / 2^e) * 2^e.
Proof.
  intros.
  rewrite Zmod.unsigned_and.
  rewrite Zmod.unsigned_slu.
  rewrite Zmod.unsigned_of_Z.
  change (AddrSz + 1) with 33 in *.
  rewrite <- and_slu_mask_raw; try lia.
  apply Z.bits_inj_iff'. intros k Hk.
  destruct (Z_lt_le_dec k 33) as [Hlt | Hle].
  - (* k < 33 *)
    rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.land_spec.
    rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.shiftl_spec; try lia.
    destruct (Z_lt_le_dec k e) as [Hlte | Hgee].
    + rewrite (Z.testbit_neg_r (-1) (k - e)) by lia.
      rewrite (Z.testbit_neg_r (-1 mod 2^33) (k - e)) by lia.
      reflexivity.
    + rewrite !Z.mod_pow2_bits_low; try lia.
      reflexivity.
  - (* k >= 33 *)
    assert (H_b: Z.testbit (Zmod.unsigned b) k = false).
    { apply Z.testbit_false; try lia. replace (Zmod.unsigned b / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      generalize (Zmod.unsigned_range b). intros [[H1 H2] | [H1 | [H1 H2]]]; try lia.
      split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    assert (H_lhs: Z.testbit (Z.land (Zmod.unsigned b) (Z.shiftl (-1 mod 2 ^ 33) e mod 2 ^ 33) mod 2 ^ 33) k = false).
    { apply Z.testbit_false; try lia. replace (Z.land (Zmod.unsigned b) (Z.shiftl (-1 mod 2 ^ 33) e mod 2 ^ 33) mod 2 ^ 33 / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      assert (H_pos: 0 < 2^33) by reflexivity.
      generalize (Z.mod_pos_bound (Z.land (Zmod.unsigned b) (Z.shiftl (-1 mod 2^33) e mod 2^33)) (2^33) H_pos).
      intros [H1 H2]. split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    rewrite H_lhs.
    rewrite Z.land_spec.
    rewrite H_b. simpl. reflexivity.
  - generalize (Zmod.unsigned_range b). intros [[H1 H2] | [H1 | [H1 H2]]]; lia.
Qed.


Lemma and_all_ones : forall (b: bits (AddrSz+1)),
  Zmod.to_Z (Zmod.and (bits.of_Z (AddrSz+1) (-1)) b) = Zmod.to_Z b.
Proof.
  intros.
  rewrite Zmod.unsigned_and.
  rewrite Zmod.unsigned_of_Z.
  change (AddrSz + 1) with 33 in *.
  change ((-1) mod 2^33) with (Z.ones 33).
  apply Z.bits_inj_iff'. intros k Hk.
  destruct (Z_lt_le_dec k 33) as [Hlt | Hle].
  - rewrite Z.mod_pow2_bits_low; try lia.
    rewrite Z.land_spec.
    rewrite (Z.ones_spec_low 33 k) by lia.
    rewrite andb_true_l. reflexivity.
  - assert (H_b: Z.testbit (Zmod.unsigned b) k = false).
    { apply Z.testbit_false; try lia. replace (Zmod.unsigned b / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      generalize (Zmod.unsigned_range b). intros [[H1 H2] | [H1 | [H1 H2]]]; try lia.
      split; try lia. eapply Z.lt_le_trans; eauto. apply Z.pow_le_mono_r; lia. }
    assert (H_lhs: Z.testbit (Z.land (Z.ones 33) (Zmod.unsigned b) mod 2^33) k = false).
    { apply Z.testbit_false; try lia. replace (Z.land (Z.ones 33) (Zmod.unsigned b) mod 2^33 / 2 ^ k) with 0; try reflexivity. symmetry. apply Z.div_small.
      assert (H_pos: 0 < 2^33) by reflexivity.
      generalize (Z.mod_pos_bound (Z.land (Z.ones 33) (Zmod.unsigned b)) (2^33) H_pos).
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

Lemma cE_decode_id : forall (ef : bits 5) (cond : bool),
  ef <> Zmod.of_Z 32 (-1) ->
  (if Zmod.eqb (if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z 32 (-1) else ef) (Zmod.of_Z 32 (-1))
   then (0%Zmod : bits 5)
   else (if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z 32 (-1) else ef)) = ef.
Proof.
  intros ef cond H31.
  destruct (Zmod.eqb_spec (if (Zmod.eqb ef 0 && cond)%bool then Zmod.of_Z 32 (-1) else ef) (Zmod.of_Z 32 (-1))) as [H_eq | H_neq].
  - destruct (Zmod.eqb ef 0 && cond)%bool eqn:H_and.
    + apply andb_true_iff in H_and as [H_ef0 H_cond].
      apply Zmod.eqb_eq in H_ef0. subst ef.
      reflexivity.
    + congruence.
  - destruct (Zmod.eqb ef 0 && cond)%bool eqn:H_and.
    + congruence.
    + reflexivity.
Qed.

Ltac solve_not_31 :=
  intros H_disc;
  apply (f_equal (@Zmod.unsigned 32)) in H_disc;
  rewrite !Zmod.unsigned_of_Z in H_disc;
  change (24 mod 32) with 24 in H_disc;
  change ((-1) mod 32) with 31 in H_disc;
  discriminate.

Lemma bounds_base_math : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"base") = (Zmod.to_Z base / 2^ef) * 2^ef.
Proof.
  evalSimplGoal; intros; subst.
  unfold ExpSz in *.
  cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr get_E_from_cE isAllOnes
         mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit countTrailingZerosArray
         countTrailingZerosLoop] in *.
  unfold ef.
  rewrite and_slu_mask by (destruct isRoundDown; [ destruct (_ <? _) | destruct (_ <? _) ]; apply bits_ExpSz_range).
  rewrite and_all_ones.
  rewrite (to_Z_app_0 (n := 32)); [ | lia ].
  unfold Zmod.to_Z.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  destruct isRoundDown.
  - destruct (Zmod.unsigned _ <? Zmod.unsigned _) eqn:H_slt.
    + rewrite cE_decode_id; [ reflexivity | ].
      intros H_eq.
      apply (f_equal (@Zmod.unsigned 32)) in H_eq.
      rewrite Zmod.unsigned_of_Z in H_eq.
      change ((-1) mod 32) with 31 in H_eq.
      apply Z.ltb_lt in H_slt.
      rewrite H_eq in H_slt.
      match type of H_slt with
      | 31 < Zmod.unsigned ?X =>
          destruct (Zmod.unsigned_range X) as [[H1 H2] | [H1 | [H1 H2]]]; lia
      end.
    + rewrite cE_decode_id; [ reflexivity | ].
      apply e_init_not_31; lia.
  - destruct (_ <? _) eqn:H_sat.
    + rewrite cE_decode_id; [ reflexivity | solve_not_31 ].
    + rewrite cE_decode_id; [ reflexivity | ].
      intros H_eq.
      apply (f_equal (@Zmod.unsigned 32)) in H_eq.
      rewrite Zmod.unsigned_of_Z in H_eq.
      change ((-1) mod 32) with 31 in H_eq.
      apply Z.ltb_ge in H_sat.
      change (if negb (Z.sgn (23 mod 32) =? -1) && (Z.abs (23 mod 32) <? 32) then 23 mod 32 else 0) with 23 in H_sat.
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
  change (2 ^ (AddrSz + 2 - (AddrSz + 1))) with 2.
  change (0 mod 2) with 0.
  rewrite !Z.shiftl_0_l, !Z.lor_0_r.
  change (AddrSz + 1 + (AddrSz + 2 - (AddrSz + 1))) with (AddrSz + 2).
  rewrite <- Z.add_mod by (change AddrSz with 32; lia).
  reflexivity.
Qed.

Lemma div_le_add : forall a b c,
  0 < c ->
  a / c + b / c <= (a + b) / c.
Proof.
  intros.
  rewrite (Z.div_mod a c) at 2 by lia.
  rewrite (Z.div_mod b c) at 2 by lia.
  replace (c * (a / c) + a mod c + (c * (b / c) + b mod c)) with
    ((a / c + b / c) * c + (a mod c + b mod c)) by lia.
  rewrite Z_div_plus_full_l by lia.
  assert (0 <= (a mod c + b mod c) / c).
  { apply Z.div_pos; [ | lia ].
    pose proof (Z.mod_pos_bound a c H).
    pose proof (Z.mod_pos_bound b c H).
    lia. }
  lia.
Qed.

Lemma ceil_ge : forall x e,
  0 <= e ->
  (x / 2^e) * 2^e <= ((x + 2^e - 1) / 2^e) * 2^e.
Proof.
  intros.
  apply Z.mul_le_mono_nonneg_r.
  - apply Z.pow_nonneg; lia.
  - apply Z.div_le_mono; [ apply Z.pow_pos_nonneg; lia | lia ].
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
  - apply Z.pow_pos_nonneg; [ lia | change AddrSz with 32; lia ].
  - pose proof (@to_Z_nonneg (Xlen + 1) (bounds@%"base") ltac:(change Xlen with 32; lia)).
    pose proof (@to_Z_nonneg (Xlen + 1) (bounds@%"length") ltac:(change Xlen with 32; lia)).
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
  512 * 2^ef <= len ->
  511 <= (len + base_mod + 2^ef - 1) / 2^ef.
Proof.
  intros len base_mod ef Hef Hbase Hlen.
  assert (Hpos: 0 < 2^ef) by (apply Z.pow_pos_nonneg; lia).
  assert (511 * 2^ef <= 512 * 2^ef - 2^ef) by lia.
  assert (511 * 2^ef <= len + base_mod + 2^ef - 1) by lia.
  apply Z.div_le_lower_bound; [ exact Hpos | lia ].
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
  0 <= clz <= 23 ->
  ef <= 22 - clz ->
  2^(31 - clz) <= len ->
  512 * 2^ef <= len.
Proof.
  intros len ef clz Hef Hclz Hef_le Hlen.
  change 512 with (2^9).
  rewrite <- Z.pow_add_r by lia.
  eapply Z.le_trans; [ | exact Hlen ].
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma unsigned_lastn_23_32 : forall (x : bits 32),
  Zmod.unsigned (Zmod_lastn 23 x) = Zmod.unsigned x / 512.
Proof.
  intros x.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z x) with (Zmod.unsigned x).
  change (32 - 23) with 9.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^9) with 512.
  apply Z.mod_small.
  generalize (Zmod.unsigned_range x).
  change (2^32) with 4294967296.
  change (2^23) with 8388608.
  intros; split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
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

Lemma eval_readNatToFinType_mkBoolArray : forall (w : bits 23) (i : nat),
  (i < 23)%nat ->
  evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst (mkBoolArray 23 (Var type (Bit 23) w))) i) =
  Z.testbit (Zmod.unsigned w) (Z.of_nat i).
Proof.
  intros w i.
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (0 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (1 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (2 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (3 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (4 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (5 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (6 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (7 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (8 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (9 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (10 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (11 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (12 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (13 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (14 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (15 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (16 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (17 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (18 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (19 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (20 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (21 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  destruct i as [| i].
  { intro Hlt; unfold readNatToFinType, mkBoolArray; change (PosDef.Pos.to_nat 23) with 23%nat; change (Z.to_nat 23) with 23%nat; change (22 <? 23)%nat with true; cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit evalOrBinary orb getDefault]; rewrite readSameTuple_nth with (d := false); change (evalFromBit (k:=Array 23 Bool) w) with (@evalFromBitArray 23 Bool (fun v : type (Bit (kindSize Bool)) => Zmod.eqb v Zmod.one) w); cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity. }
  intro Hlt. lia.
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

Lemma countLeadingZerosLoop_23_ge_pow2 : forall (w : bits 23) (count : nat) (accum : bits 5),
  (count <= 23)%nat ->
  Zmod.unsigned accum = (23 - Z.of_nat count) ->
  Zmod.unsigned (evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray 23 (Var type (Bit 23) w)) count false accum)) <= 22 ->
  2^(22 - Zmod.unsigned (evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray 23 (Var type (Bit 23) w)) count false accum))) <= Zmod.unsigned w.
Proof.
  induction count as [| count' IHcount']; intros accum Hcount Haccum Hle.
  - unfold ExpSz in *; simpl countLeadingZerosLoop in *; cbn [evalLetExpr evalExpr] in Hle; rewrite Haccum in Hle; change (Z.of_nat 0) with 0 in Hle; lia.
  - unfold ExpSz in *.
    rewrite countLeadingZerosLoop_step in *.
    rewrite eval_readNatToFinType_mkBoolArray in * by lia.
    change (kindSize (Array 23 Bool)) with 23 in *.
    change (2^5) with 32 in *.
    destruct (Z.testbit (Zmod.unsigned w) (Z.of_nat count')) eqn:Hbit.
    + cbv zeta iota in *.
      assert (Hpos: 0 < 2^23) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Zmod.unsigned_pos_bound w Hpos) as [H0 H1].
      apply testbit_true_ge_pow2.
      * exact H0.
      * lia.
      * rewrite Haccum.
        replace (22 - (23 - Z.of_nat (S count'))) with (Z.of_nat count') by lia.
        exact Hbit.
    + cbv zeta iota in *.
      apply IHcount'.
      * lia.
      * unfold Zmod.add.
        cbn [Zmod.unsigned Zmod.of_small_Z].
        rewrite Haccum.
        change (@Zmod.unsigned 32 (@Zmod.one 32)) with 1.
        change (Z.abs 32) with 32.
        assert (Habs: (Z.abs (23 - Z.of_nat (S count') + 1) <? 32) = true) by (apply Z.ltb_lt; lia).
        rewrite Habs.
        rewrite Zmod.unsigned_of_small_Z by (apply Z.mod_small; lia).
        lia.
      * exact Hle.
Qed.

Lemma clz_23_ge_pow2 : forall (w : bits 23) (clz : bits 5),
  clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray 23 (Var type (Bit 23) w)) (PosDef.Pos.to_nat 23) false Zmod.zero) ->
  Zmod.unsigned clz <= 22 ->
  2^(22 - Zmod.unsigned clz) <= Zmod.unsigned w.
Proof.
  intros w clz Hclz Hclz_22.
  subst clz.
  change (PosDef.Pos.to_nat 23) with 23%nat.
  assert (H_zero: Zmod.unsigned (Zmod.zero : bits 5) = 0).
  { apply Zmod.unsigned_0. }
  apply (@countLeadingZerosLoop_23_ge_pow2 w 23%nat Zmod.zero); [ lia | rewrite H_zero; lia | exact Hclz_22 ].
Qed.

Lemma length_ge_pow2_clz : forall (length: bits 32) (clz: bits 5),
  clz = evalLetExpr (countLeadingZerosLoop ExpSz (mkBoolArray 23 (Var type (Bit 23) (Zmod_lastn 23 length))) (PosDef.Pos.to_nat 23) false Zmod.zero) ->
  Zmod.unsigned clz <= 22 ->
  2^(31 - Zmod.unsigned clz) <= Zmod.unsigned length.
Proof.
  intros length clz Hclz Hclz_22.
  pose proof (@clz_23_ge_pow2 (Zmod_lastn 23 length) clz Hclz Hclz_22) as Hw.
  pose proof (unsigned_lastn_23_32 length) as Hlastn.
  replace (31 - Zmod.unsigned clz) with (9 + (22 - Zmod.unsigned clz)) by lia.
  rewrite Z.pow_add_r by (pose proof (bits_ExpSz_range clz); lia).
  change (2^9) with 512.
  assert (Hlen_div: 512 * (Zmod.unsigned length / 512) <= Zmod.unsigned length).
  { apply Z.mul_div_le. lia. }
  rewrite <- Hlastn in Hlen_div.
  eapply Z.le_trans; [ | exact Hlen_div ].
  apply Z.mul_le_mono_nonneg_l; [ lia | exact Hw ].
Qed.

Lemma lt_23_le_22 : forall (x y : Z), x < 23 - y -> x <= 22 - y.
Proof. intros; lia. Qed.

Lemma lt_23_bound : forall (x y : Z), 0 <= x -> x < 23 - y -> y <= 22.
Proof. intros; lia. Qed.

Lemma bounds_length_roundDown_le : forall base length bounds,
  bounds = evalLetExpr (Bounds base length true) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"length") <= ((Zmod.to_Z length + (Zmod.to_Z base mod 2^ef) + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
  evalSimplGoal; intros; subst.
  unfold ExpSz in *.
  cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr get_E_from_cE
         mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit countTrailingZerosArray
         countTrailingZerosLoop countLeadingZerosArray countLeadingZerosLoop ZeroExtend ZeroExtendTo] in *.
  unfold Zmod.to_Z in *.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m) in *.
  fold ef.
  unfold ef in *.
  remember (_ <? _) as pick_b eqn:Hpick_b.
  destruct pick_b.
  - (* pick_b = true: mf = 511, e_b < e_init *)
    rewrite cE_decode_id; [ |
      intros H_eq;
      rewrite H_eq in Hpick_b;
      rewrite Zmod.unsigned_of_Z in Hpick_b;
      change ((-1) mod 32) with 31 in Hpick_b;
      symmetry in Hpick_b; apply Z.ltb_lt in Hpick_b;
      match type of Hpick_b with
      | 31 < Zmod.unsigned ?X =>
          destruct (Zmod.unsigned_range X) as [[H1 H2] | [H1 | [H1 H2]]]; lia
      end ].
    rewrite Zmod.unsigned_slu.
    rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
    rewrite Z.shiftl_mul_pow2 by (match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia).
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.mul_nonneg_nonneg.
        + match goal with |- 0 <= Zmod.unsigned ?X =>
            generalize (Zmod.unsigned_range X)
          end; solve_lia.
        + apply Z.pow_nonneg; lia.
      - change AddrSz with 32; change (2^(32+1)) with 8589934592; lia. }
    apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
    symmetry in Hpick_b; apply Z.ltb_lt in Hpick_b.
    cbn in |- *.
    change (PosDef.Pos.to_nat 23) with 23%nat in *.
    change (PosDef.Pos.to_nat 32) with 32%nat in *.
    change (Zmod.unsigned (Zmod.of_Z 512 (-1))) with 511.
    match goal with
    | |- context [2 ^ (Zmod.unsigned ?eb)] =>
        set (eb_bits := eb) in *
    end.
    clearbody eb_bits.
    assert (Heb_min: 0 <= Zmod.unsigned eb_bits) by (generalize (Zmod.unsigned_range eb_bits); solve_lia).
    apply roundDown_pick_b_math; [
      exact Heb_min
    | apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; [ lia | exact Heb_min ]
    | match goal with
      | H: context [Zmod.not (evalLetExpr ?clz_expr)] |- _ =>
          set (clz_bits := evalLetExpr clz_expr) in *
      end;
      rewrite e_init_24_val in Hpick_b by (unfold clz_bits; apply (countLeadingZerosArray_bound_5 (ni:=23%nat)); lia);
      assert (Hclz_range: 0 <= Zmod.unsigned clz_bits <= 23) by
        (split; [ generalize (Zmod.unsigned_range clz_bits); solve_lia | unfold clz_bits; apply (countLeadingZerosArray_bound_5 (ni:=23%nat)); lia ]);
      assert (Hlen_pow: 2 ^ (31 - Zmod.unsigned clz_bits) <= Zmod.unsigned length)
        by (apply length_ge_pow2_clz; [ reflexivity | apply (@lt_23_bound (Zmod.unsigned eb_bits) (Zmod.unsigned clz_bits)); [ lia | exact Hpick_b ] ]);
      clearbody clz_bits;
      apply (@pow2_ef_le_length_clz (Zmod.unsigned length) (Zmod.unsigned eb_bits) (Zmod.unsigned clz_bits));
        [ lia | lia | apply lt_23_le_22; exact Hpick_b | exact Hlen_pow ]
    ].
  - (* pick_b = false: mf = (length >> e_init) mod 512 *)
    rewrite cE_decode_id; [ | apply e_init_not_31; lia ].
    rewrite Zmod.unsigned_slu.
    rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
    rewrite Z.shiftl_mul_pow2 by (match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia).
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.mul_nonneg_nonneg.
        + match goal with |- 0 <= Zmod.unsigned ?X =>
            generalize (Zmod.unsigned_range X)
          end; solve_lia.
        + apply Z.pow_nonneg; lia.
      - change AddrSz with 32; change (2^(32+1)) with 8589934592; lia. }
    apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
    eapply Z.le_trans.
    { rewrite unsigned_firstn by solve_lia.
      apply Z.mod_le; [ | solve_lia ].
      match goal with |- 0 <= Zmod.unsigned ?X =>
        generalize (Zmod.unsigned_range X)
      end; solve_lia. }
    eapply Z.le_trans.
    { rewrite unsigned_firstn by solve_lia.
      apply Z.mod_le; [ | solve_lia ].
      match goal with |- 0 <= Zmod.unsigned ?X =>
        generalize (Zmod.unsigned_range X)
      end; solve_lia. }
    rewrite unsigned_sru_pos by (match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia).
    rewrite Z.shiftr_div_pow2 by (match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia).
    apply div_add_ge.
    + apply Z.pow_pos_nonneg; [ lia | match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia ].
    + generalize (Zmod.unsigned_range length); solve_lia.
    + apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; [ lia | match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia ].
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

Lemma iceil_le_math : forall (b_mod l_mod e_val : Z),
  0 <= b_mod < 2^e_val ->
  0 <= l_mod < 2^e_val ->
  0 <= e_val ->
  let s := b_mod + l_mod in
  s / 2^e_val + (if s mod 2^e_val =? 0 then 0 else 1) <=
  (b_mod + l_mod + 2^e_val - 1) / 2^e_val.
Proof.
  intros b_mod l_mod e_val Hb Hl He s.
  subst s.
  assert (Hpos: 0 < 2^e_val) by (apply Z.pow_pos_nonneg; lia).
  assert (Hs_nonneg: 0 <= b_mod + l_mod) by lia.
  rewrite ceil_div_eq; [ apply Z.le_refl | exact Hs_nonneg | exact Hpos ].
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

Lemma unsigned_app_8_1_zero : forall (b : bool),
  Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) (if b then (Zmod.one : bits 1) else (Zmod.zero : bits 1))) (Zmod.of_Z 256 128 : bits 8)) <= 257.
Proof.
  intros b.
  destruct b; unfold Zmod.app; rewrite !Zmod.unsigned_of_Z; vm_compute; discriminate.
Qed.

Lemma ltb_23_sub_Z : forall (z : Z),
  0 <= z ->
  (23 <? 23 - z) = false.
Proof.
  intros z Hz.
  apply Z.ltb_ge.
  lia.
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

Lemma not_slu_minus1_25 : forall (e : Z),
  0 <= e <= 23 ->
  Zmod.unsigned (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e)) = 2^e - 1.
Proof.
  intros e He.
  unfold Zmod.not.
  rewrite Zmod.unsigned_of_Z.
  rewrite Zmod.unsigned_slu.
  rewrite Zmod.unsigned_of_Z.
  change (2^25) with 33554432.
  change ((-1) mod 33554432) with (33554432 - 1).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_le: 2^e <= 2^23) by (apply Z.pow_le_mono_r; lia).
  change (2^23) with 8388608 in Hpow_le.
  replace ((33554432 - 1) * 2^e) with (33554432 * (2^e - 1) + (33554432 - 2^e)) by lia.
  assert (Hr_pos: 0 <= 33554432 - 2^e < 33554432) by lia.
  rewrite <- (Z.mod_unique_pos (33554432 * (2^e - 1) + (33554432 - 2^e)) 33554432 (2^e - 1) (33554432 - 2^e)); [ | exact Hr_pos | ring ].
  unfold Z.lnot, Z.pred.
  replace (- (33554432 - 2 ^ e) + -1) with (33554432 * (-1) + (2^e - 1)) by lia.
  rewrite <- (Z.mod_unique_pos (33554432 * (-1) + (2^e - 1)) 33554432 (-1) (2^e - 1)); [ reflexivity | lia | ring ].
Qed.

Lemma and_mask_e_25 : forall (w : bits 25) (e : Z),
  0 <= e <= 23 ->
  Zmod.unsigned (Zmod.and w (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e))) =
  Zmod.unsigned w mod 2^e.
Proof.
  intros w e He.
  rewrite Zmod.unsigned_and.
  rewrite not_slu_minus1_25 by exact He.
  change (2^25) with 33554432.
  rewrite test_land_ones by exact (proj1 He).
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_le: 2^e <= 2^23) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound (Zmod.unsigned w) (2^e) Hpow_pos) as [Hmod0 Hmod1].
  assert (Hbound: 0 <= Zmod.unsigned w mod 2^e < 33554432) by (change (2^23) with 8388608 in Hpow_le; lia).
  apply Z.mod_small.
  exact Hbound.
Qed.

Lemma and_minus1_25 : forall (w : bits 25),
  Zmod.unsigned (Zmod.and (Zmod.of_Z 33554432 (-1)) w) = Zmod.unsigned w.
Proof.
  intros w.
  rewrite Zmod.unsigned_and.
  rewrite Zmod.unsigned_of_Z.
  change (2^25) with 33554432.
  change ((-1) mod 33554432) with (33554432 - 1).
  change (33554432 - 1) with (Z.pred (2^25)).
  rewrite <- Z.ones_equiv.
  rewrite Z.land_comm.
  rewrite Z.land_ones by lia.
  assert (Hpos: 0 < 33554432) by lia.
  change (2^25) with 33554432 in *.
  pose proof (Zmod.unsigned_pos_bound w Hpos) as [Hw0 Hw1].
  rewrite Z.mod_mod by lia.
  apply Z.mod_small.
  lia.
Qed.

Lemma mod_mod_25_e : forall (z e : Z),
  0 <= e <= 23 ->
  (z mod 2^25) mod 2^e = z mod 2^e.
Proof.
  intros z e He.
  assert (Hpow_pos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_div: (2^e | 2^25)).
  { replace 25 with (e + (25 - e)) by lia.
    rewrite Z.pow_add_r by lia.
    exists (2^(25 - e)). ring. }
  rewrite (Z.mod_mod_divide z (2^25) (2^e) Hpow_div) by lia.
  reflexivity.
Qed.

Lemma unsigned_base_masked_mod : forall (base : bits 32) (e : Z),
  0 <= e <= 23 ->
  Zmod.unsigned (Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) (Zmod.firstn 25 base))
                    (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e))) =
  Zmod.unsigned base mod 2^e.
Proof.
  intros base e He.
  rewrite and_mask_e_25 by exact He.
  rewrite and_minus1_25.
  rewrite (unsigned_firstn (n:=25)) by lia.
  rewrite mod_mod_25_e by exact He.
  reflexivity.
Qed.

Lemma unsigned_sum_masked_div_le : forall (base length : bits 32) (e : Z),
  0 <= e <= 23 ->
  let base_masked := Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) (Zmod.firstn 25 base))
                              (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e)) in
  let length_masked := Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) (Zmod.firstn 25 length))
                                (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e)) in
  Zmod.unsigned (@Zmod.firstn 2 25 (Zmod.sru (base_masked + length_masked) e)) <=
  (Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e) / 2^e.
Proof.
  intros base length e He base_masked length_masked.
  eapply Z.le_trans.
  { rewrite (@unsigned_firstn 2 25) by lia.
    apply Z.mod_le.
    - apply (@to_Z_nonneg 25); lia.
    - change (2^2) with 4; lia. }
  rewrite Zmod.unsigned_sru.
  rewrite (Z.shiftr_div_pow2 _ e (proj1 He)).
  apply Z.div_le_mono.
  - apply Z.pow_pos_nonneg; lia.
  - rewrite Zmod.unsigned_add.
    eapply Z.le_trans.
    + apply Z.mod_le.
      * apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 25); lia.
      * change (2^25) with 33554432; lia.
    + subst base_masked length_masked.
      rewrite !unsigned_base_masked_mod by exact He.
      apply Z.le_refl.
  - exact (proj1 He).
Qed.

Lemma carry_true_implies_rem_nonneg : forall (base length : bits 32) (e : Z),
  0 <= e <= 23 ->
  let base_masked := Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) (Zmod.firstn 25 base))
                              (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e)) in
  let length_masked := Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) (Zmod.firstn 25 length))
                                (Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e)) in
  let sum_masked := (base_masked + length_masked)%Zmod in
  let mask_e := Zmod.not (Zmod.slu (Zmod.of_Z 33554432 (-1)) e) in
  negb (Zmod.eqb (Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) sum_masked) mask_e) (Zmod.zero : bits 25)) = true ->
  (Zmod.unsigned base mod 2^e + Zmod.unsigned length mod 2^e) mod 2^e <> 0.
Proof.
  intros base length e He base_masked length_masked sum_masked mask_e Hc.
  apply Bool.negb_true_iff in Hc.
  intro Hrem.
  assert (Heq: Zmod.and (Zmod.and (Zmod.of_Z 33554432 (-1)) sum_masked) mask_e = Zmod.zero).
  { apply Zmod.unsigned_inj.
    rewrite Zmod.unsigned_0.
    subst mask_e sum_masked.
    rewrite and_mask_e_25 by exact He.
    rewrite and_minus1_25.
    rewrite Zmod.unsigned_add.
    rewrite mod_mod_25_e by exact He.
    subst base_masked length_masked.
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
  512 <= (l + b mod 2^e + 2^e - 1) / 2^e ->
  256 <= (l + b mod (2^(e + 1)) + 2^(e + 1) - 1) / (2^(e + 1)).
Proof.
  intros l b e He Hl Hb H512.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(e + 1)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^(e + 1)) with (2 * 2^e) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hge: 512 * 2^e <= l + b mod 2^e + 2^e - 1).
  { assert (H512_mul: 512 * 2^e <= ((l + b mod 2^e + 2^e - 1) / 2^e) * 2^e) by (apply Z.mul_le_mono_nonneg_r; [ lia | exact H512 ]).
    pose proof (Z.mul_div_le (l + b mod 2^e + 2^e - 1) (2^e) Hpos). lia. }
  pose proof (@mod_pow2_le b e Hb He) as Hmod_le.
  assert (Hnum: 256 * (2 * 2^e) <= l + b mod (2 * 2^e) + 2 * 2^e - 1) by lia.
  rewrite (Z.mul_comm 256 (2 * 2^e)) in Hnum.
  apply Z.div_le_lower_bound; [ lia | exact Hnum ].
Qed.

Lemma unsigned_app_8_1_val : forall (b : bool),
  Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) (if b then (Zmod.one : bits 1) else (Zmod.zero : bits 1))) (Zmod.of_Z 256 128 : bits 8)) =
  256 + (if b then 1 else 0).
Proof.
  intros [|]; reflexivity.
Qed.

Lemma roundUp_ovf_math_inc : forall (l b e : Z),
  0 <= e ->
  0 <= l ->
  0 <= b ->
  512 <= (l + b mod 2^e + 2^e - 1) / 2^e ->
  b mod (2 * 2^e) >= b mod 2^e + 2^e ->
  257 <= (l + b mod (2^(e + 1)) + 2^(e + 1) - 1) / (2^(e + 1)).
Proof.
  intros l b e He Hl Hb H512 Hbe.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(e + 1)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^(e + 1)) with (2 * 2^e) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hge: 512 * 2^e <= l + b mod 2^e + 2^e - 1).
  { assert (H512_mul: 512 * 2^e <= ((l + b mod 2^e + 2^e - 1) / 2^e) * 2^e) by (apply Z.mul_le_mono_nonneg_r; [ lia | exact H512 ]).
    pose proof (Z.mul_div_le (l + b mod 2^e + 2^e - 1) (2^e) Hpos). lia. }
  assert (Hnum: 257 * (2 * 2^e) <= l + b mod (2 * 2^e) + 2 * 2^e - 1) by lia.
  rewrite (Z.mul_comm 257 (2 * 2^e)) in Hnum.
  apply Z.div_le_lower_bound; [ lia | exact Hnum ].
Qed.

Lemma roundUp_ovf_math_odd : forall (l b e : Z),
  0 <= e ->
  0 <= l ->
  0 <= b ->
  513 <= (l + b mod 2^e + 2^e - 1) / 2^e ->
  257 <= (l + b mod (2^(e + 1)) + 2^(e + 1) - 1) / (2^(e + 1)).
Proof.
  intros l b e He Hl Hb H513.
  assert (Hpos: 0 < 2^e) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos2: 0 < 2^(e + 1)) by (apply Z.pow_pos_nonneg; lia).
  replace (2^(e + 1)) with (2 * 2^e) by (rewrite Z.pow_add_r by lia; ring).
  assert (Hge: 513 * 2^e <= l + b mod 2^e + 2^e - 1).
  { assert (H513_mul: 513 * 2^e <= ((l + b mod 2^e + 2^e - 1) / 2^e) * 2^e) by (apply Z.mul_le_mono_nonneg_r; [ lia | exact H513 ]).
    pose proof (Z.mul_div_le (l + b mod 2^e + 2^e - 1) (2^e) Hpos). lia. }
  pose proof (@mod_pow2_le b e Hb He) as Hmod_le.
  assert (Hnum: 257 * (2 * 2^e) <= l + b mod (2 * 2^e) + 2 * 2^e - 1) by lia.
  rewrite (Z.mul_comm 257 (2 * 2^e)) in Hnum.
  apply Z.div_le_lower_bound; [ lia | exact Hnum ].
Qed.

Lemma unsigned_lastn_1_10 : forall (x : bits 10),
  Zmod.unsigned (Zmod_lastn 1 x) = Zmod.unsigned x / 512.
Proof.
  intros x.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  unfold Zmod.to_Z.
  change (Zmod.Private_to_Z x) with (Zmod.unsigned x).
  change (10 - 1) with 9.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^9) with 512.
  apply Z.mod_small.
  change (2^10) with 1024 in *.
  split.
  - apply Z.div_pos; [ generalize (Zmod.unsigned_range x); solve_lia | lia ].
  - apply Z.div_lt_upper_bound; [ lia | generalize (Zmod.unsigned_range x); solve_lia ].
Qed.

Lemma lastn_1_10_eq_1 : forall (x : bits 10),
  Zmod.eqb (Zmod_lastn 1 x) (Zmod.one : bits 1) = true ->
  512 <= Zmod.unsigned x.
Proof.
  intros x H.
  apply Zmod.eqb_eq in H.
  apply (f_equal Zmod.unsigned) in H.
  rewrite unsigned_lastn_1_10 in H.
  rewrite Zmod.unsigned_1 in H.
  change (2^1) with 2 in H.
  rewrite Z.mod_small in H by lia.
  assert (Zmod.unsigned x / 512 = 1) by exact H.
  pose proof (Z.mul_div_le (Zmod.unsigned x) 512 ltac:(lia)).
  generalize (Zmod.unsigned_range x); solve_lia.
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

Lemma odd_ge_512_implies_ge_513 : forall z : Z,
  512 <= z ->
  z mod 2 = 1 ->
  513 <= z.
Proof.
  intros z Hge Hodd.
  assert (Hz: z = 512 \/ 513 <= z \/ z < 512) by lia.
  destruct Hz as [-> | [H | H]]; [ | exact H | lia ].
  change (512 mod 2) with 0 in Hodd; discriminate.
Qed.

Lemma firstn_1_10_eq_1 : forall (x : bits 10),
  Zmod.eqb (Zmod.firstn 1 x) (Zmod.one : bits 1) = true ->
  512 <= Zmod.unsigned x ->
  513 <= Zmod.unsigned x.
Proof.
  intros x Hlsb Hge.
  apply Zmod.eqb_eq in Hlsb.
  apply (f_equal Zmod.unsigned) in Hlsb.
  assert (Hpos: (0 < 10)%Z) by easy.
  rewrite (unsigned_firstn_1 (n:=10%Z) x Hpos) in Hlsb.
  rewrite Zmod.unsigned_1 in Hlsb.
  change (2^1) with 2 in Hlsb.
  change (1 mod 2) with 1 in Hlsb.
  apply (odd_ge_512_implies_ge_513 Hge Hlsb).
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

Lemma readNatToFinType_evalFromBitArray32 : forall (w : bits 32) (i : nat),
  (i < 24)%nat ->
  readNatToFinType false (readSameTuple (@evalFromBitArray 32 Bool (fun v => Zmod.eqb v Zmod.one) w)) i =
  Z.testbit (Zmod.unsigned w) (Z.of_nat i).
Proof.
  intros w i.
  do 24 (destruct i as [| i]; [
    intro Hlt; unfold readNatToFinType; change (PosDef.Pos.to_nat (Pos.of_succ_nat (32 - 1))) with 32%nat;
    change (_ <? 32)%nat with true;
    cbn [readDiffTuple finNum Fst Snd evalFromBit evalOrBinary orb getDefault];
    rewrite readSameTuple_nth with (d := false);
    cbn [finNum]; rewrite evalFromBitArray_nth by lia; reflexivity
  | ]).
  intro; lia.
Qed.

Lemma bounds_length_roundUp_le : forall base length bounds,
  bounds = evalLetExpr (Bounds base length false) ->
  let ef := Zmod.to_Z (evalExpr (get_E_from_cE (bounds@%"cE"))) in
  Zmod.to_Z (bounds@%"length") <= ((Zmod.to_Z length + (Zmod.to_Z base mod 2^ef) + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
  evalSimplGoal; intros; subst.
  unfold ExpSz in *.
  unfold ef.
  cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr get_E_from_cE
         mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit countTrailingZerosArray
         countTrailingZerosLoop countLeadingZerosArray countLeadingZerosLoop ZeroExtend ZeroExtendTo] in *.
  unfold Zmod.to_Z in *.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m) in *.
  change (if negb (Z.sgn (23 mod 32) =? -1) && (Z.abs (23 mod 32) <? 32) then 23 mod 32 else 0) with 23 in *.
  rewrite cE_decode_id.
  2: {
    intro H_eq.
    match type of H_eq with
    | (if ?b then _ else _) = _ =>
        destruct b eqn:Hsat
    end.
    - change (if true then ?A else ?B) with A in H_eq.
      apply (f_equal (@Zmod.unsigned 32)) in H_eq.
      change (Zmod.unsigned (Zmod.of_Z 32 24)) with 24 in H_eq.
      change (Zmod.unsigned (Zmod.of_Z 32 (-1))) with 31 in H_eq.
      lia.
    - change (if false then ?A else ?B) with B in H_eq.
      apply (f_equal (@Zmod.unsigned 32)) in H_eq.
      change (Zmod.unsigned (Zmod.of_Z 32 (-1))) with 31 in H_eq.
      apply Z.ltb_ge in Hsat.
      rewrite H_eq in Hsat.
      lia.
  }
  fold ef.
  rewrite Zmod.unsigned_slu.
  rewrite (unsigned_app_zero (n:=CapBSz) (m:=AddrSz + 1 - CapBSz)) by solve_lia.
  rewrite Z.shiftl_mul_pow2 by (match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia).
  eapply Z.le_trans.
  { apply Z.mod_le.
    - apply Z.mul_nonneg_nonneg; [ match goal with |- 0 <= Zmod.unsigned ?X => generalize (Zmod.unsigned_range X) end; solve_lia | apply Z.pow_nonneg; lia ].
    - change AddrSz with 32; change (2^(32+1)) with 8589934592; lia. }
  apply Z.mul_le_mono_nonneg_r; [ apply Z.pow_nonneg; lia | ].
  unfold ef in *.
  match goal with
  | |- context [evalLetExpr (countLeadingZerosLoop 5 ?arr ?p ?b ?z)] =>
      set (clz_bits := evalLetExpr (countLeadingZerosLoop 5 arr p b z))
  end.
  repeat match goal with
  | |- context [evalLetExpr (countLeadingZerosLoop 5 ?arr ?p ?b ?z)] =>
      change (evalLetExpr (countLeadingZerosLoop 5 arr p b z)) with clz_bits in |- *
  end.
  pose proof (bits_ExpSz_range clz_bits) as [Hclz_min Hclz_max].
  assert (Hclz_23: Zmod.unsigned clz_bits <= 23) by (unfold clz_bits; apply (countLeadingZerosArray_bound_5 (ni:=23%nat)); lia).
  assert (He_nonneg: 0 <= 23 - Zmod.unsigned clz_bits) by lia.
  assert (Hb_nonneg: 0 <= Zmod.unsigned base) by (generalize (Zmod.unsigned_range base); solve_lia).
  assert (Hlen_nonneg: 0 <= Zmod.unsigned length) by (generalize (Zmod.unsigned_range length); solve_lia).
  pose proof (@e_init_24_plus_one_val clz_bits Hclz_23) as He_plus1_val.
  pose proof (@e_init_24_val clz_bits Hclz_23) as He_val.
  clearbody clz_bits.
  change (if negb (Z.sgn (23 mod 32) =? -1) && (Z.abs (23 mod 32) <? 32) then 23 mod 32 else 0) with 23 in *.
  match goal with
  | |- context [Zmod.unsigned (if ?cond then _ else _)] =>
      destruct cond eqn:Hovf
  end.
  - (* Overflow branch *)
    change (if false then (Zmod.of_Z 256 0) else ?X) with X.
    rewrite unsigned_app_8_1_val.
    change (Zmod.of_Z 32 0) with (Zmod.zero : bits 5) in |- *.
    change (Zmod.of_Z 32 1) with (Zmod.one : bits 5) in |- *.
    rewrite !Zmod.add_0_l in |- *.
    match goal with
    | |- context [23 <? Zmod.unsigned ?X] => set (E_ovf := X) in |- *
    end.
    assert (HE_ovf_val: Zmod.unsigned E_ovf = if Zmod.unsigned clz_bits =? 0 then 24 else 24 - Zmod.unsigned clz_bits).
    { subst E_ovf; unfold ExpSz in *; apply (e_init_24_plus_one_val (clz:=clz_bits)); lia. }
    rewrite HE_ovf_val in |- *.
    destruct (Zmod.unsigned clz_bits =? 0) eqn:Hclz0.
    + (* clz_bits = 0: ef = 24 *)
      change (23 <? 24) with true.
      change (if true then ?A else ?B) with A.
      change (Zmod.unsigned (Zmod.of_Z 32 24 : bits ExpSz)) with 24.
      match goal with
      | |- context [256 + (if ?cond then 1 else 0) <= _] =>
          destruct cond eqn:Hinc
      end.
      * change (if true then 1 else 0) with 1.
        apply orb_true_iff in Hinc.
        apply Z.eqb_eq in Hclz0.
        destruct Hinc as [Hlsb | Hbe].
        -- replace 24 with (23 - Zmod.unsigned clz_bits + 1) by lia.
           apply roundUp_ovf_math_odd; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
           change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hovf, Hlsb.
           change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hovf, Hlsb.
           rewrite !Zmod.add_0_l in Hovf.
           rewrite !e_init_24_val in Hovf, Hlsb by lia.
           pose proof (lastn_1_10_eq_1 Hovf) as H512_raw.
           pose proof (firstn_1_10_eq_1 Hlsb H512_raw) as H513_raw.
           eapply Z.le_trans; [ exact H513_raw | ].
           eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
             (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
           { rewrite Zmod.unsigned_add.
             eapply Z.le_trans.
             { apply Z.mod_le.
               - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
               - change (2^10) with 1024; lia. }
             apply Z.add_le_mono.
             + eapply Z.le_trans.
               - rewrite (unsigned_firstn (n:=10)) by lia.
                 apply Z.mod_le.
                 * apply (@to_Z_nonneg 32); lia.
                 * change (2^10) with 1024; lia.
               - rewrite Zmod.unsigned_sru.

                 match goal with |- Z.shiftr _ ?E <= _ =>
                   rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
                 end.
                 apply Z.le_refl.
                 exact He_nonneg.
             + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
               rewrite Zmod.unsigned_add.
               eapply Z.le_trans.
               { apply Z.mod_le.
                 - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                 - change (2^2) with 4; lia. }
               rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
               eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                             Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                            (if negb (Zmod.eqb _ _) then 1 else 0)).
               { apply Z.add_le_mono.
                 - apply unsigned_sum_masked_div_le.
                   split; [ exact He_nonneg | lia ].
                 - apply unsigned_if_one_zero. }
               apply carry_bound_math.
               * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * exact He_nonneg.
               * intros Hc.
                 apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
                 -- split; [ exact He_nonneg | lia ].
                 -- exact Hc. }
           rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
           apply Z.le_refl.
        -- replace 24 with (23 - Zmod.unsigned clz_bits + 1) by lia.
           apply roundUp_ovf_math_inc; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
           ++ change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hovf.
              change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hovf.
              rewrite !Zmod.add_0_l in Hovf.
              rewrite !e_init_24_val in Hovf by lia.
              pose proof (lastn_1_10_eq_1 Hovf) as H512_raw.
              eapply Z.le_trans; [ exact H512_raw | ].
              eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
                (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
              { rewrite Zmod.unsigned_add.
                eapply Z.le_trans.
                { apply Z.mod_le.
                  - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
                  - change (2^10) with 1024; lia. }
                apply Z.add_le_mono.
                + eapply Z.le_trans.
                  - rewrite (unsigned_firstn (n:=10)) by lia.
                    apply Z.mod_le.
                    * apply (@to_Z_nonneg 32); lia.
                    * change (2^10) with 1024; lia.
                  - rewrite Zmod.unsigned_sru.
   
                    match goal with |- Z.shiftr _ ?E <= _ =>
                      rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
                    end.
                    apply Z.le_refl.
                    exact He_nonneg.
                + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
                  rewrite Zmod.unsigned_add.
                  eapply Z.le_trans.
                  { apply Z.mod_le.
                    - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                    - change (2^2) with 4; lia. }
                  rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
                  eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                                Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                               (if negb (Zmod.eqb _ _) then 1 else 0)).
                  { apply Z.add_le_mono.
                    - apply unsigned_sum_masked_div_le.
                      split; [ exact He_nonneg | lia ].
                    - apply unsigned_if_one_zero. }
                  apply carry_bound_math.
                  * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                    apply Z.mod_pos_bound; exact Hpow_pos.
                  * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                    apply Z.mod_pos_bound; exact Hpow_pos.
                  * exact He_nonneg.
                  * intros Hc.
                    apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
                    -- split; [ exact He_nonneg | lia ].
                    -- exact Hc. }
              rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
              apply Z.le_refl.
           ++ change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hbe.
              change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hbe.
              rewrite !e_init_24_val in Hbe by lia.
              assert (Hlt24: (Z.to_nat (23 - Zmod.unsigned clz_bits) < 24)%nat).
              { apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia. }
              rewrite readNatToFinType_evalFromBitArray32 in Hbe by exact Hlt24.
              rewrite Z2Nat.id in Hbe by exact He_nonneg.
              apply testbit_true_mod_pow2_ge; [ exact He_nonneg | exact Hb_nonneg | exact Hbe ].
      * change (if false then 1 else 0) with 0.
        rewrite Z.add_0_r.
        apply Z.eqb_eq in Hclz0.
        replace 24 with (23 - Zmod.unsigned clz_bits + 1) by lia.
        apply roundUp_ovf_math; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
        change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hovf.
        change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hovf.
        rewrite !Zmod.add_0_l in Hovf.
        rewrite !e_init_24_val in Hovf by lia.
        eapply Z.le_trans; [ apply (lastn_1_10_eq_1 Hovf) | ].
        eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
          (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
        { rewrite Zmod.unsigned_add.
          eapply Z.le_trans.
          { apply Z.mod_le.
            - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
            - change (2^10) with 1024; lia. }
          apply Z.add_le_mono.
          + eapply Z.le_trans.
            - rewrite (unsigned_firstn (n:=10)) by lia.
              apply Z.mod_le.
              * apply (@to_Z_nonneg 32); lia.
              * change (2^10) with 1024; lia.
            - rewrite Zmod.unsigned_sru.

              match goal with |- Z.shiftr _ ?E <= _ =>
                rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
              end.
              apply Z.le_refl.
              exact He_nonneg.
          + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
            rewrite Zmod.unsigned_add.
            eapply Z.le_trans.
            { apply Z.mod_le.
              - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
              - change (2^2) with 4; lia. }
            rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
            eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                          Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                         (if negb (Zmod.eqb _ _) then 1 else 0)).
            { apply Z.add_le_mono.
              - apply unsigned_sum_masked_div_le.
                split; [ exact He_nonneg | lia ].
              - apply unsigned_if_one_zero. }
            apply carry_bound_math.
            * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * exact He_nonneg.
            * intros Hc.
              apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
              -- split; [ exact He_nonneg | lia ].
              -- exact Hc. }
        rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
        apply Z.le_refl.
    + (* clz_bits > 0: ef = 24 - clz_bits <= 23 *)
      change (if false then 24 else ?X) with X.
      assert (Hsat: (23 <? 24 - Zmod.unsigned clz_bits) = false).
      { apply Z.ltb_ge. destruct (Z.eqb_spec (Zmod.unsigned clz_bits) 0); [ congruence | pose proof (Zmod.unsigned_range clz_bits); lia ]. }
      rewrite Hsat.
      change (if false then (Zmod.of_Z 32 24 : bits 5) else ?X) with X.
      rewrite HE_ovf_val.
      match goal with
      | |- context [256 + (if ?cond then 1 else 0) <= _] =>
          destruct cond eqn:Hinc
      end.
      * change (if true then 1 else 0) with 1.
        apply orb_true_iff in Hinc.
        destruct Hinc as [Hlsb | Hbe].
        -- replace (24 - Zmod.unsigned clz_bits) with (23 - Zmod.unsigned clz_bits + 1) by lia.
           apply roundUp_ovf_math_odd; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
           change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hovf, Hlsb.
           change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hovf, Hlsb.
           rewrite !Zmod.add_0_l in Hovf.
           rewrite !e_init_24_val in Hovf, Hlsb by lia.
           pose proof (lastn_1_10_eq_1 Hovf) as H512_raw.
           pose proof (firstn_1_10_eq_1 Hlsb H512_raw) as H513_raw.
           eapply Z.le_trans; [ exact H513_raw | ].
           eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
             (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
           { rewrite Zmod.unsigned_add.
             eapply Z.le_trans.
             { apply Z.mod_le.
               - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
               - change (2^10) with 1024; lia. }
             apply Z.add_le_mono.
             + eapply Z.le_trans.
               - rewrite (unsigned_firstn (n:=10)) by lia.
                 apply Z.mod_le.
                 * apply (@to_Z_nonneg 32); lia.
                 * change (2^10) with 1024; lia.
               - rewrite Zmod.unsigned_sru.

                 match goal with |- Z.shiftr _ ?E <= _ =>
                   rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
                 end.
                 apply Z.le_refl.
                 exact He_nonneg.
             + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
               rewrite Zmod.unsigned_add.
               eapply Z.le_trans.
               { apply Z.mod_le.
                 - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                 - change (2^2) with 4; lia. }
               rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
               eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                             Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                            (if negb (Zmod.eqb _ _) then 1 else 0)).
               { apply Z.add_le_mono.
                 - apply unsigned_sum_masked_div_le.
                   split; [ exact He_nonneg | lia ].
                 - apply unsigned_if_one_zero. }
               apply carry_bound_math.
               * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                 apply Z.mod_pos_bound; exact Hpow_pos.
               * exact He_nonneg.
               * intros Hc.
                 apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
                 -- split; [ exact He_nonneg | lia ].
                 -- exact Hc. }
           rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
           apply Z.le_refl.
        -- replace (24 - Zmod.unsigned clz_bits) with (23 - Zmod.unsigned clz_bits + 1) by lia.
           apply roundUp_ovf_math_inc; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
           ++ change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hovf.
              change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hovf.
              rewrite !Zmod.add_0_l in Hovf.
              rewrite !e_init_24_val in Hovf by lia.
              pose proof (lastn_1_10_eq_1 Hovf) as H512_raw.
              eapply Z.le_trans; [ exact H512_raw | ].
              eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
                (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
              { rewrite Zmod.unsigned_add.
                eapply Z.le_trans.
                { apply Z.mod_le.
                  - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
                  - change (2^10) with 1024; lia. }
                apply Z.add_le_mono.
                + eapply Z.le_trans.
                  - rewrite (unsigned_firstn (n:=10)) by lia.
                    apply Z.mod_le.
                    * apply (@to_Z_nonneg 32); lia.
                    * change (2^10) with 1024; lia.
                  - rewrite Zmod.unsigned_sru.
   
                    match goal with |- Z.shiftr _ ?E <= _ =>
                      rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
                    end.
                    apply Z.le_refl.
                    exact He_nonneg.
                + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
                  rewrite Zmod.unsigned_add.
                  eapply Z.le_trans.
                  { apply Z.mod_le.
                    - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
                    - change (2^2) with 4; lia. }
                  rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
                  eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                                Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                               (if negb (Zmod.eqb _ _) then 1 else 0)).
                  { apply Z.add_le_mono.
                    - apply unsigned_sum_masked_div_le.
                      split; [ exact He_nonneg | lia ].
                    - apply unsigned_if_one_zero. }
                  apply carry_bound_math.
                  * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                    apply Z.mod_pos_bound; exact Hpow_pos.
                  * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
                    apply Z.mod_pos_bound; exact Hpow_pos.
                  * exact He_nonneg.
                  * intros Hc.
                    apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
                    -- split; [ exact He_nonneg | lia ].
                    -- exact Hc. }
              rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
              apply Z.le_refl.
           ++ change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hbe.
              change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hbe.
              rewrite !e_init_24_val in Hbe by lia.
              assert (Hlt24: (Z.to_nat (23 - Zmod.unsigned clz_bits) < 24)%nat).
              { apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia. }
              rewrite readNatToFinType_evalFromBitArray32 in Hbe by exact Hlt24.
              rewrite Z2Nat.id in Hbe by exact He_nonneg.
              apply testbit_true_mod_pow2_ge; [ exact He_nonneg | exact Hb_nonneg | exact Hbe ].
      * change (if false then 1 else 0) with 0.
        rewrite Z.add_0_r.
        replace (24 - Zmod.unsigned clz_bits) with (23 - Zmod.unsigned clz_bits + 1) by lia.
        apply roundUp_ovf_math; try lia; try exact Hb_nonneg; try exact Hlen_nonneg.
        change (Zmod.of_Z 32 0) with (Zmod.zero : bits ExpSz) in Hovf.
        change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits ExpSz) in Hovf.
        rewrite !Zmod.add_0_l in Hovf.
        rewrite !e_init_24_val in Hovf by lia.
        eapply Z.le_trans; [ apply (lastn_1_10_eq_1 Hovf) | ].
        eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
          (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
        { rewrite Zmod.unsigned_add.
          eapply Z.le_trans.
          { apply Z.mod_le.
            - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
            - change (2^10) with 1024; lia. }
          apply Z.add_le_mono.
          + eapply Z.le_trans.
            - rewrite (unsigned_firstn (n:=10)) by lia.
              apply Z.mod_le.
              * apply (@to_Z_nonneg 32); lia.
              * change (2^10) with 1024; lia.
            - rewrite Zmod.unsigned_sru.

              match goal with |- Z.shiftr _ ?E <= _ =>
                rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
              end.
              apply Z.le_refl.
              exact He_nonneg.
          + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
            rewrite Zmod.unsigned_add.
            eapply Z.le_trans.
            { apply Z.mod_le.
              - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
              - change (2^2) with 4; lia. }
            rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
            eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                          Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                         (if negb (Zmod.eqb _ _) then 1 else 0)).
            { apply Z.add_le_mono.
              - apply unsigned_sum_masked_div_le.
                split; [ exact He_nonneg | lia ].
              - apply unsigned_if_one_zero. }
            apply carry_bound_math.
            * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
              apply Z.mod_pos_bound; exact Hpow_pos.
            * exact He_nonneg.
            * intros Hc.
              apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
              -- split; [ exact He_nonneg | lia ].
              -- exact Hc. }
        rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
        apply Z.le_refl.
  - (* Non-overflow branch *)
    eapply Z.le_trans.
    { rewrite (unsigned_firstn (n:=CapBSz)) by (change CapBSz with 9; lia).
      apply Z.mod_le.
      - apply (@to_Z_nonneg (CapBSz + 1)); change CapBSz with 9; lia.
      - apply Z.pow_pos_nonneg; [ lia | change CapBSz with 9; lia ]. }
    rewrite Zmod.unsigned_add.
    eapply Z.le_trans.
    { apply Z.mod_le.
      - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 10); lia.
      - change (2^10) with 1024; lia. }
    change (if negb (Z.sgn (23 mod 32) =? -1) && (Z.abs (23 mod 32) <? 32) then 23 mod 32 else 0) with 23 in *.
    change (Zmod.of_Z 32 0) with (Zmod.zero : bits 5) in *.
    change (Zmod.of_Z 32 24) with (Zmod.of_Z 32 24 : bits 5) in *.
    rewrite !Zmod.add_0_l, !Zmod.add_0_r in *.
    rewrite !e_init_24_val by lia.
    assert (Hsat_false: forall x, 0 <= x -> (23 <? 23 - x) = false) by (intros; apply Z.ltb_ge; lia).
    rewrite !Hsat_false by exact Hclz_min.
    change (if false then (Zmod.of_Z 32 24 : bits 5) else ?X) with X.
    rewrite !e_init_24_val by lia.
    eapply Z.le_trans with (m := Zmod.unsigned length / 2^(23 - Zmod.unsigned clz_bits) +
      (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) + Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits) + 2^(23 - Zmod.unsigned clz_bits) - 1) / 2^(23 - Zmod.unsigned clz_bits)).
    { apply Z.add_le_mono.
      + eapply Z.le_trans.
        - rewrite (unsigned_firstn (n:=10)) by lia.
          apply Z.mod_le.
          * apply (@to_Z_nonneg 32); lia.
          * change (2^10) with 1024; lia.
        - rewrite Zmod.unsigned_sru.
          match goal with |- Z.shiftr _ ?E <= _ =>
            rewrite (Z.shiftr_div_pow2 (Zmod.unsigned length) E He_nonneg)
          end.
          apply Z.le_refl.
          exact He_nonneg.
      + rewrite (unsigned_app_zero (n:=2) (m:=8)) by solve_lia.
        rewrite Zmod.unsigned_add.
        eapply Z.le_trans.
        { apply Z.mod_le.
          - apply Z.add_nonneg_nonneg; apply (@to_Z_nonneg 2); lia.
          - change (2^2) with 4; lia. }
        rewrite (unsigned_app_zero (n:=1) (m:=1)) by solve_lia.
        eapply Z.le_trans with (m := (Zmod.unsigned base mod 2^(23 - Zmod.unsigned clz_bits) +
                                      Zmod.unsigned length mod 2^(23 - Zmod.unsigned clz_bits)) / 2^(23 - Zmod.unsigned clz_bits) +
                                     (if negb (Zmod.eqb _ _) then 1 else 0)).
        { apply Z.add_le_mono.
          - apply unsigned_sum_masked_div_le.
            split; [ exact He_nonneg | pose proof (Zmod.unsigned_range clz_bits); lia ].
          - apply unsigned_if_one_zero. }
        apply carry_bound_math.
        * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
          apply Z.mod_pos_bound; exact Hpow_pos.
        * assert (Hpow_pos: 0 < 2^(23 - Zmod.unsigned clz_bits)) by (apply Z.pow_pos_nonneg; lia).
          apply Z.mod_pos_bound; exact Hpow_pos.
        * exact He_nonneg.
        * intros Hc.
          apply (carry_true_implies_rem_nonneg (base:=base) (length:=length) (e:=23 - Zmod.unsigned clz_bits)).
          -- split; [ exact He_nonneg | pose proof (Zmod.unsigned_range clz_bits); lia ].
          -- exact Hc. }
    rewrite (@roundUp_no_ovf_math (Zmod.unsigned length) (Zmod.unsigned base) (23 - Zmod.unsigned clz_bits) He_nonneg Hb_nonneg Hlen_nonneg).
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
  assert (Hbase_ge0: 0 <= Zmod.unsigned base) by (apply (@to_Z_nonneg Xlen base); change Xlen with 32; lia).
  assert (Hlen_ge0: 0 <= Zmod.unsigned length) by (apply (@to_Z_nonneg Xlen length); change Xlen with 32; lia).
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
      generalize (Zmod.unsigned_range Y)
  end.
  intros HH. unfold ExpSz in *. change (Z.pow_pos 2 5) with 32 in *.
  match goal with
  | |- context [ Z.shiftl _ ?e ] =>
      remember e as eCorr in *; clear HeqeCorr
  end.
  assert (0 <= eCorr <= 31) as Hbounds.
  {
    destruct HH as [H1 | [H2 | H3]].
    - clear -H1; lia.
    - cbv in H2; discriminate.
    - clear -H3; lia.
  }
  rewrite Z.shiftl_mul_pow2; [| clear -Hbounds; destruct Hbounds; lia].
  unfold AddrSz, Xlen, LgXlen, CapBSz, LgAddrSz.
  change (0 + 14 + (32 - 14) + (32 + 1 - (0 + 14 + (32 - 14)))) with 33.
  apply multiple.
  clear -Hbounds; destruct Hbounds; lia.
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
      generalize (Zmod.unsigned_range Y)
  end.
  intros HH. unfold ExpSz in *. change (Z.pow_pos 2 5) with 32 in *.
  match goal with
  | |- context [ Z.shiftl _ ?e ] =>
      remember e as eCorr in *; clear HeqeCorr
  end.
  assert (0 <= eCorr <= 31) as Hbounds.
  {
    destruct HH as [H1 | [H2 | H3]].
    - clear -H1; lia.
    - cbv in H2; discriminate.
    - clear -H3; lia.
  }
  rewrite Z.shiftl_mul_pow2; [| clear -Hbounds; destruct Hbounds; lia].
  unfold AddrSz, Xlen, LgXlen, CapBSz, LgAddrSz.
  change (0 + 14 + (32 - 14) + (32 + 1 - (0 + 14 + (32 - 14)))) with 33.
  apply multiple.
  clear -Hbounds; destruct Hbounds; lia.
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

Theorem BoundsMonotonic cap addr base length isRoundDown:
  let ecap : type ECap := evalLetExpr (DecodeCap cap addr) in
  let bounds : type BoundsRes := evalLetExpr (Bounds base length isRoundDown) in
  (Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z base + Zmod.to_Z length <= Zmod.to_Z (ecap@%"top")) ->
  (Zmod.to_Z (bounds@%"base") >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (bounds@%"top") <= Zmod.to_Z (ecap@%"top")).
Proof.
  intros ecap bounds H_in_bounds.
  destruct H_in_bounds as [H_base_ge H_top_le].

  assert (H_no_wrap : Zmod.to_Z base + Zmod.to_Z length < Z.pow 2 (Xlen + 1)).
  { assert (Hb_lt : Zmod.to_Z base < Z.pow 2 Xlen).
    { apply pow2_width.
      unfold Xlen.
      lia.
    }
    assert (Hl_lt : Zmod.to_Z length < Z.pow 2 Xlen).
    { apply pow2_width.
      unfold Xlen.
      lia.
    }
    simpl.
    simpl in Hb_lt, Hl_lt.
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
