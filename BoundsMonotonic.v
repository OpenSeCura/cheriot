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
  0 <= Zmod.to_Z (bounds@%"E").
Proof.
  intros. unfold Zmod.to_Z.
  assert (H_pos: 0 < 2 ^ ExpSz) by reflexivity.
  destruct (Zmod.unsigned_range (bounds@%"E")) as [[H0 H1] | [H0 | [H0 H1]]].
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

Lemma bounds_E_bound : forall (bounds: type BoundsRes),
  0 <= Zmod.to_Z (bounds@%"E") <= 31.
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

Lemma bounds_E_le_ecap_ECorrected : forall cap addr base length isRoundDown ecap bounds,
  ecap = evalLetExpr (DecodeCap cap addr) ->
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (base + length) <= Zmod.to_Z (ecap@%"top") ->
  Zmod.to_Z (bounds@%"E") <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE")))))).
Proof.
  intros.
  pose proof (bounds_E_bound bounds) as Hb.
  pose proof (ecap_E_bound cap) as He.
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

Lemma to_Z_app_0 : forall (b : bits Xlen),
  Zmod.to_Z (Zmod.app b (0%Zmod : bits 1)) = Zmod.to_Z b.
Proof.
  intros.
  unfold Zmod.to_Z, Zmod.app.
  change (@Zmod.Private_to_Z ?m) with (@Zmod.unsigned m).
  rewrite Zmod.unsigned_of_Z.
  change (Zmod.unsigned (0%Zmod : bits 1)) with 0.
  rewrite Z.shiftl_0_l, Z.lor_0_r.
  change (Xlen + 1) with 33.
  rewrite Z.mod_small; [ reflexivity | ].
  unfold Xlen in *.
  generalize (Zmod.unsigned_range b).
  lia.
Qed.

Lemma bounds_base_math : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  let ef := Zmod.to_Z (bounds@%"E") in
  Zmod.to_Z (bounds@%"base") = (Zmod.to_Z base / 2^ef) * 2^ef.
Proof.
  evalSimplGoal; intros; subst.
  cbn [evalLetExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
         finNum Fst Snd evalExpr
         mapDiffTuple Fst Snd snd evalAndBinary fold_left map InvDefault evalFromBit countTrailingZerosArray
         countTrailingZerosLoop] in *.
  fold ef.
  rewrite and_slu_mask.
  - rewrite and_all_ones.
    rewrite to_Z_app_0.
    reflexivity.
  - unfold ef.
    destruct isRoundDown; [ destruct (_ <? _) | destruct (_ <? _) ];
    apply bits_ExpSz_range.
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

Lemma bounds_top_math : forall base length isRoundDown bounds,
  bounds = evalLetExpr (Bounds base length isRoundDown) ->
  Zmod.to_Z base + Zmod.to_Z length < 8589934592 ->
  let ef := Zmod.to_Z (bounds@%"E") in
  Zmod.to_Z (bounds@%"top") <= ((Zmod.to_Z (base + length) + 2^ef - 1) / 2^ef) * 2^ef.
Proof.
Admitted.

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
  (Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (base + length) <= Zmod.to_Z (ecap@%"top")) ->
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

  assert (H_E_nonneg : 0 <= Zmod.to_Z (bounds@%"E")).
  { eapply bounds_E_nonneg with (base:=base) (length:=length) (isRoundDown:=isRoundDown); reflexivity. }

  assert (H_ecap_E_nonneg : 0 <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))).
  { eapply ecap_E_nonneg with (cap:=cap) (addr:=addr); reflexivity. }

  assert (HE : Zmod.to_Z (bounds@%"E") <= (Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))).
  { eapply bounds_E_le_ecap_ECorrected with (cap:=cap) (addr:=addr) (base:=base) (length:=length) (isRoundDown:=isRoundDown).
    - reflexivity.
    - reflexivity.
    - split; assumption.
  }

  assert (H_base_math: Zmod.to_Z (bounds@%"base") = (Zmod.to_Z base / 2^(Zmod.to_Z (bounds@%"E"))) * 2^(Zmod.to_Z (bounds@%"E"))) by (eapply bounds_base_math with (base:=base) (length:=length) (isRoundDown:=isRoundDown); reflexivity).

  assert (H_top_math: Zmod.to_Z (bounds@%"top") <= ((Zmod.to_Z (base + length) + 2^(Zmod.to_Z (bounds@%"E")) - 1) / 2^(Zmod.to_Z (bounds@%"E"))) * 2^(Zmod.to_Z (bounds@%"E"))).
  { eapply bounds_top_math with (base:=base) (length:=length) (isRoundDown:=isRoundDown); auto. }

  assert (H_ecap_base: Zmod.to_Z (ecap@%"base") mod 2^((Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))) = 0) by (eapply ecap_base_multiple with (cap:=cap) (addr:=addr); reflexivity).

  assert (H_ecap_top: Zmod.to_Z (ecap@%"top") mod 2^((Zmod.to_Z (evalExpr (get_ECorrected_from_E (evalExpr (get_E_from_cE (cap@%"cE"))))))) = 0) by (eapply ecap_top_multiple with (cap:=cap) (addr:=addr); reflexivity).

  assert (H_ecap_base_mod_eb: Zmod.to_Z (ecap@%"base") mod 2^(Zmod.to_Z (bounds@%"E")) = 0).
  { eapply multiple_divides; try eassumption; lia. }

  assert (H_ecap_top_mod_eb: Zmod.to_Z (ecap@%"top") mod 2^(Zmod.to_Z (bounds@%"E")) = 0).
  { eapply multiple_divides; try eassumption; lia. }

  split.
  - rewrite H_base_math.
    apply floor_geq; try eassumption; eauto.
  - eapply Z.le_trans.
    + apply H_top_math.
    + apply ceil_leq; try eassumption; eauto.
Qed.
