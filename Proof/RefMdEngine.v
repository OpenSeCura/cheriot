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
From Cheriot Require Import SpecDefines SpecMulDiv ImplStaged ImplMulDiv.
From Cheriot.Proof Require Import ShiftFifoLemmas ImplStagedProof ImplMulDivProof StateRel RefRevTable.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * MILESTONE 5: THE MULDIV ENGINES
 * ===========================================================================
 * What each engine action does to the engine state, and what that does to the engine's flush
 * entries (`extractIterEngineEntries`, `extractPipeStageStates`: the result after the remaining
 * steps).
 * - `fifo1_to_list`: a capacity-1 FIFO as a list.
 * - `iterEnq_char`, `iterStep_char`, `iterFirst_char`, `iterDeq_char`: the iterative engine.
 * - `iterStepN_StageValAt`: remaining steps on top of `StageValAt`. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Capacity-1 FIFOs --- *)

Lemma bits1_cases : forall sz : bits 1, sz = Zmod.of_Z 2 0 \/ sz = Zmod.of_Z 2 1.
Proof.
  intros sz.
  destruct (Zmod.eqb sz (Zmod.of_Z 2 1)) eqn:E.
  - right; apply Zmod.eqb_eq in E; exact E.
  - left; exact (bits1_not_one_is_zero sz E).
Qed.

Lemma fifo1_to_list :
  forall K (f : TS (fifoTree 1 K)),
    fifo_to_list f = if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0) then [] else [fifo1_elem f].
Proof.
  intros K [[e []] [sz []]].
  unfold fifo_to_list, fifo_elems_all, fifo_size, fifo1_size, fifo1_elem; cbn [Fst Snd].
  destruct (elemPathsWithKind_1 K) as [[[rp rpf] rkf] [Hp Hr]]; rewrite Hp.
  cbn in Hr; subst rp.
  destruct (bits1_cases sz) as [-> | ->]; cbn; [reflexivity |].
  unfold readRegOfKind; cbn.
  rewrite eq_rect_Kind_refl; reflexivity.
Qed.

(* --- 2. Remaining Steps --- *)

Lemma iterStepN_StageValAt :
  forall {InpK StateK : Kind} (initFn : forall ty, ty InpK -> LetExpr ty StateK)
         (stepFn : forall ty, ty StateK -> LetExpr ty StateK) n m inp,
    iterStepN stepFn n (StageValAt initFn stepFn m inp) = StageValAt initFn stepFn (m + n) inp.
Proof.
  intros InpK StateK initFn stepFn n; induction n as [| n IH]; intros m inp; cbn [iterStepN].
  - rewrite Nat.add_0_r; reflexivity.
  - change (evalLetExpr (stepFn type (StageValAt initFn stepFn m inp))) with (StageValAt initFn stepFn (S m) inp).
    rewrite IH; f_equal; lia.
Qed.

(* --- 3. The Engine Results Are the Spec's --- *)

(* At the core's width, the engines' operand truncation keeps the operand *)
Lemma addrToBitD_id : forall e : type Addr, evalExpr (@addrToBitD (Z.to_nat Xlen) type e) = e.
Proof.
  intros e; apply Zmod.unsigned_inj.
  unfold addrToBitD; cbn [evalExpr].
  rewrite unsigned_firstn by (cbv; congruence).
  match goal with |- context [Zmod.unsigned (evalExpr (castBits ?pf ?x))] =>
    change (Zmod.unsigned (evalExpr (castBits pf x))) with (Zmod.to_Z (evalExpr (castBits pf x)))
  end.
  rewrite to_Z_castBits; cbn [evalExpr].
  apply Z.mod_small; exact (Zmod.unsigned_pos_bound e ltac:(cbv; congruence)).
Qed.

Ltac readback2 :=
  match goal with |- context [?x] =>
    lazymatch x with evalExpr (ReadUnionData (Var _ _ (evalExpr (BuildUnion ?i ?e))) _) =>
      let Hr := fresh in
      assert (Hr : x = evalExpr e) by exact (evalExpr_ReadUnionData_BuildUnion _ i e eq_refl);
      rewrite Hr; clear Hr
    end
  end.

Lemma mulUnion_rb :
  forall mOp : type MulOp,
    evalExpr ((Var type (TaggedUnion MulDivType) (evalExpr (UNION (MulDivType, "Mul" ::= Const type MulOp mOp)))) `! "Mul") = mOp.
Proof. intros mOp; apply (evalExpr_ReadUnionData_BuildUnion MulDivType); reflexivity. Qed.

Lemma mulUnion_tag :
  forall mOp : type MulOp,
    evalExpr ((Var type (TaggedUnion MulDivType) (evalExpr (UNION (MulDivType, "Mul" ::= Const type MulOp mOp)))) `? "Mul") = true.
Proof. intros mOp; reflexivity. Qed.

Lemma divUnion_tag :
  forall dOp : type DivOp,
    evalExpr ((Var type (TaggedUnion MulDivType) (evalExpr (UNION (MulDivType, "Div" ::= Const type DivOp dOp)))) `? "Mul") = false.
Proof. intros dOp; reflexivity. Qed.

Lemma divUnion_rb :
  forall dOp : type DivOp,
    evalExpr ((Var type (TaggedUnion MulDivType) (evalExpr (UNION (MulDivType, "Div" ::= Const type DivOp dOp)))) `! "Div") = dOp.
Proof. intros dOp; apply (evalExpr_ReadUnionData_BuildUnion MulDivType); reflexivity. Qed.

Lemma PureMulOut_res :
  forall d (inp : type (MulInput d)),
    let o := evalLetExpr (@PureMulOut d type inp) in
    evalExpr (#o`"res") =
    evalLetExpr (@PureMultiply d type (inp @% "isHigh") (inp @% "op1Signed") (inp @% "op2Signed")
                   (inp @% "op1") (inp @% "op2")).
Proof. intros d [ih [s1 [s2 [o1 [o2 []]]]]]; reflexivity. Qed.

Lemma PureMultiply_Multiply :
  forall isHigh s1 s2 (op1 op2 : type Addr),
    evalLetExpr (@PureMultiply Xlen type isHigh s1 s2 op1 op2) = evalLetExpr (Multiply isHigh s1 s2 op1 op2).
Proof. intros; reflexivity. Qed.

Lemma decodeMul_eq :
  forall (x : type (Bit (dataLen (Z.to_nat Xlen)))) (mOp : type MulOp),
    evalLetExpr (@decodeMulInput (Z.to_nat Xlen) type x mOp) =
    (mOp @% "isHigh" ,, (mOp @% "op1Signed" ,, (mOp @% "op2Signed" ,, (x ,,
      (evalExpr (@addrToBitD (Z.to_nat Xlen) type (mOp @% "op2")) ,, tt))))).
Proof. intros x [op2 [ih [s1 [s2 []]]]]; reflexivity. Qed.

Lemma PureDivOut_res :
  forall d (inp : type (DivInput d)),
    let o := evalLetExpr (@PureDivOut d type inp) in
    evalExpr (#o`"res") =
    evalLetExpr (@PureDivide d type (inp @% "isUnsigned") (inp @% "isRem") (inp @% "op1") (inp @% "op2")).
Proof. intros d [iu [ir [o1 [o2 []]]]]; reflexivity. Qed.

Lemma decodeDiv_eq :
  forall (x : type (Bit (dataLen (Z.to_nat Xlen)))) (dOp : type DivOp),
    evalLetExpr (@decodeDivInput (Z.to_nat Xlen) type x dOp) =
    (dOp @% "isUnsigned" ,, (dOp @% "isRem" ,, (x ,,
      (evalExpr (@addrToBitD (Z.to_nat Xlen) type (dOp @% "op2")) ,, tt)))).
Proof. intros x [op2 [iu [ir []]]]; reflexivity. Qed.

Lemma PureSharedOut_res :
  forall d (inp : type (SharedInput d)),
    let o := evalLetExpr (@PureSharedOut d type inp) in
    evalExpr (#o`"res") =
    if inp @% "isMul"
    then evalLetExpr (@PureMultiply d type (inp @% "isHigh") (inp @% "op1Signed") (inp @% "op2Signed")
                        (inp @% "op1") (inp @% "op2"))
    else evalLetExpr (@PureDivide d type (inp @% "isUnsigned") (inp @% "isRem") (inp @% "op1") (inp @% "op2")).
Proof. intros d [im [ih [s1 [s2 [iu [ir [o1 [o2 []]]]]]]]]; destruct im; reflexivity. Qed.

Definition mdTagMul (u : type MulDivUnion) : bool := evalExpr ((Var type MulDivUnion u) `? "Mul").
Definition mdMulData (u : type MulDivUnion) : type MulOp := evalExpr ((Var type MulDivUnion u) `! "Mul").
Definition mdDivData (u : type MulDivUnion) : type DivOp := evalExpr ((Var type MulDivUnion u) `! "Div").

Lemma specMulDiv_cases :
  forall (op1 : type Addr) (u : type MulDivUnion),
    evalLetExpr (SpecMulDiv.MulDiv (ty := type) op1 u) =
    if mdTagMul u
    then evalLetExpr (Multiply ((mdMulData u) @% "isHigh") ((mdMulData u) @% "op1Signed") ((mdMulData u) @% "op2Signed")
                        op1 ((mdMulData u) @% "op2"))
    else evalLetExpr (Divide ((mdDivData u) @% "isUnsigned") ((mdDivData u) @% "isRem") op1 ((mdDivData u) @% "op2")).
Proof.
  intros op1 u; unfold SpecMulDiv.MulDiv; cbn [evalLetExpr].
  match goal with |- context [if ?c then _ else _] => change c with (mdTagMul u) end.
  destruct (mdTagMul u); reflexivity.
Qed.

Lemma decodeShared_eq :
  forall (x : type (Bit (dataLen (Z.to_nat Xlen)))) (u : type MulDivUnion),
    evalLetExpr (@decodeSharedInput (Z.to_nat Xlen) type x u) =
    (mdTagMul u ,, ((mdMulData u) @% "isHigh" ,, ((mdMulData u) @% "op1Signed" ,, ((mdMulData u) @% "op2Signed" ,,
     ((mdDivData u) @% "isUnsigned" ,, ((mdDivData u) @% "isRem" ,, (x ,,
     (evalExpr (@addrToBitD (Z.to_nat Xlen) type
                  (if mdTagMul u then (mdMulData u) @% "op2" else (mdDivData u) @% "op2")) ,, tt)))))))).
Proof. intros x u; reflexivity. Qed.

Section Results.
  Variable mulStages divStages : nat.
  Hypothesis Hmd : Is_true (mulDivStagesDivideXlen mulStages divStages).

  Local Abbreviation W := (Z.to_nat Xlen).

  Lemma stages_divide :
    (mulStages * (W / mulStages) = W)%nat /\ (divStages * (W / divStages) = W)%nat.
  Proof.
    unfold mulDivStagesDivideXlen in Hmd; apply Is_true_eq_true, andb_prop in Hmd as [H1 H2].
    apply Nat.eqb_eq in H1, H2; exact (conj H1 H2).
  Qed.

  Lemma W_pos : (0 < W)%nat.
  Proof. cbv; lia. Qed.

  Lemma mul_engine :
    forall (inp : type (MulInput (dataLen W))),
      let o := evalLetExpr (@mulFinishStage W type
                 (iterStepN (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st') mulStages
                    (evalLetExpr (@mulInitStage W type inp)))) in
      evalExpr (#o`"res") =
      evalLetExpr (@PureMultiply (dataLen W) type (inp @% "isHigh") (inp @% "op1Signed") (inp @% "op2Signed")
                     (inp @% "op1") (inp @% "op2")).
  Proof.
    intros inp o; subst o.
    change (evalLetExpr (@mulInitStage W type inp))
      with (StageValAt (@mulInitStage W) (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st') 0 inp).
    rewrite iterStepN_StageValAt; cbn [Nat.add].
    rewrite (PipelinedMul_StageValAt_PureMulOut W mulStages inp W_pos (proj1 stages_divide)).
    apply PureMulOut_res.
  Qed.

  Lemma mul_spec_gen :
    forall (op1 : type Addr) (mOp : type MulOp) (u : type MulDivUnion),
      evalExpr ((Var type (TaggedUnion MulDivType) u) `? "Mul") = true ->
      evalExpr ((Var type (TaggedUnion MulDivType) u) `! "Mul") = mOp ->
      evalLetExpr (@PureMultiply Xlen type (mOp @% "isHigh") (mOp @% "op1Signed") (mOp @% "op2Signed") op1
                     (mOp @% "op2")) =
      evalLetExpr (SpecMulDiv.MulDiv (ty := type) op1 u).
  Proof.
    intros op1 mOp u Ht Hd; rewrite PureMultiply_Multiply.
    unfold SpecMulDiv.MulDiv; cbn [evalLetExpr].
    rewrite Ht; cbv iota; cbn [evalLetExpr].
    match goal with |- context [@evalExpr ?k (@ReadUnionData type ?ls (Var ?t ?kk u) ?i)] =>
      let Hd' := fresh in
      assert (Hd' : @evalExpr k (@ReadUnionData type ls (Var t kk u) i) = mOp) by exact Hd; rewrite Hd'
    end.
    reflexivity.
  Qed.
  Lemma mul_bridge :
    forall (req : type MulReq),
      let inp := evalLetExpr (@decodeMulInput W type (evalExpr (@addrToBitD W type req.(Snd).(Fst))) req.(Snd).(Snd).(Fst)) in
      (req.(Fst), mkMulDivCap
                    (evalLetExpr (@PureMultiply (dataLen W) type (inp @% "isHigh") (inp @% "op1Signed")
                                    (inp @% "op2Signed") (inp @% "op1") (inp @% "op2")))) = evalMulReqCap req.
  Proof.
    intros [dst [op1 [mOp []]]] inp; subst inp; cbn [Fst Snd].
    rewrite decodeMul_eq.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum].
    rewrite !addrToBitD_id.
    change (dataLen W) with Xlen.
    unfold evalMulReqCap; cbn [Fst Snd]; f_equal; f_equal.
    apply mul_spec_gen; [apply mulUnion_tag | apply mulUnion_rb].
  Qed.

  (* The pipelined multiplier's entry for a request it has just taken is the request's flush entry *)
  Lemma mul_result_pipe :
    forall (req : type MulReq),
      let inp := evalLetExpr (@decodeMulInput W type (evalExpr (@addrToBitD W type req.(Snd).(Fst))) req.(Snd).(Snd).(Fst)) in
      let o := evalLetExpr (@mulFinishStage W type
                 (iterStepN (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st') mulStages
                    (evalLetExpr (@mulInitStage W type inp)))) in
      (req.(Fst), mkMulDivCap (evalExpr (#o`"res"))) = evalMulReqCap req.
  Proof. intros req inp o; subst o; rewrite mul_engine; apply mul_bridge. Qed.

  Lemma iterSteps_mul :
    forall inp, Z.to_nat (Zmod.unsigned (evalLetExpr (@mulStepsConst W mulStages type inp))) = mulStages.
  Proof. intros inp; exact (IterTargetSteps_mulStepsConst W mulStages inp). Qed.

  Lemma iterSteps_div :
    forall inp, Z.to_nat (Zmod.unsigned (evalLetExpr (@divStepsConst W divStages type inp))) = divStages.
  Proof. intros inp; exact (IterTargetSteps_divStepsConst W divStages inp). Qed.

  (* The iterative multiplier's entry for a request it has just taken *)
  Lemma mul_result_iter :
    forall (req : type MulReq),
      let inp := evalLetExpr (@decodeMulInput W type (evalExpr (@addrToBitD W type req.(Snd).(Fst))) req.(Snd).(Snd).(Fst)) in
      let o := evalLetExpr (@mulFinishStage W type
                 (iterStepN (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st')
                    (Z.to_nat (Zmod.unsigned (evalLetExpr (@mulStepsConst W mulStages type inp))))
                    (evalLetExpr (@mulInitStage W type inp)))) in
      (req.(Fst), mkMulDivCap (evalExpr (#o`"res"))) = evalMulReqCap req.
  Proof. intros req inp o; subst o; rewrite iterSteps_mul, mul_engine; apply mul_bridge. Qed.

  Lemma div_engine :
    forall (inp : type (DivInput (dataLen W))),
      let o := evalLetExpr (@divFinishStage W type
                 (iterStepN (fun ty' st' => @divStageStep W ty' (W / divStages)%nat st') divStages
                    (evalLetExpr (@divInitStage W type inp)))) in
      evalExpr (#o`"res") =
      evalLetExpr (@PureDivide (dataLen W) type (inp @% "isUnsigned") (inp @% "isRem") (inp @% "op1") (inp @% "op2")).
  Proof.
    intros inp o; subst o.
    change (evalLetExpr (@divInitStage W type inp))
      with (StageValAt (@divInitStage W) (fun ty' st' => @divStageStep W ty' (W / divStages)%nat st') 0 inp).
    rewrite iterStepN_StageValAt; cbn [Nat.add].
    pose proof (IterDiv_StageValAt_PureDivOut W divStages inp W_pos (proj2 stages_divide)) as E.
    cbv zeta in E; rewrite IterTargetSteps_divStepsConst in E; rewrite E.
    apply PureDivOut_res.
  Qed.

  Lemma div_spec_gen :
    forall (op1 : type Addr) (dOp : type DivOp) (u : type MulDivUnion),
      evalExpr ((Var type (TaggedUnion MulDivType) u) `? "Mul") = false ->
      evalExpr ((Var type (TaggedUnion MulDivType) u) `! "Div") = dOp ->
      evalLetExpr (@PureDivide Xlen type (dOp @% "isUnsigned") (dOp @% "isRem") op1 (dOp @% "op2")) =
      evalLetExpr (SpecMulDiv.MulDiv (ty := type) op1 u).
  Proof.
    intros op1 dOp u Ht Hd; rewrite PureDivide_eq_SpecDivide.
    unfold SpecMulDiv.MulDiv; cbn [evalLetExpr].
    rewrite Ht; cbv iota; cbn [evalLetExpr].
    match goal with |- context [@evalExpr ?k (@ReadUnionData type ?ls (Var ?t ?kk u) ?i)] =>
      let Hd' := fresh in
      assert (Hd' : @evalExpr k (@ReadUnionData type ls (Var t kk u) i) = dOp) by exact Hd; rewrite Hd'
    end.
    reflexivity.
  Qed.

  Lemma div_bridge :
    forall (req : type DivReq),
      let inp := evalLetExpr (@decodeDivInput W type (evalExpr (@addrToBitD W type req.(Snd).(Fst))) req.(Snd).(Snd).(Fst)) in
      (req.(Fst), mkMulDivCap
                    (evalLetExpr (@PureDivide (dataLen W) type (inp @% "isUnsigned") (inp @% "isRem")
                                    (inp @% "op1") (inp @% "op2")))) = evalDivReqCap req.
  Proof.
    intros [dst [op1 [dOp []]]] inp; subst inp; cbn [Fst Snd].
    rewrite decodeDiv_eq.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum].
    rewrite !addrToBitD_id.
    change (dataLen W) with Xlen.
    unfold evalDivReqCap; cbn [Fst Snd]; f_equal; f_equal.
    apply div_spec_gen; [apply divUnion_tag | apply divUnion_rb].
  Qed.

  (* The iterative divider's entry for a request it has just taken *)
  Lemma div_result_iter :
    forall (req : type DivReq),
      let inp := evalLetExpr (@decodeDivInput W type (evalExpr (@addrToBitD W type req.(Snd).(Fst))) req.(Snd).(Snd).(Fst)) in
      let o := evalLetExpr (@divFinishStage W type
                 (iterStepN (fun ty' st' => @divStageStep W ty' (W / divStages)%nat st')
                    (Z.to_nat (Zmod.unsigned (evalLetExpr (@divStepsConst W divStages type inp))))
                    (evalLetExpr (@divInitStage W type inp)))) in
      (req.(Fst), mkMulDivCap (evalExpr (#o`"res"))) = evalDivReqCap req.
  Proof. intros req inp o; subst o; rewrite iterSteps_div, div_engine; apply div_bridge. Qed.

  (* The shared engine's entry for a request it has just taken *)
  Lemma shared_result :
    forall (req : type MulDivReq),
      let inp := evalLetExpr (@decodeSharedInput W type (evalExpr (@addrToBitD W type req.(Snd).(Fst))) req.(Snd).(Snd).(Fst)) in
      let o := evalLetExpr (@sharedFinishStage W type
                 (iterStepN (fun ty' st' => @sharedStageStep W ty' (W / mulStages)%nat (W / divStages)%nat st')
                    (Z.to_nat (Zmod.unsigned (evalLetExpr (@sharedStepsFn W mulStages divStages type inp))))
                    (evalLetExpr (@sharedInitStage W type inp)))) in
      (req.(Fst), mkMulDivCap (evalExpr (#o`"res"))) = evalMulDivReqCap req.
  Proof.
    intros req inp o; subst o.
    change (evalLetExpr (@sharedInitStage W type inp))
      with (StageValAt (@sharedInitStage W)
              (fun ty' st' => @sharedStageStep W ty' (W / mulStages)%nat (W / divStages)%nat st') 0 inp).
    rewrite iterStepN_StageValAt; cbn [Nat.add].
    pose proof (SharedIterMulDiv_StageValAt_PureSharedOut W mulStages divStages inp W_pos
                  (proj1 stages_divide) (proj2 stages_divide)) as E.
    cbv zeta in E; unfold IterTargetSteps in E; rewrite E, PureSharedOut_res.
    subst inp; destruct req as [dst [op1 [mdOp []]]]; cbn [Fst Snd].
    rewrite decodeShared_eq.
    cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum].
    rewrite !addrToBitD_id.
    unfold evalMulDivReqCap; cbn [Fst Snd]; f_equal; f_equal.
    rewrite specMulDiv_cases; destruct (mdTagMul mdOp); change (dataLen W) with Xlen.
    - apply PureMultiply_Multiply.
    - apply PureDivide_eq_SpecDivide.
  Qed.

End Results.

(* --- 4. The Iterative Engine's Actions --- *)

Section IterChar.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Local Abbreviation stepsSz := (iterStepsSz num_stages).
  Variable numStepsFn : forall ty, ty InpK -> LetExpr ty (Bit stepsSz).
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.

  Local Abbreviation IT := (stagedIterTree StateK num_stages).

  Definition mkWork (busy : bool) (rem : bits stepsSz) (st : type StateK) : TS IT :=
    (busy ,, (rem ,, (st ,, tt))).

  Lemma iterEnq_char :
    forall env inp (s s' : TS IT) r,
      SemAction env (stagedIterEnq InpK StateK num_stages numStepsFn initFn type inp) s s' r ->
      s' = if s.(Fst) then s else mkWork true (evalLetExpr (numStepsFn type inp)) (evalLetExpr (initFn type inp)).
  Proof.
    intros env inp [busy [rem [st []]]] s' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedIterEnq, stagedWorkRegPath, stagedIterTree in H.
    revert H; cbn -[toAction stepsSz]; destruct busy; cbn -[toAction stepsSz].
    - intros [<- _]; reflexivity.
    - rewrite evalActionPropGen_toAction; cbn -[toAction stepsSz].
      rewrite evalActionPropGen_toAction; cbn -[stepsSz]; intros [<- _]; reflexivity.
  Qed.

  Lemma iterStep_char :
    forall env (s s' : TS IT) r,
      SemAction env (stagedIterStep StateK num_stages stepFn type) s s' r ->
      s' = if andb s.(Fst) (negb (Zmod.eqb s.(Snd).(Fst) Zmod.zero))
           then mkWork true (evalExpr (Sub (Var type (Bit stepsSz) s.(Snd).(Fst)) $1))
                  (evalLetExpr (stepFn type s.(Snd).(Snd).(Fst)))
           else s.
  Proof.
    intros env [busy [rem [st []]]] s' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedIterStep, stagedWorkRegPath, stagedIterTree in H.
    revert H; cbn -[toAction Sub stepsSz].
    change (Zmod.of_Z (2 ^ stepsSz) 0) with (@Zmod.zero (2 ^ stepsSz)).
    destruct (andb busy (negb (Zmod.eqb rem Zmod.zero))); cbn -[toAction Sub stepsSz].
    - rewrite evalActionPropGen_toAction; cbn -[Sub stepsSz]; intros [<- _]; reflexivity.
    - intros [<- _]; reflexivity.
  Qed.
  Lemma iterFirst_char :
    forall env (s s' : TS IT) (r : type (Option OutK)),
      SemAction env (stagedIterFirst StateK OutK num_stages finishFn type) s s' r ->
      s' = s /\ r.(Snd).(Fst) = andb s.(Fst) (Zmod.eqb s.(Snd).(Fst) Zmod.zero) /\
      (r.(Snd).(Fst) = true -> r.(Fst) = evalLetExpr (finishFn type s.(Snd).(Snd).(Fst))).
  Proof.
    intros env [busy [rem [st []]]] s' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedIterFirst, stagedWorkRegPath, stagedIterTree in H.
    revert H; cbn -[toAction mkSome mkNone stepsSz].
    rewrite evalActionPropGen_toAction; cbn -[mkSome mkNone stepsSz].
    change (Zmod.of_Z (2 ^ stepsSz) 0) with (@Zmod.zero (2 ^ stepsSz)).
    intros [<- <-]; split; [reflexivity |].
    destruct (andb busy (Zmod.eqb rem Zmod.zero)); split; try reflexivity; intros E; discriminate E.
  Qed.

  Lemma iterDeq_char :
    forall env (s s' : TS IT) r,
      SemAction env (stagedIterDeq StateK num_stages type) s s' r ->
      s' = if andb s.(Fst) (Zmod.eqb s.(Snd).(Fst) Zmod.zero) then mkWork false s.(Snd).(Fst) s.(Snd).(Snd).(Fst) else s.
  Proof.
    intros env [busy [rem [st []]]] s' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedIterDeq, stagedWorkRegPath, stagedIterTree in H.
    revert H; cbn -[stepsSz].
    change (Zmod.of_Z (2 ^ stepsSz) 0) with (@Zmod.zero (2 ^ stepsSz)).
    destruct (andb busy (Zmod.eqb rem Zmod.zero)); cbn -[stepsSz]; intros [<- _]; reflexivity.
  Qed.

  (* A step keeps the result after the remaining steps *)
  Lemma iterStepN_rem_step :
    forall (rem : bits stepsSz) (st : type StateK),
      Zmod.eqb rem Zmod.zero = false ->
      iterStepN stepFn (Z.to_nat (Zmod.unsigned (evalExpr (Sub (Var type (Bit stepsSz) rem) $1))))
        (evalLetExpr (stepFn type st)) =
      iterStepN stepFn (Z.to_nat (Zmod.unsigned rem)) st.
  Proof.
    intros rem st Hnz.
    assert (Hsz : 0 < stepsSz) by apply iterStepsSz_pos.
    assert (H2 : 2 <= 2 ^ stepsSz)
      by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
    assert (Hu1 : Zmod.unsigned (evalExpr ($1 : Expr type (Bit stepsSz))) = 1).
    { cbn [evalExpr]; rewrite Zmod.unsigned_of_Z, Z.mod_small by lia; reflexivity. }
    assert (Hpos : 1 <= Zmod.unsigned rem).
    { pose proof (bits.unsigned_range rem ltac:(lia)) as Hr.
      destruct (Z.eq_dec (Zmod.unsigned rem) 0) as [E | E]; [| lia].
      exfalso; assert (rem = Zmod.zero) by (apply Zmod.unsigned_inj; rewrite E, Zmod.unsigned_0; reflexivity).
      subst rem; rewrite Zmod.eqb_refl in Hnz; discriminate Hnz. }
    rewrite evalExpr_Sub_Bit; [| exact Hsz | rewrite Hu1; cbn [evalExpr]; lia].
    rewrite Hu1; cbn [evalExpr].
    replace (Z.to_nat (Zmod.unsigned rem)) with (S (Z.to_nat (Zmod.unsigned rem - 1))) by lia.
    reflexivity.
  Qed.
End IterChar.

(* --- 5. The Pipelined Engine's Actions --- *)

Section PipeChar.
  Variable StateK OutK : Kind.
  Variable stepFn   : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn : forall ty, ty StateK -> LetExpr ty OutK.

  Local Abbreviation ST n := (stagedStagesTree StateK n).

  (* The result of each state after its remaining steps, oldest first *)
  Definition pipeRes (n : nat) (s : TS (ST n)) : list (type StateK) :=
    map (fun ks => iterStepN stepFn (fst ks) (snd ks)) (extractPipeStageStates n s).

  Definition pipeBelow (n : nat) : TS (ST n) -> list (nat * type StateK) :=
    match n return TS (ST n) -> list (nat * type StateK) with
    | 0%nat => fun _ => []
    | S m => fun s => extractPipeStageStates m s.(Snd).(Fst)
    end.

  Lemma states_top :
    forall n (s : TS (ST n)),
      extractPipeStageStates n s = (pipeBelow n s ++ map (pair n) (@fifo_to_list 1 StateK s.(Fst)))%list.
  Proof. intros [| n] s; reflexivity. Qed.

  Lemma fifo1_list_full :
    forall (f : TS (fifoTree 1 StateK)), fifo1_size f = Zmod.of_Z 2 1 -> fifo_to_list f = [fifo1_elem f].
  Proof. intros f H; rewrite fifo1_to_list, H; reflexivity. Qed.

  Lemma fifo1_list_empty :
    forall (f : TS (fifoTree 1 StateK)), fifo1_size f = Zmod.of_Z 2 0 -> fifo_to_list f = [].
  Proof. intros f H; rewrite fifo1_to_list, H; reflexivity. Qed.

  (* One stage step: the head state moves to the next stage, one step further *)
  Lemma pipeAdj_char :
    forall m env (s s' : TS (ST (S m))) r,
      SemAction env (stagedPipeStepAdjacent StateK stepFn type m) s s' r ->
      s' = s \/
      (exists x, @fifo_to_list 1 StateK s.(Fst) = [x] /\ @fifo_to_list 1 StateK s.(Snd).(Fst).(Fst) = [] /\
                 @fifo_to_list 1 StateK s'.(Fst) = [] /\
                 @fifo_to_list 1 StateK s'.(Snd).(Fst).(Fst) = [evalLetExpr (stepFn type x)] /\
                 s'.(Snd).(Fst).(Snd) = s.(Snd).(Fst).(Snd)).
  Proof.
    intros m env [f_cur [[f_next st_tail] []]] s' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedPipeStepAdjacent, stagedStagesTree in H.
    revert H; cbn [stagedStagesTail evalActionPropGen].
    rewrite evalActionPropGen_liftAction_child0Path, (evalActionPropGen_fifo_first f_cur).
    destruct (bits1_cases (fifo1_size f_cur)) as [Ec | Ec]; rewrite Ec.
    - change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 0)) with true; cbn [evalActionPropGen].
      rewrite evalActionPropGen_liftAction_child1Path, evalActionPropGen_liftAction_child0Path,
              (evalActionPropGen_fifo_isFull f_next).
      cbn [evalActionPropGen]; rewrite evalExpr_And2_Not.
      match goal with |- (if ?c then _ else _) -> _ =>
        let Hc := fresh in assert (Hc : c = false) by reflexivity; rewrite Hc
      end; cbv iota.
      cbn [evalActionPropGen]; intros [<- _]; left; reflexivity.
    - change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [evalActionPropGen].
      rewrite evalActionPropGen_liftAction_child1Path, evalActionPropGen_liftAction_child0Path,
              (evalActionPropGen_fifo_isFull f_next).
      destruct (bits1_cases (fifo1_size f_next)) as [En | En]; rewrite En.
      + change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false.
        cbn [evalActionPropGen].
        rewrite evalExpr_And2_Not.
        match goal with |- (if ?c then _ else _) -> _ =>
          let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc
        end; cbv iota.
        rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
        rewrite evalActionPropGen_liftAction_child1Path,
                evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_enq, En.
        change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false.
        cbn [negb evalActionPropGen].
        rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_deq, Ec.
        change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false.
        cbn [negb evalActionPropGen]; intros [<- _]; right.
        exists (fifo1_elem f_cur); cbn [Fst Snd].
        rewrite (fifo1_list_full f_cur Ec), (fifo1_list_empty f_next En).
        split; [reflexivity | split; [reflexivity |]].
        rewrite !fifo1_to_list, ?Ec, ?En.
        unfold mkFifo1, fifo1_size, fifo1_elem; cbn [Fst Snd].
        split; [reflexivity | split; reflexivity].
      + change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 1)) with true.
        cbn [evalActionPropGen].
        rewrite evalExpr_And2_Not.
        match goal with |- (if ?c then _ else _) -> _ =>
          let Hc := fresh in assert (Hc : c = false) by reflexivity; rewrite Hc
        end; cbv iota.
        cbn [evalActionPropGen]; intros [<- _]; left; reflexivity.
  Qed.
  Lemma pipeBelow_snd :
    forall m (a b : TS (ST m)), a.(Snd) = b.(Snd) -> pipeBelow m a = pipeBelow m b.
  Proof. intros [| m] a b E; cbn [pipeBelow]; [reflexivity | rewrite E; reflexivity]. Qed.

  (* The stage rules keep each state's result after its remaining steps *)
  Lemma pipeChain_res :
    forall n r, In r (stagedPipeStageRulesChain StateK stepFn type n) ->
    forall env (s s' : TS (ST n)) v, SemAction env r s s' v -> pipeRes n s' = pipeRes n s.
  Proof.
    induction n as [| m IH]; intros r Hin env s s' v H; cbn [stagedPipeStageRulesChain] in Hin; [destruct Hin |].
    destruct Hin as [<- | Hin].
    - destruct (pipeAdj_char m env s s' v H) as [-> | [x [E1 [E2 [E3 [E4 E5]]]]]]; [reflexivity |].
      unfold pipeRes; cbn [extractPipeStageStates].
      rewrite (states_top m s'.(Snd).(Fst)), (states_top m s.(Snd).(Fst)), E1, E2, E3, E4.
      rewrite (pipeBelow_snd m _ _ E5).
      cbn [map]; rewrite !app_nil_r, !map_app; reflexivity.
    - apply in_map_iff in Hin as [r' [<- Hr']].
      destruct s as [f [sub []]].
      rewrite SemAction_iff_evalActionPropGen in H.
      unfold stagedStagesTree in H; cbn [stagedStagesTail] in H.
      rewrite evalActionPropGen_liftAction_child1Path in H.
      destruct (evalActionPropGen_to_SemAction r' _ _ H) as [sub' [v' [Hs [<- _]]]].
      pose proof (IH r' Hr' _ sub sub' v' Hs) as E.
      unfold pipeRes in *; cbn [extractPipeStageStates Fst Snd]; rewrite !map_app, E; reflexivity.
  Qed.

  (* The states above the last stage *)
  Fixpoint pipeUpper (n : nat) : TS (ST n) -> list (nat * type StateK) :=
    match n return TS (ST n) -> list (nat * type StateK) with
    | 0%nat => fun _ => []
    | S m => fun s => (pipeUpper m s.(Snd).(Fst) ++ map (pair (S m)) (@fifo_to_list 1 StateK s.(Fst)))%list
    end.

  Lemma states_last :
    forall n (s : TS (ST n)),
      extractPipeStageStates n s =
      (map (pair 0%nat) (@fifo_to_list 1 StateK (stagedLastFifo StateK n s)) ++ pipeUpper n s)%list.
  Proof.
    induction n as [| m IH]; intros s; cbn [extractPipeStageStates stagedLastFifo pipeUpper].
    - rewrite app_nil_r; reflexivity.
    - rewrite IH, app_assoc; reflexivity.
  Qed.

  Lemma upper_update :
    forall n (s : TS (ST n)) f, pipeUpper n (stagedUpdateLastFifo StateK n s f) = pipeUpper n s.
  Proof.
    induction n as [| m IH]; intros s f; cbn [pipeUpper stagedUpdateLastFifo Fst Snd]; [reflexivity |].
    rewrite IH; reflexivity.
  Qed.

  Lemma last_update :
    forall n (s : TS (ST n)) f, stagedLastFifo StateK n (stagedUpdateLastFifo StateK n s f) = f.
  Proof. induction n as [| m IH]; intros s f; cbn [stagedLastFifo stagedUpdateLastFifo Fst Snd]; [reflexivity | apply IH]. Qed.

  Lemma update_last_same :
    forall n (s : TS (ST n)), stagedUpdateLastFifo StateK n s (stagedLastFifo StateK n s) = s.
  Proof.
    induction n as [| m IH]; intros s.
    - destruct s as [f []]; reflexivity.
    - destruct s as [f [sub []]]; cbn [stagedLastFifo stagedUpdateLastFifo Fst Snd]; rewrite IH; reflexivity.
  Qed.

  Lemma pipeFirst_char :
    forall n env (s s' : TS (ST n)) (r : type (Option OutK)),
      SemAction env (stagedPipeFirst StateK OutK n finishFn type) s s' r ->
      s' = s /\
      (r.(Snd).(Fst) = true -> exists x, @fifo_to_list 1 StateK (stagedLastFifo StateK n s) = [x] /\
                                         r.(Fst) = evalLetExpr (finishFn type x)).
  Proof.
    intros n env s s' r H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedPipeFirst in H; cbn [evalActionPropGen] in H.
    rewrite evalActionPropGen_stagedLiftLastStage, evalActionPropGen_fifo_first, update_last_same in H.
    rewrite fifo1_to_list.
    destruct (bits1_cases (fifo1_size (stagedLastFifo StateK n s))) as [Ec | Ec]; rewrite Ec in H |- *.
    - change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 0)) with true in H |- *.
      revert H; cbv iota; cbn -[toAction mkSome mkNone].
      rewrite evalActionPropGen_toAction; cbn -[mkSome mkNone].
      intros [<- <-]; split; [reflexivity |]; intros E; discriminate E.
    - change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false in H |- *.
      revert H; cbv iota; cbn -[toAction mkSome mkNone].
      rewrite evalActionPropGen_toAction; cbn -[mkSome mkNone].
      intros [<- <-]; split; [reflexivity |]; intros _.
      exists (fifo1_elem (stagedLastFifo StateK n s)); split; reflexivity.
  Qed.

  Lemma pipeDeq_char :
    forall n env (s s' : TS (ST n)) r x,
      @fifo_to_list 1 StateK (stagedLastFifo StateK n s) = [x] ->
      SemAction env (stagedPipeDeq StateK n type) s s' r ->
      extractPipeStageStates n s' = pipeUpper n s.
  Proof.
    intros n env s s' r x Hx H.
    rewrite SemAction_iff_evalActionPropGen in H; unfold stagedPipeDeq in H.
    rewrite evalActionPropGen_stagedLiftLastStage, evalActionPropGen_fifo_deq in H.
    destruct H as [<- _].
    rewrite states_last, upper_update, last_update.
    rewrite fifo1_to_list in Hx |- *.
    destruct (bits1_cases (fifo1_size (stagedLastFifo StateK n s))) as [Ec | Ec]; rewrite Ec in Hx |- *.
    - change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 0)) with true in Hx; discriminate Hx.
    - change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbv iota beta; cbn [negb].
      unfold mkFifo1, fifo1_size; cbn [Fst Snd].
      match goal with |- context [if ?c then _ else _] =>
        let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc
      end; reflexivity.
  Qed.

  Lemma pipeEnq_char :
    forall InpK (initFn : forall ty, ty InpK -> LetExpr ty StateK) n env inp (s s' : TS (ST n)) r,
      @fifo_to_list 1 StateK s.(Fst) = [] ->
      SemAction env (stagedPipeEnq InpK StateK n initFn type inp) s s' r ->
      @fifo_to_list 1 StateK s'.(Fst) = [evalLetExpr (initFn type inp)] /\ s'.(Snd) = s.(Snd).
  Proof.
    intros InpK initFn n env inp [f rest] s' r Hx H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold stagedPipeEnq, stagedPipeTree, stagedStagesTree in H; revert H; cbn [evalActionPropGen Fst] in Hx |- *.
    rewrite evalActionPropGen_toAction, evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_enq.
    rewrite fifo1_to_list in Hx.
    destruct (bits1_cases (fifo1_size f)) as [Ec | Ec]; rewrite Ec in Hx |- *.
    - change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false; cbn [negb].
      intros [<- _]; cbn [Fst Snd]; split; [| reflexivity].
      rewrite fifo1_to_list; unfold mkFifo1, fifo1_size, fifo1_elem; cbn [Fst Snd].
      match goal with |- context [if ?c then _ else _] =>
        let Hc := fresh in assert (Hc : c = false) by reflexivity; rewrite Hc
      end; reflexivity.
    - change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false in Hx; discriminate Hx.
  Qed.
End PipeChar.
