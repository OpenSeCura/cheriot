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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec.
From Cheriot Require Import ImplCommon ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof Impl.
From Cheriot.Proof Require Import TreeLemmas StateRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. `regRead` / `executeNonDeferred` COMMUTATION LEMMAS
 * =========================================================================== *)

Section RfActionCommutes.
  Variable pcAddrInit : Z.

  Local Abbreviation rTree := (rfTree pcAddrInit).
  Context {env : Env rTree}.
  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind.

  Lemma ActionCommutes_readCsr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit CsrIdxSz)),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (readRegsList (csrPathsWithKind pcAddrInit) idxExpr).
  Proof.
    intros wIdx wbVal idxExpr env0 s P.
    rewrite !evalActionPropGen_readRegsList.
    change (evalReadRegsList (csrPathsWithKind pcAddrInit) (evalExpr idxExpr) (updGpr pcAddrInit wIdx wbVal s))
      with (readCsr pcAddrInit (evalExpr idxExpr) (updGpr pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (csrPathsWithKind pcAddrInit) (evalExpr idxExpr) s)
      with (readCsr pcAddrInit (evalExpr idxExpr) s).
    rewrite readCsr_updGpr.
    reflexivity.
  Qed.

  Lemma ActionCommutes_writeCsr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit CsrIdxSz)) (valExpr : Expr type (Bit Xlen)),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (writeRegsList (csrPathsWithKind pcAddrInit) idxExpr valExpr).
  Proof.
    intros wIdx wbVal idxExpr valExpr env0 s P.
    rewrite !evalActionPropGen_writeRegsList.
    change (evalWriteRegsList (csrPathsWithKind pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) (updGpr pcAddrInit wIdx wbVal s))
      with (updCsr pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) (updGpr pcAddrInit wIdx wbVal s)).
    change (evalWriteRegsList (csrPathsWithKind pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) s)
      with (updCsr pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) s).
    rewrite updGpr_updCsr_comm.
    reflexivity.
  Qed.

  Lemma ActionCommutes_readScr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit ScrIdxSz)),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (readRegsList (scrPathsWithKind pcAddrInit) idxExpr).
  Proof.
    intros wIdx wbVal idxExpr env0 s P.
    rewrite !evalActionPropGen_readRegsList.
    change (evalReadRegsList (scrPathsWithKind pcAddrInit) (evalExpr idxExpr) (updGpr pcAddrInit wIdx wbVal s))
      with (readScr pcAddrInit (evalExpr idxExpr) (updGpr pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (scrPathsWithKind pcAddrInit) (evalExpr idxExpr) s)
      with (readScr pcAddrInit (evalExpr idxExpr) s).
    rewrite readScr_updGpr.
    reflexivity.
  Qed.

  Lemma ActionCommutes_writeScr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit ScrIdxSz)) (valExpr : Expr type FullECapWithTag),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (writeRegsList (scrPathsWithKind pcAddrInit) idxExpr valExpr).
  Proof.
    intros wIdx wbVal idxExpr valExpr env0 s P.
    rewrite !evalActionPropGen_writeRegsList.
    change (evalWriteRegsList (scrPathsWithKind pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) (updGpr pcAddrInit wIdx wbVal s))
      with (updScr pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) (updGpr pcAddrInit wIdx wbVal s)).
    change (evalWriteRegsList (scrPathsWithKind pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) s)
      with (updScr pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) s).
    rewrite updGpr_updScr_comm.
    reflexivity.
  Qed.

  Lemma ActionCommutes_writeGpr_updGpr_other :
    forall wIdx wbVal (idxExpr : Expr type (Bit RegIdxSzReal)) (valExpr : Expr type FullECapWithTag),
      wIdx <> evalExpr idxExpr ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (writeRegsList (gprPathsWithKind pcAddrInit) idxExpr valExpr).
  Proof.
    intros wIdx wbVal idxExpr valExpr Hneq env0 s P.
    rewrite !evalActionPropGen_writeRegsList.
    change (evalWriteRegsList (gprPathsWithKind pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) (updGpr pcAddrInit wIdx wbVal s))
      with (updGpr pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) (updGpr pcAddrInit wIdx wbVal s)).
    change (evalWriteRegsList (gprPathsWithKind pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) s)
      with (updGpr pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) s).
    rewrite (updGpr_comm pcAddrInit wIdx (evalExpr idxExpr) wbVal (evalExpr valExpr) s Hneq).
    reflexivity.
  Qed.

  Lemma isNotZero_true_iff :
    forall {sz : Z} (x : bits sz),
      evalExpr (isNotZero (Var type (Bit sz) x)) = true <->
      Zmod.eqb x Zmod.zero = false.
  Proof.
    intros sz x.
    cbn [isNotZero evalExpr].
    rewrite negb_true_iff; reflexivity.
  Qed.

  Lemma ActionCommutes_writeGpr_if_isNotZero :
    forall wIdx wbVal (nm : string)
           (dstIdx : bits RegIdxSzReal) (valExpr : Expr type FullECapWithTag)
           {k : Kind} (cont : bits 0 -> Action type rTree k),
      (Zmod.eqb dstIdx Zmod.zero = false -> wIdx <> dstIdx) ->
      (forall v, ActionCommutes (updGpr pcAddrInit wIdx wbVal) (cont v)) ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (IfElse nm (isNotZero (Var type (Bit RegIdxSzReal) dstIdx))
                (writeRegsList (gprPathsWithKind pcAddrInit)
                               (Var type (Bit RegIdxSzReal) dstIdx) valExpr)
                Retv
                cont).
  Proof.
    intros wIdx wbVal nm dstIdx valExpr k cont Hdst Hcont.
    apply ActionCommutes_IfElse_dep.
    - intros Hnz.
      apply isNotZero_true_iff in Hnz.
      apply ActionCommutes_writeGpr_updGpr_other.
      exact (Hdst Hnz).
    - intros ?.
      apply ActionCommutes_Return.
    - exact Hcont.
  Qed.

  Lemma ActionCommutes_incrementMinstret_updGpr :
    forall wIdx wbVal,
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@incrementMinstret pcAddrInit type).
  Proof.
    intros wIdx wbVal.
    unfold incrementMinstret.
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    apply ActionCommutes_LetExp; intros ?.
    apply ActionCommutes_Seq; [apply ActionCommutes_writeCsr_updGpr | apply ActionCommutes_writeCsr_updGpr].
  Qed.

  Lemma ActionCommutes_updateMshwmOnStore_updGpr :
    forall wIdx wbVal (stAddr : type Addr),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@updateMshwmOnStore pcAddrInit type stAddr).
  Proof.
    intros wIdx wbVal stAddr.
    unfold updateMshwmOnStore.
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    apply ActionCommutes_LetExp; intros ?.
    apply ActionCommutes_IfElse.
    - apply ActionCommutes_LetExp; intros ?.
      apply ActionCommutes_Seq; [apply ActionCommutes_writeCsr_updGpr | apply ActionCommutes_Return].
    - apply ActionCommutes_Return.
    - intros ?; apply ActionCommutes_Return.
  Qed.

  Ltac step_LetExp :=
    lazymatch goal with
    | |- ActionCommutes _ (LetExp _ _ _) => apply ActionCommutes_LetExp; intros ?
    end.

  Lemma ActionCommutes_isInterruptPending_updGpr :
    forall wIdx wbVal (meip mtip : bool),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@isInterruptPending pcAddrInit type meip mtip).
  Proof.
    intros wIdx wbVal meip mtip.
    unfold isInterruptPending.
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    repeat step_LetExp.
    apply ActionCommutes_Return.
  Qed.

  Lemma ActionCommutes_handleTrap_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (newMcause newMtval : type (Bit Xlen)),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@handleTrap pcAddrInit type currPcc newMcause newMtval).
  Proof.
    intros wIdx wbVal currPcc newMcause newMtval.
    unfold handleTrap.
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    apply ActionCommutes_LetExp; intros ?.
    apply ActionCommutes_LetExp; intros ?.
    apply ActionCommutes_LetAction; [apply ActionCommutes_readScr_updGpr | intros ?].
    apply ActionCommutes_Seq; [apply ActionCommutes_writeScr_updGpr |].
    apply ActionCommutes_Seq; [apply ActionCommutes_writeCsr_updGpr |].
    apply ActionCommutes_Seq; [apply ActionCommutes_writeCsr_updGpr |].
    apply ActionCommutes_Seq; [apply ActionCommutes_writeCsr_updGpr |].
    apply ActionCommutes_Return.
  Qed.

  Lemma ActionCommutes_executeInterrupt_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool),
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@executeInterrupt pcAddrInit type currPcc meip mtip).
  Proof.
    intros wIdx wbVal currPcc meip mtip.
    unfold executeInterrupt.
    apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
    repeat step_LetExp.
    apply ActionCommutes_handleTrap_updGpr.
  Qed.

  Lemma ActionCommutes_executeSequential_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (aluOut : type AluOutUnion),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@executeSequential pcAddrInit type currPcc aluOut).
  Proof.
    intros wIdx wbVal currPcc aluOut Hdst.
    unfold executeSequential.
    apply ActionCommutes_LetExp_eval.
    repeat step_LetExp.
    apply ActionCommutes_Seq; [apply ActionCommutes_incrementMinstret_updGpr |].
    apply ActionCommutes_Seq; [apply ActionCommutes_writeScr_updGpr |].
    apply ActionCommutes_IfElse.
    - apply ActionCommutes_writeGpr_if_isNotZero.
      + exact Hdst.
      + intros ?; apply ActionCommutes_Return.
    - apply ActionCommutes_LetExp; intros ?.
      apply ActionCommutes_Return.
    - intros ?; apply ActionCommutes_Return.
  Qed.

  Lemma ActionCommutes_executeNonSequential_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut).
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut Hdst.
    unfold executeNonSequential.
    do 2 apply ActionCommutes_LetExp_eval.
    repeat step_LetExp.
    apply ActionCommutes_IfElse.
    - (* Exception *)
      repeat step_LetExp.
      apply ActionCommutes_handleTrap_updGpr.
    - (* NoException *)
      apply ActionCommutes_Seq; [apply ActionCommutes_incrementMinstret_updGpr |].
      apply ActionCommutes_Seq; [apply ActionCommutes_writeScr_updGpr |].
      apply ActionCommutes_LetExp; intros ?.
      apply ActionCommutes_IfElse.
      + (* DataMem *)
        apply ActionCommutes_LetExp; intros ?.
        apply ActionCommutes_IfElse.
        * repeat step_LetExp.
          apply ActionCommutes_IfElse.
          -- apply ActionCommutes_updateMshwmOnStore_updGpr.
          -- apply ActionCommutes_Return.
          -- intros ?; apply ActionCommutes_LetExp; intros ?; apply ActionCommutes_Return.
        * repeat step_LetExp; apply ActionCommutes_Return.
        * intros ?; apply ActionCommutes_Return.
      + (* CfScrCsr *)
        apply ActionCommutes_LetExp; intros ?.
        apply ActionCommutes_IfElse.
        * (* ScrCsr *)
          repeat step_LetExp.
          apply ActionCommutes_IfElse.
          -- (* Scr *)
             apply ActionCommutes_LetExp; intros ?.
             apply ActionCommutes_LetAction; [apply ActionCommutes_readScr_updGpr | intros ?].
             apply ActionCommutes_writeGpr_if_isNotZero; [exact Hdst | intros ?].
             apply ActionCommutes_IfElse;
               [apply ActionCommutes_writeScr_updGpr | apply ActionCommutes_Return | intros ?; apply ActionCommutes_Return].
          -- (* Csr *)
             apply ActionCommutes_LetExp; intros ?.
             apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
             repeat step_LetExp.
             apply ActionCommutes_writeGpr_if_isNotZero; [exact Hdst | intros ?].
             apply ActionCommutes_IfElse.
             ++ repeat step_LetExp.
                apply ActionCommutes_writeCsr_updGpr.
             ++ apply ActionCommutes_Return.
             ++ intros ?; apply ActionCommutes_Return.
          -- intros ?; apply ActionCommutes_Return.
        * (* ControlFlow *)
          repeat step_LetExp.
          apply ActionCommutes_LetAction; [apply ActionCommutes_readCsr_updGpr | intros ?].
          apply ActionCommutes_IfElse_dep.
          -- intros Hnz.
             apply isNotZero_true_iff in Hnz.
             repeat step_LetExp.
             apply ActionCommutes_writeGpr_updGpr_other.
             exact (Hdst Hnz).
          -- intros ?; apply ActionCommutes_Return.
          -- intros ?.
             apply ActionCommutes_IfElse.
             ++ (* ControlFlowAddrOnly *)
                apply ActionCommutes_LetExp; intros ?.
                apply ActionCommutes_IfElse;
                  [repeat step_LetExp; apply ActionCommutes_Return
                  | repeat step_LetExp; apply ActionCommutes_Return
                  | intros ?; apply ActionCommutes_Return].
             ++ (* ControlFlowAddrECap *)
                repeat step_LetExp.
                apply ActionCommutes_IfElse.
                ** (* Cjalr *)
                   apply ActionCommutes_LetExp; intros ?.
                   apply ActionCommutes_IfElse.
                   --- apply ActionCommutes_LetExp; intros ?.
                       apply ActionCommutes_writeCsr_updGpr.
                   --- apply ActionCommutes_Return.
                   --- intros ?; apply ActionCommutes_Return.
                ** (* Mret *)
                   apply ActionCommutes_LetAction; [apply ActionCommutes_readScr_updGpr | intros ?].
                   apply ActionCommutes_LetExp; intros ?.
                   apply ActionCommutes_Seq; [apply ActionCommutes_writeCsr_updGpr |].
                   apply ActionCommutes_LetExp; intros ?.
                   apply ActionCommutes_Return.
                ** intros ?; apply ActionCommutes_Return.
             ++ intros ?; apply ActionCommutes_Return.
        * intros ?; apply ActionCommutes_Return.
      + intros ?; apply ActionCommutes_Return.
    - intros ?; apply ActionCommutes_Return.
  Qed.

  Theorem ActionCommutes_executeNonDeferred_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut).
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut Hdst.
    unfold executeNonDeferred.
    apply ActionCommutes_LetExp; intros ?.
    apply ActionCommutes_LetAction; [apply ActionCommutes_isInterruptPending_updGpr | intros ?].
    apply ActionCommutes_IfElse.
    - apply ActionCommutes_executeInterrupt_updGpr.
    - apply ActionCommutes_IfElse.
      + repeat step_LetExp.
        apply ActionCommutes_LetAction;
          [apply ActionCommutes_executeSequential_updGpr; exact Hdst
          | intros ?; apply ActionCommutes_Return].
      + apply ActionCommutes_executeNonSequential_updGpr; exact Hdst.
      + intros ?; apply ActionCommutes_Return.
    - intros ?; apply ActionCommutes_Return.
  Qed.

End RfActionCommutes.

(* ===========================================================================
 * 3. `writeGprVal`, `flushMulDivCaps`, AND `flushMulDiv` COMMUTATION LEMMAS
 * =========================================================================== *)

Section FlushMulDivLemmas.
  Variable pcAddrInit : Z.
  Context {env : Env (RfTree pcAddrInit)}.

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind
               evalWriteRegsList evalReadRegsList.
  Local Strategy opaque [evalWriteRegsList evalReadRegsList ElemState gprPathsWithKind scrPathsWithKind csrPathsWithKind].

  Lemma writeGprVal_unfold :
    forall dstIdx val (rf : RfState pcAddrInit),
      writeGprVal pcAddrInit dstIdx val rf =
      if negb (Zmod.eqb dstIdx Zmod.zero)
      then updGpr pcAddrInit dstIdx val rf
      else rf.
  Proof.
    intros dstIdx val rf; reflexivity.
  Qed.

  Local Opaque rfTree TreeState getDefault
               updGpr readGpr updScr readScr updCsr readCsr writeGprVal
               evalActionPropGen
               executeNonDeferred executeNonSequential executeSequential
               executeInterrupt handleTrap isInterruptPending regRead.

  Lemma writeGprVal_zero :
    forall dstIdx val (rf : RfState pcAddrInit),
      Zmod.eqb dstIdx Zmod.zero = true ->
      writeGprVal pcAddrInit dstIdx val rf = rf.
  Proof.
    intros dstIdx val rf Hz.
    rewrite writeGprVal_unfold, Hz; reflexivity.
  Qed.

  Local Strategy opaque [rfTree TreeState].

  Lemma readCsr_writeGprVal :
    forall cIdx dstIdx val (rf : RfState pcAddrInit),
      readCsr pcAddrInit cIdx (writeGprVal pcAddrInit dstIdx val rf) =
      readCsr pcAddrInit cIdx rf.
  Proof.
    intros cIdx dstIdx val rf.
    rewrite writeGprVal_unfold.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply readCsr_updGpr | reflexivity].
  Qed.

  Lemma readGpr_writeGprVal_other :
    forall rIdx dstIdx val (rf : RfState pcAddrInit),
      (Zmod.eqb dstIdx Zmod.zero = false -> rIdx <> dstIdx) ->
      readGpr pcAddrInit rIdx (writeGprVal pcAddrInit dstIdx val rf) =
      readGpr pcAddrInit rIdx rf.
  Proof.
    intros rIdx dstIdx val rf Hneq.
    rewrite writeGprVal_unfold.
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hz; cbn [negb].
    - reflexivity.
    - apply readGpr_updGpr_other; exact (Hneq eq_refl).
  Qed.

  Lemma readGpr_zero_writeGprVal :
    forall dstIdx val (rf : RfState pcAddrInit),
      readGpr pcAddrInit Zmod.zero (writeGprVal pcAddrInit dstIdx val rf) =
      readGpr pcAddrInit Zmod.zero rf.
  Proof.
    intros dstIdx val rf.
    apply readGpr_writeGprVal_other.
    intros Hz Heq; subst dstIdx.
    rewrite Zmod.eqb_refl in Hz; discriminate Hz.
  Qed.

  Local Transparent RfTree RfState writeGprVal updGpr.

  Lemma writeGprVal_comm :
    forall idx1 val1 idx2 val2 (rf : RfState pcAddrInit),
      (Zmod.eqb idx1 Zmod.zero = false -> Zmod.eqb idx2 Zmod.zero = false -> idx1 <> idx2) ->
      writeGprVal pcAddrInit idx1 val1 (writeGprVal pcAddrInit idx2 val2 rf) =
      writeGprVal pcAddrInit idx2 val2 (writeGprVal pcAddrInit idx1 val1 rf).
  Proof.
    intros idx1 val1 idx2 val2 rf Hneq.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind pcAddrInit)) with (updGpr pcAddrInit).
    destruct (Zmod.eqb idx1 Zmod.zero) eqn:Hz1;
      destruct (Zmod.eqb idx2 Zmod.zero) eqn:Hz2; cbn [negb]; try reflexivity.
    apply updGpr_comm; exact (not_eq_sym (Hneq eq_refl eq_refl)).
  Qed.

  Lemma writeGprVal_updGpr_other_comm :
    forall dstIdx val wIdx wVal (rf : RfState pcAddrInit),
      (Zmod.eqb dstIdx Zmod.zero = false -> dstIdx <> wIdx) ->
      writeGprVal pcAddrInit dstIdx val (updGpr pcAddrInit wIdx wVal rf) =
      updGpr pcAddrInit wIdx wVal (writeGprVal pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val wIdx wVal rf Hneq.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind pcAddrInit)) with (updGpr pcAddrInit).
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hz; cbn [negb].
    - reflexivity.
    - apply updGpr_comm; exact (not_eq_sym (Hneq eq_refl)).
  Qed.

  Lemma writeGprVal_updGpr_zero_comm :
    forall dstIdx val pccVal (rf : RfState pcAddrInit),
      writeGprVal pcAddrInit dstIdx val (updGpr pcAddrInit Zmod.zero pccVal rf) =
      updGpr pcAddrInit Zmod.zero pccVal (writeGprVal pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val pccVal rf.
    apply writeGprVal_updGpr_other_comm.
    intros Hz Heq; subst dstIdx.
    rewrite Zmod.eqb_refl in Hz; discriminate Hz.
  Qed.

  Lemma ActionCommutes_writeGprVal {k : Kind} :
    forall dstIdx val (act : Action type (RfTree pcAddrInit) k),
      (Zmod.eqb dstIdx Zmod.zero = false ->
       ActionCommutes (updGpr pcAddrInit dstIdx val) act) ->
      ActionCommutes (writeGprVal pcAddrInit dstIdx val) act.
  Proof.
    intros dstIdx val act Hcomm env0 s P.
    unfold writeGprVal, updGpr in *.
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hz; cbn [negb].
    - split; intros H; exact H.
    - exact (Hcomm eq_refl env0 s P).
  Qed.
  Local Opaque writeGprVal updGpr.
  Local Strategy opaque [writeGprVal updGpr readGpr updScr readScr updCsr readCsr].

  Theorem ActionCommutes_executeNonDeferred_writeGprVal :
    forall dstIdx val (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion),
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
       dstIdx <> aluOut.(Snd).(Fst)) ->
      ActionCommutes (writeGprVal pcAddrInit dstIdx val)
        (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut).
  Proof.
    intros dstIdx val currPcc meip mtip aluOut Hdst.
    apply ActionCommutes_writeGprVal; intros Hz.
    apply ActionCommutes_executeNonDeferred_updGpr; exact (Hdst Hz).
  Qed.

  Theorem SemAction_executeNonDeferred_writeGprVal :
    forall dstIdx val (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : RfState pcAddrInit)
           (execOut : type ExecuteOut),
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
       dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut)
        (writeGprVal pcAddrInit dstIdx val rf)
        (writeGprVal pcAddrInit dstIdx val rf')
        execOut.
  Proof.
    intros dstIdx val currPcc meip mtip aluOut rf rf' execOut Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeNonDeferred_writeGprVal; exact Hdst.
    - exact Hsem.
  Qed.

  (* --- `flushMulDivCaps` Structural and Commutation Lemmas --- *)

  Lemma flushMulDivCaps_app :
    forall (l1 l2 : list (bits RegIdxSzReal * type FullECapWithTag))
           (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit (l1 ++ l2)%list rf =
      flushMulDivCaps pcAddrInit l2 (flushMulDivCaps pcAddrInit l1 rf).
  Proof.
    induction l1 as [| [dstIdx resCap] rest IH]; intros l2 rf; cbn [flushMulDivCaps app].
    - reflexivity.
    - apply IH.
  Qed.

  Lemma flushMulDivCaps_snoc :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           dstIdx resCap (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit (entries ++ [(dstIdx, resCap)])%list rf =
      writeGprVal pcAddrInit dstIdx resCap (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    intros entries dstIdx resCap rf.
    rewrite flushMulDivCaps_app; reflexivity.
  Qed.

  Local Strategy 0 [rfTree TreeState].
  Local Strategy opaque [rfTree TreeState].

  Theorem SemAction_executeNonDeferred_flushMulDivCaps :
    forall entries (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf rf' : RfState pcAddrInit) (execOut : type ExecuteOut),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
         dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        execOut.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros currPcc meip mtip aluOut rf rf' execOut Hneq Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH.
      + intros d r Hin Hz Hdst; exact (Hneq d r (or_intror Hin) Hz Hdst).
      + apply SemAction_executeNonDeferred_writeGprVal;
          [intros Hz Hdst; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz Hdst) | exact Hsem].
  Qed.

End FlushMulDivLemmas.

(* ===========================================================================
 * 4. `GhostStep` AND `Inductive GhostList` STRUCTURAL & COMMUTATION LEMMAS
 * =========================================================================== *)

Section GhostListLemmas.
  Variable pcAddrInit : Z.

  Local Opaque rfTree TreeState getDefault
               gprPathsWithKind scrPathsWithKind csrPathsWithKind
               evalWriteRegsList evalReadRegsList
               updGpr readGpr updScr readScr updCsr readCsr writeGprVal
               evalActionPropGen executeNonDeferred.
  Local Strategy opaque [rfTree TreeState ElemState gprPathsWithKind scrPathsWithKind csrPathsWithKind
                         evalWriteRegsList evalReadRegsList
                         writeGprVal updGpr readGpr updScr readScr updCsr readCsr].

  (* --- 4C. Commutation of `updGpr`, `writeGprVal`, and `flushMulDivCaps` with `GhostStep` and `GhostList` --- *)

  Local Transparent updGpr.
  Local Strategy 0 [updGpr].
  Local Opaque updGpr.
  Local Strategy opaque [updGpr].

End GhostListLemmas.
