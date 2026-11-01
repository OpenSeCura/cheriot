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

  Lemma ActionCommutes_readGpr_updGpr_other :
    forall wIdx wbVal (idxExpr : Expr type (Bit RegIdxSzReal)),
      evalExpr idxExpr <> wIdx ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (readRegsList (gprPathsWithKind pcAddrInit) idxExpr).
  Proof.
    intros wIdx wbVal idxExpr Hneq env0 s P.
    rewrite !evalActionPropGen_readRegsList.
    change (evalReadRegsList (gprPathsWithKind pcAddrInit) (evalExpr idxExpr) (updGpr pcAddrInit wIdx wbVal s))
      with (readGpr pcAddrInit (evalExpr idxExpr) (updGpr pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (gprPathsWithKind pcAddrInit) (evalExpr idxExpr) s)
      with (readGpr pcAddrInit (evalExpr idxExpr) s).
    rewrite readGpr_updGpr_other by exact Hneq.
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

  Lemma ActionCommutes_incrementMcycle_updGpr :
    forall wIdx wbVal,
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@incrementMcycle pcAddrInit type).
  Proof.
    intros wIdx wbVal.
    unfold incrementMcycle.
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

  Theorem SemAction_isInterruptPending_updGpr :
    forall wIdx wbVal (meip mtip : bool)
           (rf rf' : TreeState ElemState rTree) (res : bool),
      SemAction env (@isInterruptPending pcAddrInit type meip mtip) rf rf' res ->
      SemAction env (@isInterruptPending pcAddrInit type meip mtip)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        res.
  Proof.
    intros wIdx wbVal meip mtip rf rf' res Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_isInterruptPending_updGpr.
    - exact Hsem.
  Qed.

  Theorem SemAction_handleTrap_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (mcauseVal mtvalVal : type (Bit Xlen))
           (rf rf' : TreeState ElemState rTree) (execOut : type ExecuteOut),
      SemAction env (@handleTrap pcAddrInit type currPcc mcauseVal mtvalVal) rf rf' execOut ->
      SemAction env (@handleTrap pcAddrInit type currPcc mcauseVal mtvalVal)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc mcauseVal mtvalVal rf rf' execOut Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_handleTrap_updGpr.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeInterrupt_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool)
           (rf rf' : TreeState ElemState rTree) (execOut : type ExecuteOut),
      SemAction env (@executeInterrupt pcAddrInit type currPcc meip mtip) rf rf' execOut ->
      SemAction env (@executeInterrupt pcAddrInit type currPcc meip mtip)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc meip mtip rf rf' execOut Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeInterrupt_updGpr.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeSequential_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (aluOut : type AluOutUnion)
           (rf rf' : TreeState ElemState rTree) (mulDivOpt : type (Option MulDivUnion)),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeSequential pcAddrInit type currPcc aluOut) rf rf' mulDivOpt ->
      SemAction env (@executeSequential pcAddrInit type currPcc aluOut)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        mulDivOpt.
  Proof.
    intros wIdx wbVal currPcc aluOut rf rf' mulDivOpt Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeSequential_updGpr; exact Hdst.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeNonSequential_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : TreeState ElemState rTree)
           (execOut : type ExecuteOut),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut rf rf' execOut Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeNonSequential_updGpr; exact Hdst.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeNonDeferred_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : TreeState ElemState rTree)
           (execOut : type ExecuteOut),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut rf rf' execOut Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeNonDeferred_updGpr; exact Hdst.
    - exact Hsem.
  Qed.

  (* --- `DataMem` branch commutation (when `Sequential = false` and `DataMem = true`) --- *)

  Lemma ActionCommutes_executeNonSequential_DataMem_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion),
      let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
      let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
      let noExcOp : type NoExceptionUnion := evalExpr (#nonSeqOp `! "NoException") in
      evalExpr (#noExcOp `? "DataMem") = true ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut).
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut aluOp nonSeqOp noExcOp Hdm.
    unfold executeNonSequential.
    do 5 apply ActionCommutes_LetExp_eval.
    repeat step_LetExp.
    apply ActionCommutes_IfElse.
    - repeat step_LetExp.
      apply ActionCommutes_handleTrap_updGpr.
    - apply ActionCommutes_Seq; [apply ActionCommutes_incrementMinstret_updGpr |].
      apply ActionCommutes_Seq; [apply ActionCommutes_writeScr_updGpr |].
      apply ActionCommutes_LetExp_eval.
      apply ActionCommutes_IfElse_dep.
      + intros _.
        apply ActionCommutes_LetExp; intros ?.
        apply ActionCommutes_IfElse.
        * repeat step_LetExp.
          apply ActionCommutes_IfElse.
          -- apply ActionCommutes_updateMshwmOnStore_updGpr.
          -- apply ActionCommutes_Return.
          -- intros ?; apply ActionCommutes_LetExp; intros ?; apply ActionCommutes_Return.
        * repeat step_LetExp; apply ActionCommutes_Return.
        * intros ?; apply ActionCommutes_Return.
      + intros HnotDm; subst aluOp nonSeqOp noExcOp; cbn [evalExpr] in Hdm, HnotDm; congruence.
      + intros ?; apply ActionCommutes_Return.
    - intros ?; apply ActionCommutes_Return.
  Qed.

  Theorem ActionCommutes_executeNonDeferred_DataMem_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion),
      let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
      let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
      let noExcOp : type NoExceptionUnion := evalExpr (#nonSeqOp `! "NoException") in
      evalExpr (#aluOp `? "Sequential") = false ->
      evalExpr (#noExcOp `? "DataMem") = true ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut).
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut aluOp nonSeqOp noExcOp Hseq Hdm.
    unfold executeNonDeferred.
    apply ActionCommutes_LetExp_eval.
    apply ActionCommutes_LetAction; [apply ActionCommutes_isInterruptPending_updGpr | intros ?].
    apply ActionCommutes_IfElse.
    - apply ActionCommutes_executeInterrupt_updGpr.
    - apply ActionCommutes_IfElse_dep.
      + intros Htrue; subst aluOp; cbn [evalExpr] in Hseq, Htrue; congruence.
      + intros _; apply ActionCommutes_executeNonSequential_DataMem_updGpr; exact Hdm.
      + intros ?; apply ActionCommutes_Return.
    - intros ?; apply ActionCommutes_Return.
  Qed.

  (* --- `regRead` Commutation with `updGpr` --- *)

  Lemma evalExpr_ITE_ext {k : Kind} :
    forall (c : Expr type Bool) (e1 e1' e2 : Expr type k),
      (evalExpr c = true -> evalExpr e1 = evalExpr e1') ->
      evalExpr (ITE c e1 e2) = evalExpr (ITE c e1' e2).
  Proof.
    intros c e1 e1' e2 Heq; cbn [evalExpr].
    destruct (evalExpr c) eqn:Hc; [exact (Heq eq_refl) | reflexivity].
  Qed.

  Lemma ActionCommutes_readGpr_ITE0 {k' : Kind} :
    forall wIdx wbVal (nm1 nm2 : string) (idx : bits RegIdxSzReal)
           (cont : type FullECapWithTag -> Action type rTree k'),
      (Zmod.eqb idx Zmod.zero = false -> idx <> wIdx) ->
      (forall cs, ActionCommutes (updGpr pcAddrInit wIdx wbVal) (cont cs)) ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (LetAction nm1 (readRegsList (gprPathsWithKind pcAddrInit) (Var type (Bit RegIdxSzReal) idx))
          (fun csRaw =>
             LetExp nm2 (ITE0 (isNotZero (Var type (Bit RegIdxSzReal) idx)) (Var type FullECapWithTag csRaw))
               cont)).
  Proof.
    intros wIdx wbVal nm1 nm2 idx cont Hidx Hcont env0 s P.
    cbn [evalActionPropGen].
    rewrite !evalActionPropGen_readRegsList.
    cbn [evalActionPropGen].
    change (evalExpr (Var type (Bit RegIdxSzReal) idx)) with idx.
    change (evalReadRegsList (gprPathsWithKind pcAddrInit) idx (updGpr pcAddrInit wIdx wbVal s))
      with (readGpr pcAddrInit idx (updGpr pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (gprPathsWithKind pcAddrInit) idx s)
      with (readGpr pcAddrInit idx s).
    unfold ITE0.
    erewrite (evalExpr_ITE_ext (isNotZero (Var type (Bit RegIdxSzReal) idx))
                (Var type FullECapWithTag (readGpr pcAddrInit idx (updGpr pcAddrInit wIdx wbVal s)))
                (Var type FullECapWithTag (readGpr pcAddrInit idx s))).
    - apply Hcont.
    - intros Hnz; apply isNotZero_true_iff in Hnz.
      cbn [evalExpr].
      apply readGpr_updGpr_other; exact (Hidx Hnz).
  Qed.

  Theorem ActionCommutes_regRead_updGpr :
    forall wIdx wbVal (regReadIn : type RegReadIn),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb cs1Idx Zmod.zero = false -> cs1Idx <> wIdx) ->
      (Zmod.eqb cs2Idx Zmod.zero = false -> cs2Idx <> wIdx) ->
      ActionCommutes (updGpr pcAddrInit wIdx wbVal)
        (@regRead pcAddrInit type regReadIn).
  Proof.
    intros wIdx wbVal regReadIn decodeOut cs1Idx cs2Idx Hcs1 Hcs2.
    unfold regRead.
    do 4 apply ActionCommutes_LetExp_eval.
    apply ActionCommutes_readGpr_ITE0; [exact Hcs1 | intros ?].
    apply ActionCommutes_readGpr_ITE0; [exact Hcs2 | intros ?].
    apply ActionCommutes_Return.
  Qed.

  Theorem SemAction_regRead_updGpr :
    forall wIdx wbVal (regReadIn : type RegReadIn)
           (rf rf' : TreeState ElemState rTree) (out : type AluInInstGroup),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb cs1Idx Zmod.zero = false -> cs1Idx <> wIdx) ->
      (Zmod.eqb cs2Idx Zmod.zero = false -> cs2Idx <> wIdx) ->
      SemAction env (@regRead pcAddrInit type regReadIn) rf rf' out ->
      SemAction env (@regRead pcAddrInit type regReadIn)
        (updGpr pcAddrInit wIdx wbVal rf)
        (updGpr pcAddrInit wIdx wbVal rf')
        out.
  Proof.
    intros wIdx wbVal regReadIn rf rf' out decodeOut cs1Idx cs2Idx Hcs1 Hcs2 Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_regRead_updGpr; [exact Hcs1 | exact Hcs2].
    - exact Hsem.
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

  Lemma writeGprVal_zero_literal :
    forall val (rf : RfState pcAddrInit),
      writeGprVal pcAddrInit Zmod.zero val rf = rf.
  Proof.
    intros val rf.
    apply writeGprVal_zero.
    apply Zmod.eqb_refl.
  Qed.

  Lemma writeGprVal_nonzero :
    forall dstIdx val (rf : RfState pcAddrInit),
      Zmod.eqb dstIdx Zmod.zero = false ->
      writeGprVal pcAddrInit dstIdx val rf = updGpr pcAddrInit dstIdx val rf.
  Proof.
    intros dstIdx val rf Hnz.
    rewrite writeGprVal_unfold, Hnz; reflexivity.
  Qed.

  Lemma writeGprVal_Snd :
    forall dstIdx val (rf : RfState pcAddrInit),
      (writeGprVal pcAddrInit dstIdx val rf).(Snd) = rf.(Snd).
  Proof.
    intros dstIdx val rf.
    rewrite writeGprVal_unfold.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply updGpr_Snd | reflexivity].
  Qed.

  Local Strategy opaque [rfTree TreeState].

  Lemma readScr_writeGprVal :
    forall sIdx dstIdx val (rf : RfState pcAddrInit),
      readScr pcAddrInit sIdx (writeGprVal pcAddrInit dstIdx val rf) =
      readScr pcAddrInit sIdx rf.
  Proof.
    intros sIdx dstIdx val rf.
    rewrite writeGprVal_unfold.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply readScr_updGpr | reflexivity].
  Qed.

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

  Lemma writeGprVal_updScr_comm :
    forall dstIdx val sIdx sVal (rf : RfState pcAddrInit),
      writeGprVal pcAddrInit dstIdx val (updScr pcAddrInit sIdx sVal rf) =
      updScr pcAddrInit sIdx sVal (writeGprVal pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val sIdx sVal rf.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind pcAddrInit)) with (updGpr pcAddrInit).
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply updGpr_updScr_comm | reflexivity].
  Qed.

  Lemma writeGprVal_updCsr_comm :
    forall dstIdx val cIdx cVal (rf : RfState pcAddrInit),
      writeGprVal pcAddrInit dstIdx val (updCsr pcAddrInit cIdx cVal rf) =
      updCsr pcAddrInit cIdx cVal (writeGprVal pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val cIdx cVal rf.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind pcAddrInit)) with (updGpr pcAddrInit).
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply updGpr_updCsr_comm | reflexivity].
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

  Theorem SemAction_executeNonDeferred_DataMem_writeGprVal :
    forall dstIdx val (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : RfState pcAddrInit)
           (execOut : type ExecuteOut),
      let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
      let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
      let noExcOp : type NoExceptionUnion := evalExpr (#nonSeqOp `! "NoException") in
      evalExpr (#aluOp `? "Sequential") = false ->
      evalExpr (#noExcOp `? "DataMem") = true ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut)
        (writeGprVal pcAddrInit dstIdx val rf)
        (writeGprVal pcAddrInit dstIdx val rf')
        execOut.
  Proof.
    intros dstIdx val currPcc meip mtip aluOut rf rf' execOut aluOp nonSeqOp noExcOp Hseq Hdm Hsem.
    eapply ActionCommutes_SemAction; [| exact Hsem].
    apply ActionCommutes_writeGprVal; intros _.
    apply ActionCommutes_executeNonDeferred_DataMem_updGpr; [exact Hseq | exact Hdm].
  Qed.

  Theorem ActionCommutes_regRead_writeGprVal :
    forall dstIdx val (regReadIn : type RegReadIn),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb dstIdx Zmod.zero = false -> Zmod.eqb cs1Idx Zmod.zero = false -> cs1Idx <> dstIdx) ->
      (Zmod.eqb dstIdx Zmod.zero = false -> Zmod.eqb cs2Idx Zmod.zero = false -> cs2Idx <> dstIdx) ->
      ActionCommutes (writeGprVal pcAddrInit dstIdx val)
        (@regRead pcAddrInit type regReadIn).
  Proof.
    intros dstIdx val regReadIn decodeOut cs1Idx cs2Idx Hcs1 Hcs2.
    apply ActionCommutes_writeGprVal; intros Hz.
    apply ActionCommutes_regRead_updGpr; [exact (Hcs1 Hz) | exact (Hcs2 Hz)].
  Qed.

  Theorem SemAction_regRead_writeGprVal :
    forall dstIdx val (regReadIn : type RegReadIn)
           (rf rf' : RfState pcAddrInit) (out : type AluInInstGroup),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb dstIdx Zmod.zero = false -> Zmod.eqb cs1Idx Zmod.zero = false -> cs1Idx <> dstIdx) ->
      (Zmod.eqb dstIdx Zmod.zero = false -> Zmod.eqb cs2Idx Zmod.zero = false -> cs2Idx <> dstIdx) ->
      SemAction env (@regRead pcAddrInit type regReadIn) rf rf' out ->
      SemAction env (@regRead pcAddrInit type regReadIn)
        (writeGprVal pcAddrInit dstIdx val rf)
        (writeGprVal pcAddrInit dstIdx val rf')
        out.
  Proof.
    intros dstIdx val regReadIn rf rf' out decodeOut cs1Idx cs2Idx Hcs1 Hcs2 Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_regRead_writeGprVal; [exact Hcs1 | exact Hcs2].
    - exact Hsem.
  Qed.

  (* --- `flushMulDivCaps` Structural and Commutation Lemmas --- *)

  Lemma flushMulDivCaps_nil :
    forall (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit [] rf = rf.
  Proof.
    intros rf; reflexivity.
  Qed.

  Lemma flushMulDivCaps_cons :
    forall dstIdx resCap rest (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit ((dstIdx, resCap) :: rest) rf =
      flushMulDivCaps pcAddrInit rest (writeGprVal pcAddrInit dstIdx resCap rf).
  Proof.
    intros dstIdx resCap rest rf; reflexivity.
  Qed.

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
  Lemma flushMulDivCaps_Snd :
    forall entries (rf : RfState pcAddrInit),
      (flushMulDivCaps pcAddrInit entries rf).(Snd) = rf.(Snd).
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply writeGprVal_Snd.
  Qed.
  Local Strategy opaque [rfTree TreeState].

  Lemma readScr_flushMulDivCaps :
    forall sIdx entries (rf : RfState pcAddrInit),
      readScr pcAddrInit sIdx (flushMulDivCaps pcAddrInit entries rf) =
      readScr pcAddrInit sIdx rf.
  Proof.
    intros sIdx entries; induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply readScr_writeGprVal.
  Qed.

  Lemma readCsr_flushMulDivCaps :
    forall cIdx entries (rf : RfState pcAddrInit),
      readCsr pcAddrInit cIdx (flushMulDivCaps pcAddrInit entries rf) =
      readCsr pcAddrInit cIdx rf.
  Proof.
    intros cIdx entries; induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply readCsr_writeGprVal.
  Qed.

  Lemma readGpr_zero_flushMulDivCaps :
    forall entries (rf : RfState pcAddrInit),
      readGpr pcAddrInit Zmod.zero (flushMulDivCaps pcAddrInit entries rf) =
      readGpr pcAddrInit Zmod.zero rf.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply readGpr_zero_writeGprVal.
  Qed.

  Lemma readGpr_flushMulDivCaps_other :
    forall rIdx entries (rf : RfState pcAddrInit),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         rIdx <> dstIdx) ->
      readGpr pcAddrInit rIdx (flushMulDivCaps pcAddrInit entries rf) =
      readGpr pcAddrInit rIdx rf.
  Proof.
    intros rIdx entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf Hneq; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH.
      + apply readGpr_writeGprVal_other.
        intros Hz; apply (Hneq dstIdx resCap (or_introl eq_refl) Hz).
      + intros d r Hin Hz; apply (Hneq d r (or_intror Hin) Hz).
  Qed.

  Lemma updScr_flushMulDivCaps_comm :
    forall sIdx sVal entries (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit entries (updScr pcAddrInit sIdx sVal rf) =
      updScr pcAddrInit sIdx sVal (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    intros sIdx sVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updScr pcAddrInit sIdx sVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updScr_comm dstIdx resCap sIdx sVal rf).
      apply IH.
  Qed.

  Lemma updCsr_flushMulDivCaps_comm :
    forall cIdx cVal entries (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit entries (updCsr pcAddrInit cIdx cVal rf) =
      updCsr pcAddrInit cIdx cVal (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    intros cIdx cVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updCsr pcAddrInit cIdx cVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updCsr_comm dstIdx resCap cIdx cVal rf).
      apply IH.
  Qed.

  Lemma updGpr_zero_flushMulDivCaps_comm :
    forall pccVal entries (rf : RfState pcAddrInit),
      flushMulDivCaps pcAddrInit entries (updGpr pcAddrInit Zmod.zero pccVal rf) =
      updGpr pcAddrInit Zmod.zero pccVal (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    intros pccVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updGpr pcAddrInit Zmod.zero pccVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updGpr_zero_comm dstIdx resCap pccVal rf).
      apply IH.
  Qed.

  Lemma updGpr_other_flushMulDivCaps_comm :
    forall wIdx wVal entries (rf : RfState pcAddrInit),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         dstIdx <> wIdx) ->
      flushMulDivCaps pcAddrInit entries (updGpr pcAddrInit wIdx wVal rf) =
      updGpr pcAddrInit wIdx wVal (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    intros wIdx wVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf Hneq.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updGpr pcAddrInit wIdx wVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updGpr_other_comm dstIdx resCap wIdx wVal rf).
      + apply IH; intros d r Hin Hz; exact (Hneq d r (or_intror Hin) Hz).
      + intros Hz; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz).
  Qed.

  Lemma writeGprVal_flushMulDivCaps_comm :
    forall wIdx wVal entries (rf : RfState pcAddrInit),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb wIdx Zmod.zero = false ->
         dstIdx <> wIdx) ->
      flushMulDivCaps pcAddrInit entries (writeGprVal pcAddrInit wIdx wVal rf) =
      writeGprVal pcAddrInit wIdx wVal (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    intros wIdx wVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf Hneq; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite (writeGprVal_comm dstIdx resCap wIdx wVal rf).
      + apply IH; intros d r Hin Hz1 Hz2; exact (Hneq d r (or_intror Hin) Hz1 Hz2).
      + intros Hz1 Hz2; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz1 Hz2).
  Qed.

  Theorem SemAction_isInterruptPending_flushMulDivCaps :
    forall entries (meip mtip : bool)
           (rf rf' : RfState pcAddrInit) (res : bool),
      SemAction env (@isInterruptPending pcAddrInit type meip mtip) rf rf' res ->
      SemAction env (@isInterruptPending pcAddrInit type meip mtip)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        res.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros meip mtip rf rf' res Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH.
      eapply ActionCommutes_SemAction; [| exact Hsem].
      apply ActionCommutes_writeGprVal; intros _.
      apply ActionCommutes_isInterruptPending_updGpr.
  Qed.

  Theorem SemAction_executeInterrupt_flushMulDivCaps :
    forall entries (currPcc : type FullECapWithTag) (meip mtip : bool)
           (rf rf' : RfState pcAddrInit) (execOut : type ExecuteOut),
      SemAction env (@executeInterrupt pcAddrInit type currPcc meip mtip) rf rf' execOut ->
      SemAction env (@executeInterrupt pcAddrInit type currPcc meip mtip)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        execOut.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros currPcc meip mtip rf rf' execOut Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH.
      eapply ActionCommutes_SemAction; [| exact Hsem].
      apply ActionCommutes_writeGprVal; intros _.
      apply ActionCommutes_executeInterrupt_updGpr.
  Qed.

  Theorem SemAction_executeSequential_flushMulDivCaps :
    forall entries (currPcc : type FullECapWithTag) (aluOut : type AluOutUnion)
           (rf rf' : RfState pcAddrInit) (mulDivOpt : type (Option MulDivUnion)),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
         dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeSequential pcAddrInit type currPcc aluOut) rf rf' mulDivOpt ->
      SemAction env (@executeSequential pcAddrInit type currPcc aluOut)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        mulDivOpt.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros currPcc aluOut rf rf' mulDivOpt Hneq Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH.
      + intros d r Hin Hz Hdst; exact (Hneq d r (or_intror Hin) Hz Hdst).
      + eapply ActionCommutes_SemAction; [| exact Hsem].
        apply ActionCommutes_writeGprVal; intros Hz.
        apply ActionCommutes_executeSequential_updGpr; intros Hdst; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz Hdst).
  Qed.

  Theorem SemAction_executeNonSequential_flushMulDivCaps :
    forall entries (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf rf' : RfState pcAddrInit) (execOut : type ExecuteOut),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
         dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction env (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        execOut.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros currPcc meip mtip aluOut rf rf' execOut Hneq Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH.
      + intros d r Hin Hz Hdst; exact (Hneq d r (or_intror Hin) Hz Hdst).
      + eapply ActionCommutes_SemAction; [| exact Hsem].
        apply ActionCommutes_writeGprVal; intros Hz.
        apply ActionCommutes_executeNonSequential_updGpr; intros Hdst; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz Hdst).
  Qed.

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

  Theorem SemAction_executeNonDeferred_DataMem_flushMulDivCaps :
    forall entries (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf rf' : RfState pcAddrInit) (execOut : type ExecuteOut),
      let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
      let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
      let noExcOp : type NoExceptionUnion := evalExpr (#nonSeqOp `! "NoException") in
      evalExpr (#aluOp `? "Sequential") = false ->
      evalExpr (#noExcOp `? "DataMem") = true ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        execOut.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH];
      intros currPcc meip mtip aluOut rf rf' execOut aluOp nonSeqOp noExcOp Hseq Hdm Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH; [exact Hseq | exact Hdm |].
      apply SemAction_executeNonDeferred_DataMem_writeGprVal; [exact Hseq | exact Hdm | exact Hsem].
  Qed.

  Theorem SemAction_regRead_flushMulDivCaps :
    forall entries (regReadIn : type RegReadIn)
           (rf rf' : RfState pcAddrInit) (out : type AluInInstGroup),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb cs1Idx Zmod.zero = false ->
         cs1Idx <> dstIdx) ->
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb cs2Idx Zmod.zero = false ->
         cs2Idx <> dstIdx) ->
      SemAction env (@regRead pcAddrInit type regReadIn) rf rf' out ->
      SemAction env (@regRead pcAddrInit type regReadIn)
        (flushMulDivCaps pcAddrInit entries rf)
        (flushMulDivCaps pcAddrInit entries rf')
        out.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH];
      intros regReadIn rf rf' out decodeOut cs1Idx cs2Idx Hcs1 Hcs2 Hsem; cbn [flushMulDivCaps].
    - exact Hsem.
    - apply IH.
      + intros d r Hin Hz Hc1; exact (Hcs1 d r (or_intror Hin) Hz Hc1).
      + intros d r Hin Hz Hc2; exact (Hcs2 d r (or_intror Hin) Hz Hc2).
      + apply SemAction_regRead_writeGprVal.
        * intros Hz Hc1; exact (Hcs1 dstIdx resCap (or_introl eq_refl) Hz Hc1).
        * intros Hz Hc2; exact (Hcs2 dstIdx resCap (or_introl eq_refl) Hz Hc2).
        * exact Hsem.
  Qed.

  (* --- `flushMulDivOn` Preservation, Writeback Pop, and Enqueue Lemmas --- *)

  Section FlushMulDivOnMode.
    Variable mulCapacity divCapacity mulStages divStages : nat.
    Variable mulDivMode : MulDivMode.
    Variable bp : WithInstPredIfc.

    Local Opaque MulDivSubState extractMulDivEntries.
    Local Strategy opaque [MulDivSubState extractMulDivEntries].

    Lemma flushMulDivOn_preserve :
      forall (rf : RfState pcAddrInit)
             (smd smd' : MulDivSubState mulCapacity divCapacity mulStages divStages mulDivMode),
        extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode smd' =
        extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode smd ->
        flushMulDivOn pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd' =
        flushMulDivOn pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd.
    Proof.
      intros rf smd smd' Heq.
      unfold flushMulDivOn; rewrite Heq; reflexivity.
    Qed.

    Lemma flushMulDivOn_wb_pop :
      forall dstIdx resCap (rf : RfState pcAddrInit)
             (smd smd' : MulDivSubState mulCapacity divCapacity mulStages divStages mulDivMode),
        extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode smd =
        (dstIdx, resCap) :: extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode smd' ->
        flushMulDivOn pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode
          (writeGprVal pcAddrInit dstIdx resCap rf) smd' =
        flushMulDivOn pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd.
    Proof.
      intros dstIdx resCap rf smd smd' Hpop.
      unfold flushMulDivOn; rewrite Hpop; reflexivity.
    Qed.

    Lemma flushMulDivOn_enq :
      forall dstIdx resCap (rf : RfState pcAddrInit)
             (smd smd' : MulDivSubState mulCapacity divCapacity mulStages divStages mulDivMode),
        extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode smd' =
        (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode smd ++ [(dstIdx, resCap)])%list ->
        flushMulDivOn pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd' =
        writeGprVal pcAddrInit dstIdx resCap
          (flushMulDivOn pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd).
    Proof.
      intros dstIdx resCap rf smd smd' Henq.
      unfold flushMulDivOn; rewrite Henq, flushMulDivCaps_snoc; reflexivity.
    Qed.

  End FlushMulDivOnMode.

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

  (* --- 4A. Scoreboard WaitMask Helpers (`updWaitMask`, `stepWaitMask`, `foldWaitMask`) --- *)

  Definition ghostReqWritesDst (req : type MemFenceReq) : bool :=
    let dstIdx := req.(Fst) in
    let addr   := req.(Snd).(Fst) in
    let op     := req.(Snd).(Snd).(Fst) in
    let mfAct  := evalLetExpr (@dispatchMemFence type dstIdx addr op) in
    let isLoad :=
      andb (evalExpr (#mfAct `? "Mem"))
           (evalExpr ((#mfAct `! "Mem") `? "Load")) in
    andb isLoad (negb (Zmod.eqb dstIdx Zmod.zero)).

  Definition stepWaitMask
    (req : type MemFenceReq)
    (mask : bits RegIdxSzReal -> bool) : bits RegIdxSzReal -> bool :=
    updWaitMask (ghostReqWritesDst req) (req.(Fst)) true mask.

  Fixpoint foldWaitMask
    (reqs : list (type MemFenceReq))
    (mask : bits RegIdxSzReal -> bool) : bits RegIdxSzReal -> bool :=
    match reqs with
    | nil => mask
    | req :: rest => foldWaitMask rest (stepWaitMask req mask)
    end.

  Lemma updWaitMask_same :
    forall writes dstIdx val (mask : bits RegIdxSzReal -> bool),
      writes = true ->
      updWaitMask writes dstIdx val mask dstIdx = val.
  Proof.
    intros writes dstIdx val mask ->.
    unfold updWaitMask; rewrite Zmod.eqb_refl; reflexivity.
  Qed.

  Lemma updWaitMask_other :
    forall writes dstIdx val (mask : bits RegIdxSzReal -> bool) idx,
      (writes = true -> idx <> dstIdx) ->
      updWaitMask writes dstIdx val mask idx = mask idx.
  Proof.
    intros writes dstIdx val mask idx Hneq.
    unfold updWaitMask.
    destruct writes; cbn [andb]; [| reflexivity].
    destruct (Zmod.eqb idx dstIdx) eqn:Heq; [| reflexivity].
    apply Zmod.eqb_eq in Heq; exfalso; exact (Hneq eq_refl Heq).
  Qed.

  Lemma updWaitMask_false :
    forall dstIdx val (mask : bits RegIdxSzReal -> bool) idx,
      updWaitMask false dstIdx val mask idx = mask idx.
  Proof.
    intros dstIdx val mask idx; reflexivity.
  Qed.

  Lemma updWaitMask_comm_at :
    forall writes1 idx1 val1 writes2 idx2 val2 (mask : bits RegIdxSzReal -> bool) idx,
      (writes1 = true -> writes2 = true -> idx1 <> idx2) ->
      updWaitMask writes1 idx1 val1 (updWaitMask writes2 idx2 val2 mask) idx =
      updWaitMask writes2 idx2 val2 (updWaitMask writes1 idx1 val1 mask) idx.
  Proof.
    intros writes1 idx1 val1 writes2 idx2 val2 mask idx Hneq.
    unfold updWaitMask.
    destruct writes1; destruct writes2; cbn [andb]; try reflexivity.
    destruct (Zmod.eqb idx idx1) eqn:Heq1; destruct (Zmod.eqb idx idx2) eqn:Heq2; try reflexivity.
    apply Zmod.eqb_eq in Heq1; apply Zmod.eqb_eq in Heq2; subst.
    exfalso; exact (Hneq eq_refl eq_refl eq_refl).
  Qed.

  Lemma foldWaitMask_app :
    forall l1 l2 (mask : bits RegIdxSzReal -> bool),
      foldWaitMask (l1 ++ l2)%list mask = foldWaitMask l2 (foldWaitMask l1 mask).
  Proof.
    induction l1 as [| req rest IH]; intros l2 mask; cbn [foldWaitMask app].
    - reflexivity.
    - apply IH.
  Qed.

  Lemma foldWaitMask_ext :
    forall l (m1 m2 : bits RegIdxSzReal -> bool),
      (forall i, m1 i = m2 i) ->
      forall i, foldWaitMask l m1 i = foldWaitMask l m2 i.
  Proof.
    induction l as [| r rs IHl]; intros m1 m2 Heq i; cbn [foldWaitMask].
    - apply Heq.
    - apply IHl; intros j; unfold stepWaitMask, updWaitMask.
      rewrite (Heq j); reflexivity.
  Qed.

  Lemma foldWaitMask_updWaitMask_comm_at :
    forall reqs writes wIdx val (mask : bits RegIdxSzReal -> bool) idx,
      (forall req,
         In req reqs ->
         writes = true ->
         ghostReqWritesDst req = true ->
         wIdx <> req.(Fst)) ->
      foldWaitMask reqs (updWaitMask writes wIdx val mask) idx =
      updWaitMask writes wIdx val (foldWaitMask reqs mask) idx.
  Proof.
    induction reqs as [| req rest IH]; intros writes wIdx val mask idx Hneq; cbn [foldWaitMask].
    - reflexivity.
    - rewrite <- IH by (intros r Hin; apply (Hneq r (or_intror Hin))).
      apply foldWaitMask_ext; intros j.
      unfold stepWaitMask.
      apply updWaitMask_comm_at.
      intros Hwr Hw1 Heq; symmetry in Heq.
      exact (Hneq req (or_introl eq_refl) Hw1 Hwr Heq).
  Qed.

  Lemma GhostStep_waitMask_det :
    forall rf0 rf1 wm0 wm1 req,
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      wm1 = stepWaitMask req wm0.
  Proof.
    intros rf0 rf1 wm0 wm1 req Hstep.
    exact (ghost_waitMask_step pcAddrInit rf0 rf1 wm0 wm1 req Hstep).
  Qed.

  Lemma GhostList_waitMask_det :
    forall rf0 wm0 reqs rf2 wm2,
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      wm2 = foldWaitMask reqs wm0.
  Proof.
    intros rf0 wm0 reqs rf2 wm2 Hgl.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH]; cbn [foldWaitMask].
    - reflexivity.
    - rewrite IH, (GhostStep_waitMask_det rf0 rf1 wm0 wm1 req Hstep); reflexivity.
  Qed.

  Lemma GhostStep_change_waitMask :
    forall rf0 rf1 wm0 wm1 req wm0',
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep pcAddrInit rf0 rf1 wm0' (stepWaitMask req wm0') req.
  Proof.
    intros rf0 rf1 wm0 wm1 req wm0' Hstep.
    constructor.
    - reflexivity.
    - exact (ghost_rf_step pcAddrInit rf0 rf1 wm0 wm1 req Hstep).
  Qed.

  Lemma GhostList_change_waitMask :
    forall rf0 wm0 reqs rf2 wm2 wm0',
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList pcAddrInit rf0 wm0' reqs rf2 (foldWaitMask reqs wm0').
  Proof.
    intros rf0 wm0 reqs rf2 wm2 wm0' Hgl.
    revert wm0'.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH]; intros wm0'; cbn [foldWaitMask].
    - apply GhostNil.
    - eapply GhostCons.
      + eapply GhostStep_change_waitMask; exact Hstep.
      + apply IH.
  Qed.

  (* --- 4B. Structural Lemmas for `GhostList` (`snoc`, `app`, `drain`, `inv`) --- *)

  Theorem GhostList_single :
    forall rf0 rf1 wm0 wm1 req,
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostList pcAddrInit rf0 wm0 [req] rf1 wm1.
  Proof.
    intros rf0 rf1 wm0 wm1 req Hstep.
    eapply GhostCons; [exact Hstep | apply GhostNil].
  Qed.

  Theorem GhostList_app :
    forall rf0 wm0 l1 rf1 wm1 l2 rf2 wm2,
      GhostList pcAddrInit rf0 wm0 l1 rf1 wm1 ->
      GhostList pcAddrInit rf1 wm1 l2 rf2 wm2 ->
      GhostList pcAddrInit rf0 wm0 (l1 ++ l2)%list rf2 wm2.
  Proof.
    intros rf0 wm0 l1 rf1 wm1 l2 rf2 wm2 H1 H2.
    revert l2 rf2 wm2 H2.
    induction H1 as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH];
      intros l2 rf3 wm3 H2; simpl.
    - exact H2.
    - eapply GhostCons; [exact Hstep | apply IH; exact H2].
  Qed.

  Theorem GhostList_snoc :
    forall rf0 wm0 reqs rf2 wm2 rf3 wm3 req,
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostStep pcAddrInit rf2 rf3 wm2 wm3 req ->
      GhostList pcAddrInit rf0 wm0 (reqs ++ [req])%list rf3 wm3.
  Proof.
    intros rf0 wm0 reqs rf2 wm2 rf3 wm3 req Hgl Hstep.
    eapply GhostList_app; [exact Hgl | apply GhostList_single; exact Hstep].
  Qed.

  Theorem GhostList_cons_inv :
    forall rf0 wm0 req reqs rf2 wm2,
      GhostList pcAddrInit rf0 wm0 (req :: reqs) rf2 wm2 ->
      exists rf1 wm1,
        GhostStep pcAddrInit rf0 rf1 wm0 wm1 req /\
        GhostList pcAddrInit rf1 wm1 reqs rf2 wm2.
  Proof.
    intros rf0 wm0 req reqs rf2 wm2 Hgl.
    inversion Hgl; subst.
    eexists; eexists; split; eassumption.
  Qed.

  Definition GhostList_drain := GhostList_cons_inv.

  Theorem GhostList_app_inv :
    forall l1 l2 rf0 wm0 rf2 wm2,
      GhostList pcAddrInit rf0 wm0 (l1 ++ l2)%list rf2 wm2 ->
      exists rf1 wm1,
        GhostList pcAddrInit rf0 wm0 l1 rf1 wm1 /\
        GhostList pcAddrInit rf1 wm1 l2 rf2 wm2.
  Proof.
    induction l1 as [| req rest IH]; intros l2 rf0 wm0 rf2 wm2 Hgl; simpl in *.
    - exists rf0, wm0; split; [apply GhostNil | exact Hgl].
    - destruct (GhostList_cons_inv rf0 wm0 req (rest ++ l2)%list rf2 wm2 Hgl)
        as [rf1 [wm1 [Hstep Hrest]]].
      destruct (IH l2 rf1 wm1 rf2 wm2 Hrest) as [rf_mid [wm_mid [Hl1 Hl2]]].
      exists rf_mid, wm_mid; split; [eapply GhostCons; [exact Hstep | exact Hl1] | exact Hl2].
  Qed.

  Theorem GhostList_snoc_inv :
    forall reqs req rf0 wm0 rf3 wm3,
      GhostList pcAddrInit rf0 wm0 (reqs ++ [req])%list rf3 wm3 ->
      exists rf2 wm2,
        GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 /\
        GhostStep pcAddrInit rf2 rf3 wm2 wm3 req.
  Proof.
    intros reqs req rf0 wm0 rf3 wm3 Hgl.
    destruct (GhostList_app_inv reqs [req] rf0 wm0 rf3 wm3 Hgl)
      as [rf2 [wm2 [Hreqs Hsingle]]].
    destruct (GhostList_cons_inv rf2 wm2 req [] rf3 wm3 Hsingle)
      as [rf_end [wm_end [Hstep Hnil]]].
    destruct (GhostList_nil_inv pcAddrInit rf_end wm_end rf3 wm3 Hnil) as [-> ->].
    exists rf2, wm2; split; [exact Hreqs | exact Hstep].
  Qed.

  Section DataMemInFlightLemmas.
    Variable dataMemCapacity : nat.

    Local Opaque DataMemSubState isDataMemLoadRq.
    Local Strategy opaque [DataMemSubState isDataMemLoadRq].

    Lemma DataMemInFlightRel_LoadRq_True :
      forall (sdm : DataMemSubState dataMemCapacity)
             (rf_spec : RfState pcAddrInit)
             (wm0 : bits RegIdxSzReal -> bool),
        isDataMemLoadRq dataMemCapacity sdm = true ->
        DataMemInFlightRel pcAddrInit dataMemCapacity sdm rf_spec rf_spec wm0 wm0.
    Proof.
      intros sdm rf_spec wm0 Hrq.
      unfold DataMemInFlightRel; rewrite Hrq; split; reflexivity.
    Qed.

    Lemma DataMemInFlightRel_LoadRq_inv :
      forall (sdm : DataMemSubState dataMemCapacity)
             (rf_spec rf_after : RfState pcAddrInit)
             (wm0 wm_after : bits RegIdxSzReal -> bool),
        isDataMemLoadRq dataMemCapacity sdm = true ->
        DataMemInFlightRel pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
        rf_after = rf_spec /\ wm_after = wm0.
    Proof.
      intros sdm rf_spec rf_after wm0 wm_after Hrq Hrel.
      unfold DataMemInFlightRel in Hrel; rewrite Hrq in Hrel; exact Hrel.
    Qed.

    Lemma DataMemInFlightRel_NotLoadRq_inv :
      forall (sdm : DataMemSubState dataMemCapacity)
             (rf_spec rf_after : RfState pcAddrInit)
             (wm0 wm_after : bits RegIdxSzReal -> bool),
        isDataMemLoadRq dataMemCapacity sdm = false ->
        DataMemInFlightRel pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
        exists req, GhostStep pcAddrInit rf_spec rf_after wm0 wm_after req.
    Proof.
      intros sdm rf_spec rf_after wm0 wm_after Hrq Hrel.
      unfold DataMemInFlightRel in Hrel; rewrite Hrq in Hrel; exact Hrel.
    Qed.

    Theorem GhostList_drain_to_inflight :
      forall (sdm sdm' : DataMemSubState dataMemCapacity)
             (rf_spec rf_after rf_impl : RfState pcAddrInit)
             (wm0 wm_after wm_impl : bits RegIdxSzReal -> bool)
             (req : type MemFenceReq) (reqs : list (type MemFenceReq)),
        isDataMemLoadRq dataMemCapacity sdm = true ->
        isDataMemLoadRq dataMemCapacity sdm' = false ->
        DataMemInFlightRel pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
        GhostList pcAddrInit rf_after wm_after (req :: reqs) rf_impl wm_impl ->
        exists rf_after' wm_after',
          GhostStep pcAddrInit rf_spec rf_after' wm0 wm_after' req /\
          DataMemInFlightRel pcAddrInit dataMemCapacity sdm' rf_spec rf_after' wm0 wm_after' /\
          GhostList pcAddrInit rf_after' wm_after' reqs rf_impl wm_impl.
    Proof.
      intros sdm sdm' rf_spec rf_after rf_impl wm0 wm_after wm_impl req reqs Hrq HnotRq Hrel Hgl.
      destruct (DataMemInFlightRel_LoadRq_inv sdm rf_spec rf_after wm0 wm_after Hrq Hrel) as [-> ->].
      destruct (GhostList_cons_inv rf_spec wm0 req reqs rf_impl wm_impl Hgl)
        as [rf_after' [wm_after' [Hstep Hrest]]].
      exists rf_after', wm_after'; split; [exact Hstep | split; [| exact Hrest]].
      unfold DataMemInFlightRel; rewrite HnotRq; exists req; exact Hstep.
    Qed.

  End DataMemInFlightLemmas.

  (* --- 4C. Commutation of `updGpr`, `writeGprVal`, and `flushMulDivCaps` with `GhostStep` and `GhostList` --- *)

  Local Transparent updGpr.
  Local Strategy 0 [updGpr].
  Theorem GhostStep_updGpr :
    forall wIdx wbVal rf0 rf1 wm0 wm1 req,
      wIdx <> Zmod.zero ->
      (Zmod.eqb (req.(Fst)) Zmod.zero = false -> wIdx <> req.(Fst)) ->
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep pcAddrInit
        (updGpr pcAddrInit wIdx wbVal rf0)
        (updGpr pcAddrInit wIdx wbVal rf1)
        wm0 wm1 req.
  Proof.
    intros wIdx wbVal rf0 rf1 wm0 wm1 req Hnz Hneq Hstep.
    pose proof (ghost_waitMask_step pcAddrInit rf0 rf1 wm0 wm1 req Hstep) as Hwm.
    destruct (ghost_rf_step pcAddrInit rf0 rf1 wm0 wm1 req Hstep)
      as [pcc [meip [mtip [aluOut [execOut [rf_mid [Hsem [Hrf1 [Hdm [Hdst Haddr]]]]]]]]]].
    constructor.
    - exact Hwm.
    - exists pcc, meip, mtip, aluOut, execOut, (updGpr pcAddrInit wIdx wbVal rf_mid).
      repeat split.
      + apply SemAction_executeNonDeferred_updGpr; [| exact Hsem].
        unfold ghost_dstIdx in Hdst; rewrite Hdst; exact Hneq.
      + rewrite Hrf1.
        change (evalWriteRegsList (gprPathsWithKind pcAddrInit)) with (updGpr pcAddrInit).
        apply updGpr_comm; exact (not_eq_sym Hnz).
      + exact Hdm.
      + exact Hdst.
      + exact Haddr.
  Qed.
  Local Opaque updGpr.
  Local Strategy opaque [updGpr].

  Theorem GhostStep_writeGprVal :
    forall wIdx wbVal rf0 rf1 wm0 wm1 req,
      (Zmod.eqb wIdx Zmod.zero = false ->
       Zmod.eqb (req.(Fst)) Zmod.zero = false ->
       wIdx <> req.(Fst)) ->
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep pcAddrInit
        (writeGprVal pcAddrInit wIdx wbVal rf0)
        (writeGprVal pcAddrInit wIdx wbVal rf1)
        wm0 wm1 req.
  Proof.
    intros wIdx wbVal rf0 rf1 wm0 wm1 req Hneq Hstep.
    rewrite (writeGprVal_unfold pcAddrInit wIdx wbVal rf0),
            (writeGprVal_unfold pcAddrInit wIdx wbVal rf1).
    destruct (Zmod.eqb wIdx Zmod.zero) eqn:Hz; cbn [negb].
    - exact Hstep.
    - apply GhostStep_updGpr; [| exact (Hneq eq_refl) | exact Hstep].
      intros Heq; subst wIdx; rewrite Zmod.eqb_refl in Hz; discriminate Hz.
  Qed.

  Theorem GhostStep_flushMulDivCaps :
    forall entries rf0 rf1 wm0 wm1 req,
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         dstIdx <> req.(Fst)) ->
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep pcAddrInit
        (flushMulDivCaps pcAddrInit entries rf0)
        (flushMulDivCaps pcAddrInit entries rf1)
        wm0 wm1 req.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf0 rf1 wm0 wm1 req Hneq Hstep; cbn [flushMulDivCaps].
    - exact Hstep.
    - apply IH.
      + intros d r Hin Hz Hreq; exact (Hneq d r (or_intror Hin) Hz Hreq).
      + apply GhostStep_writeGprVal; [| exact Hstep].
        intros Hz Hreq; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz Hreq).
  Qed.

  Theorem GhostList_updGpr :
    forall wIdx wbVal rf0 wm0 reqs rf2 wm2,
      wIdx <> Zmod.zero ->
      (forall req,
         In req reqs ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         wIdx <> req.(Fst)) ->
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList pcAddrInit
        (updGpr pcAddrInit wIdx wbVal rf0) wm0
        reqs
        (updGpr pcAddrInit wIdx wbVal rf2) wm2.
  Proof.
    intros wIdx wbVal rf0 wm0 reqs rf2 wm2 Hnz Hneq Hgl.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH].
    - apply GhostNil.
    - eapply GhostCons.
      + apply GhostStep_updGpr; [exact Hnz | exact (Hneq req (or_introl eq_refl)) | exact Hstep].
      + apply IH; intros r Hin; exact (Hneq r (or_intror Hin)).
  Qed.

  Definition GhostList_write_waitReg := GhostList_updGpr.

  Theorem GhostList_writeGprVal :
    forall wIdx wbVal rf0 wm0 reqs rf2 wm2,
      (forall req,
         In req reqs ->
         Zmod.eqb wIdx Zmod.zero = false ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         wIdx <> req.(Fst)) ->
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList pcAddrInit
        (writeGprVal pcAddrInit wIdx wbVal rf0) wm0
        reqs
        (writeGprVal pcAddrInit wIdx wbVal rf2) wm2.
  Proof.
    intros wIdx wbVal rf0 wm0 reqs rf2 wm2 Hneq Hgl.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH].
    - apply GhostNil.
    - eapply GhostCons.
      + apply GhostStep_writeGprVal; [exact (Hneq req (or_introl eq_refl)) | exact Hstep].
      + apply IH; intros r Hin; exact (Hneq r (or_intror Hin)).
  Qed.

  Theorem GhostList_writeGprVal_waitMask :
    forall wIdx wbVal rf0 wm0 reqs rf2 wm2 wm0',
      (forall req,
         In req reqs ->
         Zmod.eqb wIdx Zmod.zero = false ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         wIdx <> req.(Fst)) ->
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList pcAddrInit
        (writeGprVal pcAddrInit wIdx wbVal rf0) wm0'
        reqs
        (writeGprVal pcAddrInit wIdx wbVal rf2) (foldWaitMask reqs wm0').
  Proof.
    intros wIdx wbVal rf0 wm0 reqs rf2 wm2 wm0' Hneq Hgl.
    eapply GhostList_change_waitMask.
    apply GhostList_writeGprVal; [exact Hneq | exact Hgl].
  Qed.

  Theorem GhostList_flushMulDivCaps :
    forall entries rf0 wm0 reqs rf2 wm2,
      (forall dstIdx resCap req,
         In (dstIdx, resCap) entries ->
         In req reqs ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (req.(Fst)) Zmod.zero = false ->
         dstIdx <> req.(Fst)) ->
      GhostList pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList pcAddrInit
        (flushMulDivCaps pcAddrInit entries rf0) wm0
        reqs
        (flushMulDivCaps pcAddrInit entries rf2) wm2.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf0 wm0 reqs rf2 wm2 Hneq Hgl; cbn [flushMulDivCaps].
    - exact Hgl.
    - apply IH.
      + intros d r req Hin Hreq; exact (Hneq d r req (or_intror Hin) Hreq).
      + apply GhostList_writeGprVal; [| exact Hgl].
        intros req Hreq; exact (Hneq dstIdx resCap req (or_introl eq_refl) Hreq).
  Qed.

  (* ===========================================================================
   * 8. `GhostStepOpt`, `GhostListOpt`, AND `DataMemInFlightCmdRel` LEMMAS
   * =========================================================================== *)

  Lemma GhostStepOpt_Some_of_GhostStep :
    forall rf0 rf1 wm0 wm1 req,
      wm0 (req.(Fst)) = false ->
      GhostStep pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStepOpt pcAddrInit rf0 rf1 wm0 wm1 (Some req).
  Proof.
    intros rf0 rf1 wm0 wm1 req Hni Hstep.
    constructor; [intros _; exact Hni | exact Hstep].
  Qed.

  Lemma GhostListOpt_app :
    forall rf0 wm0 reqs1 rf1 wm1 reqs2 rf2 wm2,
      GhostListOpt pcAddrInit rf0 wm0 reqs1 rf1 wm1 ->
      GhostListOpt pcAddrInit rf1 wm1 reqs2 rf2 wm2 ->
      GhostListOpt pcAddrInit rf0 wm0 (reqs1 ++ reqs2) rf2 wm2.
  Proof.
    intros rf0 wm0 reqs1 rf1 wm1 reqs2 rf2 wm2 H1 H2.
    induction H1 as [rf wm | r0 r1 r2 w0 w1 w2 [req |] reqs Hstep Hrest IH]; cbn [app].
    - exact H2.
    - eapply (GhostOptCons _ _ _ _ _ _ _ (Some req)); [exact Hstep | exact (IH H2)].
    - eapply (GhostOptCons _ _ _ _ _ _ _ None); [exact Hstep | exact (IH H2)].
  Qed.

  Lemma GhostListOpt_snoc_Some :
    forall rf0 wm0 reqs rf1 wm1 req rf2 wm2,
      GhostListOpt pcAddrInit rf0 wm0 reqs rf1 wm1 ->
      GhostStepOpt pcAddrInit rf1 rf2 wm1 wm2 (Some req) ->
      GhostListOpt pcAddrInit rf0 wm0 (reqs ++ [req]) rf2 wm2.
  Proof.
    intros rf0 wm0 reqs rf1 wm1 req rf2 wm2 Hgl Hstep.
    eapply GhostListOpt_app; [exact Hgl |].
    eapply (GhostOptCons _ _ _ _ _ _ _ (Some req)); [exact Hstep | apply GhostOptNil].
  Qed.

  Lemma GhostListOpt_snoc_None :
    forall rf0 wm0 reqs rf1 wm1 rf2 wm2,
      GhostListOpt pcAddrInit rf0 wm0 reqs rf1 wm1 ->
      GhostStepOpt pcAddrInit rf1 rf2 wm1 wm2 None ->
      GhostListOpt pcAddrInit rf0 wm0 reqs rf2 wm2.
  Proof.
    intros rf0 wm0 reqs rf1 wm1 rf2 wm2 Hgl Hstep.
    rewrite <- (app_nil_r reqs).
    eapply GhostListOpt_app; [exact Hgl |].
    eapply (GhostOptCons _ _ _ _ _ _ _ None); [exact Hstep | apply GhostOptNil].
  Qed.

  Lemma DataMemInFlightCmdRel_LoadRq :
    forall (dataMemCapacity : nat) (sdm : DataMemSubState dataMemCapacity)
           (req : type MemFenceReq),
      isDataMemLoadRq dataMemCapacity sdm = true ->
      DataMemInFlightCmdRel dataMemCapacity sdm req.
  Proof.
    intros dataMemCapacity sdm req Hrq.
    unfold DataMemInFlightCmdRel, isDataMemLoadRq in *.
    cbn [evalExpr isEq] in Hrq |- *.
    apply Zmod.eqb_eq in Hrq.
    rewrite Hrq; cbn; exact I.
  Qed.

End GhostListLemmas.
