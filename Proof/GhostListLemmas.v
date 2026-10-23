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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems ActionSim.
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
  Variable dom : string.
  Variable pcAddrInit : Z.

  Local Abbreviation rTree := (rfTree dom pcAddrInit).
  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind.

  Lemma ActionCommutes_readCsr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit CsrIdxSz)),
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (readRegsList (csrPathsWithKind dom pcAddrInit) idxExpr).
  Proof.
    intros wIdx wbVal idxExpr s P.
    rewrite !evalActionPropGen_readRegsList.
    change (evalReadRegsList (csrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (updGpr dom pcAddrInit wIdx wbVal s))
      with (readCsr dom pcAddrInit (evalExpr idxExpr) (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (csrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) s)
      with (readCsr dom pcAddrInit (evalExpr idxExpr) s).
    rewrite readCsr_updGpr.
    reflexivity.
  Qed.

  Lemma ActionCommutes_writeCsr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit CsrIdxSz)) (valExpr : Expr type (Bit Xlen)),
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (writeRegsList (csrPathsWithKind dom pcAddrInit) idxExpr valExpr).
  Proof.
    intros wIdx wbVal idxExpr valExpr s P.
    rewrite !evalActionPropGen_writeRegsList.
    change (evalWriteRegsList (csrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) (updGpr dom pcAddrInit wIdx wbVal s))
      with (updCsr dom pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalWriteRegsList (csrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) s)
      with (updCsr dom pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) s).
    rewrite updGpr_updCsr_comm.
    reflexivity.
  Qed.

  Lemma ActionCommutes_readScr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit ScrIdxSz)),
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (readRegsList (scrPathsWithKind dom pcAddrInit) idxExpr).
  Proof.
    intros wIdx wbVal idxExpr s P.
    rewrite !evalActionPropGen_readRegsList.
    change (evalReadRegsList (scrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (updGpr dom pcAddrInit wIdx wbVal s))
      with (readScr dom pcAddrInit (evalExpr idxExpr) (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (scrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) s)
      with (readScr dom pcAddrInit (evalExpr idxExpr) s).
    rewrite readScr_updGpr.
    reflexivity.
  Qed.

  Lemma ActionCommutes_writeScr_updGpr :
    forall wIdx wbVal (idxExpr : Expr type (Bit ScrIdxSz)) (valExpr : Expr type FullECapWithTag),
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (writeRegsList (scrPathsWithKind dom pcAddrInit) idxExpr valExpr).
  Proof.
    intros wIdx wbVal idxExpr valExpr s P.
    rewrite !evalActionPropGen_writeRegsList.
    change (evalWriteRegsList (scrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) (updGpr dom pcAddrInit wIdx wbVal s))
      with (updScr dom pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalWriteRegsList (scrPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) s)
      with (updScr dom pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) s).
    rewrite updGpr_updScr_comm.
    reflexivity.
  Qed.

  Lemma ActionCommutes_readGpr_updGpr_other :
    forall wIdx wbVal (idxExpr : Expr type (Bit RegIdxSzReal)),
      evalExpr idxExpr <> wIdx ->
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (readRegsList (gprPathsWithKind dom pcAddrInit) idxExpr).
  Proof.
    intros wIdx wbVal idxExpr Hneq s P.
    rewrite !evalActionPropGen_readRegsList.
    change (evalReadRegsList (gprPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (updGpr dom pcAddrInit wIdx wbVal s))
      with (readGpr dom pcAddrInit (evalExpr idxExpr) (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (gprPathsWithKind dom pcAddrInit) (evalExpr idxExpr) s)
      with (readGpr dom pcAddrInit (evalExpr idxExpr) s).
    rewrite readGpr_updGpr_other by exact Hneq.
    reflexivity.
  Qed.

  Lemma ActionCommutes_writeGpr_updGpr_other :
    forall wIdx wbVal (idxExpr : Expr type (Bit RegIdxSzReal)) (valExpr : Expr type FullECapWithTag),
      wIdx <> evalExpr idxExpr ->
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (writeRegsList (gprPathsWithKind dom pcAddrInit) idxExpr valExpr).
  Proof.
    intros wIdx wbVal idxExpr valExpr Hneq s P.
    rewrite !evalActionPropGen_writeRegsList.
    change (evalWriteRegsList (gprPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) (updGpr dom pcAddrInit wIdx wbVal s))
      with (updGpr dom pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalWriteRegsList (gprPathsWithKind dom pcAddrInit) (evalExpr idxExpr) (evalExpr valExpr) s)
      with (updGpr dom pcAddrInit (evalExpr idxExpr) (evalExpr valExpr) s).
    rewrite (updGpr_comm dom pcAddrInit wIdx (evalExpr idxExpr) wbVal (evalExpr valExpr) s Hneq).
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
      (forall v, ActionCommutes (updGpr dom pcAddrInit wIdx wbVal) (cont v)) ->
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (IfElse nm (isNotZero (Var type (Bit RegIdxSzReal) dstIdx))
                (writeRegsList (gprPathsWithKind dom pcAddrInit)
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@incrementMinstret dom pcAddrInit type).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@incrementMcycle dom pcAddrInit type).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@updateMshwmOnStore dom pcAddrInit type stAddr).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@isInterruptPending dom pcAddrInit type meip mtip).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@handleTrap dom pcAddrInit type currPcc newMcause newMtval).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@executeInterrupt dom pcAddrInit type currPcc meip mtip).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@executeSequential dom pcAddrInit type currPcc aluOut).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@executeNonSequential dom pcAddrInit type currPcc meip mtip aluOut).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut).
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
           (rf rf' : TreeState DomainElemState rTree) (res : bool),
      SemAction (@isInterruptPending dom pcAddrInit type meip mtip) rf rf' res ->
      SemAction (@isInterruptPending dom pcAddrInit type meip mtip)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
        res.
  Proof.
    intros wIdx wbVal meip mtip rf rf' res Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_isInterruptPending_updGpr.
    - exact Hsem.
  Qed.

  Theorem SemAction_handleTrap_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (mcauseVal mtvalVal : type (Bit Xlen))
           (rf rf' : TreeState DomainElemState rTree) (execOut : type ExecuteOut),
      SemAction (@handleTrap dom pcAddrInit type currPcc mcauseVal mtvalVal) rf rf' execOut ->
      SemAction (@handleTrap dom pcAddrInit type currPcc mcauseVal mtvalVal)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc mcauseVal mtvalVal rf rf' execOut Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_handleTrap_updGpr.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeInterrupt_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool)
           (rf rf' : TreeState DomainElemState rTree) (execOut : type ExecuteOut),
      SemAction (@executeInterrupt dom pcAddrInit type currPcc meip mtip) rf rf' execOut ->
      SemAction (@executeInterrupt dom pcAddrInit type currPcc meip mtip)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc meip mtip rf rf' execOut Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeInterrupt_updGpr.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeSequential_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (aluOut : type AluOutUnion)
           (rf rf' : TreeState DomainElemState rTree) (mulDivOpt : type (Option MulDivUnion)),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeSequential dom pcAddrInit type currPcc aluOut) rf rf' mulDivOpt ->
      SemAction (@executeSequential dom pcAddrInit type currPcc aluOut)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
        mulDivOpt.
  Proof.
    intros wIdx wbVal currPcc aluOut rf rf' mulDivOpt Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeSequential_updGpr; exact Hdst.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeNonSequential_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : TreeState DomainElemState rTree)
           (execOut : type ExecuteOut),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeNonSequential dom pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonSequential dom pcAddrInit type currPcc meip mtip aluOut)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
        execOut.
  Proof.
    intros wIdx wbVal currPcc meip mtip aluOut rf rf' execOut Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeNonSequential_updGpr; exact Hdst.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeNonDeferred_updGpr :
    forall wIdx wbVal (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : TreeState DomainElemState rTree)
           (execOut : type ExecuteOut),
      (Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false -> wIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@executeNonSequential dom pcAddrInit type currPcc meip mtip aluOut).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut).
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
      (forall cs, ActionCommutes (updGpr dom pcAddrInit wIdx wbVal) (cont cs)) ->
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (LetAction nm1 (readRegsList (gprPathsWithKind dom pcAddrInit) (Var type (Bit RegIdxSzReal) idx))
          (fun csRaw =>
             LetExp nm2 (ITE0 (isNotZero (Var type (Bit RegIdxSzReal) idx)) (Var type FullECapWithTag csRaw))
               cont)).
  Proof.
    intros wIdx wbVal nm1 nm2 idx cont Hidx Hcont s P.
    cbn [evalActionPropGen].
    rewrite !evalActionPropGen_readRegsList.
    cbn [evalActionPropGen].
    change (evalExpr (Var type (Bit RegIdxSzReal) idx)) with idx.
    change (evalReadRegsList (gprPathsWithKind dom pcAddrInit) idx (updGpr dom pcAddrInit wIdx wbVal s))
      with (readGpr dom pcAddrInit idx (updGpr dom pcAddrInit wIdx wbVal s)).
    change (evalReadRegsList (gprPathsWithKind dom pcAddrInit) idx s)
      with (readGpr dom pcAddrInit idx s).
    unfold ITE0.
    erewrite (evalExpr_ITE_ext (isNotZero (Var type (Bit RegIdxSzReal) idx))
                (Var type FullECapWithTag (readGpr dom pcAddrInit idx (updGpr dom pcAddrInit wIdx wbVal s)))
                (Var type FullECapWithTag (readGpr dom pcAddrInit idx s))).
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
      ActionCommutes (updGpr dom pcAddrInit wIdx wbVal)
        (@regRead dom pcAddrInit type regReadIn).
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
           (rf rf' : TreeState DomainElemState rTree) (out : type AluInInstGroup),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb cs1Idx Zmod.zero = false -> cs1Idx <> wIdx) ->
      (Zmod.eqb cs2Idx Zmod.zero = false -> cs2Idx <> wIdx) ->
      SemAction (@regRead dom pcAddrInit type regReadIn) rf rf' out ->
      SemAction (@regRead dom pcAddrInit type regReadIn)
        (updGpr dom pcAddrInit wIdx wbVal rf)
        (updGpr dom pcAddrInit wIdx wbVal rf')
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
  Variable core : string.
  Variable pcAddrInit : Z.

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind
               evalWriteRegsList evalReadRegsList.
  Local Strategy opaque [evalWriteRegsList evalReadRegsList DomainElemState gprPathsWithKind scrPathsWithKind csrPathsWithKind].

  Lemma writeGprVal_unfold :
    forall dstIdx val (rf : RfState core pcAddrInit),
      writeGprVal core pcAddrInit dstIdx val rf =
      if negb (Zmod.eqb dstIdx Zmod.zero)
      then updGpr core pcAddrInit dstIdx val rf
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
    forall dstIdx val (rf : RfState core pcAddrInit),
      Zmod.eqb dstIdx Zmod.zero = true ->
      writeGprVal core pcAddrInit dstIdx val rf = rf.
  Proof.
    intros dstIdx val rf Hz.
    rewrite writeGprVal_unfold, Hz; reflexivity.
  Qed.

  Lemma writeGprVal_zero_literal :
    forall val (rf : RfState core pcAddrInit),
      writeGprVal core pcAddrInit Zmod.zero val rf = rf.
  Proof.
    intros val rf.
    apply writeGprVal_zero.
    apply Zmod.eqb_refl.
  Qed.

  Lemma writeGprVal_nonzero :
    forall dstIdx val (rf : RfState core pcAddrInit),
      Zmod.eqb dstIdx Zmod.zero = false ->
      writeGprVal core pcAddrInit dstIdx val rf = updGpr core pcAddrInit dstIdx val rf.
  Proof.
    intros dstIdx val rf Hnz.
    rewrite writeGprVal_unfold, Hnz; reflexivity.
  Qed.

  Lemma writeGprVal_Snd :
    forall dstIdx val (rf : RfState core pcAddrInit),
      (writeGprVal core pcAddrInit dstIdx val rf).(Snd) = rf.(Snd).
  Proof.
    intros dstIdx val rf.
    rewrite writeGprVal_unfold.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply updGpr_Snd | reflexivity].
  Qed.

  Local Strategy opaque [rfTree TreeState].

  Lemma readScr_writeGprVal :
    forall sIdx dstIdx val (rf : RfState core pcAddrInit),
      readScr core pcAddrInit sIdx (writeGprVal core pcAddrInit dstIdx val rf) =
      readScr core pcAddrInit sIdx rf.
  Proof.
    intros sIdx dstIdx val rf.
    rewrite writeGprVal_unfold.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply readScr_updGpr | reflexivity].
  Qed.

  Lemma readCsr_writeGprVal :
    forall cIdx dstIdx val (rf : RfState core pcAddrInit),
      readCsr core pcAddrInit cIdx (writeGprVal core pcAddrInit dstIdx val rf) =
      readCsr core pcAddrInit cIdx rf.
  Proof.
    intros cIdx dstIdx val rf.
    rewrite writeGprVal_unfold.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply readCsr_updGpr | reflexivity].
  Qed.

  Lemma readGpr_writeGprVal_other :
    forall rIdx dstIdx val (rf : RfState core pcAddrInit),
      (Zmod.eqb dstIdx Zmod.zero = false -> rIdx <> dstIdx) ->
      readGpr core pcAddrInit rIdx (writeGprVal core pcAddrInit dstIdx val rf) =
      readGpr core pcAddrInit rIdx rf.
  Proof.
    intros rIdx dstIdx val rf Hneq.
    rewrite writeGprVal_unfold.
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hz; cbn [negb].
    - reflexivity.
    - apply readGpr_updGpr_other; exact (Hneq eq_refl).
  Qed.

  Lemma readGpr_zero_writeGprVal :
    forall dstIdx val (rf : RfState core pcAddrInit),
      readGpr core pcAddrInit Zmod.zero (writeGprVal core pcAddrInit dstIdx val rf) =
      readGpr core pcAddrInit Zmod.zero rf.
  Proof.
    intros dstIdx val rf.
    apply readGpr_writeGprVal_other.
    intros Hz Heq; subst dstIdx.
    rewrite Zmod.eqb_refl in Hz; discriminate Hz.
  Qed.

  Local Transparent RfTree RfState writeGprVal updGpr.

  Lemma writeGprVal_comm :
    forall idx1 val1 idx2 val2 (rf : RfState core pcAddrInit),
      (Zmod.eqb idx1 Zmod.zero = false -> Zmod.eqb idx2 Zmod.zero = false -> idx1 <> idx2) ->
      writeGprVal core pcAddrInit idx1 val1 (writeGprVal core pcAddrInit idx2 val2 rf) =
      writeGprVal core pcAddrInit idx2 val2 (writeGprVal core pcAddrInit idx1 val1 rf).
  Proof.
    intros idx1 val1 idx2 val2 rf Hneq.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind core pcAddrInit)) with (updGpr core pcAddrInit).
    destruct (Zmod.eqb idx1 Zmod.zero) eqn:Hz1;
      destruct (Zmod.eqb idx2 Zmod.zero) eqn:Hz2; cbn [negb]; try reflexivity.
    apply updGpr_comm; exact (not_eq_sym (Hneq eq_refl eq_refl)).
  Qed.

  Lemma writeGprVal_updGpr_other_comm :
    forall dstIdx val wIdx wVal (rf : RfState core pcAddrInit),
      (Zmod.eqb dstIdx Zmod.zero = false -> dstIdx <> wIdx) ->
      writeGprVal core pcAddrInit dstIdx val (updGpr core pcAddrInit wIdx wVal rf) =
      updGpr core pcAddrInit wIdx wVal (writeGprVal core pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val wIdx wVal rf Hneq.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind core pcAddrInit)) with (updGpr core pcAddrInit).
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hz; cbn [negb].
    - reflexivity.
    - apply updGpr_comm; exact (not_eq_sym (Hneq eq_refl)).
  Qed.

  Lemma writeGprVal_updGpr_zero_comm :
    forall dstIdx val pccVal (rf : RfState core pcAddrInit),
      writeGprVal core pcAddrInit dstIdx val (updGpr core pcAddrInit Zmod.zero pccVal rf) =
      updGpr core pcAddrInit Zmod.zero pccVal (writeGprVal core pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val pccVal rf.
    apply writeGprVal_updGpr_other_comm.
    intros Hz Heq; subst dstIdx.
    rewrite Zmod.eqb_refl in Hz; discriminate Hz.
  Qed.

  Lemma writeGprVal_updScr_comm :
    forall dstIdx val sIdx sVal (rf : RfState core pcAddrInit),
      writeGprVal core pcAddrInit dstIdx val (updScr core pcAddrInit sIdx sVal rf) =
      updScr core pcAddrInit sIdx sVal (writeGprVal core pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val sIdx sVal rf.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind core pcAddrInit)) with (updGpr core pcAddrInit).
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply updGpr_updScr_comm | reflexivity].
  Qed.

  Lemma writeGprVal_updCsr_comm :
    forall dstIdx val cIdx cVal (rf : RfState core pcAddrInit),
      writeGprVal core pcAddrInit dstIdx val (updCsr core pcAddrInit cIdx cVal rf) =
      updCsr core pcAddrInit cIdx cVal (writeGprVal core pcAddrInit dstIdx val rf).
  Proof.
    intros dstIdx val cIdx cVal rf.
    unfold writeGprVal.
    change (evalWriteRegsList (gprPathsWithKind core pcAddrInit)) with (updGpr core pcAddrInit).
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); [apply updGpr_updCsr_comm | reflexivity].
  Qed.

  Lemma ActionCommutes_writeGprVal {k : Kind} :
    forall dstIdx val (act : Action type (RfTree core pcAddrInit) k),
      (Zmod.eqb dstIdx Zmod.zero = false ->
       ActionCommutes (updGpr core pcAddrInit dstIdx val) act) ->
      ActionCommutes (writeGprVal core pcAddrInit dstIdx val) act.
  Proof.
    intros dstIdx val act Hcomm s P.
    unfold writeGprVal, updGpr in *.
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hz; cbn [negb].
    - split; intros H; exact H.
    - exact (Hcomm eq_refl s P).
  Qed.
  Local Opaque writeGprVal updGpr.
  Local Strategy opaque [writeGprVal updGpr readGpr updScr readScr updCsr readCsr].

  Theorem ActionCommutes_executeNonDeferred_writeGprVal :
    forall dstIdx val (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion),
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
       dstIdx <> aluOut.(Snd).(Fst)) ->
      ActionCommutes (writeGprVal core pcAddrInit dstIdx val)
        (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut).
  Proof.
    intros dstIdx val currPcc meip mtip aluOut Hdst.
    apply ActionCommutes_writeGprVal; intros Hz.
    apply ActionCommutes_executeNonDeferred_updGpr; exact (Hdst Hz).
  Qed.

  Theorem SemAction_executeNonDeferred_writeGprVal :
    forall dstIdx val (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : RfState core pcAddrInit)
           (execOut : type ExecuteOut),
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
       dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut)
        (writeGprVal core pcAddrInit dstIdx val rf)
        (writeGprVal core pcAddrInit dstIdx val rf')
        execOut.
  Proof.
    intros dstIdx val currPcc meip mtip aluOut rf rf' execOut Hdst Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_executeNonDeferred_writeGprVal; exact Hdst.
    - exact Hsem.
  Qed.

  Theorem SemAction_executeNonDeferred_DataMem_writeGprVal :
    forall dstIdx val (currPcc : type FullECapWithTag) (meip mtip : bool)
           (aluOut : type AluOutUnion) (rf rf' : RfState core pcAddrInit)
           (execOut : type ExecuteOut),
      let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
      let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
      let noExcOp : type NoExceptionUnion := evalExpr (#nonSeqOp `! "NoException") in
      evalExpr (#aluOp `? "Sequential") = false ->
      evalExpr (#noExcOp `? "DataMem") = true ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut)
        (writeGprVal core pcAddrInit dstIdx val rf)
        (writeGprVal core pcAddrInit dstIdx val rf')
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
      ActionCommutes (writeGprVal core pcAddrInit dstIdx val)
        (@regRead core pcAddrInit type regReadIn).
  Proof.
    intros dstIdx val regReadIn decodeOut cs1Idx cs2Idx Hcs1 Hcs2.
    apply ActionCommutes_writeGprVal; intros Hz.
    apply ActionCommutes_regRead_updGpr; [exact (Hcs1 Hz) | exact (Hcs2 Hz)].
  Qed.

  Theorem SemAction_regRead_writeGprVal :
    forall dstIdx val (regReadIn : type RegReadIn)
           (rf rf' : RfState core pcAddrInit) (out : type AluInInstGroup),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : bits RegIdxSzReal := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb dstIdx Zmod.zero = false -> Zmod.eqb cs1Idx Zmod.zero = false -> cs1Idx <> dstIdx) ->
      (Zmod.eqb dstIdx Zmod.zero = false -> Zmod.eqb cs2Idx Zmod.zero = false -> cs2Idx <> dstIdx) ->
      SemAction (@regRead core pcAddrInit type regReadIn) rf rf' out ->
      SemAction (@regRead core pcAddrInit type regReadIn)
        (writeGprVal core pcAddrInit dstIdx val rf)
        (writeGprVal core pcAddrInit dstIdx val rf')
        out.
  Proof.
    intros dstIdx val regReadIn rf rf' out decodeOut cs1Idx cs2Idx Hcs1 Hcs2 Hsem.
    eapply ActionCommutes_SemAction.
    - apply ActionCommutes_regRead_writeGprVal; [exact Hcs1 | exact Hcs2].
    - exact Hsem.
  Qed.

  (* --- `flushMulDivCaps` Structural and Commutation Lemmas --- *)

  Lemma flushMulDivCaps_nil :
    forall (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit [] rf = rf.
  Proof.
    intros rf; reflexivity.
  Qed.

  Lemma flushMulDivCaps_cons :
    forall dstIdx resCap rest (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit ((dstIdx, resCap) :: rest) rf =
      flushMulDivCaps core pcAddrInit rest (writeGprVal core pcAddrInit dstIdx resCap rf).
  Proof.
    intros dstIdx resCap rest rf; reflexivity.
  Qed.

  Lemma flushMulDivCaps_app :
    forall (l1 l2 : list (bits RegIdxSzReal * type FullECapWithTag))
           (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit (l1 ++ l2)%list rf =
      flushMulDivCaps core pcAddrInit l2 (flushMulDivCaps core pcAddrInit l1 rf).
  Proof.
    induction l1 as [| [dstIdx resCap] rest IH]; intros l2 rf; cbn [flushMulDivCaps app].
    - reflexivity.
    - apply IH.
  Qed.

  Lemma flushMulDivCaps_snoc :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           dstIdx resCap (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit (entries ++ [(dstIdx, resCap)])%list rf =
      writeGprVal core pcAddrInit dstIdx resCap (flushMulDivCaps core pcAddrInit entries rf).
  Proof.
    intros entries dstIdx resCap rf.
    rewrite flushMulDivCaps_app; reflexivity.
  Qed.

  Local Strategy 0 [rfTree TreeState].
  Lemma flushMulDivCaps_Snd :
    forall entries (rf : RfState core pcAddrInit),
      (flushMulDivCaps core pcAddrInit entries rf).(Snd) = rf.(Snd).
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply writeGprVal_Snd.
  Qed.
  Local Strategy opaque [rfTree TreeState].

  Lemma readScr_flushMulDivCaps :
    forall sIdx entries (rf : RfState core pcAddrInit),
      readScr core pcAddrInit sIdx (flushMulDivCaps core pcAddrInit entries rf) =
      readScr core pcAddrInit sIdx rf.
  Proof.
    intros sIdx entries; induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply readScr_writeGprVal.
  Qed.

  Lemma readCsr_flushMulDivCaps :
    forall cIdx entries (rf : RfState core pcAddrInit),
      readCsr core pcAddrInit cIdx (flushMulDivCaps core pcAddrInit entries rf) =
      readCsr core pcAddrInit cIdx rf.
  Proof.
    intros cIdx entries; induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply readCsr_writeGprVal.
  Qed.

  Lemma readGpr_zero_flushMulDivCaps :
    forall entries (rf : RfState core pcAddrInit),
      readGpr core pcAddrInit Zmod.zero (flushMulDivCaps core pcAddrInit entries rf) =
      readGpr core pcAddrInit Zmod.zero rf.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH; apply readGpr_zero_writeGprVal.
  Qed.

  Lemma readGpr_flushMulDivCaps_other :
    forall rIdx entries (rf : RfState core pcAddrInit),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         rIdx <> dstIdx) ->
      readGpr core pcAddrInit rIdx (flushMulDivCaps core pcAddrInit entries rf) =
      readGpr core pcAddrInit rIdx rf.
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
    forall sIdx sVal entries (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit entries (updScr core pcAddrInit sIdx sVal rf) =
      updScr core pcAddrInit sIdx sVal (flushMulDivCaps core pcAddrInit entries rf).
  Proof.
    intros sIdx sVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updScr core pcAddrInit sIdx sVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updScr_comm dstIdx resCap sIdx sVal rf).
      apply IH.
  Qed.

  Lemma updCsr_flushMulDivCaps_comm :
    forall cIdx cVal entries (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit entries (updCsr core pcAddrInit cIdx cVal rf) =
      updCsr core pcAddrInit cIdx cVal (flushMulDivCaps core pcAddrInit entries rf).
  Proof.
    intros cIdx cVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updCsr core pcAddrInit cIdx cVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updCsr_comm dstIdx resCap cIdx cVal rf).
      apply IH.
  Qed.

  Lemma updGpr_zero_flushMulDivCaps_comm :
    forall pccVal entries (rf : RfState core pcAddrInit),
      flushMulDivCaps core pcAddrInit entries (updGpr core pcAddrInit Zmod.zero pccVal rf) =
      updGpr core pcAddrInit Zmod.zero pccVal (flushMulDivCaps core pcAddrInit entries rf).
  Proof.
    intros pccVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updGpr core pcAddrInit Zmod.zero pccVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updGpr_zero_comm dstIdx resCap pccVal rf).
      apply IH.
  Qed.

  Lemma updGpr_other_flushMulDivCaps_comm :
    forall wIdx wVal entries (rf : RfState core pcAddrInit),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         dstIdx <> wIdx) ->
      flushMulDivCaps core pcAddrInit entries (updGpr core pcAddrInit wIdx wVal rf) =
      updGpr core pcAddrInit wIdx wVal (flushMulDivCaps core pcAddrInit entries rf).
  Proof.
    intros wIdx wVal entries.
    induction entries as [| [dstIdx resCap] rest IH]; intros rf Hneq.
    - reflexivity.
    - rewrite (flushMulDivCaps_cons dstIdx resCap rest (updGpr core pcAddrInit wIdx wVal rf)),
              (flushMulDivCaps_cons dstIdx resCap rest rf).
      rewrite (writeGprVal_updGpr_other_comm dstIdx resCap wIdx wVal rf).
      + apply IH; intros d r Hin Hz; exact (Hneq d r (or_intror Hin) Hz).
      + intros Hz; exact (Hneq dstIdx resCap (or_introl eq_refl) Hz).
  Qed.

  Lemma writeGprVal_flushMulDivCaps_comm :
    forall wIdx wVal entries (rf : RfState core pcAddrInit),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb wIdx Zmod.zero = false ->
         dstIdx <> wIdx) ->
      flushMulDivCaps core pcAddrInit entries (writeGprVal core pcAddrInit wIdx wVal rf) =
      writeGprVal core pcAddrInit wIdx wVal (flushMulDivCaps core pcAddrInit entries rf).
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
           (rf rf' : RfState core pcAddrInit) (res : bool),
      SemAction (@isInterruptPending core pcAddrInit type meip mtip) rf rf' res ->
      SemAction (@isInterruptPending core pcAddrInit type meip mtip)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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
           (rf rf' : RfState core pcAddrInit) (execOut : type ExecuteOut),
      SemAction (@executeInterrupt core pcAddrInit type currPcc meip mtip) rf rf' execOut ->
      SemAction (@executeInterrupt core pcAddrInit type currPcc meip mtip)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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
           (rf rf' : RfState core pcAddrInit) (mulDivOpt : type (Option MulDivUnion)),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
         dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeSequential core pcAddrInit type currPcc aluOut) rf rf' mulDivOpt ->
      SemAction (@executeSequential core pcAddrInit type currPcc aluOut)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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
           (rf rf' : RfState core pcAddrInit) (execOut : type ExecuteOut),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
         dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeNonSequential core pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonSequential core pcAddrInit type currPcc meip mtip aluOut)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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
           (rf rf' : RfState core pcAddrInit) (execOut : type ExecuteOut),
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb (aluOut.(Snd).(Fst)) Zmod.zero = false ->
         dstIdx <> aluOut.(Snd).(Fst)) ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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
           (rf rf' : RfState core pcAddrInit) (execOut : type ExecuteOut),
      let aluOp : type AluOpUnion := evalExpr (##aluOut`"Op") in
      let nonSeqOp : type NonSequentialUnion := evalExpr (#aluOp `! "NonSequential") in
      let noExcOp : type NoExceptionUnion := evalExpr (#nonSeqOp `! "NoException") in
      evalExpr (#aluOp `? "Sequential") = false ->
      evalExpr (#noExcOp `? "DataMem") = true ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut) rf rf' execOut ->
      SemAction (@executeNonDeferred core pcAddrInit type currPcc meip mtip aluOut)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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
           (rf rf' : RfState core pcAddrInit) (out : type AluInInstGroup),
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
      SemAction (@regRead core pcAddrInit type regReadIn) rf rf' out ->
      SemAction (@regRead core pcAddrInit type regReadIn)
        (flushMulDivCaps core pcAddrInit entries rf)
        (flushMulDivCaps core pcAddrInit entries rf')
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

    Local Opaque MulDivSubState extractMulDivEntries.
    Local Strategy opaque [MulDivSubState extractMulDivEntries].

    Lemma flushMulDivOn_preserve :
      forall (rf : RfState core pcAddrInit)
             (smd smd' : MulDivSubState core mulCapacity divCapacity mulStages divStages mulDivMode),
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode smd' =
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode smd ->
        flushMulDivOn core pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd' =
        flushMulDivOn core pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd.
    Proof.
      intros rf smd smd' Heq.
      unfold flushMulDivOn; rewrite Heq; reflexivity.
    Qed.

    Lemma flushMulDivOn_wb_pop :
      forall dstIdx resCap (rf : RfState core pcAddrInit)
             (smd smd' : MulDivSubState core mulCapacity divCapacity mulStages divStages mulDivMode),
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode smd =
        (dstIdx, resCap) :: extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode smd' ->
        flushMulDivOn core pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode
          (writeGprVal core pcAddrInit dstIdx resCap rf) smd' =
        flushMulDivOn core pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd.
    Proof.
      intros dstIdx resCap rf smd smd' Hpop.
      unfold flushMulDivOn; rewrite Hpop; reflexivity.
    Qed.

    Lemma flushMulDivOn_enq :
      forall dstIdx resCap (rf : RfState core pcAddrInit)
             (smd smd' : MulDivSubState core mulCapacity divCapacity mulStages divStages mulDivMode),
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode smd' =
        (extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode smd ++ [(dstIdx, resCap)])%list ->
        flushMulDivOn core pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd' =
        writeGprVal core pcAddrInit dstIdx resCap
          (flushMulDivOn core pcAddrInit mulCapacity divCapacity mulStages divStages mulDivMode rf smd).
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
  Variable core : string.
  Variable pcAddrInit : Z.

  Local Opaque rfTree TreeState getDefault
               gprPathsWithKind scrPathsWithKind csrPathsWithKind
               evalWriteRegsList evalReadRegsList
               updGpr readGpr updScr readScr updCsr readCsr writeGprVal
               evalActionPropGen executeNonDeferred.
  Local Strategy opaque [rfTree TreeState DomainElemState gprPathsWithKind scrPathsWithKind csrPathsWithKind
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
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      wm1 = stepWaitMask req wm0.
  Proof.
    intros rf0 rf1 wm0 wm1 req Hstep.
    exact (ghost_waitMask_step core pcAddrInit rf0 rf1 wm0 wm1 req Hstep).
  Qed.

  Lemma GhostList_waitMask_det :
    forall rf0 wm0 reqs rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      wm2 = foldWaitMask reqs wm0.
  Proof.
    intros rf0 wm0 reqs rf2 wm2 Hgl.
    induction Hgl as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH]; cbn [foldWaitMask].
    - reflexivity.
    - rewrite IH, (GhostStep_waitMask_det rf0 rf1 wm0 wm1 req Hstep); reflexivity.
  Qed.

  Lemma GhostStep_change_waitMask :
    forall rf0 rf1 wm0 wm1 req wm0',
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep core pcAddrInit rf0 rf1 wm0' (stepWaitMask req wm0') req.
  Proof.
    intros rf0 rf1 wm0 wm1 req wm0' Hstep.
    constructor.
    - reflexivity.
    - exact (ghost_rf_step core pcAddrInit rf0 rf1 wm0 wm1 req Hstep).
  Qed.

  Lemma GhostList_change_waitMask :
    forall rf0 wm0 reqs rf2 wm2 wm0',
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList core pcAddrInit rf0 wm0' reqs rf2 (foldWaitMask reqs wm0').
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
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostList core pcAddrInit rf0 wm0 [req] rf1 wm1.
  Proof.
    intros rf0 rf1 wm0 wm1 req Hstep.
    eapply GhostCons; [exact Hstep | apply GhostNil].
  Qed.

  Theorem GhostList_app :
    forall rf0 wm0 l1 rf1 wm1 l2 rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 l1 rf1 wm1 ->
      GhostList core pcAddrInit rf1 wm1 l2 rf2 wm2 ->
      GhostList core pcAddrInit rf0 wm0 (l1 ++ l2)%list rf2 wm2.
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
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostStep core pcAddrInit rf2 rf3 wm2 wm3 req ->
      GhostList core pcAddrInit rf0 wm0 (reqs ++ [req])%list rf3 wm3.
  Proof.
    intros rf0 wm0 reqs rf2 wm2 rf3 wm3 req Hgl Hstep.
    eapply GhostList_app; [exact Hgl | apply GhostList_single; exact Hstep].
  Qed.

  Theorem GhostList_cons_inv :
    forall rf0 wm0 req reqs rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 (req :: reqs) rf2 wm2 ->
      exists rf1 wm1,
        GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req /\
        GhostList core pcAddrInit rf1 wm1 reqs rf2 wm2.
  Proof.
    intros rf0 wm0 req reqs rf2 wm2 Hgl.
    inversion Hgl; subst.
    eexists; eexists; split; eassumption.
  Qed.

  Definition GhostList_drain := GhostList_cons_inv.

  Theorem GhostList_app_inv :
    forall l1 l2 rf0 wm0 rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 (l1 ++ l2)%list rf2 wm2 ->
      exists rf1 wm1,
        GhostList core pcAddrInit rf0 wm0 l1 rf1 wm1 /\
        GhostList core pcAddrInit rf1 wm1 l2 rf2 wm2.
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
      GhostList core pcAddrInit rf0 wm0 (reqs ++ [req])%list rf3 wm3 ->
      exists rf2 wm2,
        GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 /\
        GhostStep core pcAddrInit rf2 rf3 wm2 wm3 req.
  Proof.
    intros reqs req rf0 wm0 rf3 wm3 Hgl.
    destruct (GhostList_app_inv reqs [req] rf0 wm0 rf3 wm3 Hgl)
      as [rf2 [wm2 [Hreqs Hsingle]]].
    destruct (GhostList_cons_inv rf2 wm2 req [] rf3 wm3 Hsingle)
      as [rf_end [wm_end [Hstep Hnil]]].
    destruct (GhostList_nil_inv core pcAddrInit rf_end wm_end rf3 wm3 Hnil) as [-> ->].
    exists rf2, wm2; split; [exact Hreqs | exact Hstep].
  Qed.

  Section DataMemInFlightLemmas.
    Variable dataMemCapacity : nat.

    Local Opaque DataMemSubState isDataMemLoadRq.
    Local Strategy opaque [DataMemSubState isDataMemLoadRq].

    Lemma DataMemInFlightRel_LoadRq_True :
      forall (sdm : DataMemSubState core dataMemCapacity)
             (rf_spec : RfState core pcAddrInit)
             (wm0 : bits RegIdxSzReal -> bool),
        isDataMemLoadRq core dataMemCapacity sdm = true ->
        DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_spec wm0 wm0.
    Proof.
      intros sdm rf_spec wm0 Hrq.
      unfold DataMemInFlightRel; rewrite Hrq; split; reflexivity.
    Qed.

    Lemma DataMemInFlightRel_LoadRq_inv :
      forall (sdm : DataMemSubState core dataMemCapacity)
             (rf_spec rf_after : RfState core pcAddrInit)
             (wm0 wm_after : bits RegIdxSzReal -> bool),
        isDataMemLoadRq core dataMemCapacity sdm = true ->
        DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
        rf_after = rf_spec /\ wm_after = wm0.
    Proof.
      intros sdm rf_spec rf_after wm0 wm_after Hrq Hrel.
      unfold DataMemInFlightRel in Hrel; rewrite Hrq in Hrel; exact Hrel.
    Qed.

    Lemma DataMemInFlightRel_NotLoadRq_inv :
      forall (sdm : DataMemSubState core dataMemCapacity)
             (rf_spec rf_after : RfState core pcAddrInit)
             (wm0 wm_after : bits RegIdxSzReal -> bool),
        isDataMemLoadRq core dataMemCapacity sdm = false ->
        DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
        exists req, GhostStep core pcAddrInit rf_spec rf_after wm0 wm_after req.
    Proof.
      intros sdm rf_spec rf_after wm0 wm_after Hrq Hrel.
      unfold DataMemInFlightRel in Hrel; rewrite Hrq in Hrel; exact Hrel.
    Qed.

    Theorem GhostList_drain_to_inflight :
      forall (sdm sdm' : DataMemSubState core dataMemCapacity)
             (rf_spec rf_after rf_impl : RfState core pcAddrInit)
             (wm0 wm_after wm_impl : bits RegIdxSzReal -> bool)
             (req : type MemFenceReq) (reqs : list (type MemFenceReq)),
        isDataMemLoadRq core dataMemCapacity sdm = true ->
        isDataMemLoadRq core dataMemCapacity sdm' = false ->
        DataMemInFlightRel core pcAddrInit dataMemCapacity sdm rf_spec rf_after wm0 wm_after ->
        GhostList core pcAddrInit rf_after wm_after (req :: reqs) rf_impl wm_impl ->
        exists rf_after' wm_after',
          GhostStep core pcAddrInit rf_spec rf_after' wm0 wm_after' req /\
          DataMemInFlightRel core pcAddrInit dataMemCapacity sdm' rf_spec rf_after' wm0 wm_after' /\
          GhostList core pcAddrInit rf_after' wm_after' reqs rf_impl wm_impl.
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
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep core pcAddrInit
        (updGpr core pcAddrInit wIdx wbVal rf0)
        (updGpr core pcAddrInit wIdx wbVal rf1)
        wm0 wm1 req.
  Proof.
    intros wIdx wbVal rf0 rf1 wm0 wm1 req Hnz Hneq Hstep.
    pose proof (ghost_waitMask_step core pcAddrInit rf0 rf1 wm0 wm1 req Hstep) as Hwm.
    destruct (ghost_rf_step core pcAddrInit rf0 rf1 wm0 wm1 req Hstep)
      as [pcc [meip [mtip [aluOut [execOut [rf_mid [Hsem [Hrf1 [Hdm [Hdst Haddr]]]]]]]]]].
    constructor.
    - exact Hwm.
    - exists pcc, meip, mtip, aluOut, execOut, (updGpr core pcAddrInit wIdx wbVal rf_mid).
      repeat split.
      + apply SemAction_executeNonDeferred_updGpr; [| exact Hsem].
        unfold ghost_dstIdx in Hdst; rewrite Hdst; exact Hneq.
      + rewrite Hrf1.
        change (evalWriteRegsList (gprPathsWithKind core pcAddrInit)) with (updGpr core pcAddrInit).
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
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep core pcAddrInit
        (writeGprVal core pcAddrInit wIdx wbVal rf0)
        (writeGprVal core pcAddrInit wIdx wbVal rf1)
        wm0 wm1 req.
  Proof.
    intros wIdx wbVal rf0 rf1 wm0 wm1 req Hneq Hstep.
    rewrite (writeGprVal_unfold core pcAddrInit wIdx wbVal rf0),
            (writeGprVal_unfold core pcAddrInit wIdx wbVal rf1).
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
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStep core pcAddrInit
        (flushMulDivCaps core pcAddrInit entries rf0)
        (flushMulDivCaps core pcAddrInit entries rf1)
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
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList core pcAddrInit
        (updGpr core pcAddrInit wIdx wbVal rf0) wm0
        reqs
        (updGpr core pcAddrInit wIdx wbVal rf2) wm2.
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
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList core pcAddrInit
        (writeGprVal core pcAddrInit wIdx wbVal rf0) wm0
        reqs
        (writeGprVal core pcAddrInit wIdx wbVal rf2) wm2.
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
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList core pcAddrInit
        (writeGprVal core pcAddrInit wIdx wbVal rf0) wm0'
        reqs
        (writeGprVal core pcAddrInit wIdx wbVal rf2) (foldWaitMask reqs wm0').
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
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostList core pcAddrInit
        (flushMulDivCaps core pcAddrInit entries rf0) wm0
        reqs
        (flushMulDivCaps core pcAddrInit entries rf2) wm2.
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
      GhostStep core pcAddrInit rf0 rf1 wm0 wm1 req ->
      GhostStepOpt core pcAddrInit rf0 rf1 wm0 wm1 (Some req).
  Proof.
    intros rf0 rf1 wm0 wm1 req Hni Hstep.
    constructor; [intros _; exact Hni | exact Hstep].
  Qed.

  Lemma GhostListOpt_app :
    forall rf0 wm0 reqs1 rf1 wm1 reqs2 rf2 wm2,
      GhostListOpt core pcAddrInit rf0 wm0 reqs1 rf1 wm1 ->
      GhostListOpt core pcAddrInit rf1 wm1 reqs2 rf2 wm2 ->
      GhostListOpt core pcAddrInit rf0 wm0 (reqs1 ++ reqs2) rf2 wm2.
  Proof.
    intros rf0 wm0 reqs1 rf1 wm1 reqs2 rf2 wm2 H1 H2.
    induction H1 as [rf wm | r0 r1 r2 w0 w1 w2 [req |] reqs Hstep Hrest IH]; cbn [app].
    - exact H2.
    - eapply (GhostOptCons _ _ _ _ _ _ _ _ (Some req)); [exact Hstep | exact (IH H2)].
    - eapply (GhostOptCons _ _ _ _ _ _ _ _ None); [exact Hstep | exact (IH H2)].
  Qed.

  Lemma GhostListOpt_snoc_Some :
    forall rf0 wm0 reqs rf1 wm1 req rf2 wm2,
      GhostListOpt core pcAddrInit rf0 wm0 reqs rf1 wm1 ->
      GhostStepOpt core pcAddrInit rf1 rf2 wm1 wm2 (Some req) ->
      GhostListOpt core pcAddrInit rf0 wm0 (reqs ++ [req]) rf2 wm2.
  Proof.
    intros rf0 wm0 reqs rf1 wm1 req rf2 wm2 Hgl Hstep.
    eapply GhostListOpt_app; [exact Hgl |].
    eapply (GhostOptCons _ _ _ _ _ _ _ _ (Some req)); [exact Hstep | apply GhostOptNil].
  Qed.

  Lemma GhostListOpt_snoc_None :
    forall rf0 wm0 reqs rf1 wm1 rf2 wm2,
      GhostListOpt core pcAddrInit rf0 wm0 reqs rf1 wm1 ->
      GhostStepOpt core pcAddrInit rf1 rf2 wm1 wm2 None ->
      GhostListOpt core pcAddrInit rf0 wm0 reqs rf2 wm2.
  Proof.
    intros rf0 wm0 reqs rf1 wm1 rf2 wm2 Hgl Hstep.
    rewrite <- (app_nil_r reqs).
    eapply GhostListOpt_app; [exact Hgl |].
    eapply (GhostOptCons _ _ _ _ _ _ _ _ None); [exact Hstep | apply GhostOptNil].
  Qed.

  Lemma DataMemInFlightCmdRel_LoadRq :
    forall (dataMemCapacity : nat) (sdm : DataMemSubState core dataMemCapacity)
           (req : type MemFenceReq),
      isDataMemLoadRq core dataMemCapacity sdm = true ->
      DataMemInFlightCmdRel core dataMemCapacity sdm req.
  Proof.
    intros dataMemCapacity sdm req Hrq.
    unfold DataMemInFlightCmdRel, isDataMemLoadRq in *.
    cbn [evalExpr isEq] in Hrq |- *.
    apply Zmod.eqb_eq in Hrq.
    rewrite Hrq; cbn; exact I.
  Qed.

End GhostListLemmas.


