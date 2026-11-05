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
From Stdlib Require Import Permutation.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel DecodeFacts SimDevices SimFetchDecode SimExecute SimDataMem GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead RefSpecFetch RefRevoker RefReplay.
From Cheriot.Proof Require Import RefExec RefExecImpl RefRedirect RefRevBitRule RefRedirStep.
From Cheriot.Proof Require Import RefPcEven.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7: THE RELATION SIDE OF `aluAndExecuteNonDeferredStage`
 * ===========================================================================
 * One lemma per branch of the stage: from related states and the impl step of that branch
 * (RefExecImpl.v), spec steps (none, a lockstep `specStep`, or the replay after a ghost
 * append) and a ghost that relate the states after the step. *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma readPcc_writePcc :
  forall pcAddrInit v rf, readPcc pcAddrInit (writePcc pcAddrInit v rf) = v.
Proof.
  intros pcAddrInit v rf; unfold readPcc, writePcc, readGpr, updGpr.
  apply evalReadRegsList_evalWriteRegsList_same; reflexivity.
Qed.

(* With an interrupt pending, `executeNonDeferred` is `executeInterrupt` (any ALU output).  The
 * equations restate the arguments, so callers never rely on a conversion between the two forms. *)
Lemma nonDeferred_of_interrupt :
  forall pcAddrInit (env : Env (rfTree pcAddrInit)) pcc pcc' meip meip' mtip mtip' aluOut rf rf' out,
    pcc = pcc' -> meip = meip' -> mtip = mtip' ->
    evalIsInterruptPending pcAddrInit meip mtip rf = true ->
    SemAction env (@executeInterrupt pcAddrInit type pcc meip mtip) rf rf' out ->
    SemAction env (@executeNonDeferred pcAddrInit type pcc' meip' mtip' aluOut) rf rf' out.
Proof.
  intros pcAddrInit env pcc pcc' meip meip' mtip mtip' aluOut rf rf' out <- <- <- Hint Hex.
  rewrite SemAction_iff_evalActionPropGen in Hex |- *.
  exact (proj2 (evalActionPropGen_executeNonDeferred_interrupt pcAddrInit pcc meip mtip aluOut rf _ Hint) Hex).
Qed.

(* --- Sequential Instructions: Generic Facts (over variables; the ALU is never evaluated) --- *)

(* The execute output of a sequential instruction (SimExecute.v,
 * `evalActionPropGen_executeNonDeferred_sequential`) *)
Definition seqOut (pcc : type FullECapWithTag) (aluOut : type AluOutUnion) (mdOpt : type (Option MulDivUnion))
  : type ExecuteOut :=
  (mdOpt ,, (evalExpr (@mkNone type MemFenceUnion) ,, (evalExpr (@mkNone type CfPayload) ,,
   (false ,, (evalExpr (@Alu.getSeqPcc type pcc aluOut.(Fst)) ,, tt))))).

Lemma nonDeferred_of_sequential :
  forall pcAddrInit (env : Env (rfTree pcAddrInit)) pcc meip mtip (aluOut : type AluOutUnion) rf rf' mdOpt,
    evalIsInterruptPending pcAddrInit meip mtip rf = false ->
    aluIsSeq aluOut = true ->
    SemAction env (@executeSequential pcAddrInit type pcc aluOut) rf rf' mdOpt ->
    SemAction env (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut) rf rf' (seqOut pcc aluOut mdOpt).
Proof.
  intros pcAddrInit env pcc meip mtip aluOut rf rf' mdOpt Hint Hseq Hex.
  rewrite SemAction_iff_evalActionPropGen in Hex; rewrite SemAction_iff_evalActionPropGen.
  apply (proj2 (evalActionPropGen_executeNonDeferred_sequential pcAddrInit pcc meip mtip aluOut rf _ Hint Hseq)).
  eapply evalActionPropGen_mono; [| exact Hex].
  intros s r [-> ->]; cbv zeta; split; reflexivity.
Qed.

(* A sequential op is not a virtual CSR read (the AluOp tag is Sequential, not NonSequential) *)
Lemma seq_notVirt :
  forall aluOut : type AluOutUnion, aluIsSeq aluOut = true -> isVirtualCsrAluOut aluOut = false.
Proof.
  intros aluOut Hseq; unfold aluIsSeq, isVirtualCsrAluOut in *; cbv zeta in *.
  set (aluOp := evalExpr (##aluOut`"Op")) in *.
  assert (Hns : evalExpr ((Var type AluOpUnion aluOp) `? "NonSequential") = false).
  { cbn [evalExpr] in Hseq |- *. apply Zmod.eqb_eq in Hseq. rewrite Hseq. reflexivity. }
  rewrite Hns; reflexivity.
Qed.

(* The Sequential op's tags, in the stage's syntax: Normal or MulDiv, and the MulDiv payload *)
Definition aluSeqNormal (aluOut : type AluOutUnion) : bool :=
  let aluOp : type AluOpUnion      := evalExpr (##aluOut`"Op") in
  let seqOp : type SequentialUnion := evalExpr (#aluOp `! "Sequential") in
  evalExpr (#seqOp `? "Normal").

Definition aluSeqMd (aluOut : type AluOutUnion) : type MulDivUnion :=
  let aluOp : type AluOpUnion      := evalExpr (##aluOut`"Op") in
  let seqOp : type SequentialUnion := evalExpr (#aluOp `! "Sequential") in
  evalExpr (#seqOp `! "MulDiv").

(* An `IfElse` with each branch handled under its condition *)
Lemma allReturns_IfElse_cond :
  forall {t : Tree Elem} {k1 k2 : Kind} (nm : string) (p : Expr type Bool)
         (tb fb : Action type t k1) (cont : type k1 -> Action type t k2) (Q : type k2 -> Prop),
    (evalExpr p = true -> allReturns tb (fun v => allReturns (cont v) Q)) ->
    (evalExpr p = false -> allReturns fb (fun v => allReturns (cont v) Q)) ->
    allReturns (IfElse nm p tb fb cont) Q.
Proof.
  intros t k1 k2 nm p tb fb cont Q Ht Hf; cbn [allReturns].
  destruct (evalExpr p); [exact (Ht eq_refl) | exact (Hf eq_refl)].
Qed.

(* `executeSequential` returns the MulDiv payload exactly when the op is not Normal *)
Lemma executeSequential_mdOpt :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)} (pcc : type FullECapWithTag) (aluOut : type AluOutUnion)
         (rf rf' : RfState pcAddrInit) (mdOpt : type (Option MulDivUnion)),
    SemAction env (@executeSequential pcAddrInit type pcc aluOut) rf rf' mdOpt ->
    optValid mdOpt = negb (aluSeqNormal aluOut) /\
    (optValid mdOpt = true -> optData mdOpt = aluSeqMd aluOut).
Proof.
  intros pcAddrInit env pcc aluOut rf rf' mdOpt Hsem.
  refine (allReturns_SemAction _ rf rf' mdOpt
            (fun r => optValid r = negb (aluSeqNormal aluOut) /\ (optValid r = true -> optData r = aluSeqMd aluOut))
            _ Hsem).
  unfold executeSequential.
  repeat (lazymatch goal with
          | |- allReturns (LetExp _ _ _) _ => simple apply allReturns_step_letexp
          | |- allReturns (LetAction _ _ _) _ => simple apply allReturns_step_let; intros _
          end; cbv beta).
  apply allReturns_IfElse_cond; intros E.
  - change (aluSeqNormal aluOut = true) in E.
    apply allReturns_IfElse_any; intros _; cbn [allReturns].
    rewrite E; split; [reflexivity | discriminate].
  - change (aluSeqNormal aluOut = false) in E.
    simple apply allReturns_step_letexp; cbv beta; cbn [allReturns].
    rewrite E; split; reflexivity.
Qed.

(* With the op not Normal, a Mul payload means `aluIsMul`, a Div payload `aluIsDiv` *)
Lemma seq_md_isMul :
  forall aluOut : type AluOutUnion,
    aluIsSeq aluOut = true -> aluSeqNormal aluOut = false -> mdIsMul (aluSeqMd aluOut) = true ->
    aluIsMul aluOut = true.
Proof.
  intros aluOut Hs Hn Hm; unfold aluIsSeq, aluSeqNormal, aluSeqMd, aluIsMul, mdIsMul in *; cbv zeta in *.
  set (aluOp := evalExpr (##aluOut`"Op")) in *.
  set (seqOp := evalExpr ((Var type AluOpUnion aluOp) `! "Sequential")) in *.
  set (mdOp := evalExpr ((Var type SequentialUnion seqOp) `! "MulDiv")) in *.
  assert (Hmd : evalExpr ((Var type SequentialUnion seqOp) `? "MulDiv") = true)
    by (apply bits1_eqb_0_false_1_true; exact Hn).
  change (andb (andb true (andb (andb true (evalExpr ((Var type AluOpUnion aluOp) `? "Sequential")))
                                (evalExpr ((Var type SequentialUnion seqOp) `? "MulDiv"))))
               (evalExpr ((Var type MulDivUnion mdOp) `? "Mul")) = true).
  rewrite Hs, Hmd, Hm; reflexivity.
Qed.

Lemma seq_md_isDiv :
  forall aluOut : type AluOutUnion,
    aluIsSeq aluOut = true -> aluSeqNormal aluOut = false -> mdIsMul (aluSeqMd aluOut) = false ->
    aluIsDiv aluOut = true.
Proof.
  intros aluOut Hs Hn Hm; unfold aluIsSeq, aluSeqNormal, aluSeqMd, aluIsDiv, mdIsMul in *; cbv zeta in *.
  set (aluOp := evalExpr (##aluOut`"Op")) in *.
  set (seqOp := evalExpr ((Var type AluOpUnion aluOp) `! "Sequential")) in *.
  set (mdOp := evalExpr ((Var type SequentialUnion seqOp) `! "MulDiv")) in *.
  assert (Hmd : evalExpr ((Var type SequentialUnion seqOp) `? "MulDiv") = true)
    by (apply bits1_eqb_0_false_1_true; exact Hn).
  assert (Hdv : evalExpr ((Var type MulDivUnion mdOp) `? "Div") = true)
    by (apply bits1_eqb_0_false_1_true; exact Hm).
  change (andb (andb true (andb (andb true (evalExpr ((Var type AluOpUnion aluOp) `? "Sequential")))
                                (evalExpr ((Var type SequentialUnion seqOp) `? "MulDiv"))))
               (evalExpr ((Var type MulDivUnion mdOp) `? "Div")) = true).
  rewrite Hs, Hmd, Hdv; reflexivity.
Qed.

(* The sequential stall guard: a Mul needs the mul FIFO not full, a Div the div FIFO *)
Lemma seqGuard_mul : forall im id mf df, seqGuardV im id mf df = true -> im = true -> mf = false.
Proof. intros [] [] [] []; cbn; intros H E; first [reflexivity | discriminate H | discriminate E]. Qed.

Lemma seqGuard_div : forall im id mf df, seqGuardV im id mf df = true -> id = true -> df = false.
Proof. intros [] [] [] []; cbn; intros H E; first [reflexivity | discriminate H | discriminate E]. Qed.

(* The sequential next PCC is the PCC with the next sequential address *)
Lemma getSeqPcc_pccWithAddr :
  forall (pcc : type FullECapWithTag) (inst : type Inst) (isComp : bool),
    isComp = evalExpr (@isCompressed type inst) ->
    evalExpr (@Alu.getSeqPcc type pcc isComp) = pccWithAddr pcc (seqPcOf pcc.(Snd).(Snd).(Fst) inst).
Proof.
  intros pcc inst isComp ->.
  destruct pcc as [t [e [ad u]]]; destruct u; reflexivity.
Qed.

(* --- MulDiv Results: the Rebuilt Union Computes the Same Result (Readback, No Arithmetic) --- *)

(* `MulDiv` depends only on the Mul tag and the payload of the branch taken.  The unions are
 * variables here, so the kernel never computes one. *)
Lemma MulDiv_ext_mul :
  forall (op1 : type Addr) (u1 u2 : type MulDivUnion),
    evalExpr ((Var type MulDivUnion u1) `? "Mul") = true ->
    evalExpr ((Var type MulDivUnion u2) `? "Mul") = true ->
    evalExpr ((Var type MulDivUnion u1) `! "Mul") = evalExpr ((Var type MulDivUnion u2) `! "Mul") ->
    evalLetExpr (@SpecMulDiv.MulDiv type op1 u1) = evalLetExpr (@SpecMulDiv.MulDiv type op1 u2).
Proof.
  intros op1 u1 u2 T1 T2 R; unfold SpecMulDiv.MulDiv; cbn [evalLetExpr].
  match goal with |- context [?X] => lazymatch X with evalExpr (ReadUnionTag (Var type _ u1) _) =>
    let E := fresh in assert (E : X = true) by exact T1; rewrite E; clear E end end.
  match goal with |- context [?X] => lazymatch X with evalExpr (ReadUnionTag (Var type _ u2) _) =>
    let E := fresh in assert (E : X = true) by exact T2; rewrite E; clear E end end.
  repeat match goal with |- context [?X] => lazymatch X with evalExpr (ReadUnionData (Var type _ u1) _) =>
    let E := fresh in assert (E : X = evalExpr ((Var type MulDivUnion u2) `! "Mul")) by exact R;
    rewrite E; clear E end end.
  reflexivity.
Qed.

Lemma MulDiv_ext_div :
  forall (op1 : type Addr) (u1 u2 : type MulDivUnion),
    evalExpr ((Var type MulDivUnion u1) `? "Mul") = false ->
    evalExpr ((Var type MulDivUnion u2) `? "Mul") = false ->
    evalExpr ((Var type MulDivUnion u1) `! "Div") = evalExpr ((Var type MulDivUnion u2) `! "Div") ->
    evalLetExpr (@SpecMulDiv.MulDiv type op1 u1) = evalLetExpr (@SpecMulDiv.MulDiv type op1 u2).
Proof.
  intros op1 u1 u2 T1 T2 R; unfold SpecMulDiv.MulDiv; cbn [evalLetExpr].
  match goal with |- context [?X] => lazymatch X with evalExpr (ReadUnionTag (Var type _ u1) _) =>
    let E := fresh in assert (E : X = false) by exact T1; rewrite E; clear E end end.
  match goal with |- context [?X] => lazymatch X with evalExpr (ReadUnionTag (Var type _ u2) _) =>
    let E := fresh in assert (E : X = false) by exact T2; rewrite E; clear E end end.
  repeat match goal with |- context [?X] => lazymatch X with evalExpr (ReadUnionData (Var type _ u1) _) =>
    let E := fresh in assert (E : X = evalExpr ((Var type MulDivUnion u2) `! "Div")) by exact R;
    rewrite E; clear E end end.
  reflexivity.
Qed.

(* The rebuilt union of the enqueued request computes the same result (readback, no arithmetic) *)
Lemma MulDiv_mulUnion :
  forall (op1 : type Addr) (mdOp : type MulDivUnion),
    mdIsMul mdOp = true ->
    evalLetExpr (@SpecMulDiv.MulDiv type op1 (mulUnionV (mdMulOf mdOp))) =
    evalLetExpr (@SpecMulDiv.MulDiv type op1 mdOp).
Proof.
  intros op1 mdOp Hm; apply MulDiv_ext_mul; [reflexivity | exact Hm |].
  transitivity (mdMulOf mdOp); [| reflexivity].
  unfold mulUnionV.
  exact (evalExpr_ReadUnionData_BuildUnion MulDivType (@Build_FinType (length MulDivType) 0 I)
           (Var type MulOp (mdMulOf mdOp)) eq_refl).
Qed.

Lemma MulDiv_divUnion :
  forall (op1 : type Addr) (mdOp : type MulDivUnion),
    mdIsMul mdOp = false ->
    evalLetExpr (@SpecMulDiv.MulDiv type op1 (divUnionV (mdDivOf mdOp))) =
    evalLetExpr (@SpecMulDiv.MulDiv type op1 mdOp).
Proof.
  intros op1 mdOp Hm; apply MulDiv_ext_div; [reflexivity | exact Hm |].
  transitivity (mdDivOf mdOp); [| reflexivity].
  unfold divUnionV.
  exact (evalExpr_ReadUnionData_BuildUnion MulDivType (@Build_FinType (length MulDivType) 1 I)
           (Var type DivOp (mdDivOf mdOp)) eq_refl).
Qed.

(* The result entries the request FIFOs hold *)
Lemma evalMulReqCap_mulReqV :
  forall dst op1 mOp,
    evalMulReqCap (mulReqV dst op1 mOp) = (dst, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type op1 (mulUnionV mOp)))).
Proof. reflexivity. Qed.

Lemma evalDivReqCap_divReqV :
  forall dst op1 dOp,
    evalDivReqCap (divReqV dst op1 dOp) = (dst, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type op1 (divUnionV dOp)))).
Proof. reflexivity. Qed.

Lemma evalMulDivReqCap_mulDivReqV :
  forall dst op1 u,
    evalMulDivReqCap (mulDivReqV dst op1 u) = (dst, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type op1 u))).
Proof. reflexivity. Qed.

(* A FIFO that is not full has room *)
Lemma fifo_notFull_lt :
  forall (cap : nat) (k : Kind) (f : TreeState ElemState (ShiftFifo.fifoTree cap k)),
    fifo_wf f -> Zmod.eqb (fifo_size f) (Zmod.of_Z _ (Z.of_nat cap)) = false ->
    (length (fifo_to_list f) < cap)%nat.
Proof.
  intros cap k f Hwf Hnf.
  rewrite (fifo_size_eqb_cap _ _ f) in Hnf; apply Nat.eqb_neq in Hnf.
  rewrite (length_fifo_to_list _ _ f Hwf); unfold fifo_wf in Hwf; lia.
Qed.

Lemma perm_move_last : forall {A : Type} (P B : list A) (x : A), Permutation (P ++ x :: B) (P ++ B ++ [x]).
Proof. intros A P B x; apply Permutation_app_head, Permutation_cons_append. Qed.

(* The entries after an enqueue: the old ones and the new request (a Mul in the split modes lands
 * before the Div entries, hence a permutation) *)
Section MdEnq.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.

  Local Abbreviation MDT := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation EXT := (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation WF := (MulDivWf mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation ENQM := (mdEnqMul mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation ENQD := (mdEnqDiv mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation FULLM := (mdFullMul mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation FULLD := (mdFullDiv mulCapacity divCapacity mulStages divStages mulDivMode).

  Lemma extract_enqMul :
    forall dst op1 mOp (smd : TreeState ElemState MDT),
      WF smd -> FULLM smd = false ->
      Permutation (EXT (ENQM dst op1 mOp smd))
                  (EXT smd ++ [(dst, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type op1 (mulUnionV mOp))))]).
  Proof.
    intros dst op1 mOp; unfold extractMulDivEntries, MulDivWf, MulDivReqWf, mdEnqMul, mdFullMul.
    destruct mulDivMode; intros smd [Hwf _] Hnf.
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm _]; cbv zeta.
      rewrite (fifo_to_list_enq _ _ mulReqF _ Hwm (fifo_notFull_lt _ _ mulReqF Hwm Hnf)), map_app; cbn [map].
      rewrite evalMulReqCap_mulReqV, <- !app_assoc; cbn [app].
      do 2 apply Permutation_app_head; rewrite app_assoc; apply Permutation_cons_append.
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm _]; cbv zeta.
      rewrite (fifo_to_list_enq _ _ mulReqF _ Hwm (fifo_notFull_lt _ _ mulReqF Hwm Hnf)), map_app; cbn [map].
      rewrite evalMulReqCap_mulReqV, <- !app_assoc; cbn [app].
      do 2 apply Permutation_app_head; rewrite app_assoc; apply Permutation_cons_append.
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [Fst Snd] in *; cbv zeta.
      rewrite (fifo_to_list_enq _ _ reqF _ Hwf (fifo_notFull_lt _ _ reqF Hwf Hnf)), map_app; cbn [map].
      rewrite evalMulDivReqCap_mulDivReqV, <- !app_assoc; apply Permutation_refl.
  Qed.

  Lemma extract_enqDiv :
    forall dst op1 dOp (smd : TreeState ElemState MDT),
      WF smd -> FULLD smd = false ->
      Permutation (EXT (ENQD dst op1 dOp smd))
                  (EXT smd ++ [(dst, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type op1 (divUnionV dOp))))]).
  Proof.
    intros dst op1 dOp; unfold extractMulDivEntries, MulDivWf, MulDivReqWf, mdEnqDiv, mdFullDiv.
    destruct mulDivMode; intros smd [Hwf _] Hnf.
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [_ Hwd]; cbv zeta.
      rewrite (fifo_to_list_enq _ _ divReqF _ Hwd (fifo_notFull_lt _ _ divReqF Hwd Hnf)), map_app; cbn [map].
      rewrite evalDivReqCap_divReqV, <- !app_assoc; apply Permutation_refl.
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [_ Hwd]; cbv zeta.
      rewrite (fifo_to_list_enq _ _ divReqF _ Hwd (fifo_notFull_lt _ _ divReqF Hwd Hnf)), map_app; cbn [map].
      rewrite evalDivReqCap_divReqV, <- !app_assoc; apply Permutation_refl.
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [Fst Snd] in *; cbv zeta.
      rewrite (fifo_to_list_enq _ _ reqF _ Hwf (fifo_notFull_lt _ _ reqF Hwf Hnf)), map_app; cbn [map].
      rewrite evalMulDivReqCap_mulDivReqV, <- !app_assoc; apply Permutation_refl.
  Qed.

  Lemma WF_enqMul : forall dst op1 mOp (smd : TreeState ElemState MDT), WF smd -> WF (ENQM dst op1 mOp smd).
  Proof.
    intros dst op1 mOp; unfold MulDivWf, MulDivReqWf, MulDivEngWf, mdEnqMul; destruct mulDivMode; intros smd [Hwf He].
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [split; [apply fifo_wf_enq; exact Hwm | exact Hwd] | exact He].
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [split; [apply fifo_wf_enq; exact Hwm | exact Hwd] | exact He].
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [Fst Snd] in *; split; [apply fifo_wf_enq; exact Hwf | exact He].
  Qed.

  Lemma WF_enqDiv : forall dst op1 dOp (smd : TreeState ElemState MDT), WF smd -> WF (ENQD dst op1 dOp smd).
  Proof.
    intros dst op1 dOp; unfold MulDivWf, MulDivReqWf, MulDivEngWf, mdEnqDiv; destruct mulDivMode; intros smd [Hwf He].
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [split; [exact Hwm | apply fifo_wf_enq; exact Hwd] | exact He].
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [split; [exact Hwm | apply fifo_wf_enq; exact Hwd] | exact He].
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [Fst Snd] in *; split; [apply fifo_wf_enq; exact Hwf | exact He].
  Qed.
End MdEnq.

(* --- Flushing the MulDiv Entries --- *)

Lemma flushMulDivCaps_app :
  forall pcAddrInit l1 l2 (rf : RfState pcAddrInit),
    flushMulDivCaps pcAddrInit (l1 ++ l2) rf = flushMulDivCaps pcAddrInit l2 (flushMulDivCaps pcAddrInit l1 rf).
Proof.
  intros pcAddrInit l1; induction l1 as [| [d v] l1 IH]; intros l2 rf; cbn [app flushMulDivCaps];
    [reflexivity | apply IH].
Qed.

(* the destinations an entry list writes (x0 writes nothing) *)
Definition nzDsts (l : list (bits RegIdxSzReal * type FullECapWithTag)) : list (bits RegIdxSzReal) :=
  filter (fun d => negb (Zmod.eqb d Zmod.zero)) (map fst l).

Lemma Permutation_filter_local :
  forall {A : Type} (f : A -> bool) (l l' : list A), Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros A f l l' Hp; induction Hp as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; cbn [filter].
  - constructor.
  - destruct (f x); [apply perm_skip |]; exact IH.
  - destruct (f x), (f y); first [apply perm_swap | apply Permutation_refl].
  - exact (perm_trans IH1 IH2).
Qed.

Lemma nzDsts_perm : forall l l', Permutation l l' -> Permutation (nzDsts l) (nzDsts l').
Proof. intros l l' Hp; unfold nzDsts; apply Permutation_filter_local, Permutation_map, Hp. Qed.

(* Flushing respects permutations when the non-x0 destinations are distinct *)
Lemma flushMulDivCaps_perm :
  forall pcAddrInit l l' (rf : RfState pcAddrInit),
    NoDup (nzDsts l) -> Permutation l l' ->
    flushMulDivCaps pcAddrInit l rf = flushMulDivCaps pcAddrInit l' rf.
Proof.
  intros pcAddrInit l l' rf Hnd Hp; revert rf Hnd.
  induction Hp as [| [d v] l l' _ IH | [dx vx] [dy vy] l | l l' l'' Hp1 IH1 _ IH2]; intros rf Hnd;
    cbn [flushMulDivCaps].
  - reflexivity.
  - apply IH; unfold nzDsts in *; cbn [map filter fst] in Hnd.
    destruct (negb (Zmod.eqb d Zmod.zero)); [inversion Hnd; assumption | exact Hnd].
  - f_equal; apply writeGprVal_comm.
    intros Hy Hx Heq; subst dy; unfold nzDsts in Hnd; cbn [map filter fst] in Hnd.
    rewrite Hy in Hnd; cbn [negb] in Hnd; inversion Hnd as [| ? ? Hn _]; apply Hn; left; reflexivity.
  - rewrite (IH1 rf Hnd); apply IH2; exact (Permutation_NoDup (nzDsts_perm _ _ Hp1) Hnd).
Qed.

Lemma flushMulDivCaps_snoc :
  forall pcAddrInit l d v (rf : RfState pcAddrInit),
    flushMulDivCaps pcAddrInit (l ++ [(d, v)]) rf = writeGprVal pcAddrInit d v (flushMulDivCaps pcAddrInit l rf).
Proof. intros pcAddrInit l d v rf; rewrite flushMulDivCaps_app; reflexivity. Qed.

(* The mulDiv write-back of the spec for a valid mulDiv output *)
Lemma specMulDivWb_md :
  forall pcAddrInit (aluOut : type AluOutUnion) (execOut : type ExecuteOut) (rf : RfState pcAddrInit),
    optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = true ->
    specMulDivWb pcAddrInit aluOut execOut rf =
    writeGprVal pcAddrInit (aluDstIdx aluOut)
      (mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type (aluDstVal aluOut).(Snd).(Snd).(Fst)
                                   (optData (execMulDiv execOut))))) rf.
Proof.
  intros pcAddrInit aluOut execOut rf Hdm Hmd; unfold specMulDivWb, optValid, optData in *; cbv zeta.
  rewrite Hdm, Hmd; reflexivity.
Qed.

Lemma specMulDivWb_noMd :
  forall pcAddrInit (aluOut : type AluOutUnion) (execOut : type ExecuteOut) (rf : RfState pcAddrInit),
    optValid (execDataMem execOut) = false -> optValid (execMulDiv execOut) = false ->
    specMulDivWb pcAddrInit aluOut execOut rf = rf.
Proof.
  intros pcAddrInit aluOut execOut rf Hdm Hmd; unfold specMulDivWb, optValid in *; cbv zeta.
  rewrite Hdm, Hmd; reflexivity.
Qed.

(* The fields of the sequential execute output *)
Lemma execMulDiv_seqOut : forall pcc aluOut mdOpt, execMulDiv (seqOut pcc aluOut mdOpt) = mdOpt.
Proof. reflexivity. Qed.

Lemma execDataMem_seqOut : forall pcc aluOut mdOpt, optValid (execDataMem (seqOut pcc aluOut mdOpt)) = false.
Proof. reflexivity. Qed.

Lemma execNextPcc_seqOut :
  forall pcc (aluOut : type AluOutUnion) mdOpt,
    execNextPcc (seqOut pcc aluOut mdOpt) = evalExpr (@Alu.getSeqPcc type pcc aluOut.(Fst)).
Proof. reflexivity. Qed.

(* An entry without a memory or fence request is no fence.i *)
Lemma entryIsFenceI_noDm : forall e : GEntry, optValid (ge_dm e) = false -> entryIsFenceI e = false.
Proof. intros e H; unfold entryIsFenceI, entryReq; rewrite H; reflexivity. Qed.

Lemma NoDup_mid : forall {A : Type} (x y z w : list A), NoDup (x ++ y ++ z ++ w) -> NoDup (y ++ z).
Proof.
  intros A x y z w H; apply NoDup_app_remove_l in H; rewrite app_assoc in H; exact (NoDup_app_remove_r _ _ H).
Qed.

(* --- Sequential Instructions: ALU Facts (DecodeFacts.v; the ALU output stays a variable `a`) --- *)

Lemma excAny_or4 :
  forall x : type FetchException,
    excAny x = true -> evalExpr (Or [##x`"tag"; ##x`"seal"; ##x`"perm"; ##x`"bounds"]) = true.
Proof.
  intros [t [s [p [b []]]]] H; destruct t, s, p, b; first [reflexivity | cbv in H; discriminate H].
Qed.

(* A sequential op had no fetch fault (a fault gives the Exception op) *)
Lemma seq_noFault :
  forall pcAddrInit (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit) (a : type AluOutUnion),
    a = evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) -> aluIsSeq a = true -> foFault fo = false.
Proof.
  intros pcAddrInit pcc fo rf a Ha Hseq.
  set (pkg := evalRegRead pcAddrInit (evalDecode fo) rf) in Ha.
  destruct (foFault fo) eqn:Ef; [exfalso | reflexivity].
  pose proof (wrappedAlu_fetchExc_nonSeq pcc pkg) as T; cbv zeta in T.
  change (evalLetExpr (@wrappedAlu type pcc pkg)) with (evalAluOut pcc pkg) in T.
  rewrite <- Ha in T.
  destruct (T (excAny_or4 _ Ef)) as [T1 _].
  change (aluIsSeq a = false) in T1; rewrite T1 in Hseq; discriminate Hseq.
Qed.

(* A sequential op needs no prediction (a predicted branch or jump is a ControlFlow op) *)
Lemma seq_noPred :
  forall pcAddrInit (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit) (a : type AluOutUnion),
    a = evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) -> aluIsSeq a = true ->
    needsPredOf (foInst fo) = false.
Proof.
  intros pcAddrInit pcc fo rf a Ha Hseq.
  set (pkg := evalRegRead pcAddrInit (evalDecode fo) rf) in Ha.
  destruct (needsPredOf (foInst fo)) eqn:En; [exfalso | reflexivity].
  pose proof (preDecodeBranch_needsPred (foInst fo) En) as Hb.
  pose proof (preDecodeBranch_nonSeq pcc fo (foInst fo) pkg eq_refl eq_refl Hb) as T; cbv zeta in T.
  change (evalLetExpr (@wrappedAlu type pcc pkg)) with (evalAluOut pcc pkg) in T.
  rewrite <- Ha in T; destruct T as [T1 _].
  change (aluIsSeq a = false) in T1; rewrite T1 in Hseq; discriminate Hseq.
Qed.

(* The ALU's `isComp` is the instruction's compressed flag *)
Lemma seq_isComp :
  forall pcAddrInit (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit) (a : type AluOutUnion),
    a = evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) ->
    a.(Fst) = evalExpr (@isCompressed type (foInst fo)).
Proof.
  intros pcAddrInit pcc fo rf a Ha.
  set (pkg := evalRegRead pcAddrInit (evalDecode fo) rf) in Ha.
  pose proof (wrappedAlu_isComp pcc pkg) as T; cbv zeta in T.
  change (evalLetExpr (@wrappedAlu type pcc pkg)) with (evalAluOut pcc pkg) in T.
  rewrite <- Ha in T.
  change (a.(Fst) = evalExpr (@isCompressed type (aluInInst pkg))) in T.
  rewrite T; unfold pkg; rewrite regRead_inst; reflexivity.
Qed.

(* After the head's step, a later entry reads the same registers: it avoids the head's
 * destination (the scoreboard), and the PCC write and the mulDiv write-back touch nothing else *)
Lemma regRead_after_step :
  forall pcAddrInit (pcc : type FullECapWithTag) meip mtip (a : type AluOutUnion) j l1 fo ow
         (rf0 rfM : RfState pcAddrInit) (x : type ExecuteOut),
    a = evalAluOut pcc (daAluIn j) ->
    SemAction defaultEnv (@executeNonDeferred pcAddrInit type pcc meip mtip a) rf0 rfM x ->
    RegAvoidAll (ow ++ d2aWriters (j :: l1)) (decCs1 fo) ->
    RegAvoidAll (ow ++ d2aWriters (j :: l1)) (decCs2 fo) ->
    evalRegRead pcAddrInit (evalDecode fo) (specMulDivWb pcAddrInit a x (writePcc pcAddrInit (execNextPcc x) rfM)) =
    evalRegRead pcAddrInit (evalDecode fo) rf0.
Proof.
  intros pcAddrInit pcc meip mtip a j l1 fo ow rf0 rfM x Ha Hsem H1 H2.
  assert (Hd : Zmod.eqb (aluDstIdx a) Zmod.zero = false -> In (aluDstIdx a) (ow ++ d2aWriters (j :: l1))).
  { intros Hz; rewrite Ha, d2aDst_aluDstIdx in Hz |- *.
    apply in_or_app; right; rewrite d2aWriters_cons, Hz; left; reflexivity. }
  transitivity (evalRegRead pcAddrInit (evalDecode fo) (writePcc pcAddrInit (execNextPcc x) rfM)).
  - unfold specMulDivWb; cbv zeta.
    destruct ((execDataMem x).(Snd).(Fst)); [reflexivity |].
    destruct ((execMulDiv x).(Snd).(Fst)); [| reflexivity].
    apply evalRegRead_writeGprVal.
    + intros Hz Hc; exact (H1 _ (Hd Hz) Hz Hc).
    + intros Hz Hc; exact (H2 _ (Hd Hz) Hz Hc).
  - subst a; eapply evalRegRead_executeNonDeferred_writePcc_other; [exact Hsem | exact H1 | exact H2].
Qed.

(* --- Non-Sequential Instructions: Generic Facts (the ALU output is a variable) --- *)

Lemma nonDeferred_of_nonSequential :
  forall pcAddrInit (env : Env (rfTree pcAddrInit)) pcc meip mtip (aluOut : type AluOutUnion) rf rf' out,
    evalIsInterruptPending pcAddrInit meip mtip rf = false ->
    aluIsSeq aluOut = false ->
    SemAction env (@executeNonSequential pcAddrInit type pcc meip mtip aluOut) rf rf' out ->
    SemAction env (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut) rf rf' out.
Proof.
  intros pcAddrInit env pcc meip mtip aluOut rf rf' out Hint Hns Hex.
  rewrite SemAction_iff_evalActionPropGen in Hex; rewrite SemAction_iff_evalActionPropGen.
  exact (proj2 (evalActionPropGen_executeNonDeferred_nonSequential pcAddrInit pcc meip mtip aluOut rf _ Hint Hns) Hex).
Qed.

(* No mulDiv output: the spec's mulDiv write-back does nothing (whatever the dataMem output) *)
Lemma specMulDivWb_noMd2 :
  forall pcAddrInit (aluOut : type AluOutUnion) (execOut : type ExecuteOut) (rf : RfState pcAddrInit),
    optValid (execMulDiv execOut) = false -> specMulDivWb pcAddrInit aluOut execOut rf = rf.
Proof.
  intros pcAddrInit aluOut execOut rf Hmd; unfold specMulDivWb, optValid in *; cbv zeta.
  destruct ((execDataMem execOut).(Snd).(Fst)); [reflexivity | rewrite Hmd; reflexivity].
Qed.

(* The non-sequential stall guard: a dataMem op needs room, a virtual CSR read a quiet dataMem *)
Lemma nonSeqGuard_dm : forall im df iv de nw, nonSeqGuardV im df iv de nw = true -> im = true -> df = false.
Proof. intros [] [] [] [] []; cbn; intros H E; first [reflexivity | discriminate H | discriminate E]. Qed.

Lemma nonSeqGuard_virt :
  forall im df iv de nw, nonSeqGuardV im df iv de nw = true -> iv = true -> andb de nw = true.
Proof. intros [] [] [] [] []; cbn; intros H E; first [reflexivity | discriminate H | discriminate E]. Qed.

Lemma or4_false :
  forall e1 e2 e3 e4 : Expr type Bool,
    evalExpr (Or [e1; e2; e3; e4]) = false ->
    evalExpr e1 = false /\ evalExpr e2 = false /\ evalExpr e3 = false /\ evalExpr e4 = false.
Proof.
  intros e1 e2 e3 e4 H.
  change (orb (orb (orb (orb false (evalExpr e1)) (evalExpr e2)) (evalExpr e3)) (evalExpr e4) = false) in H.
  destruct (evalExpr e1), (evalExpr e2), (evalExpr e3), (evalExpr e4); cbn in H; try discriminate H.
  repeat split; reflexivity.
Qed.

Lemma not_eq_addr : forall u v : type Addr, evalExpr (Not (Eq (Var type Addr u) (Var type Addr v))) = false -> u = v.
Proof.
  intros u v H; change (negb (Zmod.eqb u v) = false) in H.
  apply negb_false_iff, Zmod.eqb_eq in H; exact H.
Qed.

Lemma andb_true_l_false : forall b c : bool, b = true -> andb b c = false -> c = false.
Proof. intros b c -> H; exact H. Qed.

(* Without a redirect: no exception, no capability change, no fence.i, and the next address is
 * the predicted one *)
Lemma noRedirect_facts :
  forall (a : type AluOutUnion) (x : type ExecuteOut) (predPc : type Addr),
    execRedirect a x predPc = false ->
    aluIsExc a = false /\
    (optValid (execCf x) = true -> let cf : type CfPayload := optData (execCf x) in evalExpr (##cf`"capChanged") = false) /\
    execIsFenceIRq x = false /\
    (execNextPcc x).(Snd).(Snd).(Fst) = predPc.
Proof.
  intros a x predPc H; unfold execRedirect in H; cbv zeta in H.
  apply or4_false in H as [H1 [H2 [H3 H4]]].
  split; [exact H1 | split; [| split; [exact H3 | exact (not_eq_addr _ _ H4)]]].
  intros Hv; cbv zeta; apply (andb_true_l_false (optValid (execCf x))); [exact Hv | exact H2].
Qed.

(* ALU fact A3: an op without exception had no fetch fault (a fault gives the Exception op) *)
Lemma nonSeq_noFault :
  forall pcAddrInit (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit) (a : type AluOutUnion),
    a = evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) -> aluIsExc a = false -> foFault fo = false.
Proof.
  intros pcAddrInit pcc fo rf a Ha Hexc.
  set (pkg := evalRegRead pcAddrInit (evalDecode fo) rf) in Ha.
  destruct (foFault fo) eqn:Ef; [exfalso | reflexivity].
  pose proof (wrappedAlu_fetchExc_nonSeq pcc pkg) as T; cbv zeta in T.
  change (evalLetExpr (@wrappedAlu type pcc pkg)) with (evalAluOut pcc pkg) in T.
  rewrite <- Ha in T.
  destruct (T (excAny_or4 _ Ef)) as [_ [T2 T3]].
  lazymatch type of T2 with ?L2 = true => lazymatch type of T3 with ?L3 = true =>
    assert (E : aluIsExc a = andb (andb true L2) L3) by reflexivity;
    rewrite E, T2, T3 in Hexc; cbn in Hexc; discriminate Hexc end end.
Qed.

(* The stage's reads of a non-sequential op, in its own syntax *)
Definition nsOp (a : type AluOutUnion) : type NonSequentialUnion :=
  let aluOp : type AluOpUnion := evalExpr (##a`"Op") in
  evalExpr (#aluOp `! "NonSequential").
Definition nsNoExc (a : type AluOutUnion) : type NoExceptionUnion :=
  let nonSeq : type NonSequentialUnion := nsOp a in
  evalExpr (#nonSeq `! "NoException").
Definition nsDm (a : type AluOutUnion) : type MemFenceUnion :=
  let noExc : type NoExceptionUnion := nsNoExc a in
  evalExpr (#noExc `! "DataMem").

Lemma memOrFence_of_tags :
  forall a : type AluOutUnion,
    aluIsSeq a = false ->
    evalExpr ((Var type NonSequentialUnion (nsOp a)) `? "Exception") = false ->
    evalExpr ((Var type NoExceptionUnion (nsNoExc a)) `? "DataMem") = true ->
    aluIsMemOrFence a = true.
Proof.
  intros a Hns Hexc Hdm.
  assert (Hnsq : evalExpr ((Var type AluOpUnion (evalExpr (##a`"Op"))) `? "NonSequential") = true)
    by (apply bits1_eqb_0_false_1_true; exact Hns).
  assert (Hne : evalExpr ((Var type NonSequentialUnion (nsOp a)) `? "NoException") = true)
    by (apply bits1_eqb_0_false_1_true; exact Hexc).
  assert (E : aluIsMemOrFence a =
              andb (andb true (andb (andb true (evalExpr ((Var type AluOpUnion (evalExpr (##a`"Op"))) `? "NonSequential")))
                                    (evalExpr ((Var type NonSequentialUnion (nsOp a)) `? "NoException"))))
                   (evalExpr ((Var type NoExceptionUnion (nsNoExc a)) `? "DataMem"))) by reflexivity.
  rewrite E, Hnsq, Hne, Hdm; reflexivity.
Qed.

Lemma fenceI_mem : forall op, opIsMem op = true -> opIsFenceI op = false.
Proof. intros op H; unfold opIsFenceI; rewrite H; reflexivity. Qed.

Lemma fenceI_fence :
  forall op, opIsMem op = false -> opIsFenceI op = (let f : type FenceOp := opFenceV op in evalExpr (##f`"FenceI")).
Proof. intros op H; unfold opIsFenceI; rewrite H; reflexivity. Qed.

Lemma allReturns_IfElse_Ret_cond :
  forall {t : Tree Elem} {k : Kind} (nm : string) (p : Expr type Bool) (tb fb : Action type t k)
         (Q : type k -> Prop),
    (evalExpr p = true -> allReturns tb Q) -> (evalExpr p = false -> allReturns fb Q) ->
    allReturns (IfElse nm p tb fb (fun v => Return (Var type k v))) Q.
Proof.
  intros t k nm p tb fb Q Ht Hf; cbn [allReturns].
  destruct (evalExpr p); [exact (Ht eq_refl) | exact (Hf eq_refl)].
Qed.

Lemma allReturns_handleTrap_nf :
  forall pcAddrInit (pcc : type FullECapWithTag) (mc mt : type (Bit Xlen)) (Q : type ExecuteOut -> Prop),
    (forall r, optValid (execDataMem r) = false -> execIsFenceIRq r = false -> Q r) ->
    allReturns (@handleTrap pcAddrInit type pcc mc mt) Q.
Proof.
  intros pcAddrInit pcc mc mt Q HQ; unfold handleTrap;
    repeat (lazymatch goal with
            | |- allReturns (LetAction _ _ _) _ => simple apply allReturns_step_let; intro
            | |- allReturns (LetExp _ _ _) _ => simple apply allReturns_step_letexp
            | |- allReturns (IfElse _ _ _ _ (fun v => Return (Var _ _ v))) _ => simple apply allReturns_IfElse_Ret
            | |- allReturns (IfElse _ _ _ _ _) _ => simple apply allReturns_IfElse_any; intro
            | |- allReturns (Return _) _ => cbn [allReturns]
            end);
    apply HQ; reflexivity.
Qed.

(* The dataMem output of `executeNonSequential`: only a DataMem op makes a request (its payload),
 * and fence.i is requested exactly by a fence request with the FenceI flag *)
Lemma nonSeq_dm :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)} (pcc : type FullECapWithTag) meip mtip (a : type AluOutUnion)
         (rf rf' : RfState pcAddrInit) (x : type ExecuteOut),
    aluIsSeq a = false ->
    SemAction env (@executeNonSequential pcAddrInit type pcc meip mtip a) rf rf' x ->
    (optValid (execDataMem x) = true -> aluIsMemOrFence a = true /\ optData (execDataMem x) = nsDm a) /\
    execIsFenceIRq x = andb (optValid (execDataMem x)) (opIsFenceI (optData (execDataMem x))).
Proof.
  intros pcAddrInit env pcc meip mtip a rf rf' x Hns Hsem.
  refine (allReturns_SemAction _ rf rf' x
            (fun r => (optValid (execDataMem r) = true -> aluIsMemOrFence a = true /\ optData (execDataMem r) = nsDm a) /\
                      execIsFenceIRq r = andb (optValid (execDataMem r)) (opIsFenceI (optData (execDataMem r))))
            _ Hsem).
  unfold executeNonSequential.
  do 6 (simple apply allReturns_step_letexp).
  apply allReturns_IfElse_Ret_cond; intros Hexc.
  - do 3 (simple apply allReturns_step_letexp).
    apply allReturns_handleTrap_nf; intros r Hdm Hfi.
    split; [intros H; rewrite Hdm in H; discriminate H | rewrite Hfi, Hdm; reflexivity].
  - simple apply allReturns_step_let; intros _.
    simple apply allReturns_step_let; intros _.
    simple apply allReturns_step_letexp.
    apply allReturns_IfElse_Ret_cond; intros Hdmt.
    + simple apply allReturns_step_letexp.
      apply allReturns_IfElse_cond; intros Hmem; repeat step_allReturns.
      * split; [intros _; split; [exact (memOrFence_of_tags a Hns Hexc Hdmt) | reflexivity] |].
        exact (eq_sym (fenceI_mem _ Hmem)).
      * split; [intros _; split; [exact (memOrFence_of_tags a Hns Hexc Hdmt) | reflexivity] |].
        exact (eq_sym (fenceI_fence _ Hmem)).
    + repeat step_allReturns;
        (split; [intros H; change (false = true) in H; discriminate H | reflexivity]).
Qed.

(* The appended entry's request and fence.i flag, from the execute output *)
Lemma entryReq_exec :
  forall fo meip mtip (a : type AluOutUnion) (x : type ExecuteOut),
    optValid (execDataMem x) = true -> entryReq (mkGEntry fo meip mtip a (execDataMem x)) = Some (execDmReq a x).
Proof. intros fo meip mtip a x Hv; unfold entryReq; cbn [ge_dm ge_aluOut]; rewrite Hv; reflexivity. Qed.

Lemma entryIsFenceI_exec :
  forall fo meip mtip (a : type AluOutUnion) (x : type ExecuteOut),
    entryIsFenceI (mkGEntry fo meip mtip a (execDataMem x)) =
    andb (optValid (execDataMem x)) (opIsFenceI (optData (execDataMem x))).
Proof.
  intros fo meip mtip a x; unfold entryIsFenceI, entryReq; cbn [ge_dm ge_aluOut].
  destruct (optValid (execDataMem x)); reflexivity.
Qed.

Lemma fip_after : forall (b fip : bool) e, fip = false -> b = entryIsFenceI e -> (if b then true else fip) = entryIsFenceI e.
Proof. intros b fip e -> ->; destruct (entryIsFenceI e); reflexivity. Qed.

(* --- Non-Sequential Instructions: the Next PCC Without a Redirect --- *)

Definition nsCfScrCsr (a : type AluOutUnion) : type CfScrCsrUnion :=
  let noExc : type NoExceptionUnion := nsNoExc a in
  evalExpr (#noExc `! "CfScrCsr").
Definition nsCf (a : type AluOutUnion) : type CfPayload :=
  let cfScrCsr : type CfScrCsrUnion := nsCfScrCsr a in
  evalExpr (#cfScrCsr `! "ControlFlow").
(* the op is a ControlFlow op (given no exception) *)
Definition nsIsCf (a : type AluOutUnion) : bool :=
  let noExc : type NoExceptionUnion := nsNoExc a in
  let cfScrCsr : type CfScrCsrUnion := nsCfScrCsr a in
  andb (negb (evalExpr (#noExc `? "DataMem"))) (negb (evalExpr (#cfScrCsr `? "ScrCsr"))).

(* ALU fact A2 (to be proven from the ControlFlow unit): a ControlFlow payload that does not change
 * the capability keeps the PCC's tag (taken branch, jal) and is a jalr with the PCC's tag and
 * ecap otherwise (an mret always changes it) *)
Definition CfOK (pcc : type FullECapWithTag) (cf : type CfPayload) : Prop :=
  let newPcc : type FullECapWithTag := evalExpr (##cf`"NewPcc") in
  let cfOp : type CfOp := evalExpr (##cf`"CfOp") in
  let ao : type ControlFlowAddrOnlyOp := evalExpr (#cfOp `! "ControlFlowAddrOnly") in
  let ae : type ControlFlowAddrECap := evalExpr (#cfOp `! "ControlFlowAddrECap") in
  let aeOp : type ControlFlowAddrECapOp := evalExpr (##ae`"op") in
  evalExpr (##cf`"capChanged") = false ->
  (evalExpr (#cfOp `? "ControlFlowAddrOnly") = true ->
     (evalExpr (#ao `? "Branch") = true -> evalExpr (#ao `! "Branch") = true -> newPcc.(Fst) = pcc.(Fst)) /\
     (evalExpr (#ao `? "Branch") = false -> newPcc.(Fst) = pcc.(Fst))) /\
  (evalExpr (#cfOp `? "ControlFlowAddrOnly") = false ->
     evalExpr (#aeOp `? "Cjalr") = true /\ newPcc.(Fst) = pcc.(Fst) /\ newPcc.(Snd).(Fst) = pcc.(Snd).(Fst)).

Lemma getSeqPcc_keep :
  forall (pcc : type FullECapWithTag) (b : bool),
    (evalExpr (@Alu.getSeqPcc type pcc b)).(Fst) = pcc.(Fst) /\
    (evalExpr (@Alu.getSeqPcc type pcc b)).(Snd).(Fst) = pcc.(Snd).(Fst).
Proof. intros [t [e [ad u]]] b; destruct u; split; reflexivity. Qed.

Lemma exc_of_tags :
  forall a : type AluOutUnion,
    aluIsSeq a = false -> evalExpr ((Var type NonSequentialUnion (nsOp a)) `? "Exception") = true -> aluIsExc a = true.
Proof.
  intros a Hns Hexc.
  assert (Hnsq : evalExpr ((Var type AluOpUnion (evalExpr (##a`"Op"))) `? "NonSequential") = true)
    by (apply bits1_eqb_0_false_1_true; exact Hns).
  assert (E : aluIsExc a = andb (andb true (evalExpr ((Var type AluOpUnion (evalExpr (##a`"Op"))) `? "NonSequential")))
                                (evalExpr ((Var type NonSequentialUnion (nsOp a)) `? "Exception"))) by reflexivity.
  rewrite E, Hnsq, Hexc; reflexivity.
Qed.

Lemma isCf_of_tags :
  forall a : type AluOutUnion,
    evalExpr ((Var type NoExceptionUnion (nsNoExc a)) `? "DataMem") = false ->
    evalExpr ((Var type CfScrCsrUnion (nsCfScrCsr a)) `? "ScrCsr") = false ->
    nsIsCf a = true.
Proof.
  intros a H1 H2.
  assert (E : nsIsCf a = andb (negb (evalExpr ((Var type NoExceptionUnion (nsNoExc a)) `? "DataMem")))
                              (negb (evalExpr ((Var type CfScrCsrUnion (nsCfScrCsr a)) `? "ScrCsr")))) by reflexivity.
  rewrite E, H1, H2; reflexivity.
Qed.

(* An mret payload changes the capability (over a variable payload, so the conversion through
 * the NewPcc update stays cheap) *)
Lemma mret_contra :
  forall (pcc : type FullECapWithTag) (cf : type CfPayload) (mePcc : type FullECapWithTag),
    CfOK pcc cf ->
    (let cfOp : type CfOp := evalExpr (##cf`"CfOp") in evalExpr (#cfOp `? "ControlFlowAddrOnly") = false) ->
    (let cfOp : type CfOp := evalExpr (##cf`"CfOp") in
     let ae : type ControlFlowAddrECap := evalExpr (#cfOp `! "ControlFlowAddrECap") in
     let aeOp : type ControlFlowAddrECapOp := evalExpr (##ae`"op") in
     evalExpr (#aeOp `? "Cjalr") = false) ->
    (let cfo : type CfPayload := evalExpr ((Var type CfPayload cf) `{ "NewPcc" <- Var type FullECapWithTag mePcc }) in
     evalExpr (##cfo`"capChanged") = false) ->
    False.
Proof.
  intros pcc cf mePcc Hok Hao Hcj Hcc; cbv zeta in Hao, Hcj, Hcc.
  destruct (proj2 (Hok Hcc) Hao) as [Hcj' _].
  rewrite Hcj in Hcj'; discriminate Hcj'.
Qed.

(* Without a redirect the next PCC keeps the PCC's tag and ecap *)
Lemma nonSeq_pcc :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)} (pcc : type FullECapWithTag) meip mtip (a : type AluOutUnion)
         (rf rf' : RfState pcAddrInit) (x : type ExecuteOut) (predPc : type Addr),
    aluIsSeq a = false ->
    (nsIsCf a = true -> CfOK pcc (nsCf a)) ->
    SemAction env (@executeNonSequential pcAddrInit type pcc meip mtip a) rf rf' x ->
    execRedirect a x predPc = false ->
    (execNextPcc x).(Fst) = pcc.(Fst) /\ (execNextPcc x).(Snd).(Fst) = pcc.(Snd).(Fst).
Proof.
  intros pcAddrInit env pcc meip mtip a rf rf' x predPc Hns Hcf Hsem.
  refine (allReturns_SemAction _ rf rf' x
            (fun r => execRedirect a r predPc = false ->
                      (execNextPcc r).(Fst) = pcc.(Fst) /\ (execNextPcc r).(Snd).(Fst) = pcc.(Snd).(Fst)) _ Hsem).
  unfold executeNonSequential.
  do 6 (simple apply allReturns_step_letexp).
  apply allReturns_IfElse_Ret_cond; intros Hexc.
  - (* an exception redirects *)
    do 3 (simple apply allReturns_step_letexp).
    apply allReturns_handleTrap_nf; intros r _ _ Hr; exfalso.
    destruct (noRedirect_facts a r predPc Hr) as [Hx _].
    rewrite (exc_of_tags a Hns Hexc) in Hx; discriminate Hx.
  - simple apply allReturns_step_let; intros _.
    simple apply allReturns_step_let; intros _.
    simple apply allReturns_step_letexp.
    apply allReturns_IfElse_Ret_cond; intros Hdmt.
    + repeat step_allReturns; intros _; exact (getSeqPcc_keep pcc a.(Fst)).
    + simple apply allReturns_step_letexp.
      apply allReturns_IfElse_Ret_cond; intros Hsc.
      * repeat step_allReturns; intros _; exact (getSeqPcc_keep pcc a.(Fst)).
      * pose proof (Hcf (isCf_of_tags a Hdmt Hsc)) as Hok0; pose proof Hok0 as Hok.
        unfold CfOK in Hok; cbv zeta in Hok.
        do 4 (simple apply allReturns_step_letexp).
        simple apply allReturns_step_let; intros ?.
        simple apply allReturns_IfElse_any; intros _.
        apply allReturns_IfElse_Ret_cond; intros Hao.
        -- simple apply allReturns_step_letexp.
           apply allReturns_IfElse_cond; intros Hbr; repeat step_allReturns; intros Hr;
             destruct (noRedirect_facts a _ predPc Hr) as [_ [Hcc _]];
             destruct (proj1 (Hok (Hcc eq_refl)) Hao) as [Hb Hj].
           ++ match goal with |- context [evalExpr (ITE (Var _ _ ?t) _ _)] => destruct t eqn:Et end.
              ** split; [exact (Hb Hbr Et) | reflexivity].
              ** exact (getSeqPcc_keep pcc a.(Fst)).
           ++ split; [exact (Hj Hbr) | reflexivity].
        -- do 2 (simple apply allReturns_step_letexp).
           apply allReturns_IfElse_Ret_cond; intros Hcj.
           ++ repeat step_allReturns; intros Hr; destruct (noRedirect_facts a _ predPc Hr) as [_ [Hcc _]].
              destruct (proj2 (Hok (Hcc eq_refl)) Hao) as [_ [Ht He]]; split; [exact Ht | exact He].
           ++ simple apply allReturns_step_let; intros mePcc.
              repeat step_allReturns; intros Hr; destruct (noRedirect_facts a _ predPc Hr) as [_ [Hcc _]].
              exfalso; exact (mret_contra pcc (nsCf a) mePcc Hok0 Hao Hcj (Hcc eq_refl)).
Qed.

(* Virtual CSR tests. Comparing the stage's `And` shape with an `andb` shape by conversion is
 * exponential in the depth (12 s at 6 levels), so `virtCsr_eq` first rewrites `And` into `andb`
 * with `evalExpr_And2` (proven over variables) and then compares equal shapes. *)
Lemma evalExpr_And2 :
  forall (x : bool) (y : Expr type Bool), evalExpr (And [Var type Bool x; y]) = andb x (evalExpr y).
Proof. intros x y; reflexivity. Qed.

Lemma bits1_eqb_0_true_1_false :
  forall (b : bits 1), Zmod.eqb b (Zmod.of_Z (2 ^ 1) 0) = true -> Zmod.eqb b (Zmod.of_Z (2 ^ 1) 1) = false.
Proof. intros b Hb; apply Zmod.eqb_eq in Hb; subst b; reflexivity. Qed.

Definition vcScr (a : type AluOutUnion) : type ScrCsrPayload :=
  let c : type CfScrCsrUnion := nsCfScrCsr a in evalExpr (#c `! "ScrCsr").
Definition vcDest (a : type AluOutUnion) : type (TaggedUnion ScrCsrIdx) :=
  let s : type ScrCsrPayload := vcScr a in evalExpr (##s`"SpecialDest").

(* The stage's virtual CSR test is the relation's `isVirtualCsrAluOut` *)
Lemma virtCsr_eq : forall a : type AluOutUnion, aluIsVirtCsr a = isVirtualCsrAluOut a.
Proof.
  intros a; unfold aluIsVirtCsr, isVirtualCsrAluOut; cbv beta zeta.
  rewrite !evalExpr_And2; reflexivity.
Qed.

(* A dataMem op is not a virtual CSR read (the NoException tags DataMem and CfScrCsr exclude each
 * other) *)
Lemma memOrFence_virt_excl :
  forall a : type AluOutUnion, aluIsMemOrFence a = true -> aluIsVirtCsr a = false.
Proof.
  intros a H.
  pose (ns := evalExpr ((Var type AluOpUnion (evalExpr (##a`"Op"))) `? "NonSequential")).
  pose (ne := evalExpr ((Var type NonSequentialUnion (nsOp a)) `? "NoException")).
  pose (dm := evalExpr ((Var type NoExceptionUnion (nsNoExc a)) `? "DataMem")).
  pose (cs := evalExpr ((Var type NoExceptionUnion (nsNoExc a)) `? "CfScrCsr")).
  pose (sc := evalExpr ((Var type CfScrCsrUnion (nsCfScrCsr a)) `? "ScrCsr")).
  pose (csr := evalExpr ((Var type (TaggedUnion ScrCsrIdx) (vcDest a)) `? "Csr")).
  pose (v := evalExpr (@csrIdxIsVirtual type (evalExpr ((Var type (TaggedUnion ScrCsrIdx) (vcDest a)) `! "Csr")))).
  assert (E : aluIsMemOrFence a = andb (andb true (andb (andb true ns) ne)) dm) by reflexivity.
  assert (Hdm : dm = true) by (rewrite E in H; apply andb_true_iff in H as [_ H]; exact H).
  assert (Hcs : cs = false) by (apply bits1_eqb_0_true_1_false; exact Hdm).
  assert (E2 : isVirtualCsrAluOut a = andb (andb (andb (andb (andb ns ne) cs) sc) csr) v) by reflexivity.
  rewrite virtCsr_eq, E2, Hcs, andb_false_r; reflexivity.
Qed.

(* ALU fact A1, ALU part: with no exception and a valid dataMem output, the op is the DataMem op
 * and carries the routing's payload (the op equation by `reflexivity`, then three readbacks) *)
Lemma alu_dm_payload :
  forall ro : type AluOut,
    ro.(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = false ->
    ro.(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true ->
    nsDm (evalLetExpr (@Alu type ro)) = ro.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).
Proof.
  intros ro He Hd.
  destruct ro as [isComp [dstIdx [dstValue [[excD [excV []]] [[dmD [dmV []]] [md [cf [sc []]]]]]]]].
  cbn [Fst Snd] in He, Hd |- *; subst excV dmV.
  unfold nsDm, nsNoExc, nsOp; cbv zeta.
  set (A := evalLetExpr (@Alu type _)).
  assert (Eop : evalExpr (##A`"Op") =
                evalExpr (UNION (AluOpUnionType, "NonSequential" ::=
                  Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "NoException" ::=
                    Var type NoExceptionUnion (evalExpr (UNION (NoExceptionUnionType, "DataMem" ::=
                      Var type MemFenceUnion dmD))))))))) by reflexivity.
  rewrite Eop; readback; readback; readback; reflexivity.
Qed.

(* ALU fact A1, ALU part: a DataMem op means no exception and a valid dataMem output *)
Lemma alu_memOrFence_valid :
  forall ro : type AluOut,
    aluIsMemOrFence (evalLetExpr (@Alu type ro)) = true ->
    ro.(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = false /\ ro.(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true.
Proof.
  intros ro.
  destruct ro as [isComp [dstIdx [dstValue [[excD [excV []]] [[dmD [dmV []]] [md [[cfD [cfV []]] [[scD [scV []]] []]]]]]]]].
  cbn [Fst Snd].
  destruct excV.
  - intros H; exfalso; revert H; unfold aluIsMemOrFence; cbv zeta.
    set (A := evalLetExpr (@Alu type _)).
    assert (Eop : evalExpr (##A`"Op") =
                  evalExpr (UNION (AluOpUnionType, "NonSequential" ::=
                    Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "Exception" ::=
                      Var type ExceptionInfo excD)))))) by reflexivity.
    rewrite Eop; readback; intros H; tag_contra H.
  - destruct dmV; [intros _; split; reflexivity | intros H; exfalso; revert H].
    unfold aluIsMemOrFence; cbv zeta.
    set (A := evalLetExpr (@Alu type _)).
    destruct cfV; [| destruct scV].
    + assert (Eop : evalExpr (##A`"Op") =
                    evalExpr (UNION (AluOpUnionType, "NonSequential" ::=
                      Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "NoException" ::=
                        Var type NoExceptionUnion (evalExpr (UNION (NoExceptionUnionType, "CfScrCsr" ::=
                          Var type CfScrCsrUnion (evalExpr (ITE (Var type Bool true)
                            (UNION (CfScrCsrType, "ControlFlow" ::= Var type CfPayload cfD))
                            (UNION (CfScrCsrType, "ScrCsr" ::= Var type ScrCsrPayload scD)))))))))))))
        by reflexivity.
      rewrite Eop; readback; readback; intros H; tag_contra H.
    + assert (Eop : evalExpr (##A`"Op") =
                    evalExpr (UNION (AluOpUnionType, "NonSequential" ::=
                      Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "NoException" ::=
                        Var type NoExceptionUnion (evalExpr (UNION (NoExceptionUnionType, "CfScrCsr" ::=
                          Var type CfScrCsrUnion (evalExpr (ITE (Var type Bool false)
                            (UNION (CfScrCsrType, "ControlFlow" ::= Var type CfPayload cfD))
                            (UNION (CfScrCsrType, "ScrCsr" ::= Var type ScrCsrPayload scD)))))))))))))
        by reflexivity.
      rewrite Eop; readback; readback; intros H; tag_contra H.
    + intros H; tag_contra H.
Qed.

(* ALU fact A1, DataMem part: neither a store nor a fence gives a load payload *)
Lemma dm_unit_load :
  forall (isLoad : bool) (cs1Perms cs2Perms : type CapPerms) (instv : type (Bit Xlen)) (storeTag : bool)
         (storeCap : type Cap) (cs2Addr : type Addr),
    opIsLoad (evalLetExpr (@DataMem type isLoad false false cs1Perms cs2Perms instv storeTag storeCap cs2Addr)).(Fst) = true.
Proof.
  intros isLoad cs1Perms cs2Perms instv storeTag storeCap cs2Addr.
  pose (M := evalLetExpr (@LoadStore type cs1Perms cs2Perms (evalExpr (@getMemSize type instv))
                            (evalExpr (FromBit Bool ((Var type (Bit Xlen) instv)`[14:14]))) isLoad false storeTag storeCap cs2Addr)).
  assert (Ed : (evalLetExpr (@DataMem type isLoad false false cs1Perms cs2Perms instv storeTag storeCap cs2Addr)).(Fst) =
               evalExpr (UNION (MemFenceType, "Mem" ::= Var type MemPayload M))) by reflexivity.
  rewrite Ed; unfold opIsLoad, opMemPayload; cbv zeta.
  readback; reflexivity.
Qed.

Lemma dm_unit_load' :
  forall (l s f : bool) (c1 c2 : type CapPerms) (i : type (Bit Xlen)) (t : bool) (cap : type Cap) (a : type Addr),
    s = false -> f = false -> opIsLoad (evalLetExpr (@DataMem type l s f c1 c2 i t cap a)).(Fst) = true.
Proof. intros l s f c1 c2 i t cap a -> ->; apply dm_unit_load. Qed.

(* ALU fact A1, ALU and routing parts: the destination index passes through the ALU; the routing
 * zeroes it unless writesCd; without the store and fence flags the dataMem payload is a load *)
Lemma alu_dstIdx : forall ro : type AluOut, aluDstIdx (evalLetExpr (@Alu type ro)) = ro.(Snd).(Fst).
Proof. intros ro; reflexivity. Qed.

Lemma routing_dstIdx :
  forall (pcc : type FullECapWithTag) (aluIn : type AluIn),
    aluIn.(Snd).(Snd).(Fst) = false -> (evalLetExpr (@AluRouting type pcc aluIn)).(Snd).(Fst) = Zmod.zero.
Proof.
  intros pcc aluIn H.
  destruct aluIn as [rs [rc [wcd [inst0 [dexc [fexc [cs1 [cs2 [ctrl0 []]]]]]]]]].
  cbn [Fst Snd] in H; subst wcd; reflexivity.
Qed.

Lemma routing_dm_load :
  forall (pcc : type FullECapWithTag) (aluIn : type AluIn),
    let ctrl : type AluControl := evalExpr (##aluIn`"aluControl") in
    evalExpr (##ctrl`"Store") = false -> evalExpr (##ctrl`"DataMem_isFence") = false ->
    opIsLoad ((evalLetExpr (@AluRouting type pcc aluIn)).(Snd).(Snd).(Snd).(Snd).(Fst)).(Fst) = true.
Proof.
  intros pcc aluIn; cbv zeta; intros Hs Hf.
  apply dm_unit_load'; [exact Hs | exact Hf].
Qed.

(* ALU fact A1, plumbing: constructAluIn and the register read copy the decoder's fields *)
Lemma constructAluIn_facts :
  forall pkg : type AluInInstGroup,
    let aluIn : type AluIn := evalLetExpr (@constructAluIn type pkg) in
    let ctrl : type AluControl := evalExpr (##aluIn`"aluControl") in
    let grp : type InstGroup := evalExpr (##pkg`"instGroup") in
    aluIn.(Snd).(Snd).(Fst) = evalExpr (##pkg`"writesCd") /\
    evalExpr (##ctrl`"Store") = evalExpr (##grp`"Store") /\
    evalExpr (##ctrl`"DataMem_isFence") = evalExpr (##grp`"Fence").
Proof. intros pkg aluIn ctrl grp; split; [| split]; reflexivity. Qed.

Lemma regRead_facts :
  forall pcAddrInit (rri : type RegReadIn) (rf : RfState pcAddrInit),
    let pkg : type AluInInstGroup := evalRegRead pcAddrInit rri rf in
    let dout : type DecodeOut := evalExpr (##rri`"decodeOut") in
    evalExpr (##pkg`"writesCd") = evalExpr (##dout`"writesCd") /\
    evalExpr (##pkg`"instGroup") = evalExpr (##dout`"instGroup").
Proof. intros pcAddrInit rri rf pkg dout; split; reflexivity. Qed.

Lemma bool_wcd :
  forall nz br st fe ec eb mr : bool,
    andb (andb true nz) (negb (orb (orb (orb (orb (orb (orb false br) st) fe) ec) eb) mr)) = true ->
    st = false /\ fe = false.
Proof. intros [] [] [] [] [] [] []; cbn; intros H; first [discriminate H | split; reflexivity]. Qed.

(* ALU fact A1, decoder part: writesCd excludes stores and fences (Decoder.v line 259) *)
Lemma decode_writesCd :
  forall fo : type FetchOut,
    let rri : type RegReadIn := evalDecode fo in
    let dout : type DecodeOut := evalExpr (##rri`"decodeOut") in
    let grp : type InstGroup := evalExpr (##dout`"instGroup") in
    evalExpr (##dout`"writesCd") = true -> evalExpr (##grp`"Store") = false /\ evalExpr (##grp`"Fence") = false.
Proof.
  intros fo rri dout grp H.
  assert (E : evalExpr (##dout`"writesCd") =
              andb (andb true (evalExpr (isNotZero (Var type (Bit RegIdxSzReal)
                     (evalExpr (TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal
                        (Var type (Bit RegIdxSz) (evalExpr (@getCd type (evalExpr (##fo`"inst")))))))))))
                   (negb (orb (orb (orb (orb (orb (orb false (evalExpr (##grp`"Branch"))) (evalExpr (##grp`"Store")))
                      (evalExpr (##grp`"Fence"))) (evalExpr (##grp`"ECall"))) (evalExpr (##grp`"EBreak")))
                      (evalExpr (##grp`"Mret"))))) by reflexivity.
  rewrite E in H; exact (bool_wcd _ _ _ _ _ _ _ H).
Qed.

(* ALU fact A1: a dataMem request that is not a load has destination 0 (the decoder's writesCd
 * excludes stores and fences; the routing zeroes the destination unless writesCd) *)
Lemma aluFact_A1 :
  forall pcAddrInit (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit),
    let a := evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) in
    aluIsMemOrFence a = true -> opIsLoad (nsDm a) = false -> aluDstIdx a = Zmod.zero.
Proof.
  intros pcAddrInit pcc fo rf; cbv zeta.
  unfold evalAluOut; rewrite df_wrappedAlu_unfold.
  pose proof (regRead_facts pcAddrInit (evalDecode fo) rf) as [Rw Rg]; cbv zeta in Rw, Rg.
  pose proof (constructAluIn_facts (evalRegRead pcAddrInit (evalDecode fo) rf)) as [Cw [Cs Cf]];
    cbv zeta in Cw, Cs, Cf.
  pose proof (decode_writesCd fo) as D; cbv zeta in D.
  set (ro := evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type (evalRegRead pcAddrInit (evalDecode fo) rf))))).
  intros Hmf Hnl.
  rewrite alu_dstIdx.
  destruct (alu_memOrFence_valid ro Hmf) as [He Hd].
  rewrite (alu_dm_payload ro He Hd) in Hnl.
  match type of D with ?W = true -> _ =>
    assert (Hdec : W = true \/ W = false) by (destruct W; [left | right]; reflexivity) end.
  destruct Hdec as [Ew | Ew].
  - destruct (D Ew) as [Ds Df]; exfalso.
    assert (Hl : opIsLoad (ro.(Snd).(Snd).(Snd).(Snd).(Fst)).(Fst) = true).
    { apply routing_dm_load; [rewrite Cs, Rg; exact Ds | rewrite Cf, Rg; exact Df]. }
    rewrite Hl in Hnl; discriminate Hnl.
  - apply routing_dstIdx; rewrite Cw, Rw; exact Ew.
Qed.

(* ALU fact A2, ALU part: a ControlFlow op (not sequential, no exception) means no exception, no
 * dataMem output and a valid ControlFlow output, and it carries the routing's payload *)
Lemma alu_cf_valid :
  forall ro : type AluOut,
    let a := evalLetExpr (@Alu type ro) in
    aluIsSeq a = false -> aluIsExc a = false -> nsIsCf a = true ->
    ro.(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = false /\ ro.(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = false /\
    ro.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true.
Proof.
  intros ro; cbv zeta.
  destruct ro as [isComp [dstIdx [dstValue [[excD [excV []]] [[dmD [dmV []]] [md [[cfD [cfV []]] [[scD [scV []]] []]]]]]]]].
  cbn [Fst Snd].
  destruct excV.
  - intros _ He _; exfalso; revert He; unfold aluIsExc; cbv zeta.
    set (A := evalLetExpr (@Alu type _)).
    assert (Eop : evalExpr (##A`"Op") =
      evalExpr (UNION (AluOpUnionType, "NonSequential" ::= Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "Exception" ::= Var type ExceptionInfo excD)))))) by reflexivity.
    rewrite Eop; readback; intros He; tag_contra He.
  - destruct dmV.
    + intros _ _ Hc; exfalso; revert Hc; unfold nsIsCf, nsCfScrCsr, nsNoExc, nsOp; cbv zeta.
      set (A := evalLetExpr (@Alu type _)).
    assert (Eop : evalExpr (##A`"Op") =
      evalExpr (UNION (AluOpUnionType, "NonSequential" ::= Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "NoException" ::= Var type NoExceptionUnion (evalExpr (UNION (NoExceptionUnionType, "DataMem" ::= Var type MemFenceUnion dmD))))))))) by reflexivity.
      rewrite Eop; readback; readback; intros Hc; tag_contra Hc.
    + destruct cfV; [intros _ _ _; split; [| split]; reflexivity |].
      destruct scV.
      * intros _ _ Hc; exfalso; revert Hc; unfold nsIsCf, nsCfScrCsr, nsNoExc, nsOp; cbv zeta.
        set (A := evalLetExpr (@Alu type _)).
    assert (Eop : evalExpr (##A`"Op") =
      evalExpr (UNION (AluOpUnionType, "NonSequential" ::= Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "NoException" ::= Var type NoExceptionUnion (evalExpr (UNION (NoExceptionUnionType, "CfScrCsr" ::= Var type CfScrCsrUnion (evalExpr (UNION (CfScrCsrType, "ScrCsr" ::= Var type ScrCsrPayload scD)))))))))))) by reflexivity.
        rewrite Eop; readback; readback; readback; intros Hc; tag_contra Hc.
      * intros Hs _ _; exfalso; tag_contra Hs.
Qed.

Lemma alu_cf_payload :
  forall ro : type AluOut,
    ro.(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = false ->
    ro.(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = false ->
    ro.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true ->
    nsCf (evalLetExpr (@Alu type ro)) = ro.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).
Proof.
  intros ro He Hd Hc.
  destruct ro as [isComp [dstIdx [dstValue [[excD [excV []]] [[dmD [dmV []]] [md [[cfD [cfV []]] [sc0 []]]]]]]]].
  cbn [Fst Snd] in He, Hd, Hc |- *; subst excV dmV cfV.
  unfold nsCf, nsCfScrCsr, nsNoExc, nsOp; cbv zeta.
  set (A := evalLetExpr (@Alu type _)).
    assert (Eop : evalExpr (##A`"Op") =
      evalExpr (UNION (AluOpUnionType, "NonSequential" ::= Var type NonSequentialUnion (evalExpr (UNION (NonSequentialUnionType, "NoException" ::= Var type NoExceptionUnion (evalExpr (UNION (NoExceptionUnionType, "CfScrCsr" ::= Var type CfScrCsrUnion (evalExpr (UNION (CfScrCsrType, "ControlFlow" ::= Var type CfPayload cfD)))))))))))) by reflexivity.
  rewrite Eop; readback; readback; readback; readback; reflexivity.
Qed.

Lemma isEq_true : forall k (x y : type k), @isEq k x y = true -> x = y.
Proof. intros k x y H; destruct (isEq_BoolSpec x y) as [E | E]; [exact E | discriminate H]. Qed.

(* ALU fact A2, ControlFlow unit: a jalr (no branch, no jal) has the Cjalr AddrECap op *)
Lemma cf_unit_cjalr :
  forall (isMret isCond : bool) (addrIn : type Addr) (inBounds cjalrTag : bool) (cjalrEcap : type ECap)
         (cjalrIntStatus : type (Option Bool)) (pccTag : bool) (pccEcap : type ECap) (instv : type Inst),
    let cf : type CfPayload := (evalLetExpr (@ControlFlow type isMret false true false isCond addrIn inBounds cjalrTag
                                  cjalrEcap cjalrIntStatus pccTag pccEcap instv)).(Fst) in
    let cfOp : type CfOp := evalExpr (##cf`"CfOp") in
    let ae : type ControlFlowAddrECap := evalExpr (#cfOp `! "ControlFlowAddrECap") in
    let aeOp : type ControlFlowAddrECapOp := evalExpr (##ae`"op") in
    evalExpr (#aeOp `? "Cjalr") = true.
Proof.
  intros isMret isCond addrIn inBounds cjalrTag cjalrEcap cjalrIntStatus pccTag pccEcap instv.
  assert (Eop : let cf : type CfPayload := (evalLetExpr (@ControlFlow type isMret false true false isCond addrIn
                    inBounds cjalrTag cjalrEcap cjalrIntStatus pccTag pccEcap instv)).(Fst) in
                evalExpr (##cf`"CfOp") = evalExpr (UNION (CfOpType, "ControlFlowAddrECap" ::= Var type ControlFlowAddrECap (evalExpr (STRUCT { "interruptStatus" ::= Var type (Option Bool) cjalrIntStatus ; "op" ::= ITE (Var type Bool true) (UNION (ControlFlowAddrECapOpType, "Cjalr" ::= Var type CjalrOp (evalExpr (STRUCT { "isCall" ::= Eq (@getCd type instv) $Cra ; "isReturn" ::= And [ isZero (@getCd type instv) ; Eq (@getCs1 type instv) $Cra ] })))) (UNION (ControlFlowAddrECapOpType, "Mret" ::= Const type (Bit 0) Zmod.zero)) }))))) by reflexivity.
  cbv zeta in Eop |- *; rewrite Eop; readback; reflexivity.
Qed.

(* ALU fact A2, ControlFlow unit: the fields CfOK reads, over variables *)
Lemma cf_unit_eqs :
  forall (pcc : type FullECapWithTag) (isMret isCjal isCjalr isBranch isCond : bool) (addrIn : type Addr)
         (inBounds cjalrTag : bool) (cjalrEcap : type ECap) (cjalrIntStatus : type (Option Bool)) (instv : type Inst),
    let out := evalLetExpr (@ControlFlow type isMret isCjal isCjalr isBranch isCond addrIn inBounds cjalrTag
                              cjalrEcap cjalrIntStatus pcc.(Fst) pcc.(Snd).(Fst) instv) in
    let cf : type CfPayload := out.(Fst) in
    let newPcc : type FullECapWithTag := evalExpr (##cf`"NewPcc") in
    let pto : bool := evalExpr (caseDefault (k := Bool)
                        [ (Or [ Var type Bool isBranch ; Var type Bool isCjal ], Var type Bool inBounds) ;
                          (Var type Bool isCjalr, Var type Bool cjalrTag) ] (Var type Bool pcc.(Fst))) in
    let taken : bool := orb (orb (orb false (andb (andb true isBranch) isCond)) isCjal) isCjalr in
    out.(Snd).(Fst) = orb (orb (orb (orb false isBranch) isCjal) isCjalr) isMret /\
    newPcc.(Fst) = pto /\ newPcc.(Snd).(Fst) = cjalrEcap /\
    evalExpr (##cf`"capChanged") =
      orb (orb (orb false (andb (andb true taken) (negb (@isEq Bool pto pcc.(Fst)))))
               (andb (andb true isCjalr) (negb (@isEq ECap cjalrEcap pcc.(Snd).(Fst))))) isMret.
Proof. intros; split; [| split; [| split]]; reflexivity. Qed.

Lemma andb_negb_false : forall b p : bool, b = true -> andb (andb true b) (negb p) = false -> p = true.
Proof. intros b p -> H; destruct p; [reflexivity | discriminate H]. Qed.

(* `readback` with the payload's kind taken from the union (a constant payload has no inferable kind) *)
Ltac readback2 :=
  match goal with |- context [evalExpr (@ReadUnionData _ ?ls (Var ?ty ?k ?u) ?i)] =>
    let w := strip_var u in
    lazymatch w with evalExpr (BuildUnion _ (Var ?ty2 ?k2 ?x)) =>
      replace (evalExpr (@ReadUnionData _ ls (Var ty k u) i)) with x
        by (symmetry; exact (evalExpr_ReadUnionData_BuildUnion ls i (Var ty2 k2 x) eq_refl))
    end
  end.

Ltac cf_taken Ht := intros _; split; [intros _ _ | intros _];
  apply (isEq_true Bool); exact (andb_negb_false _ _ eq_refl Ht).

(* ALU fact A2, ControlFlow unit: a valid payload satisfies CfOK *)
Lemma cf_unit_ok :
  forall (pcc : type FullECapWithTag) (isMret isCjal isCjalr isBranch isCond : bool) (addrIn : type Addr)
         (inBounds cjalrTag : bool) (cjalrEcap : type ECap) (cjalrIntStatus : type (Option Bool)) (instv : type Inst),
    let out := evalLetExpr (@ControlFlow type isMret isCjal isCjalr isBranch isCond addrIn inBounds cjalrTag
                              cjalrEcap cjalrIntStatus pcc.(Fst) pcc.(Snd).(Fst) instv) in
    out.(Snd).(Fst) = true -> CfOK pcc out.(Fst).
Proof.
  intros pcc isMret isCjal isCjalr isBranch isCond addrIn inBounds cjalrTag cjalrEcap cjalrIntStatus instv.
  destruct (cf_unit_eqs pcc isMret isCjal isCjalr isBranch isCond addrIn inBounds cjalrTag cjalrEcap cjalrIntStatus instv)
    as [Ev [Et [Ee Ecc]]].
  cbv zeta in Ev, Et, Ee, Ecc |- *; intros Hv.
  unfold CfOK; cbv zeta; intros Hcc.
  rewrite Ecc in Hcc; rewrite Et, Ee.
  apply orb_false_iff in Hcc as [Hcc Hm]; apply orb_false_iff in Hcc as [Hcc He].
  apply orb_false_iff in Hcc as [_ Ht].
  subst isMret.
  destruct isBranch, isCjal, isCjalr.
  - destruct isCond; (split; [cf_taken Ht | intros H; exfalso; tag_contra H]).
  - destruct isCond; (split; [cf_taken Ht | intros H; exfalso; tag_contra H]).
  - destruct isCond; (split; [cf_taken Ht | intros H; exfalso; tag_contra H]).
  - destruct isCond; [split; [cf_taken Ht | intros H; exfalso; tag_contra H] |].
    split; [| intros H; exfalso; tag_contra H].
    assert (Eop : let cf : type CfPayload := (evalLetExpr (@ControlFlow type false false false true false addrIn
                      inBounds cjalrTag cjalrEcap cjalrIntStatus pcc.(Fst) pcc.(Snd).(Fst) instv)).(Fst) in
                  evalExpr (##cf`"CfOp") = evalExpr (UNION (CfOpType, "ControlFlowAddrOnly" ::= Var type ControlFlowAddrOnlyOp (evalExpr (UNION (ControlFlowAddrOnlyOpType, "Branch" ::= Var type Bool false)))))) by reflexivity.
    cbv zeta in Eop; rewrite Eop; readback; readback2.
    intros _; split; [intros _ H; discriminate H | intros H; exfalso; tag_contra H].
  - split; [cf_taken Ht | intros H; exfalso; tag_contra H].
  - split; [cf_taken Ht | intros H; exfalso; tag_contra H].
  - split; [intros H; exfalso; tag_contra H |].
    intros _; split; [exact (cf_unit_cjalr false isCond addrIn inBounds cjalrTag cjalrEcap cjalrIntStatus
                               pcc.(Fst) pcc.(Snd).(Fst) instv) |].
    split; [apply (isEq_true Bool); exact (andb_negb_false _ _ eq_refl Ht)
           | apply (isEq_true ECap); exact (andb_negb_false _ _ eq_refl He)].
  - exfalso; rewrite Ev in Hv; cbn in Hv; discriminate Hv.
Qed.

(* ALU fact A2, routing part: the routing's ControlFlow output is the unit applied to the PCC
 * (the unit is opaque here, so unification stops at its application instead of evaluating it) *)
Local Strategy opaque [ControlFlow].
Lemma routing_cf_ok :
  forall (pcc : type FullECapWithTag) (aluIn : type AluIn),
    let cfo : type (Option CfPayload) := (evalLetExpr (@AluRouting type pcc aluIn)).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) in
    cfo.(Snd).(Fst) = true -> CfOK pcc cfo.(Fst).
Proof.
  intros pcc aluIn; cbv zeta.
  Timeout 20 apply cf_unit_ok.
Qed.
Local Strategy transparent [ControlFlow].

(* ALU fact A2: a ControlFlow op without capability change keeps the PCC's tag (and ecap for jalr) *)
Lemma aluFact_A2 :
  forall pcAddrInit (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit),
    let a := evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) in
    aluIsSeq a = false -> aluIsExc a = false -> nsIsCf a = true -> CfOK pcc (nsCf a).
Proof.
  intros pcAddrInit pcc fo rf; cbv zeta.
  unfold evalAluOut; rewrite df_wrappedAlu_unfold.
  set (ro := evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type (evalRegRead pcAddrInit (evalDecode fo) rf))))).
  intros Hs He Hc.
  destruct (alu_cf_valid ro Hs He Hc) as [He' [Hd' Hc']].
  rewrite (alu_cf_payload ro He' Hd' Hc').
  Timeout 20 exact (routing_cf_ok pcc (evalLetExpr (@constructAluIn type (evalRegRead pcAddrInit (evalDecode fo) rf))) Hc').
Qed.

Section ExecMain.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.

  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation RfSt := (RfState pcAddrInit).
  Local Abbreviation Ghost := (Ghost pcAddrInit).

  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation STAGE :=
    (@aluAndExecuteNonDeferredStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions clint revI plic type).

  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).

  (* a lemma or accessor applied to the 17 parameters of the impl state *)
  Local Abbreviation IMPL L := (L pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post
                                  revBase revPfB revPfA).

  Local Abbreviation applyPA := (IMPL applyP).
  Local Abbreviation effSA := (IMPL effS).
  Local Abbreviation stRedirA := (IMPL stRedir).
  Local Abbreviation stEffA := (IMPL stEff).

  Local Abbreviation iRfA := (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFlushA := (iFlush pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA := (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchA := (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA := (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecA := (iExec pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA := (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA := (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iD2aA := (iD2a pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation D2AF s1 := (decode_toAluFifo decodeCapacity (iDecodeA s1)).
  Local Abbreviation iDmBufA := (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA := (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecEpochA := (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFenceIPendingA := (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iPccA := (iPcc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iPlicA := (iPlic pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA plic).
  Local Abbreviation iClintA := (iClint pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clint).
  Local Abbreviation iInstBufA := (iInstBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchBufA := (iFetchBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iStraddleA := (iStraddle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchPcA := (iFetchPc pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation daLiveA := (daLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation olderWritersA := (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* what the stage reads (RefExecImpl.v) *)
  Local Abbreviation stHeadA := (stHead pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation stJA := (stJ pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation stIntA := (stInt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clint plic).
  Local Abbreviation stMeipA := (stMeip pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA plic).
  Local Abbreviation stMtipA := (stMtip pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA clint).
  Local Abbreviation stDmEmptyA := (stDmEmpty pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation stNoWrA := (stNoWr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation stAluOutA := (stAluOut pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Local Abbreviation stMulFullA := (stMulFull pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation stDivFullA := (stDivFull pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation ScoreRelA := (ScoreRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation EXTA md := (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode md).
  Local Abbreviation MDWF := (MulDivWf mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation DmQueueRelA := (DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation FrontRelA := (FrontRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  initLine fwcs).
  Local Abbreviation NoLiveA := (NoLive pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation stDmFullA := (stDmFull pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* --- 1. Facts the Branches Share --- *)

  (* conversions never unfold the register paths; the stage's small wrappers unfold first *)
  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.
  Local Strategy opaque [gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind].
  Local Strategy expand [stHead stJ stInt stMeip stMtip stWb iPcc].

  (* the stage's reads in the forms of the RefExec*.v lemmas: proven once, then passed as
   * equations (never by conversion; "Compile speed", rules 1 and 9) *)
  Lemma stPcc_eq : forall s1 : IState, iPccA s1 = readPcc pcAddrInit (iRfA s1).
  Proof. reflexivity. Qed.
  Lemma stMeip_eq : forall s1 : IState, stMeipA s1 = plicMeipOf (iPlicA s1).
  Proof. reflexivity. Qed.
  Lemma stMtip_eq : forall s1 : IState, stMtipA s1 = clintSampled (iClintA s1).
  Proof. reflexivity. Qed.
  Lemma stInt_eq :
    forall s1 : IState, stIntA s1 = evalIsInterruptPending pcAddrInit (stMeipA s1) (stMtipA s1) (iRfA s1).
  Proof. reflexivity. Qed.

  Lemma wf_d2a : forall g (s1 : IState) (s2 : SState), RELG g s1 s2 -> fifo_wf (D2AF s1).
  Proof. intros g s1 s2 Hg; destruct Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; exact (proj1 (proj2 (proj2 Hw))). Qed.

  (* a valid head is the first entry of the decode-to-ALU FIFO *)
  Lemma head_of_valid :
    forall (s1 : IState), fifo_wf (D2AF s1) -> (stHeadA s1).(Snd).(Fst) = true ->
      iD2aA s1 = stJA s1 :: tl (iD2aA s1).
  Proof.
    intros s1 Hwf Hv; unfold stJ, stHead in *; unfold iD2a.
    rewrite (fifoFirstVal_valid _ _ _ Hwf) in Hv.
    destruct (fifo_to_list (D2AF s1)) as [| x l] eqn:El; [discriminate Hv |].
    rewrite (fifoFirstVal_data _ _ _ x l El); reflexivity.
  Qed.

  Lemma d2a_of_deq :
    forall (s1 s1' : IState), fifo_wf (D2AF s1) -> D2AF s1' = fifoDeqState (D2AF s1) ->
      iD2aA s1' = tl (iD2aA s1) /\ fifo_wf (D2AF s1').
  Proof.
    intros s1 s1' Hwf E; unfold iD2a; rewrite E.
    split; [exact (fifo_to_list_deq _ _ _ Hwf) | exact (fifo_wf_deq _ _ _ Hwf)].
  Qed.

  (* dataMem empty and no write pending, in the relation's terms *)
  Lemma dm_quiet :
    forall g (s1 : IState) (s2 : SState), RELG g s1 s2 -> andb (stDmEmptyA s1) (stNoWrA s1) = true ->
      iDmBufA s1 = [] /\ dmLoadRq (iDmStA s1) = true /\ msWriteRq (iMemStA s1) = false /\
      noPortWriteB implRegions (iRegionsA s1) = true.
  Proof.
    intros g s1 s2 Hg Hq.
    destruct Hg as [_ _ _ _ _ _ _ _ _ _ _ Hw _]; destruct Hw as [_ [_ [_ [Hwdm _]]]].
    apply andb_prop in Hq as [He Hn]; unfold stDmEmpty, stNoWr in *.
    apply andb_prop in He as [Hf Hs]; apply andb_prop in Hn as [Hw Hp].
    split; [| split; [| split]].
    - unfold iDmBuf; change (dm_inputFifo dataMemCapacity (iDmA s1)) with (dataMem_fifo dataMemCapacity (iDmA s1)) in Hf.
      rewrite (fifo_size_eqb_zero _ _ _ Hwdm) in Hf.
      destruct (fifo_to_list (dataMem_fifo dataMemCapacity (iDmA s1))); [reflexivity | discriminate Hf].
    - exact Hs.
    - apply negb_true_iff in Hw; exact Hw.
    - exact Hp.
  Qed.

  (* --- 2. No Spec Step --- *)

  (* the redirect register is unchanged from a state without one: the applied view is the state *)
  Lemma eff_np :
    forall (s1 s1' : IState),
      stRedirA s1 = false -> ex_redirect (iExecA s1') = ex_redirect (iExecA s1) -> effSA s1' = s1'.
  Proof.
    intros s1 s1' Hrd Erd; apply (IMPL effS_false).
    unfold iRedirValid, ex_redirValid; rewrite Erd; exact Hrd.
  Qed.

  Lemma exec_noCanProceed :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = false ->
      ex_canProceed (iExecA s1) = false ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1') s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hrd Hcp.
    rewrite (IMPL impl_noCanProceed clint plic envI s1 s1' Hsem Hcp), (IMPL effS_false s1 Hrd).
    exists g, s2; split; [apply NilAction; reflexivity | exact Hg].
  Qed.

  Lemma exec_stutter :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> IMPL ExecStutter s1 s1' -> stRedirA s1 = false ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1') s2'.
  Proof.
    intros g s1 s1' s2 Hg [Erf [Ewb [Emem [Efe [Ede [Edm [Emd [Eep [Efip Erd]]]]]]]]] Hrd.
    rewrite (eff_np s1 s1' Hrd Erd).
    exact (IMPL stutter_step clintS clint plicS plic initLine fwcs g s1 s1' s2 Hg Erf Ewb Emem Efe Ede Eep Efip Edm Emd).
  Qed.

  (* a stale head is dropped, given the stage's effect *)
  Lemma exec_stale_of :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> (stHeadA s1).(Snd).(Fst) = true -> daLiveA s1 (stHeadA s1).(Fst) = false ->
      iRfA s1' = iRfA s1 ->
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn (stHeadA s1).(Fst))) (aluInCd (daAluIn (stHeadA s1).(Fst)))
                   false (iWbA s1) ->
      iMemA s1' = iMemA s1 -> iFetchA s1' = iFetchA s1 -> D2AF s1' = fifoDeqState (D2AF s1) ->
      iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      iExecEpochA s1' = iExecEpochA s1 -> iFenceIPendingA s1' = iFenceIPendingA s1 ->
      exists g', RELG g' s1' s2.
  Proof.
    intros g s1 s1' s2 Hg Hv Hst Erf Ewb Emem Efe Ed2a' Edm Emd Eep Efip.
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 Hwf'].
    destruct (IMPL step_stale_drop clintS clint plicS plic initLine fwcs g s1 s1' s2 (stJA s1) (tl (iD2aA s1))
                Hg Ed2a Ed2a2 Hst Ewb Hwf' Erf Emem Efe Edm Emd Eep Efip) as [g' Hg'].
    exists g'; exact Hg'.
  Qed.

  Lemma exec_stale :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = false ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = false ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1') s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hrd Hcp Hv Hst.
    assert (Hst' : Zmod.eqb (daExecEpoch (stHeadA s1).(Fst)) (stEffA s1) = false)
      by (rewrite (IMPL stEff_false s1 Hrd); exact Hst).
    destruct (IMPL impl_stale clint plic envI s1 s1' Hsem Hcp Hv Hst')
      as [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep [Efip Erd]]]]]]]]].
    rewrite (eff_np s1 s1' Hrd Erd).
    destruct (exec_stale_of g s1 s1' s2 Hg Hv Hst Erf Ewb Emem Efe Ed2a' Edm Emd Eep Efip) as [g' Hg'].
    exists g', s2; split; [apply NilAction; reflexivity | exact Hg'].
  Qed.

  (* --- 3. The Interrupt: Lockstep --- *)

  Lemma iFlush_of :
    forall (s1' : IState) rf md,
      iRfA s1' = rf -> iMdA s1' = md ->
      iFlushA s1' = flushMulDivCaps pcAddrInit (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode md) rf.
  Proof.
    intros s1' rf md Erf Emd; unfold iFlush, flushMulDiv, flushMulDivOn.
    change (impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1') with (iRfA s1').
    rewrite Erf, Emd; reflexivity.
  Qed.

  Lemma exec_interrupt :
    forall g (s1 s1r : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1r Zmod.zero -> stRedirA s1 = false ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = true -> stIntA s1 = true ->
      andb (stDmEmptyA s1) (stNoWrA s1) = true ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1r) s2'.
  Proof.
    intros g s1 s1r s2 Hg Hsem Hrd Hcp Hv Hlive Hint Hq.
    destruct (IMPL impl_interrupt clint plic envI s1 s1r Hsem Hcp Hrd Hv Hlive Hint Hq)
      as [rfMid [execOut [Hex [Erf [Ewb [Emem [Efe0 [Ed2a' [Edm [Emd [Eep0 [Efip Erd]]]]]]]]]]]].
    (* the redirect is pending: the relation sees it applied *)
    assert (Hv1 : IMPL iRedirValid s1r = true) by (unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity).
    rewrite (IMPL effS_true s1r Hv1).
    assert (Efe : iFetchA (applyPA s1r) =
                  fetch_withPc pcAddrInit fetchCapacity instCapacity
                    (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1)
                       (getDefault (Option StraddleHalf)))
                    (defNextPcc execOut).(Snd).(Snd).(Fst))
      by (rewrite (IMPL applyP_fetch s1r), Efe0; unfold redirTarget, redirPcc, iRedirect; rewrite Erd; reflexivity).
    assert (Eep : iExecEpochA (applyPA s1r) = evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]))
      by (rewrite (IMPL applyP_epoch s1r), Eep0; reflexivity).
    clear Efe0 Eep0 Erd Hv1 Hsem.
    change (iRfA s1r) with (iRfA (applyPA s1r)) in Erf.
    change (iWbA s1r) with (iWbA (applyPA s1r)) in Ewb.
    change (iMemA s1r) with (iMemA (applyPA s1r)) in Emem.
    change (D2AF s1r) with (D2AF (applyPA s1r)) in Ed2a'.
    change (iDmA s1r) with (iDmA (applyPA s1r)) in Edm.
    change (iMdA s1r) with (iMdA (applyPA s1r)) in Emd.
    change (iFenceIPendingA s1r) with (iFenceIPendingA (applyPA s1r)) in Efip.
    set (s1' := applyPA s1r) in *; clearbody s1'.
    assert (Hpc : pcAligned (iPccA s1').(Snd).(Snd).(Fst)).
    { unfold iPcc; rewrite Erf, readPcc_writePcc.
      exact (executeInterrupt_nextPcc_even pcAddrInit _ _ _ _ _ _ Hex). }
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 Hwf'].
    destruct (dm_quiet g s1 s2 Hg Hq) as [Hbuf [Hlrq [Hms Hnp]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ _ _ _ Hf _ _ _ _].
    assert (Hlive' : daLiveA s1 (stJA s1) = true) by exact Hlive.
    destruct (IMPL live_head_fence_facts clintS clint plicS plic fwcs g s1 s2 (stJA s1) (tl (iD2aA s1)) Hf Hm Ed2a Hlive')
      as [Hfip _].
    remember (evalAluOut (readPcc pcAddrInit (iRfA s1)) (daAluIn (stJA s1))) as a eqn:Ha.
    pose proof (nonDeferred_of_interrupt pcAddrInit defaultEnv
                  (iPccA s1) (readPcc pcAddrInit (iRfA s1))
                  (stMeipA s1) (plicMeipOf (iPlicA s1))
                  (stMtipA s1) (clintSampled (iClintA s1))
                  a (iRfA s1) rfMid execOut
                  (stPcc_eq s1) (stMeip_eq s1) (stMtip_eq s1)
                  (eq_trans (eq_sym (stInt_eq s1)) Hint) Hex) as Hnd.
    destruct (executeInterrupt_fields pcAddrInit _ _ _ _ _ _ Hex) as [Hmd Hdm].
    apply (IMPL step_lockstep_commit clintS clint plicS plic initLine fwcs Hdisj HclintIdx HplicIdx
             g s1 s1' s2 (stJA s1) (tl (iD2aA s1)) a rfMid execOut
             Hg Ed2a Hlive' Hbuf Hlrq Hms Hnp Ha Hnd Hdm Hmd).
    - rewrite (iFlush_of s1' _ _ Erf Emd); symmetry; apply writePcc_flushMulDivCaps.
    - exact Emem.
    - exact Edm.
    - exact Emd.
    - rewrite Efip; exact Hfip.
    - intros g' s2m s2' Hgm Efo' Htf.
      destruct Hgm as [_ _ _ _ _ _ _ _ _ Hsm Hfrm Hwm _].
      assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
      assert (Eib : iInstBufA s1' = iInstBufA s1) by (unfold iInstBuf; rewrite Efe; reflexivity).
      assert (Efb : iFetchBufA s1' = iFetchBufA s1) by (unfold iFetchBuf; rewrite Efe; reflexivity).
      assert (Estr : optValid (iStraddleA s1') = false) by (unfold iStraddle; rewrite Efe; reflexivity).
      assert (Efpc : iFetchPcA s1' = (iPccA s1').(Snd).(Snd).(Fst))
        by (unfold iFetchPc, iPcc; rewrite Efe, Erf, readPcc_writePcc; reflexivity).
      destruct (IMPL redirect_FrontRel_NoLive initLine fwcs g g' s1 s1' s2m s2' (stJA s1) (tl (iD2aA s1))
                  Hfrm Ed2a Hlive' Ed2a2 Eib Efb Ereg Eep Estr Efpc Hpc) as [Hnl Hfr'].
      assert (Hstale : forall x, In x (tl (iD2aA s1)) -> daLiveA s1' x = false).
      { destruct Hnl as [Hnl _]; rewrite Ed2a2, Forall_forall in Hnl; exact Hnl. }
      split; [| split; [exact Hfr' |]].
      + (* the head's register is cleared; the tail is stale after the redirect *)
        pose proof Hsm as Hsm0; destruct Hsm0 as [Hnd' [Hwb [Hlen _]]].
        rewrite Ed2a in Hlen, Hnd', Hwb.
        destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen; discriminate Hlen |].
        cbn [tl] in Efo'.
        pose proof (IMPL olderWriters_ext s1 s1' Edm Emd) as Eow.
        apply (IMPL ScoreRel_pop g g' s1 s1' (stJA s1) (tl (iD2aA s1)) fo0 fo_tail
                 (if Zmod.eqb (d2aDst (stJA s1)) Zmod.zero then [] else [d2aDst (stJA s1)])
                 Hsm Ed2a Efo Ed2a2 Efo').
        * rewrite Eow, d2aWriters_cons; apply Permutation_app_head, Permutation_app_comm.
        * rewrite Eow, Ewb.
          exact (waitBits_clear_head (iWbA s1) (olderWritersA s1) (stJA s1) (tl (iD2aA s1))
                   (IMPL olderWriters_nz s1) Hnd' Hwb).
        * intros r Hr; rewrite Eow in Hr; apply in_or_app; left; exact Hr.
        * intros x Hin Hx; rewrite (Hstale x Hin) in Hx; discriminate Hx.
        * intros l1 j2 l2 fo Hl1 _ Hx _ _; exfalso.
          assert (Hin : In j2 (tl (iD2aA s1))) by (rewrite Hl1; apply in_or_app; right; left; reflexivity).
          rewrite (Hstale j2 Hin) in Hx; discriminate Hx.
      + eapply (IMPL WfRel_exec_step); [exact Hwm | | | exact Hwf' | | | exact Ereg | unfold iCurParcel; rewrite Efe; reflexivity | exact Hpc | intros y Hy; rewrite Ed2a2 in Hy; rewrite Ed2a; right; exact Hy].
        * rewrite Efe; reflexivity.
        * rewrite Efe; reflexivity.
        * rewrite Edm; destruct Hwm as [_ [_ [_ [W4 _]]]]; exact W4.
        * rewrite Emd; destruct Hwm as [_ [_ [_ [_ [W5 _]]]]]; exact W5.
  Qed.

  (* --- 4. Ghost Append: Shared Steps --- *)

  Lemma stAluOut_eq : forall s1 : IState, stAluOutA s1 = evalAluOut (iPccA s1) (daAluIn (stJA s1)).
  Proof. reflexivity. Qed.

  Lemma iFlush_readPcc : forall s1 : IState, readPcc pcAddrInit (iFlushA s1) = iPccA s1.
  Proof. intros s1; rewrite (iFlush_of s1 _ _ eq_refl eq_refl), readPcc_flushMulDivCaps; reflexivity. Qed.

  (* The appended entry is one chain step on the flushed register files, given the step of the
   * head on the flushed file and the flushed file after the step *)
  Lemma append_ginst :
    forall (s1 s1' : IState) (fo0 : type FetchOut) (a : type AluOutUnion) (rfM : RfSt) (x : type ExecuteOut),
      a = evalAluOut (iPccA s1) (evalRegRead pcAddrInit (evalDecode fo0) (iFlushA s1)) ->
      isVirtualCsrAluOut a = false ->
      evalIsInterruptPending pcAddrInit (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) (iRfA s1) = false ->
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type (iPccA s1) (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) a)
        (iFlushA s1) rfM x ->
      iFlushA s1' = specMulDivWb pcAddrInit a x (writePcc pcAddrInit (execNextPcc x) rfM) ->
      GInstStep pcAddrInit (iFlushA s1) (iFlushA s1')
        (mkGEntry fo0 (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) a (execDataMem x)).
  Proof.
    intros s1 s1' fo0 a rfM x Ha Hnv Hint Hsem Efl.
    unfold GInstStep, geAluOut, geAluIn; cbn [ge_aluOut ge_fetchOut ge_meip ge_mtip ge_dm].
    rewrite (iFlush_readPcc s1).
    split; [exact Hnv |]; split; [exact Ha |].
    split; [rewrite (iFlush_of s1 _ _ eq_refl eq_refl), evalIsInterruptPending_flushMulDivCaps; exact Hint |].
    exists x, rfM; split; [exact Hsem | split; [reflexivity | exact Efl]].
  Qed.

  (* --- 5. Sequential Instructions --- *)

  (* The head's step on the flushed register file *)
  Lemma seq_semF :
    forall (s1 : IState) (a : type AluOutUnion) (rfMid : RfSt) mdOpt meip mtip,
      evalIsInterruptPending pcAddrInit meip mtip (iRfA s1) = false ->
      aluIsSeq a = true ->
      (forall d v, In (d, v) (EXTA (iMdA s1)) -> Zmod.eqb d Zmod.zero = false ->
                   Zmod.eqb (aluDstIdx a) Zmod.zero = false -> d <> aluDstIdx a) ->
      SemAction defaultEnv (@executeSequential pcAddrInit type (iPccA s1) a) (iRfA s1) rfMid mdOpt ->
      SemAction defaultEnv (@executeNonDeferred pcAddrInit type (iPccA s1) meip mtip a) (iFlushA s1)
        (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid) (seqOut (iPccA s1) a mdOpt).
  Proof.
    intros s1 a rfMid mdOpt meip mtip Hint Hseq Hneq Hex.
    rewrite (iFlush_of s1 _ _ eq_refl eq_refl).
    apply SemAction_executeNonDeferred_flushMulDivCaps; [exact Hneq |].
    exact (nonDeferred_of_sequential pcAddrInit defaultEnv _ meip mtip a (iRfA s1) rfMid mdOpt Hint Hseq Hex).
  Qed.

  (* A mulDiv op: the engine's entries gain the request, whose result is the spec's *)
  Lemma seq_md_perm :
    forall (s1 s1' : IState) (a : type AluOutUnion) (md : type MulDivUnion),
      MDWF (iMdA s1) ->
      (mdIsMul md = true -> stMulFullA s1 = false) ->
      (mdIsMul md = false -> stDivFullA s1 = false) ->
      iMdA s1' = (if mdIsMul md
                  then mdEnqMul mulCapacity divCapacity mulStages divStages mulDivMode
                         (aluDstIdx a) (aluDstVal a).(Snd).(Snd).(Fst) (mdMulOf md) (iMdA s1)
                  else mdEnqDiv mulCapacity divCapacity mulStages divStages mulDivMode
                         (aluDstIdx a) (aluDstVal a).(Snd).(Snd).(Fst) (mdDivOf md) (iMdA s1)) ->
      Permutation (EXTA (iMdA s1'))
        (EXTA (iMdA s1) ++
         [(aluDstIdx a, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type (aluDstVal a).(Snd).(Snd).(Fst) md)))]) /\
      MDWF (iMdA s1').
  Proof.
    intros s1 s1' a md Hwf Hfm Hfd Emd.
    assert (Hdec : mdIsMul md = true \/ mdIsMul md = false) by (destruct (mdIsMul md); [left | right]; reflexivity).
    destruct Hdec as [Hm | Hm]; rewrite Hm in Emd; cbv iota in Emd; rewrite Emd.
    - pose proof (extract_enqMul mulCapacity divCapacity mulStages divStages mulDivMode (aluDstIdx a)
                    (aluDstVal a).(Snd).(Snd).(Fst) (mdMulOf md) (iMdA s1) Hwf (Hfm Hm)) as P.
      rewrite (MulDiv_mulUnion _ md Hm) in P.
      split; [exact P | apply WF_enqMul; exact Hwf].
    - pose proof (extract_enqDiv mulCapacity divCapacity mulStages divStages mulDivMode (aluDstIdx a)
                    (aluDstVal a).(Snd).(Snd).(Fst) (mdDivOf md) (iMdA s1) Hwf (Hfd Hm)) as P.
      rewrite (MulDiv_divUnion _ md Hm) in P.
      split; [exact P | apply WF_enqDiv; exact Hwf].
  Qed.

  (* The engine's destinations and the head's are distinct (the scoreboard) *)
  Lemma seq_nodup :
    forall (s1 : IState) j tail (a : type AluOutUnion) v,
      NoDup (olderWritersA s1 ++ d2aWriters (j :: tail)) ->
      aluDstIdx a = d2aDst j ->
      NoDup (nzDsts (EXTA (iMdA s1) ++ [(aluDstIdx a, v)])).
  Proof.
    intros s1 j tail a v Hnd Ed.
    assert (E2 : nzDsts (EXTA (iMdA s1) ++ [(aluDstIdx a, v)]) =
                 (nzDsts (EXTA (iMdA s1)) ++ (if Zmod.eqb (d2aDst j) Zmod.zero then [] else [d2aDst j]))%list).
    { unfold nzDsts; rewrite map_app, filter_app, Ed; cbn [map filter fst].
      destruct (Zmod.eqb (d2aDst j) Zmod.zero); reflexivity. }
    rewrite E2.
    unfold olderWriters in Hnd; rewrite app_assoc, filter_app, d2aWriters_cons, <- app_assoc in Hnd.
    exact (NoDup_mid _ _ _ _ Hnd).
  Qed.

  (* A mulDiv op's register moves to the older writers *)
  Lemma seq_md_olderWriters :
    forall (s1 s1' : IState) j (a : type AluOutUnion) v,
      iDmA s1' = iDmA s1 ->
      Permutation (EXTA (iMdA s1')) (EXTA (iMdA s1) ++ [(aluDstIdx a, v)]) ->
      aluDstIdx a = d2aDst j ->
      Permutation (olderWritersA s1') (olderWritersA s1 ++ d2aWriters [j]).
  Proof.
    intros s1 s1' j a v Edm Hp Ed.
    unfold olderWriters, dmInFlightDst, iDmBuf, iDmSt, d2aWriters.
    change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1')
      with (iDmA s1').
    change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1)
      with (iDmA s1).
    rewrite Edm, <- filter_app; apply Permutation_filter_local.
    rewrite <- !app_assoc; apply Permutation_app_head, Permutation_app_head.
    cbn [map]; rewrite <- Ed.
    change [aluDstIdx a] with (map fst [(aluDstIdx a, v)]); rewrite <- map_app.
    apply Permutation_map; exact Hp.
  Qed.

  (* The flushed register file after the step: a Normal op *)
  Lemma seq_flush_normal :
    forall (s1 s1' : IState) (a : type AluOutUnion) (rfMid : RfSt) mdOpt np,
      optValid mdOpt = false ->
      iRfA s1' = writePcc pcAddrInit np rfMid -> iMdA s1' = iMdA s1 ->
      evalExpr (@Alu.getSeqPcc type (iPccA s1) a.(Fst)) = np ->
      iFlushA s1' = specMulDivWb pcAddrInit a (seqOut (iPccA s1) a mdOpt)
                      (writePcc pcAddrInit (execNextPcc (seqOut (iPccA s1) a mdOpt))
                         (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid)).
  Proof.
    intros s1 s1' a rfMid mdOpt np Hv Erf Emd Hnp.
    rewrite specMulDivWb_noMd; [| exact (execDataMem_seqOut _ _ _) | exact Hv].
    rewrite execNextPcc_seqOut, Hnp, (iFlush_of s1' _ _ Erf Emd).
    symmetry; apply writePcc_flushMulDivCaps.
  Qed.

  (* ... and a mulDiv op (its entry commutes to the end of the engine's entries) *)
  Lemma seq_flush_md :
    forall (s1 s1' : IState) (a : type AluOutUnion) (rfMid : RfSt) mdOpt np,
      optValid mdOpt = true ->
      iRfA s1' = writePcc pcAddrInit np rfMid ->
      Permutation (EXTA (iMdA s1'))
        (EXTA (iMdA s1) ++
         [(aluDstIdx a, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type (aluDstVal a).(Snd).(Snd).(Fst) (optData mdOpt))))]) ->
      NoDup (nzDsts (EXTA (iMdA s1) ++
         [(aluDstIdx a, mkMulDivCap (evalLetExpr (@SpecMulDiv.MulDiv type (aluDstVal a).(Snd).(Snd).(Fst) (optData mdOpt))))])) ->
      evalExpr (@Alu.getSeqPcc type (iPccA s1) a.(Fst)) = np ->
      iFlushA s1' = specMulDivWb pcAddrInit a (seqOut (iPccA s1) a mdOpt)
                      (writePcc pcAddrInit (execNextPcc (seqOut (iPccA s1) a mdOpt))
                         (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid)).
  Proof.
    intros s1 s1' a rfMid mdOpt np Hv Erf Hperm Hnd Hnp.
    rewrite specMulDivWb_md; [| exact (execDataMem_seqOut _ _ _) | exact Hv].
    rewrite execNextPcc_seqOut, execMulDiv_seqOut, Hnp, (iFlush_of s1' _ _ Erf eq_refl).
    rewrite <- (flushMulDivCaps_perm pcAddrInit _ _ _ Hnd (Permutation_sym Hperm)).
    rewrite flushMulDivCaps_snoc, writePcc_flushMulDivCaps; reflexivity.
  Qed.

  (* The scoreboard after the step: a Normal op clears the head's wait bit *)
  Lemma seq_score_normal :
    forall g g' (s1 s1' : IState) j tail fo0 fo_tail (a : type AluOutUnion) (rfM : RfSt) (x : type ExecuteOut) meip mtip,
      ScoreRelA g s1 ->
      iD2aA s1 = j :: tail -> g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = tail -> g_d2aFo pcAddrInit g' = fo_tail ->
      iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn j)) (aluInCd (daAluIn j)) false (iWbA s1) ->
      iExecEpochA s1' = iExecEpochA s1 ->
      a = evalAluOut (iPccA s1) (daAluIn j) ->
      SemAction defaultEnv (@executeNonDeferred pcAddrInit type (iPccA s1) meip mtip a) (iFlushA s1) rfM x ->
      iFlushA s1' = specMulDivWb pcAddrInit a x (writePcc pcAddrInit (execNextPcc x) rfM) ->
      ScoreRelA g' s1'.
  Proof.
    intros g g' s1 s1' j tail fo0 fo_tail a rfM x meip mtip Hsc Ed2a Efo Ed2a' Efo' Edm Emd Ewb Eep Ha Hsem Efl.
    pose proof (IMPL olderWriters_ext s1 s1' Edm Emd) as Eow.
    pose proof Hsc as Hsc0; destruct Hsc0 as [Hnd [Hwb _]].
    rewrite Ed2a in Hnd, Hwb.
    apply (IMPL ScoreRel_pop g g' s1 s1' j tail fo0 fo_tail
             (if Zmod.eqb (d2aDst j) Zmod.zero then [] else [d2aDst j]) Hsc Ed2a Efo Ed2a' Efo').
    - rewrite Eow, d2aWriters_cons; apply Permutation_app_head, Permutation_app_comm.
    - rewrite Eow, Ewb.
      exact (waitBits_clear_head (iWbA s1) (olderWritersA s1) j tail (IMPL olderWriters_nz s1) Hnd Hwb).
    - intros r Hr; rewrite Eow in Hr; apply in_or_app; left; exact Hr.
    - intros y _ Hy; unfold daLive in Hy |- *; rewrite Eep in Hy; exact Hy.
    - intros l1 j2 l2 fo _ _ _ H1 H2; rewrite Efl.
      exact (regRead_after_step pcAddrInit (iPccA s1) meip mtip a j l1 fo (olderWritersA s1) (iFlushA s1) rfM x
               Ha Hsem H1 H2).
  Qed.

  (* ... a mulDiv op keeps it (its register moves to the older writers) *)
  Lemma seq_score_md :
    forall g g' (s1 s1' : IState) j tail fo0 fo_tail (a : type AluOutUnion) (rfM : RfSt) (x : type ExecuteOut) meip mtip,
      ScoreRelA g s1 ->
      iD2aA s1 = j :: tail -> g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = tail -> g_d2aFo pcAddrInit g' = fo_tail ->
      Permutation (olderWritersA s1') (olderWritersA s1 ++ d2aWriters [j]) ->
      iWbA s1' = iWbA s1 ->
      iExecEpochA s1' = iExecEpochA s1 ->
      a = evalAluOut (iPccA s1) (daAluIn j) ->
      SemAction defaultEnv (@executeNonDeferred pcAddrInit type (iPccA s1) meip mtip a) (iFlushA s1) rfM x ->
      iFlushA s1' = specMulDivWb pcAddrInit a x (writePcc pcAddrInit (execNextPcc x) rfM) ->
      ScoreRelA g' s1'.
  Proof.
    intros g g' s1 s1' j tail fo0 fo_tail a rfM x meip mtip Hsc Ed2a Efo Ed2a' Efo' Hperm Ewb Eep Ha Hsem Efl.
    apply (IMPL ScoreRel_move_to_older g g' s1 s1' j tail fo0 fo_tail Hsc Ed2a Efo Ed2a' Efo' Hperm Ewb).
    - intros y _ Hy; unfold daLive in Hy |- *; rewrite Eep in Hy; exact Hy.
    - intros l1 j2 l2 fo _ _ _ H1 H2; rewrite Efl.
      exact (regRead_after_step pcAddrInit (iPccA s1) meip mtip a j l1 fo (olderWritersA s1) (iFlushA s1) rfM x
               Ha Hsem H1 H2).
  Qed.

  Lemma exec_seq :
    forall g (s1 s1' : IState) (s2 : SState) (a : type AluOutUnion),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = false ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = true -> stIntA s1 = false ->
      a = stAluOutA s1 -> aluIsSeq a = true ->
      seqGuardV (aluIsMul a) (aluIsDiv a) (stMulFullA s1) (stDivFullA s1) = true ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1') s2'.
  Proof.
    intros g s1 s1' s2 a Hg Hsem Hrd Hcp Hv Hlive Hint Ha Hseq Hgd.
    destruct (IMPL impl_seq clint plic envI s1 s1' a Hsem Hcp Hrd Hv Hlive Hint Ha Hseq Hgd)
      as [rfMid [mdOpt [Hex [Erf [Emem [Efe [Ed2a' [Edm [Eep [Efip [Erd Hmd]]]]]]]]]]].
    rewrite (eff_np s1 s1' Hrd Erd).
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 Hwf'].
    assert (Hlive' : daLiveA s1 (stJA s1) = true) by exact Hlive.
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ _ _ Hdq Hf Hs Hfr Hw _].
    destruct (IMPL live_head_fence_facts clintS clint plicS plic fwcs g s1 s2 (stJA s1) (tl (iD2aA s1)) Hf Hm Ed2a Hlive')
      as [Hfip _].
    pose proof Hs as Hs0; destruct Hs0 as [Hnd [_ [Hlen Hreg]]].
    rewrite Ed2a in Hlen, Hnd.
    destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen; discriminate Hlen |].
    destruct (Hreg [] (stJA s1) (tl (iD2aA s1)) fo0 Ed2a eq_refl Hlive') as [HaluIn _].
    (* the ALU output: no fault, no prediction, the next PCC is the sequential one *)
    assert (Ha1 : a = evalAluOut (iPccA s1) (daAluIn (stJA s1))) by (rewrite Ha; apply stAluOut_eq).
    assert (Ha2 : a = evalAluOut (iPccA s1) (evalRegRead pcAddrInit (evalDecode fo0) (iFlushA s1)))
      by (rewrite <- HaluIn; exact Ha1).
    assert (Ed : aluDstIdx a = d2aDst (stJA s1)) by (rewrite Ha1; apply d2aDst_aluDstIdx).
    pose proof (seq_noFault pcAddrInit _ fo0 _ a Ha2 Hseq) as Hnf.
    pose proof (seq_noPred pcAddrInit _ fo0 _ a Ha2 Hseq) as Hnp.
    pose proof (seq_isComp pcAddrInit _ fo0 _ a Ha2) as Hic.
    destruct (IMPL live_head_front_facts initLine fwcs g s1 s2 (stJA s1) (tl (iD2aA s1)) fo0 fo_tail Hfr Ed2a Efo Hlive')
      as [_ Hff].
    destruct (Hff Hnf) as [Hpred _].
    assert (Enp : evalExpr (@Alu.getSeqPcc type (iPccA s1) a.(Fst)) = pccWithAddr (iPccA s1) (daPredPc (stJA s1)))
      by (rewrite (getSeqPcc_pccWithAddr (iPccA s1) (foInst fo0) a.(Fst) Hic), (Hpred Hnp); reflexivity).
    pose proof (eq_trans (eq_sym (stInt_eq s1)) Hint) as Hint1.
    rewrite (stMeip_eq s1), (stMtip_eq s1) in Hint1.
    (* the engine's entries avoid the head's destination *)
    assert (Hneq : forall d v, In (d, v) (EXTA (iMdA s1)) -> Zmod.eqb d Zmod.zero = false ->
                     Zmod.eqb (aluDstIdx a) Zmod.zero = false -> d <> aluDstIdx a).
    { intros d v Hin Hzd Hza Heq; subst d.
      apply NoDup_app_iff in Hnd as [_ [_ Hdj]]; apply (Hdj (aluDstIdx a)).
      - unfold olderWriters; apply filter_In; split; [| rewrite Hzd; reflexivity].
        apply in_or_app; right; apply in_or_app; right.
        change (aluDstIdx a) with (fst (aluDstIdx a, v)); apply in_map; exact Hin.
      - rewrite Ed in Hza |- *; rewrite d2aWriters_cons, Hza; left; reflexivity. }
    pose proof (seq_semF s1 a rfMid mdOpt _ _ Hint1 Hseq Hneq Hex) as HsemF.
    set (X := seqOut (iPccA s1) a mdOpt) in HsemF.
    (* the two cases: the flushed register file, the scoreboard and the engine's FIFOs *)
    assert (Hcase :
      iFlushA s1' = specMulDivWb pcAddrInit a X
                      (writePcc pcAddrInit (execNextPcc X) (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid)) /\
      (forall g', g_d2aFo pcAddrInit g' = fo_tail -> ScoreRelA g' s1') /\
      MDWF (iMdA s1')).
    { destruct Hw as [_ [_ [_ [_ [W5 _]]]]].
      assert (Hdec : optValid mdOpt = true \/ optValid mdOpt = false)
        by (destruct (optValid mdOpt); [left | right]; reflexivity).
      destruct Hdec as [Ev | Ev]; rewrite Ev in Hmd; destruct Hmd as [Ewb Emd].
      - (* a mulDiv op: its request enters the engine *)
        destruct (executeSequential_mdOpt pcAddrInit (iPccA s1) a (iRfA s1) rfMid mdOpt Hex) as [Evn Emdd].
        assert (Hn : aluSeqNormal a = false)
          by (rewrite Ev in Evn; destruct (aluSeqNormal a); [discriminate Evn | reflexivity]).
        pose proof (Emdd Ev) as Emd0.
        destruct (seq_md_perm s1 s1' a (optData mdOpt) W5
                    (fun Hm => seqGuard_mul _ _ _ _ Hgd
                                 (seq_md_isMul a Hseq Hn (eq_trans (f_equal mdIsMul (eq_sym Emd0)) Hm)))
                    (fun Hm => seqGuard_div _ _ _ _ Hgd
                                 (seq_md_isDiv a Hseq Hn (eq_trans (f_equal mdIsMul (eq_sym Emd0)) Hm)))
                    Emd) as [Hperm Hwf5].
        assert (Hfl : iFlushA s1' = specMulDivWb pcAddrInit a X
                        (writePcc pcAddrInit (execNextPcc X) (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid)))
          by exact (seq_flush_md s1 s1' a rfMid mdOpt _ Ev Erf Hperm (seq_nodup s1 _ _ a _ Hnd Ed) Enp).
        split; [exact Hfl | split; [| exact Hwf5]].
        intros g' Efo'.
        exact (seq_score_md g g' s1 s1' (stJA s1) (tl (iD2aA s1)) fo0 fo_tail a _ X _ _ Hs Ed2a Efo Ed2a2 Efo'
                 (seq_md_olderWriters s1 s1' (stJA s1) a _ Edm Hperm Ed) Ewb Eep Ha1 HsemF Hfl).
      - (* a Normal op: its register was written; the wait bit is cleared *)
        assert (Hfl : iFlushA s1' = specMulDivWb pcAddrInit a X
                        (writePcc pcAddrInit (execNextPcc X) (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid)))
          by exact (seq_flush_normal s1 s1' a rfMid mdOpt _ Ev Erf Emd Enp).
        split; [exact Hfl | split; [| rewrite Emd; exact W5]].
        intros g' Efo'.
        exact (seq_score_normal g g' s1 s1' (stJA s1) (tl (iD2aA s1)) fo0 fo_tail a _ X _ _ Hs Ed2a Efo Ed2a2 Efo'
                 Edm Emd Ewb Eep Ha1 HsemF Hfl). }
    destruct Hcase as [Hfl [Hsc' Hwf5]].
    pose proof (append_ginst s1 s1' fo0 a _ X Ha2 (seq_notVirt a Hseq) Hint1 HsemF Hfl) as Hstep.
    set (e := mkGEntry fo0 (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) a (execDataMem X)) in Hstep.
    set (g1 := mkGhost pcAddrInit (g_chain pcAddrInit g ++ [GInst e])%list (g_rf0 pcAddrInit g)
                 (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g) fo_tail (g_acc pcAddrInit g)).
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Hpc : forall p, iPccA s1' = pccWithAddr (iPccA s1) p -> pcAligned p -> pcAligned (iPccA s1').(Snd).(Snd).(Fst))
      by (intros p Ep Hp; rewrite Ep; exact Hp).
    assert (Epcc : iPccA s1' = pccWithAddr (iPccA s1) (daPredPc (stJA s1)))
      by (rewrite (stPcc_eq s1'), Erf; apply readPcc_writePcc).
    assert (Hdm0 : optValid (ge_dm e) = false) by exact (execDataMem_seqOut (iPccA s1) a mdOpt).
    pose proof Hw as Hw0; destruct Hw0 as [_ [_ [_ [W4 _]]]].
    apply (IMPL step_append_nonvirt clintS clint plicS plic initLine fwcs Hdisj
             g s1 s1' s2 (stJA s1) (tl (iD2aA s1)) fo0 fo_tail e g1
             Hg Ed2a Efo Hlive' eq_refl eq_refl eq_refl Hstep eq_refl Emem).
    - unfold iDmSt; rewrite Edm; reflexivity.
    - apply (IMPL DmQueueRel_snoc_none g g1 s1 s1' e Hdq eq_refl eq_refl Hdm0).
      unfold iDmBuf; rewrite Edm; reflexivity.
    - apply (IMPL FenceRel_snoc_step clintS clint plicS plic fwcs g g1 s1 s1' s2 (stJA s1) (tl (iD2aA s1)) e
               Hf Hm Ed2a Hlive' eq_refl Ereg).
      + rewrite (entryIsFenceI_noDm e Hdm0), Efip; exact Hfip.
      + rewrite (entryIsFenceI_noDm e Hdm0); intros H; discriminate H.
    - exact (Hsc' g1 eq_refl).
    - apply (IMPL FrontRel_step_no_redirect initLine fwcs g g1 s1 s1' s2 (stJA s1) (tl (iD2aA s1)) fo0 fo_tail
               Hfr Ed2a Efo Hlive' Hnf Ed2a2 eq_refl Eep);
        try (unfold iInstBuf, iFetchBuf, iFetchPc, iPredEpoch, iCurParcel, iStraddle; rewrite Efe; reflexivity);
        try exact Ereg; rewrite Epcc; reflexivity.
    - eapply (IMPL WfRel_exec_step);
        [exact Hw | rewrite Efe; reflexivity | rewrite Efe; reflexivity | exact Hwf'
        | rewrite Edm; exact W4 | exact Hwf5 | exact Ereg | unfold iCurParcel; rewrite Efe; reflexivity
        | apply (Hpc _ Epcc); destruct Hw as [[_ [_ [_ [Hd _]]]] _]; rewrite Ed2a in Hd; exact (Forall_inv Hd)
        | intros y Hy; rewrite Ed2a2 in Hy; rewrite Ed2a; right; exact Hy].
  Qed.

  (* --- 6. Non-Sequential Instructions --- *)

  Lemma nonSeq_semF :
    forall (s1 : IState) (a : type AluOutUnion) (rfMid : RfSt) (x : type ExecuteOut) meip mtip,
      evalIsInterruptPending pcAddrInit meip mtip (iRfA s1) = false ->
      aluIsSeq a = false ->
      (forall d v, In (d, v) (EXTA (iMdA s1)) -> Zmod.eqb d Zmod.zero = false ->
                   Zmod.eqb (aluDstIdx a) Zmod.zero = false -> d <> aluDstIdx a) ->
      SemAction defaultEnv (@executeNonSequential pcAddrInit type (iPccA s1) meip mtip a) (iRfA s1) rfMid x ->
      SemAction defaultEnv (@executeNonDeferred pcAddrInit type (iPccA s1) meip mtip a) (iFlushA s1)
        (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid) x.
  Proof.
    intros s1 a rfMid x meip mtip Hint Hns Hneq Hex.
    rewrite (iFlush_of s1 _ _ eq_refl eq_refl).
    apply SemAction_executeNonDeferred_flushMulDivCaps; [exact Hneq |].
    exact (nonDeferred_of_nonSequential pcAddrInit defaultEnv _ meip mtip a (iRfA s1) rfMid x Hint Hns Hex).
  Qed.

  (* The flushed register file after the step (no mulDiv output; the engine is unchanged) *)
  Lemma nonSeq_flush :
    forall (s1 s1' : IState) (a : type AluOutUnion) (rfMid : RfSt) (x : type ExecuteOut),
      optValid (execMulDiv x) = false ->
      iRfA s1' = writePcc pcAddrInit (defNextPcc x) rfMid -> iMdA s1' = iMdA s1 ->
      iFlushA s1' = specMulDivWb pcAddrInit a x
                      (writePcc pcAddrInit (execNextPcc x) (flushMulDivCaps pcAddrInit (EXTA (iMdA s1)) rfMid)).
  Proof.
    intros s1 s1' a rfMid x Hmd Erf Emd.
    rewrite specMulDivWb_noMd2 by exact Hmd.
    rewrite (iFlush_of s1' _ _ Erf Emd).
    symmetry; apply writePcc_flushMulDivCaps.
  Qed.

  (* A dataMem enqueue: the request joins the queue, the dataMem state is unchanged *)
  Lemma dm_enq_facts :
    forall (s1 s1' : IState) q,
      fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1)) ->
      stDmFullA s1 = false ->
      iDmA s1' = dm_withInputFifo dataMemCapacity (iDmA s1) (fifoEnqState (dm_inputFifo dataMemCapacity (iDmA s1)) q) ->
      iDmBufA s1' = (iDmBufA s1 ++ [q])%list /\ iDmStA s1' = iDmStA s1 /\
      fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1')).
  Proof.
    intros s1 s1' q Hwf Hnf Edm.
    unfold iDmBuf, iDmSt; rewrite Edm.
    split; [| split; [reflexivity |]].
    - exact (fifo_to_list_enq _ _ _ _ Hwf (fifo_notFull_lt _ _ _ Hwf Hnf)).
    - exact (fifo_wf_enq _ _ _ _ Hwf).
  Qed.

  (* ... and the older writers gain the request's register if it is a load *)
  Lemma olderWriters_enq :
    forall (s1 s1' : IState) q,
      iDmBufA s1' = (iDmBufA s1 ++ [q])%list -> iDmStA s1' = iDmStA s1 -> iMdA s1' = iMdA s1 ->
      Permutation (olderWritersA s1')
        (olderWritersA s1 ++ filter (fun d => negb (Zmod.eqb d Zmod.zero))
                                   (if opIsLoad (mrOp q) then [mrDst q] else []))%list.
  Proof.
    intros s1 s1' q Ebuf Est Emd.
    unfold olderWriters, dmInFlightDst; cbv zeta.
    rewrite Ebuf, Est, Emd, <- filter_app; apply Permutation_filter_local.
    rewrite filter_app, map_app; cbn [filter].
    destruct (opIsLoad (mrOp q)); cbn [map].
    - rewrite <- !app_assoc; do 2 apply Permutation_app_head; apply Permutation_app_comm.
    - rewrite !app_nil_r; apply Permutation_refl.
  Qed.

  (* The scoreboard after a non-sequential step; `Hlv`/`Hrr` are the live-tail obligations of
   * `ScoreRel_pop` (no redirect: `rr_step`, same epoch; redirect: the tail is stale) *)
  Lemma rr_step :
    forall (s1 s1' : IState) j tail fo_tail (a : type AluOutUnion) (rfM : RfSt) (x : type ExecuteOut) meip mtip,
      a = evalAluOut (iPccA s1) (daAluIn j) ->
      SemAction defaultEnv (@executeNonDeferred pcAddrInit type (iPccA s1) meip mtip a) (iFlushA s1) rfM x ->
      iFlushA s1' = specMulDivWb pcAddrInit a x (writePcc pcAddrInit (execNextPcc x) rfM) ->
      forall l1 j2 l2 fo,
        tail = (l1 ++ j2 :: l2)%list -> nth_error fo_tail (length l1) = Some fo -> daLiveA s1' j2 = true ->
        RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs1 fo) ->
        RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs2 fo) ->
        evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1).
  Proof.
    intros s1 s1' j tail fo_tail a rfM x meip mtip Ha Hsem Efl l1 j2 l2 fo _ _ _ H1 H2; rewrite Efl.
    exact (regRead_after_step pcAddrInit (iPccA s1) meip mtip a j l1 fo (olderWritersA s1) (iFlushA s1) rfM x
             Ha Hsem H1 H2).
  Qed.

  Lemma score_clear :
    forall g g' (s1 s1' : IState) j tail fo0 fo_tail,
      ScoreRelA g s1 ->
      iD2aA s1 = j :: tail -> g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = tail -> g_d2aFo pcAddrInit g' = fo_tail ->
      iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      iWbA s1' = evalSetDstWaitBits (aluInWritesCd (daAluIn j)) (aluInCd (daAluIn j)) false (iWbA s1) ->
      (forall y, In y tail -> daLiveA s1' y = true -> daLiveA s1 y = true) ->
      (forall l1 j2 l2 fo, tail = (l1 ++ j2 :: l2)%list -> nth_error fo_tail (length l1) = Some fo ->
         daLiveA s1' j2 = true ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs1 fo) ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs2 fo) ->
         evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) ->
      ScoreRelA g' s1'.
  Proof.
    intros g g' s1 s1' j tail fo0 fo_tail Hsc Ed2a Efo Ed2a' Efo' Edm Emd Ewb Hlv Hrr.
    pose proof (IMPL olderWriters_ext s1 s1' Edm Emd) as Eow.
    pose proof Hsc as Hsc0; destruct Hsc0 as [Hnd [Hwb _]].
    rewrite Ed2a in Hnd, Hwb.
    apply (IMPL ScoreRel_pop g g' s1 s1' j tail fo0 fo_tail
             (if Zmod.eqb (d2aDst j) Zmod.zero then [] else [d2aDst j]) Hsc Ed2a Efo Ed2a' Efo');
      [| | | exact Hlv | exact Hrr].
    - rewrite Eow, d2aWriters_cons; apply Permutation_app_head, Permutation_app_comm.
    - rewrite Eow, Ewb.
      exact (waitBits_clear_head (iWbA s1) (olderWritersA s1) j tail (IMPL olderWriters_nz s1) Hnd Hwb).
    - intros r Hr; rewrite Eow in Hr; apply in_or_app; left; exact Hr.
  Qed.

  (* A dataMem request keeps the wait bits: a load's register moves to the older writers; any
   * other request has destination 0 (ALU fact A1) *)
  Lemma score_dm :
    forall g g' (s1 s1' : IState) j tail fo0 fo_tail q,
      ScoreRelA g s1 ->
      iD2aA s1 = j :: tail -> g_d2aFo pcAddrInit g = fo0 :: fo_tail ->
      iD2aA s1' = tail -> g_d2aFo pcAddrInit g' = fo_tail ->
      iDmBufA s1' = (iDmBufA s1 ++ [q])%list -> iDmStA s1' = iDmStA s1 -> iMdA s1' = iMdA s1 ->
      iWbA s1' = iWbA s1 ->
      mrDst q = d2aDst j ->
      (opIsLoad (mrOp q) = false -> d2aDst j = Zmod.zero) ->
      (forall y, In y tail -> daLiveA s1' y = true -> daLiveA s1 y = true) ->
      (forall l1 j2 l2 fo, tail = (l1 ++ j2 :: l2)%list -> nth_error fo_tail (length l1) = Some fo ->
         daLiveA s1' j2 = true ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs1 fo) ->
         RegAvoidAll (olderWritersA s1 ++ d2aWriters (j :: l1)) (decCs2 fo) ->
         evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) ->
      ScoreRelA g' s1'.
  Proof.
    intros g g' s1 s1' j tail fo0 fo_tail q Hsc Ed2a Efo Ed2a' Efo' Ebuf Est Emd Ewb Edst Hst Hlv Hrr.
    apply (IMPL ScoreRel_move_to_older g g' s1 s1' j tail fo0 fo_tail Hsc Ed2a Efo Ed2a' Efo');
      [| exact Ewb | exact Hlv | exact Hrr].
    eapply perm_trans; [exact (olderWriters_enq s1 s1' q Ebuf Est Emd) |].
    apply Permutation_app_head; unfold d2aWriters; cbn [map].
    destruct (opIsLoad (mrOp q)) eqn:El.
    - rewrite Edst; apply Permutation_refl.
    - rewrite (Hst eq_refl); cbn [filter]; rewrite Zmod.eqb_refl; cbn [negb]; apply Permutation_refl.
  Qed.

  (* Non-sequential, no virtual CSR read: ghost append. ALU facts A1 and A2 are premises until
   * proven (guide: plan b). *)
  Lemma exec_nonSeq_append :
    forall g (s1 s1r : IState) (s2 : SState) (a : type AluOutUnion),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1r Zmod.zero -> stRedirA s1 = false ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = true -> stIntA s1 = false ->
      a = stAluOutA s1 -> aluIsSeq a = false ->
      nonSeqGuardV (aluIsMemOrFence a) (stDmFullA s1) (aluIsVirtCsr a) (stDmEmptyA s1) (stNoWrA s1) = true ->
      isVirtualCsrAluOut a = false ->
      (aluIsMemOrFence a = true -> opIsLoad (nsDm a) = false -> aluDstIdx a = Zmod.zero) ->
      (aluIsExc a = false -> nsIsCf a = true -> CfOK (iPccA s1) (nsCf a)) ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1r) s2'.
  Proof.
    intros g s1 s1r s2 a Hg Hsem Hrd Hcp Hv Hlive Hint Ha Hns Hgd Hnv HA1 HA2.
    destruct (IMPL impl_nonSeq clint plic envI s1 s1r a Hsem Hcp Hrd Hv Hlive Hint Ha Hns Hgd)
      as [rfMid [x [Hex [Erf [Emem [Ed2a' [Emd [Eep0 [Efe0 [Erd [Efip Hdmc]]]]]]]]]]].
    (* the state the relation sees: with the redirect applied when there is one *)
    assert (Hred : if execRedirect a x (daPredPc (stJA s1))
                   then iExecEpochA (effSA s1r) = evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]) /\
                        iFetchA (effSA s1r) = fetch_withPc pcAddrInit fetchCapacity instCapacity
                                                (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1)
                                                   (getDefault (Option StraddleHalf)))
                                                (defNextPcc x).(Snd).(Snd).(Fst)
                   else iExecEpochA (effSA s1r) = iExecEpochA s1 /\ iFetchA (effSA s1r) = iFetchA s1).
    { destruct (execRedirect a x (daPredPc (stJA s1))) eqn:Er.
      - assert (Hv1 : IMPL iRedirValid s1r = true) by (unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity).
        rewrite (IMPL effS_true s1r Hv1); split.
        + rewrite (IMPL applyP_epoch s1r), Eep0; reflexivity.
        + rewrite (IMPL applyP_fetch s1r), Efe0; unfold redirTarget, redirPcc, iRedirect; rewrite Erd; reflexivity.
      - rewrite (eff_np s1 s1r Hrd Erd); split; [exact Eep0 | exact Efe0]. }
    clear Eep0 Efe0 Erd Hsem.
    rewrite <- (IMPL effS_rf s1r) in Erf.
    rewrite <- (IMPL effS_mem s1r) in Emem.
    rewrite <- (IMPL effS_decode s1r) in Ed2a'.
    rewrite <- (IMPL effS_md s1r) in Emd.
    rewrite <- (IMPL effS_fip s1r) in Efip.
    rewrite <- (IMPL effS_wb s1r), <- (IMPL effS_dm s1r) in Hdmc.
    set (s1' := effSA s1r) in *; clearbody s1'.
    assert (Hpc : pcAligned (iPccA s1').(Snd).(Snd).(Fst)).
    { pose proof Hg as HgW; destruct HgW as [_ _ _ _ _ _ _ _ _ _ _ [[_ [_ [Hpc0 _]]] _] _].
      unfold iPcc; rewrite Erf, readPcc_writePcc.
      exact (executeNonSequential_nextPcc_even pcAddrInit _ _ _ _ _ _ _ Hpc0 Hex). }
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 Hwf'].
    assert (Hlive' : daLiveA s1 (stJA s1) = true) by exact Hlive.
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ Hacc _ Hdq Hf Hs Hfr Hw _].
    destruct (IMPL live_head_fence_facts clintS clint plicS plic fwcs g s1 s2 (stJA s1) (tl (iD2aA s1)) Hf Hm Ed2a Hlive')
      as [Hfip _].
    pose proof Hs as Hs0; destruct Hs0 as [Hnd [_ [Hlen Hreg]]].
    rewrite Ed2a in Hlen, Hnd.
    destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen; discriminate Hlen |].
    destruct (Hreg [] (stJA s1) (tl (iD2aA s1)) fo0 Ed2a eq_refl Hlive') as [HaluIn _].
    assert (Ha1 : a = evalAluOut (iPccA s1) (daAluIn (stJA s1))) by (rewrite Ha; apply stAluOut_eq).
    assert (Ha2 : a = evalAluOut (iPccA s1) (evalRegRead pcAddrInit (evalDecode fo0) (iFlushA s1)))
      by (rewrite <- HaluIn; exact Ha1).
    assert (Ed : aluDstIdx a = d2aDst (stJA s1)) by (rewrite Ha1; apply d2aDst_aluDstIdx).
    pose proof (eq_trans (eq_sym (stInt_eq s1)) Hint) as Hint1.
    rewrite (stMeip_eq s1), (stMtip_eq s1) in Hint1, Hex.
    assert (Hneq : forall d v, In (d, v) (EXTA (iMdA s1)) -> Zmod.eqb d Zmod.zero = false ->
                     Zmod.eqb (aluDstIdx a) Zmod.zero = false -> d <> aluDstIdx a).
    { intros d v Hin Hzd Hza Heq; subst d.
      apply NoDup_app_iff in Hnd as [_ [_ Hdj]]; apply (Hdj (aluDstIdx a)).
      - unfold olderWriters; apply filter_In; split; [| rewrite Hzd; reflexivity].
        apply in_or_app; right; apply in_or_app; right.
        change (aluDstIdx a) with (fst (aluDstIdx a, v)); apply in_map; exact Hin.
      - rewrite Ed in Hza |- *; rewrite d2aWriters_cons, Hza; left; reflexivity. }
    pose proof (executeNonSequential_mulDiv_none pcAddrInit _ _ _ _ _ _ _ Hex) as Hmd0.
    destruct (nonSeq_dm pcAddrInit _ _ _ a _ _ _ Hns Hex) as [Hdm1 Hfi1].
    pose proof (nonSeq_semF s1 a rfMid x _ _ Hint1 Hns Hneq Hex) as HsemF.
    pose proof (nonSeq_flush s1 s1' a rfMid x Hmd0 Erf Emd) as Hfl.
    pose proof (append_ginst s1 s1' fo0 a _ x Ha2 Hnv Hint1 HsemF Hfl) as Hstep.
    set (e := mkGEntry fo0 (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) a (execDataMem x)) in Hstep.
    set (g1 := mkGhost pcAddrInit (g_chain pcAddrInit g ++ [GInst e])%list (g_rf0 pcAddrInit g)
                 (g_cnwb pcAddrInit g) (g_revOff pcAddrInit g) fo_tail (g_acc pcAddrInit g)).
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Epcc : iPccA s1' = defNextPcc x) by (rewrite (stPcc_eq s1'), Erf; apply readPcc_writePcc).
    pose proof Hw as Hw0; destruct Hw0 as [_ [_ [_ [W4 [W5 _]]]]].
    (* the dataMem request: queue, state and scoreboard *)
    assert (HD : iDmStA s1' = iDmStA s1 /\ DmQueueRelA g1 s1' /\ fifo_wf (dataMem_fifo dataMemCapacity (iDmA s1')) /\
                 ((forall y, In y (tl (iD2aA s1)) -> daLiveA s1' y = true -> daLiveA s1 y = true) ->
                  (forall l1 j2 l2 fo, tl (iD2aA s1) = (l1 ++ j2 :: l2)%list -> nth_error fo_tail (length l1) = Some fo ->
                     daLiveA s1' j2 = true ->
                     RegAvoidAll (olderWritersA s1 ++ d2aWriters (stJA s1 :: l1)) (decCs1 fo) ->
                     RegAvoidAll (olderWritersA s1 ++ d2aWriters (stJA s1 :: l1)) (decCs2 fo) ->
                     evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) ->
                  ScoreRelA g1 s1')).
    { assert (Hdec : optValid (execDataMem x) = true \/ optValid (execDataMem x) = false)
        by (destruct (optValid (execDataMem x)); [left | right]; reflexivity).
      destruct Hdec as [Hdv | Hdv]; rewrite Hdv in Hdmc; destruct Hdmc as [Ewb Edm].
      - destruct (Hdm1 Hdv) as [Hmf Hpay].
        destruct (dm_enq_facts s1 s1' (execDmReq a x) W4 (nonSeqGuard_dm _ _ _ _ _ Hgd Hmf) Edm) as [Ebuf [Est Hwfd]].
        split; [exact Est | split; [| split; [exact Hwfd |]]].
        + apply (IMPL DmQueueRel_snoc_some initLine g g1 s1 s1' s2 e (execDmReq a x) Hdq Hacc eq_refl eq_refl
                   (entryReq_exec fo0 _ _ a x Hdv) Ebuf).
        + intros Hlv Hrr.
          apply (score_dm g g1 s1 s1' (stJA s1) (tl (iD2aA s1)) fo0 fo_tail (execDmReq a x) Hs Ed2a Efo Ed2a2 eq_refl
                   Ebuf Est Emd Ewb Ed); [| exact Hlv | exact Hrr].
          intros Hl; rewrite <- Ed; apply HA1; [exact Hmf | rewrite <- Hpay; exact Hl].
      - split; [unfold iDmSt; rewrite Edm; reflexivity | split; [| split; [rewrite Edm; exact W4 |]]].
        + apply (IMPL DmQueueRel_snoc_none g g1 s1 s1' e Hdq eq_refl eq_refl Hdv).
          unfold iDmBuf; rewrite Edm; reflexivity.
        + intros Hlv Hrr.
          exact (score_clear g g1 s1 s1' (stJA s1) (tl (iD2aA s1)) fo0 fo_tail Hs Ed2a Efo Ed2a2 eq_refl Edm Emd Ewb
                   Hlv Hrr). }
    (* redirect or not: the live tail, the frontend and the fence flag *)
    assert (Ecp : iCurParcel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                 iCurParcel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
          by (destruct (execRedirect a x (daPredPc (stJA s1))); destruct Hred as [_ Efe0];
              unfold iCurParcel; rewrite Efe0; reflexivity).
    assert (HR : (forall y, In y (tl (iD2aA s1)) -> daLiveA s1' y = true -> daLiveA s1 y = true) /\
                 (forall l1 j2 l2 fo, tl (iD2aA s1) = (l1 ++ j2 :: l2)%list -> nth_error fo_tail (length l1) = Some fo ->
                    daLiveA s1' j2 = true ->
                    RegAvoidAll (olderWritersA s1 ++ d2aWriters (stJA s1 :: l1)) (decCs1 fo) ->
                    RegAvoidAll (olderWritersA s1 ++ d2aWriters (stJA s1 :: l1)) (decCs2 fo) ->
                    evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) /\
                 FrontRelA g1 s1' s2 /\
                 (entryIsFenceI e = true -> NoLiveA s1' /\ optValid (iStraddleA s1') = false) /\
                 fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') =
                   fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) /\
                 fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') =
                   fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
    { assert (Hdec : execRedirect a x (daPredPc (stJA s1)) = true \/ execRedirect a x (daPredPc (stJA s1)) = false)
        by (destruct (execRedirect a x (daPredPc (stJA s1))); [left | right]; reflexivity).
      destruct Hdec as [Hr | Hr]; rewrite Hr in Hred; destruct Hred as [Eep Efe].
      - assert (Eib : iInstBufA s1' = iInstBufA s1) by (unfold iInstBuf; rewrite Efe; reflexivity).
        assert (Efb : iFetchBufA s1' = iFetchBufA s1) by (unfold iFetchBuf; rewrite Efe; reflexivity).
        assert (Estr : optValid (iStraddleA s1') = false) by (unfold iStraddle; rewrite Efe; reflexivity).
        assert (Efpc : iFetchPcA s1' = (iPccA s1').(Snd).(Snd).(Fst))
          by (unfold iFetchPc, iPcc; rewrite Efe, Erf, readPcc_writePcc; reflexivity).
        destruct (IMPL redirect_FrontRel_NoLive initLine fwcs g g1 s1 s1' s2 s2 (stJA s1) (tl (iD2aA s1))
                    Hfr Ed2a Hlive' Ed2a2 Eib Efb Ereg Eep Estr Efpc Hpc) as [Hnl Hfr'].
        assert (Hstale : forall y, In y (tl (iD2aA s1)) -> daLiveA s1' y = false).
        { destruct Hnl as [Hnl0 _]; rewrite Ed2a2, Forall_forall in Hnl0; exact Hnl0. }
        split; [intros y Hin Hy; rewrite (Hstale y Hin) in Hy; discriminate Hy |].
        split; [intros l1 j2 l2 fo Hl1 _ Hy _ _; exfalso;
                assert (Hin : In j2 (tl (iD2aA s1))) by (rewrite Hl1; apply in_or_app; right; left; reflexivity);
                rewrite (Hstale j2 Hin) in Hy; discriminate Hy |].
        split; [exact Hfr' | split; [intros _; split; [exact Hnl | exact Estr] |]].
        split; rewrite Efe; reflexivity.
      - destruct (noRedirect_facts a x _ Hr) as [Hexc [_ [Hfi0 Epc]]].
        assert (Hnf : foFault fo0 = false) by exact (nonSeq_noFault pcAddrInit _ fo0 _ a Ha2 Hexc).
        destruct (nonSeq_pcc pcAddrInit _ _ _ a _ _ x _ Hns (HA2 Hexc) Hex Hr) as [Et Ee].
        split; [intros y _ Hy; unfold daLive in Hy |- *; rewrite Eep in Hy; exact Hy |].
        split; [exact (rr_step s1 s1' (stJA s1) (tl (iD2aA s1)) fo_tail a _ x _ _ Ha1 HsemF Hfl) |].
        split.
        + apply (IMPL FrontRel_step_no_redirect initLine fwcs g g1 s1 s1' s2 (stJA s1) (tl (iD2aA s1)) fo0 fo_tail
                   Hfr Ed2a Efo Hlive' Hnf Ed2a2 eq_refl Eep);
            try (unfold iInstBuf, iFetchBuf, iFetchPc, iPredEpoch, iCurParcel, iStraddle; rewrite Efe; reflexivity);
            try exact Ereg; rewrite Epcc; [exact Et | exact Ee | exact Epc].
        + split; [| split; rewrite Efe; reflexivity].
          intros Hfi; exfalso.
          change (entryIsFenceI (mkGEntry fo0 (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) a (execDataMem x))
                  = true) in Hfi.
          rewrite entryIsFenceI_exec, <- Hfi1, Hfi0 in Hfi; discriminate Hfi. }
    destruct HD as [Hdmst [Hdmq' [Hwfd Hsc']]].
    destruct HR as [Hlv [Hrr [Hfr' [Hpost [Efb Eib]]]]].
    apply (IMPL step_append_nonvirt clintS clint plicS plic initLine fwcs Hdisj
             g s1 s1' s2 (stJA s1) (tl (iD2aA s1)) fo0 fo_tail e g1
             Hg Ed2a Efo Hlive' eq_refl eq_refl eq_refl Hstep eq_refl Emem Hdmst Hdmq').
    - apply (IMPL FenceRel_snoc_step clintS clint plicS plic fwcs g g1 s1 s1' s2 (stJA s1) (tl (iD2aA s1)) e
               Hf Hm Ed2a Hlive' eq_refl Ereg); [| exact Hpost].
      rewrite Efip; apply fip_after; [exact Hfip |].
      exact (eq_trans Hfi1 (eq_sym (entryIsFenceI_exec fo0 (plicMeipOf (iPlicA s1)) (clintSampled (iClintA s1)) a x))).
    - exact (Hsc' Hlv Hrr).
    - exact Hfr'.
    - eapply (IMPL WfRel_exec_step);
        [exact Hw | exact Efb | exact Eib | exact Hwf' | exact Hwfd | rewrite Emd; exact W5 | exact Ereg
        | exact Ecp | exact Hpc | intros y Hy; rewrite Ed2a2 in Hy; rewrite Ed2a; right; exact Hy].
  Qed.

  (* Non-sequential virtual CSR read: lockstep (dataMem is empty, so the spec catches up first) *)
  Lemma exec_nonSeq_virt :
    forall g (s1 s1r : IState) (s2 : SState) (a : type AluOutUnion),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1r Zmod.zero -> stRedirA s1 = false ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = true -> stIntA s1 = false ->
      a = stAluOutA s1 -> aluIsSeq a = false ->
      nonSeqGuardV (aluIsMemOrFence a) (stDmFullA s1) (aluIsVirtCsr a) (stDmEmptyA s1) (stNoWrA s1) = true ->
      aluIsVirtCsr a = true ->
      (aluIsExc a = false -> nsIsCf a = true -> CfOK (iPccA s1) (nsCf a)) ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1r) s2'.
  Proof.
    intros g s1 s1r s2 a Hg Hsem Hrd Hcp Hv Hlive Hint Ha Hns Hgd Hvc HA2.
    destruct (IMPL impl_nonSeq clint plic envI s1 s1r a Hsem Hcp Hrd Hv Hlive Hint Ha Hns Hgd)
      as [rfMid [x [Hex [Erf [Emem [Ed2a' [Emd [Eep0 [Efe0 [Erd [Efip Hdmc]]]]]]]]]]].
    (* the state the relation sees: with the redirect applied when there is one *)
    assert (Hred : if execRedirect a x (daPredPc (stJA s1))
                   then iExecEpochA (effSA s1r) = evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]) /\
                        iFetchA (effSA s1r) = fetch_withPc pcAddrInit fetchCapacity instCapacity
                                                (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (iFetchA s1)
                                                   (getDefault (Option StraddleHalf)))
                                                (defNextPcc x).(Snd).(Snd).(Fst)
                   else iExecEpochA (effSA s1r) = iExecEpochA s1 /\ iFetchA (effSA s1r) = iFetchA s1).
    { destruct (execRedirect a x (daPredPc (stJA s1))) eqn:Er.
      - assert (Hv1 : IMPL iRedirValid s1r = true) by (unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity).
        rewrite (IMPL effS_true s1r Hv1); split.
        + rewrite (IMPL applyP_epoch s1r), Eep0; reflexivity.
        + rewrite (IMPL applyP_fetch s1r), Efe0; unfold redirTarget, redirPcc, iRedirect; rewrite Erd; reflexivity.
      - rewrite (eff_np s1 s1r Hrd Erd); split; [exact Eep0 | exact Efe0]. }
    clear Eep0 Efe0 Erd Hsem.
    rewrite <- (IMPL effS_rf s1r) in Erf.
    rewrite <- (IMPL effS_mem s1r) in Emem.
    rewrite <- (IMPL effS_decode s1r) in Ed2a'.
    rewrite <- (IMPL effS_md s1r) in Emd.
    rewrite <- (IMPL effS_fip s1r) in Efip.
    rewrite <- (IMPL effS_wb s1r), <- (IMPL effS_dm s1r) in Hdmc.
    set (s1' := effSA s1r) in *; clearbody s1'.
    assert (Hpc : pcAligned (iPccA s1').(Snd).(Snd).(Fst)).
    { pose proof Hg as HgW; destruct HgW as [_ _ _ _ _ _ _ _ _ _ _ [[_ [_ [Hpc0 _]]] _] _].
      unfold iPcc; rewrite Erf, readPcc_writePcc.
      exact (executeNonSequential_nextPcc_even pcAddrInit _ _ _ _ _ _ _ Hpc0 Hex). }
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 Hwf'].
    assert (Hlive' : daLiveA s1 (stJA s1) = true) by exact Hlive.
    destruct (dm_quiet g s1 s2 Hg (nonSeqGuard_virt _ _ _ _ _ Hgd Hvc)) as [Hbuf [Hlrq [Hms Hnp]]].
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm _ _ _ _ _ _ Hf Hs _ _ _].
    destruct (IMPL live_head_fence_facts clintS clint plicS plic fwcs g s1 s2 (stJA s1) (tl (iD2aA s1)) Hf Hm Ed2a Hlive')
      as [Hfip _].
    pose proof Hs as Hs0; destruct Hs0 as [Hnd [_ [Hlen Hreg]]].
    rewrite Ed2a in Hlen, Hnd.
    destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen; discriminate Hlen |].
    destruct (Hreg [] (stJA s1) (tl (iD2aA s1)) fo0 Ed2a eq_refl Hlive') as [HaluIn _].
    assert (Ha1 : a = evalAluOut (iPccA s1) (daAluIn (stJA s1))) by (rewrite Ha; apply stAluOut_eq).
    assert (Ha2 : a = evalAluOut (iPccA s1) (evalRegRead pcAddrInit (evalDecode fo0) (iFlushA s1)))
      by (rewrite <- HaluIn; exact Ha1).
    assert (Ha0 : a = evalAluOut (readPcc pcAddrInit (iRfA s1)) (daAluIn (stJA s1)))
      by (rewrite <- stPcc_eq; exact Ha1).
    assert (Ed : aluDstIdx a = d2aDst (stJA s1)) by (rewrite Ha1; apply d2aDst_aluDstIdx).
    pose proof (eq_trans (eq_sym (stInt_eq s1)) Hint) as Hint1.
    rewrite (stMeip_eq s1), (stMtip_eq s1) in Hint1, Hex.
    assert (Hneq : forall d v, In (d, v) (EXTA (iMdA s1)) -> Zmod.eqb d Zmod.zero = false ->
                     Zmod.eqb (aluDstIdx a) Zmod.zero = false -> d <> aluDstIdx a).
    { intros d v Hin Hzd Hza Heq; subst d.
      apply NoDup_app_iff in Hnd as [_ [_ Hdj]]; apply (Hdj (aluDstIdx a)).
      - unfold olderWriters; apply filter_In; split; [| rewrite Hzd; reflexivity].
        apply in_or_app; right; apply in_or_app; right.
        change (aluDstIdx a) with (fst (aluDstIdx a, v)); apply in_map; exact Hin.
      - rewrite Ed in Hza |- *; rewrite d2aWriters_cons, Hza; left; reflexivity. }
    pose proof (executeNonSequential_mulDiv_none pcAddrInit _ _ _ _ _ _ _ Hex) as Hmd0.
    destruct (nonSeq_dm pcAddrInit _ _ _ a _ _ _ Hns Hex) as [Hdm1 Hfi1].
    assert (Hdv : optValid (execDataMem x) = false).
    { apply not_true_is_false; intros Edv.
      destruct (Hdm1 Edv) as [Hmf _]; rewrite (memOrFence_virt_excl a Hmf) in Hvc; discriminate Hvc. }
    rewrite Hdv in Hdmc; destruct Hdmc as [Ewb Edm].
    pose proof (nonSeq_semF s1 a rfMid x _ _ Hint1 Hns Hneq Hex) as HsemF.
    pose proof (nonSeq_flush s1 s1' a rfMid x Hmd0 Erf Emd) as Hfl.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Epcc : iPccA s1' = defNextPcc x) by (rewrite (stPcc_eq s1'), Erf; apply readPcc_writePcc).
    pose proof (nonDeferred_of_nonSequential pcAddrInit defaultEnv _ _ _ a _ _ _ Hint1 Hns Hex) as Hnd'.
    rewrite (stPcc_eq s1) in Hnd'.
    apply (IMPL step_lockstep_commit clintS clint plicS plic initLine fwcs Hdisj HclintIdx HplicIdx
             g s1 s1' s2 (stJA s1) (tl (iD2aA s1)) a rfMid x
             Hg Ed2a Hlive' Hbuf Hlrq Hms Hnp Ha0 Hnd' Hdv Hmd0).
    - rewrite (iFlush_of s1' _ _ Erf Emd); symmetry; apply writePcc_flushMulDivCaps.
    - exact Emem.
    - exact Edm.
    - exact Emd.
    - rewrite Efip, Hfi1, Hdv; exact Hfip.
    - intros g' s2m s2' Hgm Efo' Htf.
      pose proof Hgm as Hgm0; destruct Hgm0 as [_ Hmm _ _ _ _ _ _ _ _ Hfrm Hwm _].
      rewrite Efo in Efo'; cbn [tl] in Efo'.
      assert (Ecp : iCurParcel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' =
                   iCurParcel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1)
            by (destruct (execRedirect a x (daPredPc (stJA s1))); destruct Hred as [_ Efe0];
                unfold iCurParcel; rewrite Efe0; reflexivity).
      assert (HR : (forall y, In y (tl (iD2aA s1)) -> daLiveA s1' y = true -> daLiveA s1 y = true) /\
                   (forall l1 j2 l2 fo, tl (iD2aA s1) = (l1 ++ j2 :: l2)%list -> nth_error fo_tail (length l1) = Some fo ->
                      daLiveA s1' j2 = true ->
                      RegAvoidAll (olderWritersA s1 ++ d2aWriters (stJA s1 :: l1)) (decCs1 fo) ->
                      RegAvoidAll (olderWritersA s1 ++ d2aWriters (stJA s1 :: l1)) (decCs2 fo) ->
                      evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1') = evalRegRead pcAddrInit (evalDecode fo) (iFlushA s1)) /\
                   FrontRelA g' s1' s2' /\
                   fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') =
                     fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1) /\
                   fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1') =
                     fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
      { assert (Hdec : execRedirect a x (daPredPc (stJA s1)) = true \/ execRedirect a x (daPredPc (stJA s1)) = false)
          by (destruct (execRedirect a x (daPredPc (stJA s1))); [left | right]; reflexivity).
        destruct Hdec as [Hr | Hr]; rewrite Hr in Hred; destruct Hred as [Eep Efe].
        - assert (Eib : iInstBufA s1' = iInstBufA s1) by (unfold iInstBuf; rewrite Efe; reflexivity).
          assert (Efb : iFetchBufA s1' = iFetchBufA s1) by (unfold iFetchBuf; rewrite Efe; reflexivity).
          assert (Estr : optValid (iStraddleA s1') = false) by (unfold iStraddle; rewrite Efe; reflexivity).
          assert (Efpc : iFetchPcA s1' = (iPccA s1').(Snd).(Snd).(Fst))
            by (unfold iFetchPc, iPcc; rewrite Efe, Erf, readPcc_writePcc; reflexivity).
          destruct (IMPL redirect_FrontRel_NoLive initLine fwcs g g' s1 s1' s2m s2' (stJA s1) (tl (iD2aA s1))
                      Hfrm Ed2a Hlive' Ed2a2 Eib Efb Ereg Eep Estr Efpc Hpc) as [Hnl Hfr'].
          assert (Hstale : forall y, In y (tl (iD2aA s1)) -> daLiveA s1' y = false).
          { destruct Hnl as [Hnl0 _]; rewrite Ed2a2, Forall_forall in Hnl0; exact Hnl0. }
          split; [intros y Hin Hy; rewrite (Hstale y Hin) in Hy; discriminate Hy |].
          split; [intros l1 j2 l2 fo Hl1 _ Hy _ _; exfalso;
                  assert (Hin : In j2 (tl (iD2aA s1))) by (rewrite Hl1; apply in_or_app; right; left; reflexivity);
                  rewrite (Hstale j2 Hin) in Hy; discriminate Hy |].
          split; [exact Hfr' |].
          split; rewrite Efe; reflexivity.
        - destruct (noRedirect_facts a x _ Hr) as [Hexc [_ [_ Epc]]].
          assert (Hnf : foFault fo0 = false) by exact (nonSeq_noFault pcAddrInit _ fo0 _ a Ha2 Hexc).
          destruct (nonSeq_pcc pcAddrInit _ _ _ a _ _ x _ Hns (HA2 Hexc) Hex Hr) as [Et Ee].
          split; [intros y _ Hy; unfold daLive in Hy |- *; rewrite Eep in Hy; exact Hy |].
          split; [exact (rr_step s1 s1' (stJA s1) (tl (iD2aA s1)) fo_tail a _ x _ _ Ha1 HsemF Hfl) |].
          split; [| split; rewrite Efe; reflexivity].
          apply (IMPL FrontRel_traceFrame initLine fwcs g' s1' s2m s2' (proj2 (proj2 Hmm)) Htf).
          apply (IMPL FrontRel_step_no_redirect initLine fwcs g g' s1 s1' s2m (stJA s1) (tl (iD2aA s1)) fo0 fo_tail
                   Hfrm Ed2a Efo Hlive' Hnf Ed2a2 Efo' Eep);
            try (unfold iInstBuf, iFetchBuf, iFetchPc, iPredEpoch, iCurParcel, iStraddle; rewrite Efe; reflexivity);
            try exact Ereg; rewrite Epcc; [exact Et | exact Ee | exact Epc]. }
      destruct HR as [Hlv [Hrr [Hfr' [Efb Eib]]]].
      split; [| split; [exact Hfr' |]].
      + exact (score_clear g g' s1 s1' (stJA s1) (tl (iD2aA s1)) fo0 fo_tail Hs Ed2a Efo Ed2a2 Efo' Edm Emd Ewb Hlv Hrr).
      + eapply (IMPL WfRel_exec_step);
          [exact Hwm | exact Efb | exact Eib | exact Hwf'
          | rewrite Edm; destruct Hwm as [_ [_ [_ [W4 _]]]]; exact W4
          | rewrite Emd; destruct Hwm as [_ [_ [_ [_ [W5 _]]]]]; exact W5 | exact Ereg
          | exact Ecp | exact Hpc | intros y Hy; rewrite Ed2a2 in Hy; rewrite Ed2a; right; exact Hy].
  Qed.

  (* --- 7. The Whole Stage --- *)

  (* A live head's ALU output is the ALU applied to a decoded instruction *)
  Lemma liveHead_aluOut :
    forall g (s1 : IState) (s2 : SState),
      RELG g s1 s2 -> (stHeadA s1).(Snd).(Fst) = true -> daLiveA s1 (stHeadA s1).(Fst) = true ->
      exists fo0, stAluOutA s1 = evalAluOut (iPccA s1) (evalRegRead pcAddrInit (evalDecode fo0) (iFlushA s1)).
  Proof.
    intros g s1 s2 Hg Hv Hlive.
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    assert (Hlive' : daLiveA s1 (stJA s1) = true) by exact Hlive.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ _ _ _ _ Hs _ _ _].
    destruct Hs as [_ [_ [Hlen Hreg]]].
    rewrite Ed2a in Hlen.
    destruct (g_d2aFo pcAddrInit g) as [| fo0 fo_tail] eqn:Efo; [cbn [length] in Hlen; discriminate Hlen |].
    destruct (Hreg [] (stJA s1) (tl (iD2aA s1)) fo0 Ed2a eq_refl Hlive') as [HaluIn _].
    exists fo0; rewrite <- HaluIn; apply stAluOut_eq.
  Qed.

  (* Every branch of the stage. The ALU facts A1 and A2 (guide: plan b) are premises, stated for
   * any decoded instruction; the theorem passes their proofs. *)
  Lemma exec_step :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = false ->
      (forall (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit),
         let a := evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) in
         aluIsMemOrFence a = true -> opIsLoad (nsDm a) = false -> aluDstIdx a = Zmod.zero) ->
      (forall (pcc : type FullECapWithTag) (fo : type FetchOut) (rf : RfState pcAddrInit),
         let a := evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf) in
         aluIsSeq a = false -> aluIsExc a = false -> nsIsCf a = true -> CfOK pcc (nsCf a)) ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1') s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hrd HA1g HA2g.
    destruct (ex_canProceed (iExecA s1)) eqn:Hcp; [| exact (exec_noCanProceed g s1 s1' s2 Hg Hsem Hrd Hcp)].
    destruct ((stHeadA s1).(Snd).(Fst)) eqn:Hv;
      [| exact (exec_stutter g s1 s1' s2 Hg (IMPL impl_noHead clint plic envI s1 s1' Hsem Hcp Hv) Hrd)].
    destruct (daLiveA s1 (stHeadA s1).(Fst)) eqn:Hlive; [| exact (exec_stale g s1 s1' s2 Hg Hsem Hrd Hcp Hv Hlive)].
    destruct (stIntA s1) eqn:Hint.
    - destruct (andb (stDmEmptyA s1) (stNoWrA s1)) eqn:Hq.
      + exact (exec_interrupt g s1 s1' s2 Hg Hsem Hrd Hcp Hv Hlive Hint Hq).
      + exact (exec_stutter g s1 s1' s2 Hg (IMPL impl_intStall clint plic envI s1 s1' Hsem Hcp Hrd Hv Hlive Hint Hq) Hrd).
    - destruct (liveHead_aluOut g s1 s2 Hg Hv Hlive) as [fo0 Hfo].
      pose proof (HA1g (iPccA s1) fo0 (iFlushA s1)) as HA1; pose proof (HA2g (iPccA s1) fo0 (iFlushA s1)) as HA2.
      cbv zeta in HA1, HA2; rewrite <- Hfo in HA1, HA2.
      destruct (aluIsSeq (stAluOutA s1)) eqn:Hseq.
      + destruct (seqGuardV (aluIsMul (stAluOutA s1)) (aluIsDiv (stAluOutA s1)) (stMulFullA s1) (stDivFullA s1)) eqn:Hgd.
        * exact (exec_seq g s1 s1' s2 _ Hg Hsem Hrd Hcp Hv Hlive Hint eq_refl Hseq Hgd).
        * exact (exec_stutter g s1 s1' s2 Hg
                   (IMPL impl_seqStall clint plic envI s1 s1' _ Hsem Hcp Hrd Hv Hlive Hint eq_refl Hseq Hgd) Hrd).
      + destruct (nonSeqGuardV (aluIsMemOrFence (stAluOutA s1)) (stDmFullA s1) (aluIsVirtCsr (stAluOutA s1))
                    (stDmEmptyA s1) (stNoWrA s1)) eqn:Hgd.
        * assert (Hdec : aluIsVirtCsr (stAluOutA s1) = true \/ aluIsVirtCsr (stAluOutA s1) = false)
            by (destruct (aluIsVirtCsr (stAluOutA s1)); [left | right]; reflexivity).
          destruct Hdec as [Hvc | Hvc].
          -- exact (exec_nonSeq_virt g s1 s1' s2 _ Hg Hsem Hrd Hcp Hv Hlive Hint eq_refl Hseq Hgd Hvc
                      (HA2 ltac:(first [exact Hseq | reflexivity]))).
          -- exact (exec_nonSeq_append g s1 s1' s2 _ Hg Hsem Hrd Hcp Hv Hlive Hint eq_refl Hseq Hgd
                      (eq_trans (eq_sym (virtCsr_eq _)) Hvc) HA1 (HA2 ltac:(first [exact Hseq | reflexivity]))).
        * exact (exec_stutter g s1 s1' s2 Hg
                   (IMPL impl_nonSeqStall clint plic envI s1 s1' _ Hsem Hcp Hrd Hv Hlive Hint eq_refl Hseq Hgd) Hrd).
  Qed.

  (* The stage from a state without a pending redirect (ALU facts A1 and A2 proven) *)
  Theorem exec_live_ok :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = false ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' (effSA s1') s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hrd.
    exact (exec_step g s1 s1' s2 Hg Hsem Hrd (aluFact_A1 pcAddrInit) (aluFact_A2 pcAddrInit)).
  Qed.

  (* --- 8. A Pending Redirect --- *)

  (* With a redirect pending every decode-to-ALU entry is stale: the stage stutters or drops one *)
  Theorem exec_pending_ok :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g (applyPA s1) s2 -> SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = true ->
      Forall (fun j => daExecEpoch j = iExecEpochA s1) (iD2aA s1) ->
      exists g', RELG g' (applyPA s1') s2.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hrd Hep.
    destruct (ex_canProceed (iExecA s1)) eqn:Hcp.
    2: { rewrite (IMPL impl_noCanProceed clint plic envI s1 s1' Hsem Hcp); exists g; exact Hg. }
    destruct ((stHeadA s1).(Snd).(Fst)) eqn:Hv.
    2: { destruct (IMPL impl_noHead clint plic envI s1 s1' Hsem Hcp Hv)
           as [Erf [Ewb [Emem [Efe [Ede [Edm [Emd [Eep [Efip Erd]]]]]]]]].
         exists g.
         apply (IMPL RefRelG_impl_ext clintS clint plicS plic initLine fwcs g (applyPA s1) (applyPA s1') s2);
           try assumption.
         - rewrite !(IMPL applyP_fetch), Efe; unfold redirTarget, redirPcc, iRedirect; rewrite Erd; reflexivity.
         - rewrite !(IMPL applyP_epoch), Eep; reflexivity. }
    pose proof (wf_d2a g (applyPA s1) s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    rewrite Ed2a in Hep; apply Forall_inv in Hep.
    assert (Hst' : Zmod.eqb (daExecEpoch (stHeadA s1).(Fst)) (stEffA s1) = false).
    { rewrite (IMPL stEff_true s1 Hrd).
      change (Zmod.eqb (daExecEpoch (stJA s1)) (evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]))
              = false).
      rewrite Hep; apply zmod_epoch_add1_neq. }
    destruct (IMPL impl_stale clint plic envI s1 s1' Hsem Hcp Hv Hst')
      as [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep [Efip Erd]]]]]]]]].
    assert (Hst : daLiveA (applyPA s1) (stHeadA (applyPA s1)).(Fst) = false).
    { change (Zmod.eqb (daExecEpoch (stJA s1)) (evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]))
              = false).
      rewrite Hep; apply zmod_epoch_add1_neq. }
    apply (exec_stale_of g (applyPA s1) (applyPA s1') s2 Hg Hv Hst); try assumption.
    - rewrite !(IMPL applyP_fetch), Efe; unfold redirTarget, redirPcc, iRedirect; rewrite Erd; reflexivity.
    - rewrite !(IMPL applyP_epoch), Eep; reflexivity.
  Qed.

  (* --- 9. The Redirect Invariant --- *)

  Local Abbreviation InvA := (IMPL RedirInv).

  Lemma inv_np_frame :
    forall (s1 s1' : IState),
      stRedirA s1 = false -> InvA s1 -> ex_redirect (iExecA s1') = ex_redirect (iExecA s1) ->
      iFetchA s1' = iFetchA s1 -> tagEcap (iPccA s1') = tagEcap (iPccA s1) ->
      iFenceIPendingA s1' = iFenceIPendingA s1 -> InvA s1'.
  Proof.
    intros s1 s1' Hrd [I1 [I2 _]] Erd Efe Ep Efip.
    apply (IMPL RedirInv_np_of).
    - unfold iRedirValid, ex_redirValid; rewrite Erd; exact Hrd.
    - unfold iFetchPcc; rewrite Efe, Ep; exact (I1 Hrd).
    - intros H; unfold iFetchFip; rewrite Efe; apply (I2 Hrd); rewrite <- Efip; exact H.
  Qed.

  (* after a redirect from a live head: everything still in the frontend is in the old epoch *)
  Lemma inv_after_redirect :
    forall g (s1 s1' : IState) (s2 : SState) j tl0,
      RELG g s1 s2 -> iD2aA s1 = j :: tl0 -> daLiveA s1 j = true -> iD2aA s1' = tl0 ->
      iFetchA s1' = iFetchA s1 -> iExecEpochA s1' = iExecEpochA s1 ->
      IMPL iRedirValid s1' = true -> tagEcap (IMPL redirPcc s1') = tagEcap (iPccA s1') -> InvA s1'.
  Proof.
    intros g s1 s1' s2 j tl0 Hg Ed2a Hlive Ed2a' Efe Eep Hv Hp.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ _ _ _ _ _ Hfr _ _].
    destruct Hfr as [F1 [_ [_ [F4 [F5 _]]]]].
    rewrite Ed2a in F1, F4, F5.
    pose proof (StalePrefix_live_head (daLiveA s1) j tl0 F1 Hlive) as Htl.
    assert (Hex : Exists (fun x => daLiveA s1 x = true) (j :: tl0)) by (left; exact Hlive).
    apply (IMPL RedirInv_p_of); [exact Hv | exact Hp | | |].
    - rewrite Ed2a', Eep; eapply Forall_impl; [| exact Htl]; intros y Hy; apply Zmod.eqb_eq; exact Hy.
    - unfold iInstBuf; rewrite Efe, Eep; eapply Forall_impl; [| exact (F4 Hex)]; intros y Hy; apply Zmod.eqb_eq; exact Hy.
    - unfold iFetchBuf; rewrite Efe, Eep; eapply Forall_impl; [| exact (F5 (or_introl Hex))]; intros y Hy;
        apply Zmod.eqb_eq; exact Hy.
  Qed.

  Lemma inv_stutter :
    forall (s1 s1' : IState), InvA s1 -> IMPL ExecStutter s1 s1' -> InvA s1'.
  Proof.
    intros s1 s1' Hi [Erf [Ewb [Emem [Efe [Ede [Edm [Emd [Eep [Efip Erd]]]]]]]]].
    refine (IMPL RedirInv_frame s1 s1' _ _ _ Efip _ _ Eep _ _ _ Hi).
    - unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity.
    - unfold iFetchPcc; rewrite Efe; reflexivity.
    - unfold iFetchFip; rewrite Efe; reflexivity.
    - unfold redirPcc, iRedirect; rewrite Erd; reflexivity.
    - unfold iPcc; rewrite Erf; reflexivity.
    - unfold iD2a; rewrite Ede; reflexivity.
    - unfold iInstBuf; rewrite Efe; reflexivity.
    - unfold iFetchBuf; rewrite Efe; reflexivity.
  Qed.

  Theorem exec_inv :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g (effSA s1) s2 -> InvA s1 -> SemAction envI STAGE s1 s1' Zmod.zero -> InvA s1'.
  Proof.
    intros g s1 s1' s2 Hg Hi Hsem.
    destruct (ex_canProceed (iExecA s1)) eqn:Hcp.
    2: { rewrite (IMPL impl_noCanProceed clint plic envI s1 s1' Hsem Hcp); exact Hi. }
    destruct ((stHeadA s1).(Snd).(Fst)) eqn:Hv.
    2: { exact (inv_stutter s1 s1' Hi (IMPL impl_noHead clint plic envI s1 s1' Hsem Hcp Hv)). }
    destruct (stRedirA s1) eqn:Hrd.
    - (* pending: the head is stale (its epoch is the old one) *)
      erewrite (IMPL effS_true) in Hg by exact Hrd.
      pose proof Hi as [_ [_ I3]]; destruct (I3 Hrd) as [Ip [Hep [Hib Hfb]]].
      pose proof (wf_d2a g (applyPA s1) s2 Hg) as Hwf.
      pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
      pose proof Hep as Hep0; rewrite Ed2a in Hep0; apply Forall_inv in Hep0.
      assert (Hst' : Zmod.eqb (daExecEpoch (stHeadA s1).(Fst)) (stEffA s1) = false).
      { rewrite (IMPL stEff_true s1 Hrd).
        change (Zmod.eqb (daExecEpoch (stJA s1)) (evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]))
                = false).
        rewrite Hep0; apply zmod_epoch_add1_neq. }
      destruct (IMPL impl_stale clint plic envI s1 s1' Hsem Hcp Hv Hst')
        as [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep [Efip Erd]]]]]]]]].
      destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 _].
      apply (IMPL RedirInv_p_of).
      + unfold iRedirValid, ex_redirValid; rewrite Erd; exact Hrd.
      + unfold redirPcc, iRedirect, iPcc; rewrite Erd, Erf; exact Ip.
      + rewrite Ed2a2, Eep; rewrite Ed2a in Hep; exact (Forall_inv_tail Hep).
      + unfold iInstBuf; rewrite Efe, Eep; exact Hib.
      + unfold iFetchBuf; rewrite Efe, Eep; exact Hfb.
    - erewrite (IMPL effS_false) in Hg by exact Hrd.
      pose proof (wf_d2a g s1 s2 Hg) as Hwf.
      pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
      destruct (daLiveA s1 (stHeadA s1).(Fst)) eqn:Hlive.
      2: { assert (Hst' : Zmod.eqb (daExecEpoch (stHeadA s1).(Fst)) (stEffA s1) = false)
             by (rewrite (IMPL stEff_false s1 Hrd); exact Hlive).
           destruct (IMPL impl_stale clint plic envI s1 s1' Hsem Hcp Hv Hst')
             as [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep [Efip Erd]]]]]]]]].
           apply (inv_np_frame s1 s1' Hrd Hi Erd Efe); [unfold iPcc; rewrite Erf; reflexivity | exact Efip]. }
      assert (Hlive' : daLiveA s1 (stJA s1) = true) by exact Hlive.
      destruct (stIntA s1) eqn:Hint.
      + destruct (andb (stDmEmptyA s1) (stNoWrA s1)) eqn:Hq.
        2: { exact (inv_stutter s1 s1' Hi (IMPL impl_intStall clint plic envI s1 s1' Hsem Hcp Hrd Hv Hlive Hint Hq)). }
        destruct (IMPL impl_interrupt clint plic envI s1 s1' Hsem Hcp Hrd Hv Hlive Hint Hq)
          as [rfMid [execOut [Hex [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep [Efip Erd]]]]]]]]]]]].
        destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 _].
        apply (inv_after_redirect g s1 s1' s2 (stJA s1) (tl (iD2aA s1)) Hg Ed2a Hlive' Ed2a2 Efe Eep).
        * unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity.
        * unfold redirPcc, iRedirect, iPcc; rewrite Erd, Erf, readPcc_writePcc; reflexivity.
      + destruct (liveHead_aluOut g s1 s2 Hg Hv Hlive) as [fo0 Hfo].
        destruct (aluIsSeq (stAluOutA s1)) eqn:Hseq.
        * destruct (seqGuardV (aluIsMul (stAluOutA s1)) (aluIsDiv (stAluOutA s1)) (stMulFullA s1) (stDivFullA s1)) eqn:Hgd.
          2: { exact (inv_stutter s1 s1' Hi
                        (IMPL impl_seqStall clint plic envI s1 s1' _ Hsem Hcp Hrd Hv Hlive Hint eq_refl Hseq Hgd)). }
          destruct (IMPL impl_seq clint plic envI s1 s1' _ Hsem Hcp Hrd Hv Hlive Hint eq_refl Hseq Hgd)
            as [rfMid [mdOpt [Hex [Erf [Emem [Efe [Ed2a' [Edm [Eep [Efip [Erd Hmd]]]]]]]]]]].
          apply (inv_np_frame s1 s1' Hrd Hi Erd Efe); [| exact Efip].
          unfold iPcc; rewrite Erf, readPcc_writePcc; reflexivity.
        * destruct (nonSeqGuardV (aluIsMemOrFence (stAluOutA s1)) (stDmFullA s1) (aluIsVirtCsr (stAluOutA s1))
                      (stDmEmptyA s1) (stNoWrA s1)) eqn:Hgd.
          2: { exact (inv_stutter s1 s1' Hi
                        (IMPL impl_nonSeqStall clint plic envI s1 s1' _ Hsem Hcp Hrd Hv Hlive Hint eq_refl Hseq Hgd)). }
          destruct (IMPL impl_nonSeq clint plic envI s1 s1' _ Hsem Hcp Hrd Hv Hlive Hint eq_refl Hseq Hgd)
            as [rfMid [x [Hex [Erf [Emem [Ed2a' [Emd [Eep [Efe [Erd [Efip Hdmc]]]]]]]]]]].
          destruct (execRedirect (stAluOutA s1) x (daPredPc (stJA s1))) eqn:Er.
          -- destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 _].
             apply (inv_after_redirect g s1 s1' s2 (stJA s1) (tl (iD2aA s1)) Hg Ed2a Hlive' Ed2a2 Efe Eep).
             ++ unfold iRedirValid, ex_redirValid; rewrite Erd; reflexivity.
             ++ unfold redirPcc, iRedirect, iPcc; rewrite Erd, Erf, readPcc_writePcc; reflexivity.
          -- destruct (noRedirect_facts _ x _ Er) as [Hexc [_ [Hfi _]]].
             pose proof (aluFact_A2 pcAddrInit (iPccA s1) fo0 (iFlushA s1)) as HA2; cbv zeta in HA2.
             rewrite <- Hfo in HA2.
             destruct (nonSeq_pcc pcAddrInit _ _ _ _ _ _ x _ Hseq (HA2 Hseq Hexc) Hex Er) as [Et Ee].
             apply (inv_np_frame s1 s1' Hrd Hi Erd Efe).
             ++ unfold iPcc at 1; rewrite Erf, readPcc_writePcc; unfold tagEcap; f_equal; [exact Et | exact Ee].
             ++ rewrite Efip, Hfi; reflexivity.
  Qed.


  (* With a redirect pending the stage stutters or drops a stale head: the redirect stays *)
  Lemma exec_pending_valid :
    forall (s1 s1' : IState),
      SemAction envI STAGE s1 s1' Zmod.zero -> stRedirA s1 = true -> fifo_wf (D2AF s1) ->
      Forall (fun j => daExecEpoch j = iExecEpochA s1) (iD2aA s1) ->
      stRedirA s1' = true.
  Proof.
    intros s1 s1' Hsem Hrd Hwf Hep.
    destruct (ex_canProceed (iExecA s1)) eqn:Hcp.
    2: { rewrite (IMPL impl_noCanProceed clint plic envI s1 s1' Hsem Hcp); exact Hrd. }
    destruct ((stHeadA s1).(Snd).(Fst)) eqn:Hv.
    2: { destruct (IMPL impl_noHead clint plic envI s1 s1' Hsem Hcp Hv) as [_ [_ [_ [_ [_ [_ [_ [_ [_ Erd]]]]]]]]].
         unfold stRedir, ex_redirValid; rewrite Erd; exact Hrd. }
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    rewrite Ed2a in Hep; apply Forall_inv in Hep.
    assert (Hst' : Zmod.eqb (daExecEpoch (stHeadA s1).(Fst)) (stEffA s1) = false).
    { rewrite (IMPL stEff_true s1 Hrd).
      change (Zmod.eqb (daExecEpoch (stJA s1)) (evalExpr (Add [ Var type Epoch (iExecEpochA s1) ; ($1 : Expr type Epoch) ]))
              = false).
      rewrite Hep; apply zmod_epoch_add1_neq. }
    destruct (IMPL impl_stale clint plic envI s1 s1' Hsem Hcp Hv Hst') as [_ [_ [_ [_ [_ [_ [_ [_ [_ Erd]]]]]]]]].
    unfold stRedir, ex_redirValid; rewrite Erd; exact Hrd.
  Qed.

  Theorem stepOK_exec :
    StepOKRR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs STAGE.
  Proof.
    intros s1 s1' s2 Hsem _ [Hi [g Hg]].
    pose proof (exec_inv g s1 s1' s2 Hg Hi Hsem) as Hi'.
    destruct (stRedirA s1) eqn:Hrd.
    - erewrite (IMPL effS_true) in Hg by exact Hrd.
      pose proof Hi as [_ [_ I3]]; destruct (I3 Hrd) as [_ [Hep _]].
      pose proof (wf_d2a g (applyPA s1) s2 Hg) as Hwf.
      destruct (exec_pending_ok g s1 s1' s2 Hg Hsem Hrd Hep) as [g' Hg'].
      exists s2; split; [apply NilAction; reflexivity |]; split; [exact Hi' | exists g'].
      erewrite (IMPL effS_true) by exact (exec_pending_valid s1 s1' Hsem Hrd Hwf Hep); exact Hg'.
    - erewrite (IMPL effS_false) in Hg by exact Hrd.
      destruct (exec_live_ok g s1 s1' s2 Hg Hsem Hrd) as [g' [s2' [Hss Hg']]].
      exists s2'; split; [exact Hss |]; split; [exact Hi' | exists g'; exact Hg'].
  Qed.

End ExecMain.
