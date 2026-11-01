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
From Cheriot.Proof Require Import RefExec RefExecImpl.

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
    intros dst op1 mOp; unfold extractMulDivEntries, MulDivWf, mdEnqMul, mdFullMul.
    destruct mulDivMode; intros smd Hwf Hnf.
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
    intros dst op1 dOp; unfold extractMulDivEntries, MulDivWf, mdEnqDiv, mdFullDiv.
    destruct mulDivMode; intros smd Hwf Hnf.
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
    intros dst op1 mOp; unfold MulDivWf, mdEnqMul; destruct mulDivMode; intros smd Hwf.
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [apply fifo_wf_enq; exact Hwm | exact Hwd].
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [apply fifo_wf_enq; exact Hwm | exact Hwd].
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [Fst Snd] in *; apply fifo_wf_enq; exact Hwf.
  Qed.

  Lemma WF_enqDiv : forall dst op1 dOp (smd : TreeState ElemState MDT), WF smd -> WF (ENQD dst op1 dOp smd).
  Proof.
    intros dst op1 dOp; unfold MulDivWf, mdEnqDiv; destruct mulDivMode; intros smd Hwf.
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [exact Hwm | apply fifo_wf_enq; exact Hwd].
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [Fst Snd] in *; destruct Hwf as [Hwm Hwd]; split; [exact Hwm | apply fifo_wf_enq; exact Hwd].
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [Fst Snd] in *; apply fifo_wf_enq; exact Hwf.
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

  Lemma exec_noCanProceed :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = false ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hcp.
    rewrite (IMPL impl_noCanProceed clint plic envI s1 s1' Hsem Hcp).
    exists g, s2; split; [apply NilAction; reflexivity | exact Hg].
  Qed.

  Lemma exec_stutter :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> IMPL ExecStutter s1 s1' ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 Hg [Erf [Ewb [Emem [Efe [Ede [Edm [Emd [Eep Efip]]]]]]]].
    exact (IMPL stutter_step clintS clint plicS plic initLine fwcs g s1 s1' s2 Hg Erf Ewb Emem Efe Ede Eep Efip Edm Emd).
  Qed.

  Lemma exec_stale :
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = false ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hcp Hv Hst.
    destruct (IMPL impl_stale clint plic envI s1 s1' Hsem Hcp Hv Hst)
      as [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep Efip]]]]]]]].
    pose proof (wf_d2a g s1 s2 Hg) as Hwf.
    pose proof (head_of_valid s1 Hwf Hv) as Ed2a.
    destruct (d2a_of_deq s1 s1' Hwf Ed2a') as [Ed2a2 Hwf'].
    destruct (IMPL step_stale_drop clintS clint plicS plic initLine fwcs g s1 s1' s2 (stJA s1) (tl (iD2aA s1))
                Hg Ed2a Ed2a2 Hst Ewb Hwf' Erf Emem Efe Edm Emd Eep Efip) as [g' Hg'].
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
    forall g (s1 s1' : IState) (s2 : SState),
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = true -> stIntA s1 = true ->
      andb (stDmEmptyA s1) (stNoWrA s1) = true ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 Hg Hsem Hcp Hv Hlive Hint Hq.
    destruct (IMPL impl_interrupt clint plic envI s1 s1' Hsem Hcp Hv Hlive Hint Hq)
      as [rfMid [execOut [Hex [Erf [Ewb [Emem [Efe [Ed2a' [Edm [Emd [Eep Efip]]]]]]]]]]].
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
                  Hfrm Ed2a Hlive' Ed2a2 Eib Efb Ereg Eep Estr Efpc) as [Hnl Hfr'].
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
      + eapply (IMPL WfRel_exec_step); [exact Hwm | | | exact Hwf' | | | exact Ereg].
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
      RELG g s1 s2 -> SemAction envI STAGE s1 s1' Zmod.zero ->
      ex_canProceed (iExecA s1) = true -> (stHeadA s1).(Snd).(Fst) = true ->
      daLiveA s1 (stHeadA s1).(Fst) = true -> stIntA s1 = false ->
      a = stAluOutA s1 -> aluIsSeq a = true ->
      seqGuardV (aluIsMul a) (aluIsDiv a) (stMulFullA s1) (stDivFullA s1) = true ->
      exists g' s2', SemActions envS specActs s2 s2' /\ RELG g' s1' s2'.
  Proof.
    intros g s1 s1' s2 a Hg Hsem Hcp Hv Hlive Hint Ha Hseq Hgd.
    destruct (IMPL impl_seq clint plic envI s1 s1' a Hsem Hcp Hv Hlive Hint Ha Hseq Hgd)
      as [rfMid [mdOpt [Hex [Erf [Emem [Efe [Ed2a' [Edm [Eep [Efip Hmd]]]]]]]]]].
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
        | rewrite Edm; exact W4 | exact Hwf5 | exact Ereg].
  Qed.

End ExecMain.
