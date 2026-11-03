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

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot Require Import SpecDefines SpecMulDiv Impl ImplCommon ImplStaged ImplMulDiv.
From Cheriot.Proof Require Import ShiftFifoLemmas FifoGen ImplStagedProof ImplMulDivProof StateRel RefMdEngine RefCoreRel SimExecute.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * MILESTONE 5: THE MULDIV RULES ON THE MULDIV SUBTREE
 * ===========================================================================
 * Each issue and stage rule keeps the flush entries and `MulDivWf`; each write-back pop removes the
 * entry it writes back. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Stepping through actions --- *)

Lemma peelA :
  forall {t : Tree Elem} {env : Env t} {k k' : Kind} (nm : string) (a : Action type t k')
         (cont : type k' -> Action type t k) old P,
    evalActionPropGen env (LetAction nm a cont) old P ->
    exists mid r, SemAction env a old mid r /\ evalActionPropGen env (cont r) mid P.
Proof. intros t env k k' nm a cont old P H; exact (evalActionPropGen_to_SemAction a old _ H). Qed.

Lemma ifA :
  forall {t : Tree Elem} {env : Env t} {k k' : Kind} (nm : string) (p : Expr type Bool)
         (tb fb : Action type t k') (cont : type k' -> Action type t k) old P,
    evalActionPropGen env (IfElse nm p tb fb cont) old P ->
    exists mid r, SemAction env (if evalExpr p then tb else fb) old mid r /\ evalActionPropGen env (cont r) mid P.
Proof.
  intros t env k k' nm p tb fb cont old P H; cbn [evalActionPropGen] in H.
  destruct (evalExpr p); exact (evalActionPropGen_to_SemAction _ old _ H).
Qed.

Lemma liftSem :
  forall {t : Tree Elem} (p : NodePath t) {k : Kind} {env : Env t} (a : Action type (getNode p) k) s s' r,
    SemAction env (liftAction p a) s s' r ->
    exists sub', SemAction (subEnv p env s) a (readSubTreeState p s) sub' r /\ s' = writeSubTreeState p s sub'.
Proof.
  intros t p k env a s s' r H.
  rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in H.
  destruct (evalActionPropGen_to_SemAction a _ _ H) as [sub' [r' [Ha [<- <-]]]].
  exists sub'; split; [exact Ha | reflexivity].
Qed.

Lemma toActionSem :
  forall {t : Tree Elem} {env : Env t} {k : Kind} (le : LetExpr type k) s s' r,
    SemAction env (toAction t le) s s' r -> s' = s /\ r = evalLetExpr le.
Proof.
  intros t env k le s s' r H; rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_toAction in H.
  destruct H as [-> ->]; split; reflexivity.
Qed.

Section FifoSem.
  Variable cap : nat.
  Variable k : Kind.

  Lemma firstSem : forall env f f' r, SemAction env (@ShiftFifo.first cap k type) f f' r -> f' = f /\ r = fifoFirstVal f.
  Proof.
    intros env f f' r H; rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_first_iff in H.
    destruct H as [-> ->]; split; reflexivity.
  Qed.

  Lemma deqSem : forall env f f' r, SemAction env (@ShiftFifo.deq cap k type) f f' r -> f' = fifoDeqState f.
  Proof. intros env f f' r H; rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_deq_iff in H; destruct H as [-> _]; reflexivity. Qed.

  Lemma enqSem : forall env v f f' r, SemAction env (@ShiftFifo.enq cap k type v) f f' r -> f' = fifoEnqState f v.
  Proof. intros env v f f' r H; rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_enq_iff in H; destruct H as [-> _]; reflexivity. Qed.
End FifoSem.

Lemma isFull1Sem :
  forall K env (f f' : TS (fifoTree 1 K)) r,
    SemAction env (@ShiftFifo.isFull 1 K type) f f' r -> f' = f /\ r = negb (match fifo_to_list f with [] => true | _ => false end).
Proof.
  intros K env f f' r H; rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_fifo_isFull in H.
  destruct H as [<- <-]; split; [reflexivity |].
  rewrite fifo1_to_list; destruct (bits1_cases (fifo1_size f)) as [E | E]; rewrite E; reflexivity.
Qed.

Lemma fifo1_wf : forall K (f : TS (fifoTree 1 K)), @fifo_wf 1 K f.
Proof.
  intros K f; unfold fifo_wf; change (fifo_size f) with (fifo1_size f).
  destruct (bits1_cases (fifo1_size f)) as [E | E]; rewrite E; cbv; lia.
Qed.

Lemma letE :
  forall {t : Tree Elem} {env : Env t} {k k' : Kind} (nm : string) (e : Expr type k')
         (cont : type k' -> Action type t k) old P,
    evalActionPropGen env (LetExp nm e cont) old P -> evalActionPropGen env (cont (evalExpr e)) old P.
Proof. intros t env k k' nm e cont old P H; exact H. Qed.

Lemma evalExpr_And3_Not :
  forall (a b c : Expr type Bool),
    evalExpr (And [a; b; Not c]) = true -> evalExpr a = true /\ evalExpr b = true /\ evalExpr c = false.
Proof.
  intros a b c; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b), (evalExpr c); cbn;
    intros H; try discriminate H; repeat split.
Qed.

Lemma pipeCanEnqSem :
  forall StateK n env (s s' : TS (stagedStagesTree StateK n)) r,
    SemAction env (stagedPipeCanEnq StateK n type) s s' r ->
    s' = s /\ r = match @fifo_to_list 1 StateK s.(Fst) with [] => true | _ => false end.
Proof.
  intros StateK n env [f rest] s' r H.
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold stagedPipeCanEnq, stagedPipeTree, stagedStagesTree in H; cbn [evalActionPropGen] in H.
  rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_isFull in H.
  cbn [evalActionPropGen] in H; destruct H as [<- <-]; split; [reflexivity |].
  cbn [Fst]; rewrite fifo1_to_list; destruct (bits1_cases (fifo1_size f)) as [E | E]; rewrite E; reflexivity.
Qed.

Lemma rd0 : forall {A} {f : A -> Type} name c0 cs (s : TreeState f (Node name (c0 :: cs))),
    readSubTreeState (@child0Path A name c0 cs) s = s.(Fst).
Proof. reflexivity. Qed.
Lemma rd1 : forall {A} {f : A -> Type} name c0 c1 cs (s : TreeState f (Node name (c0 :: c1 :: cs))),
    readSubTreeState (@child1Path A name c0 c1 cs) s = s.(Snd).(Fst).
Proof. reflexivity. Qed.
Lemma wr0 : forall {A} {f : A -> Type} name c0 cs (s : TreeState f (Node name (c0 :: cs))) v,
    writeSubTreeState (@child0Path A name c0 cs) s v = (v ,, s.(Snd)).
Proof. reflexivity. Qed.
Lemma wr1 : forall {A} {f : A -> Type} name c0 c1 cs (s : TreeState f (Node name (c0 :: c1 :: cs))) v,
    writeSubTreeState (@child1Path A name c0 c1 cs) s v = (s.(Fst) ,, (v ,, s.(Snd).(Snd))).
Proof. reflexivity. Qed.

Lemma retSem :
  forall {t : Tree Elem} {env : Env t} {k : Kind} (e : Expr type k) s s' r,
    SemAction env (Return e) s s' r -> s' = s.
Proof. intros t env k e s s' r H; rewrite SemAction_iff_evalActionPropGen in H; destruct H as [<- _]; reflexivity. Qed.

Ltac dlift H :=
  let H' := fresh in destruct (liftSem _ _ _ _ _ H) as [? [H' ->]]; clear H; rename H' into H.

Ltac peel H Hs :=
  let H' := fresh in destruct (peelA _ _ _ _ _ H) as [? [? [Hs H']]]; clear H; rename H' into H.

Lemma iterCanEnqSem :
  forall StateK n env (w w' : TS (stagedIterTree StateK n)) r,
    SemAction env (stagedIterCanEnq StateK n type) w w' r -> w' = w /\ r = negb w.(Fst).
Proof.
  intros StateK n env [busy [rem [st []]]] w' r H.
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold stagedIterCanEnq, stagedWorkRegPath, stagedIterTree in H.
  revert H; cbn -[iterStepsSz]; intros [<- <-]; split; reflexivity.
Qed.

Lemma iterStep_keep :
  forall StateK OutK n (stepFn : forall ty, ty StateK -> LetExpr ty StateK)
         (finishFn : forall ty, ty StateK -> LetExpr ty OutK) proj env (w w' : TS (stagedIterTree StateK n)) r,
    SemAction env (stagedIterStep StateK n stepFn type) w w' r ->
    w'.(Fst) = w.(Fst) /\
    forall dst, extractIterEngineEntries n stepFn finishFn proj w' dst = extractIterEngineEntries n stepFn finishFn proj w dst.
Proof.
  intros StateK OutK n stepFn finishFn proj env w w' r H; apply iterStep_char in H; subst w'.
  destruct w as [busy [rem [st []]]]; cbn [Fst Snd].
  destruct (andb busy (negb (Zmod.eqb rem Zmod.zero))) eqn:E; [| split; reflexivity].
  apply andb_true_iff in E as [-> E]; apply negb_true_iff in E.
  split; [reflexivity |]; intros dst.
  unfold extractIterEngineEntries, mkWork; cbn [Fst Snd].
  rewrite (iterStepN_rem_step StateK n stepFn rem st E); reflexivity.
Qed.

Lemma evalExpr_And2 :
  forall (a b : Expr type Bool), evalExpr (And [a; b]) = true -> evalExpr a = true /\ evalExpr b = true.
Proof.
  intros a b; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b); cbn; intros H;
    try discriminate H; split; reflexivity.
Qed.

Lemma retSemV :
  forall {t : Tree Elem} {env : Env t} {k : Kind} (e : Expr type k) s s' r,
    SemAction env (Return e) s s' r -> s' = s /\ r = evalExpr e.
Proof. intros t env k e s s' r H; rewrite SemAction_iff_evalActionPropGen in H; destruct H as [<- <-]; split; reflexivity. Qed.

Lemma extractIter_done :
  forall StateK OutK n stepFn (finishFn : forall ty, ty StateK -> LetExpr ty OutK) proj
         (w : TS (stagedIterTree StateK n)) (dst : TS (fifoTree MulDivFifoCapacity RegIdx)) d,
    w.(Fst) = true -> w.(Snd).(Fst) = Zmod.zero -> fifo_to_list dst = [d] ->
    extractIterEngineEntries n stepFn finishFn proj w dst =
    [(d, mkMulDivCap (proj (evalLetExpr (finishFn type w.(Snd).(Snd).(Fst)))))].
Proof.
  intros StateK OutK n stepFn finishFn proj w dst d Hb Hr Hd.
  unfold extractIterEngineEntries; rewrite Hd, Hb, Hr, Zmod.unsigned_0; reflexivity.
Qed.

Lemma extractIter_idle :
  forall StateK OutK n stepFn (finishFn : forall ty, ty StateK -> LetExpr ty OutK) proj
         (w : TS (stagedIterTree StateK n)) (dst : TS (fifoTree MulDivFifoCapacity RegIdx)),
    w.(Fst) = false -> extractIterEngineEntries n stepFn finishFn proj w dst = [].
Proof.
  intros StateK OutK n stepFn finishFn proj w dst Hb.
  unfold extractIterEngineEntries; destruct (fifo_to_list dst); rewrite ?Hb; reflexivity.
Qed.

Ltac rdstep H :=
  let H1 := fresh "H1" in
  peel H H1; repeat dlift H1;
  first [ destruct (firstSem _ _ _ _ _ _ H1) as [-> ->]
        | destruct (pipeCanEnqSem _ _ _ _ _ _ H1) as [-> ->]
        | destruct (iterCanEnqSem _ _ _ _ _ _ H1) as [-> ->]
        | destruct (isFull1Sem _ _ _ _ _ H1) as [-> ->] ];
  rewrite ?writeSubTreeState_readSubTreeState in H; clear H1.

Ltac mdcbn :=
  cbn [readSubTreeState writeSubTreeState readSubTreeState_child writeSubTreeState_child child0Path child1Path
       implMulDivTree getNode getNodeChildren Fst Snd] in *.

(* An issue rule up to its state change: `Hen` the engine's enqueue, `Ev`/`Ec`/`Ef` the guard *)
Ltac issue_steps H Hwf :=
  rdstep H; rdstep H; rdstep H;
  let m := fresh "m" in let rr := fresh "rr" in let Hb := fresh "Hb" in let Hc := fresh "Hc" in
  destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H;
  let Em := fresh in destruct Hc as [Em _]; subst;
  let Ec := fresh "Ec" in
  match type of Hb with SemAction _ (if ?c then _ else _) _ _ _ => destruct c eqn:Ec end;
  [| apply retSem in Hb; subst; split; [exact Hwf | reflexivity] ];
  let Ev := fresh "Ev" in let Eg := fresh "Eg" in let Ef := fresh "Ef" in
  apply evalExpr_And3_Not in Ec; destruct Ec as [Ev [Eg Ef]];
  rewrite SemAction_iff_evalActionPropGen in Hb;
  do 5 apply letE in Hb;
  let H1 := fresh "H1" in let Hen := fresh "Hen" in let H2 := fresh "H2" in let H3 := fresh "H3" in
  peel Hb H1; destruct (toActionSem _ _ _ _ H1) as [-> ->]; clear H1;
  peel Hb Hen; repeat dlift Hen;
  match type of Hen with SemAction _ _ _ ?x _ => rename x into eng' end;
  peel Hb H2; repeat dlift H2;
  destruct (evalActionPropGen_to_SemAction _ _ _ Hb) as [? [? [H3 [<- _]]]]; clear Hb;
  repeat dlift H3;
  apply deqSem in H3; apply enqSem in H2; subst;
  mdcbn; cbn [evalExpr] in Eg, Ef.

Section MdRules.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Hypothesis Hmd : Is_true (mulDivStagesDivideXlen mulStages divStages).

  Local Abbreviation W := (Z.to_nat Xlen).
  Local Abbreviation MDTm m := (implMulDivTree mulCapacity divCapacity W mulStages divStages m).
  Local Abbreviation WFm m := (MulDivWf mulCapacity divCapacity mulStages divStages m).
  Local Abbreviation EXTm m := (extractMulDivEntries mulCapacity divCapacity mulStages divStages m).

  Lemma pm_issueMul :
    forall env (smd smd' : TS (MDTm PipelinedMul_IterDiv)) v d,
      WFm PipelinedMul_IterDiv smd ->
      SemAction env (nth 0 (mulDivIssueRules mulCapacity divCapacity W mulStages divStages PipelinedMul_IterDiv type) d)
        smd smd' v ->
      WFm PipelinedMul_IterDiv smd' /\ EXTm PipelinedMul_IterDiv smd' = EXTm PipelinedMul_IterDiv smd.
  Proof.
    intros env smd smd' v d Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    issue_steps H Hwf.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [[Hwq Hwd] [Hlen Hbusy]].
    change (@fifo_to_list MulDivFifoCapacity RegIdx) with (@fifo_to_list 1 RegIdx) in *.
    change ((@fifoFirstVal mulCapacity MulReq (Fst (Fst smd))).(Snd).(Fst) = true) in Ev.
    rewrite (fifoFirstVal_valid _ _ _ Hwq) in Ev.
    pose proof (fifo_to_list_deq _ _ _ Hwq) as Edq.
    destruct (fifo_to_list (Fst (Fst smd))) as [| q qs] eqn:Eq; [discriminate Ev |].
    pose proof (fifoFirstVal_data _ _ _ q qs Eq) as Eqd.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))) as [| d0 ds] eqn:Ed; [| discriminate Ef].
    destruct (@fifo_to_list 1 (MulStageState (dataLen W)) (Fst (Fst (Fst (Snd (Fst smd)))))) as [| t0 ts] eqn:Et; [| discriminate Eg].
    apply length_zero_iff_nil in Hlen.
    unfold mulPipeEnq in Hen.
    destruct (pipeEnq_char _ _ _ _ _ _ _ _ _ Et Hen) as [Eeng' Eeng's]; clear Hen.
    change MulDivFifoCapacity with 1%nat in *.
    remember (@fifoFirstVal mulCapacity MulReq (Fst (Fst smd))) as fv eqn:Efv.
    destruct fv as [fq [fvb []]]; cbn [Fst] in Eqd; subst fq.
    pose proof (states_top _ mulStages eng') as T1.
    pose proof (states_top _ mulStages (Fst (Fst (Snd (Fst smd))))) as T0.
    rewrite Hlen, Et in T0; cbn [map] in T0; rewrite app_nil_r in T0.
    rewrite (pipeBelow_snd _ mulStages eng' _ Eeng's), <- T0, Eeng' in T1; cbn [map app] in T1.
    rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [app].
    split; [split; [split; [apply fifo_wf_deq; exact Hwq | exact Hwd] | split; [rewrite T1; reflexivity | exact Hbusy]] |].
    rewrite Edq; unfold extractPipeEngineEntries; change MulDivFifoCapacity with 1%nat.
    rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed, T1, Hlen; cbn [combine map tl app].
    f_equal.
    rewrite <- (mul_result_pipe mulStages divStages Hmd q).
    reflexivity.
  Qed.
  Lemma pm_issueDiv :
    forall env (smd smd' : TS (MDTm PipelinedMul_IterDiv)) v d,
      WFm PipelinedMul_IterDiv smd ->
      SemAction env (nth 1 (mulDivIssueRules mulCapacity divCapacity W mulStages divStages PipelinedMul_IterDiv type) d)
        smd smd' v ->
      WFm PipelinedMul_IterDiv smd' /\ EXTm PipelinedMul_IterDiv smd' = EXTm PipelinedMul_IterDiv smd.
  Proof.
    intros env smd smd' v d Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    issue_steps H Hwf.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [[Hwq Hwd] [Hlen Hbusy]].
    change (@fifo_to_list MulDivFifoCapacity RegIdx) with (@fifo_to_list 1 RegIdx) in *.
    change ((@fifoFirstVal divCapacity DivReq (Fst (Fst (Snd smd)))).(Snd).(Fst) = true) in Ev.
    rewrite (fifoFirstVal_valid _ _ _ Hwd) in Ev.
    pose proof (fifo_to_list_deq _ _ _ Hwd) as Edq.
    destruct (fifo_to_list (Fst (Fst (Snd smd)))) as [| q qs] eqn:Eq; [discriminate Ev |].
    pose proof (fifoFirstVal_data _ _ _ q qs Eq) as Eqd.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))) as [| d0 ds] eqn:Ed; [| discriminate Ef].
    apply negb_true_iff in Eg.
    unfold divIterEnq in Hen; apply iterEnq_char in Hen; rewrite Eg in Hen; subst eng'.
    change MulDivFifoCapacity with 1%nat in *.
    remember (@fifoFirstVal divCapacity DivReq (Fst (Fst (Snd smd)))) as fv eqn:Efv.
    destruct fv as [fq [fvb []]]; cbn [Fst] in Eqd; subst fq.
    rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [app].
    split; [split; [split; [exact Hwq | apply fifo_wf_deq; exact Hwd] | split; [exact Hlen |]] |].
    - unfold IterBusyRel, mkWork; cbn [Fst]; split; [intros _; discriminate | intros _; reflexivity].
    - rewrite Edq; unfold extractIterEngineEntries, mkWork; change MulDivFifoCapacity with 1%nat.
      rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [Fst Snd tl map app].
      apply f_equal; cbn [app]; f_equal.
      rewrite <- (div_result_iter mulStages divStages Hmd q).
      reflexivity.
  Qed.
  Lemma sep_issueMul :
    forall env (smd smd' : TS (MDTm IterMul_SeparateIterDiv)) v d,
      WFm IterMul_SeparateIterDiv smd ->
      SemAction env (nth 0 (mulDivIssueRules mulCapacity divCapacity W mulStages divStages IterMul_SeparateIterDiv type) d)
        smd smd' v ->
      WFm IterMul_SeparateIterDiv smd' /\ EXTm IterMul_SeparateIterDiv smd' = EXTm IterMul_SeparateIterDiv smd.
  Proof.
    intros env smd smd' v d Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    issue_steps H Hwf.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [[Hwq Hwd] [Hbm Hbd]].
    change (@fifo_to_list MulDivFifoCapacity RegIdx) with (@fifo_to_list 1 RegIdx) in *.
    change ((@fifoFirstVal mulCapacity MulReq (Fst (Fst smd))).(Snd).(Fst) = true) in Ev.
    rewrite (fifoFirstVal_valid _ _ _ Hwq) in Ev.
    pose proof (fifo_to_list_deq _ _ _ Hwq) as Edq.
    destruct (fifo_to_list (Fst (Fst smd))) as [| q qs] eqn:Eq; [discriminate Ev |].
    pose proof (fifoFirstVal_data _ _ _ q qs Eq) as Eqd.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))) as [| d0 ds] eqn:Ed; [| discriminate Ef].
    apply negb_true_iff in Eg.
    unfold mulIterEnq in Hen; apply iterEnq_char in Hen; rewrite Eg in Hen; subst eng'.
    change MulDivFifoCapacity with 1%nat in *.
    remember (@fifoFirstVal mulCapacity MulReq (Fst (Fst smd))) as fv eqn:Efv.
    destruct fv as [fq [fvb []]]; cbn [Fst] in Eqd; subst fq.
    rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [app].
    split; [split; [split; [apply fifo_wf_deq; exact Hwq | exact Hwd] | split; [| exact Hbd]] |].
    - unfold IterBusyRel, mkWork; cbn [Fst]; split; [intros _; discriminate | intros _; reflexivity].
    - rewrite Edq; unfold extractIterEngineEntries, mkWork; change MulDivFifoCapacity with 1%nat.
      rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [Fst Snd tl map app].
      cbn [app]; f_equal.
      rewrite <- (mul_result_iter mulStages divStages Hmd q).
      reflexivity.
  Qed.

  Lemma sep_issueDiv :
    forall env (smd smd' : TS (MDTm IterMul_SeparateIterDiv)) v d,
      WFm IterMul_SeparateIterDiv smd ->
      SemAction env (nth 1 (mulDivIssueRules mulCapacity divCapacity W mulStages divStages IterMul_SeparateIterDiv type) d)
        smd smd' v ->
      WFm IterMul_SeparateIterDiv smd' /\ EXTm IterMul_SeparateIterDiv smd' = EXTm IterMul_SeparateIterDiv smd.
  Proof.
    intros env smd smd' v d Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    issue_steps H Hwf.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [[Hwq Hwd] [Hbm Hbd]].
    change (@fifo_to_list MulDivFifoCapacity RegIdx) with (@fifo_to_list 1 RegIdx) in *.
    change ((@fifoFirstVal divCapacity DivReq (Fst (Fst (Snd smd)))).(Snd).(Fst) = true) in Ev.
    rewrite (fifoFirstVal_valid _ _ _ Hwd) in Ev.
    pose proof (fifo_to_list_deq _ _ _ Hwd) as Edq.
    destruct (fifo_to_list (Fst (Fst (Snd smd)))) as [| q qs] eqn:Eq; [discriminate Ev |].
    pose proof (fifoFirstVal_data _ _ _ q qs Eq) as Eqd.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))) as [| d0 ds] eqn:Ed; [| discriminate Ef].
    apply negb_true_iff in Eg.
    unfold divIterEnq in Hen; apply iterEnq_char in Hen; rewrite Eg in Hen; subst eng'.
    change MulDivFifoCapacity with 1%nat in *.
    remember (@fifoFirstVal divCapacity DivReq (Fst (Fst (Snd smd)))) as fv eqn:Efv.
    destruct fv as [fq [fvb []]]; cbn [Fst] in Eqd; subst fq.
    rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [app].
    split; [split; [split; [exact Hwq | apply fifo_wf_deq; exact Hwd] | split; [exact Hbm |]] |].
    - unfold IterBusyRel, mkWork; cbn [Fst]; split; [intros _; discriminate | intros _; reflexivity].
    - rewrite Edq; unfold extractIterEngineEntries, mkWork; change MulDivFifoCapacity with 1%nat.
      rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [Fst Snd tl map app].
      apply f_equal; cbn [app]; f_equal.
      rewrite <- (div_result_iter mulStages divStages Hmd q).
      reflexivity.
  Qed.

  Lemma sh_issue :
    forall env (smd smd' : TS (MDTm IterMul_SharedIterDiv)) v d,
      WFm IterMul_SharedIterDiv smd ->
      SemAction env (nth 0 (mulDivIssueRules mulCapacity divCapacity W mulStages divStages IterMul_SharedIterDiv type) d)
        smd smd' v ->
      WFm IterMul_SharedIterDiv smd' /\ EXTm IterMul_SharedIterDiv smd' = EXTm IterMul_SharedIterDiv smd.
  Proof.
    intros env smd smd' v d Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    issue_steps H Hwf.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hwq Hb].
    change (@fifo_to_list MulDivFifoCapacity RegIdx) with (@fifo_to_list 1 RegIdx) in *.
    change ((@fifoFirstVal mulCapacity MulDivReq (Fst smd)).(Snd).(Fst) = true) in Ev.
    rewrite (fifoFirstVal_valid _ _ _ Hwq) in Ev.
    pose proof (fifo_to_list_deq _ _ _ Hwq) as Edq.
    destruct (fifo_to_list (Fst smd)) as [| q qs] eqn:Eq; [discriminate Ev |].
    pose proof (fifoFirstVal_data _ _ _ q qs Eq) as Eqd.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd smd))))) as [| d0 ds] eqn:Ed; [| discriminate Ef].
    apply negb_true_iff in Eg.
    unfold sharedIterEnq in Hen; apply iterEnq_char in Hen; rewrite Eg in Hen; subst eng'.
    change MulDivFifoCapacity with 1%nat in *.
    remember (@fifoFirstVal mulCapacity MulDivReq (Fst smd)) as fv eqn:Efv.
    destruct fv as [fq [fvb []]]; cbn [Fst] in Eqd; subst fq.
    rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [app].
    split; [split; [apply fifo_wf_deq; exact Hwq |] |].
    - unfold IterBusyRel, mkWork; cbn [Fst]; split; [intros _; discriminate | intros _; reflexivity].
    - rewrite Edq; unfold extractIterEngineEntries, mkWork; change MulDivFifoCapacity with 1%nat.
      rewrite (fifo_to_list_enq _ _ _ _ (fifo1_wf _ _) ltac:(rewrite Ed; cbn; lia)), Ed; cbn [Fst Snd tl map app].
      cbn [app]; f_equal.
      rewrite <- (shared_result mulStages divStages Hmd q).
      reflexivity.
  Qed.
  Lemma pipeEntries_eq :
    forall s s' dst,
      pipeRes _ (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st') mulStages s' =
      pipeRes _ (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st') mulStages s ->
      extractPipeEngineEntries mulStages s' dst = extractPipeEngineEntries mulStages s dst.
  Proof.
    intros s s' dst E; unfold extractPipeEngineEntries, pipeRes in *.
    generalize (fifo_to_list dst) as l; revert E.
    generalize (extractPipeStageStates mulStages s') as x, (extractPipeStageStates mulStages s) as y.
    induction x as [| [k st] x IH]; intros [| [k' st'] y] E l; try discriminate E; destruct l as [| a l]; try reflexivity.
    rewrite !map_cons in E.
    pose proof (f_equal (@hd _ st) E) as E1; pose proof (f_equal (@tl _) E) as E2; clear E.
    cbn [hd tl fst snd] in E1, E2.
    cbn [combine]; rewrite !map_cons; f_equal; [cbv beta iota zeta; rewrite E1; reflexivity | exact (IH y E2 l)].
  Qed.

  Lemma pm_stage :
    forall r, In r (mulDivAllStageRules mulCapacity divCapacity W mulStages divStages PipelinedMul_IterDiv type) ->
    forall env (smd smd' : TS (MDTm PipelinedMul_IterDiv)) v,
      WFm PipelinedMul_IterDiv smd -> SemAction env r smd smd' v ->
      WFm PipelinedMul_IterDiv smd' /\ EXTm PipelinedMul_IterDiv smd' = EXTm PipelinedMul_IterDiv smd.
  Proof.
    intros r Hin env smd smd' v Hwf H.
    unfold mulDivAllStageRules in Hin; apply in_app_or in Hin as [Hin | [<- | []]].
    - apply in_map_iff in Hin as [r0 [<- Hr0]].
      repeat dlift H.
      pose proof (pipeChain_res _ _ mulStages r0 Hr0 _ _ _ _ H) as Er.
      mdcbn; unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
      destruct Hwf as [Hq [Hlen Hb]].
      split; [split; [exact Hq | split; [| exact Hb]] |].
      + rewrite <- Hlen; apply (f_equal (@length _)) in Er; unfold pipeRes in Er; rewrite !length_map in Er; exact Er.
      + rewrite (pipeEntries_eq _ _ _ Er); reflexivity.
    - repeat dlift H.
      destruct (iterStep_keep _ (DivOutput (dataLen W)) _ _ (@divFinishStage W) (fun o => evalExpr (#o`"res")) _ _ _ _ H) as [Eb Ee].
      mdcbn; unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
      destruct Hwf as [Hq [Hlen Hb]].
      split; [split; [exact Hq | split; [exact Hlen | rewrite Eb; exact Hb]] | rewrite Ee; reflexivity].
  Qed.

  Lemma sep_stage :
    forall r, In r (mulDivAllStageRules mulCapacity divCapacity W mulStages divStages IterMul_SeparateIterDiv type) ->
    forall env (smd smd' : TS (MDTm IterMul_SeparateIterDiv)) v,
      WFm IterMul_SeparateIterDiv smd -> SemAction env r smd smd' v ->
      WFm IterMul_SeparateIterDiv smd' /\ EXTm IterMul_SeparateIterDiv smd' = EXTm IterMul_SeparateIterDiv smd.
  Proof.
    intros r Hin env smd smd' v Hwf H.
    unfold mulDivAllStageRules in Hin; destruct Hin as [<- | [<- | []]]; repeat dlift H.
    - destruct (iterStep_keep _ (MulOutput (dataLen W)) _ _ (@mulFinishStage W) (fun o => evalExpr (#o`"res")) _ _ _ _ H) as [Eb Ee].
      mdcbn; unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
      destruct Hwf as [Hq [Hbm Hbd]].
      split; [split; [exact Hq | split; [rewrite Eb; exact Hbm | exact Hbd]] | rewrite Ee; reflexivity].
    - destruct (iterStep_keep _ (DivOutput (dataLen W)) _ _ (@divFinishStage W) (fun o => evalExpr (#o`"res")) _ _ _ _ H) as [Eb Ee].
      mdcbn; unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
      destruct Hwf as [Hq [Hbm Hbd]].
      split; [split; [exact Hq | split; [exact Hbm | rewrite Eb; exact Hbd]] | rewrite Ee; reflexivity].
  Qed.

  Lemma sh_stage :
    forall r, In r (mulDivAllStageRules mulCapacity divCapacity W mulStages divStages IterMul_SharedIterDiv type) ->
    forall env (smd smd' : TS (MDTm IterMul_SharedIterDiv)) v,
      WFm IterMul_SharedIterDiv smd -> SemAction env r smd smd' v ->
      WFm IterMul_SharedIterDiv smd' /\ EXTm IterMul_SharedIterDiv smd' = EXTm IterMul_SharedIterDiv smd.
  Proof.
    intros r Hin env smd smd' v Hwf H.
    unfold mulDivAllStageRules in Hin; destruct Hin as [<- | []]; repeat dlift H.
    destruct (iterStep_keep _ (SharedOutput (dataLen W)) _ _ (@sharedFinishStage W) (fun o => evalExpr (#o`"res")) _ _ _ _ H) as [Eb Ee].
    mdcbn; unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hq Hb].
    split; [split; [exact Hq | rewrite Eb; exact Hb] | rewrite Ee; reflexivity].
  Qed.
  (* What a write-back pop does: it removes the flush entry it returns *)
  Definition PopOK m (smd smd' : TS (MDTm m)) (r : type (Option (MulDivWbResp W))) : Prop :=
    if r.(Snd).(Fst)
    then exists l1 l2, EXTm m smd = (l1 ++ (r.(Fst).(Fst), mkMulDivCap r.(Fst).(Snd).(Fst)) :: l2)%list /\
                       EXTm m smd' = (l1 ++ l2)%list /\ WFm m smd'
    else smd' = smd.

  Lemma pm_popMul :
    forall env (smd smd' : TS (MDTm PipelinedMul_IterDiv)) r,
      WFm PipelinedMul_IterDiv smd ->
      SemAction env (mulDivPopMulResp mulCapacity divCapacity W mulStages divStages PipelinedMul_IterDiv type) smd smd' r ->
      PopOK PipelinedMul_IterDiv smd smd' r.
  Proof.
    intros env smd smd' r Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    peel H H1; repeat dlift H1.
    match type of H1 with SemAction _ _ _ _ ?o => rename o into optOut end.
    destruct (pipeFirst_char _ _ _ _ _ _ _ _ H1) as [-> Hout]; rewrite ?writeSubTreeState_readSubTreeState in H; clear H1.
    rdstep H.
    destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H.
    destruct Hc as [Em Er]; subst.
    match type of Hb with SemAction _ (if ?c then _ else _) _ _ _ => destruct c eqn:Ec end.
    2:{ apply retSemV in Hb; destruct Hb as [-> ->]; exact eq_refl. }
    apply evalExpr_And2 in Ec; destruct Ec as [Eo Ed].
    rewrite SemAction_iff_evalActionPropGen in Hb.
    do 2 apply letE in Hb.
    peel Hb Hp; repeat dlift Hp.
    peel Hb Hq; repeat dlift Hq.
    apply letE in Hb; destruct Hb as [<- <-].
    apply deqSem in Hq; subst.
    match type of Hp with SemAction _ _ _ ?x _ => rename x into p' end.
    change (optOut.(Snd).(Fst) = true) in Eo.
    destruct (Hout Eo) as [x [Hx Hox]]; clear Hout.
    unfold mulPipeDeq in Hp; pose proof (pipeDeq_char _ _ _ _ _ _ _ Hx Hp) as Ep'; clear Hp.
    mdcbn.
    unfold PopOK.
    match goal with |- (if ?c then _ else _) => let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc end.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hq0 [Hlen Hb]].
    change MulDivFifoCapacity with 1%nat in *.
    change ((@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))).(Snd).(Fst) = true) in Ed.
    rewrite (fifoFirstVal_valid _ _ _ (fifo1_wf _ _)) in Ed.
    pose proof (fifo_to_list_deq _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst smd))))))) as Edq.
    pose proof (length_fifo_to_list_le _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst smd))))))) as Hle.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))) as [| d0 ds] eqn:El; [discriminate Ed |].
    destruct ds as [| ? ?]; [| cbn [length] in Hle; lia].
    pose proof (fifoFirstVal_data _ _ _ d0 [] El) as Ed0.
    rewrite states_last, Hx in Hlen; cbn [map app length] in Hlen; apply eq_add_S in Hlen.
    apply length_zero_iff_nil in Hlen; rename Hlen into Hup.
    remember (@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))) as fv eqn:Efv.
    destruct fv as [fq [fb []]]; cbn [Fst] in Ed0; subst fq.
    destruct optOut as [od [ov []]]; cbn [Fst] in Hox; subst od.
    exists [], (map evalMulReqCap (fifo_to_list (Fst (Fst smd))) ++
           extractIterEngineEntries divStages
             (fun ty' st' => @divStageStep W ty' (W / divStages)%nat st')
             (@divFinishStage W) (fun o => evalExpr (#o`"res"))
             (Fst (Fst (Snd (Fst (Snd smd))))) (Fst (Snd (Fst (Snd (Fst (Snd smd)))))) ++
           map evalDivReqCap (fifo_to_list (Fst (Fst (Snd smd)))))%list.
    unfold extractPipeEngineEntries; change MulDivFifoCapacity with 1%nat.
    rewrite Ep', Hup, Edq, El, states_last, Hx, Hup; cbn [combine map app tl length].
    split; [reflexivity | split; [reflexivity |]].
    split; [exact Hq0 | split; [reflexivity | exact Hb]].
  Qed.
  Lemma pm_popDiv :
    forall env (smd smd' : TS (MDTm PipelinedMul_IterDiv)) r,
      WFm PipelinedMul_IterDiv smd ->
      SemAction env (mulDivPopDivResp mulCapacity divCapacity W mulStages divStages PipelinedMul_IterDiv type) smd smd' r ->
      PopOK PipelinedMul_IterDiv smd smd' r.
  Proof.
    intros env smd smd' r Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    peel H H1; repeat dlift H1.
    match type of H1 with SemAction _ _ _ _ ?o => rename o into optOut end.
    destruct (iterFirst_char _ _ _ _ _ _ _ _ H1) as [-> [Hov Hod]]; rewrite ?writeSubTreeState_readSubTreeState in H; clear H1.
    rdstep H.
    destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H.
    destruct Hc as [Em Er]; subst.
    match type of Hb with SemAction _ (if ?c then _ else _) _ _ _ => destruct c eqn:Ec end.
    2:{ apply retSemV in Hb; destruct Hb as [-> ->]; exact eq_refl. }
    apply evalExpr_And2 in Ec; destruct Ec as [Eo Ed].
    rewrite SemAction_iff_evalActionPropGen in Hb.
    do 2 apply letE in Hb.
    peel Hb Hp; repeat dlift Hp.
    peel Hb Hq; repeat dlift Hq.
    apply letE in Hb; destruct Hb as [<- <-].
    apply deqSem in Hq; subst.
    change (optOut.(Snd).(Fst) = true) in Eo.
    specialize (Hod Eo); rewrite Hov in Eo.
    apply iterDeq_char in Hp; rewrite Eo in Hp; subst.
    mdcbn.
    unfold PopOK.
    match goal with |- (if ?c then _ else _) => let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc end.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hq0 [Hlen Hb]].
    apply andb_true_iff in Eo; destruct Eo as [Ebusy Erem]; apply Zmod.eqb_eq in Erem.
    change MulDivFifoCapacity with 1%nat in *.
    change ((@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))).(Snd).(Fst) = true) in Ed.
    rewrite (fifoFirstVal_valid _ _ _ (fifo1_wf _ _)) in Ed.
    pose proof (fifo_to_list_deq _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd)))))))) as Edq.
    pose proof (length_fifo_to_list_le _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd)))))))) as Hle.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))) as [| d0 ds] eqn:El; [discriminate Ed |].
    destruct ds as [| ? ?]; [| cbn [length] in Hle; lia].
    pose proof (fifoFirstVal_data _ _ _ d0 [] El) as Ed0.
    remember (@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))) as fv eqn:Efv.
    destruct fv as [fq [fb []]]; cbn [Fst] in Ed0; subst fq.
    destruct optOut as [od [ov []]]; cbn [Fst] in Hod; subst od.
    rewrite (extractIter_done _ (DivOutput (dataLen W)) _ _ _ _ _ _ d0 Ebusy Erem El).
    rewrite (extractIter_idle _ (DivOutput (dataLen W)) _ _ _ _ (mkWork _ _ false _ _) _ eq_refl).
    exists (extractPipeEngineEntries mulStages (Fst (Fst (Snd (Fst smd)))) (Fst (Snd (Fst (Snd (Fst smd))))) ++ map evalMulReqCap (fifo_to_list (Fst (Fst smd))))%list, (map evalDivReqCap (fifo_to_list (Fst (Fst (Snd smd)))))%list.
    split; [rewrite <- ?app_assoc; reflexivity | split; [rewrite <- ?app_assoc; reflexivity |]].
    split; [exact Hq0 | split; [exact Hlen |]].
    unfold IterBusyRel, mkWork; cbn [Fst]; rewrite Edq; cbn [tl].
    split; [discriminate | intros Hn; exfalso; exact (Hn eq_refl)].
  Qed.

  Lemma sep_popMul :
    forall env (smd smd' : TS (MDTm IterMul_SeparateIterDiv)) r,
      WFm IterMul_SeparateIterDiv smd ->
      SemAction env (mulDivPopMulResp mulCapacity divCapacity W mulStages divStages IterMul_SeparateIterDiv type) smd smd' r ->
      PopOK IterMul_SeparateIterDiv smd smd' r.
  Proof.
    intros env smd smd' r Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    peel H H1; repeat dlift H1.
    match type of H1 with SemAction _ _ _ _ ?o => rename o into optOut end.
    destruct (iterFirst_char _ _ _ _ _ _ _ _ H1) as [-> [Hov Hod]]; rewrite ?writeSubTreeState_readSubTreeState in H; clear H1.
    rdstep H.
    destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H.
    destruct Hc as [Em Er]; subst.
    match type of Hb with SemAction _ (if ?c then _ else _) _ _ _ => destruct c eqn:Ec end.
    2:{ apply retSemV in Hb; destruct Hb as [-> ->]; exact eq_refl. }
    apply evalExpr_And2 in Ec; destruct Ec as [Eo Ed].
    rewrite SemAction_iff_evalActionPropGen in Hb.
    do 2 apply letE in Hb.
    peel Hb Hp; repeat dlift Hp.
    peel Hb Hq; repeat dlift Hq.
    apply letE in Hb; destruct Hb as [<- <-].
    apply deqSem in Hq; subst.
    change (optOut.(Snd).(Fst) = true) in Eo.
    specialize (Hod Eo); rewrite Hov in Eo.
    apply iterDeq_char in Hp; rewrite Eo in Hp; subst.
    mdcbn.
    unfold PopOK.
    match goal with |- (if ?c then _ else _) => let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc end.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hq0 [Hbm Hbd]].
    apply andb_true_iff in Eo; destruct Eo as [Ebusy Erem]; apply Zmod.eqb_eq in Erem.
    change MulDivFifoCapacity with 1%nat in *.
    change ((@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))).(Snd).(Fst) = true) in Ed.
    rewrite (fifoFirstVal_valid _ _ _ (fifo1_wf _ _)) in Ed.
    pose proof (fifo_to_list_deq _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst smd))))))) as Edq.
    pose proof (length_fifo_to_list_le _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst smd))))))) as Hle.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))) as [| d0 ds] eqn:El; [discriminate Ed |].
    destruct ds as [| ? ?]; [| cbn [length] in Hle; lia].
    pose proof (fifoFirstVal_data _ _ _ d0 [] El) as Ed0.
    remember (@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst smd)))))) as fv eqn:Efv.
    destruct fv as [fq [fb []]]; cbn [Fst] in Ed0; subst fq.
    destruct optOut as [od [ov []]]; cbn [Fst] in Hod; subst od.
    rewrite (extractIter_done _ (MulOutput (dataLen W)) _ _ _ _ _ _ d0 Ebusy Erem El).
    rewrite (extractIter_idle _ (MulOutput (dataLen W)) _ _ _ _ (mkWork _ _ false _ _) _ eq_refl).
    exists ([])%list, (map evalMulReqCap (fifo_to_list (Fst (Fst smd))) ++ extractIterEngineEntries divStages (fun ty' st' => @divStageStep W ty' (W / divStages)%nat st') (@divFinishStage W) (fun o => evalExpr (#o`"res")) (Fst (Fst (Snd (Fst (Snd smd))))) (Fst (Snd (Fst (Snd (Fst (Snd smd)))))) ++ map evalDivReqCap (fifo_to_list (Fst (Fst (Snd smd)))))%list.
    split; [rewrite <- ?app_assoc; reflexivity | split; [rewrite <- ?app_assoc; reflexivity |]].
    split; [exact Hq0 | split; [| exact Hbd]].
    unfold IterBusyRel, mkWork; cbn [Fst]; rewrite Edq; cbn [tl].
    split; [discriminate | intros Hn; exfalso; exact (Hn eq_refl)].
  Qed.

  Lemma sep_popDiv :
    forall env (smd smd' : TS (MDTm IterMul_SeparateIterDiv)) r,
      WFm IterMul_SeparateIterDiv smd ->
      SemAction env (mulDivPopDivResp mulCapacity divCapacity W mulStages divStages IterMul_SeparateIterDiv type) smd smd' r ->
      PopOK IterMul_SeparateIterDiv smd smd' r.
  Proof.
    intros env smd smd' r Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    peel H H1; repeat dlift H1.
    match type of H1 with SemAction _ _ _ _ ?o => rename o into optOut end.
    destruct (iterFirst_char _ _ _ _ _ _ _ _ H1) as [-> [Hov Hod]]; rewrite ?writeSubTreeState_readSubTreeState in H; clear H1.
    rdstep H.
    destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H.
    destruct Hc as [Em Er]; subst.
    match type of Hb with SemAction _ (if ?c then _ else _) _ _ _ => destruct c eqn:Ec end.
    2:{ apply retSemV in Hb; destruct Hb as [-> ->]; exact eq_refl. }
    apply evalExpr_And2 in Ec; destruct Ec as [Eo Ed].
    rewrite SemAction_iff_evalActionPropGen in Hb.
    do 2 apply letE in Hb.
    peel Hb Hp; repeat dlift Hp.
    peel Hb Hq; repeat dlift Hq.
    apply letE in Hb; destruct Hb as [<- <-].
    apply deqSem in Hq; subst.
    change (optOut.(Snd).(Fst) = true) in Eo.
    specialize (Hod Eo); rewrite Hov in Eo.
    apply iterDeq_char in Hp; rewrite Eo in Hp; subst.
    mdcbn.
    unfold PopOK.
    match goal with |- (if ?c then _ else _) => let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc end.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hq0 [Hbm Hbd]].
    apply andb_true_iff in Eo; destruct Eo as [Ebusy Erem]; apply Zmod.eqb_eq in Erem.
    change MulDivFifoCapacity with 1%nat in *.
    change ((@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))).(Snd).(Fst) = true) in Ed.
    rewrite (fifoFirstVal_valid _ _ _ (fifo1_wf _ _)) in Ed.
    pose proof (fifo_to_list_deq _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd)))))))) as Edq.
    pose proof (length_fifo_to_list_le _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd)))))))) as Hle.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))) as [| d0 ds] eqn:El; [discriminate Ed |].
    destruct ds as [| ? ?]; [| cbn [length] in Hle; lia].
    pose proof (fifoFirstVal_data _ _ _ d0 [] El) as Ed0.
    remember (@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd (Fst (Snd smd))))))) as fv eqn:Efv.
    destruct fv as [fq [fb []]]; cbn [Fst] in Ed0; subst fq.
    destruct optOut as [od [ov []]]; cbn [Fst] in Hod; subst od.
    rewrite (extractIter_done _ (DivOutput (dataLen W)) _ _ _ _ _ _ d0 Ebusy Erem El).
    rewrite (extractIter_idle _ (DivOutput (dataLen W)) _ _ _ _ (mkWork _ _ false _ _) _ eq_refl).
    exists (extractIterEngineEntries mulStages (fun ty' st' => @mulStageStep W ty' (W / mulStages)%nat st') (@mulFinishStage W) (fun o => evalExpr (#o`"res")) (Fst (Fst (Snd (Fst smd)))) (Fst (Snd (Fst (Snd (Fst smd))))) ++ map evalMulReqCap (fifo_to_list (Fst (Fst smd))))%list, (map evalDivReqCap (fifo_to_list (Fst (Fst (Snd smd)))))%list.
    split; [rewrite <- ?app_assoc; reflexivity | split; [rewrite <- ?app_assoc; reflexivity |]].
    split; [exact Hq0 | split; [exact Hbm |]].
    unfold IterBusyRel, mkWork; cbn [Fst]; rewrite Edq; cbn [tl].
    split; [discriminate | intros Hn; exfalso; exact (Hn eq_refl)].
  Qed.

  Lemma sh_popMul :
    forall env (smd smd' : TS (MDTm IterMul_SharedIterDiv)) r,
      WFm IterMul_SharedIterDiv smd ->
      SemAction env (mulDivPopMulResp mulCapacity divCapacity W mulStages divStages IterMul_SharedIterDiv type) smd smd' r ->
      PopOK IterMul_SharedIterDiv smd smd' r.
  Proof.
    intros env smd smd' r Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    peel H H1; repeat dlift H1.
    match type of H1 with SemAction _ _ _ _ ?o => rename o into optOut end.
    destruct (iterFirst_char _ _ _ _ _ _ _ _ H1) as [-> [Hov Hod]]; rewrite ?writeSubTreeState_readSubTreeState in H; clear H1.
    rdstep H.
    destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H.
    destruct Hc as [Em Er]; subst.
    match type of Hb with SemAction _ (if ?c then _ else _) _ _ _ => destruct c eqn:Ec end.
    2:{ apply retSemV in Hb; destruct Hb as [-> ->]; exact eq_refl. }
    apply evalExpr_And2 in Ec; destruct Ec as [Eo Ed].
    rewrite SemAction_iff_evalActionPropGen in Hb.
    do 2 apply letE in Hb.
    peel Hb Hp; repeat dlift Hp.
    peel Hb Hq; repeat dlift Hq.
    apply letE in Hb; destruct Hb as [<- <-].
    apply deqSem in Hq; subst.
    change (optOut.(Snd).(Fst) = true) in Eo.
    specialize (Hod Eo); rewrite Hov in Eo.
    apply iterDeq_char in Hp; rewrite Eo in Hp; subst.
    mdcbn.
    unfold PopOK.
    match goal with |- (if ?c then _ else _) => let Hc := fresh in assert (Hc : c = true) by reflexivity; rewrite Hc end.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf, extractMulDivEntries in *; cbn [Fst Snd] in *.
    destruct Hwf as [Hq0 Hb].
    apply andb_true_iff in Eo; destruct Eo as [Ebusy Erem]; apply Zmod.eqb_eq in Erem.
    change MulDivFifoCapacity with 1%nat in *.
    change ((@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd smd))))).(Snd).(Fst) = true) in Ed.
    rewrite (fifoFirstVal_valid _ _ _ (fifo1_wf _ _)) in Ed.
    pose proof (fifo_to_list_deq _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd smd)))))) as Edq.
    pose proof (length_fifo_to_list_le _ _ _ (fifo1_wf RegIdx (Fst (Snd (Fst (Snd smd)))))) as Hle.
    destruct (@fifo_to_list 1 RegIdx (Fst (Snd (Fst (Snd smd))))) as [| d0 ds] eqn:El; [discriminate Ed |].
    destruct ds as [| ? ?]; [| cbn [length] in Hle; lia].
    pose proof (fifoFirstVal_data _ _ _ d0 [] El) as Ed0.
    remember (@fifoFirstVal 1 RegIdx (Fst (Snd (Fst (Snd smd))))) as fv eqn:Efv.
    destruct fv as [fq [fb []]]; cbn [Fst] in Ed0; subst fq.
    destruct optOut as [od [ov []]]; cbn [Fst] in Hod; subst od.
    rewrite (extractIter_done _ (SharedOutput (dataLen W)) _ _ _ _ _ _ d0 Ebusy Erem El).
    rewrite (extractIter_idle _ (SharedOutput (dataLen W)) _ _ _ _ (mkWork _ _ false _ _) _ eq_refl).
    exists ([])%list, (map evalMulDivReqCap (fifo_to_list (Fst smd)))%list.
    split; [rewrite <- ?app_assoc; reflexivity | split; [rewrite <- ?app_assoc; reflexivity |]].
    split; [exact Hq0 |].
    unfold IterBusyRel, mkWork; cbn [Fst]; rewrite Edq; cbn [tl].
    split; [discriminate | intros Hn; exfalso; exact (Hn eq_refl)].
  Qed.

  Lemma sh_popDiv :
    forall env (smd smd' : TS (MDTm IterMul_SharedIterDiv)) r,
      SemAction env (mulDivPopDivResp mulCapacity divCapacity W mulStages divStages IterMul_SharedIterDiv type) smd smd' r ->
      PopOK IterMul_SharedIterDiv smd smd' r.
  Proof. intros env smd smd' r H; apply retSemV in H; destruct H as [-> ->]; exact eq_refl. Qed.
  (* --- All modes --- *)

  Lemma md_rule_ok :
    forall m r,
      In r (mulDivIssueRules mulCapacity divCapacity W mulStages divStages m type ++
            mulDivAllStageRules mulCapacity divCapacity W mulStages divStages m type)%list ->
      forall env (smd smd' : TS (MDTm m)) v,
        WFm m smd -> SemAction env r smd smd' v -> WFm m smd' /\ EXTm m smd' = EXTm m smd.
  Proof.
    intros m r Hin env smd smd' v Hwf H.
    apply in_app_or in Hin as [Hin | Hin].
    - apply (In_nth _ _ r) in Hin as [i [Hi Hn]]; rewrite <- Hn in H; clear Hn.
      destruct m; cbn [length mulDivIssueRules] in Hi.
      + destruct i as [| [| i]]; [exact (pm_issueMul _ _ _ _ _ Hwf H) | exact (pm_issueDiv _ _ _ _ _ Hwf H) | lia].
      + destruct i as [| [| i]]; [exact (sep_issueMul _ _ _ _ _ Hwf H) | exact (sep_issueDiv _ _ _ _ _ Hwf H) | lia].
      + destruct i as [| i]; [exact (sh_issue _ _ _ _ _ Hwf H) | lia].
    - destruct m; [exact (pm_stage r Hin env smd smd' v Hwf H) | exact (sep_stage r Hin env smd smd' v Hwf H) |
                   exact (sh_stage r Hin env smd smd' v Hwf H)].
  Qed.

  Lemma popMul_ok :
    forall m env (smd smd' : TS (MDTm m)) r,
      WFm m smd -> SemAction env (mulDivPopMulResp mulCapacity divCapacity W mulStages divStages m type) smd smd' r ->
      PopOK m smd smd' r.
  Proof.
    intros m; destruct m; intros env smd smd' r Hwf H;
      [exact (pm_popMul _ _ _ _ Hwf H) | exact (sep_popMul _ _ _ _ Hwf H) | exact (sh_popMul _ _ _ _ Hwf H)].
  Qed.

  Lemma popDiv_ok :
    forall m env (smd smd' : TS (MDTm m)) r,
      WFm m smd -> SemAction env (mulDivPopDivResp mulCapacity divCapacity W mulStages divStages m type) smd smd' r ->
      PopOK m smd smd' r.
  Proof.
    intros m; destruct m; intros env smd smd' r Hwf H;
      [exact (pm_popDiv _ _ _ _ Hwf H) | exact (sep_popDiv _ _ _ _ Hwf H) | exact (sh_popDiv _ _ _ _ H)].
  Qed.
End MdRules.

(* --- The write-back rules on the core --- *)

Section MdWbCore.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable pcAddrInit : Z.
  Variable bpT memT fetchT decodeT executeT dataMemT : Tree Elem.

  Local Abbreviation rTree := (rfTree pcAddrInit).
  Local Abbreviation mdTree := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree rTree bpT memT fetchT decodeT executeT dataMemT mdTree).

  Lemma wb_step :
    forall env (popResp : Action type mdTree (Option (MulDivWbResp (Z.to_nat Xlen)))) (c c' : TS cTree) v,
      SemAction env (@ImplMulDiv.mulDivWriteBack mulCapacity divCapacity mulStages divStages mulDivMode pcAddrInit
                       bpT memT fetchT decodeT executeT dataMemT type popResp) c c' v ->
      exists env' smd' (res : type (Option (MulDivWbResp (Z.to_nat Xlen)))),
        SemAction env' popResp (core_mulDiv rTree bpT memT fetchT decodeT executeT dataMemT mdTree c) smd' res /\
        c' = if res.(Snd).(Fst)
             then evalCommitMulDivWb mulCapacity divCapacity mulStages divStages mulDivMode pcAddrInit
                    bpT memT fetchT decodeT executeT dataMemT res.(Fst).(Fst) (mkMulDivCap res.(Fst).(Snd).(Fst))
                    (core_withMulDiv rTree bpT memT fetchT decodeT executeT dataMemT mdTree c smd')
             else core_withMulDiv rTree bpT memT fetchT decodeT executeT dataMemT mdTree c smd'.
  Proof.
    intros env popResp c c' v H.
    rewrite SemAction_iff_evalActionPropGen in H; unfold ImplMulDiv.mulDivWriteBack in H.
    peel H H1; apply liftSem in H1; destruct H1 as [smd' [Hp ->]].
    match type of Hp with SemAction ?e _ _ _ ?r => exists e, smd', r end; split; [exact Hp |].
    match type of Hp with SemAction _ _ _ _ ?r => rename r into res end.
    destruct (ifA _ _ _ _ _ _ _ H) as [m [rr [Hb Hc]]]; clear H.
    destruct Hc as [<- _].
    match type of Hb with SemAction _ (if ?cnd then _ else _) _ _ _ => destruct cnd eqn:Ev end.
    - change (res.(Snd).(Fst) = true) in Ev; rewrite Ev.
      rewrite SemAction_iff_evalActionPropGen in Hb.
      do 4 apply letE in Hb.
      rewrite evalActionPropGen_commitMulDivWb in Hb; destruct Hb as [<- _].
      reflexivity.
    - change (res.(Snd).(Fst) = false) in Ev; rewrite Ev.
      apply retSem in Hb; subst; reflexivity.
  Qed.
End MdWbCore.
