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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel DecodeFacts SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead RefSpecFetch RefReplay.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7 AUXILIARY LEMMAS: DECODER/ALU, WAIT-BITS, LISTS, AND EXECUTE
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Decoder, RegRead, and WrappedAlu Field Identities --- *)

Lemma wrappedAlu_dstIdx :
  forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
    aluDstIdx (evalAluOut pcc pkg) =
      if aluInWritesCd pkg then instCd (aluInInst pkg) else Zmod.zero.
Proof.
  intros pcc pkg.
  cbn.
  destruct (aluInWritesCd pkg); reflexivity.
Qed.

Lemma regRead_writesCd :
  forall pcAddrInit (fo : type FetchOut) (rf : RfState pcAddrInit),
    aluInWritesCd (evalRegRead pcAddrInit (evalDecode fo) rf) = decWritesCd fo.
Proof.
  intros pcAddrInit fo rf; reflexivity.
Qed.

Lemma regRead_inst :
  forall pcAddrInit (fo : type FetchOut) (rf : RfState pcAddrInit),
    aluInInst (evalRegRead pcAddrInit (evalDecode fo) rf) = foInst fo.
Proof.
  intros pcAddrInit fo rf; reflexivity.
Qed.

Lemma aluDstIdx_geAluOut :
  forall pcAddrInit (fo : type FetchOut) (pcc : type FullECapWithTag) (rf : RfState pcAddrInit),
    aluDstIdx (evalAluOut pcc (evalRegRead pcAddrInit (evalDecode fo) rf)) = decDst fo.
Proof.
  intros pcAddrInit fo pcc rf.
  rewrite wrappedAlu_dstIdx, regRead_writesCd, regRead_inst.
  unfold decDst; reflexivity.
Qed.

(* --- 2. Epoch Arithmetic --- *)

Lemma zmod_epoch_add1_neq :
  forall (ep : bits EpochSz),
    Zmod.eqb ep (evalExpr (Add [ Var type Epoch ep ; ($1 : Expr type Epoch) ])) = false.
Proof.
  intros ep.
  destruct (Zmod.eqb ep (evalExpr (Add [ Var type Epoch ep ; ($1 : Expr type Epoch) ]))) eqn:E;
    [| reflexivity].
  apply Zmod.eqb_eq in E.
  exfalso.
  pose proof (Zmod.unsigned_range ep) as Hr.
  set (k := Zmod.unsigned ep) in *.
  cbn in Hr.
  assert (k = 0 \/ k = 1) as [H0 | H1] by lia.
  - assert (ep = Zmod.of_Z (2 ^ EpochSz) 0) as -> by (apply Zmod.unsigned_inj; exact H0).
    vm_compute in E; discriminate E.
  - assert (ep = Zmod.of_Z (2 ^ EpochSz) 1) as -> by (apply Zmod.unsigned_inj; exact H1).
    vm_compute in E; discriminate E.
Qed.

(* --- 3. Wait-Bit (`waitBitsTree`) Read-Over-Write Lemmas --- *)

Lemma NoDup_gprWaitPathsWithKind :
  NoDup (map (fun r : RegOfKind Bool => r.(rk_path).(regPath))
             gprWaitPathsWithKind).
Proof.
  apply NoDup_regPath_of_leafPath_id.
  cbn [gprWaitPathsWithKind map rk_path regPath leafPath_id].
  repeat (constructor; [simpl; intuition congruence |]); constructor.
Qed.

(* x1 .. x15: one wait leaf per register but x0; with the start index 1 they fill the 4-bit index space *)
Lemma length_gprWaitPathsWithKind : length gprWaitPathsWithKind = 15%nat.
Proof. reflexivity. Qed.

Lemma waitPaths_fit : (Z.of_nat (1 + length gprWaitPathsWithKind) <= 2 ^ RegIdxSzReal)%Z.
Proof. rewrite length_gprWaitPathsWithKind; apply Z.leb_le; reflexivity. Qed.

(* x0 has no wait bit: it always reads false *)
Lemma evalReadWaitBit_zero :
  forall (wb : TS waitBitsTree), evalReadWaitBit Zmod.zero wb = false.
Proof.
  intros wb; unfold evalReadWaitBit.
  rewrite (evalReadRegsListHelper_above (sz := RegIdxSzReal) gprWaitPathsWithKind 1%nat nil Zmod.zero wb);
    [reflexivity | | exact waitPaths_fit].
  rewrite Zmod.unsigned_0; lia.
Qed.

Lemma evalReadWaitBit_write_same :
  forall (d : bits RegIdxSzReal) (v : bool) (wb : TS waitBitsTree),
    Zmod.eqb d Zmod.zero = false ->
    evalReadWaitBit d (evalWriteWaitBit d v wb) = v.
Proof.
  intros d v wb Hnz; unfold evalReadWaitBit, evalWriteWaitBit.
  apply (@evalReadRegsListHelper_evalWriteRegsListHelper_same waitBitsTree Bool RegIdxSzReal);
    [| exact waitPaths_fit | constructor].
  rewrite length_gprWaitPathsWithKind.
  pose proof (Zmod.unsigned_pos_bound d (ltac:(reflexivity) : (0 < 2 ^ RegIdxSzReal)%Z)) as Hb.
  assert (E16 : (2 ^ RegIdxSzReal = 16)%Z) by reflexivity.
  assert (Hne : Zmod.to_Z d <> 0%Z).
  { intros H0; rewrite <- (Zmod.unsigned_0 (2 ^ RegIdxSzReal)) in H0.
    apply Zmod.unsigned_inj in H0; rewrite H0, Zmod.eqb_refl in Hnz; discriminate Hnz. }
  lia.
Qed.

Lemma evalReadWaitBit_write_other :
  forall (r d : bits RegIdxSzReal) (v : bool) (wb : TS waitBitsTree),
    r <> d ->
    evalReadWaitBit r (evalWriteWaitBit d v wb) = evalReadWaitBit r wb.
Proof.
  intros r d v wb Hneq; unfold evalReadWaitBit, evalWriteWaitBit.
  apply (@evalReadRegsListHelper_evalWriteRegsListHelper_other waitBitsTree Bool RegIdxSzReal);
    [apply NoDup_gprWaitPathsWithKind | exact Hneq].
Qed.

Lemma evalReadWaitBit_setDst_false :
  forall (w : bool) (d r : bits RegIdxSzReal) (wb : TS waitBitsTree),
    evalReadWaitBit r (evalSetDstWaitBits w d false wb) =
      if andb w (Zmod.eqb r d) then false else evalReadWaitBit r wb.
Proof.
  intros [|] d r wb; cbn [evalSetDstWaitBits andb].
  - destruct (Zmod.eqb r d) eqn:Eq.
    + apply Zmod.eqb_eq in Eq; subst r.
      destruct (Zmod.eqb d Zmod.zero) eqn:Ez.
      * apply Zmod.eqb_eq in Ez; subst d; apply evalReadWaitBit_zero.
      * apply evalReadWaitBit_write_same; exact Ez.
    + apply evalReadWaitBit_write_other.
      intros Heq; subst r; rewrite Zmod.eqb_refl in Eq; discriminate Eq.
  - reflexivity.
Qed.

(* --- 4. List & Permutation Helpers for ScoreRel and FrontRel --- *)

Lemma In_swap_mid :
  forall {A : Type} (x : A) (l1 m l2 l3 : list A),
    In x ((l1 ++ m ++ l2) ++ l3) <-> In x ((l1 ++ l2) ++ m ++ l3).
Proof.
  intros A x l1 m l2 l3.
  rewrite !in_app_iff; tauto.
Qed.

Lemma NoDup_app_iff :
  forall {A : Type} (l1 l2 : list A),
    NoDup (l1 ++ l2) <->
    (NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> ~ In x l2).
Proof.
  intros A l1; induction l1 as [| a l1 IH]; intros l2; cbn [app].
  - split.
    + intros H; split; [constructor | split; [exact H | intros x []]].
    + intros [_ [H _]]; exact H.
  - split.
    + intros H; inversion H as [| ? ? Hnin Hnd]; subst.
      apply IH in Hnd as [Hnd1 [Hnd2 Hdisj]].
      split; [constructor; [intros Hin; apply Hnin; apply in_or_app; left; exact Hin | exact Hnd1] |].
      split; [exact Hnd2 |].
      intros x [-> | Hin] Hx2.
      * apply Hnin; apply in_or_app; right; exact Hx2.
      * exact (Hdisj x Hin Hx2).
    + intros [Hnd1 [Hnd2 Hdisj]].
      inversion Hnd1 as [| ? ? Hnin1 Hnd1']; subst.
      constructor.
      * intros Hin; apply in_app_or in Hin as [Hin | Hin];
          [exact (Hnin1 Hin) | exact (Hdisj a (or_introl eq_refl) Hin)].
      * apply IH; split; [exact Hnd1' | split; [exact Hnd2 |]].
        intros x Hin; exact (Hdisj x (or_intror Hin)).
Qed.

Lemma NoDup_swap_mid :
  forall {A : Type} (l1 m l2 l3 : list A),
    NoDup ((l1 ++ l2) ++ m ++ l3) ->
    NoDup ((l1 ++ m ++ l2) ++ l3).
Proof.
  intros A l1 m l2 l3 H.
  rewrite !NoDup_app_iff in H |- *.
  destruct H as [[H1 [H2 H12]] [[Hm [H3 Hm3]] H12_m3]].
  split.
  - split; [exact H1 |]; split.
    + split; [exact Hm |]; split; [exact H2 |].
      intros x Hxm Hx2.
      apply (H12_m3 x); [apply in_or_app; right; exact Hx2 | apply in_or_app; left; exact Hxm].
    + intros x Hx1 Hxm2; apply in_app_or in Hxm2 as [Hxm | Hx2].
      * apply (H12_m3 x); [apply in_or_app; left; exact Hx1 | apply in_or_app; left; exact Hxm].
      * exact (H12 x Hx1 Hx2).
  - split; [exact H3 |].
    intros x Hx1m2 Hx3.
    apply in_app_or in Hx1m2 as [Hx1 | Hxm2].
    + apply (H12_m3 x); [apply in_or_app; left; exact Hx1 | apply in_or_app; right; exact Hx3].
    + apply in_app_or in Hxm2 as [Hxm | Hx2].
      * exact (Hm3 x Hxm Hx3).
      * apply (H12_m3 x); [apply in_or_app; right; exact Hx2 | apply in_or_app; right; exact Hx3].
Qed.

Lemma StalePrefix_tail :
  forall {A : Type} (live : A -> bool) (x : A) (xs : list A),
    StalePrefix live (x :: xs) -> StalePrefix live xs.
Proof.
  intros A live x xs [l1 [l2 [Heq [Hf Ht]]]].
  destruct l1 as [| a l1].
  - cbn [app] in Heq; subst l2.
    inversion Ht as [| ? ? _ Ht']; subst.
    exists [], xs; split; [reflexivity | split; [constructor | exact Ht']].
  - cbn [app] in Heq; injection Heq as _ Heq'.
    inversion Hf as [| ? ? _ Hf']; subst.
    exists l1, l2; split; [reflexivity | split; [exact Hf' | exact Ht]].
Qed.

Lemma StalePrefix_all_false :
  forall {A : Type} (live : A -> bool) (xs : list A),
    Forall (fun x => live x = false) xs -> StalePrefix live xs.
Proof.
  intros A live xs Hf.
  exists xs, []; split; [rewrite app_nil_r; reflexivity | split; [exact Hf | constructor]].
Qed.

Lemma StalePrefix_live_head :
  forall {A : Type} (live : A -> bool) (x : A) (xs : list A),
    StalePrefix live (x :: xs) ->
    live x = true ->
    Forall (fun y => live y = true) xs.
Proof.
  intros A live x xs [l1 [l2 [Heq [Hf Ht]]]] Hx.
  destruct l1 as [| a l1].
  - cbn [app] in Heq; subst l2.
    inversion Ht as [| ? ? _ Ht']; subst; exact Ht'.
  - cbn [app] in Heq; injection Heq as <- _.
    inversion Hf as [| ? ? Ha _]; subst.
    rewrite Ha in Hx; discriminate Hx.
Qed.

(* --- 5. State-Free Return Postcondition Engine (`allReturns`) & Execute Output Properties --- *)

Fixpoint allReturns {t : Tree Elem} {k : Kind}
  (a : Action type t k) : (type k -> Prop) -> Prop :=
  match a with
  | ReadReg _ _ cont      => fun Q => forall v, allReturns (cont v) Q
  | WriteReg _ _ cont     => fun Q => allReturns cont Q
  | ReadRqMem _ _ _ cont  => fun Q => allReturns cont Q
  | ReadRpMem _ _ _ cont  => fun Q => forall v, allReturns (cont v) Q
  | WriteMem _ _ _ cont   => fun Q => allReturns cont Q
  | Send _ _ cont         => fun Q => allReturns cont Q
  | Recv _ _ cont         => fun Q => forall v, allReturns (cont v) Q
  | LetExp _ e cont      => fun Q => allReturns (cont (evalExpr e)) Q
  | LetAction _ a1 cont  => fun Q => allReturns a1 (fun v => allReturns (cont v) Q)
  | NonDet _ _ cont      => fun Q => forall v, allReturns (cont v) Q
  | IfElse _ p tb fb c   => fun Q =>
      if evalExpr p then allReturns tb (fun v => allReturns (c v) Q)
                    else allReturns fb (fun v => allReturns (c v) Q)
  | System _ cont         => fun Q => allReturns cont Q
  | Return e              => fun Q => Q (evalExpr e)
  end.

Lemma allReturns_evalActionPropGen :
  forall {t : Tree Elem} {k : Kind} {env : Env t}
         (a : Action type t k) (s : TS t)
         (Q : type k -> Prop) (P : TS t -> type k -> Prop),
    allReturns a Q ->
    evalActionPropGen env a s P ->
    exists s' r', P s' r' /\ Q r'.
Proof.
  intros t k env a.
  induction a; intros s0 Q P Har Hev; cbn [allReturns evalActionPropGen] in *.
  - eapply H; [apply Har | exact Hev].
  - eapply IHa; [exact Har | exact Hev].
  - eapply IHa; [exact Har | exact Hev].
  - eapply H; [apply Har | exact Hev].
  - eapply IHa; [exact Har | exact Hev].
  - eapply IHa; [exact Har | exact Hev].
  - destruct Hev as [v [Hv Hev]]; eapply H; [apply Har | exact Hev].
  - eapply H; [exact Har | exact Hev].
  - destruct (IHa s0 _ _ Har Hev) as [mid [v [Hcont HQv]]].
    exact (H v mid Q P HQv Hcont).
  - destruct Hev as [v Hev]; exact (H v s0 Q P (Har v) Hev).
  - destruct (evalExpr p).
    + destruct (IHa1 s0 _ _ Har Hev) as [mid [v [Hcont HQv]]].
      exact (H v mid Q P HQv Hcont).
    + destruct (IHa2 s0 _ _ Har Hev) as [mid [v [Hcont HQv]]].
      exact (H v mid Q P HQv Hcont).
  - eapply IHa; [exact Har | exact Hev].
  - exists s0, (evalExpr e); split; [exact Hev | exact Har].
Qed.

Lemma allReturns_SemAction :
  forall {t : Tree Elem} {k : Kind} {env : Env t}
         (a : Action type t k) (s s' : TS t) (out : type k)
         (Q : type k -> Prop),
    allReturns a Q ->
    SemAction env a s s' out ->
    Q out.
Proof.
  intros t k env a s s' out Q Har Hsem.
  rewrite SemAction_iff_evalActionPropGen in Hsem.
  destruct (allReturns_evalActionPropGen a s Q _ Har Hsem) as [? [? [[_ <-] HQ]]].
  exact HQ.
Qed.

Lemma allReturns_any :
  forall {t : Tree Elem} {k : Kind} (a : Action type t k) (Q : type k -> Prop),
    (forall r, Q r) -> allReturns a Q.
Proof.
  intros t k a.
  induction a; intros Q HQ; cbn [allReturns];
    try (intro v; apply H; exact HQ);
    try (apply (H (evalExpr e)); exact HQ);
    try (apply IHa; exact HQ);
    try (apply IHa; intro v; apply H; exact HQ);
    try (destruct (evalExpr p); [apply IHa1 | apply IHa2]; intro v; apply H; exact HQ);
    exact (HQ _).
Qed.

Lemma allReturns_step_let :
  forall {t : Tree Elem} {k1 k2 : Kind}
         (nm : string) (a : Action type t k1) (cont : type k1 -> Action type t k2)
         (Q : type k2 -> Prop),
    (forall v, allReturns (cont v) Q) ->
    allReturns (LetAction nm a cont) Q.
Proof.
  intros t k1 k2 nm a cont Q H.
  cbn [allReturns]; apply allReturns_any; exact H.
Qed.

Lemma allReturns_step_letexp :
  forall {t : Tree Elem} {k1 k2 : Kind}
         (nm : string) (e : Expr type k1) (cont : type k1 -> Action type t k2)
         (Q : type k2 -> Prop),
    allReturns (cont (evalExpr e)) Q ->
    allReturns (LetExp nm e cont) Q.
Proof.
  intros t k1 k2 nm e cont Q H; exact H.
Qed.

Lemma allReturns_IfElse_Ret :
  forall {t : Tree Elem} {k : Kind}
         (nm : string) (p : Expr type Bool)
         (tb fb : Action type t k)
         (Q : type k -> Prop),
    allReturns tb Q ->
    allReturns fb Q ->
    allReturns (IfElse nm p tb fb (fun v => Return #v)) Q.
Proof.
  intros t k nm p tb fb Q Ht Hf.
  cbn [allReturns]; destruct (evalExpr p); [exact Ht | exact Hf].
Qed.

Lemma allReturns_IfElse_any :
  forall {t : Tree Elem} {k1 k2 : Kind}
         (nm : string) (p : Expr type Bool)
         (tb fb : Action type t k1) (cont : type k1 -> Action type t k2)
         (Q : type k2 -> Prop),
    (forall v, allReturns (cont v) Q) ->
    allReturns (IfElse nm p tb fb cont) Q.
Proof.
  intros t k1 k2 nm p tb fb cont Q H.
  cbn [allReturns]; destruct (evalExpr p); apply allReturns_any; exact H.
Qed.

Lemma allReturns_handleTrap :
  forall pcAddrInit (pcc : type FullECapWithTag) (mc mt : type (Bit Xlen))
         (Q : type ExecuteOut -> Prop),
    (forall r, optValid (execMulDiv r) = false /\ optValid (execDataMem r) = false -> Q r) ->
    allReturns (@handleTrap pcAddrInit type pcc mc mt) Q.
Proof.
  intros pcAddrInit pcc mc mt Q HQ.
  unfold handleTrap;
    repeat (lazymatch goal with
            | |- allReturns (LetAction _ _ _) _ => simple apply allReturns_step_let; intro
            | |- allReturns (LetExp _ _ _) _ => simple apply allReturns_step_letexp
            | |- allReturns (IfElse _ _ _ _ (fun v => Return (Var _ _ v))) _ => simple apply allReturns_IfElse_Ret
            | |- allReturns (IfElse _ _ _ _ _) _ => simple apply allReturns_IfElse_any; intro
            | |- allReturns (Return _) _ => cbn [allReturns]
            end);
    apply HQ; split; reflexivity.
Qed.

Lemma handleTrap_fields :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)}
         (pcc : type FullECapWithTag) (mc mt : type (Bit Xlen))
         (rf rf' : RfState pcAddrInit) (out : type ExecuteOut),
    SemAction env (@handleTrap pcAddrInit type pcc mc mt) rf rf' out ->
    optValid (execMulDiv out) = false /\ optValid (execDataMem out) = false.
Proof.
  intros pcAddrInit env pcc mc mt rf rf' out Hsem.
  refine (allReturns_SemAction _ rf rf' out
            (fun r => optValid (execMulDiv r) = false /\ optValid (execDataMem r) = false) _ Hsem).
  apply allReturns_handleTrap; intros ? H; exact H.
Qed.

Ltac step_allReturns :=
  lazymatch goal with
  | |- allReturns (LetAction _ _ _) _ =>
      simple apply allReturns_step_let; intro
  | |- allReturns (LetExp _ _ _) _ =>
      simple apply allReturns_step_letexp
  | |- allReturns (@handleTrap _ _ _ _ _) _ =>
      simple apply allReturns_handleTrap; intros ? [? ?]
  | |- allReturns (IfElse _ _ _ _ (fun v => Return (Var _ _ v))) _ =>
      simple apply allReturns_IfElse_Ret
  | |- allReturns (IfElse _ _ _ _ _) _ =>
      simple apply allReturns_IfElse_any; intro
  | |- allReturns (Return _) _ =>
      cbn [allReturns]
  end.

Lemma executeInterrupt_fields :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)}
         (pcc : type FullECapWithTag) (meip mtip : bool)
         (rf rf' : RfState pcAddrInit) (out : type ExecuteOut),
    SemAction env (@executeInterrupt pcAddrInit type pcc meip mtip) rf rf' out ->
    optValid (execMulDiv out) = false /\ optValid (execDataMem out) = false.
Proof.
  intros pcAddrInit env pcc meip mtip rf rf' out Hsem.
  refine (allReturns_SemAction _ rf rf' out
            (fun r => optValid (execMulDiv r) = false /\ optValid (execDataMem r) = false) _ Hsem).
  unfold executeInterrupt; repeat step_allReturns; split; assumption.
Qed.

Lemma executeNonSequential_mulDiv_none :
  forall pcAddrInit {env : Env (rfTree pcAddrInit)}
         (pcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
         (rf rf' : RfState pcAddrInit) (out : type ExecuteOut),
    SemAction env (@executeNonSequential pcAddrInit type pcc meip mtip aluOut) rf rf' out ->
    optValid (execMulDiv out) = false.
Proof.
  intros pcAddrInit env pcc meip mtip aluOut rf rf' out Hsem.
  refine (allReturns_SemAction _ rf rf' out
            (fun r => optValid (execMulDiv r) = false) _ Hsem).
  unfold executeNonSequential; repeat step_allReturns; first [assumption | reflexivity].
Qed.
