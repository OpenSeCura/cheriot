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
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker RefSpecRead RefSpecFetch RefReplay.
From Cheriot.Proof Require Import RefExecAux RefExecFrame RefExecStep.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 7 LIVE EXECUTION TRANSITIONS (`RefExecLive.v`)
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Tag Exhaustion & Determinism on Pure Register Trees --- *)

Lemma dmState_tags_exhaust :
  forall st : type DataMemState,
    dmValid st = true ->
    dmLoadRq st = false ->
    dmLoadRp st = false ->
    dmRevRq st = false ->
    dmCheck st = false ->
    dmRevRp st = true.
Proof.
  intros st Hv H0 H1 H2 H4; unfold dmValid in Hv; rewrite H0, H1, H2, H4 in Hv.
  destruct (dmRevRp st); [reflexivity | discriminate Hv].
Qed.

Lemma dmLoadRp_excl :
  forall st : type DataMemState,
    dmLoadRp st = true ->
    dmLoadRq st = false /\ dmRevRq st = false /\ dmRevRp st = false.
Proof.
  intros [d tg]; unfold dmLoadRq, dmLoadRp, dmRevRq, dmRevRp; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma pccWithAddr_self :
  forall p : type FullECapWithTag,
    pccWithAddr p p.(Snd).(Snd).(Fst) = p.
Proof.
  intros [t [ec [a []]]]; reflexivity.
Qed.

Lemma preExcAt_pccWithAddr :
  forall (p : type FullECapWithTag) (a pc : type Addr),
    preExcAt (pccWithAddr p a) pc = preExcAt p pc.
Proof.
  intros [t [ec [a0 []]]] a pc; reflexivity.
Qed.

Lemma readPcc_flushMulDivCaps :
  forall pcAddrInit entries rf,
    readPcc pcAddrInit (flushMulDivCaps pcAddrInit entries rf) = readPcc pcAddrInit rf.
Proof.
  intros pcAddrInit entries; induction entries as [| [d v] rest IH]; intros rf; cbn [flushMulDivCaps].
  - reflexivity.
  - rewrite IH; exact (readPcc_writeGprVal pcAddrInit d v rf).
Qed.

Lemma writePcc_flushMulDivCaps :
  forall pcAddrInit p entries rf,
    writePcc pcAddrInit p (flushMulDivCaps pcAddrInit entries rf) =
    flushMulDivCaps pcAddrInit entries (writePcc pcAddrInit p rf).
Proof.
  intros pcAddrInit p entries; induction entries as [| [d v] rest IH]; intros rf; cbn [flushMulDivCaps].
  - reflexivity.
  - rewrite IH, writePcc_writeGprVal; reflexivity.
Qed.

Lemma evalIsInterruptPending_flushMulDivCaps :
  forall pcAddrInit meip mtip entries rf,
    evalIsInterruptPending pcAddrInit meip mtip (flushMulDivCaps pcAddrInit entries rf) =
    evalIsInterruptPending pcAddrInit meip mtip rf.
Proof.
  intros pcAddrInit meip mtip entries; induction entries as [| [d v] rest IH]; intros rf; cbn [flushMulDivCaps].
  - reflexivity.
  - rewrite IH; exact (evalIsInterruptPending_writeGprVal pcAddrInit meip mtip d v rf).
Qed.

Fixpoint evalActionFun {t : Tree Elem} {k : Kind} (a : @Action type t k) (s : TS t)
  : option (TS t * type k) :=
  match a with
  | ReadReg _ x cont =>
      evalActionFun (cont (castStateReg x (readTreeState t s x.(regPath)))) s
  | WriteReg x v cont =>
      evalActionFun cont (writeTreeState t s x.(regPath) (castStateRegInv x (evalExpr v)))
  | ReadRqMem x i p cont =>
      let arr := castStateMem x (readTreeState t s x.(memPath)) in
      let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
      evalActionFun cont (writeTreeState t s x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val)))
  | ReadRpMem _ x p cont =>
      evalActionFun (cont (readSameTuple (castStateMem x (readTreeState t s x.(memPath))).(Snd) p)) s
  | WriteMem x i v cont =>
      let arr := castStateMem x (readTreeState t s x.(memPath)) in
      evalActionFun cont (writeTreeState t s x.(memPath)
        (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd))))
  | Send x v cont =>
      let currentTrace := castStateSend x (readTreeState t s x.(sendPath)) in
      evalActionFun cont (writeTreeState t s x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace)))
  | Recv _ _ _ => None
  | LetExp _ e cont =>
      evalActionFun (cont (evalExpr e)) s
  | LetAction _ a1 cont =>
      match evalActionFun a1 s with
      | Some (sm, rm) => evalActionFun (cont rm) sm
      | None => None
      end
  | NonDet _ _ _ => None
  | IfElse _ p tb fb cont =>
      match evalActionFun (if evalExpr p then tb else fb) s with
      | Some (sm, rm) => evalActionFun (cont rm) sm
      | None => None
      end
  | System _ cont => evalActionFun cont s
  | Return e => Some (s, evalExpr e)
  | CallGallina _ _ _ _ _ _ => None
  end.

Lemma evalActionFun_complete :
  forall t (env : Env t) k (a : @Action type t k) (s0 s1 : TS t) (v1 : type k),
    SemAction env a s0 s1 v1 ->
    evalActionFun a s0 <> None ->
    evalActionFun a s0 = Some (s1, v1).
Proof.
  intros t env k a s0 s1 v1 H1; induction H1; intros Hne; cbn [evalActionFun] in Hne |- *.
  - exact (IHSemAction Hne).
  - exact (IHSemAction Hne).
  - exact (IHSemAction Hne).
  - exact (IHSemAction Hne).
  - exact (IHSemAction Hne).
  - exact (IHSemAction Hne).
  - exfalso; apply Hne; reflexivity.
  - exact (IHSemAction Hne).
  - destruct (evalActionFun a old) as [[sm rm] |] eqn:Ea; [| exfalso; apply Hne; reflexivity].
    assert (E1 : Some (sm, rm) = Some (midState, midRet))
      by (apply IHSemAction1; discriminate).
    injection E1 as -> ->; exact (IHSemAction2 Hne).
  - exfalso; apply Hne; reflexivity.
  - destruct (evalExpr p) eqn:Ep.
    + destruct (evalActionFun t_branch old) as [[sm rm] |] eqn:Eb; [| exfalso; apply Hne; reflexivity].
      assert (E1 : Some (sm, rm) = Some (midState, midRet))
        by (apply (H eq_refl); discriminate).
      injection E1 as -> ->; exact (IHSemAction Hne).
    + destruct (evalActionFun f_branch old) as [[sm rm] |] eqn:Eb; [| exfalso; apply Hne; reflexivity].
      assert (E1 : Some (sm, rm) = Some (midState, midRet))
        by (apply (H0 eq_refl); discriminate).
      injection E1 as -> ->; exact (IHSemAction Hne).
  - exact (IHSemAction Hne).
  - subst; reflexivity.
  - exfalso; apply Hne; reflexivity.
Qed.

Lemma SemAction_det_of_some :
  forall t (env : Env t) k (a : @Action type t k) (s0 s1 s2 : TS t) (v1 v2 : type k),
    evalActionFun a s0 <> None ->
    SemAction env a s0 s1 v1 ->
    SemAction env a s0 s2 v2 ->
    s1 = s2 /\ v1 = v2.
Proof.
  intros t env k a s0 s1 s2 v1 v2 Hne H1 H2.
  pose proof (evalActionFun_complete t env k a s0 s1 v1 H1 Hne) as E1.
  pose proof (evalActionFun_complete t env k a s0 s2 v2 H2 Hne) as E2.
  rewrite E1 in E2; injection E2 as -> ->; split; reflexivity.
Qed.

Fixpoint pureAction {t : Tree Elem} {k : Kind} (a : @Action type t k) : Prop :=
  match a with
  | Recv _ _ _ => False
  | NonDet _ _ _ => False
  | ReadReg _ _ cont => forall v, pureAction (cont v)
  | WriteReg _ _ cont => pureAction cont
  | ReadRqMem _ _ _ cont => pureAction cont
  | ReadRpMem _ _ _ cont => forall v, pureAction (cont v)
  | WriteMem _ _ _ cont => pureAction cont
  | Send _ _ cont => pureAction cont
  | LetExp _ _ cont => forall v, pureAction (cont v)
  | LetAction _ a1 cont => pureAction a1 /\ forall v, pureAction (cont v)
  | IfElse _ _ tb fb cont => pureAction tb /\ pureAction fb /\ forall v, pureAction (cont v)
  | System _ cont => pureAction cont
  | Return _ => True
  | CallGallina _ _ _ _ _ _ => False
  end.

Lemma evalActionFun_some_of_pure :
  forall t k (a : @Action type t k),
    pureAction a ->
    forall (s : TS t), evalActionFun a s <> None.
Proof.
  intros t k a; induction a; intros Hp s0; cbn [pureAction evalActionFun] in *.
  - exact (H _ (Hp _) s0).
  - exact (IHa Hp _).
  - exact (IHa Hp _).
  - exact (H _ (Hp _) s0).
  - exact (IHa Hp _).
  - exact (IHa Hp _).
  - contradiction.
  - exact (H _ (Hp _) s0).
  - destruct Hp as [Hp1 Hp2].
    specialize (IHa Hp1 s0).
    destruct (evalActionFun a s0) as [[sm rm] |]; [exact (H rm (Hp2 rm) sm) | exfalso; exact (IHa eq_refl)].
  - contradiction.
  - destruct Hp as [Hp1 [Hp2 Hp3]].
    destruct (evalExpr p).
    + specialize (IHa1 Hp1 s0).
      destruct (evalActionFun a1 s0) as [[sm rm] |]; [exact (H rm (Hp3 rm) sm) | exfalso; exact (IHa1 eq_refl)].
    + specialize (IHa2 Hp2 s0).
      destruct (evalActionFun a2 s0) as [[sm rm] |]; [exact (H rm (Hp3 rm) sm) | exfalso; exact (IHa2 eq_refl)].
  - exact (IHa Hp s0).
  - discriminate.
  - contradiction.
Qed.

Lemma pureAction_readRegsListHelper :
  forall t k (sz : Z) (l : list (@RegOfKind t k)) (i : nat) (acc : list (Expr type k)) (idx : Expr type (Bit sz)),
    pureAction (readRegsListHelper (ty := type) i acc l idx).
Proof.
  intros t k sz l; induction l as [| r l IH]; intros i acc idx; cbn [readRegsListHelper pureAction].
  - exact I.
  - intro; exact (IH _ _ _).
Qed.

Lemma pureAction_readRegsList :
  forall t k (sz : Z) (l : list (@RegOfKind t k)) (idx : Expr type (Bit sz)),
    pureAction (@readRegsList type k sz t l idx).
Proof.
  intros t k sz l idx; exact (pureAction_readRegsListHelper t k sz l 0 [] idx).
Qed.

Lemma pureAction_writeRegsListHelper :
  forall t k (sz : Z) (l : list (@RegOfKind t k)) (i : nat) (idx : Expr type (Bit sz)) (val : Expr type k),
    pureAction (writeRegsListHelper (ty := type) i l idx val).
Proof.
  intros t k sz l; induction l as [| r l IH]; intros i idx val; cbn [writeRegsListHelper pureAction].
  - exact I.
  - split; [exact I | split; [exact I | intro; exact (IH _ _ _)]].
Qed.

Lemma pureAction_writeRegsList :
  forall t k (sz : Z) (l : list (@RegOfKind t k)) (idx : Expr type (Bit sz)) (val : Expr type k),
    pureAction (@writeRegsList type k sz t l idx val).
Proof.
  intros t k sz l idx val; exact (pureAction_writeRegsListHelper t k sz l 0 idx val).
Qed.

Ltac step_pure :=
  repeat lazymatch goal with
  | |- pureAction (@readRegsList type ?k ?sz ?t ?l ?i) => exact (pureAction_readRegsList t k sz l i)
  | |- pureAction (@writeRegsList type ?k ?sz ?t ?l ?i ?v) => exact (pureAction_writeRegsList t k sz l i v)
  | |- pureAction (Return _) => exact I
  | |- pureAction (LetExp _ _ _) => intro
  | |- pureAction (ReadReg _ _ _) => intro
  | |- pureAction (WriteReg _ _ _) => cbn [pureAction]
  | |- pureAction (System _ _) => cbn [pureAction]
  | |- pureAction (LetAction _ _ _) => split; [| intro]
  | |- pureAction (IfElse _ _ _ _ _) => split; [| split; [| intro]]
  end.

Lemma pureAction_handleTrap :
  forall pcAddrInit currPcc a b,
    pureAction (@handleTrap pcAddrInit type currPcc a b).
Proof.
  intros; unfold handleTrap; step_pure.
Qed.

Lemma evalActionFun_executeNonDeferred_some :
  forall pcAddrInit (pcc : type FullECapWithTag) (meip mtip : bool)
         (aluOut : type AluOutUnion) (rf : RfState pcAddrInit),
    evalActionFun (@executeNonDeferred pcAddrInit type pcc meip mtip aluOut) rf <> None.
Proof.
  intros pcAddrInit pcc meip mtip aluOut rf.
  apply evalActionFun_some_of_pure.
  unfold executeNonDeferred, executeInterrupt, executeSequential, executeNonSequential,
         isInterruptPending, incrementMinstret, updateMshwmOnStore.
  repeat lazymatch goal with
  | |- pureAction (@handleTrap ?pc ?ty ?c ?a ?b) => exact (pureAction_handleTrap pc c a b)
  | |- pureAction (@readRegsList type ?k ?sz ?t ?l ?i) => exact (pureAction_readRegsList t k sz l i)
  | |- pureAction (@writeRegsList type ?k ?sz ?t ?l ?i ?v) => exact (pureAction_writeRegsList t k sz l i v)
  | |- pureAction (Return _) => exact I
  | |- pureAction (LetExp _ _ _) => intro
  | |- pureAction (ReadReg _ _ _) => intro
  | |- pureAction (WriteReg _ _ _) => cbn [pureAction]
  | |- pureAction (System _ _) => cbn [pureAction]
  | |- pureAction (LetAction _ _ _) => split; [| intro]
  | |- pureAction (IfElse _ _ _ _ _) => split; [| split; [| intro]]
  end.
Qed.

Lemma GInstStep_det :
  forall pcAddrInit rf0 rf1 rf2 e,
    GInstStep pcAddrInit rf0 rf1 e ->
    GInstStep pcAddrInit rf0 rf2 e ->
    rf1 = rf2.
Proof.
  intros pcAddrInit rf0 rf1 rf2 e
         [_ [_ [_ [ex1 [m1 [Hs1 [_ ->]]]]]]]
         [_ [_ [_ [ex2 [m2 [Hs2 [_ ->]]]]]]].
  destruct (SemAction_det_of_some (rfTree pcAddrInit) defaultEnv _ _ rf0 m1 m2 ex1 ex2
              (evalActionFun_executeNonDeferred_some pcAddrInit _ _ _ _ rf0) Hs1 Hs2) as [-> ->].
  reflexivity.
Qed.

Lemma GChain_det :
  forall pcAddrInit G rf0 rf1 rf2,
    GChain pcAddrInit rf0 G rf1 ->
    GChain pcAddrInit rf0 G rf2 ->
    rf1 = rf2.
Proof.
  intros pcAddrInit G; induction G as [| it G IH]; intros rf0 rf1 rf2 H1 H2.
  - inversion H1; inversion H2; subst; reflexivity.
  - inversion H1 as [| ? ? ? Ht1 | ? m1 e ? ? Hs1 Hr1]; subst;
    inversion H2 as [| ? ? ? Ht2 | ? m2 ? ? ? Hs2 Hr2]; subst.
    + exact (IH _ _ _ Ht1 Ht2).
    + pose proof (GInstStep_det pcAddrInit rf0 m1 m2 e Hs1 Hs2) as ->.
      exact (IH _ _ _ Hr1 Hr2).
Qed.

Lemma tl_app_nonempty :
  forall {A : Type} (l1 l2 : list A),
    l1 <> [] ->
    tl (l1 ++ l2) = (tl l1 ++ l2)%list.
Proof.
  intros A [| x xs] l2 Hne; [exfalso; apply Hne; reflexivity | reflexivity].
Qed.

Lemma snoc_eq_inv :
  forall {A : Type} (l1 l2 : list A) (x y : A),
    (l1 ++ [x])%list = (l2 ++ [y])%list ->
    l1 = l2 /\ x = y.
Proof.
  intros A l1; induction l1 as [| a l1 IH]; intros [| b l2] x y H; cbn [app] in H.
  - injection H as ->; split; reflexivity.
  - destruct l2; cbn [app] in H; discriminate H.
  - destruct l1; cbn [app] in H; discriminate H.
  - injection H as -> H'; destruct (IH l2 x y H') as [-> ->]; split; reflexivity.
Qed.

Lemma snoc_split_GInst :
  forall (G G1 G2 : list GItem) (e e0 : GEntry),
    (G ++ [GInst e])%list = (G1 ++ GInst e0 :: G2)%list ->
    (G1 = G /\ e0 = e /\ G2 = []) \/
    (exists G2', G = (G1 ++ GInst e0 :: G2')%list /\ G2 = (G2' ++ [GInst e])%list).
Proof.
  intros G G1 [| g0 G2_] e e0 H.
  - change (GInst e0 :: []) with ([GInst e0])%list in H.
    destruct (snoc_eq_inv G G1 (GInst e) (GInst e0) H) as [<- Heq].
    injection Heq as ->; left; repeat split; reflexivity.
  - destruct (exists_last (l := g0 :: G2_)) as [G2' [last Eg2]]; [discriminate |].
    right; exists G2'; rewrite Eg2 in H |- *.
    assert (H' : (G ++ [GInst e])%list = ((G1 ++ GInst e0 :: G2') ++ [last])%list)
      by (rewrite <- app_assoc; exact H).
    destruct (snoc_eq_inv G (G1 ++ GInst e0 :: G2') (GInst e) last H') as [-> ->].
    split; reflexivity.
Qed.

Ltac strip_var u :=
  lazymatch u with
  | evalExpr (Var _ _ ?u') => strip_var u'
  | _ => u
  end.

Ltac readback :=
  match goal with |- context [evalExpr (@ReadUnionData _ ?ls (Var ?ty ?k ?u) ?i)] =>
    let w := strip_var u in
    lazymatch w with evalExpr (BuildUnion _ (Var _ _ ?x)) =>
      replace (evalExpr (@ReadUnionData _ ls (Var ty k u) i)) with x
        by (symmetry; exact (evalExpr_ReadUnionData_BuildUnion ls i (Var _ _ x) eq_refl))
    end
  end.

Ltac tag_contra H :=
  match type of H with
  | ?L = true => assert (Hc_ : L = false) by reflexivity; rewrite Hc_ in H; discriminate H
  | ?L = false => assert (Hc_ : L = true) by reflexivity; rewrite Hc_ in H; discriminate H
  end.

Lemma loadOutcome_dst :
  forall config (pl : type PendingLoad) (v : type FullCapWithTag),
    (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = true ->
       (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `! "RevLookup")).(Snd).(Fst).(Fst)
         = pl.(Fst)) /\
    (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `? "RevLookup") = false ->
       (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl v))) `! "Writeback")).(Fst) = pl.(Fst)).
Proof.
  intros config pl v; unfold dispatchLoadResponse; cbn [evalLetExpr].
  match goal with |- context [evalExpr (Var type Bool (evalExpr (Eq ?x ?y)))] =>
    change (evalExpr (Var type Bool (evalExpr (Eq x y)))) with (evalExpr (Eq x y));
    destruct (evalExpr (Eq x y)); cbv iota
  end.
  - match goal with |- context [evalExpr (Var type Bool (evalExpr (needsRevocationCheck ?c ?e ?tg)))] =>
      change (evalExpr (Var type Bool (evalExpr (needsRevocationCheck c e tg))))
        with (evalExpr (needsRevocationCheck c e tg));
      destruct (evalExpr (needsRevocationCheck c e tg)); cbv iota
    end.
    + split; [intros _; readback; reflexivity | intros Hf; tag_contra Hf].
    + split; [intros Ht; tag_contra Ht | intros _; readback; reflexivity].
  - split; [intros Ht; tag_contra Ht | intros _; readback; reflexivity].
Qed.

(* --- 2. Lockstep Spec Step & Relation Helpers (`Section ExecLive`) --- *)

Section ExecLive.
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

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation CT := (specCoreTree pcAddrInit specRegions).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation RfSt := (RfState pcAddrInit).
  Local Abbreviation specClintStateA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation specPlicStateA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation sRfA := (sRf pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation sSecondA := (sSecond pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation mkCoreA := (mkCore pcAddrInit specRegions).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation GhostT := (Ghost pcAddrInit).
  Local Abbreviation iDmStA :=
    (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Lemma dmLoadRp_in_olderWriters :
    forall (s1 : IState),
      dmLoadRp (iDmStA s1) = true ->
      Zmod.eqb (ldPending (dmLoadRpV (iDmStA s1))).(Fst) Zmod.zero = false ->
      In (ldPending (dmLoadRpV (iDmStA s1))).(Fst)
        (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1).
  Proof.
    intros s1 Hrp Hnz.
    unfold olderWriters; apply filter_In; split; [| rewrite Hnz; reflexivity].
    apply in_or_app; left; unfold dmInFlightDst; cbv zeta; rewrite Hrp; left; reflexivity.
  Qed.

  Lemma some_eq_fst :
    forall {A B : Type} (p1 p2 : A * B),
      Some p1 = Some p2 -> fst p1 = fst p2.
  Proof.
    intros A B p1 p2 H.
    exact (f_equal (fun z => match z with Some p => fst p | None => fst p1 end) H).
  Qed.

  Lemma fst_specLoadWb :
    forall m pl val,
      fst (specLoadWb config pre post revBase revPfB revPfA initLine m pl val) = pl.(Fst).
  Proof.
    intros m pl val.
    destruct (loadOutcome_dst config pl val) as [Hrev Hwb].
    unfold specLoadWb; cbv zeta.
    destruct (evalExpr ((Var type LoadOutcome (evalLetExpr (dispatchLoadResponse config pl val))) `? "RevLookup")) eqn:E;
      cbn [fst].
    - exact (Hrev eq_refl).
    - exact (Hwb eq_refl).
  Qed.

  Lemma fst_revWb :
    forall m rc,
      fst (revWb config pre post revBase revPfB revPfA initLine m rc) = rc.(Snd).(Fst).(Fst).
  Proof.
    intros m rc; unfold revWb; cbv zeta; reflexivity.
  Qed.

  Lemma cnwb_dmInFlightDst :
    forall (g : GhostT) (s1 : IState) (s2 : SState) d v,
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g s1 s2 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g s1 s2 ->
      g_cnwb pcAddrInit g = Some (d, v) ->
      dmInFlightDst pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 = [d].
  Proof.
    intros g s1 s2 d v [Hcn1 [Hcn2 [_ [_ [Hcn5 [_ Hval]]]]]] Hacc Hcn.
    unfold dmInFlightDst; cbv zeta.
    destruct (dmCheck (iDmStA s1)) eqn:Eck.
    { destruct (dmCheck_excl _ Eck) as [_ [Elrp [Errq Errp]]]; rewrite Elrp, Errq, Errp.
      specialize (Hcn5 eq_refl); rewrite Hcn in Hcn5.
      apply some_eq_fst in Hcn5; cbn [fst] in Hcn5.
      destruct (checkNeeds config (dmCheckV (iDmStA s1))) in Hcn5.
      - rewrite fst_revWb in Hcn5; subst d; reflexivity.
      - subst d; reflexivity. }
    destruct (dmRevRq (iDmStA s1)) eqn:Errq.
    - destruct (dmLoadRp (iDmStA s1)) eqn:Elrp.
      + destruct (dmLoadRp_excl _ Elrp) as [_ [E _]]; rewrite E in Errq; discriminate.
      + specialize (Hcn2 eq_refl); rewrite Hcn in Hcn2.
        apply some_eq_fst in Hcn2; cbn [fst] in Hcn2; rewrite fst_revWb in Hcn2; subst d; reflexivity.
    - unfold AccessRel in Hacc.
      destruct (g_acc pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt st].
      + destruct Hacc as [_ [_ [_ [_ [_ [[Elrp Errp] _]]]]]].
        destruct (dmLoadRq (iDmStA s1)) eqn:Elrq; [rewrite (Hcn1 eq_refl) in Hcn; discriminate |].
        pose proof (dmState_tags_exhaust _ Hval Elrq Elrp Errq Eck) as E; rewrite E in Errp; discriminate.
      + destruct Hacc as [_ [Elrq _]]; rewrite (Hcn1 Elrq) in Hcn; discriminate.
      + destruct Hacc as [_ [_ [Elrp [-> [_ [_ Hst]]]]]]; rewrite Elrp; cbv zeta in Hst.
        destruct st as [[|] | [|] | [|] | [|] rp | res].
        * destruct Hst as [_ [E _]]; rewrite E in Hcn; discriminate.
        * destruct Hst as [_ [_ [E _]]]; rewrite E in Hcn; discriminate.
        * destruct Hst as [_ [E _]]; rewrite E in Hcn; discriminate.
        * destruct Hst as [_ [_ [E _]]]; rewrite E in Hcn; discriminate.
        * destruct Hst as [_ [E _]]; rewrite E in Hcn; discriminate.
        * destruct Hst as [_ [_ [E _]]]; rewrite E in Hcn; discriminate.
        * destruct Hst as [_ [_ E]]; rewrite E in Hcn; apply some_eq_fst in Hcn; cbn [fst] in Hcn; rewrite fst_specLoadWb in Hcn; subst d; reflexivity.
        * destruct Hst as [_ E].
          destruct (crossesB (ldAddr ld) (plSize (ldPending ld))).
          -- destruct E as [_ E]; rewrite E in Hcn; discriminate.
          -- destruct E as [_ E]; rewrite E in Hcn; apply some_eq_fst in Hcn; cbn [fst] in Hcn; rewrite fst_specLoadWb in Hcn; subst d; reflexivity.
        * destruct Hst as [_ E]; rewrite E in Hcn; apply some_eq_fst in Hcn; cbn [fst] in Hcn; rewrite fst_specLoadWb in Hcn; subst d; reflexivity.
      + destruct Hacc as [_ [_ [Errp [-> [_ [_ [_ [E _]]]]]]]].
        destruct (dmLoadRp (iDmStA s1)) eqn:Elrp.
        * destruct (dmLoadRp_excl _ Elrp) as [_ [_ E']]; rewrite E' in Errp; discriminate.
        * rewrite Errp; rewrite E in Hcn; apply some_eq_fst in Hcn; cbn [fst] in Hcn; rewrite fst_revWb in Hcn; subst d; reflexivity.
      + destruct Hacc as [_ [_ [_ [[Elrp Errp] _]]]].
        destruct (dmLoadRq (iDmStA s1)) eqn:Elrq; [rewrite (Hcn1 eq_refl) in Hcn; discriminate |].
        pose proof (dmState_tags_exhaust _ Hval Elrq Elrp Errq Eck) as E; rewrite E in Errp; discriminate.
      + destruct Hacc as [_ [_ [_ [[Elrp Errp] _]]]].
        destruct (dmLoadRq (iDmStA s1)) eqn:Elrq; [rewrite (Hcn1 eq_refl) in Hcn; discriminate |].
        pose proof (dmState_tags_exhaust _ Hval Elrq Elrp Errq Eck) as E; rewrite E in Errp; discriminate.
      + destruct Hacc as [_ [_ [[Elrp Errp] _]]].
        destruct (dmLoadRq (iDmStA s1)) eqn:Elrq; [rewrite (Hcn1 eq_refl) in Hcn; discriminate |].
        pose proof (dmState_tags_exhaust _ Hval Elrq Elrp Errq Eck) as E; rewrite E in Errp; discriminate.
  Qed.

  Lemma cnwb_in_olderWriters :
    forall (g : GhostT) (s1 : IState) (s2 : SState) d v,
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g s1 s2 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
        initLine g s1 s2 ->
      g_cnwb pcAddrInit g = Some (d, v) ->
      Zmod.eqb d Zmod.zero = false ->
      In d (olderWriters pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1).
  Proof.
    intros g s1 s2 d v Hcnr Hacc Hcn Hnz.
    unfold olderWriters; apply filter_In; split; [| rewrite Hnz; reflexivity].
    apply in_or_app; left; rewrite (cnwb_dmInFlightDst g s1 s2 d v Hcnr Hacc Hcn); left; reflexivity.
  Qed.

  Lemma specStep_lockstep :
    forall rf0 m sl fo aluOut rfMid execOut,
      SpecNoWait specRegions m ->
      optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) fo ->
      aluOut = evalLetExpr (@wrappedAlu type (readPcc pcAddrInit rf0) (evalRegRead pcAddrInit (evalDecode fo) rf0)) ->
      SemAction defaultEnv
        (@executeNonDeferred pcAddrInit type (readPcc pcAddrInit rf0)
           (plicMeipOf (specPlicStateA m)) (clintSampled (specClintStateA m)) aluOut)
        rf0 rfMid execOut ->
      optValid (execDataMem execOut) = false ->
      optValid (execMulDiv execOut) = false ->
      exists m',
        TraceFrameS specRegions m m' /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSysA rf0 m sl)
          (mkSysA (writePcc pcAddrInit (defNextPcc execOut) rfMid) m' sl)
          Zmod.zero.
  Proof.
    intros rf0 m sl fo aluOut rfMid execOut Hnw Hsl Hfa Halu Hsem Hdm Hmd.
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSysA rf0 m sl)
                    (fun s2' _ => exists m', TraceFrameS specRegions m m' /\
                                             s2'.(Fst) = mkCoreA (writePcc pcAddrInit (defNextPcc execOut) rfMid) m' sl)).
    { unfold specStep.
      apply sys_memAct_wp; apply specMemReadFenceIWait_wp; [exact Hnw |]; cbv beta.
      apply sys_coreAct_wp; apply readSecondLine_wp; cbv beta.
      apply ev_ifElse_true; [unfold optValid in Hsl; cbn; rewrite Hsl; reflexivity |].
      apply sys_memAct_wp; apply plicMeip_wp; cbv beta.
      apply sys_memAct_wp; apply clintMtip_wp; cbv beta.
      apply sys_coreAct_wp.
      apply (specFetch_wp initLine pcAddrInit specRegions fwcs _ _ m sl fo).
      - apply coreEnvOK.
      - intros L; apply lineUnique_disjoint, Is_true_eq_true, Hdisj.
      - exact Hfa.
      - intros m' Hm'; cbv beta.
        apply ev_letL; cbv beta.
        apply sys_rfAct_wp; apply (proj2 (evalActionPropGen_regRead _ _ _ _)); cbv beta.
        apply sys_rfAct_wp; apply (proj2 (evalActionPropGen_readRegsList _ _ _ _)); cbv beta.
        apply ev_letL; cbv beta.
        match goal with |- evalActionPropGen _ (LetAction _ (liftAction _ (@executeNonDeferred _ _ _ _ _ ?a)) _) _ _ =>
          assert (Ha : a = aluOut)
        end.
        { match goal with |- evalLetExpr (@wrappedAlu _ ?p _) = _ =>
            replace p with (readPcc pcAddrInit rf0)
              by (unfold readPcc, readGpr; f_equal; reflexivity)
          end.
          symmetry; exact Halu. }
        rewrite Ha.
        apply sys_rfAct_wp.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        apply (proj1 (evalActionPropGen_noRecvTree_env defaultEnv _ _ _ _ (noRecv_rfTree pcAddrInit))).
        eapply evalActionPropGen_mono; [| exact Hsem].
        intros s r [-> ->]; cbv beta.
        apply sys_rfAct_wp; apply (proj2 (evalActionPropGen_writeRegsList _ _ _ _ _)); cbv beta.
        repeat (apply ev_letExp; cbv beta).
        apply sys_coreAct_wp.
        eapply evalActionPropGen_mono.
        + intros sc' r' HQ; cbv beta; apply ev_return; cbv beta; apply ev_return; exact HQ.
        + apply deferred_none_wp; [exact Hdm | exact Hmd |].
          exists m'; split; [exact Hm' |].
          unfold writePcc, updGpr; f_equal; reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [m' [Hm' E]]]]].
    exists m'; split; [exact Hm' |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.

End ExecLive.
