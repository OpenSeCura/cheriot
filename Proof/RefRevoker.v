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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE IMPL REVOKER STEPS, ONE RULE PER PHASE
 * ===========================================================================
 * What each of the five revoker rules (`implRevokerSteps`) does to the impl memory:
 * 1. whether a region's portRq holds a write (`noPortWriteB`), as the impl tests it;
 * 2. the tags of the unions involved, and reading back a `state` just written;
 * 3. the impl revoker inside the impl memory (`revOfR`, `setRevR`) and a characterization
 *    of each rule (`*_char`): either nothing changes, or the listed registers change. *)

Local Abbreviation TS t := (TreeState DomainElemState t).

(* --- 1. No Write Waiting in a Region's portRq --- *)

Section NoPortWrite.
  Variable core : string.

  Definition regionNoPortWriteB (r : MemRegion) : TS (implMemRegionTree core r) -> bool :=
    match r.(regionKind) as k return TS (implMemRegionKindTree core r k) -> bool with
    | ExternalMem => fun y => negb (andb (optValid (extPortRq core r y)) (prIsWrite (optData (extPortRq core r y))))
    | CustomMem _ _ _ _ => fun _ => true
    end.

  Fixpoint noPortWriteB (l : list MemRegion) : TS (implRegionsTree core l) -> bool :=
    match l as l0 return TS (implRegionsTree core l0) -> bool with
    | [] => fun _ => true
    | r :: l' => fun mi => andb (regionNoPortWriteB r mi.(Fst)) (noPortWriteB l' mi.(Snd).(Fst))
    end.

  Lemma regionNoPortWrite_wp :
    forall r env (y : TS (implMemRegionTree core r)) P,
      evalActionPropGen env (@implMemRegionNoPortWriteRq core r type) y P <-> P y (regionNoPortWriteB r y).
  Proof.
    intros r; destruct r as [nm bs sz kd im ba sa]; destruct kd; intros env y P.
    - unfold implMemRegionNoPortWriteRq, regionNoPortWriteB, implExternalNoPortWriteRq; cbn.
      reflexivity.
    - cbn. reflexivity.
  Qed.

  Lemma noPortWrite_fold :
    forall l acc (mi : TS (implRegionsTree core l)) env P,
      evalActionPropGen env
        (genFoldRegionActionsAux (implMemRegionTree core) (fun r => @implMemRegionNoPortWriteRq core r type)
           (@And _ _) acc l) mi P <->
      P mi (andb (fold_left andb (map (@evalExpr Bool) (rev acc)) true) (noPortWriteB l mi)).
  Proof.
    induction l as [| r l IH]; intros acc mi env P.
    - cbn [genFoldRegionActionsAux evalActionPropGen noPortWriteB].
      rewrite andb_true_r, rev_tail_fast; cbn [evalExpr]; reflexivity.
    - cbn [genFoldRegionActionsAux evalActionPropGen].
      refine (iff_trans (evalActionPropGen_liftAction child0Path _ _ _) _).
      destruct mi as [y [rest []]].
      cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
      refine (iff_trans (regionNoPortWrite_wp r _ _ _) _); cbv beta.
      refine (iff_trans (evalActionPropGen_liftAction child1Path _ _ _) _).
      cbn [child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
      refine (iff_trans (IH _ _ _ _) _).
      cbn [noPortWriteB Fst Snd rev map].
      rewrite map_app, fold_left_app; cbn [map fold_left evalExpr].
      rewrite andb_assoc; reflexivity.
  Qed.

  Lemma noPortWrite_wp :
    forall l env (m : TS (implMemTree core l)) P,
      evalActionPropGen env (liftAction child0Path (@implRegionsNoPortWriteRq core type l)) m P <->
      P m (noPortWriteB l m.(Fst)).
  Proof.
    intros l env m P.
    refine (iff_trans (evalActionPropGen_liftAction child0Path _ _ _) _).
    unfold implRegionsNoPortWriteRq, genFoldRegionActions.
    refine (iff_trans (noPortWrite_fold _ _ _ _ _) _).
    destruct m as [mr mrest].
    cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd rev map fold_left andb].
    reflexivity.
  Qed.

  (* No staged request at all: no staged write *)
  Lemma noPortWriteB_true :
    forall l (mi : TS (implRegionsTree core l)),
      AllPorts core (fun r y => optValid (extPortRq core r y) = false) l mi -> noPortWriteB l mi = true.
  Proof.
    intros l; induction l as [| r l IH]; intros mi H; cbn [AllPorts noPortWriteB] in *; [reflexivity |].
    destruct H as [H0 H1]; rewrite (IH _ H1), andb_true_r.
    revert H0; generalize (Fst mi); clear.
    unfold RegionPort, regionNoPortWriteB, implMemRegionTree.
    destruct (regionKind r); intros y H0; [rewrite H0; reflexivity | reflexivity].
  Qed.

  (* A write staged in the ExternalMem region of line `L` *)
  Lemma noPortWriteB_false :
    forall L w l (mi : TS (implRegionsTree core l)),
      lineKind l L = Some true ->
      AllPorts core (fun r y => isRegionAddrB r L = true -> extPortRq core r y = someWrite w) l mi ->
      noPortWriteB l mi = false.
  Proof.
    intros L w l; induction l as [| r l IH]; intros mi Hk H; cbn [AllPorts noPortWriteB lineKind] in *;
      [discriminate Hk |].
    destruct H as [H0 H1].
    destruct (isRegionAddrB r L) eqn:Er.
    - revert Hk H0; generalize (Fst mi); clear - Er.
      unfold RegionPort, regionNoPortWriteB, implMemRegionTree.
      destruct (regionKind r); intros y Hk H0; [| discriminate Hk].
      rewrite (H0 Er); reflexivity.
    - rewrite (IH _ Hk H1), andb_false_r; reflexivity.
  Qed.
End NoPortWrite.

(* --- 2. Tags of the Unions --- *)

Lemma msIdle_excl :
  forall st, msIdle st = true ->
    msReadRq st = false /\ msReadRqSent st = false /\ msReadRpReady st = false /\ msWriteRq st = false.
Proof.
  intros [d tg]; unfold msIdle, msReadRq, msReadRqSent, msReadRpReady, msWriteRq; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma isReqRevoker_excl : forall r, isReqRevoker r = true -> isReqDataMem r = false.
Proof.
  intros [d tg]; unfold isReqRevoker, isReqDataMem; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; reflexivity.
Qed.

Lemma rpIdle_excl :
  forall p, rpIdle p = true ->
    rpWaitCapRp p = false /\ rpWaitRevBitRq p = false /\ rpWaitRevBitRp p = false /\ rpWriteCap p = false.
Proof.
  intros [d tg]; unfold rpIdle, rpWaitCapRp, rpWaitRevBitRq, rpWaitRevBitRp, rpWriteCap; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma rpWaitCapRp_excl :
  forall p, rpWaitCapRp p = true ->
    rpIdle p = false /\ rpWaitRevBitRq p = false /\ rpWaitRevBitRp p = false /\ rpWriteCap p = false.
Proof.
  intros [d tg]; unfold rpIdle, rpWaitCapRp, rpWaitRevBitRq, rpWaitRevBitRp, rpWriteCap; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma rpWaitRevBitRq_excl :
  forall p, rpWaitRevBitRq p = true ->
    rpIdle p = false /\ rpWaitCapRp p = false /\ rpWaitRevBitRp p = false /\ rpWriteCap p = false.
Proof.
  intros [d tg]; unfold rpIdle, rpWaitCapRp, rpWaitRevBitRq, rpWaitRevBitRp, rpWriteCap; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma rpWaitRevBitRp_excl :
  forall p, rpWaitRevBitRp p = true ->
    rpIdle p = false /\ rpWaitCapRp p = false /\ rpWaitRevBitRq p = false /\ rpWriteCap p = false.
Proof.
  intros [d tg]; unfold rpIdle, rpWaitCapRp, rpWaitRevBitRq, rpWaitRevBitRp, rpWriteCap; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

Lemma rpWriteCap_excl :
  forall p, rpWriteCap p = true ->
    rpIdle p = false /\ rpWaitCapRp p = false /\ rpWaitRevBitRq p = false /\ rpWaitRevBitRp p = false.
Proof.
  intros [d tg]; unfold rpIdle, rpWaitCapRp, rpWaitRevBitRq, rpWaitRevBitRp, rpWriteCap; cbn.
  intros H; apply Zmod.eqb_eq in H; subst tg; repeat split; reflexivity.
Qed.

(* Reading back the payload of a memory `state` just written *)
Lemma msReadRqV_build :
  forall e : Expr type MemStepOp,
    msReadRqV (evalExpr (BuildUnion (ls := MemStateList) (@Build_FinType (length MemStateList) 1 I) e)) = evalExpr e.
Proof. intros e; exact (evalExpr_ReadUnionData_BuildUnion MemStateList (@Build_FinType (length MemStateList) 1 I) e eq_refl). Qed.

Lemma msWriteRqV_build :
  forall e : Expr type MemStepOp,
    msWriteRqV (evalExpr (BuildUnion (ls := MemStateList) (@Build_FinType (length MemStateList) 4 I) e)) = evalExpr e.
Proof. intros e; exact (evalExpr_ReadUnionData_BuildUnion MemStateList (@Build_FinType (length MemStateList) 4 I) e eq_refl). Qed.

(* The revoker's computations on its registers, as the impl and the spec steps write them *)
Definition epochOdd (e : bits Xlen) : bool := evalExpr (FromBit Bool (TruncLsb (Xlen - 1) 1 (Var type (Bit Xlen) e))).
Definition scanDone (sa top : bits TagAddrWidth) : bool :=
  evalExpr (Uge (Var type (Bit TagAddrWidth) sa) (Var type (Bit TagAddrWidth) top)).
Definition epochInc (e : bits Xlen) : bits Xlen := evalExpr (Add [ Var type (Bit Xlen) e ; $1 ]).
Definition epochMkOdd (e : bits Xlen) : bits Xlen :=
  evalExpr ({< TruncMsb (Xlen - 1) 1 (Var type (Bit Xlen) e), Const type (Bit 1) (bits.of_Z 1 1) >}).
Definition scanNext (sa : bits TagAddrWidth) : bits TagAddrWidth := evalExpr (Add [ Var type (Bit TagAddrWidth) sa ; $1 ]).

(* --- 3. The Impl Revoker Inside the Impl Memory --- *)

Section RevLens.
  Variable core : string.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation implRegions := (implRegionsOf core pre post revBase revPfB revPfA).
  Local Abbreviation iRevR := (implRevRegion core revBase revPfB revPfA).
  Local Abbreviation pfI := (nth_error_app_cons_len pre iRevR post).
  Local Abbreviation revI := (revImplOf core pre post revBase revPfB revPfA).
  Local Abbreviation MT := (implMemTree core implRegions).
  Local Abbreviation RT := (implRegionsTree core implRegions).

  Definition revOfR (mr : TS RT) : TS (implRevokerTree core) :=
    (regionStateAt (implMemRegionTree core) (length pre) implRegions iRevR pfI mr).(Fst).

  Definition setRevR (mr : TS RT) (x : TS (implRevokerTree core)) : TS RT :=
    updRegionStateAt (implMemRegionTree core) (length pre) implRegions iRevR pfI mr
      (x ,, (regionStateAt (implMemRegionTree core) (length pre) implRegions iRevR pfI mr).(Snd)).

  Definition envRevOf (env : Env MT) (m : TS MT) : Env (implRevokerTree core) :=
    subEnv child0Path
      (envRegionAt (implMemRegionTree core) (length pre) implRegions iRevR pfI (subEnv child0Path env m) m.(Fst))
      (regionStateAt (implMemRegionTree core) (length pre) implRegions iRevR pfI m.(Fst)).

  Lemma evalActionPropGen_liftRev :
    forall env k (a : Action type (implRevokerTree core) k) (m : TS MT) P,
      evalActionPropGen env (@implNthRegionAction core type (length pre) implRegions iRevR pfI k a) m P <->
      evalActionPropGen (envRevOf env m) a (revOfR m.(Fst)) (fun x v => P (setRevR m.(Fst) x ,, m.(Snd)) v).
  Proof.
    intros env k a m P.
    unfold implNthRegionAction, implRegionsNthRegionAction, liftToImplRegion.
    refine (iff_trans (evalActionPropGen_liftAction child0Path _ m P) _).
    refine (iff_trans (evalActionPropGen_genNthRegionAction (implMemRegionTree core) (length pre) implRegions iRevR pfI _ _ _ _) _).
    refine (iff_trans (evalActionPropGen_liftAction child0Path _ _ _) _).
    destruct m as [mr mrest].
    cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
    unfold revOfR, setRevR, envRevOf; cbn [Fst Snd].
    reflexivity.
  Qed.

  Lemma evalExpr_Var : forall k (x : type k), evalExpr (Var type k x) = x.
  Proof. reflexivity. Qed.

  Lemma setRevR_revOfR : forall mr, setRevR mr (revOfR mr) = mr.
  Proof.
    intros mr; unfold setRevR, revOfR.
    rewrite updRegionStateAt_regionStateAt; reflexivity.
  Qed.

  Lemma revOfR_setRevR : forall mr x, revOfR (setRevR mr x) = x.
  Proof.
    intros mr x; unfold setRevR, revOfR.
    rewrite regionStateAt_updRegionStateAt; reflexivity.
  Qed.

  Lemma setRevR_setRevR : forall mr x y, setRevR (setRevR mr x) y = setRevR mr y.
  Proof.
    intros mr x y; unfold setRevR.
    rewrite regionStateAt_updRegionStateAt, updRegionStateAt_updRegionStateAt; reflexivity.
  Qed.

  Lemma setRevR_same : forall mr x, revOfR mr = x -> setRevR mr x = mr.
  Proof. intros mr x <-; apply setRevR_revOfR. Qed.

  Ltac rev_cbn H :=
    cbn -[evalExpr evalLetExpr toAction revOfR setRevR envRevOf implNthRegionAction implMemReadRq implMemWrite
          implMemReadRp implMemDeqRp implReadRevBitRqFor implGetDeqRevBitRpFor implMemNoPendingWrite
          implMemNoPortWriteRq noPortWriteB] in H.

  Ltac rev_fold H Ex :=
    repeat match type of H with
    | context [setRevR ?mr ?X] =>
        replace (setRevR mr X) with mr in H by (symmetry; apply setRevR_same; rewrite Ex; reflexivity)
    end.

  Ltac rev_lens H Ex :=
    apply evalActionPropGen_liftRev in H; cbn [Fst Snd] in H;
    rewrite ?revOfR_setRevR in H; rewrite ?Ex in H; rev_cbn H;
    rewrite ?setRevR_setRevR in H; rev_fold H Ex.

  Lemma waitRevBitRq_char :
    forall env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh,
      revOfR mr = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ->
      SemAction env (@implRevokerWaitRevBitRqStep core config implRegions type revI)
        (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (rpWaitRevBitRq ph = true /\ msIdle mst = true /\ noPortWriteB core implRegions mr = true /\
       exists st' rq' ph',
         m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,,
               (st' ,, (rq' ,, (mrp ,, tt)))) /\
         msReadRq st' = true /\ msReadRqV st' = stepOf false (revByteAddrOf config sb) byteSz (getDefault CapPacket) /\
         isReqRevoker rq' = true /\ rpWaitRevBitRp ph' = true).
  Proof.
    intros env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh Ex H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRevokerWaitRevBitRqStep, implRevokerWaitRevBitRq, ImplDevice.liftRevoker in H.
    cbn [evalActionPropGen] in H.
    rev_lens H Ex.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Eph end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    rev_lens H Ex.
    unfold implReadRevBitRqFor, implMemReadRq, implMemNoPortWriteRq in H.
    cbn [evalActionPropGen] in H.
    apply evalActionPropGen_toAction in H; rev_cbn H.
    apply noPortWrite_wp in H; rev_cbn H.
    rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Erdy end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    rev_lens H Ex.
    destruct H as [H _]; subst m'.
    assert (Hr : andb (msIdle mst) (noPortWriteB core implRegions mr) = true) by exact Erdy.
    apply andb_prop in Hr as [Hi Hn].
    right; split; [exact Eph | split; [exact Hi | split; [exact Hn |]]].
    do 3 eexists; split; [reflexivity |].
    split; [reflexivity |].
    split; [| split; reflexivity].
    rewrite msReadRqV_build; reflexivity.
  Qed.
  Lemma idle_char :
    forall env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh,
      revOfR mr = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ->
      SemAction env (@implRevokerIdleStep core implRegions type revI) (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (andb (negb (msWriteRq mst)) (noPortWriteB core implRegions mr) = true /\ rpIdle ph = true /\
       epochOdd e = true /\ scanDone sa st = false /\ msIdle mst = true /\
       exists st' rq' ph',
         m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (false ,, tt)))))))))))) ,,
               (st' ,, (rq' ,, (mrp ,, tt)))) /\
         msReadRq st' = true /\ msReadRqV st' = stepOf false (scanFull sa) capSz (getDefault CapPacket) /\
         isReqRevoker rq' = true /\ rpWaitCapRp ph' = true) \/
      (andb (negb (msWriteRq mst)) (noPortWriteB core implRegions mr) = true /\ rpIdle ph = true /\
       epochOdd e = true /\ scanDone sa st = true /\
       m' = (setRevR mr (b ,, (t ,, (c ,, (epochInc e ,, ((if ir then true else ist) ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,,
             (mst ,, (mrq ,, (mrp ,, tt))))) \/
      (andb (negb (msWriteRq mst)) (noPortWriteB core implRegions mr) = true /\ rpIdle ph = true /\
       epochOdd e = false /\ c = true /\
       m' = (setRevR mr (b ,, (t ,, (false ,, (epochMkOdd e ,, (false ,, (ir ,, (b ,, (t ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,,
             (mst ,, (mrq ,, (mrp ,, tt))))) \/
      (andb (negb (msWriteRq mst)) (noPortWriteB core implRegions mr) = true /\ rpIdle ph = true /\
       epochOdd e = false /\ c = false /\
       m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (false ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,,
             (mst ,, (mrq ,, (mrp ,, tt))))).
  Proof.
    intros env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh Ex H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRevokerIdleStep, implMemNoPendingWrite, implMemNoWriteRq, implMemNoPortWriteRq in H.
    cbn [evalActionPropGen] in H.
    rev_cbn H.
    apply noPortWrite_wp in H; rev_cbn H; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Enpw end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    assert (Hnp : andb (negb (msWriteRq mst)) (noPortWriteB core implRegions mr) = true) by exact Enpw.
    clear Enpw.
    unfold implRevokerIdle, ImplDevice.liftRevoker in H; cbn [evalActionPropGen] in H.
    rev_lens H Ex; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Eph end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    rev_lens H Ex; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Eodd end.
    - rev_lens H Ex; rev_lens H Ex; rewrite ?evalExpr_Var in H.
      match type of H with context [if ?c then _ else _] => destruct c eqn:Edone end.
      + assert (Hd : negb (scanDone sa st) = true) by exact Edone; apply negb_true_iff in Hd; clear Edone.
        unfold implMemReadRq, implMemNoPortWriteRq in H; cbn [evalActionPropGen] in H.
        apply noPortWrite_wp in H; rev_cbn H; rewrite ?evalExpr_Var in H.
        match type of H with context [if ?c then _ else _] => destruct c eqn:Erdy end.
        2: { left; destruct H as [H _]; symmetry; exact H. }
        assert (Hr : andb (msIdle mst) (noPortWriteB core implRegions mr) = true) by exact Erdy.
        apply andb_prop in Hr as [Hi _].
        rev_lens H Ex; rev_lens H Ex.
        destruct H as [H _]; subst m'.
        right; left.
        split; [exact Hnp | split; [exact Eph | split; [exact Eodd | split; [exact Hd | split; [exact Hi |]]]]].
        do 3 eexists; split; [reflexivity |].
        split; [reflexivity |].
        split; [| split; reflexivity].
        rewrite msReadRqV_build; reflexivity.
      + assert (Hd : negb (scanDone sa st) = false) by exact Edone; apply negb_false_iff in Hd; clear Edone.
        rev_lens H Ex; rev_lens H Ex; rewrite ?evalExpr_Var in H.
        match type of H with context [if ?c then _ else _] => destruct c eqn:Eir end.
        * rev_lens H Ex.
          destruct H as [H _]; subst m'.
          right; right; left.
          split; [exact Hnp | split; [exact Eph | split; [exact Eodd | split; [exact Hd |]]]].
          first [reflexivity | rewrite Eir; reflexivity].
        * destruct H as [H _]; subst m'.
          right; right; left.
          split; [exact Hnp | split; [exact Eph | split; [exact Eodd | split; [exact Hd |]]]].
          first [reflexivity | rewrite Eir; reflexivity].
    - rev_lens H Ex; rev_lens H Ex; rewrite ?evalExpr_Var in H.
      match type of H with context [if ?c then _ else _] => destruct c eqn:Ec end.
      + rev_lens H Ex; rev_lens H Ex; rev_lens H Ex; rev_lens H Ex; rev_lens H Ex; rev_lens H Ex.
        destruct H as [H _]; subst m'.
        right; right; right; left.
        split; [exact Hnp | split; [exact Eph | split; [exact Eodd | split; [first [exact Ec | reflexivity] |]]]].
        first [reflexivity | rewrite Ec; reflexivity].
      + destruct H as [H _]; subst m'.
        right; right; right; right.
        split; [exact Hnp | split; [exact Eph | split; [exact Eodd | split; [first [exact Ec | reflexivity] |]]]].
        first [reflexivity | rewrite Ec; reflexivity].
  Qed.

  (* The rev bit a rev-bit read response `v` gives for base `base` *)
  Definition revBitOfVal (base : type (Bit (AddrSz + 1))) (v : type FullCapWithTag) : bool :=
    let lookup := evalLetExpr (@computeRevBitAddr config type base) in
    evalExpr (extractRevBit lookup (TruncLsb (AddrSz - 8) 8 (##v`"addr"))).

  Lemma waitCapRp_char :
    forall env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh,
      revOfR mr = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ->
      SemAction env (@implRevokerWaitCapRpStep core config implRegions type revI)
        (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (rpWaitCapRp ph = true /\ msReadRpReady mst = true /\ isReqRevoker mrq = true /\
       capNeedsCheck config (msReadRpReadyV mst) = true /\
       exists st' ph',
         m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (msReadRpReadyV mst ,, (capBase (msReadRpReadyV mst) ,, (sh ,, tt)))))))))))) ,,
               (st' ,, (mrq ,, (mrp ,, tt)))) /\
         msIdle st' = true /\ rpWaitRevBitRq ph' = true) \/
      (rpWaitCapRp ph = true /\ msReadRpReady mst = true /\ isReqRevoker mrq = true /\
       capNeedsCheck config (msReadRpReadyV mst) = false /\
       exists st' ph',
         m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (scanNext sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,, (st' ,, (mrq ,, (mrp ,, tt)))) /\
         msIdle st' = true /\ rpIdle ph' = true).
  Proof.
    intros env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh Ex H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRevokerWaitCapRpStep, implRevokerWaitCapRp, ImplDevice.liftRevoker in H.
    cbn [evalActionPropGen] in H.
    rev_lens H Ex; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Eph end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    rev_lens H Ex; rewrite ?evalExpr_Var in H.
    unfold implMemReadRp in H; cbn [evalActionPropGen] in H; rev_cbn H; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Erp end.
    - match type of H with context [if ?c then _ else _] => destruct c eqn:Ev end.
      2: { exfalso; cbn in Ev; discriminate Ev. }
      assert (Hr : andb (msReadRpReady mst) (isReqRevoker mrq) = true) by exact Erp.
      apply andb_prop in Hr as [Hr1 Hr2].
      unfold implMemDeqRp in H; rev_cbn H; rewrite ?evalExpr_Var in H.
      apply evalActionPropGen_toAction in H; rev_cbn H; rewrite ?evalExpr_Var in H.
      match type of H with context [if ?c then _ else _] => destruct c eqn:Ech end.
      + rev_lens H Ex; rev_lens H Ex; rev_lens H Ex.
        destruct H as [H _]; subst m'.
        right; left.
        split; [exact Eph | split; [exact Hr1 | split; [exact Hr2 | split; [exact Ech |]]]].
        do 2 eexists; split; [reflexivity | split; reflexivity].
      + rev_lens H Ex; rev_lens H Ex.
        destruct H as [H _]; subst m'.
        right; right.
        split; [exact Eph | split; [exact Hr1 | split; [exact Hr2 | split; [exact Ech |]]]].
        do 2 eexists; split; [reflexivity | split; reflexivity].
    - match type of H with context [if ?c then _ else _] => destruct c eqn:Ev end.
      { exfalso; cbn in Ev; discriminate Ev. }
      left; destruct H as [H _]; symmetry; exact H.
  Qed.

  Lemma waitRevBitRp_char :
    forall env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh,
      revOfR mr = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ->
      SemAction env (@implRevokerWaitRevBitRpStep core config implRegions type revI)
        (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (rpWaitRevBitRp ph = true /\ msReadRpReady mst = true /\ isReqRevoker mrq = true /\
       exists st' ph',
         msIdle st' = true /\
         ((sh = true /\ rpIdle ph' = true /\
           m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,, (st' ,, (mrq ,, (mrp ,, tt))))) \/
          (sh = false /\ revBitOfVal sb (msReadRpReadyV mst) = true /\ rpWriteCap ph' = true /\
           m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,, (st' ,, (mrq ,, (mrp ,, tt))))) \/
          (sh = false /\ revBitOfVal sb (msReadRpReadyV mst) = false /\ rpIdle ph' = true /\
           m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (scanNext sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,, (st' ,, (mrq ,, (mrp ,, tt))))))).
  Proof.
    intros env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh Ex H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRevokerWaitRevBitRpStep, implRevokerWaitRevBitRp, ImplDevice.liftRevoker in H.
    cbn [evalActionPropGen] in H.
    rev_lens H Ex; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Eph end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    rev_lens H Ex; rev_lens H Ex; rewrite ?evalExpr_Var in H.
    unfold implGetDeqRevBitRpFor, implMemReadRp in H; cbn [evalActionPropGen] in H.
    apply evalActionPropGen_toAction in H; rev_cbn H; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Erp end.
    - match type of H with context [if ?c then _ else _] => destruct c eqn:Ev end.
      2: { exfalso; cbn in Ev; discriminate Ev. }
      assert (Hr : andb (msReadRpReady mst) (isReqRevoker mrq) = true) by exact Erp.
      apply andb_prop in Hr as [Hr1 Hr2].
      unfold implMemDeqRp in H; rev_cbn H; rewrite ?evalExpr_Var in H.
      match type of H with context [if ?c then _ else _] => destruct c eqn:Ev2 end.
      2: { exfalso; cbn in Ev2; discriminate Ev2. }
      rev_lens H Ex; rewrite ?evalExpr_Var in H.
      right; split; [exact Eph | split; [exact Hr1 | split; [exact Hr2 |]]].
      match type of H with context [if ?c then _ else _] => destruct c eqn:Esh end.
      + rev_lens H Ex.
        destruct H as [H _]; subst m'.
        do 2 eexists; split; [| left; split; [first [exact Esh | reflexivity] | split; [| reflexivity]]];
          reflexivity.
      + match type of H with context [if ?c then _ else _] => destruct c eqn:Erb end.
        * rev_lens H Ex.
          destruct H as [H _]; subst m'.
          do 2 eexists; split; [| right; left; split; [first [exact Esh | reflexivity] |
                                   split; [exact Erb | split; [| reflexivity]]]];
            reflexivity.
        * rev_lens H Ex; rev_lens H Ex.
          destruct H as [H _]; subst m'.
          do 2 eexists; split; [| right; right; split; [first [exact Esh | reflexivity] |
                                   split; [exact Erb | split; [| reflexivity]]]];
            reflexivity.
    - match type of H with context [if ?c then _ else _] => destruct c eqn:Ev end.
      { exfalso; cbn in Ev; discriminate Ev. }
      match type of H with context [if ?c then _ else _] => destruct c eqn:Ev2 end.
      { exfalso; cbn in Ev2; discriminate Ev2. }
      left; destruct H as [H _]; symmetry; exact H.
  Qed.

  Lemma writeCap_char :
    forall env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh,
      revOfR mr = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ->
      SemAction env (@implRevokerWriteCapStep core implRegions type revI)
        (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (rpWriteCap ph = true /\ sh = true /\
       exists ph', rpIdle ph' = true /\
         m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,, (mst ,, (mrq ,, (mrp ,, tt))))) \/
      (rpWriteCap ph = true /\ sh = false /\ msIdle mst = true /\ noPortWriteB core implRegions mr = true /\
       exists st' ph',
         m' = (setRevR mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (scanNext sa ,, (st ,, (ph' ,, (sc ,, (sb ,, (sh ,, tt)))))))))))) ,, (st' ,, (mrq ,, (mrp ,, tt)))) /\
         msWriteRq st' = true /\
         msWriteRqV st' = stepOf false (scanFull sa) capSz (disassembleW (scanFull sa) (untagCap sc) capSz) /\
         rpIdle ph' = true).
  Proof.
    intros env mr mst mrq mrp m' v b t c e ist ir sa st ph sc sb sh Ex H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRevokerWriteCapStep, implRevokerWriteCap, ImplDevice.liftRevoker in H.
    cbn [evalActionPropGen] in H.
    rev_lens H Ex; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Eph end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    rev_lens H Ex; rev_lens H Ex; rewrite ?evalExpr_Var in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Esh end.
    - rev_lens H Ex.
      destruct H as [H _]; subst m'.
      right; left.
      split; [exact Eph | split; [first [exact Esh | reflexivity] |]].
      eexists; split; [| reflexivity]; reflexivity.
    - rev_lens H Ex; rewrite ?evalExpr_Var in H.
      unfold implMemWrite, implMemNoPortWriteRq in H; cbn [evalActionPropGen] in H.
      apply noPortWrite_wp in H; rev_cbn H; rewrite ?evalExpr_Var in H.
      match type of H with context [if ?c then _ else _] => destruct c eqn:Erdy end.
      2: { left; destruct H as [H _]; symmetry; exact H. }
      assert (Hr : andb (msIdle mst) (noPortWriteB core implRegions mr) = true) by exact Erdy.
      apply andb_prop in Hr as [Hi Hn].
      apply evalActionPropGen_toAction in H; rev_cbn H; rewrite ?evalExpr_Var in H.
      rev_lens H Ex; rev_lens H Ex.
      destruct H as [H _]; subst m'.
      right; right.
      split; [exact Eph | split; [first [exact Esh | reflexivity] | split; [exact Hi | split; [exact Hn |]]]].
      do 2 eexists; split; [reflexivity |].
      split; [reflexivity |].
      split; [| reflexivity].
      rewrite msWriteRqV_build; reflexivity.
  Qed.

End RevLens.
