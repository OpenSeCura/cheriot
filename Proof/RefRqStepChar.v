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
From Cheriot Require Import SpecDefines SpecDevice Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefSpecRead RefRevoker RefWriteRqPorts RefRouteAt.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the memory `state` machine's request steps (`implMemWriteRqStep`,
 * `implMemReadRqStep`), impl side: what one step does to the memory subtree. *)

Lemma msReadRqSentV_build :
  forall e : Expr type MemReadRqSent,
    msReadRqSentV (evalExpr (BuildUnion (ls := MemStateList) (@Build_FinType (length MemStateList) 2 I) e)) = evalExpr e.
Proof. intros e; exact (evalExpr_ReadUnionData_BuildUnion MemStateList (@Build_FinType (length MemStateList) 2 I) e eq_refl). Qed.

Lemma msReadRqSent_build :
  forall e : Expr type MemReadRqSent,
    msReadRqSent (evalExpr (BuildUnion (ls := MemStateList) (@Build_FinType (length MemStateList) 2 I) e)) = true.
Proof. intros e; reflexivity. Qed.

Section RqStepChar.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation MT := (implMemTree implRegions).
  Local Abbreviation RT := (implRegionsTree implRegions).

  Ltac mem_cbn H :=
    cbn -[evalExpr evalLetExpr toAction implRegionsLineWriteRq implRegionsLineReadRq implMemNoPortWriteRq
          noPortWriteB buildW stepOf] in H.

  (* The write step: nothing happens, or line `lineOf b addr` is handed to the regions *)
  Lemma writeRqStep_char :
    forall env mr mst mrq mrp m' v b addr size pkt,
      msWriteRqV mst = stepOf b addr size pkt ->
      SemAction env (@implMemWriteRqStep implRegions type) (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (msWriteRq mst = true /\ noPortWriteB implRegions mr = true /\
       exists mr' rdy st',
         SemAction (subEnv child0Path env (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))))
           (@implRegionsLineWriteRq type implRegions (buildW b addr pkt size)) mr mr' rdy /\
         m' = (mr' ,, (st' ,, (mrq ,, (mrp ,, tt)))) /\
         (rdy = false -> st' = mst) /\
         (rdy = true -> if andb (negb b) (crossesB addr size)
                        then msWriteRq st' = true /\ msWriteRqV st' = stepOf true addr size pkt
                        else msIdle st' = true)).
  Proof.
    intros env mr mst mrq mrp m' v b addr size pkt Ev H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemWriteRqStep, implMemNoPortWriteRq in H.
    cbn [evalActionPropGen] in H.
    apply noPortWrite_wp in H; mem_cbn H.
    match type of H with (if ?c then _ else _) => destruct c eqn:Eg end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    assert (Hg : andb (msWriteRq mst) (noPortWriteB implRegions mr) = true) by exact Eg.
    apply andb_prop in Hg as [Hw Hnp].
    right; split; [exact Hw | split; [exact Hnp |]].
    apply evalActionPropGen_toAction in H.
    match type of H with context [evalExpr (ReadUnionData ?e ?i)] =>
      change (evalExpr (ReadUnionData e i)) with (msWriteRqV mst) in H end.
    rewrite Ev in H.
    match type of H with context [evalLetExpr (memBuildLineWriteRq ?x1 ?x2 ?x3 ?x4)] =>
      change (evalLetExpr (memBuildLineWriteRq x1 x2 x3 x4)) with (buildW b addr pkt size) in H end.
    mem_cbn H.
    apply evalActionPropGen_liftAction in H.
    cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [mr' [rdy [HS Hk]]]; clear H.
    exists mr', rdy.
    cbv beta in Hk.
    change (evalExpr (Var type Bool rdy)) with rdy in Hk.
    destruct rdy.
    - match type of Hk with (if ?c then _ else _) =>
        replace c with (andb (negb b) (crossesB addr size)) in Hk by reflexivity end.
      destruct (andb (negb b) (crossesB addr size)) eqn:Ec.
      + mem_cbn Hk; destruct Hk as [Hk _].
        eexists; split; [exact HS | split; [symmetry; exact Hk |]].
        split; [intros Hf; discriminate Hf | intros _].
        split; [reflexivity | rewrite msWriteRqV_build; reflexivity].
      + mem_cbn Hk; destruct Hk as [Hk _].
        eexists; split; [exact HS | split; [symmetry; exact Hk |]].
        split; [intros Hf; discriminate Hf | intros _; reflexivity].
    - mem_cbn Hk; destruct Hk as [Hk _].
      exists mst; split; [exact HS | split; [symmetry; exact Hk |]].
      split; [intros _; reflexivity | intros Hf; discriminate Hf].
  Qed.

  (* --- The regions' routed line requests --- *)

  Lemma evalOrBinary_bool : forall a b : bool, @evalOrBinary Bool a b = orb a b.
  Proof. intros [|] [|]; reflexivity. Qed.

  Lemma isMapped_fold :
    forall L l acc,
      fold_left (@evalOrBinary Bool) (map (fun r => evalExpr (isRegionAddr r (Var type Addr L))) l) acc =
      orb acc (match lineKind l L with Some _ => true | None => false end).
  Proof.
    intros L l; induction l as [| r rs IH]; intros acc; cbn [map fold_left lineKind].
    - destruct acc; reflexivity.
    - rewrite IH.
      change (evalExpr (isRegionAddr r (Var type Addr L))) with (isRegionAddrB r L).
      destruct (isRegionAddrB r L), acc; reflexivity.
  Qed.

  Lemma isMapped_eval :
    forall l L, evalExpr (isMappedAddr l (Var type Addr L)) = match lineKind l L with Some _ => true | None => false end.
  Proof.
    intros l L; unfold isMappedAddr; cbn [evalExpr]; rewrite map_map.
    exact (isMapped_fold L l false).
  Qed.

  Lemma lineKind_nth_some :
    forall L l j r, nth_error l j = Some r -> isRegionAddrB r L = true ->
      match lineKind l L with Some _ => true | None => false end = true.
  Proof.
    intros L l j r pf Hm.
    destruct (lineKind l L) eqn:E; [reflexivity |].
    exfalso; exact (lineKind_some_nth L l j r pf Hm E).
  Qed.

  (* A write of a line held by no region is dropped *)
  Lemma regionsWrite_none :
    forall env (mr mr' : TS RT) rdy (w : type LineWriteRq),
      lineKind implRegions w.(Fst) = None ->
      SemAction env (@implRegionsLineWriteRq type implRegions w) mr mr' rdy -> mr' = mr /\ rdy = true.
  Proof.
    intros env mr mr' rdy w Hk H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsLineWriteRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    pose proof (proj1 (route_none_or implMemRegionTree Bool (fun r => @implMemRegionLineWriteRq r type w) (w.(Fst))
                         implRegions [] _ mr _ Hk) H) as H'.
    cbv beta in H'; destruct H' as [E1 E2]; split; [symmetry; exact E1 |].
    rewrite <- E2; cbn [evalExpr map fold_left].
    rewrite isMapped_eval.
    match goal with |- context [lineKind implRegions ?a] =>
      change (lineKind implRegions a) with (lineKind implRegions (w.(Fst))) end.
    rewrite Hk; reflexivity.
  Qed.

  (* A write of a line held by the region at `j` is that region's write *)
  Lemma regionsWrite_at :
    forall env (mr mr' : TS RT) rdy (w : type LineWriteRq) j r (pf : nth_error implRegions j = Some r),
      isRegionAddrB r w.(Fst) = true -> lineUnique implRegions w.(Fst) ->
      SemAction env (@implRegionsLineWriteRq type implRegions w) mr mr' rdy ->
      exists y', SemAction (envRegionAt implMemRegionTree j implRegions r pf env mr) (@implMemRegionLineWriteRq r type w)
                   (regionStateAt implMemRegionTree j implRegions r pf mr) y' rdy /\
                 mr' = updRegionStateAt implMemRegionTree j implRegions r pf mr y'.
  Proof.
    intros env mr mr' rdy w j r pf Hm Hu H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsLineWriteRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    pose proof (proj1 (route_at_or implMemRegionTree Bool (fun r => @implMemRegionLineWriteRq r type w) (w.(Fst))
                         implRegions j r pf [] _ mr _ Hm Hu (Forall_nil _)) H) as H'.
    destruct (evalActionPropGen_to_SemAction _ _ _ H') as [y' [v0 [HS [E1 E2]]]].
    exists y'; split; [| symmetry; exact E1].
    replace rdy with v0; [exact HS |].
    rewrite <- E2; cbn [evalExpr map fold_left].
    rewrite isMapped_eval.
    match goal with |- context [lineKind implRegions ?a] =>
      change (lineKind implRegions a) with (lineKind implRegions (w.(Fst))) end.
    pose proof (lineKind_nth_some _ _ _ _ pf Hm) as Hs.
    destruct (lineKind implRegions (Fst w)); [| discriminate Hs].
    destruct v0; reflexivity.
  Qed.

  (* A read of a line held by no region answers zeros at once *)
  Lemma regionsRead_none :
    forall env (mr mr' : TS RT) res (L : type Addr) mask,
      lineKind implRegions L = None ->
      SemAction env (@implRegionsLineReadRq type implRegions L mask) mr mr' res ->
      mr' = mr /\ res = (true ,, ((getDefault LineReadRp ,, (true ,, tt)) ,, tt)).
  Proof.
    intros env mr mr' res L mask Hk H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsLineReadRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    pose proof (proj1 (route_none_or implMemRegionTree LineReadRqRes (fun r => @implMemRegionLineReadRq r type L mask) L
                         implRegions [] _ mr _ Hk) H) as H'.
    cbv beta in H'; cbn [evalActionPropGen] in H'; destruct H' as [E1 E2]; split; [symmetry; exact E1 |].
    rewrite <- E2; cbn [evalExpr].
    rewrite isMapped_eval, Hk; reflexivity.
  Qed.

  (* A read of a line held by the region at `j` is that region's read *)
  Lemma regionsRead_at :
    forall env (mr mr' : TS RT) res (L : type Addr) mask j r (pf : nth_error implRegions j = Some r),
      isRegionAddrB r L = true -> lineUnique implRegions L ->
      SemAction env (@implRegionsLineReadRq type implRegions L mask) mr mr' res ->
      exists y', SemAction (envRegionAt implMemRegionTree j implRegions r pf env mr) (@implMemRegionLineReadRq r type L mask)
                   (regionStateAt implMemRegionTree j implRegions r pf mr) y' res /\
                 mr' = updRegionStateAt implMemRegionTree j implRegions r pf mr y'.
  Proof.
    intros env mr mr' res L mask j r pf Hm Hu H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implRegionsLineReadRq, genRouteRegionAction in H; cbn [evalActionPropGen] in H.
    pose proof (proj1 (route_at_or implMemRegionTree LineReadRqRes (fun r => @implMemRegionLineReadRq r type L mask) L
                         implRegions j r pf [] _ mr _ Hm Hu (Forall_nil _)) H) as H'.
    destruct (evalActionPropGen_to_SemAction _ _ _ H') as [y' [v0 [HS H2]]].
    cbv beta in H2; cbn [evalActionPropGen] in H2; destruct H2 as [E1 E2].
    exists y'; split; [| symmetry; exact E1].
    replace res with v0; [exact HS |].
    rewrite <- E2; cbn [evalExpr].
    rewrite isMapped_eval.
    pose proof (lineKind_nth_some _ _ _ _ pf Hm) as Hs.
    destruct (lineKind implRegions L); [reflexivity | discriminate Hs].
  Qed.

  (* The line and the byte mask of line `b` of an access *)
  Definition rdLineOf (b : bool) (addr : type Addr) : type Addr :=
    evalExpr (ITE (Var type Bool b) (memNextLineAddr (Var type Addr addr)) (memLineAddr (Var type Addr addr))).
  Definition rdMaskOf (b : bool) (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) : type (Array LineBytes Bool) :=
    evalLetExpr (memDataMask (Var type Bool b) (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)).

  Lemma rdLineOf_eq : forall b addr, rdLineOf b addr = lineOf b addr.
  Proof. intros [|] addr; reflexivity. Qed.

  (* The spec writes the mask with a constant line bit *)
  Lemma rdMaskOf_eq :
    forall (b : bool) addr size,
      rdMaskOf b addr size =
      evalLetExpr (memDataMask (Const type Bool b) (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)).
  Proof. intros b addr size; reflexivity. Qed.

  Lemma readRqStep_char :
    forall env mr mst mrq mrp m' v b addr size pkt,
      msReadRqV mst = stepOf b addr size pkt ->
      SemAction env (@implMemReadRqStep implRegions type) (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) \/
      (msReadRq mst = true /\ optValid mrp = false /\
       exists mr' (res : type LineReadRqRes) st' mrp',
         SemAction (subEnv child0Path env (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))))
           (@implRegionsLineReadRq type implRegions (rdLineOf b addr) (rdMaskOf b addr size)) mr mr' res /\
         m' = (mr' ,, (st' ,, (mrq ,, (mrp' ,, tt)))) /\
         (res.(Fst) = false -> st' = mst /\ mrp' = mrp) /\
         (res.(Fst) = true -> msReadRqSent st' = true /\
                              msReadRqSentV st' = (crossesB addr size ,, (stepOf b addr size pkt ,, tt)) /\
                              mrp' = (if optValid res.(Snd).(Fst) then res.(Snd).(Fst) else mrp))).
  Proof.
    intros env mr mst mrq mrp m' v b addr size pkt Ev H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemReadRqStep in H.
    cbn [evalActionPropGen] in H.
    match type of H with (if ?c then _ else _) => destruct c eqn:Eg end.
    2: { left; destruct H as [H _]; symmetry; exact H. }
    assert (Hg : andb (msReadRq mst) (negb (optValid mrp)) = true) by exact Eg.
    apply andb_prop in Hg as [Hr Hv]; apply negb_true_iff in Hv.
    right; split; [exact Hr | split; [exact Hv |]].
    apply evalActionPropGen_toAction in H.
    match type of H with context [evalExpr (ReadUnionData ?e ?i)] =>
      change (evalExpr (ReadUnionData e i)) with (msReadRqV mst) in H end.
    rewrite Ev in H.
    match type of H with context [evalLetExpr (memDataMask ?x1 ?x2 ?x3)] =>
      change (evalLetExpr (memDataMask x1 x2 x3)) with (rdMaskOf b addr size) in H end.
    cbn [evalActionPropGen] in H.
    match type of H with context [@implRegionsLineReadRq type implRegions ?L (rdMaskOf b addr size)] =>
      change L with (rdLineOf b addr) in H end.
    apply evalActionPropGen_liftAction in H.
    cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [mr' [res [HS Hk]]]; clear H.
    cbv beta in Hk.
    exists mr', res.
    destruct res as [rdy [rp []]].
    destruct rdy.
    - destruct rp as [rpd [rpv []]].
      destruct rpv.
      + match type of Hk with (if ?c then _ else _) => change c with true in Hk end. cbv iota in Hk.
        match type of Hk with (if ?c then _ else _) => change c with true in Hk end. cbv iota in Hk.
        match type of Hk with context [castStateRegInv _ ?v] =>
          lazymatch v with evalExpr (BuildUnion _ _) => remember v as stv eqn:Estv end end.
        timeout 10 (mem_cbn Hk).
        timeout 5 (eexists; eexists; split; [exact HS |]).
        timeout 5 (split; [symmetry; exact (proj1 Hk) |]).
        timeout 5 (split; [intros Hf; discriminate Hf | intros _]).
        timeout 5 (split; [transitivity (msReadRqSent stv); [reflexivity | rewrite Estv; apply msReadRqSent_build] |]).
        timeout 5 (split; [transitivity (msReadRqSentV stv); [reflexivity | rewrite Estv, msReadRqSentV_build] |]).
        { unfold crossesB.
          timeout 5 (match goal with |- context [evalExpr (memCrossesLine ?a ?z)] =>
                       change (evalExpr (memCrossesLine a z)) with
                         (evalExpr (memCrossesLine (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size))) end).
          timeout 5 reflexivity. }
        timeout 5 reflexivity.
      + match type of Hk with (if ?c then _ else _) => change c with true in Hk end. cbv iota in Hk.
        match type of Hk with (if ?c then _ else _) => change c with false in Hk end. cbv iota in Hk.
        match type of Hk with context [castStateRegInv _ ?v] =>
          lazymatch v with evalExpr (BuildUnion _ _) => remember v as stv eqn:Estv end end.
        timeout 10 (mem_cbn Hk).
        timeout 5 (eexists; eexists; split; [exact HS |]).
        timeout 5 (split; [symmetry; exact (proj1 Hk) |]).
        timeout 5 (split; [intros Hf; discriminate Hf | intros _]).
        timeout 5 (split; [transitivity (msReadRqSent stv); [reflexivity | rewrite Estv; apply msReadRqSent_build] |]).
        timeout 5 (split; [transitivity (msReadRqSentV stv); [reflexivity | rewrite Estv, msReadRqSentV_build] |]).
        { unfold crossesB.
          timeout 5 (match goal with |- context [evalExpr (memCrossesLine ?a ?z)] =>
                       change (evalExpr (memCrossesLine a z)) with
                         (evalExpr (memCrossesLine (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size))) end).
          timeout 5 reflexivity. }
        timeout 5 reflexivity.
    - mem_cbn Hk; destruct Hk as [Hk _].
      exists mst, mrp; split; [exact HS | split; [symmetry; exact Hk |]].
      split; [intros _; split; reflexivity | intros Hf; discriminate Hf].
  Qed.
End RqStepChar.
