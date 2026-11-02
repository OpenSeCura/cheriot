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
From Cheriot Require Import SpecDefines SpecDevice SpecFetchDeferred Spec Clint Plic Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefSpecRead RefSpecFetch RefRevTable RefReplay RefExecLive RefLoadCommit RefWriteRqPorts.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the commit of a store line to an ExternalMem region (`writeRqPorts`, accepted),
 * spec side: `specStep` of a store entry at the head of the chain (`specStep_store`: the first
 * line is written, a crossing store records its second line). *)

Local Strategy expand [defDst defAddr defDm defMd defNextPcc geAluOut geAluIn evalAluOut evalDecode readPcc writePcc
                       storeCmdOf stAddrOf stValOf stSizeOf crossesB lineOf].

Lemma bool_cases : forall b : bool, b = true \/ b = false.
Proof. intros [|]; [left | right]; reflexivity. Qed.

(* `dispatchMemFence` on a store: a memory action that is a store *)
Lemma dispatchMemFence_store :
  forall d a op, opIsStore op = true ->
    evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `? "Mem") = true /\
    evalExpr ((Var type MemAction (evalExpr ((Var type MemFenceAction (evalLetExpr (dispatchMemFence d a op))) `! "Mem")))
                `? "Store") = true.
Proof.
  intros d a op H.
  unfold opIsStore, opMemPayload, opIsMem in *; cbv zeta in *.
  apply andb_prop in H as [Hm Hs].
  unfold dispatchMemFence; cbn [evalLetExpr]; rewrite Hm; cbv beta iota.
  split; [reflexivity |].
  readback.
  match goal with |- context [evalExpr (ReadUnionTag (Var ?ty ?k ?x) ?j)] =>
    assert (Hs' : evalExpr (ReadUnionTag (Var ty k x) j) = true) by exact Hs;
    rewrite Hs'; cbv iota
  end.
  reflexivity.
Qed.

Section StoreSpec.
  Variable pcAddrInit : Z.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Local Abbreviation CT := (specCoreTree pcAddrInit specRegions).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specClintStateA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation specPlicStateA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation mkCoreA := (mkCore pcAddrInit specRegions).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).

  Lemma lineUnique_specS : forall L, lineUnique specRegions L.
  Proof. intros L; apply lineUnique_disjoint, Is_true_eq_true, Hdisj. Qed.

  (* The packet, the spec memory after the first line, and `secondLine` after a store `st` *)
  Definition stPkt (st : type StoreCmd) : type CapPacket := disassembleW (stAddrOf st) (stValOf st) (stSizeOf st).
  Definition stWriteM (m : TS (specMemTree specRegions)) (st : type StoreCmd) : TS (specMemTree specRegions) :=
    specWriteLine specRegions (lineOf false (stAddrOf st)) (buildW false (stAddrOf st) (stPkt st) (stSizeOf st)) m.
  Definition stCommitSl (st : type StoreCmd) (sl : type (Option SecondLine)) : type (Option SecondLine) :=
    if crossesB (stAddrOf st) (stSizeOf st) then secondStoreOf (stAddrOf st) (stPkt st) (stSizeOf st) else sl.

  (* The deferred part of a store entry: the first line is written; a crossing store records its
   * second line *)
  Lemma deferred_store_wp :
    forall (envC : Env CT) rfC m sl (d : type (Bit RegIdxSzReal)) (a : type Addr) (dm : type (Option MemFenceUnion))
           (md : type (Option MulDivUnion)) st (Q : TS CT -> Prop),
      optValid dm = true -> opIsStore (optData dm) = true ->
      st = storeCmdOf (d ,, (a ,, (optData dm ,, tt))) ->
      lineKind specRegions (lineOf false (stAddrOf st)) = Some true ->
      (crossesB (stAddrOf st) (stSizeOf st) = true ->
         Q (mkCoreA rfC (stWriteM m st) (secondStoreOf (stAddrOf st) (stPkt st) (stSizeOf st)))) ->
      (crossesB (stAddrOf st) (stSizeOf st) = false -> Q (mkCoreA rfC (stWriteM m st) sl)) ->
      evalActionPropGen envC (@specExecuteDeferred pcAddrInit config specRegions type d a dm md)
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl d a dm md st Q Hv Hst Est Hk HQt HQf.
    destruct (dispatchMemFence_store d a (optData dm) Hst) as [Hmem Hsto].
    unfold specExecuteDeferred.
    apply ev_ifElse_true; [exact Hv |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_ifElse_true; [exact Hmem |].
    apply ev_letExp; cbv beta.
    apply ev_ifElse_true; [exact Hsto |].
    apply ev_letExpGen; intros stv Estv.
    assert (E : stv = st) by (rewrite Estv, Est; reflexivity).
    clear Estv; subst stv.
    do 3 (apply ev_letExp; cbv beta).
    apply core_memAct_wp.
    apply (specMemWrite_wp specRegions); [exact Hk | apply lineUnique_specS |].
    intros v; cbv beta.
    destruct (bool_cases (crossesB (stAddrOf st) (stSizeOf st))) as [Ecr | Ecr].
    - apply ev_ifElse_true; [exact Ecr |].
      apply ev_letL; cbv beta.
      apply ev_letL; cbv beta.
      apply ev_letExp; cbv beta.
      apply writeSecondLine_wp; intros r; cbv beta.
      repeat (apply ev_return; cbv beta).
      exact (HQt Ecr).
    - apply ev_ifElse_false; [exact Ecr |].
      repeat (apply ev_return; cbv beta).
      exact (HQf Ecr).
  Qed.

  (* `specStep` for a store entry at the head of the chain *)
  Lemma specStep_store :
    forall rf0 rf1 m sl e q,
      GInstStep pcAddrInit rf0 rf1 e ->
      entryReq e = Some q -> opIsStore (mrOp q) = true ->
      SpecNoWait specRegions m -> optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      lineKind specRegions (lineOf false (stAddrOf (storeCmdOf q))) = Some true ->
      exists m', TraceFrameS specRegions m m' /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSysA rf0 m sl) (mkSysA rf1 (stWriteM m' (storeCmdOf q)) (stCommitSl (storeCmdOf q) sl)) Zmod.zero.
  Proof.
    intros rf0 rf1 m sl e q [Hvc [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]]] Hq Hst Hnw Hsl Hfa Hmt Hme Hk.
    destruct (entryReq_some e q Hq) as [Hv Eq].
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSysA (cnwbApply pcAddrInit None rf0) m sl)
                    (fun s2' _ => exists m', TraceFrameS specRegions m m' /\
                       s2'.(Fst) = mkCoreA rf1 (stWriteM m' (storeCmdOf q)) (stCommitSl (storeCmdOf q) sl))).
    { apply specStep_wp with (Hdisj := Hdisj) (e := e) (rfMid := rfMid) (execOut := execOut)
        (Q := fun sc => exists m', TraceFrameS specRegions m m' /\
                 sc = mkCoreA rf1 (stWriteM m' (storeCmdOf q)) (stCommitSl (storeCmdOf q) sl));
        try assumption.
      - intros d v Hc; discriminate Hc.
      - intros m1 envC aluOut rfC HenvC Hm1 Ha Hrf.
        subst aluOut.
        assert (Erf : rfC = rf1).
        { rewrite Hrf, Hrf1, specMulDivWb_dmValid by (rewrite Hdm; exact Hv).
          rewrite defNextPcc_eq; reflexivity. }
        apply (deferred_store_wp envC rfC m1 sl _ _ _ _ (storeCmdOf q)).
        + rewrite defDm_eq, Hdm; exact Hv.
        + rewrite defDm_eq, Hdm; rewrite Eq in Hst; exact Hst.
        + rewrite defDst_eq, defAddr_eq, defDm_eq, Hdm, Eq; reflexivity.
        + exact Hk.
        + intros Ecr; exists m1; split; [exact Hm1 |].
          unfold stCommitSl; rewrite Ecr, Erf; reflexivity.
        + intros Ecr; exists m1; split; [exact Hm1 |].
          unfold stCommitSl; rewrite Ecr, Erf; reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [m' [Hm' E]]]]].
    exists m'; split; [exact Hm' |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.

  (* --- `specSecondLine` for the second line of a crossing store --- *)

  (* The record `secondStoreOf` keeps of a write request *)
  Definition slOfRq (rq : type LineWriteRq) : type SecondLineStore :=
    (rq.(Fst) ,, (rq.(Snd).(Fst) ,, (rq.(Snd).(Snd).(Fst) ,, (rq.(Snd).(Snd).(Snd).(Fst) ,,
     (rq.(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt))))).

  Lemma secondLine_store_wp :
    forall (envC : Env CT) rf m addr pkt size (Q : TS CT -> Prop),
      lineKind specRegions (lineOf true addr) = Some true ->
      Q (mkCoreA rf (specWriteLine specRegions (lineOf true addr) (buildW true addr pkt size) m)
           (getDefault (Option SecondLine))) ->
      evalActionPropGen envC (@specSecondLineStep pcAddrInit config specRegions type)
        (mkCoreA rf m (secondStoreOf addr pkt size)) (fun sc' _ => Q sc').
  Proof.
    intros envC rf m addr pkt size Q Hk HQ.
    unfold specSecondLineStep.
    apply ev_letAction; apply (readSecondLine_wp pcAddrInit pre post revBase revPfB revPfA); cbv beta.
    apply ev_ifElse_true; [reflexivity |].
    apply ev_letExpGen; intros sv Esv.
    assert (Ed : sv = evalExpr (UNION (SecondLineType, "Store" ::=
                                 Var type SecondLineStore (slOfRq (buildW true addr pkt size)))))
      by (rewrite Esv; reflexivity).
    clear Esv; subst sv.
    apply ev_ifElse_true; [reflexivity |].
    apply ev_letExpGen; intros stv Estv.
    assert (Es : stv = slOfRq (buildW true addr pkt size)).
    { rewrite Estv.
      exact (evalExpr_ReadUnionData_BuildUnion SecondLineType (@Build_FinType 2 1 I)
               (Var type SecondLineStore (slOfRq (buildW true addr pkt size))) eq_refl). }
    clear Estv; subst stv.
    apply ev_letExpGen; intros rqv Erqv.
    assert (Er : rqv = buildW true addr pkt size).
    { rewrite Erqv; unfold slOfRq.
      destruct (buildW true addr pkt size) as [x1 [x2 [x3 [x4 [x5 []]]]]]; reflexivity. }
    clear Erqv; subst rqv.
    apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
    apply specMemLineWrite_wp; rewrite buildW_addr; [exact Hk | apply lineUnique_specS |].
    intros v; cbv beta.
    apply writeSecondLine_wp; intros r; cbv beta.
    apply ev_return.
    exact HQ.
  Qed.

  Lemma specSecondLine_store :
    forall rf m addr pkt size,
      lineKind specRegions (lineOf true addr) = Some true ->
      SemAction envS (@specSecondLine pcAddrInit config specRegions type)
        (mkSysA rf m (secondStoreOf addr pkt size))
        (mkSysA rf (specWriteLine specRegions (lineOf true addr) (buildW true addr pkt size) m)
           (getDefault (Option SecondLine)))
        Zmod.zero.
  Proof.
    intros rf m addr pkt size Hk.
    assert (Hev : evalActionPropGen envS (@specSecondLine pcAddrInit config specRegions type)
                    (mkSysA rf m (secondStoreOf addr pkt size))
                    (fun s2' _ => s2'.(Fst) = mkCoreA rf (specWriteLine specRegions (lineOf true addr)
                                                            (buildW true addr pkt size) m)
                                                (getDefault (Option SecondLine)))).
    { unfold specSecondLine.
      apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
      eapply evalActionPropGen_mono;
        [| apply (secondLine_store_wp _ rf m addr pkt size
                    (fun sc => sc = mkCoreA rf (specWriteLine specRegions (lineOf true addr)
                                                 (buildW true addr pkt size) m)
                                     (getDefault (Option SecondLine))))].
      - intros sc r H; exact H.
      - exact Hk.
      - reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs E]]].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.
End StoreSpec.
