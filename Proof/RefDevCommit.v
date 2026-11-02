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
From Cheriot.Proof Require Import RefStoreCommit RefRevokerStep RefDevSim RefDevWrite RefRqStepChar.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the commit of a store line to a CustomMem or unmapped line (`writeRqStep`), spec
 * side: `specStep` of the store entry, or `specSecondLine`, with the device write (or the dropped
 * write) of `devWrite_mem` in place of an ExternalMem write. *)

Local Strategy expand [defDst defAddr defDm defMd defNextPcc geAluOut geAluIn evalAluOut evalDecode readPcc writePcc
                       storeCmdOf stAddrOf stValOf stSizeOf crossesB lineOf].

Section StoreSpecDev.
  Variable pcAddrInit : Z.
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
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.
  Hypothesis HrevTab : Is_true (revTableInExternalMem config specRegions).

  Local Abbreviation CT := (specCoreTree pcAddrInit specRegions).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specClintStateA := (specClintState pre post revBase revPfB revPfA clintS).
  Local Abbreviation specPlicStateA := (specPlicState pre post revBase revPfB revPfA plicS).
  Local Abbreviation mkCoreA := (mkCore pcAddrInit specRegions).
  Local Abbreviation mkSysA := (mkSys pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation MS := (TS (specMemTree specRegions)).
  Local Abbreviation MI := (TS (implRegionsTree implRegions)).
  Local Abbreviation MEMREL := (MemRel pre post revBase revPfB revPfA clintS clint plicS plic RevEq).
  Local Abbreviation DWOK := (DevWriteOK pre post revBase revPfB revPfA clintS clint plicS plic).
  Local Abbreviation SWP := (SpecWP pre post revBase revPfB revPfA).

  Lemma SpecEnvOK_custom : forall env, SpecEnvOK initLine specRegions fwcs env -> EnvCustomTrue specRegions env.
  Proof.
    intros env H; apply (EnvCovers_custom initLine specRegions fwcs).
    intros s [lp pf'] v Hall; apply H; intros pf; exact (Hall pf v).
  Qed.

  Lemma MemRel_traceFrame : forall ms ms' mi, TraceFrameS specRegions ms ms' -> MEMREL ms mi -> MEMREL ms' mi.
  Proof.
    intros ms ms' mi Htf Hm.
    unfold MemRel, specClintState, specPlicState, specRevState in *.
    rewrite !(regionStateAt_traceFrame specRegions _ _ _ _ _ Htf) by exact I.
    destruct Hm as [Hpre Hrest]; split; [| exact Hrest].
    exact (MemRelPre_traceFrame _ _ _ _ _ _ _ _ _ _ Htf Hpre).
  Qed.

  (* The spec's write of the store's first line, through `SpecWP` *)
  Lemma specMemWrite_swp :
    forall env ms addr stVal size ms',
      SWP env ms (buildW false addr (disassembleW addr stVal size) size) ms' ->
      forall P, (forall v, P ms' v) -> evalActionPropGen env (@specMemWrite type specRegions addr stVal size) ms P.
  Proof.
    intros env ms addr stVal size ms' Hw P HP.
    unfold specMemWrite.
    apply ev_letL; cbv beta.
    apply ev_letL; cbv beta.
    change (evalActionPropGen env (@specMemLineWrite type specRegions (buildW false addr (disassembleW addr stVal size) size)) ms P).
    exact (Hw P HP).
  Qed.

  (* `deferred_store_wp` with the memory write given by a WP fact *)
  Lemma deferred_store_dev_wp :
    forall (envC : Env CT) rfC m sl (d : type (Bit RegIdxSzReal)) (a : type Addr) (dm : type (Option MemFenceUnion))
           (md : type (Option MulDivUnion)) st (Q : TS CT -> Prop) ms',
      optValid dm = true -> opIsStore (optData dm) = true ->
      st = storeCmdOf (d ,, (a ,, (optData dm ,, tt))) ->
      SWP (subEnv (SpecFetchDeferred.np_mem pcAddrInit specRegions) envC (mkCoreA rfC m sl)) m
        (buildW false (stAddrOf st) (stPkt st) (stSizeOf st)) ms' ->
      (crossesB (stAddrOf st) (stSizeOf st) = true ->
         Q (mkCoreA rfC ms' (secondStoreOf (stAddrOf st) (stPkt st) (stSizeOf st)))) ->
      (crossesB (stAddrOf st) (stSizeOf st) = false -> Q (mkCoreA rfC ms' sl)) ->
      evalActionPropGen envC (@specExecuteDeferred pcAddrInit config specRegions type d a dm md)
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl d a dm md st Q ms' Hv Hst Est Hw HQt HQf.
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
    apply (specMemWrite_swp _ m (stAddrOf st) (stValOf st) (stSizeOf st) ms' Hw).
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

  Local Abbreviation devWrite := (devWrite_mem pre post revBase revPfB revPfA clintS clint plicS plic Hdisj HclintIdx HplicIdx).

  (* `specStep` for a store entry whose first line is a CustomMem or unmapped line *)
  Lemma specStep_store_dev :
    forall rf0 rf1 m sl e q envI (mi mi' : MI) rdy,
      GInstStep pcAddrInit rf0 rf1 e ->
      entryReq e = Some q -> opIsStore (mrOp q) = true ->
      SpecNoWait specRegions m -> optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      MEMREL m mi -> lineKind implRegions (lineOf false (stAddrOf (storeCmdOf q))) <> Some true ->
      SemAction envI (@implRegionsLineWriteRq type implRegions
                        (buildW false (stAddrOf (storeCmdOf q)) (stPkt (storeCmdOf q)) (stSizeOf (storeCmdOf q)))) mi mi' rdy ->
      rdy = true /\ exists m1 ms', TraceFrameS specRegions m m1 /\ DWOK m1 ms' mi mi' /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSysA rf0 m sl) (mkSysA rf1 ms' (stCommitSl (storeCmdOf q) sl)) Zmod.zero.
  Proof.
    intros rf0 rf1 m sl e q envI mi mi' rdy [Hvc [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]]] Hq Hst Hnw Hsl Hfa Hmt Hme
      Hrel Hk H.
    destruct (entryReq_some e q Hq) as [Hv Eq].
    assert (Hk' : lineKind implRegions (buildW false (stAddrOf (storeCmdOf q)) (stPkt (storeCmdOf q)) (stSizeOf (storeCmdOf q))).(Fst)
                  <> Some true) by (rewrite buildW_addr; exact Hk).
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSysA (cnwbApply pcAddrInit None rf0) m sl)
                    (fun s2' _ => rdy = true /\ exists m1 ms', TraceFrameS specRegions m m1 /\ DWOK m1 ms' mi mi' /\
                       s2'.(Fst) = mkCoreA rf1 ms' (stCommitSl (storeCmdOf q) sl))).
    { apply specStep_wp with (Hdisj := Hdisj) (e := e) (rfMid := rfMid) (execOut := execOut)
        (Q := fun sc => rdy = true /\ exists m1 ms', TraceFrameS specRegions m m1 /\ DWOK m1 ms' mi mi' /\
                 sc = mkCoreA rf1 ms' (stCommitSl (storeCmdOf q) sl));
        try assumption.
      - intros d v Hc; discriminate Hc.
      - intros m1 envC aluOut rfC HenvC Hm1 Ha Hrf.
        subst aluOut.
        assert (Erf : rfC = rf1).
        { rewrite Hrf, Hrf1, specMulDivWb_dmValid by (rewrite Hdm; exact Hv).
          rewrite defNextPcc_eq; reflexivity. }
        destruct (devWrite envI (subEnv (SpecFetchDeferred.np_mem pcAddrInit specRegions) envC (mkCoreA rfC m1 sl))
                    m1 mi mi' _ rdy (MemRel_traceFrame m m1 mi Hm1 Hrel) Hk' (SpecEnvOK_custom _ (HenvC _)) H)
          as [Erdy [ms' [Hwp Hok]]].
        apply (deferred_store_dev_wp envC rfC m1 sl _ _ _ _ (storeCmdOf q) _ ms').
        + rewrite defDm_eq, Hdm; exact Hv.
        + rewrite defDm_eq, Hdm; rewrite Eq in Hst; exact Hst.
        + rewrite defDst_eq, defAddr_eq, defDm_eq, Hdm, Eq; reflexivity.
        + exact Hwp.
        + intros Ecr; split; [exact Erdy |]; exists m1, ms'; split; [exact Hm1 | split; [exact Hok |]].
          unfold stCommitSl; rewrite Ecr, Erf; reflexivity.
        + intros Ecr; split; [exact Erdy |]; exists m1, ms'; split; [exact Hm1 | split; [exact Hok |]].
          unfold stCommitSl; rewrite Ecr, Erf; reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [Erdy [m1 [ms' [Hm1 [Hok E]]]]]]]].
    split; [exact Erdy |].
    exists m1, ms'; split; [exact Hm1 | split; [exact Hok |]].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.

  (* `specSecondLine` for the second line of a crossing store, a CustomMem or unmapped line *)
  Lemma specSecondLine_store_dev :
    forall rf m addr pkt size envI (mi mi' : MI) rdy,
      MEMREL m mi -> lineKind implRegions (lineOf true addr) <> Some true ->
      SemAction envI (@implRegionsLineWriteRq type implRegions (buildW true addr pkt size)) mi mi' rdy ->
      rdy = true /\ exists ms', DWOK m ms' mi mi' /\
        SemAction envS (@specSecondLine pcAddrInit config specRegions type)
          (mkSysA rf m (secondStoreOf addr pkt size)) (mkSysA rf ms' (getDefault (Option SecondLine))) Zmod.zero.
  Proof.
    intros rf m addr pkt size envI mi mi' rdy Hrel Hk H.
    assert (Hk' : lineKind implRegions (buildW true addr pkt size).(Fst) <> Some true) by (rewrite buildW_addr; exact Hk).
    assert (Hev : evalActionPropGen envS (@specSecondLine pcAddrInit config specRegions type)
                    (mkSysA rf m (secondStoreOf addr pkt size))
                    (fun s2' _ => rdy = true /\ exists ms', DWOK m ms' mi mi' /\
                       s2'.(Fst) = mkCoreA rf ms' (getDefault (Option SecondLine)))).
    { unfold specSecondLine.
      apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
      match goal with |- evalActionPropGen ?E _ _ _ =>
        assert (HenvC : forall sc, SpecEnvOK initLine specRegions fwcs (subEnv (SpecFetchDeferred.np_mem pcAddrInit specRegions) E sc))
      end.
      { eapply coreEnvOK. }
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
      match goal with |- evalActionPropGen ?E _ _ _ =>
        destruct (devWrite envI E m mi mi' _ rdy Hrel Hk' (SpecEnvOK_custom _ (HenvC _)) H) as [Erdy [ms' [Hwp Hok]]] end.
      apply Hwp; intros v; cbv beta.
      apply writeSecondLine_wp; intros r; cbv beta.
      apply ev_return.
      split; [exact Erdy |]; exists ms'; split; [exact Hok | reflexivity]. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [Erdy [ms' [Hok E]]]]]].
    split; [exact Erdy |]; exists ms'; split; [exact Hok |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.

  (* --- Loads --- *)

  Local Abbreviation SRP := (SpecRP pre post revBase revPfB revPfA).
  Local Abbreviation CEOK := (CoreEnvOK pcAddrInit pre post revBase revPfB revPfA initLine fwcs).
  Local Abbreviation specLoadWbA := (specLoadWb config pre post revBase revPfB revPfA initLine).

  Lemma deferred_load_dev_wp :
    forall (envC : Env CT) rfC m sl (d : type (Bit RegIdxSzReal)) (a : type Addr) (dm : type (Option MemFenceUnion))
           (md : type (Option MulDivUnion)) ld (Q : TS CT -> Prop) ms' rpv,
      CEOK envC ->
      optValid dm = true -> opIsLoad (optData dm) = true ->
      ld = loadCmdOf (d ,, (a ,, (optData dm ,, tt))) ->
      SRP (subEnv (SpecFetchDeferred.np_mem pcAddrInit specRegions) envC (mkCoreA rfC m sl)) m
        (rdLineOf false (ldAddr ld)) (rdMaskOf false (ldAddr ld) (plSize (ldPending ld))) ms' rpv ->
      (crossesB (ldAddr ld) (plSize (ldPending ld)) = true ->
         Q (mkCoreA rfC ms' (secondLoadOf ld (specPkt (ldAddr ld) rpv)))) ->
      (crossesB (ldAddr ld) (plSize (ldPending ld)) = false -> forall m2, ReadFrameS specRegions ms' m2 ->
         Q (mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA ms' (ldPending ld) (singleLoadVal ld rpv))) rfC) m2 sl)) ->
      evalActionPropGen envC (@specExecuteDeferred pcAddrInit config specRegions type d a dm md)
        (mkCoreA rfC m sl) (fun sc' _ => Q sc').
  Proof.
    intros envC rfC m sl d a dm md ld Q ms' rpv Henv Hv Hld Eld Hrp HQt HQf.
    destruct (dispatchMemFence_load d a (optData dm) Hld) as [Hmem Hst].
    unfold specExecuteDeferred.
    apply ev_ifElse_true; [exact Hv |].
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply ev_ifElse_true; [exact Hmem |].
    apply ev_letExp; cbv beta.
    apply ev_ifElse_false; [exact Hst |].
    apply ev_letExpGen; intros ldv Eldv.
    assert (E : ldv = ld) by (rewrite Eldv, Eld; reflexivity).
    clear Eldv; subst ldv.
    do 3 (apply ev_letExp; cbv beta).
    apply core_memAct_wp.
    unfold specMemReadFirstLine.
    apply ev_letExp; cbv beta.
    apply ev_letL; cbv beta.
    apply Hrp; cbv beta.
    apply ev_letL; cbv beta.
    destruct (bool_cases (crossesB (ldAddr ld) (plSize (ldPending ld)))) as [Ecr | Ecr].
    - apply ev_ifElse_true; [exact Ecr |].
      apply ev_letExp; cbv beta.
      apply writeSecondLine_wp; intros r; cbv beta.
      repeat (apply ev_return; cbv beta).
      exact (HQt Ecr).
    - apply ev_ifElse_false; [exact Ecr |].
      apply ev_letL; cbv beta.
      eapply evalActionPropGen_mono; [| eapply (specCompleteLoad_wp pcAddrInit config pre post revBase revPfB revPfA initLine fwcs Hdisj HrevTab
                                                envC rfC ms' sl _ _ (fun sc => Q sc) Henv)].
      + intros sc' r HQ'; cbv beta; repeat (apply ev_return; cbv beta); exact HQ'.
      + intros m2 Hm2; cbv beta; exact (HQf Ecr m2 Hm2).
  Qed.

  Local Abbreviation devRead := (devRead_mem pre post revBase revPfB revPfA clintS clint plicS plic Hdisj HclintIdx HplicIdx).

  (* The register file and `secondLine` after the first line `rpv` of load `ld` (`m2`: the spec
   * memory after the step) *)
  Definition ldDevRf (m2 : MS) (ld : type LoadCmd) (rpv : type LineReadRp) (rf1 : RfState pcAddrInit) : RfState pcAddrInit :=
    if crossesB (ldAddr ld) (plSize (ldPending ld)) then rf1
    else cnwbApply pcAddrInit (Some (specLoadWbA m2 (ldPending ld) (singleLoadVal ld rpv))) rf1.
  Definition ldDevSl (ld : type LoadCmd) (rpv : type LineReadRp) (sl : type (Option SecondLine)) : type (Option SecondLine) :=
    if crossesB (ldAddr ld) (plSize (ldPending ld)) then secondLoadOf ld (specPkt (ldAddr ld) rpv) else sl.

  (* `specStep` for a load entry whose first line is a CustomMem or unmapped line *)
  Lemma specStep_load_dev :
    forall rf0 rf1 m sl e q envI (mi mi' : MI) res,
      GInstStep pcAddrInit rf0 rf1 e ->
      entryReq e = Some q -> opIsLoad (mrOp q) = true ->
      SpecNoWait specRegions m -> optValid sl = false ->
      FetchAllowedInst initLine fwcs specRegions m (readPcc pcAddrInit rf0) (ge_fetchOut e) ->
      (clintSampled (specClintStateA m) = true -> ge_mtip e = true) ->
      (plicMeipOf (specPlicStateA m) = true -> ge_meip e = true) ->
      MEMREL m mi -> lineKind implRegions (lineOf false (ldAddr (loadCmdOf q))) <> Some true ->
      SemAction envI (@implRegionsLineReadRq type implRegions (rdLineOf false (ldAddr (loadCmdOf q)))
                        (rdMaskOf false (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q))))) mi mi' res ->
      exists rpv m1 ms' m2, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\
        TraceFrameS specRegions m m1 /\ DWOK m1 ms' mi mi' /\ ReadFrameS specRegions ms' m2 /\
        SemAction envS (@specStep pcAddrInit config specRegions clintS plicS type)
          (mkSysA rf0 m sl) (mkSysA (ldDevRf m2 (loadCmdOf q) rpv rf1) m2 (ldDevSl (loadCmdOf q) rpv sl)) Zmod.zero.
  Proof.
    intros rf0 rf1 m sl e q envI mi mi' res [Hvc [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]]] Hq Hld Hnw Hsl Hfa Hmt Hme
      Hrel Hk H.
    destruct (entryReq_some e q Hq) as [Hv Eq].
    assert (Hev : evalActionPropGen envS (@specStep pcAddrInit config specRegions clintS plicS type)
                    (mkSysA (cnwbApply pcAddrInit None rf0) m sl)
                    (fun s2' _ => exists rpv m1 ms' m2, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\
                       TraceFrameS specRegions m m1 /\ DWOK m1 ms' mi mi' /\ ReadFrameS specRegions ms' m2 /\
                       s2'.(Fst) = mkCoreA (ldDevRf m2 (loadCmdOf q) rpv rf1) m2 (ldDevSl (loadCmdOf q) rpv sl))).
    { apply specStep_wp with (Hdisj := Hdisj) (e := e) (rfMid := rfMid) (execOut := execOut)
        (Q := fun sc => exists rpv m1 ms' m2, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\
                 TraceFrameS specRegions m m1 /\ DWOK m1 ms' mi mi' /\ ReadFrameS specRegions ms' m2 /\
                 sc = mkCoreA (ldDevRf m2 (loadCmdOf q) rpv rf1) m2 (ldDevSl (loadCmdOf q) rpv sl));
        try assumption.
      - intros d v Hc; discriminate Hc.
      - intros m1 envC aluOut rfC HenvC Hm1 Ha Hrf.
        subst aluOut.
        assert (Erf : rfC = rf1).
        { rewrite Hrf, Hrf1, specMulDivWb_dmValid by (rewrite Hdm; exact Hv).
          rewrite defNextPcc_eq; reflexivity. }
        destruct (devRead envI (subEnv (SpecFetchDeferred.np_mem pcAddrInit specRegions) envC (mkCoreA rfC m1 sl))
                    m1 mi mi' (rdLineOf false (ldAddr (loadCmdOf q))) (rdMaskOf false (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q))))
                    res (MemRel_traceFrame m m1 mi Hm1 Hrel) Hk (SpecEnvOK_custom _ (HenvC _)) H)
          as [ms' [rpv [Eres [Hrp [Hok _]]]]].
        apply (deferred_load_dev_wp envC rfC m1 sl _ _ _ _ (loadCmdOf q) _ ms' rpv HenvC).
        + rewrite defDm_eq, Hdm; exact Hv.
        + rewrite defDm_eq, Hdm; rewrite Eq in Hld; exact Hld.
        + rewrite defDst_eq, defAddr_eq, defDm_eq, Hdm, Eq; reflexivity.
        + exact Hrp.
        + intros Ecr; exists rpv, m1, ms', ms'; split; [exact Eres |]; split; [exact Hm1 |]; split; [exact Hok |].
          split; [apply ReadFrameS_refl |].
          unfold ldDevRf, ldDevSl; rewrite Ecr, Erf; reflexivity.
        + intros Ecr m2 Hm2; exists rpv, m1, ms', m2; split; [exact Eres |]; split; [exact Hm1 |]; split; [exact Hok |].
          split; [exact Hm2 |].
          unfold ldDevRf, ldDevSl; rewrite Ecr, Erf.
          rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine ms' m2 _ _
                     (lineContent_readFrame initLine specRegions ms' m2 Hm2)).
          reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [rpv [m1 [ms' [m2 [Eres [Hm1 [Hok [Hm2 E]]]]]]]]]]].
    exists rpv, m1, ms', m2; split; [exact Eres |]; split; [exact Hm1 |]; split; [exact Hok |]; split; [exact Hm2 |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.

  (* `specSecondLine` for the second line of a crossing load, a CustomMem or unmapped line *)
  Lemma specSecondLine_load_dev :
    forall rf m ld pkt0 envI (mi mi' : MI) res,
      MEMREL m mi -> lineKind implRegions (lineOf true (ldAddr ld)) <> Some true ->
      SemAction envI (@implRegionsLineReadRq type implRegions (rdLineOf true (ldAddr ld))
                        (rdMaskOf true (ldAddr ld) (plSize (ldPending ld)))) mi mi' res ->
      exists rpv ms' m2, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\ DWOK m ms' mi mi' /\
        ReadFrameS specRegions ms' m2 /\
        SemAction envS (@specSecondLine pcAddrInit config specRegions type)
          (mkSysA rf m (secondLoadOf ld pkt0))
          (mkSysA (cnwbApply pcAddrInit (Some (specLoadWbA m2 (ldPending ld) (mergedLoadVal ld pkt0 rpv))) rf) m2
             (getDefault (Option SecondLine))) Zmod.zero.
  Proof.
    intros rf m ld pkt0 envI mi mi' res Hrel Hk H.
    assert (Hev : evalActionPropGen envS (@specSecondLine pcAddrInit config specRegions type)
                    (mkSysA rf m (secondLoadOf ld pkt0))
                    (fun s2' _ => exists rpv ms' m2, res = (true ,, ((rpv ,, (true ,, tt)) ,, tt)) /\ DWOK m ms' mi mi' /\
                       ReadFrameS specRegions ms' m2 /\
                       s2'.(Fst) = mkCoreA (cnwbApply pcAddrInit (Some (specLoadWbA m2 (ldPending ld) (mergedLoadVal ld pkt0 rpv))) rf) m2
                                     (getDefault (Option SecondLine)))).
    { unfold specSecondLine.
      apply (proj2 (evalActionPropGen_liftAction _ _ _ _)).
      match goal with |- evalActionPropGen ?E _ _ _ => assert (HenvC : CEOK E) by (eapply coreEnvOK) end.
      unfold specSecondLineStep.
      apply ev_letAction; apply (readSecondLine_wp pcAddrInit pre post revBase revPfB revPfA); cbv beta.
      apply ev_ifElse_true; [reflexivity |].
      apply ev_letExpGen; intros sv Esv.
      assert (Ed : sv = evalExpr (UNION (SecondLineType, "Load" ::=
                                   Var type SecondLineLoad (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt))))))
        by (rewrite Esv; reflexivity).
      clear Esv; subst sv.
      apply ev_ifElse_false; [reflexivity |].
      apply ev_letExpGen; intros lv Elv.
      assert (El : lv = (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt)))).
      { rewrite Elv.
        exact (evalExpr_ReadUnionData_BuildUnion SecondLineType (@Build_FinType 2 0 I)
                 (Var type SecondLineLoad (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt)))) eq_refl). }
      clear Elv; subst lv.
      do 4 (apply ev_letExp; cbv beta).
      apply core_memAct_wp.
      unfold specMemReadSecondLine.
      apply ev_letExp; cbv beta.
      apply ev_letL; cbv beta.
      match goal with |- evalActionPropGen ?E _ _ _ =>
        destruct (devRead envI E m mi mi' (rdLineOf true (ldAddr ld)) (rdMaskOf true (ldAddr ld) (plSize (ldPending ld)))
                    res Hrel Hk (SpecEnvOK_custom _ (HenvC _)) H) as [ms' [rpv [Eres [Hrp [Hok _]]]]] end.
      apply Hrp; cbv beta.
      apply ev_letL; cbv beta.
      apply ev_letExp; cbv beta.
      apply ev_letL; cbv beta.
      apply (specCompleteLoad_wp pcAddrInit config pre post revBase revPfB revPfA initLine fwcs Hdisj HrevTab); [exact HenvC |].
      intros m2 Hm2.
      apply writeSecondLine_wp; intros r; cbv beta.
      apply ev_return.
      exists rpv, ms', m2; split; [exact Eres |]; split; [exact Hok |]; split; [exact Hm2 |].
      rewrite (specLoadWb_ext config pre post revBase revPfB revPfA initLine ms' m2 _ _
                 (lineContent_readFrame initLine specRegions ms' m2 Hm2)).
      reflexivity. }
    apply evalActionPropGen_to_SemAction in Hev as [s2' [r [Hs [rpv [ms' [m2 [Eres [Hok [Hm2 E]]]]]]]]].
    exists rpv, ms', m2; split; [exact Eres |]; split; [exact Hok |]; split; [exact Hm2 |].
    pose proof (Zmod_1_0 r) as Er; subst r.
    destruct s2' as [sc' []]; cbn [Fst] in E; subst sc'.
    exact Hs.
  Qed.
End StoreSpecDev.
