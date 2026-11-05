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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute SimDataMem GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefFrame RefPeriph RefRevoker RefExecImpl RefDmImpl RefMdEngine.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 5: THE IMPL SIDE OF `loadRqOrStoreOrFenceStage`
 * ===========================================================================
 * - `memReadRqDm_char`: dataMem's load request on the impl memory subtree.
 * - `writeMem_char`: a core store on the impl memory subtree (with the revoker's snoop). *)

Local Abbreviation TS t := (TreeState ElemState t).

Lemma memReadRqDm_char :
  forall regions env addr sz (m m' : TS (implMemTree regions)) r,
    SemAction env (@implMemReadRq regions type ReqDataMem addr sz) m m' r ->
    (andb (msIdle m.(Snd).(Fst)) (noPortWriteB regions m.(Fst)) = false /\ m' = m /\ r = false) \/
    (msIdle m.(Snd).(Fst) = true /\ noPortWriteB regions m.(Fst) = true /\ r = true /\
     exists st' rq', m' = (m.(Fst) ,, (st' ,, (rq' ,, m.(Snd).(Snd).(Snd)))) /\ msReadRq st' = true /\
       msReadRqV st' = stepOf false addr sz (getDefault CapPacket) /\ isReqDataMem rq' = true).
Proof.
  intros regions env addr sz [mr [mst [mrq [mrp [mrdy []]]]]] m' r H; cbn [Fst Snd].
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implMemReadRq, implMemNoPortWriteRq in H.
  cbn [evalActionPropGen] in H.
  apply noPortWrite_wp in H; dm_cbn H; rewrite ?evalExpr_Var' in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Erdy end.
  2: { left; destruct H as [H1 H2]; subst m' r; split; [exact Erdy | split; reflexivity]. }
  assert (Hr : andb (msIdle mst) (noPortWriteB regions mr) = true) by exact Erdy.
  apply andb_prop in Hr as [Hi Hn].
  destruct H as [H1 H2]; subst m' r.
  right; split; [exact Hi | split; [exact Hn | split; [reflexivity |]]].
  do 2 eexists; split; [reflexivity |].
  split; [reflexivity |]; split; [| reflexivity].
  rewrite msReadRqV_build; reflexivity.
Qed.

(* The dataMem view of a request: its dispatched action and the parts the stage branches on *)
Definition mfOf (q : type MemFenceReq) : type MemFenceAction :=
  evalLetExpr (@dispatchMemFence type (mrDst q) (mrAddr q) (mrOp q)).
Definition mfMem (q : type MemFenceReq) : bool := evalExpr ((Var type MemFenceAction (mfOf q)) `? "Mem").
Definition maOf (q : type MemFenceReq) : type MemAction := evalExpr ((Var type MemFenceAction (mfOf q)) `! "Mem").
Definition maStore (q : type MemFenceReq) : bool := evalExpr ((Var type MemAction (maOf q)) `? "Store").
Definition fvOf (q : type MemFenceReq) : type FenceOp := evalExpr ((Var type MemFenceAction (mfOf q)) `! "Fence").
Definition fvFenceI (q : type MemFenceReq) : bool := evalExpr ((Var type FenceOp (fvOf q)) `"FenceI").

Definition snoopRev (addr : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)) (x : TS implRevokerTree)
  : TS implRevokerTree :=
  (x.(Fst) ,, (x.(Snd).(Fst) ,, (x.(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Fst) ,,
   (x.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
   (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
   (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
   (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
   (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
   (orb (snoopHitsB addr sz x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst))
        x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt))))))))))))).

Lemma revEta :
  forall x : TS implRevokerTree,
    x = (x.(Fst) ,, (x.(Snd).(Fst) ,, (x.(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Fst) ,,
         (x.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
         (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
         (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
         (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
         (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
         (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt))))))))))))).
Proof. intros [a [b [c [d [e [f [g [h [i [j [k [l [m []]]]]]]]]]]]]]; reflexivity. Qed.

Lemma fvFenceI_impl :
  forall q b,
    evalExpr (Var type Bool (evalExpr ((Var type FenceOp (evalExpr ((Var type MemFenceAction (mfOf q)) `! "Fence")))
                                          `"FenceI"))) = b ->
    fvFenceI q = b.
Proof. intros q b H; exact H. Qed.

Ltac readbackU :=
  match goal with |- context [@evalExpr ?k (@ReadUnionData ?t ?ls ?v ?j)] =>
    lazymatch v with Var _ _ (evalExpr (BuildUnion ?i ?e)) =>
      let Hr := fresh in
      assert (Hr : @evalExpr k (@ReadUnionData t ls v j) = evalExpr e)
        by exact (evalExpr_ReadUnionData_BuildUnion ls i e eq_refl);
      rewrite Hr; clear Hr
    end
  end.

Lemma mfMem_op : forall q, mfMem q = opIsMem (mrOp q).
Proof.
  intros q; unfold mfMem, mfOf, dispatchMemFence; cbn [evalLetExpr].
  match goal with |- context [if ?c then _ else _] =>
    assert (Hc : c = opIsMem (mrOp q)) by reflexivity; rewrite Hc end.
  destruct (opIsMem (mrOp q)); reflexivity.
Qed.

Lemma maStore_op : forall q, mfMem q = true -> maStore q = opIsStore (mrOp q).
Proof.
  intros q; rewrite mfMem_op; intros Hm.
  unfold maStore, maOf, mfOf, dispatchMemFence, opIsStore; rewrite Hm; cbn [evalLetExpr andb].
  match goal with |- context [if ?c then _ else _] =>
    assert (Hc : c = opIsMem (mrOp q)) by reflexivity; rewrite Hc, Hm end.
  cbv iota; cbn [evalLetExpr].
  rewrite !evalExpr_Var'.
  readbackU.
  cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end;
    [transitivity true | transitivity false]; (reflexivity || exact (eq_sym E)).
Qed.

Lemma fvFenceI_op : forall q, mfMem q = false -> fvFenceI q = opIsFenceI (mrOp q).
Proof.
  intros q; rewrite mfMem_op; intros Hm.
  unfold fvFenceI, fvOf, mfOf, dispatchMemFence, opIsFenceI; rewrite Hm; cbn [evalLetExpr andb negb].
  match goal with |- context [if ?c then _ else _] =>
    assert (Hc : c = opIsMem (mrOp q)) by reflexivity; rewrite Hc, Hm end.
  cbv iota; cbn [evalLetExpr].
  rewrite !evalExpr_Var'.
  readbackU.
  reflexivity.
Qed.

Lemma opIsLoad_of : forall op, opIsMem op = true -> opIsStore op = false -> opIsLoad op = true.
Proof.
  intros op Hm Hs; unfold opIsStore, opIsLoad in *; rewrite Hm in *; cbn [andb] in *.
  revert Hs; cbn [evalExpr].
  match goal with |- Zmod.eqb ?t _ = false -> _ => generalize t end.
  intros t; destruct (bits1_cases t) as [-> | ->]; intros H; [reflexivity | discriminate H].
Qed.

Lemma opIsLoad_store : forall op, opIsMem op = true -> opIsStore op = true -> opIsLoad op = false.
Proof.
  intros op Hm Hs; unfold opIsStore, opIsLoad in *; rewrite Hm in *; cbn [andb] in *.
  revert Hs; cbn [evalExpr].
  match goal with |- Zmod.eqb ?t _ = true -> _ => generalize t end.
  intros t; destruct (bits1_cases t) as [-> | ->]; intros H; [discriminate H | reflexivity].
Qed.

Lemma loadCmd_dst :
  forall q, opIsMem (mrOp q) = true -> opIsStore (mrOp q) = false -> (ldPending (loadCmdOf q)).(Fst) = mrDst q.
Proof.
  intros q Hm Hs.
  unfold opIsStore in Hs; rewrite Hm in Hs; cbn [andb] in Hs.
  unfold loadCmdOf, dispatchMemFence; cbv zeta; cbn [evalLetExpr].
  match goal with |- context [if ?c then _ else _] =>
    assert (Hc : c = opIsMem (mrOp q)) by reflexivity; rewrite Hc, Hm end.
  cbv iota; cbn [evalLetExpr].
  rewrite !evalExpr_Var'.
  readbackU.
  match goal with |- context [if ?c then _ else _] =>
    assert (Hc2 : c = false) by exact Hs; rewrite Hc2 end.
  cbv iota; rewrite !evalExpr_Var'.
  readbackU.
  reflexivity.
Qed.

Lemma evalExpr_And2' :
  forall (a b : Expr type Bool), evalExpr (And [a; b]) = true -> evalExpr a = true /\ evalExpr b = true.
Proof.
  intros a b; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b); cbn; intros H;
    try discriminate H; split; reflexivity.
Qed.

Lemma fenceIReq_char :
  forall regions env (m m' : TS (implMemTree regions)) r,
    SemAction env (@implFenceIReq regions type) m m' r ->
    (r = false /\ m' = m) \/
    (r = true /\ andb (negb (msWriteRq m.(Snd).(Fst))) (noPortWriteB regions m.(Fst)) = true /\
     exists env' mr' v', SemAction env' (@implRegionsSendFenceIRq type regions) m.(Fst) mr' v' /\
       m' = (mr' ,, m.(Snd))).
Proof.
  intros regions env [mr [mst [mrq [mrp [mrdy []]]]]] m' r H; cbn [Fst Snd].
  rewrite SemAction_iff_evalActionPropGen in H.
  unfold implFenceIReq, implMemNoPendingWrite, implMemNoWriteRq, implMemNoPortWriteRq in H.
  cbn [evalActionPropGen] in H.
  apply noPortWrite_wp in H; cbn [evalActionPropGen] in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Ew end.
  - rewrite evalActionPropGen_liftAction in H.
    destruct (evalActionPropGen_to_SemAction _ _ _ H) as [mr' [v' [Hs Hp]]].
    cbn [evalActionPropGen] in Hp; destruct Hp as [Hp1 Hp2]; subst m' r.
    right; split; [reflexivity | split; [exact Ew |]].
    eexists; exists mr', v'; split; [exact Hs | reflexivity].
  - cbn [evalActionPropGen] in H; destruct H as [H1 H2]; subst m' r.
    left; split; reflexivity.
Qed.

Section WriteMem.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).
  Local Abbreviation revOfRA := (revOfR pre post revBase revPfB revPfA).
  Local Abbreviation setRevRA := (setRevR pre post revBase revPfB revPfA).

  Ltac rev_cbn H :=
    cbn -[evalExpr evalLetExpr toAction revOfR setRevR envRevOf implNthRegionAction implMemReadRq implMemWrite
          implMemReadRp implMemDeqRp implReadRevBitRqFor implGetDeqRevBitRpFor implMemNoPendingWrite
          implMemNoPortWriteRq noPortWriteB snoopHitsB] in H.

  Ltac rev_fold H Ex :=
    repeat match type of H with
    | context [setRevR ?a ?b ?c ?d ?e ?mr ?X] =>
        replace (setRevR a b c d e mr X) with mr in H by (symmetry; apply setRevR_same; rewrite Ex; reflexivity)
    end.

  Ltac rev_lens H Ex :=
    apply evalActionPropGen_liftRev in H; cbn [Fst Snd] in H;
    rewrite ?revOfR_setRevR in H; rewrite ?Ex in H; rev_cbn H;
    rewrite ?setRevR_setRevR in H.

  Lemma writeMem_char :
    forall env addr v sz mr mst mrq mrp mrdy m' r b t c e ist ir sa st ph sc sb sh cp,
      revOfRA mr = (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,, (sh ,, (cp ,, tt))))))))))))) ->
      SemAction env (@implWriteMem implRegions type revI addr v sz) (mr ,, (mst ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) m' r ->
      (andb (msIdle mst) (noPortWriteB implRegions mr) = false /\ m' = (mr ,, (mst ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) /\ r = false) \/
      (msIdle mst = true /\ noPortWriteB implRegions mr = true /\ r = true /\
       exists st',
         m' = (setRevRA mr (b ,, (t ,, (c ,, (e ,, (ist ,, (ir ,, (sa ,, (st ,, (ph ,, (sc ,, (sb ,,
                 (orb (snoopHitsB addr sz sa) sh ,, (cp ,, tt))))))))))))) ,, (st' ,, (mrq ,, (mrp ,, (mrdy ,, tt))))) /\
         msWriteRq st' = true /\ msWriteRqV st' = stepOf false addr sz (disassembleW addr v sz)).
  Proof.
    intros env addr v sz mr mst mrq mrp mrdy m' r b t c e ist ir sa st ph sc sb sh cp Ex H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implWriteMem, implMemWrite, implMemNoPortWriteRq in H.
    cbn [evalActionPropGen] in H.
    apply noPortWrite_wp in H; dm_cbn H; rewrite ?evalExpr_Var' in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:Erdy end.
    2: { left; rev_cbn H; destruct H as [H1 H2]; subst m' r; split; [exact Erdy | split; reflexivity]. }
    assert (Hr : andb (msIdle mst) (noPortWriteB implRegions mr) = true) by exact Erdy.
    apply andb_prop in Hr as [Hi Hn].
    apply evalActionPropGen_toAction in H; rev_cbn H.
    unfold ImplDevice.liftRevoker in H.
    rev_lens H Ex.
    unfold implRevokerSnoopStore in H; rev_cbn H.
    match type of H with (if ?c then _ else _) =>
      assert (Eh : c = snoopHitsB addr sz sa) by reflexivity; rewrite Eh in H
    end.
    right; split; [exact Hi | split; [exact Hn |]].
    destruct (snoopHitsB addr sz sa); destruct H as [H1 H2]; subst m' r; (split; [reflexivity |]);
      (eexists; split; [reflexivity | split; [reflexivity | rewrite msWriteRqV_build; reflexivity]]).
  Qed.
  Lemma writeMem_char' :
    forall env addr v sz (m m' : TS (implMemTree implRegions)) r,
      SemAction env (@implWriteMem implRegions type revI addr v sz) m m' r ->
      (andb (msIdle m.(Snd).(Fst)) (noPortWriteB implRegions m.(Fst)) = false /\ m' = m /\ r = false) \/
      (msIdle m.(Snd).(Fst) = true /\ noPortWriteB implRegions m.(Fst) = true /\ r = true /\
       exists st', m' = (setRevRA m.(Fst) (snoopRev addr sz (revOfRA m.(Fst))) ,, (st' ,, m.(Snd).(Snd))) /\
         msWriteRq st' = true /\ msWriteRqV st' = stepOf false addr sz (disassembleW addr v sz)).
  Proof.
    intros env addr v sz [mr [mst [mrq [mrp [mrdy []]]]]] m' r H.
    exact (writeMem_char env addr v sz mr mst mrq mrp mrdy m' r _ _ _ _ _ _ _ _ _ _ _ _ _ (revEta (revOfRA mr)) H).
  Qed.
End WriteMem.

Section LsfImpl.
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

  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Abbreviation iRfA :=
    (iRf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iWbA :=
    (iWb pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA :=
    (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA :=
    (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA :=
    (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA :=
    (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRpReadyA :=
    (iRpReady pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iFetchA :=
    (iFetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDecodeA :=
    (iDecode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecA :=
    (iExec pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmA :=
    (iDm pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA :=
    (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
           mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  Local Abbreviation iMemA :=
    (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation NPCORE :=
    (Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPMEM :=
    (ImplDataMem.np_mem dataMemCapacity pcAddrInit (withInst_BpTree bp)
       (implFetchTree pcAddrInit fetchCapacity instCapacity) (implDecodeTree decodeCapacity)
       (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)
       (fun ty => implExecuteIfc ty) (fun ty => implMemIfc config implRegions revI) type).

  Local Abbreviation NPDM :=
    (ImplDataMem.np_dataMem dataMemCapacity pcAddrInit (withInst_BpTree bp)
       (implFetchTree pcAddrInit fetchCapacity instCapacity) (implDecodeTree decodeCapacity)
       (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)
       (fun ty => implExecuteIfc ty) (fun ty => implMemIfc config implRegions revI) type).

  Local Abbreviation FT := (implFetchTree pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation DT := (implDecodeTree decodeCapacity).
  Local Abbreviation MDT := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation EIFC := (fun ty => @implExecuteIfc ty).
  Local Abbreviation MIFC := (fun ty => @implMemIfc config implRegions ty revI).

  Local Abbreviation NPIF :=
    (ImplDataMem.np_inputFifo dataMemCapacity pcAddrInit (withInst_BpTree bp) FT DT MDT EIFC MIFC type).
  Local Abbreviation iDmBufA :=
    (iDmBuf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation LSF :=
    (@loadRqOrStoreOrFenceStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

  Local Abbreviation iDmFA s1 := (dataMem_fifo dataMemCapacity (iDmA s1)).

  Record LsfFrame (s1 s1' : IState) : Prop := {
    lf_rf    : iRfA s1' = iRfA s1 ;
    lf_wb    : iWbA s1' = iWbA s1 ;
    lf_fetch : iFetchA s1' = iFetchA s1 ;
    lf_dec   : iDecodeA s1' = iDecodeA s1 ;
    lf_md    : iMdA s1' = iMdA s1 ;
    lf_dmf   : iDmFA s1' = fifoDeqState (iDmFA s1)
  }.

  Record StoreAcc (s1 s1' : IState) (q : type MemFenceReq) : Prop := {
    sa_fr   : LsfFrame s1 s1' ;
    sa_exec : iExecA s1' = iExecA s1 ;
    sa_dmst : iDmStA s1' = iDmStA s1 ;
    sa_idle : msIdle (iMemStA s1) = true ;
    sa_npw  : noPortWriteB implRegions (iRegionsA s1) = true ;
    sa_reg  : iRegionsA s1' = setRevR pre post revBase revPfB revPfA (iRegionsA s1)
                (snoopRev (stAddrOf (storeCmdOf q)) (stSizeOf (storeCmdOf q))
                   (revOfR pre post revBase revPfB revPfA (iRegionsA s1))) ;
    sa_ms   : msWriteRq (iMemStA s1') = true ;
    sa_msv  : msWriteRqV (iMemStA s1') =
                stepOf false (stAddrOf (storeCmdOf q)) (stSizeOf (storeCmdOf q))
                  (disassembleW (stAddrOf (storeCmdOf q)) (stValOf (storeCmdOf q)) (stSizeOf (storeCmdOf q))) ;
    sa_rq   : iRequesterA s1' = iRequesterA s1 ;
    sa_rp   : iReadRpA s1' = iReadRpA s1 ;
    sa_rdy  : iRpReadyA s1' = iRpReadyA s1
  }.

  Record LoadAcc (s1 s1' : IState) (q : type MemFenceReq) : Prop := {
    la_fr   : LsfFrame s1 s1' ;
    la_exec : iExecA s1' = iExecA s1 ;
    la_dm   : dmLoadRp (iDmStA s1') = true ;
    la_dmv  : dmLoadRpV (iDmStA s1') = loadCmdOf q ;
    la_idle : msIdle (iMemStA s1) = true ;
    la_npw  : noPortWriteB implRegions (iRegionsA s1) = true ;
    la_reg  : iRegionsA s1' = iRegionsA s1 ;
    la_ms   : msReadRq (iMemStA s1') = true ;
    la_msv  : msReadRqV (iMemStA s1') =
                stepOf false (ldAddr (loadCmdOf q)) (plSize (ldPending (loadCmdOf q))) (getDefault CapPacket) ;
    la_rq   : isReqDataMem (iRequesterA s1') = true ;
    la_rp   : iReadRpA s1' = iReadRpA s1 ;
    la_rdy  : iRpReadyA s1' = iRpReadyA s1
  }.

  Record PlainAcc (s1 s1' : IState) : Prop := {
    pa_fr   : LsfFrame s1 s1' ;
    pa_exec : iExecA s1' = iExecA s1 ;
    pa_dmst : iDmStA s1' = iDmStA s1 ;
    pa_mem  : iMemA s1' = iMemA s1
  }.

  Lemma dmLoadRpOf_facts :
    forall ld, dmLoadRp (evalExpr (UNION (DataMemStateList, "LoadRp" ::= Var type LoadCmd ld))) = true /\
               dmLoadRpV (evalExpr (UNION (DataMemStateList, "LoadRp" ::= Var type LoadCmd ld))) = ld.
  Proof.
    intros ld; split; [reflexivity |].
    exact (evalExpr_ReadUnionData_BuildUnion DataMemStateList (@Build_FinType (length DataMemStateList) 1 I)
             (Var type LoadCmd ld) eq_refl).
  Qed.

  Local Abbreviation iFenceIPendingA :=
    (iFenceIPending pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iExecEpochA :=
    (iExecEpoch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  Record FenceIAcc (s1 s1' : IState) : Prop := {
    fa_fr   : LsfFrame s1 s1' ;
    fa_dmst : iDmStA s1' = iDmStA s1 ;
    fa_npw  : andb (negb (msWriteRq (iMemStA s1))) (noPortWriteB implRegions (iRegionsA s1)) = true ;
    fa_mem  : exists env' mr' v', SemAction env' (@implRegionsSendFenceIRq type implRegions) (iRegionsA s1) mr' v' /\
                iMemA s1' = (mr' ,, (iMemA s1).(Snd)) ;
    fa_fip  : iFenceIPendingA s1' = false ;
    fa_ep   : iExecEpochA s1' = iExecEpochA s1 ;
    fa_redir : ex_redirect (iExecA s1') = ex_redirect (iExecA s1)
  }.

  Lemma lsf_char :
    forall env (s1 s1' : IState) r,
      fifo_wf (iDmFA s1) ->
      SemAction env LSF s1 s1' r ->
      s1' = s1 \/
      exists q rest, iDmBufA s1 = q :: rest /\ dmLoadRq (iDmStA s1) = true /\
        ((mfMem q = true /\ maStore q = true /\ StoreAcc s1 s1' q) \/
         (mfMem q = true /\ maStore q = false /\ LoadAcc s1 s1' q) \/
         (mfMem q = false /\ fvFenceI q = false /\ PlainAcc s1 s1') \/
         (mfMem q = false /\ fvFenceI q = true /\ FenceIAcc s1 s1')).
  Proof.
    intros env s1 s1' r Hwf H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold loadRqOrStoreOrFenceStage in H; rewrite evalActionPropGen_liftAction in H.
    unfold loadRqOrStoreOrFence in H.
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_readState _ _ _) HQ_)];
      cbv beta in H.
    change (dm_state dataMemCapacity (readSubTreeState NPDM (readSubTreeState NPCORE s1))) with (iDmStA s1) in H.
    eapply fw_liftRead in H; [| intros env_ sub_ Q_ HQ_; exact (proj1 (evalActionPropGen_first_iff _ _ _ _ _) HQ_)];
      cbv beta in H.
    change (readSubTreeState NPIF (readSubTreeState NPCORE s1)) with (iDmFA s1) in H.
    apply fw_ifTF in H as [[Hg H] | [Hg H]].
    2: { left; cbn [evalActionPropGen] in H; destruct H as [H _].
         rewrite writeSubTreeState_readSubTreeState in H; symmetry; exact H. }
    apply evalExpr_And2' in Hg; destruct Hg as [Hlrq Hv].
    change (dmLoadRq (iDmStA s1) = true) in Hlrq.
    change ((@fifoFirstVal dataMemCapacity MemFenceReq (iDmFA s1)).(Snd).(Fst) = true) in Hv.
    rewrite (fifoFirstVal_valid _ _ _ Hwf) in Hv.
    destruct (@fifo_to_list dataMemCapacity MemFenceReq (iDmFA s1)) as [| q rest] eqn:El; [discriminate Hv |].
    pose proof (fifoFirstVal_data _ _ _ q rest El) as Eqd.
    remember (@fifoFirstVal dataMemCapacity MemFenceReq (iDmFA s1)) as fv eqn:Efv.
    destruct fv as [fq [fb []]]; cbn [Fst] in Eqd; subst fq.
    do 4 apply fw_letExp in H.
    apply fw_letLGen in H; destruct H as [mf [Emf H]].
    assert (Emf' : mf = mfOf q) by (rewrite Emf; reflexivity); clear Emf; subst mf.
    apply fw_ifTF in H as [[Hm H] | [Hm H]].
    - assert (Em : mfMem q = true) by exact Hm; clear Hm.
      apply fw_letExp in H.
      apply fw_ifTF in H as [[Hs H] | [Hs H]].
      + assert (Es : maStore q = true) by exact Hs; clear Hs.
        do 4 apply fw_letExp in H.
        apply fw_liftSem in H; destruct H as [sm' [acc [Hmem H]]].
        cbn [mem_writeMem implMemIfc] in Hmem.
        apply writeMem_char' in Hmem.
        change (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) with (iMemA s1) in Hmem, H.
        destruct Hmem as [[Hn [-> ->]] | [Hi [Hnp [-> [st' [-> [Hw1 Hw2]]]]]]].
        * left; apply fw_ifFalse in H; [| reflexivity].
          cbn [evalActionPropGen] in H; destruct H as [H _].
          change (iMemA s1) with (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) in H.
          rewrite !writeSubTreeState_readSubTreeState in H; symmetry; exact H.
        * apply fw_ifTrue in H; [| reflexivity].
          rewrite evalActionPropGen_liftAction in H; apply (proj1 (evalActionPropGen_deq_iff _ _ _ _ _)) in H.
          cbn [evalActionPropGen] in H; destruct H as [H _]; subst s1'.
          right; exists q, rest; split; [exact El | split; [exact Hlrq |]].
          left; split; [exact Em | split; [exact Es |]].
          split; [split; reflexivity | reflexivity | reflexivity | exact Hi | exact Hnp | reflexivity |
                  exact Hw1 | exact Hw2 | reflexivity | reflexivity | reflexivity].
      + assert (Es : maStore q = false) by exact Hs; clear Hs.
        do 4 apply fw_letExp in H.
        apply fw_liftSem in H; destruct H as [sm' [acc [Hmem H]]].
        cbn [mem_readMemRq implMemIfc] in Hmem.
        apply memReadRqDm_char in Hmem.
        change (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) with (iMemA s1) in Hmem, H.
        destruct Hmem as [[Hn [-> ->]] | [Hi [Hnp [-> [st' [rq' [-> [Hr1 [Hr2 Hr3]]]]]]]]].
        * left; apply fw_ifFalse in H; [| reflexivity].
          cbn [evalActionPropGen] in H; destruct H as [H _].
          change (iMemA s1) with (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) in H.
          rewrite !writeSubTreeState_readSubTreeState in H; symmetry; exact H.
        * apply fw_ifTrue in H; [| reflexivity].
          apply fw_letExp in H; apply fw_letAction in H.
          rewrite evalActionPropGen_liftAction in H; unfold writeState in H; cbn [evalActionPropGen] in H.
          rewrite evalActionPropGen_liftAction in H; apply (proj1 (evalActionPropGen_deq_iff _ _ _ _ _)) in H.
          cbn [evalActionPropGen] in H; destruct H as [H _]; subst s1'.
          right; exists q, rest; split; [exact El | split; [exact Hlrq |]].
          right; left; split; [exact Em | split; [exact Es |]].
          split; [split; reflexivity | reflexivity | exact (proj1 (dmLoadRpOf_facts _)) |
                  exact (proj2 (dmLoadRpOf_facts _)) | exact Hi | exact Hnp | reflexivity |
                  exact Hr1 | exact Hr2 | exact Hr3 | reflexivity | reflexivity].
    - assert (Em : mfMem q = false) by exact Hm; clear Hm.
      do 2 apply fw_letExp in H.
      apply fw_ifTF in H as [[Hf H] | [Hf H]].
      + pose proof (fvFenceI_impl q true Hf) as Ef.
        rewrite evalActionPropGen_liftAction in H; cbn [mem_fenceI_req implMemIfc] in H.
        destruct (evalActionPropGen_to_SemAction _ _ _ H) as [m' [acc [Hfi H2]]]; clear H; rename H2 into H.
        change (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) with (iMemA s1) in Hfi, H.
        apply fenceIReq_char in Hfi.
        destruct Hfi as [[-> ->] | [-> [Hnw [env' [mr' [v' [Hs ->]]]]]]].
        * left; apply fw_ifFalse in H; [| reflexivity].
          cbn [evalActionPropGen] in H; destruct H as [H _].
          change (iMemA s1) with (readSubTreeState NPMEM (readSubTreeState NPCORE s1)) in H.
          rewrite !writeSubTreeState_readSubTreeState in H; symmetry; exact H.
        * apply fw_ifTrue in H; [| reflexivity].
          apply fw_letAction in H; apply fw_ifTrue in H; [| exact Hf].
          rewrite evalActionPropGen_liftAction in H.
          cbn [execute_clearFenceIPend implExecuteIfc clearFenceIPending evalActionPropGen] in H.
          rewrite evalActionPropGen_liftAction in H; apply (proj1 (evalActionPropGen_deq_iff _ _ _ _ _)) in H.
          cbn [evalActionPropGen] in H; destruct H as [H _]; subst s1'.
          right; exists q, rest; split; [exact El | split; [exact Hlrq |]].
          right; right; right; split; [exact Em | split; [exact Ef |]].
          split; [split; reflexivity | reflexivity | exact Hnw | | reflexivity | reflexivity | reflexivity].
          exists env', mr', v'; split; [exact Hs | reflexivity].
      + pose proof (fvFenceI_impl q false Hf) as Ef.
        rewrite evalActionPropGen_liftAction in H; cbn [mem_fence_req implMemIfc] in H.
        apply fw_return in H; cbv beta in H.
        rewrite writeSubTreeState_readSubTreeState in H.
        apply fw_ifTrue in H; [| reflexivity].
        apply fw_letAction in H; apply fw_ifFalse in H; [| exact Hf].
        cbn [evalActionPropGen] in H.
        rewrite evalActionPropGen_liftAction in H; apply (proj1 (evalActionPropGen_deq_iff _ _ _ _ _)) in H.
        cbn [evalActionPropGen] in H; destruct H as [H _]; subst s1'.
        right; exists q, rest; split; [exact El | split; [exact Hlrq |]].
        right; right; left; split; [exact Em | split; [exact Ef |]].
        split; [split; reflexivity | reflexivity | reflexivity | reflexivity].
  Qed.

End LsfImpl.
