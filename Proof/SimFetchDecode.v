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
From Cheriot Require Export SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Export Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Export TreeLemmas StateRel SimDevices.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. `implFetchTree` AND `implDecodeTree` STATE ACCESSORS & ACTION LEMMAS
 * =========================================================================== *)

Section FetchDecodeTreeHelpers.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity : nat.

  Local Abbreviation fTree := (implFetchTree pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (implDecodeTree decodeCapacity).

  (* --- 1A. `implFetchTree` Updaters & Simplification Lemmas --- *)

  Definition fetch_withPc (sf : TreeState ElemState fTree) (v : type Addr)
    : TreeState ElemState fTree :=
    (v ,, sf.(Snd)).

  Definition fetch_withPredEpoch (sf : TreeState ElemState fTree) (v : type Epoch)
    : TreeState ElemState fTree :=
    (sf.(Fst) ,, (v ,, sf.(Snd).(Snd))).

  Definition fetch_withCurParcelOpt (sf : TreeState ElemState fTree)
    (v : type (Option (Bit LgFetchParcels)))
    : TreeState ElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (v ,, sf.(Snd).(Snd).(Snd)))).

  Definition fetch_withStraddleOpt (sf : TreeState ElemState fTree)
    (v : type (Option StraddleHalf))
    : TreeState ElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,, (v ,, sf.(Snd).(Snd).(Snd).(Snd))))).

  Definition fetch_withCanProceed (sf : TreeState ElemState fTree) (v : bool)
    : TreeState ElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Fst) ,, (v ,, sf.(Snd).(Snd).(Snd).(Snd).(Snd)))))).

  Definition fetch_withFetchBufFifo (sf : TreeState ElemState fTree)
    (v : TreeState ElemState (fifoTree fetchCapacity FetchBufEntry))
    : TreeState ElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Fst) ,, (sf.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))).

  Definition fetch_withInstFifo (sf : TreeState ElemState fTree)
    (v : TreeState ElemState (fifoTree instCapacity AssembledInst))
    : TreeState ElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Fst) ,, (sf.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))))).

  Lemma evalActionPropGen_readFetchPc :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@readFetchPc pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_pc pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writeFetchPc :
    forall {env : Env fTree} (val : type Addr) (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@writeFetchPc pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withPc sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readPredEpoch :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@readPredEpoch pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_predEpoch pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writePredEpoch :
    forall {env : Env fTree} (val : type Epoch) (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@writePredEpoch pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withPredEpoch sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readCurParcelOpt :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@readCurParcelOpt pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_curParcelOpt pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writeCurParcelOpt :
    forall {env : Env fTree} (val : type (Option (Bit LgFetchParcels))) (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@writeCurParcelOpt pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withCurParcelOpt sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readStraddleOpt :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@readStraddleOpt pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_straddleOpt pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writeStraddleOpt :
    forall {env : Env fTree} (val : type (Option StraddleHalf)) (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@writeStraddleOpt pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withStraddleOpt sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_clearStraddle :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@clearStraddle pcAddrInit fetchCapacity instCapacity type) sf P <->
      P (fetch_withStraddleOpt sf (getDefault (Option StraddleHalf))) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readFetchCanProceed :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@readFetchCanProceed pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_canProceed pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_setFetchCanProceed :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@setFetchCanProceed pcAddrInit fetchCapacity instCapacity type) sf P <->
      P (fetch_withCanProceed sf true) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_clearFetchCanProceed :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@clearFetchCanProceed pcAddrInit fetchCapacity instCapacity type) sf P <->
      P (fetch_withCanProceed sf false) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_fetchInstFirst :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@fetchInstFirst pcAddrInit fetchCapacity instCapacity type) sf P <->
      evalActionPropGen (subEnv (@np_fetchInstFifo pcAddrInit fetchCapacity instCapacity) env sf)
        (@first instCapacity AssembledInst type)
        (fetch_instFifo pcAddrInit fetchCapacity instCapacity sf)
        (fun f' res => P (fetch_withInstFifo sf f') res).
  Proof.
    intros env sf P.
    unfold fetchInstFirst.
    rewrite (evalActionPropGen_liftAction (@np_fetchInstFifo pcAddrInit fetchCapacity instCapacity)).
    reflexivity.
  Qed.

  Lemma evalActionPropGen_fetchInstDeq :
    forall {env : Env fTree} (sf : TreeState ElemState fTree) P,
      evalActionPropGen env (@fetchInstDeq pcAddrInit fetchCapacity instCapacity type) sf P <->
      evalActionPropGen (subEnv (@np_fetchInstFifo pcAddrInit fetchCapacity instCapacity) env sf)
        (@deq instCapacity AssembledInst type)
        (fetch_instFifo pcAddrInit fetchCapacity instCapacity sf)
        (fun f' res => P (fetch_withInstFifo sf f') res).
  Proof.
    intros env sf P.
    unfold fetchInstDeq.
    rewrite (evalActionPropGen_liftAction (@np_fetchInstFifo pcAddrInit fetchCapacity instCapacity)).
    reflexivity.
  Qed.

  (* --- 1B. `implDecodeTree` Updaters & Simplification Lemmas --- *)

  Definition decode_withCanProceed (sd : TreeState ElemState decTree) (v : bool)
    : TreeState ElemState decTree :=
    (v ,, sd.(Snd)).

  Definition decode_withToAluFifo (sd : TreeState ElemState decTree)
    (v : TreeState ElemState (fifoTree decodeCapacity DecodeToAluEntry))
    : TreeState ElemState decTree :=
    (sd.(Fst) ,, ((v ,, sd.(Snd).(Fst).(Snd)) ,, sd.(Snd).(Snd))).

  Lemma evalActionPropGen_readDecodeCanProceed :
    forall {env : Env decTree} (sd : TreeState ElemState decTree) P,
      evalActionPropGen env (@readDecodeCanProceed decodeCapacity type) sd P <->
      P sd (decode_canProceed decodeCapacity sd).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_setDecodeCanProceed :
    forall {env : Env decTree} (sd : TreeState ElemState decTree) P,
      evalActionPropGen env (@setDecodeCanProceed decodeCapacity type) sd P <->
      P (decode_withCanProceed sd true) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_clearDecodeCanProceed :
    forall {env : Env decTree} (sd : TreeState ElemState decTree) P,
      evalActionPropGen env (@clearDecodeCanProceed decodeCapacity type) sd P <->
      P (decode_withCanProceed sd false) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_decodeFirst :
    forall {env : Env decTree} (sd : TreeState ElemState decTree) P,
      evalActionPropGen env (@decodeFirst decodeCapacity type) sd P <->
      evalActionPropGen (subEnv (@np_decToAluFifo decodeCapacity) env sd)
        (@first decodeCapacity DecodeToAluEntry type)
        (decode_toAluFifo decodeCapacity sd)
        (fun f' res => P (decode_withToAluFifo sd f') res).
  Proof.
    intros env sd P.
    unfold decodeFirst.
    rewrite (evalActionPropGen_liftAction (@np_decToAluFifo decodeCapacity)).
    reflexivity.
  Qed.

  Lemma evalActionPropGen_decodeDeq :
    forall {env : Env decTree} (sd : TreeState ElemState decTree) P,
      evalActionPropGen env (@decodeDeq decodeCapacity type) sd P <->
      evalActionPropGen (subEnv (@np_decToAluFifo decodeCapacity) env sd)
        (@deq decodeCapacity DecodeToAluEntry type)
        (decode_toAluFifo decodeCapacity sd)
        (fun f' res => P (decode_withToAluFifo sd f') res).
  Proof.
    intros env sd P.
    unfold decodeDeq.
    rewrite (evalActionPropGen_liftAction (@np_decToAluFifo decodeCapacity)).
    reflexivity.
  Qed.

End FetchDecodeTreeHelpers.

(* ===========================================================================
 * 2. MEMORY FETCH CHANNEL LEMMAS (`fetchRps`, `FetchRp`, `FetchDeqRp`)
 * =========================================================================== *)

Section MemFetchChannelLemmas.
  Local Opaque liftAction.


  (* --- 2A. `implRegionsReadFenceIWait`, `implRegionsFetchRp`, `implRegionsFetchDeqRp` --- *)

  Lemma SemAction_memRegionReadFenceIWait_preserves_state :
    forall (r : MemRegion)
           {env : Env (memRegionTree r)}
           (sr sr' : TreeState ElemState (memRegionTree r))
           (wait : bool),
      SemAction env (@memRegionReadFenceIWait r type) sr sr' wait ->
      sr' = sr.
  Proof.
    intros r env sr sr' wait Hsem.
    unfold memRegionReadFenceIWait, memRegionTree, memRegionKindTree in *.
    revert env sr sr' Hsem.
    destruct (r.(regionKind)) as [| children rdAct wrAct irqAct];
      intros env sr sr' Hsem.
    - unfold externalReadFenceIWait in Hsem.
      rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [v [Hsub [Hsr' _]]]].
      apply InversionSemAction in Hsub; apply InversionSemAction in Hsub as [Hsub0' _].
      subst sr' sub0'; destruct sr as [s0 srest]; reflexivity.
    - apply InversionSemAction in Hsem as [Hsr' _]; exact Hsr'.
  Qed.

  Theorem SemAction_implRegionsReadFenceIWait_preserves_state :
    forall (rs : list MemRegion)
           {env : Env (implRegionsTree rs)}
           (sm sm' : TreeState ElemState (implRegionsTree rs))
           (wait : bool),
      SemAction env (@implRegionsReadFenceIWait type rs) sm sm' wait ->
      sm' = sm.
  Proof.
    intros rs; unfold implRegionsReadFenceIWait, genFoldRegionActions.
    lazymatch goal with
    | |- context [genFoldRegionActionsAux _ _ _ ?a _] => generalize a as acc
    end.
    induction rs as [| r rs IH]; intros acc env sm sm' wait Hsem.
    - apply InversionSemAction in Hsem as [Hsm' _]; exact Hsm'.
    - cbn [genFoldRegionActionsAux] in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      rewrite evalActionPropGen_liftAction in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [devWait [Hdev Hsem1]]].
      apply SemAction_liftToImplRegion in Hdev as [spec0' [Hspec0' Hsub0']].
      pose proof (SemAction_memRegionReadFenceIWait_preserves_state r _ _ _ Hspec0') as Hspec_eq.
      rewrite Hspec_eq, writeImplRegionSpecState_projImplRegionSpecState in Hsub0'.
      rewrite evalActionPropGen_liftAction in Hsem1.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [sub1' [restWait [Hrest [Hsm' _]]]].
      pose proof (IH _ _ _ _ _ Hrest) as Hsub1'.
      subst sm' sub0' sub1'.
      destruct sm as [s0 [s1 []]]; reflexivity.
  Qed.

  Corollary SemAction_implMemReadFenceIWait_preserves_state :
    forall (rs : list MemRegion)
           {env : Env (implMemTree rs)}
           (sm sm' : TreeState ElemState (implMemTree rs))
           (wait : bool),
      SemAction env (liftAction child0Path (@implRegionsReadFenceIWait type rs)) sm sm' wait ->
      sm' = sm.
  Proof.
    intros rs env sm sm' wait Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff in Hsem.
    destruct Hsem as [sub0' [Hsub0' Hsm']]; subst sm'.
    rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
    pose proof (SemAction_implRegionsReadFenceIWait_preserves_state rs _ _ _ Hsub0') as Heq.
    cbn [child0Path implMemTree readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child] in *.
    rewrite Heq; destruct sm as [s0 srest]; reflexivity.
  Qed.

  Lemma SemAction_implExternalFetchLineReadRp_preserves_state :
    forall (r : MemRegion)
           {env : Env (implExternalMemRegionTree r)}
           (sr sr' : TreeState ElemState (implExternalMemRegionTree r))
           (rpOpt : type (Option LineReadRp)),
      SemAction env (@implExternalFetchLineReadRp r type) sr sr' rpOpt ->
      sr' = sr.
  Proof.
    intros r env sr sr' rpOpt Hsem.
    unfold implExternalFetchLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub1' [v [Hrd [Hsr' _]]]].
    apply InversionSemAction in Hrd; apply InversionSemAction in Hrd as [Hsub1' _].
    subst sr' sub1'; destruct sr as [s0 [s1 srest]]; reflexivity.
  Qed.

  Lemma SemAction_implMemRegionFetchRp_preserves_state :
    forall (r : MemRegion)
           {env : Env (implMemRegionTree r)}
           (sr sr' : TreeState ElemState (implMemRegionTree r))
           (pktOpt : type (Option FetchPacket)),
      SemAction env (@implMemRegionFetchLineReadRp r type) sr sr' pktOpt ->
      sr' = sr.
  Proof.
    intros r env sr sr' pktOpt Hsem.
    unfold implMemRegionFetchLineReadRp, implMemRegionTree, implMemRegionKindTree in *.
    revert env sr sr' pktOpt Hsem.
    destruct (r.(regionKind)) as [| children rdAct wrAct irqAct];
      intros env sr sr' pktOpt Hsem.
    - rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sr1 [rpOpt [Hrp Hsem1]]].
      pose proof (SemAction_implExternalFetchLineReadRp_preserves_state r sr sr1 rpOpt Hrp) as Hsr1.
      subst sr1.
      cbn [evalActionPropGen] in Hsem1.
      lazymatch type of Hsem1 with | (if ?b then _ else _) => destruct b end;
        cbn [evalActionPropGen] in Hsem1;
        destruct Hsem1 as [Hsr' _]; symmetry; exact Hsr'.
    - apply InversionSemAction in Hsem as [Hsr' _]; exact Hsr'.
  Qed.

  Theorem SemAction_implRegionsFetchRp_preserves_state :
    forall (rs : list MemRegion) (addr : type Addr)
           {env : Env (implRegionsTree rs)}
           (sm sm' : TreeState ElemState (implRegionsTree rs))
           (pktOpt : type (Option FetchPacket)),
      SemAction env (@implRegionsFetchLineReadRp type rs addr) sm sm' pktOpt ->
      sm' = sm.
  Proof.
    intros rs addr env sm sm' pktOpt Hsem.
    unfold implRegionsFetchLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [smMid [rpOpt [Hroute HP]]].
    cbn [evalActionPropGen] in HP; destruct HP as [HsmMid _]; subst sm'.
    clear Hsem pktOpt; revert env sm smMid rpOpt Hroute.
    unfold genRouteRegionAction.
    lazymatch goal with
    | |- context [genRouteRegionActionAux _ _ _ _ ?a _] => generalize a as acc
    end.
    induction rs as [| r rs IH]; intros acc env sm sm' pktOpt Hsem.
    - apply InversionSemAction in Hsem as [Hsm' _]; exact Hsm'.
    - cbn [genRouteRegionActionAux] in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [devRp [Hdev Hsem1]]].
        pose proof (SemAction_implMemRegionFetchRp_preserves_state r _ _ _ Hdev) as Hsub0'.
        rewrite evalActionPropGen_liftAction in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [sub1' [restRp [Hrest [Hsm' _]]]].
        pose proof (IH _ _ _ _ _ Hrest) as Hsub1'.
        subst sm' sub0' sub1'.
        destruct sm as [s0 [s1 []]]; reflexivity.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub1' [restRp [Hrest [Hsm' _]]]].
        pose proof (IH _ _ _ _ _ Hrest) as Hsub1'.
        subst sm' sub1'.
        destruct sm as [s0 [s1 []]]; reflexivity.
  Qed.

  Corollary SemAction_implMemFetchRp_preserves_state :
    forall (rs : list MemRegion) (addr : type Addr)
           {env : Env (implMemTree rs)}
           (sm sm' : TreeState ElemState (implMemTree rs))
           (pktOpt : type (Option FetchPacket)),
      SemAction env (liftAction child0Path (@implRegionsFetchLineReadRp type rs addr)) sm sm' pktOpt ->
      sm' = sm.
  Proof.
    intros rs addr env sm sm' pktOpt Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff in Hsem.
    destruct Hsem as [sub0' [Hsub0' Hsm']]; subst sm'.
    rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
    pose proof (SemAction_implRegionsFetchRp_preserves_state rs addr _ _ _ Hsub0') as Heq.
    cbn [child0Path implMemTree readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child] in *.
    rewrite Heq; destruct sm as [s0 srest]; reflexivity.
  Qed.

  Lemma SemAction_implMemRegionFetchDeqRp_preserves_spec :
    forall (r : MemRegion)
           {env : Env (implMemRegionTree r)}
           (sr sr' : TreeState ElemState (implMemRegionTree r))
           (v : bits 0),
      SemAction env (@implMemRegionFetchLineDeqRp r type) sr sr' v ->
      projImplRegionSpecState r sr' = projImplRegionSpecState r sr.
  Proof.
    intros r env sr sr' v Hsem.
    unfold implMemRegionFetchLineDeqRp, implExternalFetchLineDeqRp, projImplRegionSpecState, implMemRegionTree, implMemRegionKindTree, memRegionTree, memRegionKindTree in *.
    revert env sr sr' Hsem.
    destruct (r.(regionKind)) as [| children rdAct wrAct irqAct];
      intros env sr sr' Hsem.
    - rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub1' [v' [_ [Hsr' _]]]].
      subst sr'; reflexivity.
    - apply InversionSemAction in Hsem as [Hsr' _]; subst sr'; reflexivity.
  Qed.

  Theorem SemAction_implRegionsFetchDeqRp_preserves_spec :
    forall (rs : list MemRegion) (addr : type Addr)
           {env : Env (implRegionsTree rs)}
           (sm sm' : TreeState ElemState (implRegionsTree rs))
           (v : bits 0),
      SemAction env (@implRegionsFetchLineDeqRp type rs addr) sm sm' v ->
      projImplMemRegions rs sm' = projImplMemRegions rs sm.
  Proof.
    intros rs addr; unfold implRegionsFetchLineDeqRp, genRouteRegionUnitAction, genRouteRegionAction.
    lazymatch goal with
    | |- context [genRouteRegionActionAux _ _ _ _ ?a _] => generalize a as acc
    end.
    induction rs as [| r rs IH]; intros acc env sm sm' v Hsem.
    - apply InversionSemAction in Hsem as [Hsm' _]; subst sm'; reflexivity.
    - destruct sm as [s0 [s1 []]].
      cbn [genRouteRegionActionAux] in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [v0 [Hdeq0 Hsem1]]].
        pose proof (SemAction_implMemRegionFetchDeqRp_preserves_spec r _ _ _ Hdeq0) as Hsub0'.
        rewrite evalActionPropGen_liftAction in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [sub1' [v1 [Hdeq1 [Hsm' _]]]].
        pose proof (IH _ _ _ _ _ Hdeq1) as Hsub1'.
        subst sm'.
        cbn [projImplMemRegions implRegionsTree implRegionsChildren regionsTree regionsTreeChildren child0Path child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsub0', Hsub1' |- *.
        change (projImplRegionSpecState r) with (StateRel.projImplRegionSpecState r) in Hsub0'.
        rewrite Hsub0', Hsub1'; reflexivity.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub1' [v1 [Hdeq1 [Hsm' _]]]].
        pose proof (IH _ _ _ _ _ Hdeq1) as Hsub1'.
        subst sm'.
        cbn [projImplMemRegions implRegionsTree implRegionsChildren regionsTree regionsTreeChildren child0Path child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsub1' |- *.
        rewrite Hsub1'; reflexivity.
  Qed.

  Corollary SemAction_implMemFetchDeqRp_preserves_spec :
    forall (rs : list MemRegion) (addr : type Addr)
           {env : Env (implMemTree rs)}
           (sm sm' : TreeState ElemState (implMemTree rs))
           (v : bits 0),
      SemAction env (liftAction child0Path (@implRegionsFetchLineDeqRp type rs addr)) sm sm' v ->
      StateRel.projImplMemSpecState rs sm' = StateRel.projImplMemSpecState rs sm.
  Proof.
    intros rs addr env sm sm' v Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff in Hsem.
    destruct Hsem as [sub0' [Hsub0' Hsm']]; subst sm'.
    rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
    pose proof (SemAction_implRegionsFetchDeqRp_preserves_spec rs addr _ _ _ Hsub0') as Heq.
    unfold StateRel.projImplMemSpecState.
    cbn [child0Path implMemTree readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst] in *.
    exact Heq.
  Qed.

End MemFetchChannelLemmas.

(* ===========================================================================
 * 3. SCOREBOARD `mulDivWaitMask` & `regRead` COMMUTATION WITH `flushMulDiv`
 * =========================================================================== *)

Section RegReadScoreboardLemmas.
  Variable pcAddrInit : Z.

  Local Abbreviation rTree := (RfTree pcAddrInit).
  Local Opaque gprPathsWithKind.

  Definition evalRegRead (regReadIn : type RegReadIn) (rf : RfState pcAddrInit)
    : type AluInInstGroup :=
    let decodeOut : type DecodeOut           := evalExpr (##regReadIn`"decodeOut") in
    let fetchExc  : type FetchException      := evalExpr (##regReadIn`"fetchExc") in
    let cs1Idx    : type (Bit RegIdxSzReal)  := evalExpr (##decodeOut`"cs1Idx") in
    let cs2Idx    : type (Bit RegIdxSzReal)  := evalExpr (##decodeOut`"cs2Idx") in
    let cs1Raw    : type FullECapWithTag     := evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf in
    let cs1       : type FullECapWithTag     := evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw) in
    let cs2Raw    : type FullECapWithTag     := evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf in
    let cs2       : type FullECapWithTag     := evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw) in
    evalExpr (STRUCT {
      "writesCd"        ::= ##decodeOut`"writesCd" ;
      "readWriteScrIdx" ::= ##decodeOut`"readWriteScrIdx" ;
      "readWriteCsrIdx" ::= ##decodeOut`"readWriteCsrIdx" ;
      "inst"            ::= ##regReadIn`"inst" ;
      "decodeExc"       ::= ##decodeOut`"decodeExc" ;
      "fetchExc"        ::= #fetchExc ;
      "cs1"             ::= #cs1 ;
      "cs2"             ::= #cs2 ;
      "instGroup"       ::= ##decodeOut`"instGroup"
    } : Expr type AluInInstGroup).

  Lemma evalActionPropGen_regRead :
    forall {env : Env (RfTree pcAddrInit)}
           (regReadIn : type RegReadIn) (rf : RfState pcAddrInit) P,
      evalActionPropGen env (@regRead pcAddrInit type regReadIn) rf P <->
      P rf (evalRegRead regReadIn rf).
  Proof.
    intros env regReadIn rf P.
    unfold regRead, evalRegRead.
    split; intros H.
    - cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_readRegsList (gprPathsWithKind pcAddrInit) _ _ _)) in H.
      cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_readRegsList (gprPathsWithKind pcAddrInit) _ _ _)) in H.
      cbn [evalActionPropGen] in H; exact H.
    - cbn [evalActionPropGen].
      apply (proj2 (evalActionPropGen_readRegsList (gprPathsWithKind pcAddrInit) _ _ _)).
      cbn [evalActionPropGen].
      apply (proj2 (evalActionPropGen_readRegsList (gprPathsWithKind pcAddrInit) _ _ _)).
      cbn [evalActionPropGen]; exact H.
  Qed.

  Lemma SemAction_regRead_iff :
    forall {env : Env (RfTree pcAddrInit)}
           (regReadIn : type RegReadIn) (rf rf' : RfState pcAddrInit) (out : type AluInInstGroup),
      SemAction env (@regRead pcAddrInit type regReadIn) rf rf' out <->
      rf' = rf /\ out = evalRegRead regReadIn rf.
  Proof.
    intros env regReadIn rf rf' out.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_regRead.
    split; intros [H1 H2]; subst; split; reflexivity.
  Qed.

  Lemma mulDivWaitMask_false_inv :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           (baseMask : bits RegIdxSzReal -> bool)
           (idx : bits RegIdxSzReal),
      mulDivWaitMask entries baseMask idx = false ->
      baseMask idx = false /\
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         idx <> dstIdx).
  Proof.
    intros entries baseMask idx Hmask.
    unfold mulDivWaitMask in Hmask.
    apply orb_false_iff in Hmask as [Hbase Hexists].
    split; [exact Hbase |].
    induction entries as [| [d r] rest IH]; intros dstIdx resCap Hin Hnz Heq.
    - contradiction.
    - cbn [existsb] in Hexists.
      apply orb_false_iff in Hexists as [Hdr Hrest].
      destruct Hin as [Hin | Hin].
      + inversion Hin; subst d r idx.
        rewrite Hnz, Zmod.eqb_refl in Hdr; discriminate Hdr.
      + exact (IH Hrest dstIdx resCap Hin Hnz Heq).
  Qed.

  Lemma evalExpr_ITE0_isNotZero_regIdx :
    forall (idx : type (Bit RegIdxSzReal)) (v1 v2 : type FullECapWithTag),
      (Zmod.eqb idx Zmod.zero = false -> v1 = v2) ->
      evalExpr (ITE0 (isNotZero #idx) #v1) = evalExpr (ITE0 (isNotZero #idx) #v2).
  Proof.
    intros idx v1 v2 Heq.
    unfold ITE0.
    set (defCap := Const type FullECapWithTag (getDefault FullECapWithTag)).
    cbn [evalExpr isNotZero isZero evalNot isEq KindCustomInd].
    change (getDefault (Bit RegIdxSzReal)) with (@Zmod.zero (2 ^ RegIdxSzReal)).
    destruct (Zmod.eqb idx Zmod.zero) eqn:Hz; cbn [negb].
    - reflexivity.
    - rewrite (Heq eq_refl); reflexivity.
  Qed.

  Lemma evalRegRead_writeGprVal :
    forall (dstIdx : bits RegIdxSzReal) (resCap : type FullECapWithTag)
           (regReadIn : type RegReadIn) (rf : RfState pcAddrInit),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb cs1Idx Zmod.zero = false ->
       cs1Idx <> dstIdx) ->
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb cs2Idx Zmod.zero = false ->
       cs2Idx <> dstIdx) ->
      evalRegRead regReadIn (writeGprVal pcAddrInit dstIdx resCap rf) =
      evalRegRead regReadIn rf.
  Proof.
    intros dstIdx resCap regReadIn rf decodeOut cs1Idx cs2Idx Hcs1 Hcs2.
    unfold writeGprVal.
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hdst; cbn [negb].
    - reflexivity.
    - unfold evalRegRead; fold decodeOut cs1Idx cs2Idx.
      set (rf' := evalWriteRegsList (gprPathsWithKind pcAddrInit) dstIdx resCap rf).
      set (cs1Raw1 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf').
      set (cs1Raw0 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs1Idx rf).
      set (cs2Raw1 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf').
      set (cs2Raw0 := evalReadRegsList (gprPathsWithKind pcAddrInit) cs2Idx rf).
      replace (evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw1))
        with (evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw0)).
      + replace (evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw1))
          with (evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw0)).
        * reflexivity.
        * symmetry; apply evalExpr_ITE0_isNotZero_regIdx; intros Hc2.
          unfold cs2Raw1, cs2Raw0, rf'.
          rewrite evalReadRegsList_evalWriteRegsList_other;
            [reflexivity | apply NoDup_gprPathsWithKind | exact (Hcs2 eq_refl Hc2)].
      + symmetry; apply evalExpr_ITE0_isNotZero_regIdx; intros Hc1.
        unfold cs1Raw1, cs1Raw0, rf'.
        rewrite evalReadRegsList_evalWriteRegsList_other;
          [reflexivity | apply NoDup_gprPathsWithKind | exact (Hcs1 eq_refl Hc1)].
  Qed.

  Theorem evalRegRead_flushMulDivCaps :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           (regReadIn : type RegReadIn)
           (rf : RfState pcAddrInit),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs2Idx") in
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb cs1Idx Zmod.zero = false ->
         cs1Idx <> dstIdx) ->
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb cs2Idx Zmod.zero = false ->
         cs2Idx <> dstIdx) ->
      evalRegRead regReadIn (flushMulDivCaps pcAddrInit entries rf) =
      evalRegRead regReadIn rf.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH];
      intros regReadIn rf decodeOut cs1Idx cs2Idx Hcs1 Hcs2; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH.
      + apply evalRegRead_writeGprVal.
        * intros Hdst Hc1; exact (Hcs1 dstIdx resCap (or_introl eq_refl) Hdst Hc1).
        * intros Hdst Hc2; exact (Hcs2 dstIdx resCap (or_introl eq_refl) Hdst Hc2).
      + intros d r Hin Hdst Hc1; exact (Hcs1 d r (or_intror Hin) Hdst Hc1).
      + intros d r Hin Hdst Hc2; exact (Hcs2 d r (or_intror Hin) Hdst Hc2).
  Qed.

End RegReadScoreboardLemmas.

(* ===========================================================================
 * 4. CORE-LEVEL FRAME LEMMAS (`fetchRq`, `fetchAssemble`, `decodeAndRegRead`)
 * =========================================================================== *)

Section CoreStageFrameLemmas.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable rev : @RevokerInstance implRevokerExtraChildren regions.

  Local Abbreviation rTree := (RfTree pcAddrInit).
  Local Abbreviation bpT := BpTree.
  Local Abbreviation mTree := (ImplMemSubTree regions).
  Local Abbreviation fTree := (FetchTree pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (DecodeTree decodeCapacity).
  Local Abbreviation eTree := ExecuteTree.
  Local Abbreviation dmTree := (DataMemTree dataMemCapacity).
  Local Abbreviation mdTree := (MulDivSubTree mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree rTree bpT mTree fTree decTree eTree dmTree mdTree).

  Local Abbreviation noInstIfc := (fun ty => @implNoInstIfc ty).
  Local Abbreviation withInstIfc := (fun ty => @implWithInstIfc noInstIfc ty).
  Local Abbreviation memIfc := (fun ty => @implMemIfc config regions ty rev).
  Local Abbreviation fetchIfc := (fun ty => @implFetchIfc pcAddrInit fetchCapacity instCapacity ty).
  Local Abbreviation executeIfc := (fun ty => @implExecuteIfc ty).
  Local Abbreviation dataMemIfc := (fun ty => @implDataMemIfc dataMemCapacity ty).

  Lemma evalActionPropGen_LetAction :
    forall {t : Tree Elem} {k k' : Kind} {env : Env t} (s : string)
           (a : @Action type t k') (cont : type k' -> @Action type t k)
           (s0 : TreeState ElemState t) P,
      evalActionPropGen env (LetAction s a cont) s0 P ->
      evalActionPropGen env a s0 (fun midState midRet => evalActionPropGen env (cont midRet) midState P).
  Proof. exact (fun _ _ _ _ _ _ _ _ _ H => H). Qed.

  Lemma evalActionPropGen_LetExp_ex :
    forall {t : Tree Elem} {k k' : Kind} {env : Env t} (s : string) (e : Expr type k')
           (cont : type k' -> @Action type t k)
           (s0 : TreeState ElemState t) P,
      evalActionPropGen env (LetExp s e cont) s0 P ->
      exists v : type k', evalActionPropGen env (cont v) s0 P.
  Proof. intros t k k' env s e cont s0 P H; exists (evalExpr e); exact H. Qed.

  Lemma evalActionPropGen_IfElse_or :
    forall {t : Tree Elem} {k k' : Kind} {env : Env t} (s : string) (p : Expr type Bool)
           (t_branch f_branch : @Action type t k') (cont : type k' -> @Action type t k)
           (s0 : TreeState ElemState t) P,
      evalActionPropGen env (IfElse s p t_branch f_branch cont) s0 P ->
      evalActionPropGen env t_branch s0 (fun midState midRet => evalActionPropGen env (cont midRet) midState P) \/
      evalActionPropGen env f_branch s0 (fun midState midRet => evalActionPropGen env (cont midRet) midState P).
  Proof.
    intros t k k' env s p tb fb cont s0 P H; cbn [evalActionPropGen] in H.
    destruct (evalExpr p); [left | right]; exact H.
  Qed.

  Lemma evalActionPropGen_Return_ex :
    forall {t : Tree Elem} {k : Kind} {env : Env t} (e : Expr type k)
           (s0 : TreeState ElemState t) P,
      evalActionPropGen env (Return e) s0 P ->
      exists v : type k, P s0 v.
  Proof. intros t k env e s0 P H; exists (evalExpr e); exact H. Qed.

  Lemma evalActionPropGen_toAction_ex :
    forall {t : Tree Elem} {k : Kind} {env : Env t} (le : LetExpr type k)
           (s0 : TreeState ElemState t) P,
      evalActionPropGen env (@toAction type t k le) s0 P ->
      exists v : type k, P s0 v.
  Proof.
    intros t k env le s0 P H.
    apply (proj1 (evalActionPropGen_toAction le s0 P)) in H.
    exists (evalLetExpr le); exact H.
  Qed.

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList
               toAction evalLetExpr preDecode preDecodeBranch wrappedDecode.

  Lemma SemAction_readRegsList :
    forall {k sz t} {env : Env t} (paths : list (RegOfKind (t:=t) k))
           (idx : Expr type (Bit sz))
           (s s' : TreeState ElemState t) (out : type k),
      SemAction env (@readRegsList type k sz t paths idx) s s' out ->
      s' = s /\ out = evalReadRegsList paths (evalExpr idx) s.
  Proof.
    intros k sz t env paths idx s s' out Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_readRegsList paths _ _ _)) in Hsem.
    destruct Hsem as [-> <-]; split; reflexivity.
  Qed.

  (* --- 4A. `fetchRq` Core-Level Frame --- *)

  Theorem fetchRq_core_frame :
    forall {env : Env cTree}
           (c c' : TreeState ElemState cTree) (v : bits 0),
      SemAction env
        (@fetchRq pcAddrInit fetchCapacity instCapacity
                  noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type)
        c c' v ->
      c'.(Fst) = c.(Fst) /\
      c'.(Snd).(Fst) = c.(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd) /\
      fetch_instFifo pcAddrInit fetchCapacity instCapacity (c'.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) =
        fetch_instFifo pcAddrInit fetchCapacity instCapacity (c.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) /\
      (c'.(Snd).(Snd).(Snd).(Fst).(Fst) = c.(Snd).(Snd).(Snd).(Fst).(Fst) \/
       (exec_fenceIPending (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) = false /\
        exists (envMem : Env (implMemTree regions)) alignedPc canEnq,
          SemAction envMem (liftAction child0Path (@implRegionsFetchLineReadRq type regions alignedPc))
            (c.(Snd).(Snd).(Snd).(Fst).(Fst))
            (c'.(Snd).(Snd).(Snd).(Fst).(Fst))
            canEnq)).
  Proof.
    intros env c c' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    unfold fetchRq in Hsem.
    cbn [evalActionPropGen] in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@np_fetchFifo pcAddrInit fetchCapacity instCapacity
                                   noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem.
    cbn [evalActionPropGen isFull] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    cbn [evalActionPropGen] in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_execute pcAddrInit fetchCapacity instCapacity
                                           noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem.
    cbn [evalActionPropGen execute_readFenceIPend implExecuteIfc readFenceIPending] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_mem pcAddrInit fetchCapacity instCapacity
                                       noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [m1 [fenceIWait [Hm1 Hsem1]]].
    pose proof (SemAction_implMemReadFenceIWait_preserves_state regions _ _ _ Hm1) as Hm1_eq.
    subst m1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    cbn [evalActionPropGen] in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_fetch pcAddrInit fetchCapacity instCapacity
                                         noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    cbn [evalActionPropGen readFetchPc] in Hsem1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_execute pcAddrInit fetchCapacity instCapacity
                                           noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    cbn [evalActionPropGen execute_readExecEpoch implExecuteIfc readExecEpoch] in Hsem1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_fetch pcAddrInit fetchCapacity instCapacity
                                         noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    cbn [evalActionPropGen readPredEpoch] in Hsem1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_rf pcAddrInit fetchCapacity instCapacity
                                      noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [rf1 [pcc [Hrf1 Hsem2]]].
    apply SemAction_readRegsList in Hrf1 as [-> _].
    rewrite !writeSubTreeState_readSubTreeState in Hsem2.
    clear Hsem1; rename Hsem2 into Hsem1.
    cbn [evalActionPropGen] in Hsem1.
    lazymatch type of Hsem1 with
    | context[if ?cond then _ else _] => destruct cond eqn:Hcond
    end.
    - (* Precondition holds *)
      assert (Hfip : exec_fenceIPending (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) = false).
      { cbn [evalExpr fold_left map evalAndBinary evalBinary evalNot KindCustomInd InvDefault andb] in Hcond.
        apply andb_prop in Hcond as [Hcond _].
        apply andb_prop in Hcond as [_ Hfip'].
        apply negb_true_iff in Hfip'; exact Hfip'. }
      cbn [evalActionPropGen] in Hsem1.
      lazymatch type of Hsem1 with
      | context[if evalExpr (Var type Bool ?hp) then _ else _] => destruct hp eqn:Hhp
      end.
      + (* hasPreFault = true *)
        change (evalExpr (Var type Bool true)) with true in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        change (evalExpr (Var type Bool (evalExpr (ConstBool true)))) with true in Hsem1.
        change (evalExpr (Not (Var type Bool true))) with false in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        apply (proj1 (evalActionPropGen_liftAction
                        (@np_fetchFifo pcAddrInit fetchCapacity instCapacity
                                       noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [ff' [_ [_ Hsem2]]].
        apply (proj1 (evalActionPropGen_liftAction
                        (@ImplFetch.np_fetch pcAddrInit fetchCapacity instCapacity
                                             noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem2.
        cbn [evalActionPropGen writeFetchPc] in Hsem2.
        destruct Hsem2 as [<- _].
        repeat split; try reflexivity; left; reflexivity.
      + (* hasPreFault = false *)
        change (evalExpr (Var type Bool false)) with false in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        apply (proj1 (evalActionPropGen_liftAction
                        (@ImplFetch.np_mem pcAddrInit fetchCapacity instCapacity
                                           noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [m2 [canEnq [Hm2 Hsem2]]].
        cbn [evalActionPropGen] in Hsem2.
        change (evalExpr (Var type Bool canEnq)) with canEnq in Hsem2.
        destruct canEnq.
        * change (evalExpr (Not (Var type Bool false))) with true in Hsem2.
          cbn [evalActionPropGen] in Hsem2.
          apply (proj1 (evalActionPropGen_liftAction
                          (@np_noInst pcAddrInit fetchCapacity instCapacity
                                      noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem2.
          destruct (evalActionPropGen_to_SemAction _ _ _ Hsem2) as [ni' [noInstOut [_ Hsem3]]].
          cbn [evalActionPropGen] in Hsem3.
          apply (proj1 (evalActionPropGen_liftAction
                          (@np_fetchFifo pcAddrInit fetchCapacity instCapacity
                                         noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem3.
          destruct (evalActionPropGen_to_SemAction _ _ _ Hsem3) as [ff' [_ [_ Hsem4]]].
          apply (proj1 (evalActionPropGen_liftAction
                          (@ImplFetch.np_fetch pcAddrInit fetchCapacity instCapacity
                                               noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem4.
          cbn [evalActionPropGen writeFetchPc] in Hsem4.
          destruct Hsem4 as [<- _].
          repeat split; try reflexivity.
          right; split; [exact Hfip |].
          eexists _, _, true; exact Hm2.
        * cbn [evalActionPropGen] in Hsem2.
          destruct Hsem2 as [<- _].
          repeat split; try reflexivity.
          right; split; [exact Hfip |].
          eexists _, _, false; exact Hm2.
    - (* Precondition false *)
      cbn [evalActionPropGen] in Hsem1.
      destruct Hsem1 as [<- _].
      repeat split; try reflexivity; left; reflexivity.
  Qed.

  (* --- Compositional `preserves_rel` Combinators --- *)

  Definition preserves_rel {t : Tree Elem}
    (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
    {k : Kind} (a : @Action type t k) : Prop :=
    forall (env : Env t) s s' v, SemAction env a s s' v -> R s' s.

  Lemma preserves_rel_Return :
    forall {t : Tree Elem} (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
           (Hrefl : forall s, R s s) {k : Kind} (e : Expr type k),
      preserves_rel R (Return e).
  Proof.
    intros t R Hrefl k e env s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [<- _]; apply Hrefl.
  Qed.

  Lemma preserves_rel_LetExp :
    forall {t : Tree Elem} (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
           {k k' : Kind} (nm : string) (e : Expr type k') (cont : type k' -> @Action type t k),
      (forall x, preserves_rel R (cont x)) ->
      preserves_rel R (LetExp nm e cont).
  Proof.
    intros t R k k' nm e cont Hcont env s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    rewrite <- SemAction_iff_evalActionPropGen in Hsem.
    eapply Hcont; exact Hsem.
  Qed.

  Lemma preserves_rel_LetAction :
    forall {t : Tree Elem} (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
           (Htrans : forall s1 s2 s3, R s3 s2 -> R s2 s1 -> R s3 s1)
           {k k' : Kind} (nm : string) (a : @Action type t k') (cont : type k' -> @Action type t k),
      preserves_rel R a ->
      (forall x, preserves_rel R (cont x)) ->
      preserves_rel R (LetAction nm a cont).
  Proof.
    intros t R Htrans k k' nm a cont Ha Hcont env s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    apply (evalActionPropGen_to_SemAction a s _) in Hsem as [midState [midRet [H1 H2]]].
    rewrite <- SemAction_iff_evalActionPropGen in H2.
    eapply Htrans; [eapply Hcont; exact H2 | eapply Ha; exact H1].
  Qed.

  Lemma preserves_rel_IfElse :
    forall {t : Tree Elem} (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
           (Htrans : forall s1 s2 s3, R s3 s2 -> R s2 s1 -> R s3 s1)
           {k k' : Kind} (nm : string) (p : Expr type Bool)
           (tb fb : @Action type t k') (cont : type k' -> @Action type t k),
      preserves_rel R tb ->
      preserves_rel R fb ->
      (forall x, preserves_rel R (cont x)) ->
      preserves_rel R (IfElse nm p tb fb cont).
  Proof.
    intros t R Htrans k k' nm p tb fb cont Htb Hfb Hcont env s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    destruct (evalExpr p).
    - apply (evalActionPropGen_to_SemAction tb s _) in Hsem as [midState [midRet [H1 H2]]].
      rewrite <- SemAction_iff_evalActionPropGen in H2.
      eapply Htrans; [eapply Hcont; exact H2 | eapply Htb; exact H1].
    - apply (evalActionPropGen_to_SemAction fb s _) in Hsem as [midState [midRet [H1 H2]]].
      rewrite <- SemAction_iff_evalActionPropGen in H2.
      eapply Htrans; [eapply Hcont; exact H2 | eapply Hfb; exact H1].
  Qed.

  Lemma preserves_rel_toAction :
    forall {t : Tree Elem} (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
           (Hrefl : forall s, R s s) {k : Kind} (le : LetExpr type k),
      preserves_rel R (@toAction type t k le).
  Proof.
    intros t R Hrefl k le env s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_toAction le s _)) in Hsem as [<- _].
    apply Hrefl.
  Qed.

  Lemma preserves_rel_liftAction :
    forall {t : Tree Elem} (R : TreeState ElemState t -> TreeState ElemState t -> Prop)
           (p : NodePath t) {k : Kind} (a : @Action type (getNode p) k),
      (forall envSub s sub' v, SemAction envSub a (readSubTreeState p s) sub' v -> R (writeSubTreeState p s sub') s) ->
      preserves_rel R (@liftAction type t p k a).
  Proof.
    intros t R p k a Hlift env s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction p a s _)) in Hsem.
    apply (evalActionPropGen_to_SemAction a (readSubTreeState p s) _) in Hsem
      as [sub' [ret' [Hsub [<- _]]]].
    eapply Hlift; exact Hsub.
  Qed.

  (* --- 4B. `fetchAssemble` Core-Level Frame --- *)

  Definition fetchAssemble_rel (c' c : TreeState ElemState cTree) : Prop :=
    c'.(Fst) = c.(Fst) /\
    c'.(Snd).(Fst) = c.(Snd).(Fst) /\
    c'.(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd) /\
    projImplMemSpecState regions (c'.(Snd).(Snd).(Snd).(Fst).(Fst)) =
      projImplMemSpecState regions (c.(Snd).(Snd).(Snd).(Fst).(Fst)).

  Lemma fetchAssemble_rel_refl : forall c, fetchAssemble_rel c c.
  Proof. intro c; unfold fetchAssemble_rel; repeat split; reflexivity. Qed.

  Lemma fetchAssemble_rel_trans :
    forall c1 c2 c3, fetchAssemble_rel c3 c2 -> fetchAssemble_rel c2 c1 -> fetchAssemble_rel c3 c1.
  Proof.
    intros c1 c2 c3 [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]].
    unfold fetchAssemble_rel; repeat split; congruence.
  Qed.

  Local Ltac solve_fetchAssemble_lift :=
    intros envSub s sub' v Hsub;
    try (
      unfold mem_getInstRp, implMemIfc in Hsub;
      pose proof (SemAction_implMemFetchRp_preserves_state regions _ _ _ _ Hsub) as HrpEq;
      subst sub'
    );
    try (
      unfold mem_deqInstRp, implMemIfc in Hsub;
      pose proof (SemAction_implMemFetchDeqRp_preserves_spec regions _ _ _ _ Hsub) as HdeqEq;
      cbn [ImplFetch.np_mem readSubTreeState readSubTreeState_child Fst Snd] in HdeqEq
    );
    try (
      unfold execute_readExecEpoch, implExecuteIfc, readExecEpoch in Hsub;
      apply InversionSemAction in Hsub;
      apply InversionSemAction in Hsub as [HexEq _];
      subst sub'
    );
    try (
      apply SemAction_readRegsList in Hsub as [HrfEq _];
      subst sub'
    );
    unfold fetchAssemble_rel;
    cbn [ImplFetch.np_mem ImplFetch.np_fetch np_fetchFifo np_instFifo
         ImplFetch.np_bp np_noInst ImplFetch.np_execute ImplFetch.np_rf
         writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child Fst Snd];
    repeat split; try reflexivity; eauto.

  Theorem fetchAssemble_core_frame :
    forall {env : Env cTree}
           (c c' : TreeState ElemState cTree) (v : bits 0),
      SemAction env
        (@fetchAssemble pcAddrInit fetchCapacity instCapacity
                        noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type)
        c c' v ->
      c'.(Fst) = c.(Fst) /\
      c'.(Snd).(Fst) = c.(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd) /\
      projImplMemSpecState regions (c'.(Snd).(Snd).(Snd).(Fst).(Fst)) =
        projImplMemSpecState regions (c.(Snd).(Snd).(Snd).(Fst).(Fst)).
  Proof.
    change (preserves_rel fetchAssemble_rel
              (@fetchAssemble pcAddrInit fetchCapacity instCapacity
                              noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type)).
    unfold fetchAssemble.
    repeat lazymatch goal with
    | |- forall _, _ => intro
    | |- preserves_rel _ (LetAction _ _ _) =>
        apply (preserves_rel_LetAction _ fetchAssemble_rel_trans)
    | |- preserves_rel _ (LetExp _ _ _) =>
        apply preserves_rel_LetExp
    | |- preserves_rel _ (IfElse _ _ _ _ _) =>
        apply (preserves_rel_IfElse _ fetchAssemble_rel_trans)
    | |- preserves_rel _ (Return _) =>
        apply (preserves_rel_Return _ fetchAssemble_rel_refl)
    | |- preserves_rel _ (@toAction _ _ _ _) =>
        apply (preserves_rel_toAction _ fetchAssemble_rel_refl)
    | |- preserves_rel _ (@liftAction _ _ _ _ _) =>
        apply preserves_rel_liftAction; solve_fetchAssemble_lift
    end.
  Qed.

  (* --- 4C. `decodeAndRegRead` Core-Level Frame --- *)

  Definition decodeAndRegRead_rel (c' c : TreeState ElemState cTree) : Prop :=
    c'.(Fst) = c.(Fst) /\
    c'.(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Fst) /\
    c'.(Snd).(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Snd).(Fst) /\
    c'.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).

  Lemma decodeAndRegRead_rel_refl : forall c, decodeAndRegRead_rel c c.
  Proof. intro c; unfold decodeAndRegRead_rel; repeat split; reflexivity. Qed.

  Lemma decodeAndRegRead_rel_trans :
    forall c1 c2 c3, decodeAndRegRead_rel c3 c2 -> decodeAndRegRead_rel c2 c1 -> decodeAndRegRead_rel c3 c1.
  Proof.
    intros c1 c2 c3 [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]].
    unfold decodeAndRegRead_rel; repeat split; congruence.
  Qed.

  Local Ltac solve_decodeAndRegRead_lift :=
    intros envSub s sub' v Hsub;
    try (
      unfold execute_readExecEpoch, implExecuteIfc, readExecEpoch in Hsub;
      apply InversionSemAction in Hsub;
      apply InversionSemAction in Hsub as [HexEq _];
      subst sub'
    );
    try (
      apply SemAction_regRead_iff in Hsub as [HrfEq _];
      subst sub'
    );
    unfold decodeAndRegRead_rel;
    cbn [ImplDecode.np_decode np_decodeToAluFifo ImplDecode.np_fetch
         ImplDecode.np_execute ImplDecode.np_rf ImplDecode.np_waitBits
         writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child Fst Snd];
    repeat split; reflexivity.

  Theorem decodeAndRegRead_core_frame :
    forall {env : Env cTree}
           (c c' : TreeState ElemState cTree) (v : bits 0),
      SemAction env
        (@decodeAndRegRead decodeCapacity pcAddrInit
                           bpT mdTree fetchIfc executeIfc dataMemIfc memIfc type)
        c c' v ->
      c'.(Fst) = c.(Fst) /\
      c'.(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).
  Proof.
    change (preserves_rel decodeAndRegRead_rel
              (@decodeAndRegRead decodeCapacity pcAddrInit
                                 bpT mdTree fetchIfc executeIfc dataMemIfc memIfc type)).
    unfold decodeAndRegRead.
    repeat lazymatch goal with
    | |- forall _, _ => intro
    | |- preserves_rel _ (LetAction _ _ _) =>
        apply (preserves_rel_LetAction _ decodeAndRegRead_rel_trans)
    | |- preserves_rel _ (LetExp _ _ _) =>
        apply preserves_rel_LetExp
    | |- preserves_rel _ (IfElse _ _ _ _ _) =>
        apply (preserves_rel_IfElse _ decodeAndRegRead_rel_trans)
    | |- preserves_rel _ (Return _) =>
        apply (preserves_rel_Return _ decodeAndRegRead_rel_refl)
    | |- preserves_rel _ (@toAction _ _ _ _) =>
        apply (preserves_rel_toAction _ decodeAndRegRead_rel_refl)
    | |- preserves_rel _ (@liftAction _ _ _ _ _) =>
        apply preserves_rel_liftAction; solve_decodeAndRegRead_lift
    end.
  Qed.

End CoreStageFrameLemmas.

(* ===========================================================================
 * 5. SYSTEM-LEVEL SIMULATION FOR FETCH, DECODE & `setCanProceedSteps`
 * =========================================================================== *)

Section FetchDecodeSystemSim.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : @ClintInstance regions.
  Variable rev : @RevokerInstance implRevokerExtraChildren regions.
  Variable revSpec : @RevokerInstance [] regions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation SState := (SpecState pcAddrInit regions).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
  Local Abbreviation specMod := (@spec pcAddrInit config regions clint revSpec plic).
  Local Abbreviation sRel :=
    (stateRel pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation implRf :=
    (@SimDevices.implRf pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implWaitBits :=
    (@SimDevices.implWaitBits pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implBp :=
    (@SimDevices.implBp pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implMem :=
    (@SimDevices.implMem pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implFetch :=
    (@SimDevices.implFetch pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implDecode :=
    (@SimDevices.implDecode pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implExecute :=
    (@SimDevices.implExecute pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implDataMem :=
    (@SimDevices.implDataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implMulDiv :=
    (@SimDevices.implMulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList
               toAction evalLetExpr preDecode preDecodeBranch wrappedDecode.

  (* --- 5A. General Stuttering & Frontend `stateRel` Preservation Helpers --- *)

  Theorem spec_stutter :
    forall {env2 : Env sTree} (s2 : SState),
      SemActions env2 (specMod type) s2 s2.
  Proof.
    intros env2 s2; apply NilAction; reflexivity.
  Qed.

  Lemma stateRel_preserved_by_frontend_step :
    forall (s1 s1' : IState) (s2 : SState),
      sRel s1 s2 ->
      impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 ->
      StateRel.projImplMemSpecState regions
        (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1') =
        StateRel.projImplMemSpecState regions
          (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1) ->
      impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 ->
      impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 ->
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      (FenceIInv pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      sRel s1' s2.
  Proof.
    intros s1 s1' s2 Hrel Hrf Hmem Hexec Hdm Hmd Hfence.
    exact (stateRel_step_stutter pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  (* --- 5B. `setCanProceedSteps` Simulation (`setFetchCanProceedStage`, `setDecodeCanProceedStage`, `setExecuteCanProceedStage`) --- *)

  Theorem sim_setFetchCanProceedStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setFetchCanProceedStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setFetchCanProceedStage_inv pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s1' v Hsem)
      as [_ [_ [Hrf [_ [_ [Hmem [Hdecode [Hexec [Hdm [Hmd [_ [_ [_ [_ [_ HrestFetch]]]]]]]]]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      rewrite Hmem; reflexivity.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive,
             StateRel.fetch_instFifo, fetch_instFifo in *.
      change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_decode pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      change (impl_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      split.
      + rewrite Hexec, Hdm, Hmem, Hdecode, HrestFetch.
        exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  Theorem sim_setDecodeCanProceedStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setDecodeCanProceedStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setDecodeCanProceedStage_inv pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s1' v Hsem)
      as [_ [_ [Hrf [_ [_ [Hmem [Hfetch [Hexec [Hdm [Hmd [_ HrestDec]]]]]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      rewrite Hmem; reflexivity.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive,
             StateRel.decode_toAluFifo, decode_toAluFifo in *.
      change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      change (impl_decode pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      split.
      + rewrite Hexec, Hdm, Hmem, Hfetch, HrestDec.
        exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  Theorem sim_setExecuteCanProceedStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setExecuteCanProceedStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_setCanProceedSteps :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@setCanProceedSteps pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin Hsem Hrel.
    unfold setCanProceedSteps in Hin.
    destruct Hin as [<- | [<- | [<- | []]]].
    - exact (sim_setFetchCanProceedStage s1 s1' s2 v Hsem Hrel).
    - exact (sim_setDecodeCanProceedStage s1 s1' s2 v Hsem Hrel).
    - exact (sim_setExecuteCanProceedStage s1 s1' s2 v Hsem Hrel).
  Qed.

  (* --- 5C. `fetchRps` Simulation --- *)

  Theorem fetchRps_frame :
    forall {env1 : Env iTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (v : bits 0),
      In act
        (@fetchRps pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      s1' = writeSubTreeState
              (@Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions)
              s1 (implMem s1') /\
      implRf s1' = implRf s1 /\
      implWaitBits s1' = implWaitBits s1 /\
      implBp s1' = implBp s1 /\
      implFetch s1' = implFetch s1 /\
      implDecode s1' = implDecode s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1.
  Proof.
    intros env1 act s1 s1' v Hin Hsem.
    unfold fetchRps in Hin.
    apply in_map_iff in Hin as [memAct [<- HinMem]].
    apply (SemAction_lift_np_mem_impl pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions) in Hsem as [m1' [_ Hs1']].
    subst s1'; repeat split; reflexivity.
  Qed.

  Theorem sim_fetchRps :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@fetchRps pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      StateRel.projImplMemSpecState regions (implMem s1') =
        StateRel.projImplMemSpecState regions (implMem s1) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin Hsem Hmem Hrel.
    pose proof (fetchRps_frame act s1 s1' v Hin Hsem)
      as [_ [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hdm Hmd]]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      exact Hmem.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive in *.
      change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      change (impl_decode pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      split.
      + rewrite Hexec, Hfetch, Hdecode, Hdm, Hmem; exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  (* --- 5D. `fetchRqStage` Simulation --- *)

  Theorem fetchRqStage_frame :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      SemAction env1
        (@fetchRqStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      implRf s1' = implRf s1 /\
      implWaitBits s1' = implWaitBits s1 /\
      implDecode s1' = implDecode s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1 /\
      fetch_instFifo pcAddrInit fetchCapacity instCapacity (implFetch s1') =
        fetch_instFifo pcAddrInit fetchCapacity instCapacity (implFetch s1) /\
      (implMem s1' = implMem s1 \/
       (exec_fenceIPending (implExecute s1) = false /\
        exists (envMem : Env (implMemTree regions)) alignedPc canEnq,
          SemAction envMem (liftAction child0Path (@implRegionsFetchLineReadRq type regions alignedPc))
            (implMem s1) (implMem s1') canEnq)).
  Proof.
    intros env1 s1 s1' v Hsem.
    unfold fetchRqStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [Hc [Hs1' _]]]].
    subst s1'.
    pose proof (fetchRq_core_frame pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions rev (Fst s1) c' v' Hc)
      as [Hrf [Hwb [Hrest [Hinst Hmem]]]].
    unfold SimDevices.implRf, SimDevices.implWaitBits, SimDevices.implMem, SimDevices.implFetch,
           SimDevices.implDecode, SimDevices.implExecute, SimDevices.implDataMem, SimDevices.implMulDiv;
      cbn [writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child implSysTree Impl.np_core Fst Snd].
    rewrite Hrf, Hwb, Hrest, Hinst.
    repeat split; try reflexivity; exact Hmem.
  Qed.

  Theorem sim_fetchRqStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@fetchRqStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      StateRel.projImplMemSpecState regions (implMem s1') =
        StateRel.projImplMemSpecState regions (implMem s1) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hmem Hrel.
    pose proof (fetchRqStage_frame s1 s1' v Hsem)
      as [Hrf [_ [Hdecode [Hexec [Hdm [Hmd [Hinst _]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      exact Hmem.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive,
             StateRel.fetch_instFifo, fetch_instFifo in *.
      change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      change (impl_decode pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      split.
      + rewrite Hexec, Hinst, Hdecode, Hdm, Hmem; exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  (* --- 5E. `fetchAssembleStage` Simulation --- *)

  Theorem fetchAssembleStage_frame :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      SemAction env1
        (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      implRf s1' = implRf s1 /\
      implWaitBits s1' = implWaitBits s1 /\
      implDecode s1' = implDecode s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1 /\
      StateRel.projImplMemSpecState regions (implMem s1') =
        StateRel.projImplMemSpecState regions (implMem s1).
  Proof.
    intros env1 s1 s1' v Hsem.
    unfold fetchAssembleStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions) _ _ _)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [Hc [Hs1' _]]]].
    subst s1'.
    pose proof (fetchAssemble_core_frame pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions rev (Fst s1) c' v' Hc)
      as [Hrf [Hwb [Hrest Hmem]]].
    unfold SimDevices.implRf, SimDevices.implWaitBits, SimDevices.implMem,
           SimDevices.implDecode, SimDevices.implExecute, SimDevices.implDataMem, SimDevices.implMulDiv;
      cbn [writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child implSysTree Impl.np_core Fst Snd].
    rewrite Hrf, Hwb, Hrest.
    repeat split; try reflexivity; exact Hmem.
  Qed.

  Lemma evalActionPropGen_IfElse_false :
    forall {t : Tree Elem} {k k' : Kind} {env : Env t} (s : string) (p : Expr type Bool)
           (t_branch f_branch : @Action type t k') (cont : type k' -> @Action type t k)
           (s0 : TreeState ElemState t) P,
      evalExpr p = false ->
      evalActionPropGen env (IfElse s p t_branch f_branch cont) s0 P ->
      evalActionPropGen env f_branch s0 (fun midState midRet => evalActionPropGen env (cont midRet) midState P).
  Proof.
    intros t k k' env s p tb fb cont s0 P Hp H; cbn [evalActionPropGen] in H.
    rewrite Hp in H; exact H.
  Qed.

  Lemma SemAction_fetchAssembleStage_notCanProceed :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      fetch_canProceed pcAddrInit fetchCapacity instCapacity (implFetch s1) = false ->
      SemAction env1
        (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      s1' = s1 /\ v = Zmod.zero.
  Proof.
    intros env1 s1 s1' v Hcp Hsem.
    unfold fetchAssembleStage, fetchAssemble in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply evalActionPropGen_LetAction in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply (proj1 (evalActionPropGen_readFetchCanProceed _ _ _ _ _)) in Hsem.
    eapply evalActionPropGen_IfElse_false in Hsem; [| exact Hcp].
    cbn [evalActionPropGen] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    destruct Hsem as [<- <-]; split; reflexivity.
  Qed.

  Theorem sim_fetchAssembleStage_notCanProceed :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      fetch_canProceed pcAddrInit fetchCapacity instCapacity (implFetch s1) = false ->
      SemAction env1
        (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hcp Hsem Hrel.
    destruct (SemAction_fetchAssembleStage_notCanProceed s1 s1' v Hcp Hsem) as [-> _].
    exists s2; split; [apply spec_stutter | exact Hrel].
  Qed.

  Theorem sim_fetchAssembleStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      (FenceIInv pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hfence Hrel.
    pose proof (fetchAssembleStage_frame s1 s1' v Hsem)
      as [Hrf [_ [_ [Hexec [Hdm [Hmd Hmem]]]]]].
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf Hmem Hexec Hdm Hmd Hfence).
  Qed.

  (* --- 5F. `decodeAndRegReadStage` Simulation --- *)

  Theorem decodeAndRegReadStage_frame :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      SemAction env1
        (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      implRf s1' = implRf s1 /\
      implBp s1' = implBp s1 /\
      implMem s1' = implMem s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1.
  Proof.
    intros env1 s1 s1' v Hsem.
    unfold decodeAndRegReadStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions) _ _ _)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [Hc [Hs1' _]]]].
    subst s1'.
    pose proof (decodeAndRegRead_core_frame pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions rev (Fst s1) c' v' Hc)
      as [Hrf [Hbp [Hmem Hrest]]].
    unfold SimDevices.implRf, SimDevices.implBp, SimDevices.implMem,
           SimDevices.implExecute, SimDevices.implDataMem, SimDevices.implMulDiv;
      cbn [writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child implSysTree Impl.np_core Fst Snd].
    rewrite Hrf, Hbp, Hmem, Hrest.
    repeat split; reflexivity.
  Qed.

  Lemma SemAction_decodeAndRegReadStage_notCanProceed :
    forall {env1 : Env iTree}
           (s1 s1' : IState) (v : bits 0),
      decode_canProceed decodeCapacity (implDecode s1) = false ->
      SemAction env1
        (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      s1' = s1 /\ v = Zmod.zero.
  Proof.
    intros env1 s1 s1' v Hcp Hsem.
    unfold decodeAndRegReadStage, decodeAndRegRead in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply evalActionPropGen_LetAction in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply (proj1 (evalActionPropGen_readDecodeCanProceed _ _ _)) in Hsem.
    eapply evalActionPropGen_IfElse_false in Hsem; [| exact Hcp].
    cbn [evalActionPropGen] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    destruct Hsem as [<- <-]; split; reflexivity.
  Qed.

  Theorem sim_decodeAndRegReadStage_notCanProceed :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      decode_canProceed decodeCapacity (implDecode s1) = false ->
      SemAction env1
        (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hcp Hsem Hrel.
    destruct (SemAction_decodeAndRegReadStage_notCanProceed s1 s1' v Hcp Hsem) as [-> _].
    exists s2; split; [apply spec_stutter | exact Hrel].
  Qed.

  Theorem sim_decodeAndRegReadStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      (FenceIInv pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hfence Hrel.
    pose proof (decodeAndRegReadStage_frame s1 s1' v Hsem)
      as [Hrf [_ [Hmem [Hexec [Hdm Hmd]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      rewrite Hmem; reflexivity.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - exact Hfence.
  Qed.

  Theorem sim_fetchRps_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@fetchRps pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_fetchRqStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@fetchRqStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_fetchAssembleStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_decodeAndRegReadStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@decodeAndRegReadStage pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (specMod type) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

End FetchDecodeSystemSim.
