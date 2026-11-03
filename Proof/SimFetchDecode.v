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
