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
From Cheriot.Proof Require Export TreeLemmas StateRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. `implExecuteTree` AND `waitBitsTree` STATE ACCESSORS & ACTION LEMMAS
 * =========================================================================== *)

Section ExecuteTreeHelpers.
  Variable dom : string.

  Local Abbreviation eTree := (implExecuteTree dom).

  Definition ex_execEpoch (ex : TreeState DomainElemState eTree) : type Epoch :=
    ex.(Fst).

  Definition ex_fenceIPending (ex : TreeState DomainElemState eTree) : bool :=
    ex.(Snd).(Fst).

  Definition ex_canProceed (ex : TreeState DomainElemState eTree) : bool :=
    ex.(Snd).(Snd).(Fst).

  Definition ex_withExecEpoch (ex : TreeState DomainElemState eTree) (v : type Epoch)
    : TreeState DomainElemState eTree :=
    (v ,, ex.(Snd)).

  Definition ex_withFenceIPending (ex : TreeState DomainElemState eTree) (v : bool)
    : TreeState DomainElemState eTree :=
    (ex.(Fst) ,, (v ,, ex.(Snd).(Snd))).

  Definition ex_withCanProceed (ex : TreeState DomainElemState eTree) (v : bool)
    : TreeState DomainElemState eTree :=
    (ex.(Fst) ,, (ex.(Snd).(Fst) ,, (v ,, ex.(Snd).(Snd).(Snd)))).

  Lemma ex_execEpoch_withExecEpoch :
    forall ex v, ex_execEpoch (ex_withExecEpoch ex v) = v.
  Proof. reflexivity. Qed.

  Lemma ex_execEpoch_withFenceIPending :
    forall ex v, ex_execEpoch (ex_withFenceIPending ex v) = ex_execEpoch ex.
  Proof. reflexivity. Qed.

  Lemma ex_execEpoch_withCanProceed :
    forall ex v, ex_execEpoch (ex_withCanProceed ex v) = ex_execEpoch ex.
  Proof. reflexivity. Qed.

  Lemma ex_fenceIPending_withExecEpoch :
    forall ex v, ex_fenceIPending (ex_withExecEpoch ex v) = ex_fenceIPending ex.
  Proof. reflexivity. Qed.

  Lemma ex_fenceIPending_withFenceIPending :
    forall ex v, ex_fenceIPending (ex_withFenceIPending ex v) = v.
  Proof. reflexivity. Qed.

  Lemma ex_fenceIPending_withCanProceed :
    forall ex v, ex_fenceIPending (ex_withCanProceed ex v) = ex_fenceIPending ex.
  Proof. reflexivity. Qed.

  Lemma ex_canProceed_withExecEpoch :
    forall ex v, ex_canProceed (ex_withExecEpoch ex v) = ex_canProceed ex.
  Proof. reflexivity. Qed.

  Lemma ex_canProceed_withFenceIPending :
    forall ex v, ex_canProceed (ex_withFenceIPending ex v) = ex_canProceed ex.
  Proof. reflexivity. Qed.

  Lemma ex_canProceed_withCanProceed :
    forall ex v, ex_canProceed (ex_withCanProceed ex v) = v.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readExecEpoch :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@readExecEpoch dom type) ex P <->
      P ex (ex_execEpoch ex).
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_writeExecEpoch :
    forall {env : Env eTree} (val : type Epoch) (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@writeExecEpoch dom type val) ex P <->
      P (ex_withExecEpoch ex val) Zmod.zero.
  Proof.
    intros env val ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_readFenceIPending :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@readFenceIPending dom type) ex P <->
      P ex (ex_fenceIPending ex).
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_setFenceIPending :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@setFenceIPending dom type) ex P <->
      P (ex_withFenceIPending ex true) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_clearFenceIPending :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@clearFenceIPending dom type) ex P <->
      P (ex_withFenceIPending ex false) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_readExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@readExecuteCanProceed dom type) ex P <->
      P ex (ex_canProceed ex).
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_setExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@setExecuteCanProceed dom type) ex P <->
      P (ex_withCanProceed ex true) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_clearExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState DomainElemState eTree) P,
      evalActionPropGen env (@clearExecuteCanProceed dom type) ex P <->
      P (ex_withCanProceed ex false) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  (* Wait-bit helpers on `waitBitsTree dom` *)
  Definition evalReadWaitBit (idx : bits RegIdxSzReal)
    (wb : TreeState DomainElemState (waitBitsTree dom)) : bool :=
    evalReadRegsList (gprWaitPathsWithKind dom) idx wb.

  Definition evalWriteWaitBit (idx : bits RegIdxSzReal) (val : bool)
    (wb : TreeState DomainElemState (waitBitsTree dom))
    : TreeState DomainElemState (waitBitsTree dom) :=
    evalWriteRegsList (gprWaitPathsWithKind dom) idx val wb.

  Definition evalSetDstWaitBits (writesGpr : bool) (gprIdx : bits RegIdxSzReal) (val : bool)
    (wb : TreeState DomainElemState (waitBitsTree dom))
    : TreeState DomainElemState (waitBitsTree dom) :=
    if writesGpr then evalWriteWaitBit gprIdx val wb else wb.

  Local Opaque gprWaitPathsWithKind.

  Lemma evalActionPropGen_readGprWaitBit :
    forall {env : Env (waitBitsTree dom)} (idx : bits RegIdxSzReal)
           (wb : TreeState DomainElemState (waitBitsTree dom)) P,
      evalActionPropGen env (@readGprWaitBit dom type idx) wb P <->
      P wb (evalReadWaitBit idx wb).
  Proof.
    intros env idx wb P.
    unfold readGprWaitBit, evalReadWaitBit.
    apply (evalActionPropGen_readRegsList (gprWaitPathsWithKind dom) (Var type (Bit RegIdxSzReal) idx)).
  Qed.

  Lemma evalActionPropGen_writeGprWaitBit :
    forall {env : Env (waitBitsTree dom)} (idx : bits RegIdxSzReal) (val : bool)
           (wb : TreeState DomainElemState (waitBitsTree dom)) P,
      evalActionPropGen env (@writeGprWaitBit dom type idx val) wb P <->
      P (evalWriteWaitBit idx val wb) Zmod.zero.
  Proof.
    intros env idx val wb P.
    unfold writeGprWaitBit, evalWriteWaitBit.
    apply (evalActionPropGen_writeRegsList (gprWaitPathsWithKind dom) (Var type (Bit RegIdxSzReal) idx) (Var type Bool val)).
  Qed.

  Lemma evalActionPropGen_setDstWaitBits :
    forall {env : Env (waitBitsTree dom)} (writesGpr : bool) (gprIdx : bits RegIdxSzReal) (val : bool)
           (wb : TreeState DomainElemState (waitBitsTree dom)) P,
      evalActionPropGen env (@setDstWaitBits dom type writesGpr gprIdx val) wb P <->
      P (evalSetDstWaitBits writesGpr gprIdx val wb) Zmod.zero.
  Proof.
    intros env writesGpr gprIdx val wb P.
    unfold setDstWaitBits, evalSetDstWaitBits.
    destruct writesGpr; cbn [evalActionPropGen evalExpr].
    - rewrite evalActionPropGen_writeGprWaitBit.
      cbn [evalActionPropGen evalExpr]; reflexivity.
    - reflexivity.
  Qed.

End ExecuteTreeHelpers.

(* ===========================================================================
 * 2. `coreTree` SUBTREE ACCESSORS & UPDATERS
 * =========================================================================== *)

Section CoreTreeAccessors.
  Variable dom : string.
  Variable rfT bpT memT fetchT decodeT executeT dataMemT mulDivT : Tree DomainElem.

  Local Abbreviation cTree := (coreTree dom rfT bpT memT fetchT decodeT executeT dataMemT mulDivT).

  Definition core_rf (c : TreeState DomainElemState cTree) : TreeState DomainElemState rfT :=
    c.(Fst).(Fst).

  Definition core_waitBits (c : TreeState DomainElemState cTree) : TreeState DomainElemState (waitBitsTree dom) :=
    c.(Snd).(Fst).(Fst).

  Definition core_bp (c : TreeState DomainElemState cTree) : TreeState DomainElemState bpT :=
    c.(Snd).(Snd).(Fst).(Fst).

  Definition core_mem (c : TreeState DomainElemState cTree) : TreeState DomainElemState memT :=
    c.(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_fetch (c : TreeState DomainElemState cTree) : TreeState DomainElemState fetchT :=
    c.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_decode (c : TreeState DomainElemState cTree) : TreeState DomainElemState decodeT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_execute (c : TreeState DomainElemState cTree) : TreeState DomainElemState executeT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_dataMem (c : TreeState DomainElemState cTree) : TreeState DomainElemState dataMemT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_mulDiv (c : TreeState DomainElemState cTree) : TreeState DomainElemState mulDivT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_withRf (c : TreeState DomainElemState cTree)
    (v : TreeState DomainElemState rfT) : TreeState DomainElemState cTree :=
    ((v ,, c.(Fst).(Snd)) ,, c.(Snd)).

  Definition core_withWaitBits (c : TreeState DomainElemState cTree)
    (v : TreeState DomainElemState (waitBitsTree dom)) : TreeState DomainElemState cTree :=
    (c.(Fst) ,, ((v ,, c.(Snd).(Fst).(Snd)) ,, c.(Snd).(Snd))).

  Definition core_withExecute (c : TreeState DomainElemState cTree)
    (v : TreeState DomainElemState executeT) : TreeState DomainElemState cTree :=
    (c.(Fst) ,, (c.(Snd).(Fst) ,, (c.(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Fst) ,, (c.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))))).

  Definition core_withDataMem (c : TreeState DomainElemState cTree)
    (v : TreeState DomainElemState dataMemT) : TreeState DomainElemState cTree :=
    (c.(Fst) ,, (c.(Snd).(Fst) ,, (c.(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Fst) ,, (c.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))))).

  Definition core_withMulDiv (c : TreeState DomainElemState cTree)
    (v : TreeState DomainElemState mulDivT) : TreeState DomainElemState cTree :=
    (c.(Fst) ,, (c.(Snd).(Fst) ,, (c.(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Fst) ,, (c.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))))))).

End CoreTreeAccessors.

(* ===========================================================================
 * 3. `Alu` EXECUTION HELPERS (`isInterruptPending` AND `executeNonDeferred`)
 * =========================================================================== *)

Section AluExecutionLemmas.
  Variable dom : string.
  Variable pcAddrInit : Z.

  Local Abbreviation rTree := (rfTree dom pcAddrInit).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind.

  Definition evalIsInterruptPending (meip mtip : bool)
    (rf : TreeState DomainElemState rTree) : bool :=
    let mstatus := evalReadRegsList (csrPathsWithKind dom pcAddrInit) (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mstatus")) rf in
    let mie     := evalReadRegsList (csrPathsWithKind dom pcAddrInit) (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mie")) rf in
    let currMIE := evalExpr (@getMstatusMIE type (Var type (Bit Xlen) mstatus)) in
    let meie    := evalExpr (@getMieMEIE type (Var type (Bit Xlen) mie)) in
    let mtie    := evalExpr (@getMieMTIE type (Var type (Bit Xlen) mie)) in
    andb currMIE (orb (andb meip meie) (andb mtip mtie)).

  Lemma evalActionPropGen_isInterruptPending :
    forall {env : Env rTree} (meip mtip : bool) (rf : TreeState DomainElemState rTree) P,
      evalActionPropGen env (@isInterruptPending dom pcAddrInit type meip mtip) rf P <->
      P rf (evalIsInterruptPending meip mtip rf).
  Proof.
    intros env meip mtip rf P.
    unfold isInterruptPending, evalIsInterruptPending.
    cbn [evalActionPropGen].
    rewrite (evalActionPropGen_readRegsList (csrPathsWithKind dom pcAddrInit)
               ($(getCsrPhysicalIdx "mstatus") : Expr type (Bit CsrIdxSz))).
    cbn [evalActionPropGen].
    rewrite (evalActionPropGen_readRegsList (csrPathsWithKind dom pcAddrInit)
               ($(getCsrPhysicalIdx "mie") : Expr type (Bit CsrIdxSz))).
    cbn [evalActionPropGen].
    change (evalExpr ($(getCsrPhysicalIdx "mstatus") : Expr type (Bit CsrIdxSz)))
      with (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mstatus")).
    change (evalExpr ($(getCsrPhysicalIdx "mie") : Expr type (Bit CsrIdxSz)))
      with (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mie")).
    set (mstatus := evalReadRegsList (csrPathsWithKind dom pcAddrInit)
                      (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mstatus")) rf).
    set (mie := evalReadRegsList (csrPathsWithKind dom pcAddrInit)
                  (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mie")) rf).
    set (currMIE := evalExpr (@getMstatusMIE type (Var type (Bit Xlen) mstatus))).
    set (meie := evalExpr (@getMieMEIE type (Var type (Bit Xlen) mie))).
    set (mtie := evalExpr (@getMieMTIE type (Var type (Bit Xlen) mie))).
    reflexivity.
  Qed.

  Lemma SemAction_isInterruptPending :
    forall {env : Env rTree} (meip mtip : bool) (rf rf' : TreeState DomainElemState rTree) (res : bool),
      SemAction env (@isInterruptPending dom pcAddrInit type meip mtip) rf rf' res <->
      rf' = rf /\ res = evalIsInterruptPending meip mtip rf.
  Proof.
    intros env meip mtip rf rf' res.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_isInterruptPending.
    split; intros [-> ->]; split; reflexivity.
  Qed.

  Local Opaque isInterruptPending executeInterrupt executeSequential executeNonSequential Zmod.of_Z Zmod.add.

  Lemma evalActionPropGen_executeNonDeferred_interrupt :
    forall {env : Env rTree} (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf : TreeState DomainElemState rTree) P,
      evalIsInterruptPending meip mtip rf = true ->
      (evalActionPropGen env (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut) rf P <->
       evalActionPropGen env (@executeInterrupt dom pcAddrInit type currPcc meip mtip) rf P).
  Proof.
    intros env currPcc meip mtip aluOut rf P Hint.
    unfold executeNonDeferred.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_isInterruptPending, Hint.
    cbn [evalActionPropGen evalExpr].
    apply evalActionPropGen_ext; intros s r; reflexivity.
  Qed.

  Definition evalGetSeqPcc (currPcc : type FullECapWithTag) (isComp : bool) : type FullECapWithTag :=
    evalExpr ((Var type FullECapWithTag currPcc) `{ "addr" <- Add [ ##currPcc`"addr" ; ITE (Var type Bool isComp) $(CompInstSz / 8) $(InstSz / 8) ] }).

  Lemma evalActionPropGen_executeNonDeferred_sequential :
    forall {env : Env rTree} (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf : TreeState DomainElemState rTree) P,
      evalIsInterruptPending meip mtip rf = false ->
      evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = true ->
      (evalActionPropGen env (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut) rf P <->
       evalActionPropGen env (@executeSequential dom pcAddrInit type currPcc aluOut) rf
         (fun rf' mulDivOpt =>
            let isComp := aluOut.(Fst) in
            let seqPcc := evalExpr (@Alu.getSeqPcc type currPcc isComp) in
            P rf' (mulDivOpt ,, (evalExpr (@mkNone type MemFenceUnion) ,,
                    (evalExpr (@mkNone type CfPayload) ,, (false ,, (seqPcc ,, tt))))))).
  Proof.
    intros env currPcc meip mtip aluOut rf P Hint Hseq.
    unfold executeNonDeferred.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_isInterruptPending, Hint.
    cbn [evalActionPropGen evalExpr readDiffTuple mapDiffTuple finNum Fst Snd].
    cbn [evalExpr finNum] in Hseq.
    rewrite Hseq.
    cbn [evalActionPropGen evalExpr readDiffTuple mapDiffTuple finNum Fst Snd].
    apply evalActionPropGen_ext; intros s r; reflexivity.
  Qed.

  Lemma evalActionPropGen_executeNonDeferred_nonSequential :
    forall {env : Env rTree} (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf : TreeState DomainElemState rTree) P,
      evalIsInterruptPending meip mtip rf = false ->
      evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = false ->
      (evalActionPropGen env (@executeNonDeferred dom pcAddrInit type currPcc meip mtip aluOut) rf P <->
       evalActionPropGen env (@executeNonSequential dom pcAddrInit type currPcc meip mtip aluOut) rf P).
  Proof.
    intros env currPcc meip mtip aluOut rf P Hint HnonSeq.
    unfold executeNonDeferred.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_isInterruptPending, Hint.
    cbn [evalActionPropGen evalExpr readDiffTuple mapDiffTuple finNum Fst Snd].
    cbn [evalExpr finNum] in HnonSeq.
    rewrite HnonSeq.
    cbn [evalActionPropGen evalExpr readDiffTuple mapDiffTuple finNum Fst Snd].
    apply evalActionPropGen_ext; intros s r.
    split; intros H; exact H.
  Qed.

End AluExecutionLemmas.

(* ===========================================================================
 * 4. `ImplMulDiv` CORE RULES & WRITEBACK EVALUATION LEMMAS
 * =========================================================================== *)

Section MulDivCoreLemmas.
  Variable dom : string.
  Variable mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable pcAddrInit : Z.
  Variable bpT memT fetchT decodeT executeT dataMemT : Tree DomainElem.

  Local Abbreviation rTree := (rfTree dom pcAddrInit).
  Local Abbreviation mdTree := (implMulDivTree dom mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  Definition evalCommitMulDivWb
    (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
    (c : TreeState DomainElemState cTree) : TreeState DomainElemState cTree :=
    if negb (Zmod.eqb dstIdx Zmod.zero)
    then
      core_withWaitBits dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree
        (core_withRf dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c
           (evalWriteRegsList (gprPathsWithKind dom pcAddrInit) dstIdx dstVal
              (core_rf dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c)))
        (evalWriteWaitBit dom dstIdx false
           (core_waitBits dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c))
    else c.

  Lemma evalActionPropGen_commitMulDivWb :
    forall {env : Env cTree} (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
           (c : TreeState DomainElemState cTree) P,
      evalActionPropGen env
        (@ImplMulDiv.commitMulDivWb dom mulCapacity divCapacity mulStages divStages mulDivMode
                                    pcAddrInit bpT memT fetchT decodeT executeT dataMemT type
                                    dstIdx dstVal) c P <->
      P (evalCommitMulDivWb dstIdx dstVal c) Zmod.zero.
  Proof.
    intros env dstIdx dstVal c P.
    unfold ImplMulDiv.commitMulDivWb, evalCommitMulDivWb.
    cbn [evalActionPropGen evalExpr isNotZero isZero evalNot isEq KindCustomInd getDefault].
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)) eqn:Hnz.
    - cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@np_mulDiv_rf dom mulCapacity divCapacity mulStages divStages mulDivMode
                                pcAddrInit bpT memT fetchT decodeT executeT dataMemT)).
      rewrite (evalActionPropGen_writeRegsList (gprPathsWithKind dom pcAddrInit)
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type FullECapWithTag dstVal)).
      cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@np_mulDiv_waitBits dom mulCapacity divCapacity mulStages divStages mulDivMode
                                      pcAddrInit bpT memT fetchT decodeT executeT dataMemT)).
      unfold writeGprWaitBit, evalWriteWaitBit.
      rewrite (evalActionPropGen_writeRegsList (gprWaitPathsWithKind dom)
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type Bool false)).
      cbn [evalActionPropGen evalExpr].
      reflexivity.
    - cbn [evalActionPropGen evalExpr]; reflexivity.
  Qed.

  Lemma evalCommitMulDivWb_frame :
    forall dstIdx dstVal (c : TreeState DomainElemState cTree),
      let c' := evalCommitMulDivWb dstIdx dstVal c in
      core_bp dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_bp dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_mem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_mem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_fetch dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_fetch dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_decode dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_decode dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_execute dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_execute dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_dataMem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_dataMem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_mulDiv dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_mulDiv dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c.
  Proof.
    intros dstIdx dstVal c.
    unfold evalCommitMulDivWb.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); repeat split; reflexivity.
  Qed.

  Lemma SemAction_lift_np_mulDiv_frame :
    forall {k : Kind} {env : Env cTree} (act : Action type mdTree k)
           (c c' : TreeState DomainElemState cTree) (res : type k),
      SemAction env
        (liftAction
           (@np_mulDiv dom mulCapacity divCapacity mulStages divStages mulDivMode
                       pcAddrInit bpT memT fetchT decodeT executeT dataMemT) act)
        c c' res ->
      exists smd',
        SemAction
          (subEnv (@np_mulDiv dom mulCapacity divCapacity mulStages divStages mulDivMode
                              pcAddrInit bpT memT fetchT decodeT executeT dataMemT) env c)
          act (core_mulDiv dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c) smd' res /\
        c' = core_withMulDiv dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c smd'.
  Proof.
    intros k env act c c' res Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@np_mulDiv dom mulCapacity divCapacity mulStages divStages mulDivMode
                           pcAddrInit bpT memT fetchT decodeT executeT dataMemT)) in Hsem.
    destruct (evalActionPropGen_to_SemAction act _ _ Hsem) as [smd' [res' [Hsem_act [Hc' Hres]]]].
    subst res'.
    exists smd'; split; [exact Hsem_act | symmetry; exact Hc'].
  Qed.

  Lemma mulDivWriteBack_frame :
    forall {env : Env cTree} (popResp : Action type mdTree (Option (MulDivWbResp (Z.to_nat Xlen))))
           (c c' : TreeState DomainElemState cTree) (res : type (Bit 0)),
      SemAction env
        (@ImplMulDiv.mulDivWriteBack dom mulCapacity divCapacity mulStages divStages mulDivMode
                                     pcAddrInit bpT memT fetchT decodeT executeT dataMemT type popResp)
        c c' res ->
      core_bp dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_bp dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_mem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_mem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_fetch dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_fetch dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_decode dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_decode dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_execute dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_execute dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_dataMem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_dataMem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c.
  Proof.
    intros env popResp c c' res Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    unfold ImplMulDiv.mulDivWriteBack in Hsem.
    cbn [evalActionPropGen] in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@np_mulDiv dom mulCapacity divCapacity mulStages divStages mulDivMode
                           pcAddrInit bpT memT fetchT decodeT executeT dataMemT)) in Hsem.
    destruct (evalActionPropGen_to_SemAction popResp _ _ Hsem) as [smd' [wbOpt [_ Hrest]]].
    cbn [evalActionPropGen evalExpr readDiffTuple finNum Fst Snd] in Hrest.
    destruct (wbOpt.(Snd).(Fst)).
    - cbn [evalActionPropGen] in Hrest.
      rewrite evalActionPropGen_commitMulDivWb in Hrest.
      cbn [evalActionPropGen] in Hrest.
      destruct Hrest as [<- _].
      unfold evalCommitMulDivWb.
      destruct (negb (Zmod.eqb _ Zmod.zero)); repeat split; reflexivity.
    - cbn [evalActionPropGen] in Hrest.
      destruct Hrest as [<- _].
      repeat split; reflexivity.
  Qed.

  Theorem mulDivRules_core_frame :
    forall {env : Env cTree} (act : Action type cTree (Bit 0))
           (c c' : TreeState DomainElemState cTree) (res : type (Bit 0)),
      In act (@mulDivRules dom mulCapacity divCapacity mulStages divStages mulDivMode
                           pcAddrInit bpT memT fetchT decodeT executeT dataMemT type) ->
      SemAction env act c c' res ->
      core_bp dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_bp dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_mem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_mem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_fetch dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_fetch dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_decode dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_decode dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_execute dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_execute dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c /\
      core_dataMem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c' =
        core_dataMem dom rTree bpT memT fetchT decodeT executeT dataMemT mdTree c.
  Proof.
    intros env act c c' res Hin Hsem.
    unfold mulDivRules in Hin.
    apply in_app_or in Hin as [Hissue | Hrest].
    - unfold mulDivIssueCoreRules in Hissue.
      apply in_map_iff in Hissue as [mdAct [<- _]].
      destruct (SemAction_lift_np_mulDiv_frame mdAct c c' res Hsem) as [smd' [_ ->]].
      repeat split; reflexivity.
    - apply in_app_or in Hrest as [Hstage | Hwb].
       + unfold mulDivStageRules in Hstage.
        apply in_map_iff in Hstage as [mdAct [<- _]].
        destruct (SemAction_lift_np_mulDiv_frame mdAct c c' res Hsem) as [smd' [_ ->]].
        repeat split; reflexivity.
      + unfold mulDivWriteBackRules in Hwb.
        destruct Hwb as [<- | Hwb].
        * unfold mulWriteBack in Hsem.
          exact (mulDivWriteBack_frame _ c c' res Hsem).
        * assert (act = @divWriteBack dom mulCapacity divCapacity mulStages divStages mulDivMode
                                      pcAddrInit bpT memT fetchT decodeT executeT dataMemT type) as ->.
          { clear c c' Hsem.
            destruct mulDivMode;
              [destruct Hwb as [<- | []]; reflexivity
              | destruct Hwb as [<- | []]; reflexivity
              | contradiction]. }
          unfold divWriteBack in Hsem.
          exact (mulDivWriteBack_frame _ c c' res Hsem).
  Qed.

End MulDivCoreLemmas.

(* ===========================================================================
 * 5. SYSTEM-LEVEL SIMULATION FOR STAGE 4 (`ImplExecute` & `ImplMulDiv`)
 * =========================================================================== *)

Section ExecuteStageSimulation.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree core pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation SState := (SpecState core pcAddrInit regions).
  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
  Local Abbreviation specMod := (@spec core pcAddrInit config regions clint revSpec plic).
  Local Abbreviation cRel :=
    (CoreStateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions).
  Local Abbreviation sRel :=
    (stateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).

  Local Abbreviation rTree := (RfTree core pcAddrInit).
  Local Abbreviation bpT := BpTree.
  Local Abbreviation mTree := (ImplMemSubTree core regions).
  Local Abbreviation fTree := (FetchTree core pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (DecodeTree core decodeCapacity).
  Local Abbreviation eTree := (ExecuteTree core).
  Local Abbreviation dmTree := (DataMemTree core dataMemCapacity).
  Local Abbreviation mdTree := (MulDivSubTree core mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree core rTree bpT mTree fTree decTree eTree dmTree mdTree).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  (* --- 5A. `specMod` Action Membership and Stuttering Helpers --- *)

  Lemma map_snd_specMod :
    map snd (specMod type) =
    ([ Retv ; @Spec.specRevokerStep core pcAddrInit config regions revSpec type ]
     ++ @specPlicPendingsSteps core pcAddrInit regions plic type
     ++ [ @specPlicClaimStep core pcAddrInit regions plic type ;
          @specPlicSampleMeipStep core pcAddrInit regions plic type ;
          @specTickCycle core pcAddrInit regions type ;
          @specTickTimer core pcAddrInit regions clint type ;
          @specSampleMtipStep core pcAddrInit regions clint type ;
          @specStep core pcAddrInit config regions clint plic type ]
     ++ @specFenceIAckSteps core pcAddrInit regions type
     ++ @specInternalMemTargetPortSteps core pcAddrInit regions type)%list.
  Proof.
    unfold specMod, spec.
    rewrite map_map; cbn [snd].
    apply map_id.
  Qed.

  Lemma In_specStep_spec :
    In (@specStep core pcAddrInit config regions clint plic type)
       (map snd (specMod type)).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; right; right; right; left; reflexivity.
  Qed.

  Lemma specMod_stutter :
    forall {env2 : Env sTree} (s2 : SState),
      SemActions env2 (map snd (specMod type)) s2 s2.
  Proof.
    intros env2 s2; apply NilAction; reflexivity.
  Qed.

  Lemma specMod_single_specStep :
    forall {env2 : Env sTree} (s2 s2' : SState),
      SemAction env2 (@specStep core pcAddrInit config regions clint plic type) s2 s2' Zmod.zero ->
      SemActions env2 (map snd (specMod type)) s2 s2'.
  Proof.
    intros env2 s2 s2' Hstep.
    eapply ConsAction.
    - apply In_specStep_spec.
    - exact Hstep.
    - apply specMod_stutter.
  Qed.

  (* --- 5B. `GhostList` Append / Snoc Helpers --- *)

  Lemma GhostList_app_local :
    forall rf0 wm0 l1 rf1 wm1 l2 rf2 wm2,
      GhostList core pcAddrInit rf0 wm0 l1 rf1 wm1 ->
      GhostList core pcAddrInit rf1 wm1 l2 rf2 wm2 ->
      GhostList core pcAddrInit rf0 wm0 (l1 ++ l2)%list rf2 wm2.
  Proof.
    intros rf0 wm0 l1 rf1 wm1 l2 rf2 wm2 H1 H2.
    revert l2 rf2 wm2 H2.
    induction H1 as [rf wm | rf0 rf1 rf2 wm0 wm1 wm2 req reqs Hstep Hrest IH];
      intros l2 rf3 wm3 H2; simpl.
    - exact H2.
    - eapply GhostCons; [exact Hstep | apply IH; exact H2].
  Qed.

  Lemma GhostList_snoc_local :
    forall rf0 wm0 reqs rf2 wm2 rf3 wm3 req,
      GhostList core pcAddrInit rf0 wm0 reqs rf2 wm2 ->
      GhostStep core pcAddrInit rf2 rf3 wm2 wm3 req ->
      GhostList core pcAddrInit rf0 wm0 (reqs ++ [req])%list rf3 wm3.
  Proof.
    intros rf0 wm0 reqs rf2 wm2 rf3 wm3 req Hgl Hstep.
    eapply GhostList_app_local; [exact Hgl |].
    eapply GhostCons; [exact Hstep | apply GhostNil].
  Qed.

  (* --- 5C. `setExecuteCanProceedStage` Simulation --- *)

  Lemma SemAction_setExecuteCanProceedStage_frame :
    forall {env1 : Env iTree} (s1 s1' : IState) (v : bits 0),
      SemAction env1
        (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      v = Zmod.zero /\
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 /\
      impl_waitBits core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1' =
        impl_waitBits core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1 /\
      impl_bp core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_bp core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 /\
      impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1' =
        impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      exec_epoch core (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                                    mulDivMode config regions s1') =
        exec_epoch core (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                                      mulDivMode config regions s1) /\
      exec_fenceIPending core (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                            dataMemCapacity mulCapacity divCapacity mulStages divStages
                                            mulDivMode config regions s1') =
        exec_fenceIPending core (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                              dataMemCapacity mulCapacity divCapacity mulStages divStages
                                              mulDivMode config regions s1) /\
      exec_canProceed core (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                                         mulDivMode config regions s1') = true.
  Proof.
    intros env1 s1 s1' v Hsem.
    unfold setExecuteCanProceedStage, setExecuteCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@Impl.np_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions)) in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [<- <-].
    repeat split; reflexivity.
  Qed.

  Theorem sim_setExecuteCanProceedStage :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setExecuteCanProceedStage_frame s1 s1' v Hsem)
      as [_ [Hrf [_ [_ [Hmem [Hfetch [Hdecode [Hdm [Hmd [Hepoch [Hfip _]]]]]]]]]]].
    exists s2; split; [apply specMod_stutter |].
    destruct Hrel as [Hghost HmemRel [Hquiescent Hcons]].
    constructor.
    - unfold flushMulDiv.
      rewrite Hdm, Hrf, Hmd; exact Hghost.
    - rewrite Hmem; exact HmemRel.
    - split.
      + unfold FenceIPipelineQuiescent, FenceIActive, StateRel.exec_epoch, StateRel.exec_fenceIPending in *.
        unfold exec_epoch, exec_fenceIPending in Hepoch, Hfip.
        rewrite Hepoch, Hfetch, Hdecode, Hfip, Hdm, Hmem.
        exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  (* --- 5D. `mulDivStageActions` Simulation --- *)

  Lemma core_rf_evalCommitMulDivWb :
    forall dstIdx dstVal (c : TreeState DomainElemState cTree),
      core_rf core rTree bpT mTree fTree decTree eTree dmTree mdTree
        (evalCommitMulDivWb core mulCapacity divCapacity mulStages divStages mulDivMode
           pcAddrInit bpT mTree fTree decTree eTree dmTree dstIdx dstVal c) =
      writeGprVal core pcAddrInit dstIdx dstVal
        (core_rf core rTree bpT mTree fTree decTree eTree dmTree mdTree c).
  Proof.
    intros dstIdx dstVal c.
    unfold evalCommitMulDivWb, writeGprVal.
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)); reflexivity.
  Qed.

  Theorem mulDivStageActions_frame :
    forall {env1 : Env iTree} (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (v : bits 0),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      impl_bp core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_bp core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 /\
      impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1' =
        impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 /\
      impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' =
        impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1 /\
      impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 /\
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 /\
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1.
  Proof.
    intros env1 act s1 s1' v Hin Hsem.
    unfold mulDivStageActions in Hin.
    apply in_map_iff in Hin as [cAct [<- HinRules]].
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions)) in Hsem.
    destruct (evalActionPropGen_to_SemAction cAct _ _ Hsem) as [c' [v' [HsemC [Hs1' _]]]].
    subst s1'.
    exact (mulDivRules_core_frame core mulCapacity divCapacity mulStages divStages mulDivMode
             pcAddrInit bpT mTree fTree decTree eTree dmTree cAct (Fst s1) c' v' HinRules HsemC).
  Qed.

  Theorem sim_mulDivStageActions :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v Hin Hsem Hflush Hrel.
    pose proof (mulDivStageActions_frame act s1 s1' v Hin Hsem)
      as [_ [Hmem [Hfetch [Hdecode [Hexec Hdm]]]]].
    exists s2; split; [apply specMod_stutter |].
    destruct Hrel as [Hghost HmemRel [Hquiescent Hcons]].
    constructor.
    - rewrite Hdm, Hflush; exact Hghost.
    - rewrite Hmem; exact HmemRel.
    - split.
      + unfold FenceIPipelineQuiescent, FenceIActive in *.
        rewrite Hexec, Hfetch, Hdecode, Hdm, Hmem.
        exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  (* --- 5E. `aluAndExecuteNonDeferredStage` Simulation (Stutter, Commit, Ghost Snoc) --- *)

  (* Case 1: Stuttering step of `aluAndExecuteNonDeferredStage`
   * (stall on `canProceed = false`, empty `decodeToAluFifo`, epoch mismatch drop,
   *  or full downstream FIFO / interrupt awaiting `dataMem_isEmpty`). *)
  Theorem sim_aluAndExecuteNonDeferredStage_stutter :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint rev plic type)
        s1 s1' v ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1' =
        impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 ->
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 ->
      (FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      cRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hflush Hmem Hdm Hfence Hrel.
    exists s2; split; [apply specMod_stutter |].
    destruct Hrel as [Hghost HmemRel HfenceInv].
    constructor.
    - rewrite Hdm, Hflush; exact Hghost.
    - rewrite Hmem; exact HmemRel.
    - exact (Hfence HfenceInv).
  Qed.

  (* Case 2: Direct architectural commit in `aluAndExecuteNonDeferredStage`
   * when `DataMemEmpty` holds and `dataMemOpt` is `None` (interrupt, sequential
   * ALU/MulDiv, or non-sequential Exception/Scr/Csr/ControlFlow). *)
  Theorem sim_aluAndExecuteNonDeferredStage_commit :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 s2' : SState) (v : bits 0),
      SemAction env1
        (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint rev plic type)
        s1 s1' v ->
      cRel s1 s2 ->
      DataMemEmpty core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) ->
      DataMemEmpty core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') ->
      SemAction env2 (@specStep core pcAddrInit config regions clint plic type) s2 s2' Zmod.zero ->
      spec_rf core pcAddrInit regions s2' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1' ->
      spec_mem core pcAddrInit regions s2' = spec_mem core pcAddrInit regions s2 ->
      impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1' =
        impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2' ->
      exists mid2 : SState,
        SemActions env2 (map snd (specMod type)) s2 mid2 /\
        cRel s1' mid2.
  Proof.
    intros env1 env2 s1 s1' s2 s2' v _ Hrel Hemp1 [Hqueue' Hst'] Hspec Hrf' Hmem2' Hmem1' Hfence'.
    exists s2'; split.
    - apply specMod_single_specStep; exact Hspec.
    - destruct Hrel as [_ HmemRel _].
      constructor.
      + exists (spec_rf core pcAddrInit regions s2'),
               (fun _ : bits RegIdxSzReal => false),
               (fun _ : bits RegIdxSzReal => false).
        split.
        * unfold DataMemInFlightRel; rewrite Hst'; split; reflexivity.
        * rewrite Hqueue', <- Hrf'; apply GhostNil.
      + rewrite Hmem1', Hmem2'; exact HmemRel.
      + exact Hfence'.
  Qed.

  (* Case 3: Deferred `DataMem` instruction in `aluAndExecuteNonDeferredStage`
   * when `dataMemOpt` is `Some mfOp` (Load, Store, or Fence):
   * `s2` stutters via `NilAction` while `GhostList` is extended at the tail
   * with `req := (reqDst, reqAddr, mfOp)` via `GhostList_snoc_local`. *)
  Theorem sim_aluAndExecuteNonDeferredStage_ghost_snoc :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0) (req : type MemFenceReq),
      SemAction env1
        (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint rev plic type)
        s1 s1' v ->
      cRel s1 s2 ->
      (forall wm_dm,
         exists wm_dm',
           GhostStep core pcAddrInit
             (flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                          dataMemCapacity mulCapacity divCapacity mulStages divStages
                          mulDivMode config regions s1)
             (flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                          dataMemCapacity mulCapacity divCapacity mulStages divStages
                          mulDivMode config regions s1')
             wm_dm wm_dm' req) ->
      dataMemPendingQueue core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        (dataMemPendingQueue core dataMemCapacity
           (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                         dataMemCapacity mulCapacity divCapacity mulStages divStages
                         mulDivMode config regions s1) ++ [req])%list ->
      isDataMemLoadRq core dataMemCapacity
        (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1') =
        isDataMemLoadRq core dataMemCapacity
          (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                        dataMemCapacity mulCapacity divCapacity mulStages divStages
                        mulDivMode config regions s1) ->
      impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions s1' =
        impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 ->
      FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1' s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        cRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v req _ Hrel Hstep Hqueue' HloadRq' Hmem' Hfence'.
    exists s2; split; [apply specMod_stutter |].
    destruct Hrel as [[rf_mid [wm_mid [wm_dm [Hinflight Hgl]]]] HmemRel _].
    destruct (Hstep wm_dm) as [wm_dm' HghostStep].
    constructor.
    - exists rf_mid, wm_mid, wm_dm'.
      split.
      + unfold DataMemInFlightRel in Hinflight |- *.
        rewrite HloadRq'; exact Hinflight.
      + rewrite Hqueue'.
        exact (GhostList_snoc_local rf_mid wm_mid _ _ wm_dm _ wm_dm' req Hgl HghostStep).
    - rewrite Hmem'; exact HmemRel.
    - exact Hfence'.
  Qed.

  Lemma flushMulDiv_preserve_of_entries :
    forall (s1 s1' : IState),
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 ->
      extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
        (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1') =
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
          (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1) ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1.
  Proof.
    intros s1 s1' Hrf Hentries.
    unfold flushMulDiv, flushMulDivOn.
    rewrite Hrf, Hentries; reflexivity.
  Qed.

  Lemma flushMulDiv_wb_pop_of_entries :
    forall dstIdx resCap (s1 s1' : IState),
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        writeGprVal core pcAddrInit dstIdx resCap
          (impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1) ->
      extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
        (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1) =
        (dstIdx, resCap) ::
        extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
          (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions s1') ->
      flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1.
  Proof.
    intros dstIdx resCap s1 s1' Hrf Hpop.
    unfold flushMulDiv, flushMulDivOn.
    rewrite Hrf, Hpop; reflexivity.
  Qed.

  Lemma SemAction_aluAndExecuteNonDeferredStage_notCanProceed :
    forall {env1 : Env iTree} (s1 s1' : IState) (v : bits 0),
      exec_canProceed core
        (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = false ->
      SemAction env1
        (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint rev plic type)
        s1 s1' v ->
      s1' = s1 /\ v = Zmod.zero.
  Proof.
    intros env1 s1 s1' v Hcp Hsem.
    unfold aluAndExecuteNonDeferredStage, aluAndExecuteNonDeferred in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem.
    cbn [evalActionPropGen] in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem.
    cbn [evalActionPropGen readExecuteCanProceed] in Hsem.
    lazymatch type of Hsem with
    | context[if ?b then _ else _] =>
        replace b with false in Hsem by (symmetry; exact Hcp)
    end.
    cbn [evalActionPropGen] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    destruct Hsem as [<- <-]; split; reflexivity.
  Qed.

  Theorem sim_aluAndExecuteNonDeferredStage_notCanProceed :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      exec_canProceed core
        (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages
                      mulDivMode config regions s1) = false ->
      SemAction env1
        (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint rev plic type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v Hcp Hsem Hrel.
    destruct (SemAction_aluAndExecuteNonDeferredStage_notCanProceed s1 s1' v Hcp Hsem) as [-> _].
    exists s2; split; [apply specMod_stutter | exact Hrel].
  Qed.

  (* --- 5F. Unconditional `stateRel` Simulation Theorems --- *)

  Theorem sim_setExecuteCanProceedStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply specMod_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_aluAndExecuteNonDeferredStage_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction env1
        (@aluAndExecuteNonDeferredStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions clint rev plic type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 s1 s1' s2 v _ Hrel.
    exists s2; split; [apply specMod_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_mulDivStageActions_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2 act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply specMod_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_mulDivStep_stateRel :
    forall {env1 : Env iTree} {env2 : Env sTree}
           (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@mulDivStageActions core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction env1 act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions env2 (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros env1 env2; exact sim_mulDivStageActions_stateRel.
  Qed.

End ExecuteStageSimulation.

