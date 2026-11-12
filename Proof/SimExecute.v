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

  Local Abbreviation eTree := implExecuteTree.

  Definition ex_execEpoch (ex : TreeState ElemState eTree) : type Epoch :=
    ex.(Fst).

  Definition ex_fenceIPending (ex : TreeState ElemState eTree) : bool :=
    ex.(Snd).(Fst).

  Definition ex_canProceed (ex : TreeState ElemState eTree) : bool :=
    ex.(Snd).(Snd).(Fst).

  Definition ex_withExecEpoch (ex : TreeState ElemState eTree) (v : type Epoch)
    : TreeState ElemState eTree :=
    (v ,, ex.(Snd)).

  Definition ex_withFenceIPending (ex : TreeState ElemState eTree) (v : bool)
    : TreeState ElemState eTree :=
    (ex.(Fst) ,, (v ,, ex.(Snd).(Snd))).

  Definition ex_withCanProceed (ex : TreeState ElemState eTree) (v : bool)
    : TreeState ElemState eTree :=
    (ex.(Fst) ,, (ex.(Snd).(Fst) ,, (v ,, ex.(Snd).(Snd).(Snd)))).

  Lemma evalActionPropGen_readExecEpoch :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@readExecEpoch type) ex P <->
      P ex (ex_execEpoch ex).
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_writeExecEpoch :
    forall {env : Env eTree} (val : type Epoch) (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@writeExecEpoch type val) ex P <->
      P (ex_withExecEpoch ex val) Zmod.zero.
  Proof.
    intros env val ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_readFenceIPending :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@readFenceIPending type) ex P <->
      P ex (ex_fenceIPending ex).
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_setFenceIPending :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@setFenceIPending type) ex P <->
      P (ex_withFenceIPending ex true) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_readExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@readExecuteCanProceed type) ex P <->
      P ex (ex_canProceed ex).
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_setExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@setExecuteCanProceed type) ex P <->
      P (ex_withCanProceed ex true) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  Lemma evalActionPropGen_clearExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@clearExecuteCanProceed type) ex P <->
      P (ex_withCanProceed ex false) Zmod.zero.
  Proof.
    intros env ex P; reflexivity.
  Qed.

  (* The hand-off between execute slots of one cycle (`firstSlot`, `handoff`) *)
  Definition ex_firstSlot (ex : TreeState ElemState eTree) : bool :=
    ex.(Snd).(Snd).(Snd).(Fst).

  Definition ex_handoff (ex : TreeState ElemState eTree) : type ExecHandoff :=
    ex.(Snd).(Snd).(Snd).(Snd).(Fst).

  (* ExecHandoff = { head; pcc; redirPending; dataMemIn_isFull; dataMem_isEmpty; mem_noWriteRq } *)
  Definition hoHead (h : type ExecHandoff) : type (Option DecodeToAluEntry) := h.(Fst).
  Definition hoPcc (h : type ExecHandoff) : type FullECapWithTag := h.(Snd).(Fst).
  Definition hoRedir (h : type ExecHandoff) : bool := h.(Snd).(Snd).(Fst).
  Definition hoDmFull (h : type ExecHandoff) : bool := h.(Snd).(Snd).(Snd).(Fst).

  Definition ex_withFirstSlot (ex : TreeState ElemState eTree) (v : bool)
    : TreeState ElemState eTree :=
    (ex.(Fst) ,, (ex.(Snd).(Fst) ,, (ex.(Snd).(Snd).(Fst) ,, (v ,, ex.(Snd).(Snd).(Snd).(Snd))))).

  Definition ex_withHandoff (ex : TreeState ElemState eTree) (v : type ExecHandoff)
    : TreeState ElemState eTree :=
    (ex.(Fst) ,, (ex.(Snd).(Fst) ,, (ex.(Snd).(Snd).(Fst) ,, (ex.(Snd).(Snd).(Snd).(Fst) ,,
      (v ,, ex.(Snd).(Snd).(Snd).(Snd).(Snd)))))).

  Lemma evalActionPropGen_readFirstSlot :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@readFirstSlot type) ex P <-> P ex (ex_firstSlot ex).
  Proof. intros env ex P; reflexivity. Qed.

  Lemma evalActionPropGen_clearFirstSlot :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@clearFirstSlot type) ex P <-> P (ex_withFirstSlot ex false) Zmod.zero.
  Proof. intros env ex P; reflexivity. Qed.

  Lemma evalActionPropGen_readHandoff :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@readHandoff type) ex P <-> P ex (ex_handoff ex).
  Proof. intros env ex P; reflexivity. Qed.

  Lemma evalActionPropGen_writeHandoff :
    forall {env : Env eTree} (v : type ExecHandoff) (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@writeHandoff type v) ex P <-> P (ex_withHandoff ex v) Zmod.zero.
  Proof. intros env v ex P; reflexivity. Qed.

  Lemma evalActionPropGen_clearHandoff :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@clearHandoff type) ex P <->
      P (ex_withHandoff ex (getDefault ExecHandoff)) Zmod.zero.
  Proof. intros env ex P; reflexivity. Qed.

  Lemma evalActionPropGen_resetExecuteCanProceed :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@resetExecuteCanProceed type) ex P <->
      P (ex_withHandoff (ex_withFirstSlot (ex_withCanProceed ex true) true) (getDefault ExecHandoff))
        Zmod.zero.
  Proof. intros env ex P; reflexivity. Qed.

  (* Execute's redirect register (applied by `applyRedirect`) *)
  Definition ex_redirect (ex : TreeState ElemState eTree) : type (Option FullECapWithTag) :=
    ex.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

  Definition ex_redirValid (ex : TreeState ElemState eTree) : bool :=
    (ex_redirect ex).(Snd).(Fst).

  Definition ex_withRedirect (ex : TreeState ElemState eTree) (v : type (Option FullECapWithTag))
    : TreeState ElemState eTree :=
    (ex.(Fst) ,, (ex.(Snd).(Fst) ,, (ex.(Snd).(Snd).(Fst) ,, (ex.(Snd).(Snd).(Snd).(Fst) ,,
      (ex.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (v ,, ex.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))).

  (* The redirect Execute sets: new PCC `p` (the target is `p`'s address) *)
  Definition redirOf (p : type FullECapWithTag) : type (Option FullECapWithTag) :=
    evalExpr (mkSome (Var type FullECapWithTag p)).

  Lemma evalActionPropGen_redirectPending :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@redirectPending type) ex P <-> P ex (ex_redirValid ex).
  Proof. intros env ex P; reflexivity. Qed.

  Lemma evalActionPropGen_readRedirect :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@readRedirect type) ex P <-> P ex (ex_redirect ex).
  Proof. intros env ex P; reflexivity. Qed.

  Lemma evalActionPropGen_setRedirect :
    forall {env : Env eTree} (p : type FullECapWithTag) (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@setRedirect type p) ex P <-> P (ex_withRedirect ex (redirOf p)) Zmod.zero.
  Proof. intros env p ex P; reflexivity. Qed.

  Lemma evalActionPropGen_clearRedirect :
    forall {env : Env eTree} (ex : TreeState ElemState eTree) P,
      evalActionPropGen env (@clearRedirect type) ex P <->
      P (ex_withRedirect ex (getDefault (Option FullECapWithTag))) Zmod.zero.
  Proof. intros env ex P; reflexivity. Qed.

  (* Wait-bit helpers on `waitBitsTree` *)
  Definition evalReadWaitBit (idx : bits RegIdxSzReal)
    (wb : TreeState ElemState waitBitsTree) : bool :=
    evalReadRegsListHelper 1%nat nil gprWaitPathsWithKind idx wb.

  Definition evalWriteWaitBit (idx : bits RegIdxSzReal) (val : bool)
    (wb : TreeState ElemState waitBitsTree)
    : TreeState ElemState waitBitsTree :=
    evalWriteRegsListHelper 1%nat gprWaitPathsWithKind idx val wb.

  Definition evalSetDstWaitBits (writesGpr : bool) (gprIdx : bits RegIdxSzReal) (val : bool)
    (wb : TreeState ElemState waitBitsTree)
    : TreeState ElemState waitBitsTree :=
    if writesGpr then evalWriteWaitBit gprIdx val wb else wb.

  Local Opaque gprWaitPathsWithKind.

  Lemma evalActionPropGen_readGprWaitBit :
    forall {env : Env waitBitsTree} (idx : bits RegIdxSzReal)
           (wb : TreeState ElemState waitBitsTree) P,
      evalActionPropGen env (@readGprWaitBit type idx) wb P <->
      P wb (evalReadWaitBit idx wb).
  Proof.
    intros env idx wb P.
    unfold readGprWaitBit, evalReadWaitBit.
    apply (evalActionPropGen_readRegsListHelper gprWaitPathsWithKind 1%nat nil (Var type (Bit RegIdxSzReal) idx)).
  Qed.

  Lemma evalActionPropGen_writeGprWaitBit :
    forall {env : Env waitBitsTree} (idx : bits RegIdxSzReal) (val : bool)
           (wb : TreeState ElemState waitBitsTree) P,
      evalActionPropGen env (@writeGprWaitBit type idx val) wb P <->
      P (evalWriteWaitBit idx val wb) Zmod.zero.
  Proof.
    intros env idx val wb P.
    unfold writeGprWaitBit, evalWriteWaitBit.
    apply (evalActionPropGen_writeRegsListHelper gprWaitPathsWithKind 1%nat (Var type (Bit RegIdxSzReal) idx) (Var type Bool val)).
  Qed.

  Lemma evalActionPropGen_setDstWaitBits :
    forall {env : Env waitBitsTree} (writesGpr : bool) (gprIdx : bits RegIdxSzReal) (val : bool)
           (wb : TreeState ElemState waitBitsTree) P,
      evalActionPropGen env (@setDstWaitBits type writesGpr gprIdx val) wb P <->
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
  Variable rfT bpT memT fetchT decodeT executeT dataMemT mulDivT : Tree Elem.

  Local Abbreviation cTree := (coreTree rfT bpT memT fetchT decodeT executeT dataMemT mulDivT).

  Definition core_rf (c : TreeState ElemState cTree) : TreeState ElemState rfT :=
    c.(Fst).(Fst).

  Definition core_waitBits (c : TreeState ElemState cTree) : TreeState ElemState waitBitsTree :=
    c.(Snd).(Fst).(Fst).

  Definition core_mulDiv (c : TreeState ElemState cTree) : TreeState ElemState mulDivT :=
    c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).

  Definition core_withRf (c : TreeState ElemState cTree)
    (v : TreeState ElemState rfT) : TreeState ElemState cTree :=
    ((v ,, c.(Fst).(Snd)) ,, c.(Snd)).

  Definition core_withWaitBits (c : TreeState ElemState cTree)
    (v : TreeState ElemState waitBitsTree) : TreeState ElemState cTree :=
    (c.(Fst) ,, ((v ,, c.(Snd).(Fst).(Snd)) ,, c.(Snd).(Snd))).

  Definition core_withMulDiv (c : TreeState ElemState cTree)
    (v : TreeState ElemState mulDivT) : TreeState ElemState cTree :=
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
  Variable pcAddrInit : Z.

  Local Abbreviation rTree := (rfTree pcAddrInit).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind.

  Definition evalIsInterruptPending (meip mtip : bool)
    (rf : TreeState ElemState rTree) : bool :=
    let mstatus := evalReadRegsList (csrPathsWithKind pcAddrInit) (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mstatus")) rf in
    let mie     := evalReadRegsList (csrPathsWithKind pcAddrInit) (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mie")) rf in
    let currMIE := evalExpr (@getMstatusMIE type (Var type (Bit Xlen) mstatus)) in
    let meie    := evalExpr (@getMieMEIE type (Var type (Bit Xlen) mie)) in
    let mtie    := evalExpr (@getMieMTIE type (Var type (Bit Xlen) mie)) in
    andb currMIE (orb (andb meip meie) (andb mtip mtie)).

  Lemma evalActionPropGen_isInterruptPending :
    forall {env : Env rTree} (meip mtip : bool) (rf : TreeState ElemState rTree) P,
      evalActionPropGen env (@isInterruptPending pcAddrInit type meip mtip) rf P <->
      P rf (evalIsInterruptPending meip mtip rf).
  Proof.
    intros env meip mtip rf P.
    unfold isInterruptPending, evalIsInterruptPending.
    cbn [evalActionPropGen].
    rewrite (evalActionPropGen_readRegsList (csrPathsWithKind pcAddrInit)
               ($(getCsrPhysicalIdx "mstatus") : Expr type (Bit CsrIdxSz))).
    cbn [evalActionPropGen].
    rewrite (evalActionPropGen_readRegsList (csrPathsWithKind pcAddrInit)
               ($(getCsrPhysicalIdx "mie") : Expr type (Bit CsrIdxSz))).
    cbn [evalActionPropGen].
    change (evalExpr ($(getCsrPhysicalIdx "mstatus") : Expr type (Bit CsrIdxSz)))
      with (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mstatus")).
    change (evalExpr ($(getCsrPhysicalIdx "mie") : Expr type (Bit CsrIdxSz)))
      with (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mie")).
    set (mstatus := evalReadRegsList (csrPathsWithKind pcAddrInit)
                      (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mstatus")) rf).
    set (mie := evalReadRegsList (csrPathsWithKind pcAddrInit)
                  (Zmod.of_Z (2 ^ CsrIdxSz) (getCsrPhysicalIdx "mie")) rf).
    set (currMIE := evalExpr (@getMstatusMIE type (Var type (Bit Xlen) mstatus))).
    set (meie := evalExpr (@getMieMEIE type (Var type (Bit Xlen) mie))).
    set (mtie := evalExpr (@getMieMTIE type (Var type (Bit Xlen) mie))).
    reflexivity.
  Qed.

  Local Opaque isInterruptPending executeInterrupt executeSequential executeNonSequential Zmod.of_Z Zmod.add.

  Lemma evalActionPropGen_executeNonDeferred_interrupt :
    forall {env : Env rTree} (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf : TreeState ElemState rTree) P,
      evalIsInterruptPending meip mtip rf = true ->
      (evalActionPropGen env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf P <->
       evalActionPropGen env (@executeInterrupt pcAddrInit type currPcc meip mtip) rf P).
  Proof.
    intros env currPcc meip mtip aluOut rf P Hint.
    unfold executeNonDeferred.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_isInterruptPending, Hint.
    cbn [evalActionPropGen evalExpr].
    apply evalActionPropGen_ext; intros s r; reflexivity.
  Qed.

  Lemma evalActionPropGen_executeNonDeferred_sequential :
    forall {env : Env rTree} (currPcc : type FullECapWithTag) (meip mtip : bool) (aluOut : type AluOutUnion)
           (rf : TreeState ElemState rTree) P,
      evalIsInterruptPending meip mtip rf = false ->
      evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = true ->
      (evalActionPropGen env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf P <->
       evalActionPropGen env (@executeSequential pcAddrInit type currPcc aluOut) rf
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
           (rf : TreeState ElemState rTree) P,
      evalIsInterruptPending meip mtip rf = false ->
      evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = false ->
      (evalActionPropGen env (@executeNonDeferred pcAddrInit type currPcc meip mtip aluOut) rf P <->
       evalActionPropGen env (@executeNonSequential pcAddrInit type currPcc meip mtip aluOut) rf P).
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

  Lemma evalExpr_csrIdxIsVirtual :
    forall (csrIdx : bits CsrIdxSz),
      evalExpr (@csrIdxIsVirtual type csrIdx) =
      evalExpr (Eq (Var type (Bit CsrIdxSz) csrIdx) $(getCsrIdx "mip")).
  Proof.
    intros csrIdx.
    unfold csrIdxIsVirtual.
    cbn [skipn length PhysicalCsrTable VirtualCsrTable CsrTable app enumerate enumerate_aux map evalExpr fold_left evalOrBinary evalBinary orb KindCustomInd getDefault].
    reflexivity.
  Qed.

  Lemma bits1_eqb_0_false_1_true :
    forall (b : bits 1),
      Zmod.eqb b (Zmod.of_Z (2 ^ 1) 0) = false ->
      Zmod.eqb b (Zmod.of_Z (2 ^ 1) 1) = true.
  Proof.
    intros b Hb.
    pose proof (bits.unsigned_range b ltac:(lia)) as Hrange.
    destruct (Zmod.eqb_spec b (Zmod.of_Z (2 ^ 1) 0)) as [_ | Hneq]; [discriminate |].
    apply Zmod.eqb_eq.
    apply Zmod.unsigned_inj.
    change (Zmod.unsigned (Zmod.of_Z (2 ^ 1) 1)) with 1.
    assert (Zmod.unsigned b <> 0).
    { intros H0; apply Hneq; apply Zmod.unsigned_inj; exact H0. }
    lia.
  Qed.

  Lemma evalActionPropGen_LetExp_eval_cong {t : Tree Elem} {k k' : Kind} :
    forall {env : Env t} (nm : string) (e : Expr type k')
           (cont1 cont2 : type k' -> Action type t k)
           (s : TreeState ElemState t) P,
      (evalActionPropGen env (cont1 (evalExpr e)) s P <->
       evalActionPropGen env (cont2 (evalExpr e)) s P) ->
      (evalActionPropGen env (LetExp nm e cont1) s P <->
       evalActionPropGen env (LetExp nm e cont2) s P).
  Proof.
    intros env nm e cont1 cont2 s P Hcont; cbn [evalActionPropGen]; exact Hcont.
  Qed.

  Lemma evalActionPropGen_LetExp_eq_cong {t : Tree Elem} {k k' : Kind} :
    forall {env : Env t} (nm : string) (e1 e2 : Expr type k')
           (cont1 cont2 : type k' -> Action type t k)
           (s : TreeState ElemState t) P,
      evalExpr e1 = evalExpr e2 ->
      (forall v, evalActionPropGen env (cont1 v) s P <-> evalActionPropGen env (cont2 v) s P) ->
      (evalActionPropGen env (LetExp nm e1 cont1) s P <->
       evalActionPropGen env (LetExp nm e2 cont2) s P).
  Proof.
    intros env nm e1 e2 cont1 cont2 s P Heq Hcont; cbn [evalActionPropGen]; rewrite Heq; apply Hcont.
  Qed.

  Lemma evalActionPropGen_LetAction_cong {t : Tree Elem} {k k' : Kind} :
    forall {env : Env t} (nm : string) (a : Action type t k')
           (cont1 cont2 : type k' -> Action type t k)
           (s : TreeState ElemState t) P,
      (forall s1 v, evalActionPropGen env (cont1 v) s1 P <-> evalActionPropGen env (cont2 v) s1 P) ->
      (evalActionPropGen env (LetAction nm a cont1) s P <->
       evalActionPropGen env (LetAction nm a cont2) s P).
  Proof.
    intros env nm a cont1 cont2 s P Hcont; cbn [evalActionPropGen].
    apply evalActionPropGen_ext; intros s1 v; apply Hcont.
  Qed.

  Lemma evalActionPropGen_IfElse_dep_cong {t : Tree Elem} {k k' : Kind} :
    forall {env : Env t} (nm : string) (c : Expr type Bool) (a1 a2 b1 b2 : Action type t k')
           (cont1 cont2 : type k' -> Action type t k)
           (s : TreeState ElemState t) P,
      (evalExpr c = true ->
       forall P0, evalActionPropGen env a1 s P0 <-> evalActionPropGen env b1 s P0) ->
      (evalExpr c = false ->
       forall P0, evalActionPropGen env a2 s P0 <-> evalActionPropGen env b2 s P0) ->
      (forall s1 v, evalActionPropGen env (cont1 v) s1 P <-> evalActionPropGen env (cont2 v) s1 P) ->
      (evalActionPropGen env (IfElse nm c a1 a2 cont1) s P <->
       evalActionPropGen env (IfElse nm c b1 b2 cont2) s P).
  Proof.
    intros env nm c a1 a2 b1 b2 cont1 cont2 s P Htrue Hfalse Hcont; cbn [evalActionPropGen].
    destruct (evalExpr c) eqn:Hc.
    - rewrite (Htrue eq_refl); apply evalActionPropGen_ext; intros s1 v; apply Hcont.
    - rewrite (Hfalse eq_refl); apply evalActionPropGen_ext; intros s1 v; apply Hcont.
  Qed.

  Lemma evalExpr_Or_ITE0_false :
    forall (x : bits Xlen) (c : Expr type Bool) (a b : Expr type (Bit Xlen)),
      evalExpr c = false ->
      evalExpr (Or [ Var type (Bit Xlen) x ; ITE0 c a ]) =
      evalExpr (Or [ Var type (Bit Xlen) x ; ITE0 c b ]).
  Proof.
    intros x c a b Hc.
    unfold ITE0; cbn [evalExpr map fold_left]; rewrite Hc; reflexivity.
  Qed.

  Local Transparent executeNonSequential.
  Local Opaque evalActionPropGen readRegsList writeRegsList incrementMinstret handleTrap updateMshwmOnStore
               Alu.getSeqPcc encodeMcause encodeCheriMtval createMip.

  Lemma evalActionPropGen_executeNonSequential_not_virtCsr_meip_mtip_indep :
    forall {env : Env rTree} (currPcc : type FullECapWithTag)
           (meip1 mtip1 meip2 mtip2 : bool) (aluOut : type AluOutUnion)
           (rf : TreeState ElemState rTree) P,
      evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = false ->
      isVirtualCsrAluOut aluOut = false ->
      (evalActionPropGen env (@executeNonSequential pcAddrInit type currPcc meip1 mtip1 aluOut) rf P <->
       evalActionPropGen env (@executeNonSequential pcAddrInit type currPcc meip2 mtip2 aluOut) rf P).
  Proof.
    intros env currPcc meip1 mtip1 meip2 mtip2 aluOut rf P Hseq Hvirt.
    unfold isVirtualCsrAluOut in Hvirt.
    rewrite evalExpr_csrIdxIsVirtual in Hvirt.
    set (aluOp := evalExpr ((Var type AluOutUnion aluOut)`"Op")) in *.
    set (nonSeqOp := evalExpr ((Var type AluOpUnion aluOp) `! "NonSequential")) in *.
    set (noExc := evalExpr ((Var type NonSequentialUnion nonSeqOp) `! "NoException")) in *.
    set (cfScrCsr := evalExpr ((Var type NoExceptionUnion noExc) `! "CfScrCsr")) in *.
    set (scrCsr := evalExpr ((Var type CfScrCsrUnion cfScrCsr) `! "ScrCsr")) in *.
    set (sDest := evalExpr ((Var type ScrCsrPayload scrCsr)`"SpecialDest")) in *.
    set (csrIdx := evalExpr ((Var type (TaggedUnion ScrCsrIdx) sDest) `! "Csr")) in *.
    assert (HnonSeq : evalExpr ((Var type AluOpUnion aluOp) `? "NonSequential") = true)
      by (apply bits1_eqb_0_false_1_true; exact Hseq).
    rewrite HnonSeq in Hvirt; cbn [andb] in Hvirt.
    unfold executeNonSequential.
    do 6 apply evalActionPropGen_LetExp_eval_cong.
    apply evalActionPropGen_IfElse_dep_cong; [intros _ ?; reflexivity | | intros ? ?; reflexivity].
    intros Hexc P0.
    assert (HnoExc : evalExpr ((Var type NonSequentialUnion nonSeqOp) `? "NoException") = true)
      by (apply bits1_eqb_0_false_1_true; exact Hexc).
    rewrite HnoExc in Hvirt; cbn [andb] in Hvirt.
    apply evalActionPropGen_LetAction_cong; intros s1 ?.
    apply evalActionPropGen_LetAction_cong; intros s2 ?.
    apply evalActionPropGen_LetExp_eval_cong.
    apply evalActionPropGen_IfElse_dep_cong; [intros _ ?; reflexivity | | intros ? ?; reflexivity].
    intros Hdm P1.
    assert (HcfScrCsr : evalExpr ((Var type NoExceptionUnion noExc) `? "CfScrCsr") = true)
      by (apply bits1_eqb_0_false_1_true; exact Hdm).
    rewrite HcfScrCsr in Hvirt; cbn [andb] in Hvirt.
    apply evalActionPropGen_LetExp_eval_cong.
    apply evalActionPropGen_IfElse_dep_cong; [| intros _ ?; reflexivity | intros ? ?; reflexivity].
    intros HscrCsr P2.
    change (evalExpr ((Var type CfScrCsrUnion cfScrCsr) `? "ScrCsr") = true) in HscrCsr.
    rewrite HscrCsr in Hvirt; cbn [andb] in Hvirt.
    do 6 apply evalActionPropGen_LetExp_eval_cong.
    apply evalActionPropGen_IfElse_dep_cong; [intros _ ?; reflexivity | | intros ? ?; reflexivity].
    intros Hscr P3.
    assert (Hcsr : evalExpr ((Var type (TaggedUnion ScrCsrIdx) sDest) `? "Csr") = true)
      by (apply bits1_eqb_0_false_1_true; exact Hscr).
    rewrite Hcsr in Hvirt; cbn [andb] in Hvirt.
    apply evalActionPropGen_LetExp_eval_cong.
    apply evalActionPropGen_LetAction_cong; intros s3 csrPhys.
    apply evalActionPropGen_LetExp_eq_cong; [| intros ?; reflexivity].
    apply evalExpr_Or_ITE0_false; exact Hvirt.
  Qed.

  Local Transparent evalActionPropGen.
  Local Opaque executeNonSequential.

  Theorem evalActionPropGen_executeNonDeferred_not_virtCsr_meip_mtip_indep :
    forall {env : Env rTree} (currPcc : type FullECapWithTag)
           (meip1 mtip1 meip2 mtip2 : bool) (aluOut : type AluOutUnion)
           (rf : TreeState ElemState rTree) P,
      evalIsInterruptPending meip1 mtip1 rf = false ->
      evalIsInterruptPending meip2 mtip2 rf = false ->
      isVirtualCsrAluOut aluOut = false ->
      (evalActionPropGen env (@executeNonDeferred pcAddrInit type currPcc meip1 mtip1 aluOut) rf P <->
       evalActionPropGen env (@executeNonDeferred pcAddrInit type currPcc meip2 mtip2 aluOut) rf P).
  Proof.
    intros env currPcc meip1 mtip1 meip2 mtip2 aluOut rf P Hint1 Hint2 Hvirt.
    destruct (evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential")) eqn:Hseq.
    - rewrite (evalActionPropGen_executeNonDeferred_sequential currPcc meip1 mtip1 aluOut rf P Hint1 Hseq).
      rewrite (evalActionPropGen_executeNonDeferred_sequential currPcc meip2 mtip2 aluOut rf P Hint2 Hseq).
      reflexivity.
    - rewrite (evalActionPropGen_executeNonDeferred_nonSequential currPcc meip1 mtip1 aluOut rf P Hint1 Hseq).
      rewrite (evalActionPropGen_executeNonDeferred_nonSequential currPcc meip2 mtip2 aluOut rf P Hint2 Hseq).
      exact (evalActionPropGen_executeNonSequential_not_virtCsr_meip_mtip_indep
               currPcc meip1 mtip1 meip2 mtip2 aluOut rf P Hseq Hvirt).
  Qed.

  Theorem SemAction_executeNonDeferred_not_virtCsr_meip_mtip_indep :
    forall {env : Env rTree} (currPcc : type FullECapWithTag)
           (meip1 mtip1 meip2 mtip2 : bool) (aluOut : type AluOutUnion)
           (rf rf' : TreeState ElemState rTree) (execOut : type ExecuteOut),
      evalIsInterruptPending meip1 mtip1 rf = false ->
      evalIsInterruptPending meip2 mtip2 rf = false ->
      isVirtualCsrAluOut aluOut = false ->
      (SemAction env (@executeNonDeferred pcAddrInit type currPcc meip1 mtip1 aluOut) rf rf' execOut <->
       SemAction env (@executeNonDeferred pcAddrInit type currPcc meip2 mtip2 aluOut) rf rf' execOut).
  Proof.
    intros env currPcc meip1 mtip1 meip2 mtip2 aluOut rf rf' execOut Hint1 Hint2 Hvirt.
    rewrite !SemAction_iff_evalActionPropGen.
    exact (evalActionPropGen_executeNonDeferred_not_virtCsr_meip_mtip_indep
             currPcc meip1 mtip1 meip2 mtip2 aluOut rf (fun s r => s = rf' /\ r = execOut)
             Hint1 Hint2 Hvirt).
  Qed.

End AluExecutionLemmas.

(* ===========================================================================
 * 4. `ImplMulDiv` CORE RULES & WRITEBACK EVALUATION LEMMAS
 * =========================================================================== *)

Section MulDivCoreLemmas.
  Variable mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable pcAddrInit : Z.
  Variable bpT memT fetchT decodeT executeT dataMemT : Tree Elem.

  Local Abbreviation rTree := (rfTree pcAddrInit).
  Local Abbreviation mdTree := (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree rTree bpT memT fetchT decodeT executeT dataMemT mdTree).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  Definition evalCommitMulDivWb
    (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
    (c : TreeState ElemState cTree) : TreeState ElemState cTree :=
    if negb (Zmod.eqb dstIdx Zmod.zero)
    then
      core_withWaitBits rTree bpT memT fetchT decodeT executeT dataMemT mdTree
        (core_withRf rTree bpT memT fetchT decodeT executeT dataMemT mdTree c
           (evalWriteRegsList (gprPathsWithKind pcAddrInit) dstIdx dstVal
              (core_rf rTree bpT memT fetchT decodeT executeT dataMemT mdTree c)))
        (evalWriteWaitBit dstIdx false
           (core_waitBits rTree bpT memT fetchT decodeT executeT dataMemT mdTree c))
    else c.

  Lemma evalActionPropGen_commitMulDivWb :
    forall {env : Env cTree} (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
           (c : TreeState ElemState cTree) P,
      evalActionPropGen env
        (@ImplMulDiv.commitMulDivWb mulCapacity divCapacity mulStages divStages mulDivMode
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
                 (@np_mulDiv_rf mulCapacity divCapacity mulStages divStages mulDivMode
                                pcAddrInit bpT memT fetchT decodeT executeT dataMemT)).
      rewrite (evalActionPropGen_writeRegsList (gprPathsWithKind pcAddrInit)
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type FullECapWithTag dstVal)).
      cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@np_mulDiv_waitBits mulCapacity divCapacity mulStages divStages mulDivMode
                                      pcAddrInit bpT memT fetchT decodeT executeT dataMemT)).
      unfold writeGprWaitBit, evalWriteWaitBit.
      rewrite (evalActionPropGen_writeRegsListHelper gprWaitPathsWithKind 1%nat
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type Bool false)).
      cbn [evalActionPropGen evalExpr].
      reflexivity.
    - cbn [evalActionPropGen evalExpr]; reflexivity.
  Qed.

End MulDivCoreLemmas.

(* ===========================================================================
 * 5. SYSTEM-LEVEL SIMULATION FOR STAGE 4 (`ImplExecute` & `ImplMulDiv`)
 * =========================================================================== *)

Section ExecuteStageSimulation.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
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
              mulDivMode bp config regions).
  Local Abbreviation SState := (SpecState pcAddrInit regions).
  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode bp config regions).
  Local Abbreviation specMod := (@spec pcAddrInit config regions clint revSpec plic).

  Local Abbreviation rTree := (RfTree pcAddrInit).
  Local Abbreviation bpT := (BpTree bp).
  Local Abbreviation mTree := (ImplMemSubTree regions).
  Local Abbreviation fTree := (FetchTree pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (DecodeTree decodeCapacity).
  Local Abbreviation eTree := ExecuteTree.
  Local Abbreviation dmTree := (DataMemTree dataMemCapacity).
  Local Abbreviation mdTree := (MulDivSubTree mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree rTree bpT mTree fTree decTree eTree dmTree mdTree).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  (* --- 5A. `specMod` Action Membership and Stuttering Helpers --- *)

  Lemma map_snd_specMod :
    specMod type =
    ([ Retv ; @Spec.specRevokerStep pcAddrInit config regions revSpec type ]
     ++ @specPlicPendingsSteps pcAddrInit regions plic type
     ++ [ @specPlicClaimStep pcAddrInit regions plic type ;
          @specPlicSampleMeipStep pcAddrInit regions plic type ;
          @specTickCycle pcAddrInit regions type ;
          @specTickTimer pcAddrInit regions clint type ;
          @specSampleMtipStep pcAddrInit regions clint type ;
          @specStep pcAddrInit config regions clint plic type ;
          @specSecondLine pcAddrInit config regions type ]
     ++ @specFenceIAckSteps pcAddrInit regions type)%list.
  Proof.
    unfold specMod, spec.
    reflexivity.
  Qed.

  Lemma In_specStep_spec :
    In (@specStep pcAddrInit config regions clint plic type)
       (specMod type).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; right; right; right; left; reflexivity.
  Qed.

  (* --- 5E. `aluAndExecuteNonDeferredStage` Simulation (Stutter, Commit, Ghost Snoc) --- *)

  (* Case 1: Stuttering step of `aluAndExecuteNonDeferredStage`
   * (stall on `canProceed = false`, empty `decodeToAluFifo`, epoch mismatch drop,
   *  or full downstream FIFO / interrupt awaiting `dataMem_isEmpty`). *)

  (* Case 2: Direct architectural commit in `aluAndExecuteNonDeferredStage`
   * when `DataMemEmpty` holds and `dataMemOpt` is `None` (interrupt, sequential
   * ALU/MulDiv, or non-sequential Exception/Scr/Csr/ControlFlow). *)

  (* Case 3: Deferred `DataMem` instruction in `aluAndExecuteNonDeferredStage`
   * when `dataMemOpt` is `Some mfOp` (Load, Store, or Fence):
   * `s2` stutters via `NilAction` while `GhostList` is extended at the tail
   * with `req := (reqDst, reqAddr, mfOp)` via `GhostList_snoc_local`. *)

End ExecuteStageSimulation.
