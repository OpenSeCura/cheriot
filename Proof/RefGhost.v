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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * GHOST CHAIN OF EXECUTED, NOT YET COMMITTED INSTRUCTIONS
 * ===========================================================================
 * The impl executes an instruction (its non-deferred part) before the spec
 * does. Executed instructions the spec has not run yet, and the mcycle ticks
 * between them, form the ghost chain. It reuses the step of `GhostStepOpt`
 * (StateRel.v): `executeNonDeferred` followed by the PCC write. The chain
 * wrapper pins down what `GhostStepOpt` leaves existential (PCC, ALU output,
 * interrupt inputs) so that the spec can replay each entry with `specStep`:
 * - the PCC is the chain register file's PCC;
 * - the ALU output is the ALU applied to the decode of the recorded fetch
 *   output and the register read from the chain register file;
 * - no interrupt is pending for the recorded latch values.
 * A mulDiv entry also applies its result, as the spec's deferred stage does.
 * Load results are not part of the chain: they are written when the load
 * commits (spec) or writes back (impl). *)

Section GhostChain.
  Variable core : string.
  Variable pcAddrInit : Z.

  Local Abbreviation RfSt := (RfState core pcAddrInit).

  (* --- 1. Evaluation Helpers --- *)

  Definition readPcc (rf : RfSt) : type FullECapWithTag :=
    readGpr core pcAddrInit Zmod.zero rf.

  Definition writePcc (v : type FullECapWithTag) (rf : RfSt) : RfSt :=
    updGpr core pcAddrInit Zmod.zero v rf.

  Definition evalDecode (fo : type FetchOut) : type RegReadIn :=
    evalLetExpr (@wrappedDecode type fo).

  Definition evalAluOut (pcc : type FullECapWithTag) (aluIn : type AluInInstGroup)
    : type AluOutUnion :=
    evalLetExpr (@wrappedAlu type pcc aluIn).

  (* Register indices seen by the scoreboard, from the decode of a fetch output *)
  Definition decOutOf (fo : type FetchOut) : type DecodeOut :=
    let rri := evalDecode fo in
    evalExpr (##rri`"decodeOut").

  Definition decCs1 (fo : type FetchOut) : bits RegIdxSzReal :=
    let d := decOutOf fo in
    evalExpr (##d`"cs1Idx").

  Definition decCs2 (fo : type FetchOut) : bits RegIdxSzReal :=
    let d := decOutOf fo in
    evalExpr (##d`"cs2Idx").

  Definition decWritesCd (fo : type FetchOut) : bool :=
    let d := decOutOf fo in
    evalExpr (##d`"writesCd").

  Definition instCd (inst : type Inst) : bits RegIdxSzReal :=
    evalExpr (TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (@getCd type inst)).

  (* The GPR the instruction writes (0: none), as the ALU routes it *)
  Definition decDst (fo : type FetchOut) : bits RegIdxSzReal :=
    if decWritesCd fo then instCd (fo.(Snd).(Fst)) else Zmod.zero.

  (* Field accessors of `AluOutUnion` and `ExecuteOut` *)
  Definition aluDstIdx (a : type AluOutUnion) : bits RegIdxSzReal := a.(Snd).(Fst).
  Definition aluDstVal (a : type AluOutUnion) : type FullECapWithTag := a.(Snd).(Snd).(Fst).
  Definition execMulDiv (x : type ExecuteOut) : type (Option MulDivUnion) := x.(Fst).
  Definition execDataMem (x : type ExecuteOut) : type (Option MemFenceUnion) := x.(Snd).(Fst).
  Definition execNextPcc (x : type ExecuteOut) : type FullECapWithTag :=
    x.(Snd).(Snd).(Snd).(Snd).(Fst).

  (* The mulDiv result the spec's deferred stage writes (`specExecuteDeferred`) *)
  Definition specMulDivWb (aluOut : type AluOutUnion) (execOut : type ExecuteOut) (rf : RfSt) : RfSt :=
    let mdOpt := execMulDiv execOut in
    if mdOpt.(Snd).(Fst)
    then
      let mdOp : type MulDivUnion := mdOpt.(Fst) in
      let addr : type Addr := (aluDstVal aluOut).(Snd).(Snd).(Fst) in
      let resAddr := evalLetExpr (@SpecMulDiv.MulDiv type addr mdOp) in
      writeGprVal core pcAddrInit (aluDstIdx aluOut) (mkMulDivCap resAddr) rf
    else rf.

  (* --- 2. Ghost Entries and Items --- *)

  (* An executed instruction: what was fetched, the impl's interrupt latches when it
   * executed, its ALU output (checked against the chain register file, so that the
   * entry's memory request does not depend on the chain position), and the dataMem
   * part of its execute output (its memory or fence request, if any). *)
  Record GEntry := mkGEntry {
    ge_fetchOut : type FetchOut ;
    ge_meip     : bool ;
    ge_mtip     : bool ;
    ge_aluOut   : type AluOutUnion ;
    ge_dm       : type (Option MemFenceUnion)
  }.

  Inductive GItem :=
  | GTick
  | GInst (e : GEntry).

  (* What the entry computes from the chain register file before it *)
  Definition geAluIn (rf0 : RfSt) (e : GEntry) : type AluInInstGroup :=
    evalRegRead core pcAddrInit (evalDecode (ge_fetchOut e)) rf0.

  Definition geAluOut (rf0 : RfSt) (e : GEntry) : type AluOutUnion :=
    evalAluOut (readPcc rf0) (geAluIn rf0 e).

  (* One instruction step of the chain, `rf0 -> rf1` *)
  Definition GInstStep (rf0 rf1 : RfSt) (e : GEntry) : Prop :=
    ge_aluOut e = geAluOut rf0 e /\
    evalIsInterruptPending core pcAddrInit (ge_meip e) (ge_mtip e) rf0 = false /\
    exists (execOut : type ExecuteOut) (rfMid : RfSt),
      SemAction defaultEnv
        (@executeNonDeferred core pcAddrInit type (readPcc rf0) (ge_meip e) (ge_mtip e) (ge_aluOut e))
        rf0 rfMid execOut /\
      execDataMem execOut = ge_dm e /\
      rf1 = specMulDivWb (ge_aluOut e) execOut (writePcc (execNextPcc execOut) rfMid).

  (* The chain: ticks and instruction steps, oldest first *)
  Inductive GChain : RfSt -> list GItem -> RfSt -> Prop :=
  | GChainNil :
      forall rf, GChain rf [] rf
  | GChainTick :
      forall rf G rf',
        GChain (evalIncrementMcycle core pcAddrInit rf) G rf' ->
        GChain rf (GTick :: G) rf'
  | GChainInst :
      forall rf0 rf1 e G rf',
        GInstStep rf0 rf1 e ->
        GChain rf1 G rf' ->
        GChain rf0 (GInst e :: G) rf'.

  (* --- 3. Basic Chain Lemmas --- *)

  Lemma GChain_app :
    forall rf0 G1 rf1 G2 rf2,
      GChain rf0 G1 rf1 -> GChain rf1 G2 rf2 -> GChain rf0 (G1 ++ G2) rf2.
  Proof.
    intros rf0 G1 rf1 G2 rf2 H1 H2.
    induction H1 as [rf | rf G rf' H IH | rf0 rf1 e G rf' Hs H IH]; cbn [app].
    - exact H2.
    - apply GChainTick; exact (IH H2).
    - eapply GChainInst; [exact Hs | exact (IH H2)].
  Qed.

  Lemma GChain_app_inv :
    forall G1 G2 rf0 rf2,
      GChain rf0 (G1 ++ G2) rf2 -> exists rf1, GChain rf0 G1 rf1 /\ GChain rf1 G2 rf2.
  Proof.
    induction G1 as [| it G1 IH]; intros G2 rf0 rf2 H; cbn [app] in H.
    - exists rf0; split; [apply GChainNil | exact H].
    - inversion H as [| rf G rf' Ht | rf0' rf1 e G rf' Hs Hr]; subst.
      + destruct (IH G2 _ _ Ht) as [rf1 [Ha Hb]].
        exists rf1; split; [apply GChainTick; exact Ha | exact Hb].
      + destruct (IH G2 _ _ Hr) as [rf1' [Ha Hb]].
        exists rf1'; split; [eapply GChainInst; [exact Hs | exact Ha] | exact Hb].
  Qed.

  Lemma GChain_snoc_tick :
    forall rf0 G rf1,
      GChain rf0 G rf1 ->
      GChain rf0 (G ++ [GTick]) (evalIncrementMcycle core pcAddrInit rf1).
  Proof.
    intros rf0 G rf1 H.
    eapply GChain_app; [exact H |].
    apply GChainTick; apply GChainNil.
  Qed.

  Lemma GChain_snoc_inst :
    forall rf0 G rf1 e rf2,
      GChain rf0 G rf1 -> GInstStep rf1 rf2 e -> GChain rf0 (G ++ [GInst e]) rf2.
  Proof.
    intros rf0 G rf1 e rf2 H Hs.
    eapply GChain_app; [exact H |].
    eapply GChainInst; [exact Hs | apply GChainNil].
  Qed.

  Lemma GChain_nil_inv :
    forall rf0 rf1, GChain rf0 [] rf1 -> rf1 = rf0.
  Proof.
    intros rf0 rf1 H; inversion H; reflexivity.
  Qed.

  (* --- 4. Commutation with GPR Writes, mulDiv Flushes and mcycle Ticks --- *)

  (* `x` (a register an entry reads or writes) is not `d` when both are non-zero *)
  Definition RegAvoid (d x : bits RegIdxSzReal) : Prop :=
    Zmod.eqb d Zmod.zero = false -> Zmod.eqb x Zmod.zero = false -> x <> d.

  (* An entry neither reads nor writes GPR `d` *)
  Definition EntryAvoids (e : GEntry) (d : bits RegIdxSzReal) : Prop :=
    RegAvoid d (decCs1 (ge_fetchOut e)) /\
    RegAvoid d (decCs2 (ge_fetchOut e)) /\
    RegAvoid d (aluDstIdx (ge_aluOut e)).

  Definition ChainAvoids (G : list GItem) (d : bits RegIdxSzReal) : Prop :=
    forall e, In (GInst e) G -> EntryAvoids e d.

  Lemma readPcc_writeGprVal :
    forall d v rf, readPcc (writeGprVal core pcAddrInit d v rf) = readPcc rf.
  Proof.
    intros d v rf; unfold readPcc; apply readGpr_zero_writeGprVal.
  Qed.

  Lemma evalIsInterruptPending_writeGprVal :
    forall meip mtip d v rf,
      evalIsInterruptPending core pcAddrInit meip mtip (writeGprVal core pcAddrInit d v rf) =
      evalIsInterruptPending core pcAddrInit meip mtip rf.
  Proof.
    intros meip mtip d v rf.
    assert (Hr : forall i, evalReadRegsList (csrPathsWithKind core pcAddrInit) i
                             (writeGprVal core pcAddrInit d v rf) =
                           evalReadRegsList (csrPathsWithKind core pcAddrInit) i rf)
      by (intros i; exact (readCsr_writeGprVal core pcAddrInit i d v rf)).
    unfold evalIsInterruptPending; rewrite !Hr; reflexivity.
  Qed.

  Lemma geAluIn_writeGprVal :
    forall e d v rf,
      EntryAvoids e d -> geAluIn (writeGprVal core pcAddrInit d v rf) e = geAluIn rf e.
  Proof.
    intros e d v rf [H1 [H2 _]].
    unfold geAluIn; apply evalRegRead_writeGprVal; [exact H1 | exact H2].
  Qed.

  Lemma geAluOut_writeGprVal :
    forall e d v rf,
      EntryAvoids e d -> geAluOut (writeGprVal core pcAddrInit d v rf) e = geAluOut rf e.
  Proof.
    intros e d v rf Hav.
    unfold geAluOut; rewrite readPcc_writeGprVal, (geAluIn_writeGprVal e d v rf Hav).
    reflexivity.
  Qed.

  Lemma writePcc_writeGprVal :
    forall p d v rf,
      writePcc p (writeGprVal core pcAddrInit d v rf) = writeGprVal core pcAddrInit d v (writePcc p rf).
  Proof.
    intros p d v rf; unfold writePcc.
    symmetry; apply writeGprVal_updGpr_zero_comm.
  Qed.

  Lemma specMulDivWb_writeGprVal :
    forall a x d v rf,
      RegAvoid d (aluDstIdx a) ->
      specMulDivWb a x (writeGprVal core pcAddrInit d v rf) =
      writeGprVal core pcAddrInit d v (specMulDivWb a x rf).
  Proof.
    intros a x d v rf Hav.
    unfold specMulDivWb.
    destruct ((execMulDiv x).(Snd).(Fst)); [| reflexivity].
    apply writeGprVal_comm.
    intros Hx Hd; exact (Hav Hd Hx).
  Qed.

  Lemma GInstStep_writeGprVal :
    forall rf0 rf1 e d v,
      EntryAvoids e d ->
      GInstStep rf0 rf1 e ->
      GInstStep (writeGprVal core pcAddrInit d v rf0) (writeGprVal core pcAddrInit d v rf1) e.
  Proof.
    intros rf0 rf1 e d v Hav [Halu [Hint [execOut [rfMid [Hsem [Hdm Hrf1]]]]]].
    split; [rewrite (geAluOut_writeGprVal e d v rf0 Hav); exact Halu |].
    split; [rewrite evalIsInterruptPending_writeGprVal; exact Hint |].
    exists execOut, (writeGprVal core pcAddrInit d v rfMid); split; [| split; [exact Hdm |]].
    - rewrite readPcc_writeGprVal.
      apply SemAction_executeNonDeferred_writeGprVal; [| exact Hsem].
      destruct Hav as [_ [_ Hdst]].
      intros Hd Hx Heq; exact (Hdst Hd Hx (eq_sym Heq)).
    - rewrite Hrf1, writePcc_writeGprVal.
      symmetry; apply specMulDivWb_writeGprVal.
      destruct Hav as [_ [_ Hdst]]; exact Hdst.
  Qed.

  Lemma evalIncrementMcycle_writeGprVal :
    forall d v rf,
      evalIncrementMcycle core pcAddrInit (writeGprVal core pcAddrInit d v rf) =
      writeGprVal core pcAddrInit d v (evalIncrementMcycle core pcAddrInit rf).
  Proof.
    intros d v rf; rewrite !writeGprVal_unfold.
    destruct (negb (Zmod.eqb d Zmod.zero)); [| reflexivity].
    apply evalIncrementMcycle_updGpr_comm.
  Qed.

  Lemma GChain_writeGprVal :
    forall G rf0 rf' d v,
      ChainAvoids G d ->
      GChain rf0 G rf' ->
      GChain (writeGprVal core pcAddrInit d v rf0) G (writeGprVal core pcAddrInit d v rf').
  Proof.
    intros G rf0 rf' d v Hav H; revert Hav.
    induction H as [rf | rf G rf' H IH | rf0 rf1 e G rf' Hs H IH]; intros Hav.
    - apply GChainNil.
    - apply GChainTick.
      rewrite evalIncrementMcycle_writeGprVal.
      apply IH; intros e' Hin; apply Hav; right; exact Hin.
    - eapply GChainInst.
      + apply GInstStep_writeGprVal; [apply Hav; left; reflexivity | exact Hs].
      + apply IH; intros e' Hin; apply Hav; right; exact Hin.
  Qed.

  Lemma GChain_flushMulDivCaps :
    forall entries G rf0 rf',
      (forall m c, In (m, c) entries -> ChainAvoids G m) ->
      GChain rf0 G rf' ->
      GChain (flushMulDivCaps core pcAddrInit entries rf0) G
             (flushMulDivCaps core pcAddrInit entries rf').
  Proof.
    induction entries as [| [m c] rest IH]; intros G rf0 rf' Hav H; cbn [flushMulDivCaps].
    - exact H.
    - apply IH.
      + intros m' c' Hin; exact (Hav m' c' (or_intror Hin)).
      + apply GChain_writeGprVal; [exact (Hav m c (or_introl eq_refl)) | exact H].
  Qed.

  Lemma ChainAvoids_app :
    forall G1 G2 d, ChainAvoids G1 d -> ChainAvoids G2 d -> ChainAvoids (G1 ++ G2) d.
  Proof.
    intros G1 G2 d H1 H2 e Hin.
    apply in_app_or in Hin as [Hin | Hin]; [exact (H1 e Hin) | exact (H2 e Hin)].
  Qed.

  Lemma ChainAvoids_app_inv :
    forall G1 G2 d, ChainAvoids (G1 ++ G2) d -> ChainAvoids G1 d /\ ChainAvoids G2 d.
  Proof.
    intros G1 G2 d H; split; intros e Hin; apply H; apply in_or_app; [left | right]; exact Hin.
  Qed.

End GhostChain.
