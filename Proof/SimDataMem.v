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
From Cheriot.Proof Require Export TreeLemmas StateRel SimExecute.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. `implDataMemTree` STATE ACCESSORS & ACTION EVALUATION LEMMAS
 * =========================================================================== *)

Section DataMemTreeHelpers.
  Variable capacity : nat.

  Local Abbreviation dmTree := (implDataMemTree capacity).
  Local Abbreviation fTree := (fifoTree capacity MemFenceReq).

  Definition dm_inputFifo (dm : TreeState ElemState dmTree)
    : TreeState ElemState fTree :=
    dm.(Fst).(Fst).

  Definition dm_state (dm : TreeState ElemState dmTree)
    : type DataMemState :=
    dm.(Snd).(Fst).

  Definition dm_withInputFifo (dm : TreeState ElemState dmTree)
    (f : TreeState ElemState fTree) : TreeState ElemState dmTree :=
    ((f ,, dm.(Fst).(Snd)) ,, dm.(Snd)).

  Lemma evalActionPropGen_readState :
    forall {env : Env dmTree} (dm : TreeState ElemState dmTree) P,
      evalActionPropGen env (@readState capacity type) dm P <->
      P dm (dm_state dm).
  Proof.
    intros env dm P; reflexivity.
  Qed.

  Lemma evalActionPropGen_dataMemIsEmpty :
    forall {env : Env dmTree} (dm : TreeState ElemState dmTree) P,
      evalActionPropGen env (@dataMemIsEmpty capacity type) dm P <->
      evalActionPropGen (subEnv (np_dmInputFifo capacity) env dm)
        (@isEmpty capacity MemFenceReq type) (dm_inputFifo dm)
        (fun f' inEmpty =>
           P (dm_withInputFifo dm f')
             (andb inEmpty (Zmod.eqb ((dm_state dm).(Snd)) Zmod.zero))).
  Proof.
    intros env dm P.
    unfold dataMemIsEmpty.
    cbn [evalActionPropGen].
    rewrite (evalActionPropGen_liftAction (np_dmInputFifo capacity)).
    eapply evalActionPropGen_ext; intros f' inEmpty.
    cbn [evalActionPropGen evalExpr].
    reflexivity.
  Qed.

  Lemma evalActionPropGen_dataMemIsFull :
    forall {env : Env dmTree} (dm : TreeState ElemState dmTree) P,
      evalActionPropGen env (@dataMemIsFull capacity type) dm P <->
      evalActionPropGen (subEnv (np_dmInputFifo capacity) env dm)
        (@isFull capacity MemFenceReq type) (dm_inputFifo dm)
        (fun f' res => P (dm_withInputFifo dm f') res).
  Proof.
    intros env dm P.
    unfold dataMemIsFull.
    rewrite (evalActionPropGen_liftAction (np_dmInputFifo capacity)).
    reflexivity.
  Qed.

  Lemma evalActionPropGen_dataMemEnq :
    forall {env : Env dmTree}
           (dstIdx : bits RegIdxSzReal) (addr : type Addr) (op : type MemFenceUnion)
           (dm : TreeState ElemState dmTree) P,
      evalActionPropGen env (@dataMemEnq capacity type dstIdx addr op) dm P <->
      let req : type MemFenceReq := (dstIdx ,, (addr ,, (op ,, tt))) in
      evalActionPropGen (subEnv (np_dmInputFifo capacity) env dm)
        (@enq capacity MemFenceReq type req) (dm_inputFifo dm)
        (fun f' res => P (dm_withInputFifo dm f') res).
  Proof.
    intros env dstIdx addr op dm P.
    unfold dataMemEnq.
    cbn [evalActionPropGen evalExpr].
    rewrite (evalActionPropGen_liftAction (np_dmInputFifo capacity)).
    reflexivity.
  Qed.

End DataMemTreeHelpers.

(* ===========================================================================
 * 2. `ImplDataMem` CORE WRITEBACK & STAGE FRAME LEMMAS
 * =========================================================================== *)

Section DataMemCoreLemmas.
  Variable capacity : nat.
  Variable pcAddrInit : Z.
  Variable bpT fetchT decodeT mulDivT : Tree Elem.
  Variable executeIfc : forall ty, @ExecuteIfc ty.
  Variable memIfc : forall ty, @MemIfc ty.

  Local Abbreviation rTree := (rfTree pcAddrInit).
  Local Abbreviation mTree := (memIfc type).(memTree).
  Local Abbreviation eTree := (executeIfc type).(executeTree).
  Local Abbreviation dmTree := (implDataMemTree capacity).
  Local Abbreviation cTree := (coreTree rTree bpT mTree fetchT decodeT eTree dmTree mulDivT).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList.

  Definition dmCore_rf (c : TreeState ElemState cTree) : TreeState ElemState rTree :=
    c.(Fst).(Fst).

  Definition dmCore_waitBits (c : TreeState ElemState cTree) : TreeState ElemState waitBitsTree :=
    c.(Snd).(Fst).(Fst).

  Definition evalCommitWb
    (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
    (c : TreeState ElemState cTree) : TreeState ElemState cTree :=
    if negb (Zmod.eqb dstIdx Zmod.zero)
    then
      ((evalWriteRegsList (gprPathsWithKind pcAddrInit) dstIdx dstVal (dmCore_rf c) ,, c.(Fst).(Snd)) ,,
       ((evalWriteRegsListHelper 1%nat gprWaitPathsWithKind dstIdx false (dmCore_waitBits c) ,, c.(Snd).(Fst).(Snd)) ,,
        c.(Snd).(Snd)))
    else c.

  Lemma evalActionPropGen_commitWb :
    forall {env : Env cTree}
           (dstIdx : bits RegIdxSzReal) (dstVal : type FullECapWithTag)
           (c : TreeState ElemState cTree) P,
      evalActionPropGen env
        (@ImplDataMem.commitWb capacity pcAddrInit bpT fetchT decodeT mulDivT
                               executeIfc memIfc type dstIdx dstVal) c P <->
      P (evalCommitWb dstIdx dstVal c) Zmod.zero.
  Proof.
    intros env dstIdx dstVal c P.
    unfold ImplDataMem.commitWb, evalCommitWb.
    cbn [evalActionPropGen evalExpr isNotZero isZero evalNot isEq KindCustomInd getDefault].
    destruct (negb (Zmod.eqb dstIdx Zmod.zero)) eqn:Hnz.
    - cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@ImplDataMem.np_rf capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)).
      rewrite (evalActionPropGen_writeRegsList (gprPathsWithKind pcAddrInit)
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type FullECapWithTag dstVal)).
      cbn [evalActionPropGen evalExpr].
      rewrite (evalActionPropGen_liftAction
                 (@ImplDataMem.np_waitBits capacity pcAddrInit bpT fetchT decodeT mulDivT executeIfc memIfc type)).
      unfold writeGprWaitBit.
      rewrite (evalActionPropGen_writeRegsListHelper gprWaitPathsWithKind 1%nat
                 (Var type (Bit RegIdxSzReal) dstIdx)
                 (Var type Bool false)).
      cbn [evalActionPropGen evalExpr].
      reflexivity.
    - cbn [evalActionPropGen evalExpr]; reflexivity.
  Qed.

End DataMemCoreLemmas.
