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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Export SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Export Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Export TreeLemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. SUBTREE ACCESSORS FOR `specSysTree` AND `implSysTree`
 * =========================================================================== *)

Section SubtreeAccessors.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).

  Local Abbreviation sTree := (@specSysTree core pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).

  Definition specRf (s : TreeState DomainElemState sTree)
    : TreeState DomainElemState (rfTree core pcAddrInit) :=
    Fst (Fst (Fst s)).

  Definition specMem (s : TreeState DomainElemState sTree)
    : TreeState DomainElemState (specMemTree regions) :=
    Fst (Fst (Snd (Fst s))).

  Definition implCore (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState
        (coreTree core (rfTree core pcAddrInit) implBpTree (implMemTree regions)
                  (implFetchTree core pcAddrInit fetchCapacity instCapacity)
                  (implDecodeTree core decodeCapacity)
                  (implExecuteTree core)
                  (implDataMemTree core dataMemCapacity)
                  (implMulDivTree core mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)) :=
    Fst s.

  Definition implRf (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (rfTree core pcAddrInit) :=
    Fst (Fst (Fst s)).

  Definition implWaitBits (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (waitBitsTree core) :=
    Fst (Fst (Snd (Fst s))).

  Definition implBp (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState implBpTree :=
    Fst (Fst (Snd (Snd (Fst s)))).

  Definition implMem (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (implMemTree regions) :=
    Fst (Fst (Snd (Snd (Snd (Fst s))))).

  Definition implFetch (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (implFetchTree core pcAddrInit fetchCapacity instCapacity) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Fst s)))))).

  Definition implDecode (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (implDecodeTree core decodeCapacity) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Fst s))))))).

  Definition implExecute (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (implExecuteTree core) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Snd (Fst s)))))))).

  Definition implDataMem (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (implDataMemTree core dataMemCapacity) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Snd (Snd (Fst s))))))))).

  Definition implMulDiv (s : TreeState DomainElemState iTree)
    : TreeState DomainElemState (implMulDivTree core mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Snd (Snd (Snd (Fst s)))))))))).

  Lemma readSubTreeState_spec_np_rf :
    forall (s : TreeState DomainElemState sTree),
      readSubTreeState (@Spec.np_rf core pcAddrInit regions) s = specRf s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_spec_np_mem :
    forall (s : TreeState DomainElemState sTree),
      readSubTreeState (@Spec.np_mem core pcAddrInit regions) s = specMem s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_core :
    forall (s : TreeState DomainElemState iTree),
      readSubTreeState (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s = implCore s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_rf :
    forall (s : TreeState DomainElemState iTree),
      readSubTreeState (@Impl.np_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s = implRf s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_mem :
    forall (s : TreeState DomainElemState iTree),
      readSubTreeState (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s = implMem s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_fetch :
    forall (s : TreeState DomainElemState iTree),
      readSubTreeState (@Impl.np_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s = implFetch s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_decode :
    forall (s : TreeState DomainElemState iTree),
      readSubTreeState (@Impl.np_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s = implDecode s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_execute :
    forall (s : TreeState DomainElemState iTree),
      readSubTreeState (@Impl.np_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s = implExecute s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma spec_write_np_rf_accessors :
    forall (s : TreeState DomainElemState sTree) rf',
      let s' := writeSubTreeState (@Spec.np_rf core pcAddrInit regions) s rf' in
      specRf s' = rf' /\ specMem s' = specMem s.
  Proof.
    intros s rf'; split; reflexivity.
  Qed.

  Lemma spec_write_np_mem_accessors :
    forall (s : TreeState DomainElemState sTree) m',
      let s' := writeSubTreeState (@Spec.np_mem core pcAddrInit regions) s m' in
      specRf s' = specRf s /\ specMem s' = m'.
  Proof.
    intros s m'; split; reflexivity.
  Qed.

  Lemma impl_write_np_rf_accessors :
    forall (s : TreeState DomainElemState iTree) rf',
      let s' := writeSubTreeState (@Impl.np_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s rf' in
      implRf s' = rf' /\
      implWaitBits s' = implWaitBits s /\
      implBp s' = implBp s /\
      implMem s' = implMem s /\
      implFetch s' = implFetch s /\
      implDecode s' = implDecode s /\
      implExecute s' = implExecute s /\
      implDataMem s' = implDataMem s /\
      implMulDiv s' = implMulDiv s.
  Proof.
    intros s rf'; repeat split; reflexivity.
  Qed.

  Lemma impl_write_np_mem_accessors :
    forall (s : TreeState DomainElemState iTree) m',
      let s' := writeSubTreeState (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions) s m' in
      implRf s' = implRf s /\
      implWaitBits s' = implWaitBits s /\
      implBp s' = implBp s /\
      implMem s' = m' /\
      implFetch s' = implFetch s /\
      implDecode s' = implDecode s /\
      implExecute s' = implExecute s /\
      implDataMem s' = implDataMem s /\
      implMulDiv s' = implMulDiv s.
  Proof.
    intros s m'; repeat split; reflexivity.
  Qed.
End SubtreeAccessors.

Arguments specRf {core pcAddrInit regions} s.
Arguments specMem {core pcAddrInit regions} s.
Arguments implCore {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implRf {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implWaitBits {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implBp {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implMem {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implFetch {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implDecode {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implExecute {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implDataMem {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments implMulDiv {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments readSubTreeState_spec_np_rf {core pcAddrInit regions} s.
Arguments readSubTreeState_spec_np_mem {core pcAddrInit regions} s.
Arguments readSubTreeState_impl_np_core {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments readSubTreeState_impl_np_rf {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments readSubTreeState_impl_np_mem {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments readSubTreeState_impl_np_fetch {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments readSubTreeState_impl_np_decode {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.
Arguments readSubTreeState_impl_np_execute {core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions} s.

(* ===========================================================================
 * 2. MEMORY REGION PROJECTION (`projImplRegionSpecState` / `projImplMemSpecState`)
 * =========================================================================== *)

Section MemProjection.
  Variable dom : string.

  Definition implRegionExtraChildren (r : MemRegion dom) : list (Tree DomainElem) :=
    match r.(regionKind) with
    | InternalMem isAccessible _ _ => implInternalMemRegionExtraChildren r isAccessible
    | ExternalMem => implExternalMemRegionExtraChildren r
    | CustomMem children _ _ _ _ => implCustomMemRegionExtraChildren r
    end.

  Definition projImplRegionSpecState (r : MemRegion dom)
    (s : TreeState DomainElemState (implMemRegionTree r))
    : TreeState DomainElemState (memRegionTree r) :=
    match r.(regionKind) as rk
      return TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                | ExternalMem => implExternalMemRegionTree r
                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                end) ->
             TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                | ExternalMem => externalMemRegionTree r
                | CustomMem children _ _ _ _ => customMemRegionTree r children
                end)
    with
    | InternalMem _ _ _ => fun st => Fst st
    | ExternalMem => fun st => Fst st
    | CustomMem _ _ _ _ _ => fun st => Fst st
    end s.

  Definition projImplRegionExtraState (r : MemRegion dom)
    (s : TreeState DomainElemState (implMemRegionTree r))
    : TreeState DomainElemState (Node "" (implRegionExtraChildren r)) :=
    match r.(regionKind) as rk
      return TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                | ExternalMem => implExternalMemRegionTree r
                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                end) ->
             TreeState DomainElemState
               (Node ""
                 (match rk with
                  | InternalMem isAccessible _ _ => implInternalMemRegionExtraChildren r isAccessible
                  | ExternalMem => implExternalMemRegionExtraChildren r
                  | CustomMem children _ _ _ _ => implCustomMemRegionExtraChildren r
                  end))
    with
    | InternalMem _ _ _ => fun st => Snd st
    | ExternalMem => fun st => Snd st
    | CustomMem _ _ _ _ _ => fun st => Snd st
    end s.

  Definition writeImplRegionSpecState (r : MemRegion dom)
    (s : TreeState DomainElemState (implMemRegionTree r))
    (m : TreeState DomainElemState (memRegionTree r))
    : TreeState DomainElemState (implMemRegionTree r) :=
    match r.(regionKind) as rk
      return TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                | ExternalMem => implExternalMemRegionTree r
                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                end) ->
             TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                | ExternalMem => externalMemRegionTree r
                | CustomMem children _ _ _ _ => customMemRegionTree r children
                end) ->
             TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                | ExternalMem => implExternalMemRegionTree r
                | CustomMem children _ _ _ _ => implCustomMemRegionTree r children
                end)
    with
    | InternalMem _ _ _ => fun st m' => (m' ,, Snd st)
    | ExternalMem => fun st m' => (m' ,, Snd st)
    | CustomMem _ _ _ _ _ => fun st m' => (m' ,, Snd st)
    end s m.

  Lemma projImplRegionSpecState_writeImplRegionSpecState :
    forall (r : MemRegion dom)
           (s : TreeState DomainElemState (implMemRegionTree r))
           (m : TreeState DomainElemState (memRegionTree r)),
      projImplRegionSpecState r (writeImplRegionSpecState r s m) = m.
  Proof.
    intros r s m.
    unfold projImplRegionSpecState, writeImplRegionSpecState, implMemRegionTree, memRegionTree in *.
    revert s m; destruct (r.(regionKind)); intros s m; reflexivity.
  Qed.

  Lemma projImplRegionExtraState_writeImplRegionSpecState :
    forall (r : MemRegion dom)
           (s : TreeState DomainElemState (implMemRegionTree r))
           (m : TreeState DomainElemState (memRegionTree r)),
      projImplRegionExtraState r (writeImplRegionSpecState r s m) =
      projImplRegionExtraState r s.
  Proof.
    intros r s m.
    unfold projImplRegionExtraState, writeImplRegionSpecState, implRegionExtraChildren, implMemRegionTree, memRegionTree in *.
    revert s m; destruct (r.(regionKind)); intros s m; reflexivity.
  Qed.

  Lemma evalActionPropGen_liftToImplRegion :
    forall (r : MemRegion dom) {k : Kind}
           (act : Action type (memRegionTree r) k)
           (s : TreeState DomainElemState (implMemRegionTree r))
           (P : TreeState DomainElemState (implMemRegionTree r) -> type k -> Prop),
      evalActionPropGen (liftToImplRegion act) s P <->
      evalActionPropGen act (projImplRegionSpecState r s)
        (fun m' v => P (writeImplRegionSpecState r s m') v).
  Proof.
    intros r k act s P.
    unfold liftToImplRegion, projImplRegionSpecState, writeImplRegionSpecState, implMemRegionTree, memRegionTree in *.
    revert act s P; destruct (r.(regionKind)); intros act s P;
      apply (evalActionPropGen_liftAction child0Path act s P).
  Qed.

  Lemma SemAction_liftToImplRegion :
    forall (r : MemRegion dom) {k : Kind}
           (act : Action type (memRegionTree r) k)
           (s s' : TreeState DomainElemState (implMemRegionTree r)) (v : type k),
      SemAction (liftToImplRegion act) s s' v <->
      exists m',
        SemAction act (projImplRegionSpecState r s) m' v /\
        s' = writeImplRegionSpecState r s m'.
  Proof.
    intros r k act s s' v.
    rewrite !SemAction_iff_evalActionPropGen.
    rewrite evalActionPropGen_liftToImplRegion.
    rewrite evalActionPropGen_ex_iff.
    split; intros [m' [Hm' Heq]]; exists m'; rewrite !SemAction_iff_evalActionPropGen in *; auto.
  Qed.

  Fixpoint implMemExtraTree (regions : list (MemRegion dom)) : Tree DomainElem :=
    match regions with
    | [] => Node "" []
    | r :: rs => Node "" [ Node "" (implRegionExtraChildren r) ; implMemExtraTree rs ]
    end.

  Fixpoint projImplMemSpecState (regions : list (MemRegion dom))
    : TreeState DomainElemState (implRegionsTree regions) ->
      TreeState DomainElemState (specMemTree regions) :=
    match regions return TreeState DomainElemState (implRegionsTree regions) ->
                         TreeState DomainElemState (specMemTree regions) with
    | [] => fun _ => tt
    | r :: rs => fun s =>
        (projImplRegionSpecState r (Fst s) ,,
         (projImplMemSpecState rs (Fst (Snd s)) ,, tt))
    end.

  Fixpoint projImplMemExtraState (regions : list (MemRegion dom))
    : TreeState DomainElemState (implRegionsTree regions) ->
      TreeState DomainElemState (implMemExtraTree regions) :=
    match regions return TreeState DomainElemState (implRegionsTree regions) ->
                         TreeState DomainElemState (implMemExtraTree regions) with
    | [] => fun _ => tt
    | r :: rs => fun s =>
        (projImplRegionExtraState r (Fst s) ,,
         (projImplMemExtraState rs (Fst (Snd s)) ,, tt))
    end.

  Fixpoint writeImplMemSpecState (regions : list (MemRegion dom))
    : TreeState DomainElemState (implRegionsTree regions) ->
      TreeState DomainElemState (specMemTree regions) ->
      TreeState DomainElemState (implRegionsTree regions) :=
    match regions return TreeState DomainElemState (implRegionsTree regions) ->
                         TreeState DomainElemState (specMemTree regions) ->
                         TreeState DomainElemState (implRegionsTree regions) with
    | [] => fun s _ => s
    | r :: rs => fun s m =>
        (writeImplRegionSpecState r (Fst s) (Fst m) ,,
         (writeImplMemSpecState rs (Fst (Snd s)) (Fst (Snd m)) ,, Snd (Snd s)))
    end.

  Lemma projImplMemSpecState_writeImplMemSpecState :
    forall (regions : list (MemRegion dom))
           (s : TreeState DomainElemState (implRegionsTree regions))
           (m : TreeState DomainElemState (specMemTree regions)),
      projImplMemSpecState regions (writeImplMemSpecState regions s m) = m.
  Proof.
    induction regions as [| r rs IH]; intros s m; cbn [projImplMemSpecState writeImplMemSpecState].
    - destruct m; reflexivity.
    - destruct m as [mr [mrs u]]; destruct u.
      cbn [Fst Snd].
      rewrite projImplRegionSpecState_writeImplRegionSpecState, IH.
      reflexivity.
  Qed.

  Lemma projImplMemExtraState_writeImplMemSpecState :
    forall (regions : list (MemRegion dom))
           (s : TreeState DomainElemState (implRegionsTree regions))
           (m : TreeState DomainElemState (specMemTree regions)),
      projImplMemExtraState regions (writeImplMemSpecState regions s m) =
      projImplMemExtraState regions s.
  Proof.
    induction regions as [| r rs IH]; intros s m; cbn [projImplMemExtraState writeImplMemSpecState].
    - reflexivity.
    - cbn [Fst Snd].
      rewrite projImplRegionExtraState_writeImplRegionSpecState, IH.
      reflexivity.
  Qed.

  Lemma writeImplRegionSpecState_projImplRegionSpecState :
    forall (r : MemRegion dom)
           (s : TreeState DomainElemState (implMemRegionTree r)),
      writeImplRegionSpecState r s (projImplRegionSpecState r s) = s.
  Proof.
    intros r s.
    unfold projImplRegionSpecState, writeImplRegionSpecState, implMemRegionTree in *.
    revert s; destruct (r.(regionKind)); intros [s0 s1]; reflexivity.
  Qed.

  Lemma writeImplMemSpecState_projImplMemSpecState :
    forall (regions : list (MemRegion dom))
           (s : TreeState DomainElemState (implRegionsTree regions)),
      writeImplMemSpecState regions s (projImplMemSpecState regions s) = s.
  Proof.
    induction regions as [| r rs IH]; intros s; cbn [projImplMemSpecState writeImplMemSpecState].
    - reflexivity.
    - destruct s as [sr [srs u]].
      cbn [Fst Snd].
      rewrite writeImplRegionSpecState_projImplRegionSpecState, IH.
      reflexivity.
  Qed.

  Theorem evalActionPropGen_implNthRegionAction :
    forall (idx : nat) (regions : list (MemRegion dom)) (r0 : MemRegion dom)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           (act : Action type (memRegionTree r0) k)
           (s : TreeState DomainElemState (implRegionsTree regions))
           (P : TreeState DomainElemState (implRegionsTree regions) -> type k -> Prop),
      evalActionPropGen (@implNthRegionAction dom type idx regions r0 pf k act) s P <->
      evalActionPropGen (@nthRegionAction dom type idx regions r0 pf k act)
        (projImplMemSpecState regions s)
        (fun m' v => P (writeImplMemSpecState regions s m') v).
  Proof.
    induction idx as [| idx' IH]; intros [| r rs] r0 pf k act s P;
      try discriminate pf.
    - cbn [implNthRegionAction nthRegionAction projImplMemSpecState].
      rewrite !evalActionPropGen_liftAction.
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd writeSubTreeState writeSubTreeState_child writeImplMemSpecState].
      rewrite (evalActionPropGen_liftToImplRegion r).
      apply evalActionPropGen_ext; intros m' v.
      rewrite writeImplMemSpecState_projImplMemSpecState; reflexivity.
    - cbn [implNthRegionAction nthRegionAction projImplMemSpecState].
      rewrite !evalActionPropGen_liftAction.
      cbn [child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child Fst Snd writeSubTreeState writeSubTreeState_child writeImplMemSpecState].
      rewrite (IH rs r0 pf k act (Fst (Snd s))).
      apply evalActionPropGen_ext; intros m' v.
      rewrite writeImplRegionSpecState_projImplRegionSpecState.
      destruct (Snd (Snd s)); reflexivity.
  Qed.

  Theorem SemAction_implNthRegionAction :
    forall (idx : nat) (regions : list (MemRegion dom)) (r0 : MemRegion dom)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           (act : Action type (memRegionTree r0) k)
           (s s' : TreeState DomainElemState (implRegionsTree regions))
           (v : type k),
      SemAction (@implNthRegionAction dom type idx regions r0 pf k act) s s' v ->
      SemAction (@nthRegionAction dom type idx regions r0 pf k act)
        (projImplMemSpecState regions s)
        (projImplMemSpecState regions s') v /\
      projImplMemExtraState regions s' = projImplMemExtraState regions s /\
      s' = writeImplMemSpecState regions s (projImplMemSpecState regions s').
  Proof.
    intros idx regions r0 pf k act s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite evalActionPropGen_implNthRegionAction in Hsem.
    apply evalActionPropGen_ex_iff in Hsem.
    destruct Hsem as [m' [Hm' Hs']]; subst s'.
    rewrite <- SemAction_iff_evalActionPropGen in Hm'.
    rewrite projImplMemSpecState_writeImplMemSpecState.
    rewrite projImplMemExtraState_writeImplMemSpecState.
    repeat split; auto.
  Qed.

  Corollary SemAction_implMemNthRegionAction :
    forall (regions : list (MemRegion dom)) (idx : nat) (r0 : MemRegion dom)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           (act : Action type (memRegionTree r0) k)
           (s s' : TreeState DomainElemState (implMemTree regions))
           (v : type k),
      SemAction (@implMemNthRegionAction dom regions type idx r0 pf k act) s s' v ->
      SemAction (@nthRegionAction dom type idx regions r0 pf k act)
        (projImplMemSpecState regions s)
        (projImplMemSpecState regions s') v /\
      projImplMemExtraState regions s' = projImplMemExtraState regions s /\
      s' = writeImplMemSpecState regions s (projImplMemSpecState regions s').
  Proof.
    intros regions idx r0 pf k act s s' v Hsem.
    exact (SemAction_implNthRegionAction idx regions r0 pf act s s' v Hsem).
  Qed.
End MemProjection.

Arguments projImplRegionSpecState_writeImplRegionSpecState {dom} r s m.
Arguments projImplRegionExtraState_writeImplRegionSpecState {dom} r s m.
Arguments evalActionPropGen_liftToImplRegion {dom} r {k} act s P.

(* ===========================================================================
 * 3. `incrementMcycle` AND `implTickCycle` / `specTickCycle` SIMULATION
 * =========================================================================== *)

Section TickCycleSim.
  Variable dom : string.
  Variable pcAddrInit : Z.

  Definition evalIncrementMcycle
    (rf : TreeState DomainElemState (rfTree dom pcAddrInit))
    : TreeState DomainElemState (rfTree dom pcAddrInit) :=
    let lowIdx  := evalExpr ($(getCsrPhysicalIdx "mcycle") : Expr type (Bit CsrIdxSz)) in
    let highIdx := evalExpr ($(getCsrPhysicalIdx "mcycleh") : Expr type (Bit CsrIdxSz)) in
    let currLow  := readCsr dom pcAddrInit lowIdx rf in
    let currHigh := readCsr dom pcAddrInit highIdx rf in
    let newVal   := evalExpr (Add [ {< #currHigh, #currLow >} ; $1 ] : Expr type (Bit DXlen)) in
    let rf1 := updCsr dom pcAddrInit lowIdx
                 (evalExpr (TruncLsb Xlen Xlen #newVal : Expr type (Bit Xlen))) rf in
    updCsr dom pcAddrInit highIdx
      (evalExpr (TruncMsb Xlen Xlen #newVal : Expr type (Bit Xlen))) rf1.

  Lemma evalActionPropGen_incrementMcycle :
    forall (rf : TreeState DomainElemState (rfTree dom pcAddrInit)) P,
      evalActionPropGen (@incrementMcycle dom pcAddrInit type) rf P <->
      P (evalIncrementMcycle rf) Zmod.zero.
  Proof.
    intros rf P.
    unfold incrementMcycle, evalIncrementMcycle, readCsr, updCsr.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_readRegsList.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_readRegsList.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_writeRegsList.
    cbn [evalActionPropGen].
    rewrite evalActionPropGen_writeRegsList.
    cbn [evalActionPropGen].
    reflexivity.
  Qed.

  Theorem SemAction_incrementMcycle_iff :
    forall (rf rf' : TreeState DomainElemState (rfTree dom pcAddrInit)) v,
      SemAction (@incrementMcycle dom pcAddrInit type) rf rf' v <->
      rf' = evalIncrementMcycle rf /\ v = Zmod.zero.
  Proof.
    intros rf rf' v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_incrementMcycle.
    split; intros [? ?]; subst; auto.
  Qed.

  Lemma evalIncrementMcycle_Fst :
    forall rf,
      (evalIncrementMcycle rf).(Fst) = rf.(Fst).
  Proof.
    intros rf; unfold evalIncrementMcycle; rewrite !updCsr_Fst; reflexivity.
  Qed.

  Lemma evalIncrementMcycle_Snd_Fst :
    forall rf,
      (evalIncrementMcycle rf).(Snd).(Fst) = rf.(Snd).(Fst).
  Proof.
    intros rf; unfold evalIncrementMcycle; rewrite !updCsr_Snd_Fst; reflexivity.
  Qed.

  Theorem evalIncrementMcycle_updGpr_comm :
    forall idx val rf,
      evalIncrementMcycle (updGpr dom pcAddrInit idx val rf) =
      updGpr dom pcAddrInit idx val (evalIncrementMcycle rf).
  Proof.
    intros idx val rf.
    unfold evalIncrementMcycle.
    rewrite !readCsr_updGpr, !updGpr_updCsr_comm.
    reflexivity.
  Qed.

  Theorem evalIncrementMcycle_updScr_comm :
    forall idx val rf,
      evalIncrementMcycle (updScr dom pcAddrInit idx val rf) =
      updScr dom pcAddrInit idx val (evalIncrementMcycle rf).
  Proof.
    intros idx val rf.
    unfold evalIncrementMcycle.
    rewrite !readCsr_updScr, !updScr_updCsr_comm.
    reflexivity.
  Qed.

  Theorem readGpr_evalIncrementMcycle :
    forall idx rf,
      readGpr dom pcAddrInit idx (evalIncrementMcycle rf) =
      readGpr dom pcAddrInit idx rf.
  Proof.
    intros idx rf; unfold evalIncrementMcycle; rewrite !readGpr_updCsr; reflexivity.
  Qed.

  Theorem readScr_evalIncrementMcycle :
    forall idx rf,
      readScr dom pcAddrInit idx (evalIncrementMcycle rf) =
      readScr dom pcAddrInit idx rf.
  Proof.
    intros idx rf; unfold evalIncrementMcycle; rewrite !readScr_updCsr; reflexivity.
  Qed.
End TickCycleSim.

(* ===========================================================================
 * 4. CLINT, PLIC, FENCE.I ACK, AND CAN-PROCEED STAGE SIMULATIONS
 * =========================================================================== *)

Section SystemDevicesSim.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (@specSysTree core pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation specMod := (@spec core pcAddrInit config regions clint revSpec plic).
  Local Abbreviation np_rf_i := (@Impl.np_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation np_mem_i := (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation np_fetch_i := (@Impl.np_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation np_decode_i := (@Impl.np_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation np_execute_i := (@Impl.np_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation np_rf_s := (@Spec.np_rf core pcAddrInit regions).
  Local Abbreviation np_mem_s := (@Spec.np_mem core pcAddrInit regions).

  (* --- 4A. Helper for lifting any mem-tree simulation to `iTree` / `sTree` --- *)

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

  Lemma SemAction_lift_np_mem_impl :
    forall {k : Kind} (act : Action type (implMemTree regions) k)
           (old1 new1 : TreeState DomainElemState iTree) (v : type k),
      SemAction (liftAction np_mem_i act) old1 new1 v <->
      exists m1',
        SemAction act (implMem old1) m1' v /\
        new1 = writeSubTreeState np_mem_i old1 m1'.
  Proof.
    intros k act old1 new1 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_impl_np_mem.
    split; intros [m1' [Hm1' Hnew1]]; exists m1';
      rewrite !SemAction_iff_evalActionPropGen in *; auto.
  Qed.

  Lemma SemAction_lift_np_mem_spec :
    forall {k : Kind} (act : Action type (specMemTree regions) k)
           (old2 new2 : TreeState DomainElemState sTree) (v : type k),
      SemAction (liftAction np_mem_s act) old2 new2 v <->
      exists m2',
        SemAction act (specMem old2) m2' v /\
        new2 = writeSubTreeState np_mem_s old2 m2'.
  Proof.
    intros k act old2 new2 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_spec_np_mem.
    split; intros [m2' [Hm2' Hnew2]]; exists m2';
      rewrite !SemAction_iff_evalActionPropGen in *; auto.
  Qed.

  Lemma SemAction_lift_np_rf_impl :
    forall {k : Kind} (act : Action type (rfTree core pcAddrInit) k)
           (old1 new1 : TreeState DomainElemState iTree) (v : type k),
      SemAction (liftAction np_rf_i act) old1 new1 v <->
      exists rf1',
        SemAction act (implRf old1) rf1' v /\
        new1 = writeSubTreeState np_rf_i old1 rf1'.
  Proof.
    intros k act old1 new1 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_impl_np_rf.
    split; intros [rf1' [Hrf1' Hnew1]]; exists rf1';
      rewrite !SemAction_iff_evalActionPropGen in *; auto.
  Qed.

  Lemma SemAction_lift_np_rf_spec :
    forall {k : Kind} (act : Action type (rfTree core pcAddrInit) k)
           (old2 new2 : TreeState DomainElemState sTree) (v : type k),
      SemAction (liftAction np_rf_s act) old2 new2 v <->
      exists rf2',
        SemAction act (specRf old2) rf2' v /\
        new2 = writeSubTreeState np_rf_s old2 rf2'.
  Proof.
    intros k act old2 new2 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_spec_np_rf.
    split; intros [rf2' [Hrf2' Hnew2]]; exists rf2';
      rewrite !SemAction_iff_evalActionPropGen in *; auto.
  Qed.

  (* --- 4B. `implTickCycle` -> `specTickCycle` --- *)

  Lemma In_specTickCycle_spec :
    In (@specTickCycle core pcAddrInit regions type)
       (map snd (specMod type)).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; left; reflexivity.
  Qed.

  Theorem sim_implTickCycle_step :
    forall (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      SemAction (@implTickCycle core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
      let mid2 := writeSubTreeState np_rf_s old2 (evalIncrementMcycle core pcAddrInit (specRf old2)) in
      new1 = writeSubTreeState np_rf_i old1 (evalIncrementMcycle core pcAddrInit (implRf old1)) /\
      v = Zmod.zero /\
      SemAction (@specTickCycle core pcAddrInit regions type) old2 mid2 Zmod.zero /\
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = evalIncrementMcycle core pcAddrInit (specRf old2) /\
      specMem mid2 = specMem old2.
  Proof.
    intros old1 new1 old2 v Hsem mid2.
    unfold implTickCycle in Hsem.
    apply SemAction_lift_np_rf_impl in Hsem as [rf1' [Hrf1' Hnew1]].
    apply SemAction_incrementMcycle_iff in Hrf1' as [Hrf1' Hv]; subst rf1' v.
    assert (Hspec : SemAction (@specTickCycle core pcAddrInit regions type) old2 mid2 Zmod.zero).
    { unfold specTickCycle.
      apply SemAction_lift_np_rf_spec.
      exists (evalIncrementMcycle core pcAddrInit (specRf old2)).
      split; [apply SemAction_incrementMcycle_iff; auto | reflexivity]. }
    repeat split; auto.
    eapply ConsAction with (a := @specTickCycle core pcAddrInit regions type).
    - apply In_specTickCycle_spec.
    - exact Hspec.
    - apply NilAction; reflexivity.
  Qed.

  (* --- 4C. `implTickTimer` and `implSampleMtipStep` (CLINT) --- *)

  Lemma In_specTickTimer_spec :
    In (@specTickTimer core pcAddrInit regions clint type)
       (map snd (specMod type)).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; right; left; reflexivity.
  Qed.

  Lemma In_specSampleMtipStep_spec :
    In (@specSampleMtipStep core pcAddrInit regions clint type)
       (map snd (specMod type)).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; right; right; left; reflexivity.
  Qed.

  Theorem sim_implTickTimer_step :
    forall (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction (@implTickTimer core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions clint type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction (@specTickTimer core pcAddrInit regions clint type) old2 mid2 v /\
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros old1 new1 old2 v Hmem Hsem mid2.
    unfold implTickTimer in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions clint.(clintIdx)
                (@clintRegion core regions clint) clint.(pfClint)
                (clintTick core type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction (@specTickTimer core pcAddrInit regions clint type) old2 mid2 v).
    { unfold specTickTimer, clintTickAction, clintAction.
      apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem | reflexivity]. }
    repeat split; auto.
    rewrite (Zmod_1_0 v) in Hspec.
    eapply ConsAction with (a := @specTickTimer core pcAddrInit regions clint type).
    - apply In_specTickTimer_spec.
    - exact Hspec.
    - apply NilAction; reflexivity.
  Qed.

  Theorem sim_implSampleMtipStep_step :
    forall (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction (@implSampleMtipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions clint type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction (@specSampleMtipStep core pcAddrInit regions clint type) old2 mid2 v /\
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros old1 new1 old2 v Hmem Hsem mid2.
    unfold implSampleMtipStep in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions clint.(clintIdx)
                (@clintRegion core regions clint) clint.(pfClint)
                (clintSampleMtip core type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction (@specSampleMtipStep core pcAddrInit regions clint type) old2 mid2 v).
    { unfold specSampleMtipStep, clintSampleMtipAction, clintAction.
      apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem | reflexivity]. }
    repeat split; auto.
    rewrite (Zmod_1_0 v) in Hspec.
    eapply ConsAction with (a := @specSampleMtipStep core pcAddrInit regions clint type).
    - apply In_specSampleMtipStep_spec.
    - exact Hspec.
    - apply NilAction; reflexivity.
  Qed.

  (* --- 4D. PLIC Steps (`implPlicClaimStep`, `implPlicSampleMeipStep`, `implPlicPendingsSteps`) --- *)

  Lemma In_specPlicClaimStep_spec :
    In (@specPlicClaimStep core pcAddrInit regions plic type)
       (map snd (specMod type)).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; left; reflexivity.
  Qed.

  Lemma In_specPlicSampleMeipStep_spec :
    In (@specPlicSampleMeipStep core pcAddrInit regions plic type)
       (map snd (specMod type)).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; left; reflexivity.
  Qed.

  Theorem sim_implPlicClaimStep_step :
    forall (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction (@implPlicClaimStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions plic type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction (@specPlicClaimStep core pcAddrInit regions plic type) old2 mid2 v /\
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros old1 new1 old2 v Hmem Hsem mid2.
    unfold implPlicClaimStep in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                (@plicRegion core _ regions plic) plic.(pfPlic)
                (@updateClaim core _ type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction (@specPlicClaimStep core pcAddrInit regions plic type) old2 mid2 v).
    { unfold specPlicClaimStep, plicClaimStep, plicAction.
      apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem | reflexivity]. }
    repeat split; auto.
    rewrite (Zmod_1_0 v) in Hspec.
    eapply ConsAction with (a := @specPlicClaimStep core pcAddrInit regions plic type).
    - apply In_specPlicClaimStep_spec.
    - exact Hspec.
    - apply NilAction; reflexivity.
  Qed.

  Theorem sim_implPlicSampleMeipStep_step :
    forall (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction (@implPlicSampleMeipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions plic type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction (@specPlicSampleMeipStep core pcAddrInit regions plic type) old2 mid2 v /\
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros old1 new1 old2 v Hmem Hsem mid2.
    unfold implPlicSampleMeipStep in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                (@plicRegion core _ regions plic) plic.(pfPlic)
                (@plicSampleMeip core _ type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction (@specPlicSampleMeipStep core pcAddrInit regions plic type) old2 mid2 v).
    { unfold specPlicSampleMeipStep, plicSampleMeipStep, plicAction.
      apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem | reflexivity]. }
    repeat split; auto.
    rewrite (Zmod_1_0 v) in Hspec.
    eapply ConsAction with (a := @specPlicSampleMeipStep core pcAddrInit regions plic type).
    - apply In_specPlicSampleMeipStep_spec.
    - exact Hspec.
    - apply NilAction; reflexivity.
  Qed.

  (* --- 4E. `implCollectIrqActions` vs `collectIrqActions` and `implPlicPendingsSteps` --- *)

  Lemma Forall2_map_both :
    forall {A B C D : Type} (R : C -> D -> Prop) (Q : A -> B -> Prop)
           (f : A -> C) (g : B -> D) (l1 : list A) (l2 : list B),
      (forall a b, Q a b -> R (f a) (g b)) ->
      Forall2 Q l1 l2 ->
      Forall2 R (map f l1) (map g l2).
  Proof.
    intros A B C D R Q f g l1 l2 Himp Hrel.
    induction Hrel; cbn [map]; constructor; auto.
  Qed.

  Lemma Forall2_irqActions_with_uart :
    Forall2 (fun (aI : Action type (implMemTree regions) Bool)
                 (aS : Action type (specMemTree regions) Bool) =>
               forall (s s' : TreeState DomainElemState (implMemTree regions)) (v : bool),
                 SemAction aI s s' v ->
                 SemAction aS (projImplMemSpecState core regions s) (projImplMemSpecState core regions s') v /\
                 projImplMemExtraState core regions s' = projImplMemExtraState core regions s)
            (implMemCollectIrqActions regions type ++
             [@implMemNthRegionAction core regions type plic.(plicIdx) (@plicRegion core _ regions plic) plic.(pfPlic) Bool
                (Recv "uartIrq" (plicUartIrqPath core (S (S (length (collectIrqActions regions))))) (fun v => Return #v))])
            (map (fun f => f type) (collectIrqActions regions) ++
             [@plicUartIrqAction core (S (S (length (collectIrqActions regions)))) regions plic type]).
  Proof.
    apply Forall2_app.
    - unfold implMemCollectIrqActions.
      assert (Hgen : forall (rs : list (MemRegion core)),
                Forall2 (fun (aI : Action type (implRegionsTree rs) Bool)
                             (aS : Action type (specMemTree rs) Bool) =>
                           forall (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bool),
                             SemAction aI s s' v ->
                             SemAction aS (projImplMemSpecState core rs s) (projImplMemSpecState core rs s') v /\
                             projImplMemExtraState core rs s' = projImplMemExtraState core rs s)
                        (map (fun f => f type) (implCollectIrqActions rs))
                        (map (fun f => f type) (collectIrqActions rs))).
      { induction rs as [| r rs IH]; cbn [implCollectIrqActions collectIrqActions].
        - constructor.
        - assert (Hrest :
            Forall2 (fun (aI : Action type (implRegionsTree (r :: rs)) Bool)
                         (aS : Action type (specMemTree (r :: rs)) Bool) =>
                       forall (s s' : TreeState DomainElemState (implRegionsTree (r :: rs))) (v : bool),
                         SemAction aI s s' v ->
                         SemAction aS (projImplMemSpecState core (r :: rs) s) (projImplMemSpecState core (r :: rs) s') v /\
                         projImplMemExtraState core (r :: rs) s' = projImplMemExtraState core (r :: rs) s)
                    (map (fun f => f type) (map (fun act ty => liftAction child1Path (act ty)) (implCollectIrqActions rs)))
                    (map (fun f => f type) (map (fun act ty => liftAction child1Path (act ty)) (collectIrqActions rs)))).
          { rewrite !map_map.
            eapply (Forall2_map_both _ _
                      (fun (aI : Action type (implRegionsTree rs) Bool) => liftAction child1Path aI)
                      (fun (aS : Action type (specMemTree rs) Bool) => liftAction child1Path aS)) in IH.
            - rewrite !map_map in IH; exact IH.
            - intros aI aS Hsim0 s s' v Hsem.
              rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
              apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
              rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
              cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState projImplMemExtraState Fst Snd] in *.
              destruct (Hsim0 _ _ _ Hsub1') as [HspecSub1 HextraSub1].
              rewrite HextraSub1; split; [| reflexivity].
              rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
              cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
              rewrite SemAction_iff_evalActionPropGen in HspecSub1.
              eapply evalActionPropGen_mono; [| exact HspecSub1].
              intros st ret [Hst Hret]; subst; split; reflexivity. }
          destruct (memRegionIrqAction r) as [irqAct |]; [| exact Hrest].
          cbn [map]; constructor; [| exact Hrest].
          intros s s' v Hsem.
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
          cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsem.
          rewrite (evalActionPropGen_liftToImplRegion r) in Hsem.
          apply evalActionPropGen_ex_iff in Hsem as [m' [Hm' Hs']]; subst s'.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState projImplMemExtraState Fst Snd] in *.
          rewrite projImplRegionSpecState_writeImplRegionSpecState.
          rewrite projImplRegionExtraState_writeImplRegionSpecState.
          split; [| reflexivity].
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
          eapply evalActionPropGen_mono; [| exact Hm'].
          intros st ret [Hst Hret]; subst; split; reflexivity. }
      apply Hgen.
    - constructor; [| constructor].
      intros s s' v Hsem.
      unfold plicUartIrqAction, plicAction in *.
      destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                  (@plicRegion core _ regions plic) plic.(pfPlic)
                  (Recv "uartIrq" (plicUartIrqPath core _) (fun v0 => Return #v0))
                  s s' v Hsem) as [Hspec [Hextra _]].
      split; assumption.
  Qed.

  Theorem sim_implPlicPendingsSteps :
    forall act (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      In act (@implPlicPendingsSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions plic type) ->
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction act old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros act old1 new1 old2 v Hin Hmem Hsem mid2.
    unfold implPlicPendingsSteps in Hin.
    apply in_map_iff in Hin as [memAct [Hact HinMem]].
    subst act.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    destruct (pendingPathsWithKind core (S (S (length (collectIrqActions regions))))) as [| p0 devPends] eqn:Hpends;
      [contradiction |].
    destruct (inServicePathsWithKind core (S (S (length (collectIrqActions regions))))) as [| i0 devInsvs] eqn:Hinsvs;
      [contradiction |].
    assert (Hhelper :
      forall (actsI : list (Action type (implMemTree regions) Bool))
             (actsS : list (Action type (specMemTree regions) Bool))
             (pends : list (RegOfKind (t := plicTree core (S (S (length (collectIrqActions regions))))) Bool))
             (insvs : list (RegOfKind (t := plicTree core (S (S (length (collectIrqActions regions))))) Bool)),
        Forall2 (fun (aI : Action type (implMemTree regions) Bool)
                     (aS : Action type (specMemTree regions) Bool) =>
                   forall (s s' : TreeState DomainElemState (implMemTree regions)) (v0 : bool),
                     SemAction aI s s' v0 ->
                     SemAction aS (projImplMemSpecState core regions s) (projImplMemSpecState core regions s') v0 /\
                     projImplMemExtraState core regions s' = projImplMemExtraState core regions s)
                actsI actsS ->
        In memAct
          ((fix helper (a : list (Action type (implMemTree regions) Bool))
                       (p i : list (RegOfKind (t := plicTree core (S (S (length (collectIrqActions regions))))) Bool))
             : list (Action type (implMemTree regions) (Bit 0)) :=
              match a, p, i with
              | act0 :: restActs, pendRk :: restPends, insvRk :: restInsvs =>
                  (LetA irqVal : Bool <- act0 ;
                   @implMemNthRegionAction core regions type plic.(plicIdx) (@plicRegion core _ regions plic) plic.(pfPlic) (Bit 0)
                     (@updatePendingLeaf core _ type pendRk insvRk irqVal))
                  :: helper restActs restPends restInsvs
              | _, _, _ => []
              end) actsI pends insvs) ->
        exists specMemAct,
          In specMemAct (@plicPendingStepsHelper core (S (S (length (collectIrqActions regions)))) regions plic type actsS pends insvs) /\
          SemAction specMemAct (projImplMemSpecState core regions (implMem old1)) (projImplMemSpecState core regions (implMem new1)) v /\
          projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1)).
    { intros actsI actsS pends insvs Hrel.
      revert pends insvs.
      induction Hrel as [| aI aS restI restS Ha Hrest IH]; intros [| pendRk restPends] [| insvRk restInsvs] Hin0;
        cbn in Hin0; try contradiction.
      destruct Hin0 as [Heq | Hin0].
      - subst memAct.
        eexists; split; [cbn; left; reflexivity |].
        rewrite SemAction_iff_evalActionPropGen in Hm1'.
        cbn [evalActionPropGen] in Hm1'.
        destruct (evalActionPropGen_to_SemAction aI (implMem old1) _ Hm1')
          as [sMid [irqVal [Hsem1 Hsem2]]].
        rewrite <- SemAction_iff_evalActionPropGen in Hsem2.
        destruct (Ha (implMem old1) sMid irqVal Hsem1) as [Hspec1 Hextra1].
        destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                    (@plicRegion core _ regions plic) plic.(pfPlic)
                    (@updatePendingLeaf core _ type pendRk insvRk irqVal) sMid (implMem new1) v Hsem2)
          as [Hspec2 [Hextra2 _]].
        split.
        + eapply SemLetAction; [exact Hspec1 | exact Hspec2].
        + congruence.
      - destruct (IH restPends restInsvs Hin0) as [specMemAct [HinS Hsim]].
        exists specMemAct; split; [cbn; right; exact HinS | exact Hsim]. }
    destruct (Hhelper _ _ devPends devInsvs Forall2_irqActions_with_uart HinMem)
      as [specMemAct [HinSpecMem [HspecMem Hextra]]].
    assert (HinSpec : In (liftAction np_mem_s specMemAct) (map snd (specMod type))).
    { rewrite map_snd_specMod.
      apply in_or_app; right; apply in_or_app; left.
      unfold specPlicPendingsSteps, plicPendingsSteps.
      rewrite Hpends, Hinsvs.
      apply in_map_iff; exists specMemAct; split; [reflexivity | exact HinSpecMem]. }
    assert (HspecAct : SemAction (liftAction np_mem_s specMemAct) old2 mid2 v).
    { apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem | reflexivity]. }
    repeat split; auto.
    rewrite (Zmod_1_0 v) in HspecAct.
    eapply ConsAction with (a := liftAction np_mem_s specMemAct).
    - exact HinSpec.
    - exact HspecAct.
    - apply NilAction; reflexivity.
  Qed.

  (* --- 4F. `fenceIAcks` -> `specFenceIAckSteps` --- *)

  Lemma implCollectFenceIAckActions_sim :
    forall (rs : list (MemRegion core))
           (act : Action type (implRegionsTree rs) (Bit 0)),
      In act (map (fun f => f type) (implCollectFenceIAckActions rs)) ->
      exists fSpec,
        In fSpec (collectFenceIAckActions rs) /\
        forall (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bits 0),
          SemAction act s s' v ->
          SemAction (fSpec type) (projImplMemSpecState core rs s) (projImplMemSpecState core rs s') v /\
          projImplMemExtraState core rs s' = projImplMemExtraState core rs s.
  Proof.
    induction rs as [| r rs IH]; intros act Hin.
    - cbn in Hin; contradiction.
    - unfold implCollectFenceIAckActions in Hin; cbn [implCollectRegionActions collectFenceIAckActions] in *.
      rewrite map_app in Hin; apply in_app_or in Hin as [HinCurr | HinRest].
      + unfold implMemRegionFenceIAckActions in HinCurr.
        rewrite !map_map in HinCurr.
        apply in_map_iff in HinCurr as [f0 [Hact Hf0]].
        subst act.
        exists (fun ty => liftAction child0Path (f0 ty)); split.
        * apply in_or_app; left.
          apply in_map_iff; exists f0; split; [reflexivity | exact Hf0].
        * intros s s' v Hsem.
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
          cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsem.
          rewrite (evalActionPropGen_liftToImplRegion r) in Hsem.
          apply evalActionPropGen_ex_iff in Hsem as [m' [Hm' Hs']]; subst s'.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState projImplMemExtraState Fst Snd] in *.
          rewrite projImplRegionSpecState_writeImplRegionSpecState.
          rewrite projImplRegionExtraState_writeImplRegionSpecState.
          split; [| reflexivity].
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
          eapply evalActionPropGen_mono; [| exact Hm'].
          intros st ret [Hst Hret]; subst; split; reflexivity.
      + rewrite map_map in HinRest.
        apply in_map_iff in HinRest as [fRest [Hact HfRest]].
        subst act.
        assert (HinRest' : In (fRest type) (map (fun f => f type) (implCollectFenceIAckActions rs))).
        { apply in_map_iff; exists fRest; split; [reflexivity | exact HfRest]. }
        destruct (IH (fRest type) HinRest') as [fSpec0 [HinSpec0 Hsim0]].
        exists (fun ty => liftAction child1Path (fSpec0 ty)); split.
        * apply in_or_app; right.
          apply in_map_iff; exists fSpec0; split; [reflexivity | exact HinSpec0].
        * intros s s' v Hsem.
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
          apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
          rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState projImplMemExtraState Fst Snd] in *.
          destruct (Hsim0 _ _ _ Hsub1') as [HspecSub1 HextraSub1].
          rewrite HextraSub1; split; [| reflexivity].
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
          rewrite SemAction_iff_evalActionPropGen in HspecSub1.
          eapply evalActionPropGen_mono; [| exact HspecSub1].
          intros st ret [Hst Hret]; subst; split; reflexivity.
  Qed.

  Theorem sim_fenceIAcks :
    forall act (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) ->
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction act old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemActions (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros act old1 new1 old2 v Hin Hmem Hsem mid2.
    unfold fenceIAcks, implMemCollectFenceIAckActions in Hin.
    apply in_map_iff in Hin as [memAct [Hact HinMem]].
    subst act.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    destruct (implCollectFenceIAckActions_sim regions memAct HinMem)
      as [fSpec [HinSpecMem Hsim]].
    destruct (Hsim (implMem old1) (implMem new1) v Hm1') as [HspecMem Hextra].
    assert (HinSpec : In (liftAction np_mem_s (fSpec type)) (map snd (specMod type))).
    { rewrite map_snd_specMod.
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
      unfold specFenceIAckSteps.
      apply in_map_iff; exists fSpec; split; [reflexivity | exact HinSpecMem]. }
    assert (HspecAct : SemAction (liftAction np_mem_s (fSpec type)) old2 mid2 v).
    { apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem | reflexivity]. }
    repeat split; auto.
    rewrite (Zmod_1_0 v) in HspecAct.
    eapply ConsAction with (a := liftAction np_mem_s (fSpec type)).
    - exact HinSpec.
    - exact HspecAct.
    - apply NilAction; reflexivity.
  Qed.

  (* --- 4G. `setCanProceedSteps` (`setFetchCanProceedStage`, `setDecodeCanProceedStage`, `setExecuteCanProceedStage`) --- *)

  Theorem SemAction_setFetchCanProceedStage_inv :
    forall (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      SemAction (@setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
      new1 = writeSubTreeState np_fetch_i old1 (implFetch new1) /\
      v = Zmod.zero /\
      implRf new1 = implRf old1 /\
      implWaitBits new1 = implWaitBits old1 /\
      implBp new1 = implBp old1 /\
      implMem new1 = implMem old1 /\
      implDecode new1 = implDecode old1 /\
      implExecute new1 = implExecute old1 /\
      implDataMem new1 = implDataMem old1 /\
      implMulDiv new1 = implMulDiv old1 /\
      Fst (implFetch new1) = Fst (implFetch old1) /\
      Fst (Snd (implFetch new1)) = Fst (Snd (implFetch old1)) /\
      Fst (Snd (Snd (implFetch new1))) = Fst (Snd (Snd (implFetch old1))) /\
      Fst (Snd (Snd (Snd (implFetch new1)))) = Fst (Snd (Snd (Snd (implFetch old1)))) /\
      Fst (Snd (Snd (Snd (Snd (implFetch new1))))) = true /\
      Snd (Snd (Snd (Snd (Snd (implFetch new1))))) = Snd (Snd (Snd (Snd (Snd (implFetch old1))))).
  Proof.
    intros old1 new1 v Hsem.
    unfold setFetchCanProceedStage, setFetchCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    rewrite readSubTreeState_impl_np_fetch in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew1 Hv]; subst new1 v.
    repeat split; reflexivity.
  Qed.

  Theorem SemAction_setDecodeCanProceedStage_inv :
    forall (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      SemAction (@setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
      new1 = writeSubTreeState np_decode_i old1 (implDecode new1) /\
      v = Zmod.zero /\
      implRf new1 = implRf old1 /\
      implWaitBits new1 = implWaitBits old1 /\
      implBp new1 = implBp old1 /\
      implMem new1 = implMem old1 /\
      implFetch new1 = implFetch old1 /\
      implExecute new1 = implExecute old1 /\
      implDataMem new1 = implDataMem old1 /\
      implMulDiv new1 = implMulDiv old1 /\
      Fst (implDecode new1) = true /\
      Snd (implDecode new1) = Snd (implDecode old1).
  Proof.
    intros old1 new1 v Hsem.
    unfold setDecodeCanProceedStage, setDecodeCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    rewrite readSubTreeState_impl_np_decode in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew1 Hv]; subst new1 v.
    repeat split; reflexivity.
  Qed.

  Theorem SemAction_setExecuteCanProceedStage_inv :
    forall (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      SemAction (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
      new1 = writeSubTreeState np_execute_i old1 (implExecute new1) /\
      v = Zmod.zero /\
      implRf new1 = implRf old1 /\
      implWaitBits new1 = implWaitBits old1 /\
      implBp new1 = implBp old1 /\
      implMem new1 = implMem old1 /\
      implFetch new1 = implFetch old1 /\
      implDecode new1 = implDecode old1 /\
      implDataMem new1 = implDataMem old1 /\
      implMulDiv new1 = implMulDiv old1 /\
      Fst (implExecute new1) = Fst (implExecute old1) /\
      Fst (Snd (implExecute new1)) = Fst (Snd (implExecute old1)) /\
      Fst (Snd (Snd (implExecute new1))) = true /\
      Snd (Snd (Snd (implExecute new1))) = Snd (Snd (Snd (implExecute old1))).
  Proof.
    intros old1 new1 v Hsem.
    unfold setExecuteCanProceedStage, setExecuteCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    rewrite readSubTreeState_impl_np_execute in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew1 Hv]; subst new1 v.
    repeat split; reflexivity.
  Qed.

  (* --- 4H. Target Port Rqs and Rps (`targetPortRqs`, `targetPortRps`) --- *)

  Definition RegionEqExceptTargetPort (r : MemRegion core)
    : TreeState DomainElemState (memRegionTree r) ->
      TreeState DomainElemState (memRegionTree r) -> Prop :=
    match r.(regionKind) as rk
      return TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                | ExternalMem => externalMemRegionTree r
                | CustomMem children _ _ _ _ => customMemRegionTree r children
                end) ->
             TreeState DomainElemState
               (match rk with
                | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                | ExternalMem => externalMemRegionTree r
                | CustomMem children _ _ _ _ => customMemRegionTree r children
                end) -> Prop
    with
    | InternalMem true _ _ => fun m1 m2 =>
        Fst m1 = Fst m2 /\ Fst (Snd m1) = Fst (Snd m2)
    | InternalMem false _ _ => fun m1 m2 => m1 = m2
    | ExternalMem => fun m1 m2 => m1 = m2
    | CustomMem _ _ _ _ _ => fun m1 m2 => m1 = m2
    end.

  Lemma RegionEqExceptTargetPort_refl :
    forall (r : MemRegion core) (m : TreeState DomainElemState (memRegionTree r)),
      RegionEqExceptTargetPort r m m.
  Proof.
    intros r m; unfold RegionEqExceptTargetPort, memRegionTree in *.
    revert m; destruct (r.(regionKind)) as [[|] ? ? | | ? ? ? ? ?]; intros m;
      [split; reflexivity | reflexivity | reflexivity | reflexivity].
  Qed.

  Fixpoint MemEqExceptTargetPort (rs : list (MemRegion core))
    : TreeState DomainElemState (specMemTree rs) ->
      TreeState DomainElemState (specMemTree rs) -> Prop :=
    match rs return TreeState DomainElemState (specMemTree rs) ->
                    TreeState DomainElemState (specMemTree rs) -> Prop with
    | [] => fun _ _ => True
    | r :: rest => fun m1 m2 =>
        RegionEqExceptTargetPort r (Fst m1) (Fst m2) /\
        MemEqExceptTargetPort rest (Fst (Snd m1)) (Fst (Snd m2))
    end.

  Lemma MemEqExceptTargetPort_refl :
    forall (rs : list (MemRegion core)) (m : TreeState DomainElemState (specMemTree rs)),
      MemEqExceptTargetPort rs m m.
  Proof.
    induction rs as [| r rest IH]; intros m; cbn [MemEqExceptTargetPort].
    - exact I.
    - split; [apply RegionEqExceptTargetPort_refl | apply IH].
  Qed.

  Local Ltac step_target_port Hsem s' :=
    repeat (
      cbn [evalActionPropGen] in Hsem;
      lazymatch type of Hsem with
      | _ /\ _ =>
          let Hs' := fresh "Hs'" in
          destruct Hsem as [Hs' _]; subst s'; split; reflexivity
      | ex _ =>
          let x := fresh "x" in
          destruct Hsem as [x Hsem];
          try (is_var x; destruct x; cbn [evalActionPropGen evalExpr] in Hsem)
      | (if ?c then _ else _) =>
          destruct c; cbn [evalActionPropGen evalExpr] in Hsem
      | context [evalActionPropGen (liftAction _ _) _ _] =>
          rewrite evalActionPropGen_liftAction in Hsem
      end).

  Lemma SemAction_implInternalMemRegionTargetPortWrite_preserves_banks :
    forall (r : MemRegion core)
           (s s' : TreeState DomainElemState (implInternalMemRegionTree r true))
           (v : bits 0),
      SemAction (@implInternalMemRegionTargetPortWrite core r type) s s' v ->
      Fst (Fst s') = Fst (Fst s) /\ Fst (Snd (Fst s')) = Fst (Snd (Fst s)).
  Proof.
    intros r s s' v Hsem.
    unfold implInternalMemRegionTargetPortWrite, implInternalMemRegionPortWriteRq in Hsem.
    destruct (r.(isReadOnly));
      rewrite SemAction_iff_evalActionPropGen in Hsem;
      step_target_port Hsem s'.
  Qed.

  Lemma SemAction_implInternalMemRegionTargetPortReadRq_preserves_banks :
    forall (r : MemRegion core)
           (s s' : TreeState DomainElemState (implInternalMemRegionTree r true))
           (v : bits 0),
      SemAction (@implInternalMemRegionTargetPortReadRq core r type) s s' v ->
      Fst (Fst s') = Fst (Fst s) /\ Fst (Snd (Fst s')) = Fst (Snd (Fst s)).
  Proof.
    intros r s s' v Hsem.
    unfold implInternalMemRegionTargetPortReadRq, implInternalMemRegionDataLineReadRq,
           implInternalMemRegionPortReadRq in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    step_target_port Hsem s'.
  Qed.

  Lemma SemAction_implInternalMemRegionTargetPortReadRp_preserves_banks :
    forall (r : MemRegion core)
           (s s' : TreeState DomainElemState (implInternalMemRegionTree r true))
           (v : bits 0),
      SemAction (@implInternalMemRegionTargetPortReadRp core r type) s s' v ->
      Fst (Fst s') = Fst (Fst s) /\ Fst (Snd (Fst s')) = Fst (Snd (Fst s)).
  Proof.
    intros r s s' v Hsem.
    unfold implInternalMemRegionTargetPortReadRp, implInternalMemRegionDataLineReadRp,
           implInternalMemRegionPortReadRp, implInternalMemRegionDataDeqRp,
           implInternalMemRegionPortDeqRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    step_target_port Hsem s'.
  Qed.

  Lemma implCollectRegionActions_preserves_spec :
    forall (getActions : forall r : MemRegion core, list (forall ty, Action ty (implMemRegionTree r) (Bit 0)))
           (Hpres : forall (r : MemRegion core) (f : forall ty, Action ty (implMemRegionTree r) (Bit 0))
                           (s s' : TreeState DomainElemState (implMemRegionTree r)) (v : bits 0),
                      In f (getActions r) ->
                      SemAction (f type) s s' v ->
                      projImplRegionSpecState core r s' = projImplRegionSpecState core r s)
           (rs : list (MemRegion core))
           (act : Action type (implRegionsTree rs) (Bit 0))
           (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bits 0),
      In act (map (fun f => f type) (implCollectRegionActions getActions rs)) ->
      SemAction act s s' v ->
      projImplMemSpecState core rs s' = projImplMemSpecState core rs s.
  Proof.
    intros getActions Hpres.
    induction rs as [| r rs IH]; intros act s s' v Hin Hsem.
    - cbn in Hin; contradiction.
    - cbn [implCollectRegionActions] in Hin.
      rewrite map_app in Hin; apply in_app_or in Hin as [HinCurr | HinRest].
      + rewrite map_map in HinCurr; apply in_map_iff in HinCurr as [f0 [Hact Hf0]]; subst act.
        rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
        apply evalActionPropGen_ex_iff in Hsem as [sub0' [Hsub0' Hs']]; subst s'.
        rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
        cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState Fst Snd] in *.
        rewrite (Hpres r f0 (Fst s) sub0' _ Hf0 Hsub0').
        reflexivity.
      + rewrite map_map in HinRest; apply in_map_iff in HinRest as [fRest [Hact HfRest]]; subst act.
        rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
        apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
        rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
        cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState Fst Snd] in *.
        f_equal; f_equal.
        eapply IH; [| exact Hsub1'].
        apply in_map_iff; exists fRest; split; [reflexivity | exact HfRest].
  Qed.

  Lemma implCollectRegionActions_MemEqExceptTargetPort :
    forall (getActions : forall r : MemRegion core, list (forall ty, Action ty (implMemRegionTree r) (Bit 0)))
           (Hpres : forall (r : MemRegion core) (f : forall ty, Action ty (implMemRegionTree r) (Bit 0))
                           (s s' : TreeState DomainElemState (implMemRegionTree r)) (v : bits 0),
                      In f (getActions r) ->
                      SemAction (f type) s s' v ->
                      RegionEqExceptTargetPort r (projImplRegionSpecState core r s') (projImplRegionSpecState core r s))
           (rs : list (MemRegion core))
           (act : Action type (implRegionsTree rs) (Bit 0))
           (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bits 0),
      In act (map (fun f => f type) (implCollectRegionActions getActions rs)) ->
      SemAction act s s' v ->
      MemEqExceptTargetPort rs (projImplMemSpecState core rs s') (projImplMemSpecState core rs s).
  Proof.
    intros getActions Hpres.
    induction rs as [| r rs IH]; intros act s s' v Hin Hsem.
    - exact I.
    - cbn [implCollectRegionActions] in Hin.
      rewrite map_app in Hin; apply in_app_or in Hin as [HinCurr | HinRest].
      + rewrite map_map in HinCurr; apply in_map_iff in HinCurr as [f0 [Hact Hf0]]; subst act.
        rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
        apply evalActionPropGen_ex_iff in Hsem as [sub0' [Hsub0' Hs']]; subst s'.
        rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
        cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState MemEqExceptTargetPort Fst Snd] in *.
        split; [exact (Hpres r f0 (Fst s) sub0' _ Hf0 Hsub0') | apply MemEqExceptTargetPort_refl].
      + rewrite map_map in HinRest; apply in_map_iff in HinRest as [fRest [Hact HfRest]]; subst act.
        rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
        apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
        rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
        cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplMemSpecState MemEqExceptTargetPort Fst Snd] in *.
        split; [apply RegionEqExceptTargetPort_refl |].
        eapply IH; [| exact Hsub1'].
        apply in_map_iff; exists fRest; split; [reflexivity | exact HfRest].
  Qed.

  Theorem sim_targetPortRqs_preserves_spec :
    forall act (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      In act (@targetPortRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) ->
      SemAction act old1 new1 v ->
      MemEqExceptTargetPort regions (projImplMemSpecState core regions (implMem new1)) (projImplMemSpecState core regions (implMem old1)) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros act old1 new1 v Hin Hsem.
    unfold targetPortRqs, implMemCollectTargetPortRqActions, implCollectTargetPortRqActions in Hin.
    apply in_map_iff in Hin as [memAct [Hact HinMem]]; subst act.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    split; [| exact Hnew1].
    eapply implCollectRegionActions_MemEqExceptTargetPort; [| exact HinMem | exact Hm1'].
    intros r f s s' v0 Hf Hsem0.
    unfold implMemRegionTargetPortRqActions, RegionEqExceptTargetPort, projImplRegionSpecState, implMemRegionTree, memRegionTree in *.
    revert f s s' Hf Hsem0.
    destruct (r.(regionKind)) as [[|] ? ? | | ? ? ? ? ?]; intros f s s' Hf Hsem0; try contradiction.
    cbn [In] in Hf; destruct Hf as [Hf | [Hf | []]]; subst f.
    - eapply SemAction_implInternalMemRegionTargetPortWrite_preserves_banks; exact Hsem0.
    - eapply SemAction_implInternalMemRegionTargetPortReadRq_preserves_banks; exact Hsem0.
  Qed.

  Theorem sim_targetPortRps_preserves_spec :
    forall act (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      In act (@targetPortRps core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) ->
      SemAction act old1 new1 v ->
      MemEqExceptTargetPort regions (projImplMemSpecState core regions (implMem new1)) (projImplMemSpecState core regions (implMem old1)) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros act old1 new1 v Hin Hsem.
    unfold targetPortRps, implMemCollectTargetPortRpActions, implCollectTargetPortRpActions in Hin.
    apply in_map_iff in Hin as [memAct [Hact HinMem]]; subst act.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    split; [| exact Hnew1].
    eapply implCollectRegionActions_MemEqExceptTargetPort; [| exact HinMem | exact Hm1'].
    intros r f s s' v0 Hf Hsem0.
    unfold implMemRegionTargetPortRpActions, RegionEqExceptTargetPort, projImplRegionSpecState, implMemRegionTree, memRegionTree in *.
    revert f s s' Hf Hsem0.
    destruct (r.(regionKind)) as [[|] ? ? | | ? ? ? ? ?]; intros f s s' Hf Hsem0; try contradiction.
    cbn [In] in Hf; destruct Hf as [Hf | []]; subst f.
    eapply SemAction_implInternalMemRegionTargetPortReadRp_preserves_banks; exact Hsem0.
  Qed.
End SystemDevicesSim.
