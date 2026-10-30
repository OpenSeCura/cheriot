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
  Variable regions : list MemRegion.

  Local Abbreviation sTree := (@specSysTree core pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation specMemTree := (specMemTree core).
  Local Abbreviation specMemChildren := (specMemChildren core).
  Local Abbreviation implMemTree := (implMemTree core).
  Local Abbreviation implRegionsTree := (implRegionsTree core).
  Local Abbreviation implRegionsChildren := (implRegionsChildren core).
  Local Abbreviation collectIrqActions := (collectIrqActions core).
  Local Abbreviation memRegionTree := (memRegionTree core).

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

  Local Abbreviation specMemTree := (specMemTree dom).
  Local Abbreviation specMemChildren := (specMemChildren dom).
  Local Abbreviation implMemTree := (implMemTree dom).
  Local Abbreviation implRegionsTree := (implRegionsTree dom).
  Local Abbreviation implRegionsChildren := (implRegionsChildren dom).
  Local Abbreviation memRegionTree := (memRegionTree dom).
  Local Abbreviation implMemRegionTree := (implMemRegionTree dom).
  Local Abbreviation implMemRegionExtraChildren := (implMemRegionExtraChildren dom).

  Definition implRegionExtraChildren (r : MemRegion) : list (Tree DomainElem) :=
    implMemRegionExtraChildren r r.(regionKind).

  Definition projImplRegionSpecState (r : MemRegion)
    (s : TreeState DomainElemState (implMemRegionTree r))
    : TreeState DomainElemState (memRegionTree r) :=
    Fst s.

  Definition projImplRegionExtraState (r : MemRegion)
    (s : TreeState DomainElemState (implMemRegionTree r))
    : TreeState DomainElemState (Node "" (implRegionExtraChildren r)) :=
    Snd s.

  Definition writeImplRegionSpecState (r : MemRegion)
    (s : TreeState DomainElemState (implMemRegionTree r))
    (m : TreeState DomainElemState (memRegionTree r))
    : TreeState DomainElemState (implMemRegionTree r) :=
    (m ,, Snd s).

  Lemma projImplRegionSpecState_writeImplRegionSpecState :
    forall (r : MemRegion)
           (s : TreeState DomainElemState (implMemRegionTree r))
           (m : TreeState DomainElemState (memRegionTree r)),
      projImplRegionSpecState r (writeImplRegionSpecState r s m) = m.
  Proof.
    intros r s m; reflexivity.
  Qed.

  Lemma projImplRegionExtraState_writeImplRegionSpecState :
    forall (r : MemRegion)
           (s : TreeState DomainElemState (implMemRegionTree r))
           (m : TreeState DomainElemState (memRegionTree r)),
      projImplRegionExtraState r (writeImplRegionSpecState r s m) =
      projImplRegionExtraState r s.
  Proof.
    intros r s m; reflexivity.
  Qed.

  Definition subEnvImplRegion (r : MemRegion)
    (env : Env (implMemRegionTree r))
    (s : TreeState DomainElemState (implMemRegionTree r))
    : Env (memRegionTree r) :=
    subEnv child0Path env s.

  Lemma evalActionPropGen_liftToImplRegion :
    forall (r : MemRegion) {k : Kind}
           {env : Env (implMemRegionTree r)}
           (act : Action type (memRegionTree r) k)
           (s : TreeState DomainElemState (implMemRegionTree r))
           (P : TreeState DomainElemState (implMemRegionTree r) -> type k -> Prop),
      evalActionPropGen env (liftToImplRegion act) s P <->
      evalActionPropGen (subEnvImplRegion r env s) act (projImplRegionSpecState r s)
        (fun m' v => P (writeImplRegionSpecState r s m') v).
  Proof.
    intros r k env act s P.
    exact (evalActionPropGen_liftAction child0Path act s P).
  Qed.

  Lemma SemAction_liftToImplRegion :
    forall (r : MemRegion) {k : Kind}
           {env : Env (implMemRegionTree r)}
           (act : Action type (memRegionTree r) k)
           (s s' : TreeState DomainElemState (implMemRegionTree r)) (v : type k),
      SemAction env (liftToImplRegion act) s s' v <->
      exists m',
        SemAction (subEnvImplRegion r env s) act (projImplRegionSpecState r s) m' v /\
        s' = writeImplRegionSpecState r s m'.
  Proof.
    intros r k env act s s' v.
    rewrite !SemAction_iff_evalActionPropGen.
    rewrite evalActionPropGen_liftToImplRegion.
    rewrite evalActionPropGen_ex_iff.
    split; intros [m' [Hm' Heq]]; exists m'; rewrite !SemAction_iff_evalActionPropGen in *; auto.
  Qed.

  Fixpoint implRegionsExtraTree (regions : list MemRegion) : Tree DomainElem :=
    match regions with
    | [] => Node "" []
    | r :: rs => Node "" [ Node "" (implRegionExtraChildren r) ; implRegionsExtraTree rs ]
    end.

  Fixpoint projImplRegionsSpecState (regions : list MemRegion)
    : TreeState DomainElemState (implRegionsTree regions) ->
      TreeState DomainElemState (specMemTree regions) :=
    match regions return TreeState DomainElemState (implRegionsTree regions) ->
                         TreeState DomainElemState (specMemTree regions) with
    | [] => fun _ => tt
    | r :: rs => fun s =>
        (projImplRegionSpecState r (Fst s) ,,
         (projImplRegionsSpecState rs (Fst (Snd s)) ,, tt))
    end.

  Fixpoint projImplRegionsExtraState (regions : list MemRegion)
    : TreeState DomainElemState (implRegionsTree regions) ->
      TreeState DomainElemState (implRegionsExtraTree regions) :=
    match regions return TreeState DomainElemState (implRegionsTree regions) ->
                         TreeState DomainElemState (implRegionsExtraTree regions) with
    | [] => fun _ => tt
    | r :: rs => fun s =>
        (projImplRegionExtraState r (Fst s) ,,
         (projImplRegionsExtraState rs (Fst (Snd s)) ,, tt))
    end.

  Fixpoint writeImplRegionsSpecState (regions : list MemRegion)
    : TreeState DomainElemState (implRegionsTree regions) ->
      TreeState DomainElemState (specMemTree regions) ->
      TreeState DomainElemState (implRegionsTree regions) :=
    match regions return TreeState DomainElemState (implRegionsTree regions) ->
                         TreeState DomainElemState (specMemTree regions) ->
                         TreeState DomainElemState (implRegionsTree regions) with
    | [] => fun s _ => s
    | r :: rs => fun s m =>
        (writeImplRegionSpecState r (Fst s) (Fst m) ,,
         (writeImplRegionsSpecState rs (Fst (Snd s)) (Fst (Snd m)) ,, Snd (Snd s)))
    end.

  Fixpoint ImplSpecRegionsEnvRel (regions : list MemRegion)
    : Env (implRegionsTree regions) ->
      Env (specMemTree regions) -> Prop :=
    match regions return Env (implRegionsTree regions) ->
                         Env (specMemTree regions) -> Prop with
    | [] => fun _ _ => True
    | r :: rs => fun envI envS =>
        (forall (s : TreeState DomainElemState (implRegionsTree (r :: rs))) m_r x v,
           subEnvImplRegion r (subEnv child0Path envI s) (Fst s) m_r x v ->
           subEnv child0Path envS (projImplRegionsSpecState (r :: rs) s) m_r x v) /\
        (forall (s : TreeState DomainElemState (implRegionsTree (r :: rs))),
           ImplSpecRegionsEnvRel rs
             (subEnv child1Path envI s)
             (subEnv child1Path envS (projImplRegionsSpecState (r :: rs) s)))
    end.

  Lemma projImplRegionsSpecState_writeImplRegionsSpecState :
    forall (regions : list MemRegion)
           (s : TreeState DomainElemState (implRegionsTree regions))
           (m : TreeState DomainElemState (specMemTree regions)),
      projImplRegionsSpecState regions (writeImplRegionsSpecState regions s m) = m.
  Proof.
    induction regions as [| r rs IH]; intros s m; cbn [projImplRegionsSpecState writeImplRegionsSpecState].
    - destruct m; reflexivity.
    - destruct m as [mr [mrs u]]; destruct u.
      cbn [Fst Snd].
      rewrite projImplRegionSpecState_writeImplRegionSpecState, IH.
      reflexivity.
  Qed.

  Lemma projImplRegionsExtraState_writeImplRegionsSpecState :
    forall (regions : list MemRegion)
           (s : TreeState DomainElemState (implRegionsTree regions))
           (m : TreeState DomainElemState (specMemTree regions)),
      projImplRegionsExtraState regions (writeImplRegionsSpecState regions s m) =
      projImplRegionsExtraState regions s.
  Proof.
    induction regions as [| r rs IH]; intros s m; cbn [projImplRegionsExtraState writeImplRegionsSpecState].
    - reflexivity.
    - cbn [Fst Snd].
      rewrite projImplRegionExtraState_writeImplRegionSpecState, IH.
      reflexivity.
  Qed.

  Lemma writeImplRegionSpecState_projImplRegionSpecState :
    forall (r : MemRegion)
           (s : TreeState DomainElemState (implMemRegionTree r)),
      writeImplRegionSpecState r s (projImplRegionSpecState r s) = s.
  Proof.
    intros r [s0 s1]; reflexivity.
  Qed.

  Lemma writeImplRegionsSpecState_projImplRegionsSpecState :
    forall (regions : list MemRegion)
           (s : TreeState DomainElemState (implRegionsTree regions)),
      writeImplRegionsSpecState regions s (projImplRegionsSpecState regions s) = s.
  Proof.
    induction regions as [| r rs IH]; intros s; cbn [projImplRegionsSpecState writeImplRegionsSpecState].
    - reflexivity.
    - destruct s as [sr [srs u]].
      cbn [Fst Snd].
      rewrite writeImplRegionSpecState_projImplRegionSpecState, IH.
      reflexivity.
  Qed.

  Theorem evalActionPropGen_implRegionsNthRegionAction :
    forall (idx : nat) (regions : list MemRegion) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           {envI : Env (implRegionsTree regions)}
           {envS : Env (specMemTree regions)}
           (Henv : ImplSpecRegionsEnvRel regions envI envS)
           (act : Action type (memRegionTree r0) k)
           (s : TreeState DomainElemState (implRegionsTree regions))
           (P : TreeState DomainElemState (implRegionsTree regions) -> type k -> Prop),
      evalActionPropGen envI (@implRegionsNthRegionAction dom type idx regions r0 pf k act) s P ->
      evalActionPropGen envS (@nthRegionAction dom type idx regions r0 pf k act)
        (projImplRegionsSpecState regions s)
        (fun m' v => P (writeImplRegionsSpecState regions s m') v).
  Proof.
    induction idx as [| idx' IH]; intros [| r rs] r0 pf k envI envS Henv act s P Heval;
      try discriminate pf.
    - unfold implRegionsNthRegionAction, nthRegionAction in Heval |- *.
      cbn [genNthRegionAction projImplRegionsSpecState] in Heval |- *.
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end with eq_refl => eq_refl end) in Heval |- *.
      clearbody Heq; clear pf; destruct Heq; cbn in Heval |- *.
      rewrite evalActionPropGen_liftAction in Heval; rewrite evalActionPropGen_liftAction.
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd writeSubTreeState writeSubTreeState_child writeImplRegionsSpecState] in Heval |- *.
      rewrite (evalActionPropGen_liftToImplRegion r0) in Heval.
      eapply evalActionPropGen_env_mono; [exact (proj1 Henv s) |].
      eapply evalActionPropGen_mono; [| exact Heval].
      intros m' v HP.
      rewrite writeImplRegionsSpecState_projImplRegionsSpecState; exact HP.
    - unfold implRegionsNthRegionAction, nthRegionAction in Heval |- *.
      cbn [genNthRegionAction projImplRegionsSpecState] in Heval |- *.
      rewrite evalActionPropGen_liftAction in Heval; rewrite evalActionPropGen_liftAction.
      cbn [child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child Fst Snd writeSubTreeState writeSubTreeState_child writeImplRegionsSpecState] in Heval |- *.
      pose proof (IH rs r0 pf k _ _ (proj2 Henv s) act (Fst (Snd s)) _ Heval) as HevalS.
      eapply evalActionPropGen_mono; [| exact HevalS].
      intros m' v HP.
      rewrite writeImplRegionSpecState_projImplRegionSpecState.
      destruct (Snd (Snd s)); exact HP.
  Qed.

  Theorem SemAction_implRegionsNthRegionAction :
    forall (idx : nat) (regions : list MemRegion) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           {envI : Env (implRegionsTree regions)}
           {envS : Env (specMemTree regions)}
           (Henv : ImplSpecRegionsEnvRel regions envI envS)
           (act : Action type (memRegionTree r0) k)
           (s s' : TreeState DomainElemState (implRegionsTree regions))
           (v : type k),
      SemAction envI (@implRegionsNthRegionAction dom type idx regions r0 pf k act) s s' v ->
      SemAction envS (@nthRegionAction dom type idx regions r0 pf k act)
        (projImplRegionsSpecState regions s)
        (projImplRegionsSpecState regions s') v /\
      projImplRegionsExtraState regions s' = projImplRegionsExtraState regions s /\
      s' = writeImplRegionsSpecState regions s (projImplRegionsSpecState regions s').
  Proof.
    intros idx regions r0 pf k envI envS Henv act s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (evalActionPropGen_implRegionsNthRegionAction idx regions r0 pf Henv act s) in Hsem.
    apply evalActionPropGen_ex_iff in Hsem.
    destruct Hsem as [m' [Hm' Hs']]; subst s'.
    rewrite <- SemAction_iff_evalActionPropGen in Hm'.
    rewrite projImplRegionsSpecState_writeImplRegionsSpecState.
    rewrite projImplRegionsExtraState_writeImplRegionsSpecState.
    repeat split; auto.
  Qed.

  Definition implMemExtraTree (regions : list MemRegion) : Tree DomainElem :=
    Node ""
      [ implRegionsExtraTree regions ;
        Leaf "state"     (dom, EReg (Build_Reg MemState (Some (getDefault _)) false)) ;
        Leaf "requester" (dom, EReg (Build_Reg Requester (Some (getDefault _)) false)) ;
        Leaf "readRp"    (dom, EReg (Build_Reg (Option LineReadRp) (Some (getDefault _)) false)) ].

  Definition projImplMemSpecState (regions : list MemRegion)
    (s : TreeState DomainElemState (implMemTree regions))
    : TreeState DomainElemState (specMemTree regions) :=
    projImplRegionsSpecState regions (Fst s).

  Definition projImplMemExtraState (regions : list MemRegion)
    (s : TreeState DomainElemState (implMemTree regions))
    : TreeState DomainElemState (implMemExtraTree regions) :=
    (projImplRegionsExtraState regions (Fst s) ,, Snd s).

  Definition writeImplMemSpecState (regions : list MemRegion)
    (s : TreeState DomainElemState (implMemTree regions))
    (m : TreeState DomainElemState (specMemTree regions))
    : TreeState DomainElemState (implMemTree regions) :=
    (writeImplRegionsSpecState regions (Fst s) m ,, Snd s).

  Definition ImplSpecMemEnvRel (regions : list MemRegion)
    (envI : Env (implMemTree regions))
    (envS : Env (specMemTree regions)) : Prop :=
    forall (s : TreeState DomainElemState (implMemTree regions)),
      ImplSpecRegionsEnvRel regions (subEnv child0Path envI s) envS.

  Lemma SemAction_lift_child0_implMem :
    forall (regions : list MemRegion) {k : Kind}
           {envI : Env (implMemTree regions)}
           {envS : Env (specMemTree regions)}
           (Henv : ImplSpecMemEnvRel regions envI envS)
           (aI : Action type (implRegionsTree regions) k)
           (aS : Action type (specMemTree regions) k)
           (Hsim : forall (envR : Env (implRegionsTree regions))
                          (envS0 : Env (specMemTree regions)),
                     ImplSpecRegionsEnvRel regions envR envS0 ->
                     forall (sr sr' : TreeState DomainElemState (implRegionsTree regions)) (v : type k),
                       SemAction envR aI sr sr' v ->
                       SemAction envS0 aS (projImplRegionsSpecState regions sr) (projImplRegionsSpecState regions sr') v /\
                       projImplRegionsExtraState regions sr' = projImplRegionsExtraState regions sr /\
                       sr' = writeImplRegionsSpecState regions sr (projImplRegionsSpecState regions sr'))
           (s s' : TreeState DomainElemState (implMemTree regions)) (v : type k),
      SemAction envI (liftAction child0Path aI) s s' v ->
      SemAction envS aS (projImplMemSpecState regions s) (projImplMemSpecState regions s') v /\
      projImplMemExtraState regions s' = projImplMemExtraState regions s /\
      s' = writeImplMemSpecState regions s (projImplMemSpecState regions s').
  Proof.
    intros regions k envI envS Henv aI aS Hsim s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff in Hsem.
    destruct Hsem as [sub0' [Hsub0' Hs']]; subst s'.
    rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
    unfold projImplMemSpecState, projImplMemExtraState, writeImplMemSpecState.
    cbn [child0Path implMemTree readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in *.
    destruct (Hsim _ _ (Henv s) (Fst s) sub0' v Hsub0') as [Hspec [Hextra Hwrite]].
    rewrite Hextra, <- Hwrite.
    repeat split; auto.
  Qed.

  Corollary SemAction_implMemNthRegionAction :
    forall (regions : list MemRegion) (idx : nat) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           {envI : Env (implMemTree regions)}
           {envS : Env (specMemTree regions)}
           (Henv : ImplSpecMemEnvRel regions envI envS)
           (act : Action type (memRegionTree r0) k)
           (s s' : TreeState DomainElemState (implMemTree regions))
           (v : type k),
      SemAction envI (@implNthRegionAction dom type idx regions r0 pf k act) s s' v ->
      SemAction envS (@nthRegionAction dom type idx regions r0 pf k act)
        (projImplMemSpecState regions s)
        (projImplMemSpecState regions s') v /\
      projImplMemExtraState regions s' = projImplMemExtraState regions s /\
      s' = writeImplMemSpecState regions s (projImplMemSpecState regions s').
  Proof.
    intros regions idx r0 pf k envI envS Henv act s s' v Hsem.
    unfold implNthRegionAction in Hsem.
    eapply SemAction_lift_child0_implMem; [exact Henv | | exact Hsem].
    intros envR envS0 HenvR sr sr' v0 HsemR.
    exact (SemAction_implRegionsNthRegionAction idx regions r0 pf HenvR act sr sr' v0 HsemR).
  Qed.
End MemProjection.

Arguments projImplRegionSpecState_writeImplRegionSpecState {dom} r s m.
Arguments projImplRegionExtraState_writeImplRegionSpecState {dom} r s m.
Arguments evalActionPropGen_liftToImplRegion {dom} r {k env} act s P.

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
    forall {env : Env (rfTree dom pcAddrInit)}
           (rf : TreeState DomainElemState (rfTree dom pcAddrInit)) P,
      evalActionPropGen env (@incrementMcycle dom pcAddrInit type) rf P <->
      P (evalIncrementMcycle rf) Zmod.zero.
  Proof.
    intros env rf P.
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
    forall {env : Env (rfTree dom pcAddrInit)}
           (rf rf' : TreeState DomainElemState (rfTree dom pcAddrInit)) v,
      SemAction env (@incrementMcycle dom pcAddrInit type) rf rf' v <->
      rf' = evalIncrementMcycle rf /\ v = Zmod.zero.
  Proof.
    intros env rf rf' v.
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
  Variable regions : list MemRegion.
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions core regions)))) regions.

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
  Local Abbreviation specMemTree := (specMemTree core).
  Local Abbreviation specMemChildren := (specMemChildren core).
  Local Abbreviation implMemTree := (implMemTree core).
  Local Abbreviation implRegionsTree := (implRegionsTree core).
  Local Abbreviation implRegionsChildren := (implRegionsChildren core).
  Local Abbreviation implMemRegionTree := (implMemRegionTree core).
  Local Abbreviation collectIrqActions := (collectIrqActions core).
  Local Abbreviation implCollectIrqActions := (implCollectIrqActions core).
  Local Abbreviation implMemCollectIrqActions := (implMemCollectIrqActions core).
  Local Abbreviation memRegionTree := (memRegionTree core).
  Local Abbreviation memRegionIrqAction := (memRegionIrqAction core).
  Local Abbreviation memRegionIrqActions := (memRegionIrqActions core).
  Local Abbreviation collectFenceIAckActions := (collectFenceIAckActions core).
  Local Abbreviation implCollectFenceIAckActions := (implCollectFenceIAckActions core).
  Local Abbreviation implMemCollectFenceIAckActions := (implMemCollectFenceIAckActions core).
  Local Abbreviation memRegionFenceIAckActions := (memRegionFenceIAckActions core).
  Local Abbreviation implMemRegionIrqActions := (implMemRegionIrqActions core).
  Local Abbreviation implMemRegionFenceIAckActions := (implMemRegionFenceIAckActions core).

  Definition ImplSpecSysEnvRel
    (envImpl : Env iTree) (envSpec : Env sTree) : Prop :=
    forall (s1 : TreeState DomainElemState iTree)
           (s2 : TreeState DomainElemState sTree),
      specMem s2 = projImplMemSpecState core regions (implMem s1) ->
      ImplSpecMemEnvRel core regions
        (subEnv np_mem_i envImpl s1)
        (subEnv np_mem_s envSpec s2).

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
          @specStep core pcAddrInit config regions clint plic type ;
          @specSecondLine core pcAddrInit config regions type ]
     ++ @specFenceIAckSteps core pcAddrInit regions type)%list.
  Proof.
    unfold specMod, spec.
    rewrite map_map; cbn [snd].
    apply map_id.
  Qed.

  Lemma SemAction_lift_np_mem_impl :
    forall {k : Kind} {env : Env iTree} (act : Action type (implMemTree regions) k)
           (old1 new1 : TreeState DomainElemState iTree) (v : type k),
      SemAction env (liftAction np_mem_i act) old1 new1 v <->
      exists m1',
        SemAction (subEnv np_mem_i env old1) act (implMem old1) m1' v /\
        new1 = writeSubTreeState np_mem_i old1 m1'.
  Proof.
    intros k env act old1 new1 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_impl_np_mem.
    split; intros [m1' [Hm1' Hnew1]]; exists m1';
      [rewrite <- SemAction_iff_evalActionPropGen in Hm1'
      | rewrite SemAction_iff_evalActionPropGen in Hm1']; auto.
  Qed.

  Lemma SemAction_lift_np_mem_spec :
    forall {k : Kind} {env : Env sTree} (act : Action type (specMemTree regions) k)
           (old2 new2 : TreeState DomainElemState sTree) (v : type k),
      SemAction env (liftAction np_mem_s act) old2 new2 v <->
      exists m2',
        SemAction (subEnv np_mem_s env old2) act (specMem old2) m2' v /\
        new2 = writeSubTreeState np_mem_s old2 m2'.
  Proof.
    intros k env act old2 new2 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_spec_np_mem.
    split; intros [m2' [Hm2' Hnew2]]; exists m2';
      [rewrite <- SemAction_iff_evalActionPropGen in Hm2'
      | rewrite SemAction_iff_evalActionPropGen in Hm2']; auto.
  Qed.

  Lemma SemAction_lift_np_rf_impl :
    forall {k : Kind} {env : Env iTree} (act : Action type (rfTree core pcAddrInit) k)
           (old1 new1 : TreeState DomainElemState iTree) (v : type k),
      SemAction env (liftAction np_rf_i act) old1 new1 v <->
      exists rf1',
        SemAction (subEnv np_rf_i env old1) act (implRf old1) rf1' v /\
        new1 = writeSubTreeState np_rf_i old1 rf1'.
  Proof.
    intros k env act old1 new1 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_impl_np_rf.
    split; intros [rf1' [Hrf1' Hnew1]]; exists rf1';
      [rewrite <- SemAction_iff_evalActionPropGen in Hrf1'
      | rewrite SemAction_iff_evalActionPropGen in Hrf1']; auto.
  Qed.

  Lemma SemAction_lift_np_rf_spec :
    forall {k : Kind} {env : Env sTree} (act : Action type (rfTree core pcAddrInit) k)
           (old2 new2 : TreeState DomainElemState sTree) (v : type k),
      SemAction env (liftAction np_rf_s act) old2 new2 v <->
      exists rf2',
        SemAction (subEnv np_rf_s env old2) act (specRf old2) rf2' v /\
        new2 = writeSubTreeState np_rf_s old2 rf2'.
  Proof.
    intros k env act old2 new2 v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff.
    rewrite readSubTreeState_spec_np_rf.
    split; intros [rf2' [Hrf2' Hnew2]]; exists rf2';
      [rewrite <- SemAction_iff_evalActionPropGen in Hrf2'
      | rewrite SemAction_iff_evalActionPropGen in Hrf2']; auto.
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
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      SemAction envImpl (@implTickCycle core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
      let mid2 := writeSubTreeState np_rf_s old2 (evalIncrementMcycle core pcAddrInit (specRf old2)) in
      new1 = writeSubTreeState np_rf_i old1 (evalIncrementMcycle core pcAddrInit (implRf old1)) /\
      v = Zmod.zero /\
      SemAction envSpec (@specTickCycle core pcAddrInit regions type) old2 mid2 Zmod.zero /\
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = evalIncrementMcycle core pcAddrInit (specRf old2) /\
      specMem mid2 = specMem old2.
  Proof.
    intros envImpl envSpec old1 new1 old2 v Hsem mid2.
    unfold implTickCycle in Hsem.
    apply SemAction_lift_np_rf_impl in Hsem as [rf1' [Hrf1' Hnew1]].
    apply SemAction_incrementMcycle_iff in Hrf1' as [Hrf1' Hv]; subst rf1' v.
    assert (Hspec : SemAction envSpec (@specTickCycle core pcAddrInit regions type) old2 mid2 Zmod.zero).
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
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (Henv : ImplSpecSysEnvRel envImpl envSpec)
           (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction envImpl (@implTickTimer core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions clint type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction envSpec (@specTickTimer core pcAddrInit regions clint type) old2 mid2 v /\
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros envImpl envSpec Henv old1 new1 old2 v Hmem Hsem mid2.
    unfold implTickTimer in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions clint.(clintIdx)
                (@clintRegion core regions clint) clint.(pfClint)
                (Henv old1 old2 Hmem)
                (clintTick core type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction envSpec (@specTickTimer core pcAddrInit regions clint type) old2 mid2 v).
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
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (Henv : ImplSpecSysEnvRel envImpl envSpec)
           (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction envImpl (@implSampleMtipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions clint type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction envSpec (@specSampleMtipStep core pcAddrInit regions clint type) old2 mid2 v /\
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros envImpl envSpec Henv old1 new1 old2 v Hmem Hsem mid2.
    unfold implSampleMtipStep in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions clint.(clintIdx)
                (@clintRegion core regions clint) clint.(pfClint)
                (Henv old1 old2 Hmem)
                (clintSampleMtip core type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction envSpec (@specSampleMtipStep core pcAddrInit regions clint type) old2 mid2 v).
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
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (Henv : ImplSpecSysEnvRel envImpl envSpec)
           (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction envImpl (@implPlicClaimStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions plic type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction envSpec (@specPlicClaimStep core pcAddrInit regions plic type) old2 mid2 v /\
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros envImpl envSpec Henv old1 new1 old2 v Hmem Hsem mid2.
    unfold implPlicClaimStep in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                (@plicRegion core _ regions plic) plic.(pfPlic)
                (Henv old1 old2 Hmem)
                (@updateClaim core _ type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction envSpec (@specPlicClaimStep core pcAddrInit regions plic type) old2 mid2 v).
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
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (Henv : ImplSpecSysEnvRel envImpl envSpec)
           (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction envImpl (@implPlicSampleMeipStep core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions plic type) old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemAction envSpec (@specPlicSampleMeipStep core pcAddrInit regions plic type) old2 mid2 v /\
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros envImpl envSpec Henv old1 new1 old2 v Hmem Hsem mid2.
    unfold implPlicSampleMeipStep in Hsem.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                (@plicRegion core _ regions plic) plic.(pfPlic)
                (Henv old1 old2 Hmem)
                (@plicSampleMeip core _ type) (implMem old1) m1' v Hm1')
      as [HspecMem [Hextra Hm1'Eq]].
    assert (Hm1'_proj : implMem new1 = m1') by (subst new1; reflexivity).
    rewrite <- Hm1'_proj in *.
    assert (Hspec : SemAction envSpec (@specPlicSampleMeipStep core pcAddrInit regions plic type) old2 mid2 v).
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
               forall (envI : Env (implMemTree regions))
                      (envS : Env (specMemTree regions)),
                 ImplSpecMemEnvRel core regions envI envS ->
                 forall (s s' : TreeState DomainElemState (implMemTree regions)) (v : bool),
                   SemAction envI aI s s' v ->
                   SemAction envS aS (projImplMemSpecState core regions s) (projImplMemSpecState core regions s') v /\
                   projImplMemExtraState core regions s' = projImplMemExtraState core regions s /\
                   s' = writeImplMemSpecState core regions s (projImplMemSpecState core regions s'))
            (implMemCollectIrqActions regions type ++
             [@implNthRegionAction core type plic.(plicIdx) regions (plicRegion plic) plic.(pfPlic) Bool
                (Recv "uartIrq" (plicUartIrqPath core (S (S (length (collectIrqActions regions))))) (fun v => Return #v))])
            (map (fun f => f type) (collectIrqActions regions) ++
             [@plicUartIrqAction core (S (S (length (collectIrqActions regions)))) regions plic type]).
  Proof.
    apply Forall2_app.
    - unfold implMemCollectIrqActions.
      assert (Hgen : forall (rs : list MemRegion),
                Forall2 (fun (aI : Action type (implRegionsTree rs) Bool)
                             (aS : Action type (specMemTree rs) Bool) =>
                           forall (envI : Env (implRegionsTree rs))
                                  (envS : Env (specMemTree rs)),
                             ImplSpecRegionsEnvRel core rs envI envS ->
                             forall (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bool),
                               SemAction envI aI s s' v ->
                               SemAction envS aS (projImplRegionsSpecState core rs s) (projImplRegionsSpecState core rs s') v /\
                               projImplRegionsExtraState core rs s' = projImplRegionsExtraState core rs s /\
                               s' = writeImplRegionsSpecState core rs s (projImplRegionsSpecState core rs s'))
                        (map (fun f => f type) (implCollectIrqActions rs))
                        (map (fun f => f type) (collectIrqActions rs))).
      { induction rs as [| r rs IH]; unfold implCollectIrqActions, collectIrqActions, implCollectRegionActions; cbn [genCollectRegionActions implMemRegionIrqActions memRegionIrqActions].
        - constructor.
        - assert (Hrest :
            Forall2 (fun (aI : Action type (implRegionsTree (r :: rs)) Bool)
                         (aS : Action type (specMemTree (r :: rs)) Bool) =>
                       forall (envI : Env (implRegionsTree (r :: rs)))
                              (envS : Env (specMemTree (r :: rs))),
                         ImplSpecRegionsEnvRel core (r :: rs) envI envS ->
                         forall (s s' : TreeState DomainElemState (implRegionsTree (r :: rs))) (v : bool),
                           SemAction envI aI s s' v ->
                           SemAction envS aS (projImplRegionsSpecState core (r :: rs) s) (projImplRegionsSpecState core (r :: rs) s') v /\
                           projImplRegionsExtraState core (r :: rs) s' = projImplRegionsExtraState core (r :: rs) s /\
                           s' = writeImplRegionsSpecState core (r :: rs) s (projImplRegionsSpecState core (r :: rs) s'))
                    (map (fun f => f type) (map (fun act ty => liftAction child1Path (act ty)) (implCollectIrqActions rs)))
                    (map (fun f => f type) (map (fun act ty => liftAction child1Path (act ty)) (collectIrqActions rs)))).
          { rewrite !map_map.
            eapply (Forall2_map_both _ _
                      (fun (aI : Action type (implRegionsTree rs) Bool) => liftAction child1Path aI)
                      (fun (aS : Action type (specMemTree rs) Bool) => liftAction child1Path aS)) in IH.
            - rewrite !map_map in IH; exact IH.
            - intros aI aS Hsim0 envI envS Henv s s' v Hsem.
              rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
              apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
              rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
              pose proof (proj2 Henv s) as Henv1.
              cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplRegionsSpecState projImplRegionsExtraState writeImplRegionsSpecState Fst Snd] in *.
              destruct (Hsim0 _ _ Henv1 _ _ _ Hsub1') as [HspecSub1 [HextraSub1 HwriteSub1]].
              rewrite HextraSub1; split; [| split; [reflexivity | rewrite writeImplRegionSpecState_projImplRegionSpecState, <- HwriteSub1; destruct (Snd (Snd s)); reflexivity]].
              rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
              cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
              rewrite SemAction_iff_evalActionPropGen in HspecSub1.
              eapply evalActionPropGen_mono; [| exact HspecSub1].
              intros st ret [Hst Hret]; subst; split; reflexivity. }
          unfold implMemRegionIrqActions, memRegionIrqActions; destruct (memRegionIrqAction r) as [irqAct |]; cbn [map app]; [| exact Hrest].
          constructor; [| exact Hrest].
          intros envI envS Henv s s' v Hsem.
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
          cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsem.
          rewrite (@evalActionPropGen_liftToImplRegion core r) in Hsem.
          apply evalActionPropGen_ex_iff in Hsem as [m' [Hm' Hs']]; subst s'.
          pose proof (proj1 Henv s) as Henv0.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplRegionsSpecState projImplRegionsExtraState writeImplRegionsSpecState Fst Snd] in *.
          rewrite projImplRegionSpecState_writeImplRegionSpecState.
          rewrite projImplRegionExtraState_writeImplRegionSpecState.
          split; [| split; [reflexivity | rewrite writeImplRegionsSpecState_projImplRegionsSpecState; destruct s as [? [? []]]; reflexivity]].
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
          eapply evalActionPropGen_env_mono; [exact Henv0 |].
          eapply evalActionPropGen_mono; [| exact Hm'].
          intros st ret [Hst Hret]; subst; split; reflexivity. }
      pose proof (Hgen regions) as Hregs.
      eapply (Forall2_map_both _ _
                (fun (aI : Action type (implRegionsTree regions) Bool) => liftAction child0Path aI)
                (fun (aS : Action type (specMemTree regions) Bool) => aS)) in Hregs.
      + rewrite !map_map in Hregs; exact Hregs.
      + intros aI aS Hsim0 envI envS Henv s s' v Hsem.
        exact (SemAction_lift_child0_implMem core regions Henv aI aS Hsim0 s s' v Hsem).
    - constructor; [| constructor].
      intros envI envS Henv s s' v Hsem.
      unfold plicUartIrqAction, plicAction in *.
      exact (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
               (@plicRegion core _ regions plic) plic.(pfPlic) Henv
               (Recv "uartIrq" (plicUartIrqPath core _) (fun v0 => Return #v0))
               s s' v Hsem).
  Qed.

  Theorem sim_implPlicPendingsSteps :
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (Henv : ImplSpecSysEnvRel envImpl envSpec)
           act (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      In act (@implPlicPendingsSteps core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions plic type) ->
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction envImpl act old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros envImpl envSpec Henv act old1 new1 old2 v Hin Hmem Hsem mid2.
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
    pose proof (Henv old1 old2 Hmem) as HenvMem.
    assert (Hhelper :
      forall (actsI : list (Action type (implMemTree regions) Bool))
             (actsS : list (Action type (specMemTree regions) Bool))
             (pends : list (RegOfKind (t := plicTree core (S (S (length (collectIrqActions regions))))) Bool))
             (insvs : list (RegOfKind (t := plicTree core (S (S (length (collectIrqActions regions))))) Bool)),
        Forall2 (fun (aI : Action type (implMemTree regions) Bool)
                     (aS : Action type (specMemTree regions) Bool) =>
                   forall (envI : Env (implMemTree regions))
                          (envS : Env (specMemTree regions)),
                     ImplSpecMemEnvRel core regions envI envS ->
                     forall (s s' : TreeState DomainElemState (implMemTree regions)) (v0 : bool),
                       SemAction envI aI s s' v0 ->
                       SemAction envS aS (projImplMemSpecState core regions s) (projImplMemSpecState core regions s') v0 /\
                       projImplMemExtraState core regions s' = projImplMemExtraState core regions s /\
                       s' = writeImplMemSpecState core regions s (projImplMemSpecState core regions s'))
                actsI actsS ->
        In memAct
          ((fix helper (a : list (Action type (implMemTree regions) Bool))
                       (p i : list (RegOfKind (t := plicTree core (S (S (length (collectIrqActions regions))))) Bool))
             : list (Action type (implMemTree regions) (Bit 0)) :=
              match a, p, i with
              | act0 :: restActs, pendRk :: restPends, insvRk :: restInsvs =>
                  (LetA irqVal : Bool <- act0 ;
                   @implNthRegionAction core type plic.(plicIdx) regions (@plicRegion core _ regions plic) plic.(pfPlic) (Bit 0)
                     (@updatePendingLeaf core _ type pendRk insvRk irqVal))
                  :: helper restActs restPends restInsvs
              | _, _, _ => []
              end) actsI pends insvs) ->
        exists specMemAct,
          In specMemAct (@plicPendingStepsHelper core (S (S (length (collectIrqActions regions)))) regions plic type actsS pends insvs) /\
          SemAction (subEnv np_mem_s envSpec old2) specMemAct (projImplMemSpecState core regions (implMem old1)) (projImplMemSpecState core regions (implMem new1)) v /\
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
        destruct (Ha _ _ HenvMem (implMem old1) sMid irqVal Hsem1) as [Hspec1 [Hextra1 HsMid]].
        destruct (SemAction_implMemNthRegionAction core regions plic.(plicIdx)
                    (@plicRegion core _ regions plic) plic.(pfPlic) HenvMem
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
    assert (HspecAct : SemAction envSpec (liftAction np_mem_s specMemAct) old2 mid2 v).
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
    forall (rs : list MemRegion)
           (act : Action type (implRegionsTree rs) (Bit 0)),
      In act (map (fun f => f type) (implCollectFenceIAckActions rs)) ->
      exists fSpec,
        In fSpec (collectFenceIAckActions rs) /\
        forall (envI : Env (implRegionsTree rs))
               (envS : Env (specMemTree rs)),
          ImplSpecRegionsEnvRel core rs envI envS ->
          forall (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bits 0),
            SemAction envI act s s' v ->
            SemAction envS (fSpec type) (projImplRegionsSpecState core rs s) (projImplRegionsSpecState core rs s') v /\
            projImplRegionsExtraState core rs s' = projImplRegionsExtraState core rs s.
  Proof.
    induction rs as [| r rs IH]; intros act Hin.
    - cbn in Hin; contradiction.
    - unfold implCollectFenceIAckActions, implCollectRegionActions, collectFenceIAckActions in Hin |- *; cbn [genCollectRegionActions] in *.
      rewrite map_app in Hin; apply in_app_or in Hin as [HinCurr | HinRest].
      + unfold implMemRegionFenceIAckActions in HinCurr.
        rewrite !map_map in HinCurr.
        apply in_map_iff in HinCurr as [f0 [Hact Hf0]].
        subst act.
        exists (fun ty => liftAction child0Path (f0 ty)); split.
        * apply in_or_app; left.
          apply in_map_iff; exists f0; split; [reflexivity | exact Hf0].
        * intros envI envS Henv s s' v Hsem.
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
          cbn [child0Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsem.
          rewrite (@evalActionPropGen_liftToImplRegion core r) in Hsem.
          apply evalActionPropGen_ex_iff in Hsem as [m' [Hm' Hs']]; subst s'.
          pose proof (proj1 Henv s) as Henv0.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplRegionsSpecState projImplRegionsExtraState Fst Snd] in *.
          rewrite projImplRegionSpecState_writeImplRegionSpecState.
          rewrite projImplRegionExtraState_writeImplRegionSpecState.
          split; [| reflexivity].
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
          eapply evalActionPropGen_env_mono; [exact Henv0 |].
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
        * intros envI envS Henv s s' v Hsem.
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
          apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
          rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
          pose proof (proj2 Henv s) as Henv1.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplRegionsSpecState projImplRegionsExtraState Fst Snd] in *.
          destruct (Hsim0 _ _ Henv1 _ _ _ Hsub1') as [HspecSub1 HextraSub1].
          rewrite HextraSub1; split; [| reflexivity].
          rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
          cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd].
          rewrite SemAction_iff_evalActionPropGen in HspecSub1.
          eapply evalActionPropGen_mono; [| exact HspecSub1].
          intros st ret [Hst Hret]; subst; split; reflexivity.
  Qed.

  Theorem sim_fenceIAcks :
    forall {envImpl : Env iTree} {envSpec : Env sTree}
           (Henv : ImplSpecSysEnvRel envImpl envSpec)
           act (old1 new1 : TreeState DomainElemState iTree)
           (old2 : TreeState DomainElemState sTree) (v : bits 0),
      In act (@fenceIAcks core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) ->
      specMem old2 = projImplMemSpecState core regions (implMem old1) ->
      SemAction envImpl act old1 new1 v ->
      let mid2 := writeSubTreeState np_mem_s old2 (projImplMemSpecState core regions (implMem new1)) in
      SemActions envSpec (map snd (specMod type)) old2 mid2 /\
      specRf mid2 = specRf old2 /\
      specMem mid2 = projImplMemSpecState core regions (implMem new1) /\
      projImplMemExtraState core regions (implMem new1) = projImplMemExtraState core regions (implMem old1) /\
      new1 = writeSubTreeState np_mem_i old1 (implMem new1).
  Proof.
    intros envImpl envSpec Henv act old1 new1 old2 v Hin Hmem Hsem mid2.
    unfold fenceIAcks, implMemCollectFenceIAckActions in Hin.
    rewrite !map_map in Hin.
    apply in_map_iff in Hin as [f0 [Hact Hf0]].
    subst act.
    apply SemAction_lift_np_mem_impl in Hsem as [m1' [Hm1' Hnew1]].
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction, evalActionPropGen_ex_iff in Hm1'.
    destruct Hm1' as [sub0' [Hsub0' Hm1'Eq]]; subst m1'.
    rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
    assert (Hm1'_proj : implMem new1 = writeSubTreeState child0Path (implMem old1) sub0') by (subst new1; reflexivity).
    assert (HinMem : In (f0 type) (map (fun f => f type) (implCollectFenceIAckActions regions))).
    { apply in_map_iff; exists f0; split; [reflexivity | exact Hf0]. }
    destruct (implCollectFenceIAckActions_sim regions (f0 type) HinMem)
      as [fSpec [HinSpecMem Hsim]].
    pose proof (Henv old1 old2 Hmem (implMem old1)) as Henv0.
    cbn [child0Path implMemTree readSubTreeState readSubTreeState_child] in Hsub0'.
    destruct (Hsim _ _ Henv0 (Fst (implMem old1)) sub0' v Hsub0') as [HspecMem Hextra].
    assert (HspecMem' : SemAction (subEnv np_mem_s envSpec old2) (fSpec type)
                          (projImplMemSpecState core regions (implMem old1))
                          (projImplMemSpecState core regions (implMem new1)) v).
    { rewrite Hm1'_proj; unfold projImplMemSpecState; cbn [child0Path implMemTree writeSubTreeState writeSubTreeState_child Fst]; exact HspecMem. }
    assert (Hextra' : projImplMemExtraState core regions (implMem new1) =
                      projImplMemExtraState core regions (implMem old1)).
    { rewrite Hm1'_proj; unfold projImplMemExtraState; cbn [child0Path implMemTree writeSubTreeState writeSubTreeState_child Fst Snd]; rewrite Hextra; reflexivity. }
    assert (HinSpec : In (liftAction np_mem_s (fSpec type)) (map snd (specMod type))).
    { rewrite map_snd_specMod.
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
      unfold specFenceIAckSteps.
      apply in_map_iff; exists fSpec; split; [reflexivity | exact HinSpecMem]. }
    assert (HspecAct : SemAction envSpec (liftAction np_mem_s (fSpec type)) old2 mid2 v).
    { apply SemAction_lift_np_mem_spec.
      exists (projImplMemSpecState core regions (implMem new1)).
      rewrite Hmem; split; [exact HspecMem' | reflexivity]. }
    assert (Hnew1' : new1 = writeSubTreeState np_mem_i old1 (implMem new1)) by (rewrite Hm1'_proj; exact Hnew1).
    repeat split; auto.
    rewrite (Zmod_1_0 v) in HspecAct.
    eapply ConsAction with (a := liftAction np_mem_s (fSpec type)).
    - exact HinSpec.
    - exact HspecAct.
    - apply NilAction; reflexivity.
  Qed.

  (* --- 4G. `setCanProceedSteps` (`setFetchCanProceedStage`, `setDecodeCanProceedStage`, `setExecuteCanProceedStage`) --- *)

  Theorem SemAction_setFetchCanProceedStage_inv :
    forall {env : Env iTree} (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      SemAction env (@setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
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
    intros env old1 new1 v Hsem.
    unfold setFetchCanProceedStage, setFetchCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    rewrite readSubTreeState_impl_np_fetch in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew1 Hv]; subst new1 v.
    repeat split; reflexivity.
  Qed.

  Theorem SemAction_setDecodeCanProceedStage_inv :
    forall {env : Env iTree} (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      SemAction env (@setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
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
    intros env old1 new1 v Hsem.
    unfold setDecodeCanProceedStage, setDecodeCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    rewrite readSubTreeState_impl_np_decode in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew1 Hv]; subst new1 v.
    repeat split; reflexivity.
  Qed.

  Theorem SemAction_setExecuteCanProceedStage_inv :
    forall {env : Env iTree} (old1 new1 : TreeState DomainElemState iTree) (v : bits 0),
      SemAction env (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions type) old1 new1 v ->
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
    intros env old1 new1 v Hsem.
    unfold setExecuteCanProceedStage, setExecuteCanProceed in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    rewrite readSubTreeState_impl_np_execute in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [Hnew1 Hv]; subst new1 v.
    repeat split; reflexivity.
  Qed.

  Lemma implCollectRegionActions_preserves_spec :
    forall (getActions : forall r : MemRegion, list (forall ty, Action ty (implMemRegionTree r) (Bit 0)))
           (Hpres : forall (r : MemRegion) {env : Env (implMemRegionTree r)}
                           (f : forall ty, Action ty (implMemRegionTree r) (Bit 0))
                           (s s' : TreeState DomainElemState (implMemRegionTree r)) (v : bits 0),
                      In f (getActions r) ->
                      SemAction env (f type) s s' v ->
                      projImplRegionSpecState core r s' = projImplRegionSpecState core r s)
           (rs : list MemRegion)
           {env : Env (implRegionsTree rs)}
           (act : Action type (implRegionsTree rs) (Bit 0))
           (s s' : TreeState DomainElemState (implRegionsTree rs)) (v : bits 0),
      In act (map (fun f => f type) (implCollectRegionActions getActions rs)) ->
      SemAction env act s s' v ->
      projImplRegionsSpecState core rs s' = projImplRegionsSpecState core rs s.
  Proof.
    intros getActions Hpres.
    induction rs as [| r rs IH]; intros env act s s' v Hin Hsem.
    - cbn in Hin; contradiction.
    - unfold implCollectRegionActions in Hin; cbn [genCollectRegionActions] in Hin.
      rewrite map_app in Hin; apply in_app_or in Hin as [HinCurr | HinRest].
      + rewrite map_map in HinCurr; apply in_map_iff in HinCurr as [f0 [Hact Hf0]]; subst act.
        rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
        apply evalActionPropGen_ex_iff in Hsem as [sub0' [Hsub0' Hs']]; subst s'.
        rewrite <- SemAction_iff_evalActionPropGen in Hsub0'.
        cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplRegionsSpecState Fst Snd] in *.
        rewrite (Hpres r _ f0 (Fst s) sub0' _ Hf0 Hsub0').
        reflexivity.
      + rewrite map_map in HinRest; apply in_map_iff in HinRest as [fRest [Hact HfRest]]; subst act.
        rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
        apply evalActionPropGen_ex_iff in Hsem as [sub1' [Hsub1' Hs']]; subst s'.
        rewrite <- SemAction_iff_evalActionPropGen in Hsub1'.
        cbn [child0Path child1Path implRegionsTree specMemTree implRegionsChildren specMemChildren regionsTree regionsTreeChildren readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child projImplRegionsSpecState Fst Snd] in *.
        f_equal; f_equal.
        eapply IH; [| exact Hsub1'].
        apply in_map_iff; exists fRest; split; [reflexivity | exact HfRest].
  Qed.
End SystemDevicesSim.

(* ===========================================================================
 * 5. CONCRETE `ExternalMem` ENVIRONMENT (`Env`) & HANDSHAKE INVARIANTS
 * =========================================================================== *)

Section ExternalMemEnvAndHandshake.
  Variable dom : string.

  (* --- 5A. Store Versions (`maskUpdateSameTuple`, `applyLineWriteRq`, `evalLineWriteRqTrace`) --- *)

  Fixpoint maskUpdateList {A : Type} {n : nat}
    (idx : nat) (upds : list A) (masks : list bool) (acc : SameTuple A n) : SameTuple A n :=
    match masks, upds with
    | true :: ms, u :: us => maskUpdateList (S idx) us ms (updSameTupleNat acc idx u)
    | false :: ms, _ :: us => maskUpdateList (S idx) us ms acc
    | _, _ => acc
    end.

  Definition maskUpdateSameTuple {A : Type} {n : nat}
    (upd val : SameTuple A n) (mask : SameTuple bool n) : SameTuple A n :=
    maskUpdateList 0%nat upd.(tupleElems) mask.(tupleElems) val.

  Definition applyLineWriteRq
    (lineAddr : bits AddrSz)
    (w : type LineWriteRq)
    (rp : type LineReadRp) : type LineReadRp :=
    let w_addr     := w.(Fst) in
    let w_data     := w.(Snd).(Fst) in
    let w_dataMask := w.(Snd).(Snd).(Fst) in
    let w_tag      := w.(Snd).(Snd).(Snd).(Fst) in
    let w_tagMask  := w.(Snd).(Snd).(Snd).(Snd).(Fst) in
    if Zmod.eqb w_addr lineAddr then
      let newData := maskUpdateSameTuple w_data rp.(Fst) w_dataMask in
      let newTag  := maskUpdateSameTuple w_tag rp.(Snd).(Fst) w_tagMask in
      (newData ,, (newTag ,, tt))
    else
      rp.

  Fixpoint evalLineWriteRqTrace
    (initLine : bits AddrSz -> type LineReadRp)
    (writes : list (type LineWriteRq))
    (lineAddr : bits AddrSz) : type LineReadRp :=
    match writes with
    | [] => initLine lineAddr
    | w :: ws => applyLineWriteRq lineAddr w (evalLineWriteRqTrace initLine ws lineAddr)
    end.

  Lemma evalLineWriteRqTrace_app_baseLine :
    forall (initLine : bits AddrSz -> type LineReadRp)
           (ws_used ws_base : list (type LineWriteRq))
           (lineAddr : bits AddrSz),
      evalLineWriteRqTrace
        (fun _ => evalLineWriteRqTrace initLine ws_base lineAddr)
        ws_used lineAddr =
      evalLineWriteRqTrace initLine (ws_used ++ ws_base)%list lineAddr.
  Proof.
    intros initLine ws_used ws_base lineAddr.
    induction ws_used as [| w rest IH]; cbn [evalLineWriteRqTrace app].
    - reflexivity.
    - rewrite IH; reflexivity.
  Qed.

  (* --- 5B. Data Read Constraint (`EnvDataLineReadRpAt`) --- *)

  (* A data response for the request for `lineAddr` is the latest version of that line
   * after `writes` (newest first). *)
  Definition EnvDataLineReadRpAt
    (initLine : bits AddrSz -> type LineReadRp)
    (writes : list (type LineWriteRq))
    (lineAddr : bits AddrSz)
    (rp : type LineReadRp) : Prop :=
    rp = evalLineWriteRqTrace initLine writes lineAddr.

  (* The spec answers each data request in the same action: the newest request, after
   * all of its writes. *)
  Definition EnvDataLineReadRpConstraint (r : MemRegion)
    (initLine : bits AddrSz -> type LineReadRp)
    (sr : TreeState DomainElemState (externalMemRegionTree dom r))
    (rp : type LineReadRp) : Prop :=
    EnvDataLineReadRpAt initLine sr.(Snd).(Snd).(Snd).(Fst) (hd Zmod.zero sr.(Snd).(Fst)) rp.

  Lemma EnvDataLineReadRpAt_inhabited :
    forall (initLine : bits AddrSz -> type LineReadRp)
           (writes : list (type LineWriteRq))
           (lineAddr : bits AddrSz),
      exists rp, EnvDataLineReadRpAt initLine writes lineAddr rp.
  Proof.
    intros initLine writes lineAddr.
    eexists; reflexivity.
  Qed.

  Lemma EnvDataLineReadRpConstraint_inhabited :
    forall (r : MemRegion)
           (initLine : bits AddrSz -> type LineReadRp)
           (sr : TreeState DomainElemState (externalMemRegionTree dom r)),
      exists rp, EnvDataLineReadRpConstraint r initLine sr rp.
  Proof.
    intros r initLine sr.
    apply EnvDataLineReadRpAt_inhabited.
  Qed.

  (* --- 5C. `fence.i` Request/Ack Counting (`count_true`, `RegionFenceICountInv`) --- *)

  Fixpoint count_true (l : list bool) : nat :=
    match l with
    | [] => 0%nat
    | true :: tl => S (count_true tl)
    | false :: tl => count_true tl
    end.

  Definition RegionFenceICountInv (r : MemRegion)
    (sr : TreeState DomainElemState (externalMemRegionTree dom r)) : Prop :=
    let sf         := sr.(Fst) in
    let fenceIWait := sf.(Snd).(Snd).(Fst) in
    let fenceIRq   := sf.(Snd).(Snd).(Snd).(Fst) in
    let fenceIAck  := sf.(Snd).(Snd).(Snd).(Snd).(Fst) in
    if fenceIWait then
      length fenceIRq = S (count_true fenceIAck)
    else
      length fenceIRq = count_true fenceIAck.

  Lemma RegionFenceICountInv_wait_false_iff :
    forall (r : MemRegion)
           (sr : TreeState DomainElemState (externalMemRegionTree dom r)),
      RegionFenceICountInv r sr ->
      (sr.(Fst).(Snd).(Snd).(Fst) = false <->
       length sr.(Fst).(Snd).(Snd).(Snd).(Fst) =
         count_true sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Proof.
    intros r sr Hinv.
    unfold RegionFenceICountInv in Hinv.
    destruct (sr.(Fst).(Snd).(Snd).(Fst)); split; intros H; try discriminate; try lia; reflexivity.
  Qed.

  Lemma RegionFenceICountInv_wait_true_iff :
    forall (r : MemRegion)
           (sr : TreeState DomainElemState (externalMemRegionTree dom r)),
      RegionFenceICountInv r sr ->
      (sr.(Fst).(Snd).(Snd).(Fst) = true <->
       length sr.(Fst).(Snd).(Snd).(Snd).(Fst) =
         (count_true sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) + 1)%nat).
  Proof.
    intros r sr Hinv.
    unfold RegionFenceICountInv in Hinv.
    destruct (sr.(Fst).(Snd).(Snd).(Fst)); split; intros H; try discriminate; try lia; reflexivity.
  Qed.

  Lemma InitStateConsistent_RegionFenceICountInv :
    forall (r : MemRegion)
           (sr : TreeState DomainElemState (externalMemRegionTree dom r)),
      InitStateConsistent (externalMemRegionTree dom r) sr ->
      RegionFenceICountInv r sr.
  Proof.
    intros r [[rq [rp [wait [fiRq [fiAck []]]]]] sdata]
           [[_ [_ [Hwait [HfiRq [HfiAck _]]]]] _].
    cbn in Hwait, HfiRq, HfiAck.
    unfold RegionFenceICountInv; cbn [Fst Snd].
    subst wait fiRq fiAck; reflexivity.
  Qed.

  (* --- 5D. `fence.i` Environment Constraints (`EnvFenceIAckConstraint`, `EnvFetchLineReadRpConstraint`) --- *)

  (* `fenceIWriteCount c` is the region's write count at the moment its ack count reached
   * `c` (`c >= 1`). Before any ack the snapshot is the initial memory (count 0), so the
   * oracle is never consulted at 0. *)
  Definition fenceISnapshotCount (fenceIWriteCount : nat -> nat) (fenceIAck : list bool) : nat :=
    match count_true fenceIAck with
    | 0%nat => 0%nat
    | c => fenceIWriteCount c
    end.

  (* `fenceIAck = true` only while a request is outstanding (`nFenceIRq` requests,
   * `fenceIAck` acks so far) and when the write count `nWrites` is the one fixed by
   * `fenceIWriteCount` for the ack count this ack produces (`S (count_true fenceIAck)`:
   * the trace does not contain the ack being answered yet). *)
  Definition EnvFenceIAckAt
    (fenceIWriteCount : nat -> nat)
    (nFenceIRq : nat) (fenceIAck : list bool) (nWrites : nat)
    (ack : bool) : Prop :=
    ack = true ->
    (nFenceIRq > count_true fenceIAck)%nat /\
    nWrites = fenceIWriteCount (S (count_true fenceIAck)).

  Definition EnvFenceIAckConstraint (r : MemRegion)
    (fenceIWriteCount : nat -> nat)
    (sr : TreeState DomainElemState (externalMemRegionTree dom r))
    (ack : bool) : Prop :=
    EnvFenceIAckAt fenceIWriteCount
      (length sr.(Fst).(Snd).(Snd).(Snd).(Fst)) sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
      (length sr.(Snd).(Snd).(Snd).(Fst)) ack.

  Lemma EnvFenceIAckAt_inhabited :
    forall (fenceIWriteCount : nat -> nat) (nFenceIRq : nat) (fenceIAck : list bool) (nWrites : nat),
      exists ack, EnvFenceIAckAt fenceIWriteCount nFenceIRq fenceIAck nWrites ack.
  Proof.
    intros fenceIWriteCount nFenceIRq fenceIAck nWrites.
    exists false; intros H; discriminate H.
  Qed.

  Lemma EnvFenceIAckConstraint_inhabited :
    forall (r : MemRegion)
           (fenceIWriteCount : nat -> nat)
           (sr : TreeState DomainElemState (externalMemRegionTree dom r)),
      exists ack, EnvFenceIAckConstraint r fenceIWriteCount sr ack.
  Proof.
    intros r fenceIWriteCount sr.
    apply EnvFenceIAckAt_inhabited.
  Qed.

  Definition isSuffix {A : Type} (sub full : list A) : Prop :=
    exists pref, full = (pref ++ sub)%list.

  (* The 16-bit instruction parcel `p` of a line response: data bytes `2p` and `2p+1`. *)
  Definition rpParcel (rp : type LineReadRp) (p : nat) : list (bits 8) :=
    firstn 2 (skipn (2 * p) rp.(Fst).(tupleElems)).

  (* Post-`fence.iAck` fetch constraint for a response to the request for `lineAddr`,
   * per 16-bit parcel (`fenceIAck` and `writes` are newest first):
   * - `n_at := fenceISnapshotCount fenceIWriteCount fenceIAck` is the write count at the
   *   last `fence.iAck` (0 before any ack: the initial memory).
   * - `writes_after := firstn (length writes - n_at) writes` is the prefix of `writes` that
   *   occurred after the last `fence.iAck`.
   * - `writes_at_fenceI := skipn (length writes - n_at) writes` is the history of writes up
   *   to the last `fence.iAck`.
   * - `baseLine` evaluates the committed state at `fence.iAck` (where all older stores to
   *   an address prior to the last store at `fence.iAck` are overwritten and irrelevant).
   * - Each parcel of `rp` independently comes from some allowed version: `baseLine` plus
   *   an oldest-first prefix `ws_used` of `writes_after`, chosen per parcel.
   * - Tag bits are unconstrained: instruction fetch never uses them. *)
  Definition EnvFetchLineReadRpAt
    (initLine : bits AddrSz -> type LineReadRp)
    (fenceIWriteCount : nat -> nat)
    (fenceIAck : list bool)
    (writes : list (type LineWriteRq))
    (lineAddr : bits AddrSz)
    (rp : type LineReadRp) : Prop :=
    let n_after          := (length writes - fenceISnapshotCount fenceIWriteCount fenceIAck)%nat in
    let writes_after     := firstn n_after writes in
    let writes_at_fenceI := skipn n_after writes in
    let baseLine         := evalLineWriteRqTrace initLine writes_at_fenceI lineAddr in
    forall p : nat,
      exists ws_used,
        isSuffix ws_used writes_after /\
        rpParcel rp p =
          rpParcel (evalLineWriteRqTrace (fun _ => baseLine) ws_used lineAddr) p.

  (* The spec answers each fetch request in the same action, so its response is for the
   * newest request, `hd fetchRqs`. *)
  Definition EnvFetchLineReadRpConstraint (r : MemRegion)
    (initLine : bits AddrSz -> type LineReadRp)
    (fenceIWriteCount : nat -> nat)
    (sr : TreeState DomainElemState (externalMemRegionTree dom r))
    (rp : type LineReadRp) : Prop :=
    EnvFetchLineReadRpAt initLine fenceIWriteCount
      sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) sr.(Snd).(Snd).(Snd).(Fst)
      (hd Zmod.zero sr.(Fst).(Fst)) rp.

  Lemma EnvFetchLineReadRpAt_inhabited :
    forall (initLine : bits AddrSz -> type LineReadRp)
           (fenceIWriteCount : nat -> nat)
           (fenceIAck : list bool)
           (writes : list (type LineWriteRq))
           (lineAddr : bits AddrSz),
      exists rp, EnvFetchLineReadRpAt initLine fenceIWriteCount fenceIAck writes lineAddr rp.
  Proof.
    intros initLine fenceIWriteCount fenceIAck writes lineAddr.
    unfold EnvFetchLineReadRpAt.
    eexists; intros p; exists []; split.
    - exists (firstn (length writes - fenceISnapshotCount fenceIWriteCount fenceIAck) writes).
      rewrite app_nil_r; reflexivity.
    - reflexivity.
  Qed.

  Lemma EnvFetchLineReadRpConstraint_inhabited :
    forall (r : MemRegion)
           (initLine : bits AddrSz -> type LineReadRp)
           (fenceIWriteCount : nat -> nat)
           (sr : TreeState DomainElemState (externalMemRegionTree dom r)),
      exists rp, EnvFetchLineReadRpConstraint r initLine fenceIWriteCount sr rp.
  Proof.
    intros r initLine fenceIWriteCount sr.
    apply EnvFetchLineReadRpAt_inhabited.
  Qed.

  Lemma firstn_app_S :
    forall {A : Type} (n : nat) (x : A) (l : list A),
      firstn (S n) (x :: l) = (x :: firstn n l)%list.
  Proof.
    reflexivity.
  Qed.

  Lemma skipn_cons_S :
    forall {A : Type} (n : nat) (x : A) (l : list A),
      skipn (S n) (x :: l) = skipn n l.
  Proof.
    reflexivity.
  Qed.

  (* Monotonicity of `EnvFetchLineReadRpAt` when newer stores `ws_new` are prepended
   * to `writes` without an intervening `fence.iAck`: any response `rp` valid at
   * `t_fetch` remains valid at `t_exec`. *)
  Lemma EnvFetchLineReadRpAt_prepend_stores :
    forall (initLine : bits AddrSz -> type LineReadRp)
           (fenceIWriteCount : nat -> nat)
           (ws_new : list (type LineWriteRq))
           (acks1 acks2 : list bool)
           (writes1 writes2 : list (type LineWriteRq))
           (lineAddr : bits AddrSz)
           (rp : type LineReadRp),
      (length writes1 >= fenceISnapshotCount fenceIWriteCount acks1)%nat ->
      count_true acks2 = count_true acks1 ->
      writes2 = (ws_new ++ writes1)%list ->
      EnvFetchLineReadRpAt initLine fenceIWriteCount acks1 writes1 lineAddr rp ->
      EnvFetchLineReadRpAt initLine fenceIWriteCount acks2 writes2 lineAddr rp.
  Proof.
    intros initLine fenceIWriteCount ws_new acks1 acks2 writes1 writes2 lineAddr rp
           Hlen Hack Hwrites Henv1.
    assert (Hsnap : fenceISnapshotCount fenceIWriteCount acks2 =
                    fenceISnapshotCount fenceIWriteCount acks1)
      by (unfold fenceISnapshotCount; rewrite Hack; reflexivity).
    unfold EnvFetchLineReadRpAt in Henv1 |- *.
    rewrite Hsnap, Hwrites, length_app.
    set (N := fenceISnapshotCount fenceIWriteCount acks1) in *.
    set (W := writes1) in *.
    replace (length ws_new + length W - N)%nat
       with (length ws_new + (length W - N))%nat by lia.
    assert (Hfirstn : firstn (length ws_new + (length W - N)) (ws_new ++ W) =
                      (ws_new ++ firstn (length W - N) W)%list).
    { clear -W N.
      induction ws_new as [| w rest IH]; cbn.
      - reflexivity.
      - f_equal; exact IH. }
    assert (Hskipn : skipn (length ws_new + (length W - N)) (ws_new ++ W) =
                     skipn (length W - N) W).
    { clear -W N.
      induction ws_new as [| w rest IH]; cbn.
      - reflexivity.
      - exact IH. }
    rewrite Hfirstn, Hskipn.
    intros p; destruct (Henv1 p) as [ws_used [[pref Hpref] Hrp]].
    exists ws_used; split; [| exact Hrp].
    exists (ws_new ++ pref)%list.
    rewrite <- app_assoc, <- Hpref; reflexivity.
  Qed.

  Lemma EnvFetchLineReadRpConstraint_prepend_stores :
    forall (r : MemRegion)
           (initLine : bits AddrSz -> type LineReadRp)
           (fenceIWriteCount : nat -> nat)
           (ws_new : list (type LineWriteRq))
           (sr1 sr2 : TreeState DomainElemState (externalMemRegionTree dom r))
           (rp : type LineReadRp),
      (length sr1.(Snd).(Snd).(Snd).(Fst) >=
       fenceISnapshotCount fenceIWriteCount sr1.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))%nat ->
      hd Zmod.zero sr2.(Fst).(Fst) = hd Zmod.zero sr1.(Fst).(Fst) ->
      count_true sr2.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) =
        count_true sr1.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) ->
      sr2.(Snd).(Snd).(Snd).(Fst) = (ws_new ++ sr1.(Snd).(Snd).(Snd).(Fst))%list ->
      EnvFetchLineReadRpConstraint r initLine fenceIWriteCount sr1 rp ->
      EnvFetchLineReadRpConstraint r initLine fenceIWriteCount sr2 rp.
  Proof.
    intros r initLine fenceIWriteCount ws_new sr1 sr2 rp Hlen Haddr Hack Hwrites Henv1.
    unfold EnvFetchLineReadRpConstraint in Henv1 |- *.
    rewrite Haddr.
    exact (EnvFetchLineReadRpAt_prepend_stores initLine fenceIWriteCount ws_new _ _ _ _ _ rp
             Hlen Hack Hwrites Henv1).
  Qed.

  (* --- 5E. Ready/Valid Handshake & Request/Response Conservation --- *)

  (* Requests the memory accepted: the entries of `xs` whose paired ready in `rdys` is
   * true. Both lists are newest first and paired index by index (each request is sent
   * together with the receive of its ready). *)
  Fixpoint acceptedOf {A : Type} (xs : list A) (rdys : list bool) : list A :=
    match xs, rdys with
    | x :: xs', true :: rdys' => x :: acceptedOf xs' rdys'
    | _ :: xs', false :: rdys' => acceptedOf xs' rdys'
    | _, _ => []
    end.

  (* The memory answers accepted requests in order: with `nRps` responses so far, the
   * next response is for the oldest accepted request not yet answered. *)
  Definition fifoRq {A : Type} (d : A) (accs : list A) (nRps : nat) : A :=
    nth (length accs - S nRps) accs d.

  (* Accepted fetch requests of an impl region (newest first), and the line address the
   * next fetch response is for. *)
  Definition implFetchAccRqs (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)) : list (bits AddrSz) :=
    acceptedOf ir.(Fst).(Fst).(Fst) ir.(Snd).(Fst).(Fst).

  Definition implFetchLineAddr (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)) : bits AddrSz :=
    fifoRq Zmod.zero (implFetchAccRqs r ir) (length ir.(Fst).(Fst).(Snd).(Fst)).

  Definition EnvFetchLineReadRpValidConstraint (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r))
    (valid : bool) : Prop :=
    let sr := ir.(Fst) in
    let fetch_lineReadRp := sr.(Fst).(Snd).(Fst) in
    valid = true -> (length (implFetchAccRqs r ir) > length fetch_lineReadRp)%nat.

  (* Data requests and writes are sent by the port actions together with the receive of
   * `lineReadRqReady` / `lineWriteRqReady`; only accepted ones reach the memory. *)
  Definition implDataAccRqs (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)) : list (bits AddrSz) :=
    acceptedOf ir.(Fst).(Snd).(Fst) ir.(Snd).(Snd).(Fst).

  Definition implAccWrites (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r))
    : list (type LineWriteRq) :=
    acceptedOf ir.(Fst).(Snd).(Snd).(Snd).(Fst) ir.(Snd).(Snd).(Snd).(Fst).

  Definition implDataLineAddr (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)) : bits AddrSz :=
    fifoRq Zmod.zero (implDataAccRqs r ir) (length ir.(Fst).(Snd).(Snd).(Fst)).

  Definition EnvDataLineReadRpValidConstraint (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r))
    (valid : bool) : Prop :=
    let sr := ir.(Fst) in
    let data_lineReadRp := sr.(Snd).(Snd).(Fst) in
    valid = true -> (length (implDataAccRqs r ir) > length data_lineReadRp)%nat.

  Lemma EnvFetchLineReadRpValidConstraint_inhabited :
    forall (r : MemRegion) (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)),
      exists valid, EnvFetchLineReadRpValidConstraint r ir valid.
  Proof.
    intros r ir; exists false; intros H; discriminate H.
  Qed.

  Lemma EnvDataLineReadRpValidConstraint_inhabited :
    forall (r : MemRegion) (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)),
      exists valid, EnvDataLineReadRpValidConstraint r ir valid.
  Proof.
    intros r ir; exists false; intros H; discriminate H.
  Qed.

  (* Ready/valid bookkeeping of an impl ExternalMem region. Data responses leave the region
   * as soon as they are received (into the memory's single data response buffer), so only
   * the fetch side keeps a response here. *)
  Definition ImplExternalRegionHandshakeInv (r : MemRegion)
    (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)) : Prop :=
    let sr := ir.(Fst) in
    let ifetch := ir.(Snd).(Fst) in
    let idata := ir.(Snd).(Snd) in
    let fetch_lineReadRp := sr.(Fst).(Snd).(Fst) in
    let fetch_lineReadRpValid := ifetch.(Snd).(Fst) in
    let fetch_lineReadRpReady := ifetch.(Snd).(Snd).(Fst) in
    let fetch_readRp := ifetch.(Snd).(Snd).(Snd).(Fst) in
    let data_lineReadRp := sr.(Snd).(Snd).(Fst) in
    let data_lineReadRpValid := idata.(Snd).(Snd).(Fst) in
    let data_lineReadRpReady := idata.(Snd).(Snd).(Snd).(Fst) in
    length fetch_lineReadRp = length fetch_lineReadRpReady /\
    length fetch_lineReadRp = count_true fetch_lineReadRpValid /\
    (fetch_readRp.(Snd).(Fst) = true ->
     fetch_readRp.(Fst) = hd (getDefault _) fetch_lineReadRp /\ fetch_lineReadRp <> []) /\
    length data_lineReadRp = length data_lineReadRpReady /\
    length data_lineReadRp = count_true data_lineReadRpValid.

  Lemma InitStateConsistent_ImplExternalRegionHandshakeInv :
    forall (r : MemRegion)
           (ir : TreeState DomainElemState (implExternalMemRegionTree dom r)),
      InitStateConsistent (implExternalMemRegionTree dom r) ir ->
      ImplExternalRegionHandshakeInv r ir.
  Proof.
    intros r [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
               [d_rq [d_rp [d_wr []]]]]
              [[if_rqRdy [if_rpVal [if_rpRdy [if_rdRp []]]]]
               [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           [[[_ [Hf_rp _]] [Hd_rq [Hd_rp [Hd_wr _]]]]
            [[_ [Hif_rpVal [Hif_rpRdy [Hif_rdRp _]]]]
             [Hid_rqRdy [Hid_wrRdy [Hid_rpVal [Hid_rpRdy [Hid_portRq _]]]]]]].
    cbn in
      Hf_rp, Hd_rq, Hd_rp, Hd_wr, Hif_rpVal, Hif_rpRdy, Hif_rdRp,
      Hid_rqRdy, Hid_wrRdy, Hid_rpVal, Hid_rpRdy, Hid_portRq.
    subst f_rp d_rq d_rp d_wr if_rpVal if_rpRdy if_rdRp id_rqRdy id_wrRdy id_rpVal id_rpRdy id_portRq.
    unfold ImplExternalRegionHandshakeInv; cbn.
    refine (conj eq_refl (conj eq_refl (conj (fun Hfalse => _) (conj eq_refl eq_refl))));
      discriminate Hfalse.
  Qed.

  Lemma externalSendFenceIRq_preserves_RegionFenceICountInv :
    forall (r : MemRegion) {env : Env (externalMemRegionTree dom r)}
           (sr sr' : TreeState DomainElemState (externalMemRegionTree dom r)) (v : bits 0),
      sr.(Fst).(Snd).(Snd).(Fst) = false ->
      RegionFenceICountInv r sr ->
      SemAction env (@externalSendFenceIRq dom r type) sr sr' v ->
      RegionFenceICountInv r sr' /\
      sr'.(Snd) = sr.(Snd).
  Proof.
    intros r env sr sr' v Hwait Hinv Hsem.
    unfold externalSendFenceIRq in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn in Hsem.
    destruct Hsem as [<- _].
    unfold RegionFenceICountInv in Hinv |- *; cbn [Fst Snd length].
    rewrite Hwait in Hinv.
    split; [f_equal; exact Hinv | reflexivity].
  Qed.

  Definition pExtFetchFenceIAck : RecvPath (externalMemFetchTree dom) :=
    Eval cbn in (getChildRecvPathTree (externalMemFetchTree dom) "fenceIAck").

  Lemma externalFenceIAckStep_preserves_RegionFenceICountInv :
    forall (r : MemRegion) {env : Env (externalMemRegionTree dom r)}
           (fenceIWriteCount : nat -> nat)
           (sr sr' : TreeState DomainElemState (externalMemRegionTree dom r)) (v : bits 0),
      RegionFenceICountInv r sr ->
      (length sr.(Snd).(Snd).(Snd).(Fst) >=
       fenceISnapshotCount fenceIWriteCount sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))%nat ->
      (forall ack,
         subEnv child0Path env sr (sr.(Fst)) pExtFetchFenceIAck ack ->
         EnvFenceIAckConstraint r fenceIWriteCount sr ack) ->
      SemAction env (@externalFenceIAckStep dom r type) sr sr' v ->
      RegionFenceICountInv r sr' /\
      (length sr'.(Snd).(Snd).(Snd).(Fst) >=
       fenceISnapshotCount fenceIWriteCount sr'.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))%nat /\
      sr'.(Snd) = sr.(Snd).
  Proof.
    intros r env fenceIWriteCount sr sr' v Hinv Hwlen HenvAck Hsem.
    unfold externalFenceIAckStep in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn in Hsem.
    destruct (sr.(Fst).(Snd).(Snd).(Fst)) eqn:Hwait.
    - destruct Hsem as [ack [Hack Hrest]].
      pose proof (HenvAck ack Hack) as HcAck.
      unfold EnvFenceIAckConstraint, EnvFenceIAckAt in HcAck.
      unfold RegionFenceICountInv in Hinv; rewrite Hwait in Hinv.
      destruct ack; cbn in Hrest; destruct Hrest as [<- _].
      + destruct (HcAck eq_refl) as [_ Hweq].
        unfold RegionFenceICountInv, fenceISnapshotCount; cbn [Fst Snd count_true].
        refine (conj Hinv (conj _ eq_refl)).
        rewrite Hweq; exact (Nat.le_refl _).
      + unfold RegionFenceICountInv; cbn [Fst Snd count_true].
        exact (conj Hinv (conj Hwlen eq_refl)).
    - cbn in Hsem.
      destruct Hsem as [<- _].
      exact (conj Hinv (conj Hwlen eq_refl)).
  Qed.

  Lemma implExternalFetchLineDeqRp_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bits 0),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalFetchLineDeqRp dom r type) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst) = ir.(Fst).
  Proof.
    intros r env ir ir' v Hinv Hsem.
    unfold implExternalFetchLineDeqRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction in Hsem.
    cbn in Hsem.
    destruct Hsem as [<- _].
    unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd].
    destruct Hinv as [H1 [H2 [_ [H4 H5]]]].
    refine (conj _ eq_refl).
    refine (conj H1 (conj H2 (conj _ (conj H4 H5)))).
    intros Hfalse; discriminate Hfalse.
  Qed.

  Lemma implExternalFetchLineReadRq_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (addr : bits AddrSz)
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bool),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalFetchLineReadRq dom r type addr) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst).(Fst).(Snd) = ir.(Fst).(Fst).(Snd) /\
      ir'.(Fst).(Snd) = ir.(Fst).(Snd).
  Proof.
    intros r env addr ir ir' v Hinv Hsem.
    unfold implExternalFetchLineReadRq, externalFetchLineReadRq in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    cbn [evalActionPropGen] in Hsem.
    rewrite !evalActionPropGen_liftAction in Hsem.
    cbn in Hsem.
    destruct Hsem as [rdy [_ [<- _]]].
    unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd].
    exact (conj Hinv (conj eq_refl eq_refl)).
  Qed.

  Opaque liftAction.

  Lemma implExternalFetchLineRpPort_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bits 0),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalFetchLineRpPort dom r type) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst).(Fst).(Snd).(Snd) = ir.(Fst).(Fst).(Snd).(Snd) /\
      ir'.(Fst).(Snd) = ir.(Fst).(Snd).
  Proof.
    intros r env
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [[if_rdRpData [if_rdRpVal []]] []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           ir' v Hinv Hsem.
    unfold implExternalFetchLineRpPort, implExternalFetchLineReadRp, externalFetchLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn in Hsem.
    rewrite evalActionPropGen_liftAction in Hsem; cbn in Hsem.
    destruct if_rdRpVal; cbn in Hsem.
    - destruct Hsem as [<- _].
      exact (conj Hinv (conj eq_refl eq_refl)).
    - rewrite evalActionPropGen_liftAction in Hsem; cbn in Hsem.
      destruct Hsem as [valid [_ HvalidBranch]].
      destruct valid; cbn in HvalidBranch.
      + rewrite !evalActionPropGen_liftAction in HvalidBranch; cbn in HvalidBranch.
        destruct HvalidBranch as [rp [_ HrpBranch]].
        rewrite evalActionPropGen_liftAction in HrpBranch; cbn in HrpBranch.
        destruct HrpBranch as [<- _].
        unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd length count_true hd] in Hinv |- *.
        destruct Hinv as [H1 [H2 [H3 [H4 H5]]]].
        refine (conj _ (conj eq_refl eq_refl)).
        refine (conj (f_equal S H1) (conj (f_equal S H2) (conj _ (conj H4 H5)))).
        intros _; split; [reflexivity | intro Hnil; discriminate Hnil].
      + destruct HvalidBranch as [<- _].
        unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd length count_true] in Hinv |- *.
        destruct Hinv as [H1 [H2 [H3 [H4 H5]]]].
        refine (conj _ (conj eq_refl eq_refl)).
        refine (conj H1 (conj H2 (conj _ (conj H4 H5)))).
        intros Hfalse; discriminate Hfalse.
  Qed.

  (* The data response port receives the response of the outstanding line read, if it has
   * arrived, and returns it to the memory. *)
  Lemma implExternalLineRpPort_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r))
           (v : type (Option LineReadRp)),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalLineRpPort dom r type) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst).(Fst) = ir.(Fst).(Fst) /\
      ir'.(Fst).(Snd).(Snd).(Snd) = ir.(Fst).(Snd).(Snd).(Snd) /\
      (v.(Snd).(Fst) = true ->
       v.(Fst) = hd (getDefault _) ir'.(Fst).(Snd).(Snd).(Fst) /\
       ir'.(Fst).(Snd).(Snd).(Fst) <> []).
  Proof.
    intros r env
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [if_rdRp []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           ir' v Hinv Hsem.
    unfold implExternalLineRpPort, externalLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn in Hsem.
    destruct Hsem as [valid [_ HvalidBranch]].
    destruct valid; cbn in HvalidBranch.
    - rewrite evalActionPropGen_liftAction in HvalidBranch; cbn in HvalidBranch.
      destruct HvalidBranch as [rp [_ [<- <-]]].
      unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd length count_true hd] in Hinv |- *.
      destruct Hinv as [H1 [H2 [H3 [H4 H5]]]].
      refine (conj (conj H1 (conj H2 (conj H3 (conj (f_equal S H4) (f_equal S H5)))))
                   (conj eq_refl (conj eq_refl _))).
      intros _; split; [reflexivity | intro Hnil; discriminate Hnil].
    - destruct HvalidBranch as [<- <-].
      refine (conj Hinv (conj eq_refl (conj eq_refl _))).
      intros Hfalse; discriminate Hfalse.
  Qed.

  Transparent liftAction.

  (* The staging and port actions below only move requests between `portRq` and the
   * region's spec-part request traces, and the invariant mentions none of those values.
   * So the proofs keep `evalExpr` opaque and case on the `if` guards as opaque booleans:
   * no request value is evaluated. *)
  Ltac caseIfGuard H :=
    lazymatch type of H with context [if ?c then _ else _] => destruct c end;
    cbn -[evalExpr] in H.

  Lemma implExternalLineReadRq_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (addr : bits AddrSz)
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bool),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalLineReadRq dom r type addr) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst) = ir.(Fst).
  Proof.
    intros r env addr
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [if_rdRp []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           ir' v Hinv Hsem.
    unfold implExternalLineReadRq in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn -[evalExpr] in Hsem.
    unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd] in Hinv.
    caseIfGuard Hsem; destruct Hsem as [<- _]; cbn [Fst Snd];
      exact (conj Hinv eq_refl).
  Qed.

  Lemma implExternalLineWriteRq_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (rq : type LineWriteRq)
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bool),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalLineWriteRq dom r type rq) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst) = ir.(Fst).
  Proof.
    intros r env rq
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [if_rdRp []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           ir' v Hinv Hsem.
    unfold implExternalLineWriteRq in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn -[evalExpr] in Hsem.
    unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd] in Hinv.
    caseIfGuard Hsem; destruct Hsem as [<- _]; cbn [Fst Snd];
      exact (conj Hinv eq_refl).
  Qed.

  Lemma implExternalLineReadRqPort_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bits 0),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalLineReadRqPort dom r type) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst).(Fst) = ir.(Fst).(Fst) /\
      ir'.(Fst).(Snd).(Snd) = ir.(Fst).(Snd).(Snd).
  Proof.
    intros r env
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [if_rdRp []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           ir' v Hinv Hsem.
    unfold implExternalLineReadRqPort, externalLineReadRq in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn -[evalExpr] in Hsem.
    unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd] in Hinv.
    caseIfGuard Hsem.
    - destruct Hsem as [extRdy [_ Hsem]].
      caseIfGuard Hsem; destruct Hsem as [<- _]; cbn [Fst Snd];
        exact (conj Hinv (conj eq_refl eq_refl)).
    - destruct Hsem as [<- _]; cbn [Fst Snd];
        exact (conj Hinv (conj eq_refl eq_refl)).
  Qed.

  Lemma implExternalLineWriteRqPort_preserves_HandshakeInv :
    forall (r : MemRegion) {env : Env (implExternalMemRegionTree dom r)}
           (ir ir' : TreeState DomainElemState (implExternalMemRegionTree dom r)) (v : bits 0),
      ImplExternalRegionHandshakeInv r ir ->
      SemAction env (@implExternalLineWriteRqPort dom r type) ir ir' v ->
      ImplExternalRegionHandshakeInv r ir' /\
      ir'.(Fst).(Fst) = ir.(Fst).(Fst) /\
      ir'.(Fst).(Snd).(Fst) = ir.(Fst).(Snd).(Fst) /\
      ir'.(Fst).(Snd).(Snd).(Fst) = ir.(Fst).(Snd).(Snd).(Fst).
  Proof.
    intros r env
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [if_rdRp []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           ir' v Hinv Hsem.
    unfold implExternalLineWriteRqPort, externalLineWrite in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn -[evalExpr] in Hsem.
    unfold ImplExternalRegionHandshakeInv in Hinv |- *; cbn [Fst Snd] in Hinv.
    caseIfGuard Hsem.
    - destruct Hsem as [extRdy [_ Hsem]].
      caseIfGuard Hsem; destruct Hsem as [<- _]; cbn [Fst Snd];
        exact (conj Hinv (conj eq_refl (conj eq_refl eq_refl))).
    - destruct Hsem as [<- _]; cbn [Fst Snd];
        exact (conj Hinv (conj eq_refl (conj eq_refl eq_refl))).
  Qed.

End ExternalMemEnvAndHandshake.

(* ===========================================================================
 * 6. CONCRETE SYSTEM ENVIRONMENTS (`specEnv`, `implEnv`)
 * ===========================================================================
 * Each env answers a receive exactly when the memory-version invariant of
 * section 5 allows the answer, evaluated on the receiving side's own state:
 * - data `lineReadRp`: the latest store version (`EnvDataLineReadRpAt`);
 * - fetch `lineReadRp`: the snapshot at the last `fence.iAck` plus an oldest-first
 *   prefix of the later stores, per 16-bit parcel (`EnvFetchLineReadRpAt`);
 * - `fenceIAck = true`: only while a request is outstanding, at the write count
 *   fixed by `fenceIWriteCount` (`EnvFenceIAckAt`).
 * The spec answers its newest request (it answers in the same action) and counts all
 * of its writes. The impl memory sees only accepted requests and writes (sent with
 * ready = true) and answers accepted requests in order (`implFetchLineAddr`,
 * `implDataLineAddr`, `implAccWrites`).
 * `implEnv` also allows `lineReadRpValid = true` only while a request is outstanding
 * (`EnvFetchLineReadRpValidConstraint`, `EnvDataLineReadRpValidConstraint`).
 * Every other receive port (ready signals, `CustomMem` children) is unconstrained.
 * Both envs share `initLine` (the initial external memory contents). Each takes a
 * `fenceIWriteCount` oracle indexed by region position; the top-level theorem
 * quantifies over the impl's and picks the spec's per run. *)

(* --- 6A. Env Combinators (`EnvCtx`, `envCtxCons`, `envNodeCons`) --- *)

Section EnvCombinators.
  (* An env fragment for subtree `t` whose leaf constraints read a context `S`
   * (e.g. the state of the enclosing memory region).
   * `Env t` is definitionally `EnvCtx (TreeState DomainElemState t) t`. *)
  Definition EnvCtx (S : Type) (t : Tree DomainElem) : Type :=
    S -> forall x : RecvPath t, type (getRecvKind x) -> Prop.

  Definition envCtxTrue {S : Type} {t : Tree DomainElem} : EnvCtx S t :=
    fun _ _ _ => True.

  Definition envCtxLeaf {S : Type} {name d : string} {k : Kind}
    (P : S -> type k -> Prop) : EnvCtx S (Leaf name (d, ERecv k)) :=
    fun s _ v => P s v.

  Definition envCtxMap {S S' : Type} {t : Tree DomainElem}
    (f : S -> S') (e : EnvCtx S' t) : EnvCtx S t :=
    fun s => e (f s).

  (* Context-sharing cons: dispatch on the first step of the receive path. *)
  Definition envCtxCons {S : Type} {name : string}
    {c : Tree DomainElem} {cs : list (Tree DomainElem)}
    (e0 : EnvCtx S c) (er : EnvCtx S (Node name cs)) : EnvCtx S (Node name (c :: cs)) :=
    fun s x =>
      match x.(recvPath) as rp return
        forall pf : Is_true (isRecvElem (@getLeafElem (Node name (c :: cs)) rp)),
          type (getRecvKind (@Build_RecvPath (Node name (c :: cs)) rp pf)) -> Prop
      with
      | inl p => fun pf v => e0 s (@Build_RecvPath c p pf) v
      | inr q => fun pf v => er s (@Build_RecvPath (Node name cs) q pf) v
      end x.(recvPathPf).

  (* State-splitting cons: child `c` sees its own state, the rest sees the rest. *)
  Definition envNodeCons {name : string}
    {c : Tree DomainElem} {cs : list (Tree DomainElem)}
    (e0 : Env c) (er : Env (Node name cs)) : Env (Node name (c :: cs)) :=
    envCtxCons
      (envCtxMap (fun s : TreeState DomainElemState (Node name (c :: cs)) => s.(Fst)) e0)
      (envCtxMap (fun s : TreeState DomainElemState (Node name (c :: cs)) => s.(Snd)) er).

  Definition EnvCtxInhabited {S : Type} {t : Tree DomainElem} (e : EnvCtx S t) : Prop :=
    forall s x, exists v, e s x v.

  Lemma envCtxTrue_inhabited :
    forall (S : Type) (t : Tree DomainElem), EnvCtxInhabited (@envCtxTrue S t).
  Proof.
    intros S t s x; exists (getDefault _); exact I.
  Qed.

  Lemma envCtxLeaf_inhabited :
    forall (S : Type) (name d : string) (k : Kind) (P : S -> type k -> Prop),
      (forall s, exists v, P s v) ->
      EnvCtxInhabited (@envCtxLeaf S name d k P).
  Proof.
    intros S name d k P HP s x; exact (HP s).
  Qed.

  Lemma envCtxMap_inhabited :
    forall (S S' : Type) (t : Tree DomainElem) (f : S -> S') (e : EnvCtx S' t),
      EnvCtxInhabited e -> EnvCtxInhabited (envCtxMap f e).
  Proof.
    intros S S' t f e He s x; exact (He (f s) x).
  Qed.

  Lemma envCtxCons_inhabited :
    forall (S : Type) (name : string) (c : Tree DomainElem) (cs : list (Tree DomainElem))
           (e0 : EnvCtx S c) (er : EnvCtx S (Node name cs)),
      EnvCtxInhabited e0 -> EnvCtxInhabited er -> EnvCtxInhabited (envCtxCons e0 er).
  Proof.
    intros S name c cs e0 er H0 Hr s [rp pf].
    destruct rp as [p | q].
    - exact (H0 s (@Build_RecvPath c p pf)).
    - exact (Hr s (@Build_RecvPath (Node name cs) q pf)).
  Qed.

  Lemma envNodeCons_inhabited :
    forall (name : string) (c : Tree DomainElem) (cs : list (Tree DomainElem))
           (e0 : Env c) (er : Env (Node name cs)),
      EnvCtxInhabited e0 -> EnvCtxInhabited er -> EnvCtxInhabited (envNodeCons e0 er).
  Proof.
    intros name c cs e0 er H0 Hr.
    apply envCtxCons_inhabited; apply envCtxMap_inhabited; assumption.
  Qed.
End EnvCombinators.

(* --- 6B. Region Envs (`specRegionsEnv`, `implMemEnv`) --- *)

Section RegionEnvs.
  Variable dom : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  (* `fwc` is the region's own `fenceIWriteCount` oracle (ack index -> write count).
   * The external-memory envs read a context `S` (the receiving side's region state):
   * `getSr` gives the region's spec-part traces, `writesOf` the writes the memory has
   * accepted (newest first), and `fetchAddr` / `dataAddr` the lines the next fetch and
   * data responses are for. *)

  (* `externalMemFetchTree`: [ lineReadRq; lineReadRp; fenceIWait; fenceIRq; fenceIAck ] *)
  Definition extFetchEnvCtx {S : Type} (r : MemRegion) (fwc : nat -> nat)
    (getSr : S -> TreeState DomainElemState (externalMemRegionTree dom r))
    (writesOf : S -> list (type LineWriteRq))
    (fetchAddr : S -> bits AddrSz)
    : EnvCtx S (externalMemFetchTree dom) :=
    envCtxCons envCtxTrue
     (envCtxCons (envCtxLeaf (k := LineReadRp) (fun s rp =>
                    EnvFetchLineReadRpAt (initLine r) fwc
                      (getSr s).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                      (writesOf s) (fetchAddr s) rp))
      (envCtxCons envCtxTrue
       (envCtxCons envCtxTrue
        (envCtxCons (envCtxLeaf (k := Bool) (fun s ack =>
                       EnvFenceIAckAt fwc
                         (length (getSr s).(Fst).(Snd).(Snd).(Snd).(Fst))
                         (getSr s).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst)
                         (length (writesOf s)) ack))
         envCtxTrue)))).

  (* `externalMemRegionTree`: [ fetch; lineReadRq; lineReadRp; lineWriteRq ] *)
  Definition extRegionEnvCtx {S : Type} (r : MemRegion) (fwc : nat -> nat)
    (getSr : S -> TreeState DomainElemState (externalMemRegionTree dom r))
    (writesOf : S -> list (type LineWriteRq))
    (fetchAddr dataAddr : S -> bits AddrSz)
    : EnvCtx S (externalMemRegionTree dom r) :=
    envCtxCons (extFetchEnvCtx r fwc getSr writesOf fetchAddr)
     (envCtxCons envCtxTrue
      (envCtxCons (envCtxLeaf (k := LineReadRp) (fun s rp =>
                     EnvDataLineReadRpAt (initLine r) (writesOf s) (dataAddr s) rp))
       (envCtxCons envCtxTrue envCtxTrue))).

  (* The spec answers each request in the same action (the newest request), after all
   * of its writes. *)
  Definition specExtRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (externalMemRegionTree dom r) :=
    extRegionEnvCtx r fwc (fun sr => sr) (fun sr => sr.(Snd).(Snd).(Snd).(Fst))
      (fun sr => hd Zmod.zero sr.(Fst).(Fst)) (fun sr => hd Zmod.zero sr.(Snd).(Fst)).

  (* `implExternalMemFetchTree`: [ lineReadRqReady; lineReadRpValid; lineReadRpReady; readRp ] *)
  Definition implExtFetchEnv (r : MemRegion)
    : EnvCtx (TreeState DomainElemState (implExternalMemRegionTree dom r)) (implExternalMemFetchTree dom) :=
    envCtxCons envCtxTrue
     (envCtxCons (envCtxLeaf (k := Bool) (fun ir valid =>
                    EnvFetchLineReadRpValidConstraint dom r ir valid))
      envCtxTrue).

  (* `implExternalMemRegionTree`:
   *   [ externalMemRegionTree; fetch; lineReadRqReady; lineWriteRqReady;
   *     lineReadRpValid; lineReadRpReady; portRq ]
   * The impl memory sees only accepted writes, and answers accepted requests in order
   * (`implFetchLineAddr`, `implDataLineAddr`). *)
  Definition implExtRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (implExternalMemRegionTree dom r) :=
    envCtxCons
      (extRegionEnvCtx r fwc
         (fun ir : TreeState DomainElemState (implExternalMemRegionTree dom r) => ir.(Fst))
         (implAccWrites dom r) (implFetchLineAddr dom r) (implDataLineAddr dom r))
      (envCtxCons (implExtFetchEnv r)
       (envCtxCons envCtxTrue
        (envCtxCons envCtxTrue
         (envCtxCons (envCtxLeaf (k := Bool) (fun ir valid =>
                        EnvDataLineReadRpValidConstraint dom r ir valid))
          envCtxTrue)))).

  Definition specRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (memRegionTree dom r) :=
    match r.(regionKind) as k return Env (memRegionKindTree dom r k) with
    | ExternalMem => specExtRegionEnv r fwc
    | CustomMem _ _ _ _ => envCtxTrue
    end.

  Definition implRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (implMemRegionTree dom r) :=
    match r.(regionKind) as k return Env (implMemRegionKindTree dom r k) with
    | ExternalMem => implExtRegionEnv r fwc
    | CustomMem _ _ _ _ => envCtxTrue
    end.

  (* `fwcs i` is the oracle of the region at position `i` of the list. *)
  Fixpoint specRegionsEnv (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : Env (specMemTree dom regions) :=
    match regions as rs return Env (specMemTree dom rs) with
    | [] => envCtxTrue
    | r :: rs =>
        envNodeCons (specRegionEnv r (fwcs 0%nat))
                    (envNodeCons (specRegionsEnv (fun i => fwcs (S i)) rs) envCtxTrue)
    end.

  Fixpoint implRegionsEnv (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : Env (implRegionsTree dom regions) :=
    match regions as rs return Env (implRegionsTree dom rs) with
    | [] => envCtxTrue
    | r :: rs =>
        envNodeCons (implRegionEnv r (fwcs 0%nat))
                    (envNodeCons (implRegionsEnv (fun i => fwcs (S i)) rs) envCtxTrue)
    end.

  (* `implMemTree`: [ implRegionsTree; state; requester; readRp ] *)
  Definition implMemEnv (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : Env (implMemTree dom regions) :=
    envNodeCons (implRegionsEnv fwcs regions) envCtxTrue.

  Lemma extRegionEnvCtx_inhabited :
    forall (S : Type) r fwc
           (getSr : S -> TreeState DomainElemState (externalMemRegionTree dom r))
           (writesOf : S -> list (type LineWriteRq))
           (fetchAddr dataAddr : S -> bits AddrSz),
      EnvCtxInhabited (extRegionEnvCtx r fwc getSr writesOf fetchAddr dataAddr).
  Proof.
    intros S r fwc getSr writesOf fetchAddr dataAddr; unfold extRegionEnvCtx, extFetchEnvCtx.
    repeat first [ apply envCtxCons_inhabited | apply envCtxLeaf_inhabited | apply envCtxTrue_inhabited ].
    all: intros s;
      first [ apply EnvFetchLineReadRpAt_inhabited
            | apply EnvFenceIAckAt_inhabited
            | apply EnvDataLineReadRpAt_inhabited ].
  Qed.

  Lemma specExtRegionEnv_inhabited :
    forall r fwc, EnvCtxInhabited (specExtRegionEnv r fwc).
  Proof.
    intros r fwc; apply extRegionEnvCtx_inhabited.
  Qed.

  Lemma implExtRegionEnv_inhabited :
    forall r fwc, EnvCtxInhabited (implExtRegionEnv r fwc).
  Proof.
    intros r fwc; unfold implExtRegionEnv, implExtFetchEnv.
    apply envCtxCons_inhabited; [apply extRegionEnvCtx_inhabited |].
    repeat first [ apply envCtxCons_inhabited | apply envCtxLeaf_inhabited | apply envCtxTrue_inhabited ].
    all: intros s;
      first [ apply EnvFetchLineReadRpValidConstraint_inhabited
            | apply EnvDataLineReadRpValidConstraint_inhabited ].
  Qed.

  Lemma specRegionEnv_inhabited :
    forall r fwc, EnvCtxInhabited (specRegionEnv r fwc).
  Proof.
    intros r fwc; unfold specRegionEnv, memRegionTree.
    destruct (regionKind r).
    - apply specExtRegionEnv_inhabited.
    - apply envCtxTrue_inhabited.
  Qed.

  Lemma implRegionEnv_inhabited :
    forall r fwc, EnvCtxInhabited (implRegionEnv r fwc).
  Proof.
    intros r fwc; unfold implRegionEnv, implMemRegionTree.
    destruct (regionKind r).
    - apply implExtRegionEnv_inhabited.
    - apply envCtxTrue_inhabited.
  Qed.

  Lemma specRegionsEnv_inhabited :
    forall regions fwcs, EnvCtxInhabited (specRegionsEnv fwcs regions).
  Proof.
    induction regions as [| r rs IH]; intros fwcs; cbn [specRegionsEnv].
    - apply envCtxTrue_inhabited.
    - apply envNodeCons_inhabited; [apply specRegionEnv_inhabited |].
      apply envNodeCons_inhabited; [apply IH | apply envCtxTrue_inhabited].
  Qed.

  Lemma implRegionsEnv_inhabited :
    forall regions fwcs, EnvCtxInhabited (implRegionsEnv fwcs regions).
  Proof.
    induction regions as [| r rs IH]; intros fwcs; cbn [implRegionsEnv].
    - apply envCtxTrue_inhabited.
    - apply envNodeCons_inhabited; [apply implRegionEnv_inhabited |].
      apply envNodeCons_inhabited; [apply IH | apply envCtxTrue_inhabited].
  Qed.

  Lemma implMemEnv_inhabited :
    forall regions fwcs, EnvCtxInhabited (implMemEnv fwcs regions).
  Proof.
    intros regions fwcs; apply envNodeCons_inhabited;
      [apply implRegionsEnv_inhabited | apply envCtxTrue_inhabited].
  Qed.
End RegionEnvs.

(* --- 6C. System Envs (`specEnv`, `implEnv`) --- *)

Section SysEnvs.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  (* `fenceIWriteCount i k`: write count of the region at position `i` at its `k`-th ack. *)
  Variable fenceIWriteCount : nat -> nat -> nat.

  Local Abbreviation sTree := (@specSysTree core pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).

  (* `specSysTree`: sys [ core [ rf; mem [ specMemTree ]; secondLine ] ] *)
  Definition specEnv : Env sTree :=
    envNodeCons
      (envNodeCons envCtxTrue
        (envNodeCons (envNodeCons (specRegionsEnv core initLine fenceIWriteCount regions) envCtxTrue)
          envCtxTrue))
      envCtxTrue.

  (* `implSysTree`: sys [ core [ rf; waitBits; bp; mem [ implMemTree ];
   *                             fetch; decode; execute; dataMem; mulDiv ] ] *)
  Definition implEnv : Env iTree :=
    envNodeCons
      (envNodeCons envCtxTrue
        (envNodeCons envCtxTrue
          (envNodeCons envCtxTrue
            (envNodeCons (envNodeCons (implMemEnv core initLine fenceIWriteCount regions) envCtxTrue)
              envCtxTrue))))
      envCtxTrue.

  Lemma specEnv_inhabited : EnvInhabited specEnv.
  Proof.
    change (EnvCtxInhabited specEnv); unfold specEnv.
    repeat first [ apply envNodeCons_inhabited | apply envCtxTrue_inhabited | apply specRegionsEnv_inhabited ].
  Qed.

  Lemma implEnv_inhabited : EnvInhabited implEnv.
  Proof.
    change (EnvCtxInhabited implEnv); unfold implEnv.
    repeat first [ apply implRegionsEnv_inhabited | apply envNodeCons_inhabited | apply envCtxTrue_inhabited ].
  Qed.
End SysEnvs.

