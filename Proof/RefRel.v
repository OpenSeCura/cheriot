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
From Cheriot.Proof Require Import ImplSpec.

Unset Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * BUILDING BLOCKS OF THE REFINEMENT RELATION
 * ===========================================================================
 * 1. The two region lists: the spec list and the impl list differ only at the
 *    revoker position (the impl revoker region has 4 extra leaves). Both are
 *    built from a common prefix `pre`, the revoker base and its proofs, and a
 *    common suffix `post`, so the revoker sits at position `length pre`.
 * 2. The spec view of the impl memory: drop the impl-only leaves of every
 *    region and project the impl revoker onto its architectural registers. *)

(* --- 1. Region Lists --- *)

Fixpoint nth_error_app_cons_len {A : Type} (l : list A) (x : A) (r : list A)
  : nth_error (l ++ x :: r) (length l) = Some x :=
  match l as l0 return nth_error (l0 ++ x :: r) (length l0) = Some x with
  | [] => eq_refl
  | _ :: l' => nth_error_app_cons_len l' x r
  end.

Section RegionLists.
  Variable core : string.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Definition specRevRegion : MemRegion :=
    @revokerMemRegion core [] revBase revPfB revPfA.

  Definition implRevRegion : MemRegion :=
    @revokerMemRegion core (implRevokerExtraChildren core) revBase revPfB revPfA.

  Definition specRegionsOf : list MemRegion := pre ++ specRevRegion :: post.
  Definition implRegionsOf : list MemRegion := pre ++ implRevRegion :: post.

  Definition revSpecOf : @RevokerInstance core [] specRegionsOf :=
    @Build_RevokerInstance core [] specRegionsOf (length pre) revBase revPfB revPfA
      (nth_error_app_cons_len pre specRevRegion post).

  Definition revImplOf : @RevokerInstance core (implRevokerExtraChildren core) implRegionsOf :=
    @Build_RevokerInstance core (implRevokerExtraChildren core) implRegionsOf (length pre)
      revBase revPfB revPfA (nth_error_app_cons_len pre implRevRegion post).

  (* --- 2. Spec View of the Impl Memory --- *)

  (* Spec memory over the impl list -> spec memory over the spec list: identity on
   * every region but the revoker, which keeps its 7 architectural registers. *)
  Fixpoint archProjRegions (l : list MemRegion)
    : TreeState DomainElemState (specMemTree core (l ++ implRevRegion :: post)) ->
      TreeState DomainElemState (specMemTree core (l ++ specRevRegion :: post)) :=
    match l as l0 return
      TreeState DomainElemState (specMemTree core (l0 ++ implRevRegion :: post)) ->
      TreeState DomainElemState (specMemTree core (l0 ++ specRevRegion :: post))
    with
    | [] => fun s =>
        (StateRel.projImplRevokerArchState core (Fst s) ,, (Fst (Snd s) ,, tt))
    | _ :: l' => fun s =>
        (Fst s ,, (archProjRegions l' (Fst (Snd s)) ,, tt))
    end.

  (* The spec view of an impl memory: impl-only leaves dropped, revoker projected. *)
  Definition specViewOfImplMem
    (m : TreeState DomainElemState (implMemTree core implRegionsOf))
    : TreeState DomainElemState (specMemTree core specRegionsOf) :=
    archProjRegions pre (SimDevices.projImplMemSpecState core implRegionsOf m).

  (* The revoker state seen through the spec view is the architectural projection. *)
  Fixpoint nthSpecRegionStatePre (l : list MemRegion)
    : TreeState DomainElemState (specMemTree core (l ++ specRevRegion :: post)) ->
      TreeState DomainElemState (memRegionTree core specRevRegion) :=
    match l as l0 return
      TreeState DomainElemState (specMemTree core (l0 ++ specRevRegion :: post)) ->
      TreeState DomainElemState (memRegionTree core specRevRegion)
    with
    | [] => fun s => Fst s
    | _ :: l' => fun s => nthSpecRegionStatePre l' (Fst (Snd s))
    end.

  Fixpoint nthImplRegionStatePre (l : list MemRegion)
    : TreeState DomainElemState (specMemTree core (l ++ implRevRegion :: post)) ->
      TreeState DomainElemState (memRegionTree core implRevRegion) :=
    match l as l0 return
      TreeState DomainElemState (specMemTree core (l0 ++ implRevRegion :: post)) ->
      TreeState DomainElemState (memRegionTree core implRevRegion)
    with
    | [] => fun s => Fst s
    | _ :: l' => fun s => nthImplRegionStatePre l' (Fst (Snd s))
    end.

  Lemma nthSpecRegionStatePre_archProj :
    forall (l : list MemRegion)
           (s : TreeState DomainElemState (specMemTree core (l ++ implRevRegion :: post))),
      nthSpecRegionStatePre l (archProjRegions l s) =
      StateRel.projImplRevokerArchState core (nthImplRegionStatePre l s).
  Proof.
    induction l as [| r l IH]; intros s; cbn [archProjRegions nthSpecRegionStatePre nthImplRegionStatePre Fst Snd].
    - reflexivity.
    - apply IH.
  Qed.

End RegionLists.
