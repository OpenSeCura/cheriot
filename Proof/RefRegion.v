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
From Cheriot Require Import SpecDefines SpecDevice.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE REGION AT A GIVEN POSITION OF A REGION LIST
 * ===========================================================================
 * `genNthRegionAction` (SpecDevice.v) runs an action of the region at position
 * `idx` of a region tree, given `pf : nth_error regions idx = Some r0`. Here are
 * the matching state accessors: `regionStateAt` reads that region's state,
 * `updRegionStateAt` replaces it, and `envRegionAt` is the env the action sees.
 * They use the same casts as `genNthRegionAction`, so that its semantics is
 * exactly "run the action on the region's state" (`evalActionPropGen_genNthRegionAction`). *)

Section RegionAt.
  Variable regionTree : MemRegion -> Tree DomainElem.

  Local Abbreviation RS regions := (TreeState DomainElemState (regionsTree regionTree regions)).
  Local Abbreviation RgS r := (TreeState DomainElemState (regionTree r)).

  Fixpoint regionStateAt (idx : nat) (regions : list MemRegion) (r0 : MemRegion) {struct regions}
    : nth_error regions idx = Some r0 -> RS regions -> RgS r0 :=
    match regions as rs, idx as i return nth_error rs i = Some r0 -> RS rs -> RgS r0 with
    | [], 0%nat | [], S _ => fun pf _ =>
        match pf in (_ = o) return if o is Some _ then RgS r0 else True with
        | eq_refl => I
        end
    | r :: _, 0%nat => fun pf s =>
        (match (match pf in (_ = o) return if o is Some r0' then r0' = r else False with
                | eq_refl => eq_refl
                end) in (_ = y) return RgS y -> RgS r0 with
         | eq_refl => fun x => x
         end) s.(Fst)
    | _ :: rs, S i' => fun pf s => regionStateAt i' rs r0 pf s.(Snd).(Fst)
    end.

  Fixpoint updRegionStateAt (idx : nat) (regions : list MemRegion) (r0 : MemRegion) {struct regions}
    : nth_error regions idx = Some r0 -> RS regions -> RgS r0 -> RS regions :=
    match regions as rs, idx as i return nth_error rs i = Some r0 -> RS rs -> RgS r0 -> RS rs with
    | [], 0%nat | [], S _ => fun _ s _ => s
    | r :: _, 0%nat => fun pf s v =>
        ((match (match pf in (_ = o) return if o is Some r0' then r0' = r else False with
                 | eq_refl => eq_refl
                 end) in (_ = y) return RgS r0 -> RgS y with
          | eq_refl => fun x => x
          end) v ,, s.(Snd))
    | _ :: rs, S i' => fun pf s v =>
        (s.(Fst) ,, (updRegionStateAt i' rs r0 pf s.(Snd).(Fst) v ,, s.(Snd).(Snd)))
    end.

  Fixpoint envRegionAt (idx : nat) (regions : list MemRegion) (r0 : MemRegion) {struct regions}
    : nth_error regions idx = Some r0 -> Env (regionsTree regionTree regions) -> RS regions ->
      Env (regionTree r0) :=
    match regions as rs, idx as i
      return nth_error rs i = Some r0 -> Env (regionsTree regionTree rs) -> RS rs -> Env (regionTree r0)
    with
    | [], 0%nat | [], S _ => fun pf _ _ =>
        match pf in (_ = o) return if o is Some _ then Env (regionTree r0) else True with
        | eq_refl => I
        end
    | r :: _, 0%nat => fun pf env s =>
        (match (match pf in (_ = o) return if o is Some r0' then r0' = r else False with
                | eq_refl => eq_refl
                end) in (_ = y) return Env (regionTree y) -> Env (regionTree r0) with
         | eq_refl => fun e => e
         end) (subEnv child0Path env s)
    | _ :: rs, S i' => fun pf env s =>
        envRegionAt i' rs r0 pf (subEnv child1Path env s) s.(Snd).(Fst)
    end.

  (* Running an action of the region at `idx` is running it on that region's state *)
  Theorem evalActionPropGen_genNthRegionAction :
    forall (idx : nat) (regions : list MemRegion) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) {k : Kind}
           (act : Action type (regionTree r0) k)
           (env : Env (regionsTree regionTree regions)) (s : RS regions)
           (P : RS regions -> type k -> Prop),
      evalActionPropGen env (@genNthRegionAction regionTree type idx regions r0 pf k act) s P <->
      evalActionPropGen (envRegionAt idx regions r0 pf env s) act (regionStateAt idx regions r0 pf s)
        (fun v r => P (updRegionStateAt idx regions r0 pf s v) r).
  Proof.
    intros idx regions; revert idx.
    induction regions as [| r rs IH]; intros [| i'] r0 pf k act env s P; try discriminate pf.
    - cbn [genNthRegionAction regionStateAt updRegionStateAt envRegionAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      rewrite evalActionPropGen_liftAction.
      destruct s as [s0 [s1 []]].
      cbn [child0Path readSubTreeState readSubTreeState_child Fst Snd writeSubTreeState writeSubTreeState_child].
      reflexivity.
    - cbn [genNthRegionAction regionStateAt updRegionStateAt envRegionAt].
      rewrite evalActionPropGen_liftAction.
      destruct s as [s0 [s1 []]].
      cbn [child1Path readSubTreeState readSubTreeState_child Fst Snd writeSubTreeState writeSubTreeState_child].
      apply IH.
  Qed.

  Lemma regionStateAt_updRegionStateAt :
    forall (idx : nat) (regions : list MemRegion) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) (s : RS regions) (v : RgS r0),
      regionStateAt idx regions r0 pf (updRegionStateAt idx regions r0 pf s v) = v.
  Proof.
    intros idx regions; revert idx.
    induction regions as [| r rs IH]; intros [| i'] r0 pf s v; try discriminate pf.
    - cbn [regionStateAt updRegionStateAt Fst].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq; reflexivity.
    - cbn [regionStateAt updRegionStateAt Fst Snd].
      apply IH.
  Qed.

  Lemma updRegionStateAt_regionStateAt :
    forall (idx : nat) (regions : list MemRegion) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) (s : RS regions),
      updRegionStateAt idx regions r0 pf s (regionStateAt idx regions r0 pf s) = s.
  Proof.
    intros idx regions; revert idx.
    induction regions as [| r rs IH]; intros [| i'] r0 pf s; try discriminate pf.
    - cbn [regionStateAt updRegionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      destruct s as [s0 [s1 []]]; reflexivity.
    - cbn [regionStateAt updRegionStateAt].
      destruct s as [s0 [s1 []]]; cbn [Fst Snd].
      rewrite IH; reflexivity.
  Qed.

  Lemma updRegionStateAt_updRegionStateAt :
    forall (idx : nat) (regions : list MemRegion) (r0 : MemRegion)
           (pf : nth_error regions idx = Some r0) (s : RS regions) (v1 v2 : RgS r0),
      updRegionStateAt idx regions r0 pf (updRegionStateAt idx regions r0 pf s v1) v2 =
      updRegionStateAt idx regions r0 pf s v2.
  Proof.
    intros idx regions; revert idx.
    induction regions as [| r rs IH]; intros [| i'] r0 pf s v1 v2; try discriminate pf.
    - cbn [updRegionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq; reflexivity.
    - cbn [updRegionStateAt Fst Snd].
      rewrite IH; reflexivity.
  Qed.

End RegionAt.

Arguments regionStateAt regionTree idx regions r0 pf s.
Arguments updRegionStateAt regionTree idx regions r0 pf s v.
Arguments envRegionAt regionTree idx regions r0 pf env s.
