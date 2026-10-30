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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * MEMORY PART OF THE REFINEMENT RELATION
 * ===========================================================================
 * The spec memory is over `specRegions = pre ++ specRev :: post`, the impl
 * memory over `implRegions = pre ++ implRev :: post` (RefRel.v).
 * 1. Ordinary positions are related by a fixpoint over the shared list
 *    structure, so no casts appear:
 *    - an ExternalMem region: the spec's writes are the writes the impl memory
 *      accepted, and the fence.i bookkeeping (fenceIWait, number of requests,
 *      number of acks) agrees;
 *    - a CustomMem region: equal states, except at the CLINT and PLIC positions
 *      (and the revoker position, which the fixpoint skips).
 * 2. The CLINT, the PLIC and the revoker are related through their instance
 *    positions (`regionStateAt` with the instance proofs), which is how their
 *    device steps see them:
 *    - CLINT: equal except `sampledMtip`, where the spec may lag (spec -> impl);
 *    - PLIC: equal except `meip`, where the spec may lag;
 *    - revoker: the spec's 7 registers are the projection of the impl's 11,
 *      except for `scanAddr` (`RevOff`). *)

Local Abbreviation TS t := (TreeState DomainElemState t).

(* --- 1. Ordinary Positions --- *)

Section RegionRel.
  Variable core : string.
  (* Positions handled through their instances *)
  Variables clintPos plicPos : nat.

  (* ExternalMem: spec part `x`, impl region `y` *)
  Definition ExtRel (r : MemRegion)
    (x : TS (externalMemRegionTree core r)) (y : TS (implExternalMemRegionTree core r)) : Prop :=
    x.(Snd).(Snd).(Snd).(Fst) = implAccWrites core r y /\
    x.(Fst).(Snd).(Snd).(Fst) = y.(Fst).(Fst).(Snd).(Snd).(Fst) /\
    length x.(Fst).(Snd).(Snd).(Snd).(Fst) = length y.(Fst).(Fst).(Snd).(Snd).(Snd).(Fst) /\
    count_true x.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) = count_true y.(Fst).(Fst).(Snd).(Snd).(Snd).(Snd).(Fst).

  Definition RegionRelAt (i : nat) (r : MemRegion)
    : TS (memRegionTree core r) -> TS (implMemRegionTree core r) -> Prop :=
    match r.(regionKind) as k
      return TS (memRegionKindTree core r k) -> TS (implMemRegionKindTree core r k) -> Prop
    with
    | ExternalMem => fun x y => ExtRel r x y
    | CustomMem _ _ _ _ => fun x y => i = clintPos \/ i = plicPos \/ x = y.(Fst)
    end.

  Fixpoint MemRelPost (i : nat) (l : list MemRegion)
    : TS (specMemTree core l) -> TS (implRegionsTree core l) -> Prop :=
    match l as l0 return TS (specMemTree core l0) -> TS (implRegionsTree core l0) -> Prop with
    | [] => fun _ _ => True
    | r :: l' => fun ms mi =>
        RegionRelAt i r ms.(Fst) mi.(Fst) /\ MemRelPost (S i) l' ms.(Snd).(Fst) mi.(Snd).(Fst)
    end.

  (* The position `length l` (the revoker) is skipped *)
  Fixpoint MemRelPre (i : nat) (l : list MemRegion) (sRev iRev : MemRegion) (post : list MemRegion)
    : TS (specMemTree core (l ++ sRev :: post)) -> TS (implRegionsTree core (l ++ iRev :: post)) -> Prop :=
    match l as l0
      return TS (specMemTree core (l0 ++ sRev :: post)) -> TS (implRegionsTree core (l0 ++ iRev :: post)) -> Prop
    with
    | [] => fun ms mi => MemRelPost (S i) post ms.(Snd).(Fst) mi.(Snd).(Fst)
    | r :: l' => fun ms mi =>
        RegionRelAt i r ms.(Fst) mi.(Fst) /\ MemRelPre (S i) l' sRev iRev post ms.(Snd).(Fst) mi.(Snd).(Fst)
    end.

End RegionRel.

(* --- 2. Special Regions --- *)

(* The impl revoker's scanAddr against the spec's: equal; one ahead while the revoker's write
 * waits in the memory; one behind from the device read of a cap (the spec has taken that
 * position's step) until the impl's WaitCapRp advances *)
Inductive RevOff := RevEq | RevImplAhead | RevSpecAhead.

Definition revOffAddr (o : RevOff) (sa : bits TagAddrWidth) : bits TagAddrWidth :=
  match o with
  | RevEq => sa
  | RevImplAhead => Zmod.add sa Zmod.one
  | RevSpecAhead => Zmod.sub sa Zmod.one
  end.

Section SpecialRegions.
  Variable core : string.

  (* CLINT: [ mtime; mtimecmp; mtip; sampledMtip ] *)
  Local Abbreviation ClintS := (TS (Node "clint" (clintChildren core))).

  Definition clintSampled (x : ClintS) : bool := x.(Snd).(Snd).(Snd).(Fst).
  Definition clintMtip (x : ClintS) : bool := x.(Snd).(Snd).(Fst).

  Definition clintWithSampled (b : bool) (x : ClintS) : ClintS :=
    (x.(Fst) ,, (x.(Snd).(Fst) ,, (x.(Snd).(Snd).(Fst) ,, (b ,, tt)))).

  Definition ClintRel (xs xi : ClintS) : Prop :=
    xs = clintWithSampled (clintSampled xs) xi /\
    (clintSampled xs = true -> clintSampled xi = true).

  (* Impl-only: a sampled MTIP is a pending MTIP *)
  Definition ClintInv (xi : ClintS) : Prop :=
    clintSampled xi = true -> clintMtip xi = true.

  (* PLIC: [ priorities; pending; enables; threshold; claim; meip; in_service; UartIrq ] *)
  Local Abbreviation PlicS n := (TS (plicTree core n)).

  Definition plicMeipOf {n} (x : PlicS n) : bool := x.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition plicClaimOf {n} (x : PlicS n) : bits Xlen := x.(Snd).(Snd).(Snd).(Snd).(Fst).

  Definition plicWithMeip {n} (b : bool) (x : PlicS n) : PlicS n :=
    (x.(Fst) ,, (x.(Snd).(Fst) ,, (x.(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Fst) ,,
     (x.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (b ,, x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))).

  Definition PlicRelSame (n : nat) (xs xi : PlicS n) : Prop :=
    xs = plicWithMeip (plicMeipOf xs) xi /\
    (plicMeipOf xs = true -> plicMeipOf xi = true).

  (* The spec and impl PLICs have the same number of sources, but the two numbers are
   * only propositionally equal (they count the irq actions of the two region lists) *)
  Definition PlicRel (n1 n2 : nat) (xs : PlicS n1) (xi : PlicS n2) : Prop :=
    exists e : n1 = n2, PlicRelSame n2 (eq_rect n1 (fun n => PlicS n) xs n2 e) xi.

  (* Impl-only: MEIP is only set while a claim is pending *)
  Definition PlicInv {n} (xi : PlicS n) : Prop :=
    plicMeipOf xi = true -> plicClaimOf xi <> Zmod.zero.

  (* Revoker: 7 architectural registers (spec) vs 7 + 4 (impl) *)
  Local Abbreviation RevS := (TS (Node "revoker" (revokerChildren core []))).
  Local Abbreviation RevI := (TS (implRevokerTree core)).

  Definition revScanAddr (x : RevS) : bits TagAddrWidth := x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

  Definition revWithScanAddr (a : bits TagAddrWidth) (x : RevS) : RevS :=
    (x.(Fst) ,, (x.(Snd).(Fst) ,, (x.(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Fst) ,,
     (x.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, (a ,, tt))))))).

  Definition RevRel (o : RevOff) (xs : RevS) (xi : RevI) : Prop :=
    projImplRevokerArchState core xi = revWithScanAddr (revOffAddr o (revScanAddr xs)) xs.

End SpecialRegions.

(* --- 3. The Memory Relation over the Two Region Lists --- *)

Section MemRelLists.
  Variable core : string.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf core pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf core pre post revBase revPfB revPfA).
  Local Abbreviation sRev := (specRevRegion core revBase revPfB revPfA).
  Local Abbreviation iRev := (implRevRegion core revBase revPfB revPfA).

  Variable clintS : @ClintInstance core specRegions.
  Variable clint : @ClintInstance core implRegions.
  Variable plicS : @PlicInstance core (S (S (length (collectIrqActions core specRegions)))) specRegions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions core implRegions)))) implRegions.

  Definition specClintState (ms : TS (specMemTree core specRegions)) : TS (Node "clint" (clintChildren core)) :=
    regionStateAt (memRegionTree core) clintS.(clintIdx) specRegions (clintRegion clintS) clintS.(pfClint) ms.

  Definition implClintState (mi : TS (implRegionsTree core implRegions)) : TS (Node "clint" (clintChildren core)) :=
    (regionStateAt (implMemRegionTree core) clint.(clintIdx) implRegions (clintRegion clint) clint.(pfClint) mi).(Fst).

  Definition specPlicState (ms : TS (specMemTree core specRegions))
    : TS (plicTree core (S (S (length (collectIrqActions core specRegions))))) :=
    regionStateAt (memRegionTree core) plicS.(plicIdx) specRegions (plicRegion plicS) plicS.(pfPlic) ms.

  Definition implPlicState (mi : TS (implRegionsTree core implRegions))
    : TS (plicTree core (S (S (length (collectIrqActions core implRegions))))) :=
    (regionStateAt (implMemRegionTree core) plic.(plicIdx) implRegions (plicRegion plic) plic.(pfPlic) mi).(Fst).

  Definition specRevState (ms : TS (specMemTree core specRegions)) : TS (Node "revoker" (revokerChildren core [])) :=
    regionStateAt (memRegionTree core) (length pre) specRegions sRev
      (nth_error_app_cons_len pre sRev post) ms.

  Definition implRevState (mi : TS (implRegionsTree core implRegions)) : TS (implRevokerTree core) :=
    (regionStateAt (implMemRegionTree core) (length pre) implRegions iRev
       (nth_error_app_cons_len pre iRev post) mi).(Fst).

  Definition MemRel (revOff : RevOff)
    (ms : TS (specMemTree core specRegions)) (mi : TS (implRegionsTree core implRegions)) : Prop :=
    MemRelPre core clintS.(clintIdx) plicS.(plicIdx) 0 pre sRev iRev post ms mi /\
    ClintRel core (specClintState ms) (implClintState mi) /\
    PlicRel core _ _ (specPlicState ms) (implPlicState mi) /\
    RevRel core revOff (specRevState ms) (implRevState mi).

  (* Impl-only facts about the devices *)
  Definition DevInv (mi : TS (implRegionsTree core implRegions)) : Prop :=
    ClintInv core (implClintState mi) /\ PlicInv core (implPlicState mi).

End MemRelLists.
