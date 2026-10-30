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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * FETCH RESPONSES THE SPEC MAY RECEIVE
 * ===========================================================================
 * An instruction the impl fetched must be re-fetchable by the spec when the spec
 * executes it (lockstep or ghost replay). The spec env (SimDevices.v section 6)
 * constrains each fetch response per ExternalMem region by the region's fence.i
 * snapshot and later writes (`EnvFetchLineReadRpAt`); a CustomMem fetch returns any
 * value. `LineAllowed m L rp` says that a spec fetch of line `L` on spec memory `m`
 * can return `rp`. It only depends on the ack traces and write traces of the
 * ExternalMem regions, and it stays true when writes are appended without a new
 * ack (`LineAllowed_fetchViewExt`). *)

Section LineAllowed.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Notation memRegionTree := (memRegionTree core).
  Local Notation memRegionKindTree := (memRegionKindTree core).
  Local Notation specMemTree := (specMemTree core).

  (* --- 1. Per-Region and Whole-Memory Predicates --- *)

  Definition RegionLineAllowed (r : MemRegion) (fwc : nat -> nat)
    : TreeState DomainElemState (memRegionTree r) -> bits AddrSz -> type LineReadRp -> Prop :=
    match r.(regionKind) as k
      return TreeState DomainElemState (memRegionKindTree r k) -> bits AddrSz -> type LineReadRp -> Prop
    with
    | ExternalMem => fun sr L rp =>
        EnvFetchLineReadRpAt (initLine r) fwc
          sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) sr.(Snd).(Snd).(Snd).(Fst) L rp
    | CustomMem _ _ _ _ => fun _ _ _ => True
    end.

  (* The router answers a line no region owns with the default response *)
  Fixpoint LineAllowed (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : TreeState DomainElemState (specMemTree regions) -> bits AddrSz -> type LineReadRp -> Prop :=
    match regions as rs
      return TreeState DomainElemState (specMemTree rs) -> bits AddrSz -> type LineReadRp -> Prop
    with
    | [] => fun _ _ rp => rp = getDefault LineReadRp
    | r :: rs => fun m L rp =>
        if evalExpr (isRegionAddr r (Var type Addr L))
        then RegionLineAllowed r (fwcs 0%nat) m.(Fst) L rp
        else LineAllowed (fun i => fwcs (S i)) rs m.(Snd).(Fst) L rp
    end.

  (* --- 2. The Fetch View: Ack Counts and Write Traces --- *)

  (* Region state `sr'` extends `sr` as far as fetches can tell: same ack count, and
   * the writes of `sr` with newer writes in front. *)
  Definition RegionFetchViewExt (r : MemRegion)
    : TreeState DomainElemState (memRegionTree r) -> TreeState DomainElemState (memRegionTree r) -> Prop :=
    match r.(regionKind) as k
      return TreeState DomainElemState (memRegionKindTree r k) ->
             TreeState DomainElemState (memRegionKindTree r k) -> Prop
    with
    | ExternalMem => fun sr sr' =>
        count_true sr'.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) =
          count_true sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst) /\
        exists ws_new, sr'.(Snd).(Snd).(Snd).(Fst) = (ws_new ++ sr.(Snd).(Snd).(Snd).(Fst))%list
    | CustomMem _ _ _ _ => fun _ _ => True
    end.

  Fixpoint FetchViewExt (regions : list MemRegion)
    : TreeState DomainElemState (specMemTree regions) ->
      TreeState DomainElemState (specMemTree regions) -> Prop :=
    match regions as rs
      return TreeState DomainElemState (specMemTree rs) ->
             TreeState DomainElemState (specMemTree rs) -> Prop
    with
    | [] => fun _ _ => True
    | r :: rs => fun m m' =>
        RegionFetchViewExt r m.(Fst) m'.(Fst) /\ FetchViewExt rs m.(Snd).(Fst) m'.(Snd).(Fst)
    end.

  (* The write count at the last ack never exceeds the current write count *)
  Definition RegionSnapshotOK (r : MemRegion) (fwc : nat -> nat)
    : TreeState DomainElemState (memRegionTree r) -> Prop :=
    match r.(regionKind) as k
      return TreeState DomainElemState (memRegionKindTree r k) -> Prop
    with
    | ExternalMem => fun sr =>
        (length sr.(Snd).(Snd).(Snd).(Fst) >=
         fenceISnapshotCount fwc sr.(Fst).(Snd).(Snd).(Snd).(Snd).(Fst))%nat
    | CustomMem _ _ _ _ => fun _ => True
    end.

  Fixpoint SnapshotOK (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : TreeState DomainElemState (specMemTree regions) -> Prop :=
    match regions as rs return TreeState DomainElemState (specMemTree rs) -> Prop with
    | [] => fun _ => True
    | r :: rs => fun m =>
        RegionSnapshotOK r (fwcs 0%nat) m.(Fst) /\ SnapshotOK (fun i => fwcs (S i)) rs m.(Snd).(Fst)
    end.

  (* --- 3. Monotonicity --- *)

  Lemma RegionLineAllowed_fetchViewExt :
    forall r fwc sr sr' L rp,
      RegionSnapshotOK r fwc sr ->
      RegionFetchViewExt r sr sr' ->
      RegionLineAllowed r fwc sr L rp ->
      RegionLineAllowed r fwc sr' L rp.
  Proof.
    intros r fwc.
    unfold RegionSnapshotOK, RegionFetchViewExt, RegionLineAllowed, memRegionTree.
    destruct (regionKind r); intros sr sr' L rp Hsnap Hext Hal; [| exact I].
    destruct Hext as [Hack [ws_new Hws]].
    exact (EnvFetchLineReadRpAt_prepend_stores (initLine r) fwc ws_new _ _ _ _ L rp
             Hsnap Hack Hws Hal).
  Qed.

  Lemma LineAllowed_fetchViewExt :
    forall regions fwcs m m' L rp,
      SnapshotOK fwcs regions m ->
      FetchViewExt regions m m' ->
      LineAllowed fwcs regions m L rp ->
      LineAllowed fwcs regions m' L rp.
  Proof.
    induction regions as [| r rs IH]; intros fwcs m m' L rp Hsnap Hext Hal; cbn [LineAllowed] in *.
    - exact Hal.
    - cbn [SnapshotOK FetchViewExt] in Hsnap, Hext.
      destruct Hsnap as [Hsnap0 Hsnap1], Hext as [Hext0 Hext1].
      destruct (evalExpr (isRegionAddr r (Var type Addr L))).
      + exact (RegionLineAllowed_fetchViewExt r (fwcs 0%nat) _ _ L rp Hsnap0 Hext0 Hal).
      + exact (IH (fun i => fwcs (S i)) _ _ L rp Hsnap1 Hext1 Hal).
  Qed.

  Lemma RegionFetchViewExt_refl :
    forall r sr, RegionFetchViewExt r sr sr.
  Proof.
    intros r; unfold RegionFetchViewExt, memRegionTree.
    destruct (regionKind r); intros sr; [| exact I].
    split; [reflexivity | exists []; reflexivity].
  Qed.

  Lemma FetchViewExt_refl :
    forall regions m, FetchViewExt regions m m.
  Proof.
    induction regions as [| r rs IH]; intros m; cbn [FetchViewExt]; [exact I |].
    split; [apply RegionFetchViewExt_refl | apply IH].
  Qed.

  Lemma RegionFetchViewExt_trans :
    forall r sr1 sr2 sr3,
      RegionFetchViewExt r sr1 sr2 -> RegionFetchViewExt r sr2 sr3 -> RegionFetchViewExt r sr1 sr3.
  Proof.
    intros r; unfold RegionFetchViewExt, memRegionTree.
    destruct (regionKind r); intros sr1 sr2 sr3 H12 H23; [| exact I].
    destruct H12 as [Ha12 [w12 Hw12]], H23 as [Ha23 [w23 Hw23]].
    split; [congruence |].
    exists (w23 ++ w12)%list; rewrite Hw23, Hw12, app_assoc; reflexivity.
  Qed.

  Lemma FetchViewExt_trans :
    forall regions m1 m2 m3,
      FetchViewExt regions m1 m2 -> FetchViewExt regions m2 m3 -> FetchViewExt regions m1 m3.
  Proof.
    induction regions as [| r rs IH]; intros m1 m2 m3 H12 H23; cbn [FetchViewExt] in *; [exact I |].
    destruct H12 as [H12a H12b], H23 as [H23a H23b].
    split; [exact (RegionFetchViewExt_trans r _ _ _ H12a H23a) | exact (IH _ _ _ H12b H23b)].
  Qed.

End LineAllowed.

(* ===========================================================================
 * INSTRUCTIONS THE SPEC MAY FETCH
 * ===========================================================================
 * `specFetchRd`, `specPreFault` and `specFetchOutOf` transcribe `specFetch` and
 * `specMemFetchRead` (SpecFetchDeferred.v, SpecDevice.v) with the two line responses
 * given. `FetchAllowedInst m pcc fo`: with PCC `pcc`, a spec fetch on memory `m` can
 * return `fo`. *)

Section FetchAllowedInst.
  Variable core : string.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Notation specMemTree := (specMemTree core).

  Definition instSzLg : type (Bit LgLgNumBytesFullCapSz) := evalExpr ($LgNumBytesInstSz : Expr type (Bit LgLgNumBytesFullCapSz)).

  (* The packet of `pc` in line response `rp` *)
  Definition specPkt (pc : type Addr) (rp : type LineReadRp) : type CapPacket :=
    evalLetExpr (memExtractCapPacket (Var type Addr pc) (Var type LineReadRp rp)).

  (* The 4-byte word read from packet `pkt` at `pc` *)
  Definition specWord (pc : type Addr) (pkt : type CapPacket) : type Inst :=
    let res : type FullCapWithTag :=
      evalLetExpr (memAssembleCapRead (Var type Addr pc) (Var type (Bit LgLgNumBytesFullCapSz) instSzLg)
                     (Var type CapPacket pkt)) in
    evalExpr (##res`"addr").

  (* Whether the instruction with raw low word `raw0` at `pc` fails the top check *)
  Definition specTopExc (pc : type Addr) (top : type (Bit (AddrSz + 2))) (raw0 : type Inst) : bool :=
    let isComp : bool := evalExpr (@isCompressed type raw0) in
    let instLgBytes : type (Bit LgLgNumBytesFullCapSz) :=
      evalExpr (ITE (Const type Bool isComp)
                    ($(Z.log2 (CompInstSz / 8)) : Expr type (Bit LgLgNumBytesFullCapSz))
                    $(Z.log2 (InstSz / 8))) in
    let instEnd : type (Bit (AddrSz + 2)) := evalLetExpr (@AdderAccessEnd type pc instLgBytes) in
    evalExpr (Ugt (Var type (Bit (AddrSz + 2)) instEnd) (Var type (Bit (AddrSz + 2)) top)).

  (* Whether the instruction (raw low word `raw0`) at `pc` spills into the next line *)
  Definition specCrosses (pc : type Addr) (raw0 : type Inst) : bool :=
    andb (negb (evalExpr (@isCompressed type raw0)))
         (evalExpr (memCrossesLine (Var type Addr pc) (Var type (Bit LgLgNumBytesFullCapSz) instSzLg))).

  (* `specMemFetchRead pc top` with line responses `rp0` (line of `pc`) and `rp1` (next
   * line, read only when the instruction crosses and passes the top check) *)
  Definition specFetchRd (pc : type Addr) (top : type (Bit (AddrSz + 2))) (rp0 rp1 : type LineReadRp)
    : type Inst * bool :=
    let pkt0 := specPkt pc rp0 in
    let raw0 := specWord pc pkt0 in
    let topExc := specTopExc pc top raw0 in
    let crosses := specCrosses pc raw0 in
    let pkt1 := if andb crosses (negb topExc) then specPkt pc rp1 else getDefault CapPacket in
    let pkt : type CapPacket :=
      if crosses
      then evalExpr (memMergeCapPacket (Var type Addr pc) (Var type CapPacket pkt0) (Var type CapPacket pkt1))
      else pkt0 in
    (specWord pc pkt, topExc).

  Definition specPreFault (pcc : type FullECapWithTag) : bool :=
    let pccAddr : type Addr := evalExpr (##pcc`"addr") in
    let pccECap : type ECap := evalExpr (##pcc`"ecap") in
    evalExpr (Or [ Not (##pcc`"tag") ;
                   @isSealed type pccECap ;
                   Not (##pccECap`"perms"`"EX") ;
                   Ult (ZeroExtendTo (AddrSz + 1) (##pccAddr)) (##pccECap`"base") ]).

  Definition pccTopOf (pcc : type FullECapWithTag) : type (Bit (AddrSz + 2)) :=
    let pccECap : type ECap := evalExpr (##pcc`"ecap") in
    evalExpr (##pccECap`"top").

  (* The fetch output for PCC `pcc`, expanded instruction `expInst` and top fault `topExc` *)
  Definition specFetchOutOf (pcc : type FullECapWithTag) (expInst : type Inst) (topExc : bool) : type FetchOut :=
    let pccAddr : type Addr := evalExpr (##pcc`"addr") in
    let pccECap : type ECap := evalExpr (##pcc`"ecap") in
    let tagExc : bool := evalExpr (Not (##pcc`"tag")) in
    let sealExc : bool := evalExpr (@isSealed type pccECap) in
    let permExc : bool := evalExpr (Not (##pccECap`"perms"`"EX")) in
    let baseBndsExc : bool := evalExpr (Ult (ZeroExtendTo (AddrSz + 1) (##pccAddr)) (##pccECap`"base")) in
    let boundsExc : bool := orb baseBndsExc topExc in
    (evalExpr (##pccECap`"perms"`"SR") ,, (expInst ,, ((tagExc ,, (sealExc ,, (permExc ,, (boundsExc ,, tt)))) ,, tt))).

  (* A pre-faulted instruction reads as 0, a compressed (2-byte) instruction *)
  Definition specPreFaultTopExc (pcc : type FullECapWithTag) : bool :=
    let pccAddr : type Addr := evalExpr (##pcc`"addr") in
    let compLgBytes : type (Bit LgLgNumBytesFullCapSz) :=
      evalExpr ($(Z.log2 (CompInstSz / 8)) : Expr type (Bit LgLgNumBytesFullCapSz)) in
    let instEnd0 : type (Bit (AddrSz + 2)) := evalLetExpr (@AdderAccessEnd type pccAddr compLgBytes) in
    evalExpr (Ugt (Var type (Bit (AddrSz + 2)) instEnd0) (Var type (Bit (AddrSz + 2)) (pccTopOf pcc))).

  Definition FetchAllowedInst (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    (m : TreeState DomainElemState (specMemTree regions))
    (pcc : type FullECapWithTag) (fo : type FetchOut) : Prop :=
    let pc : type Addr := evalExpr (##pcc`"addr") in
    let top := pccTopOf pcc in
    if specPreFault pcc
    then fo = specFetchOutOf pcc Zmod.zero (specPreFaultTopExc pcc)
    else exists rp0 rp1,
      LineAllowed core initLine fwcs regions m (evalExpr (memLineAddr (Var type Addr pc))) rp0 /\
      (let raw0 := specWord pc (specPkt pc rp0) in
       andb (specCrosses pc raw0) (negb (specTopExc pc top raw0)) = true ->
       LineAllowed core initLine fwcs regions m (evalExpr (memNextLineAddr (Var type Addr pc))) rp1) /\
      fo = specFetchOutOf pcc (evalLetExpr (@preDecode type (fst (specFetchRd pc top rp0 rp1))))
                          (snd (specFetchRd pc top rp0 rp1)).

  Lemma FetchAllowedInst_fetchViewExt :
    forall fwcs regions m m' pcc fo,
      SnapshotOK core fwcs regions m ->
      FetchViewExt core regions m m' ->
      FetchAllowedInst fwcs regions m pcc fo ->
      FetchAllowedInst fwcs regions m' pcc fo.
  Proof.
    intros fwcs regions m m' pcc fo Hsnap Hext Hal.
    unfold FetchAllowedInst in *.
    destruct (specPreFault pcc); [exact Hal |].
    destruct Hal as [rp0 [rp1 [H0 [H1 Hfo]]]].
    exists rp0, rp1; split; [| split; [| exact Hfo]].
    - exact (LineAllowed_fetchViewExt core initLine regions fwcs m m' _ rp0 Hsnap Hext H0).
    - intros Hc; exact (LineAllowed_fetchViewExt core initLine regions fwcs m m' _ rp1 Hsnap Hext (H1 Hc)).
  Qed.

End FetchAllowedInst.
