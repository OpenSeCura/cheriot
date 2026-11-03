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
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variable regions : list MemRegion.

  Local Abbreviation sTree := (@specSysTree pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions).

  Definition specRf (s : TreeState ElemState sTree)
    : TreeState ElemState (rfTree pcAddrInit) :=
    Fst (Fst (Fst s)).

  Definition specMem (s : TreeState ElemState sTree)
    : TreeState ElemState (specMemTree regions) :=
    Fst (Fst (Snd (Fst s))).

  Definition implCore (s : TreeState ElemState iTree)
    : TreeState ElemState
        (coreTree (rfTree pcAddrInit) (withInst_BpTree bp) (implMemTree regions)
                  (implFetchTree pcAddrInit fetchCapacity instCapacity)
                  (implDecodeTree decodeCapacity)
                  implExecuteTree
                  (implDataMemTree dataMemCapacity)
                  (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)) :=
    Fst s.

  Definition implRf (s : TreeState ElemState iTree)
    : TreeState ElemState (rfTree pcAddrInit) :=
    Fst (Fst (Fst s)).

  Definition implWaitBits (s : TreeState ElemState iTree)
    : TreeState ElemState waitBitsTree :=
    Fst (Fst (Snd (Fst s))).

  Definition implBp (s : TreeState ElemState iTree)
    : TreeState ElemState (withInst_BpTree bp) :=
    Fst (Fst (Snd (Snd (Fst s)))).

  Definition implMem (s : TreeState ElemState iTree)
    : TreeState ElemState (implMemTree regions) :=
    Fst (Fst (Snd (Snd (Snd (Fst s))))).

  Definition implFetch (s : TreeState ElemState iTree)
    : TreeState ElemState (implFetchTree pcAddrInit fetchCapacity instCapacity) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Fst s)))))).

  Definition implDecode (s : TreeState ElemState iTree)
    : TreeState ElemState (implDecodeTree decodeCapacity) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Fst s))))))).

  Definition implExecute (s : TreeState ElemState iTree)
    : TreeState ElemState implExecuteTree :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Snd (Fst s)))))))).

  Definition implDataMem (s : TreeState ElemState iTree)
    : TreeState ElemState (implDataMemTree dataMemCapacity) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Snd (Snd (Fst s))))))))).

  Definition implMulDiv (s : TreeState ElemState iTree)
    : TreeState ElemState (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode) :=
    Fst (Fst (Snd (Snd (Snd (Snd (Snd (Snd (Snd (Snd (Fst s)))))))))).

  Lemma readSubTreeState_spec_np_rf :
    forall (s : TreeState ElemState sTree),
      readSubTreeState (@Spec.np_rf pcAddrInit regions) s = specRf s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_spec_np_mem :
    forall (s : TreeState ElemState sTree),
      readSubTreeState (@Spec.np_mem pcAddrInit regions) s = specMem s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_core :
    forall (s : TreeState ElemState iTree),
      readSubTreeState (@Impl.np_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions) s = implCore s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_rf :
    forall (s : TreeState ElemState iTree),
      readSubTreeState (@Impl.np_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions) s = implRf s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_mem :
    forall (s : TreeState ElemState iTree),
      readSubTreeState (@Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions) s = implMem s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_fetch :
    forall (s : TreeState ElemState iTree),
      readSubTreeState (@Impl.np_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions) s = implFetch s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_decode :
    forall (s : TreeState ElemState iTree),
      readSubTreeState (@Impl.np_decode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions) s = implDecode s.
  Proof.
    intros s; reflexivity.
  Qed.

  Lemma readSubTreeState_impl_np_execute :
    forall (s : TreeState ElemState iTree),
      readSubTreeState (@Impl.np_execute pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions) s = implExecute s.
  Proof.
    intros s; reflexivity.
  Qed.

End SubtreeAccessors.

Arguments specRf {pcAddrInit regions} s.
Arguments specMem {pcAddrInit regions} s.
Arguments implCore {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implRf {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implWaitBits {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implBp {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implMem {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implFetch {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implDecode {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implExecute {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implDataMem {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments implMulDiv {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments readSubTreeState_spec_np_rf {pcAddrInit regions} s.
Arguments readSubTreeState_spec_np_mem {pcAddrInit regions} s.
Arguments readSubTreeState_impl_np_core {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments readSubTreeState_impl_np_rf {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments readSubTreeState_impl_np_mem {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments readSubTreeState_impl_np_fetch {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments readSubTreeState_impl_np_decode {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.
Arguments readSubTreeState_impl_np_execute {pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions} s.

(* ===========================================================================
 * 2. MEMORY REGION PROJECTION (`projImplRegionSpecState` / `projImplMemSpecState`)
 * =========================================================================== *)

Section MemProjection.

  Definition implRegionExtraChildren (r : MemRegion) : list (Tree Elem) :=
    implMemRegionExtraChildren r r.(regionKind).

  Definition projImplRegionSpecState (r : MemRegion)
    (s : TreeState ElemState (implMemRegionTree r))
    : TreeState ElemState (memRegionTree r) :=
    Fst s.

  Definition projImplRegionExtraState (r : MemRegion)
    (s : TreeState ElemState (implMemRegionTree r))
    : TreeState ElemState (Node "" (implRegionExtraChildren r)) :=
    Snd s.

  Definition writeImplRegionSpecState (r : MemRegion)
    (s : TreeState ElemState (implMemRegionTree r))
    (m : TreeState ElemState (memRegionTree r))
    : TreeState ElemState (implMemRegionTree r) :=
    (m ,, Snd s).

  Lemma projImplRegionSpecState_writeImplRegionSpecState :
    forall (r : MemRegion)
           (s : TreeState ElemState (implMemRegionTree r))
           (m : TreeState ElemState (memRegionTree r)),
      projImplRegionSpecState r (writeImplRegionSpecState r s m) = m.
  Proof.
    intros r s m; reflexivity.
  Qed.

  Lemma projImplRegionExtraState_writeImplRegionSpecState :
    forall (r : MemRegion)
           (s : TreeState ElemState (implMemRegionTree r))
           (m : TreeState ElemState (memRegionTree r)),
      projImplRegionExtraState r (writeImplRegionSpecState r s m) =
      projImplRegionExtraState r s.
  Proof.
    intros r s m; reflexivity.
  Qed.

  Definition subEnvImplRegion (r : MemRegion)
    (env : Env (implMemRegionTree r))
    (s : TreeState ElemState (implMemRegionTree r))
    : Env (memRegionTree r) :=
    subEnv child0Path env s.

  Lemma evalActionPropGen_liftToImplRegion :
    forall (r : MemRegion) {k : Kind}
           {env : Env (implMemRegionTree r)}
           (act : Action type (memRegionTree r) k)
           (s : TreeState ElemState (implMemRegionTree r))
           (P : TreeState ElemState (implMemRegionTree r) -> type k -> Prop),
      evalActionPropGen env (liftToImplRegion act) s P <->
      evalActionPropGen (subEnvImplRegion r env s) act (projImplRegionSpecState r s)
        (fun m' v => P (writeImplRegionSpecState r s m') v).
  Proof.
    intros r k env act s P.
    exact (evalActionPropGen_liftAction child0Path act s P).
  Qed.

  Fixpoint projImplRegionsSpecState (regions : list MemRegion)
    : TreeState ElemState (implRegionsTree regions) ->
      TreeState ElemState (specMemTree regions) :=
    match regions return TreeState ElemState (implRegionsTree regions) ->
                         TreeState ElemState (specMemTree regions) with
    | [] => fun _ => tt
    | r :: rs => fun s =>
        (projImplRegionSpecState r (Fst s) ,,
         (projImplRegionsSpecState rs (Fst (Snd s)) ,, tt))
    end.

  Definition projImplMemSpecState (regions : list MemRegion)
    (s : TreeState ElemState (implMemTree regions))
    : TreeState ElemState (specMemTree regions) :=
    projImplRegionsSpecState regions (Fst s).

End MemProjection.

Arguments projImplRegionSpecState_writeImplRegionSpecState r s m : assert.
Arguments projImplRegionExtraState_writeImplRegionSpecState r s m : assert.
Arguments evalActionPropGen_liftToImplRegion r {k env} act s P.

(* ===========================================================================
 * 3. `incrementMcycle` AND `implTickCycle` / `specTickCycle` SIMULATION
 * =========================================================================== *)

Section TickCycleSim.
  Variable pcAddrInit : Z.

  Definition evalIncrementMcycle
    (rf : TreeState ElemState (rfTree pcAddrInit))
    : TreeState ElemState (rfTree pcAddrInit) :=
    let lowIdx  := evalExpr ($(getCsrPhysicalIdx "mcycle") : Expr type (Bit CsrIdxSz)) in
    let highIdx := evalExpr ($(getCsrPhysicalIdx "mcycleh") : Expr type (Bit CsrIdxSz)) in
    let currLow  := readCsr pcAddrInit lowIdx rf in
    let currHigh := readCsr pcAddrInit highIdx rf in
    let newVal   := evalExpr (Add [ {< #currHigh, #currLow >} ; $1 ] : Expr type (Bit DXlen)) in
    let rf1 := updCsr pcAddrInit lowIdx
                 (evalExpr (TruncLsb Xlen Xlen #newVal : Expr type (Bit Xlen))) rf in
    updCsr pcAddrInit highIdx
      (evalExpr (TruncMsb Xlen Xlen #newVal : Expr type (Bit Xlen))) rf1.

  Lemma evalActionPropGen_incrementMcycle :
    forall {env : Env (rfTree pcAddrInit)}
           (rf : TreeState ElemState (rfTree pcAddrInit)) P,
      evalActionPropGen env (@incrementMcycle pcAddrInit type) rf P <->
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
    forall {env : Env (rfTree pcAddrInit)}
           (rf rf' : TreeState ElemState (rfTree pcAddrInit)) v,
      SemAction env (@incrementMcycle pcAddrInit type) rf rf' v <->
      rf' = evalIncrementMcycle rf /\ v = Zmod.zero.
  Proof.
    intros env rf rf' v.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_incrementMcycle.
    split; intros [? ?]; subst; auto.
  Qed.

  Theorem evalIncrementMcycle_updGpr_comm :
    forall idx val rf,
      evalIncrementMcycle (updGpr pcAddrInit idx val rf) =
      updGpr pcAddrInit idx val (evalIncrementMcycle rf).
  Proof.
    intros idx val rf.
    unfold evalIncrementMcycle.
    rewrite !readCsr_updGpr, !updGpr_updCsr_comm.
    reflexivity.
  Qed.

  Theorem readGpr_evalIncrementMcycle :
    forall idx rf,
      readGpr pcAddrInit idx (evalIncrementMcycle rf) =
      readGpr pcAddrInit idx rf.
  Proof.
    intros idx rf; unfold evalIncrementMcycle; rewrite !readGpr_updCsr; reflexivity.
  Qed.

End TickCycleSim.

(* ===========================================================================
 * 4. CLINT, PLIC, FENCE.I ACK, AND CAN-PROCEED STAGE SIMULATIONS
 * =========================================================================== *)

Section SystemDevicesSim.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : @ClintInstance regions.
  Variable rev : @RevokerInstance implRevokerExtraChildren regions.
  Variable revSpec : @RevokerInstance [] regions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (@specSysTree pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions).
  Local Abbreviation specMod := (@spec pcAddrInit config regions clint revSpec plic).

  (* --- 4A. Helper for lifting any mem-tree simulation to `iTree` / `sTree` --- *)

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

  (* --- 4B. `implTickCycle` -> `specTickCycle` --- *)

  Lemma In_specTickCycle_spec :
    In (@specTickCycle pcAddrInit regions type)
       (specMod type).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; left; reflexivity.
  Qed.

  (* --- 4C. `implTickTimer` and `implSampleMtipStep` (CLINT) --- *)

  Lemma In_specTickTimer_spec :
    In (@specTickTimer pcAddrInit regions clint type)
       (specMod type).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; right; left; reflexivity.
  Qed.

  Lemma In_specSampleMtipStep_spec :
    In (@specSampleMtipStep pcAddrInit regions clint type)
       (specMod type).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; right; right; right; left; reflexivity.
  Qed.

  (* --- 4D. PLIC Steps (`implPlicClaimStep`, `implPlicSampleMeipStep`, `implPlicPendingsSteps`) --- *)

  Lemma In_specPlicClaimStep_spec :
    In (@specPlicClaimStep pcAddrInit regions plic type)
       (specMod type).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; left; reflexivity.
  Qed.

  Lemma In_specPlicSampleMeipStep_spec :
    In (@specPlicSampleMeipStep pcAddrInit regions plic type)
       (specMod type).
  Proof.
    rewrite map_snd_specMod.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn [In]; right; left; reflexivity.
  Qed.

End SystemDevicesSim.

(* ===========================================================================
 * 5. CONCRETE `ExternalMem` ENVIRONMENT (`Env`) & HANDSHAKE INVARIANTS
 * =========================================================================== *)

Section ExternalMemEnvAndHandshake.

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

  Lemma EnvDataLineReadRpAt_inhabited :
    forall (initLine : bits AddrSz -> type LineReadRp)
           (writes : list (type LineWriteRq))
           (lineAddr : bits AddrSz),
      exists rp, EnvDataLineReadRpAt initLine writes lineAddr rp.
  Proof.
    intros initLine writes lineAddr.
    eexists; reflexivity.
  Qed.

  (* --- 5C. `fence.i` Request/Ack Counting (`count_true`, `RegionFenceICountInv`) --- *)

  Fixpoint count_true (l : list bool) : nat :=
    match l with
    | [] => 0%nat
    | true :: tl => S (count_true tl)
    | false :: tl => count_true tl
    end.

  Definition RegionFenceICountInv (r : MemRegion)
    (sr : TreeState ElemState (externalMemRegionTree r)) : Prop :=
    let sf         := sr.(Fst) in
    let fenceIWait := sf.(Snd).(Snd).(Fst) in
    let fenceIRq   := sf.(Snd).(Snd).(Snd).(Fst) in
    let fenceIAck  := sf.(Snd).(Snd).(Snd).(Snd).(Fst) in
    if fenceIWait then
      length fenceIRq = S (count_true fenceIAck)
    else
      length fenceIRq = count_true fenceIAck.

  Lemma InitStateConsistent_RegionFenceICountInv :
    forall (r : MemRegion)
           (sr : TreeState ElemState (externalMemRegionTree r)),
      InitStateConsistent (externalMemRegionTree r) sr ->
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

  Lemma EnvFenceIAckAt_inhabited :
    forall (fenceIWriteCount : nat -> nat) (nFenceIRq : nat) (fenceIAck : list bool) (nWrites : nat),
      exists ack, EnvFenceIAckAt fenceIWriteCount nFenceIRq fenceIAck nWrites ack.
  Proof.
    intros fenceIWriteCount nFenceIRq fenceIAck nWrites.
    exists false; intros H; discriminate H.
  Qed.

  Definition isSuffix {A : Type} (sub full : list A) : Prop :=
    exists pref, full = (pref ++ sub)%list.

  (* The 16-bit instruction parcel `p` of a line response: data bytes `2p` and `2p+1`. *)
  Definition rpParcel (rp : type LineReadRp) (p : nat) : list (bits 8) :=
    firstn 2 (skipn (2 * p) rp.(Fst).(tupleElems)).

  (* Data byte `i` of a line response (empty past the end of the line). *)
  Definition rpByte (rp : type LineReadRp) (i : nat) : list (bits 8) :=
    firstn 1 (skipn i rp.(Fst).(tupleElems)).

  (* Post-`fence.iAck` fetch constraint for a response to the request for `lineAddr`,
   * per data byte (`fenceIAck` and `writes` are newest first):
   * - `n_at := fenceISnapshotCount fenceIWriteCount fenceIAck` is the write count at the
   *   last `fence.iAck` (0 before any ack: the initial memory).
   * - `writes_after := firstn (length writes - n_at) writes` is the prefix of `writes` that
   *   occurred after the last `fence.iAck`.
   * - `writes_at_fenceI := skipn (length writes - n_at) writes` is the history of writes up
   *   to the last `fence.iAck`.
   * - `baseLine` evaluates the committed state at `fence.iAck` (where all older stores to
   *   an address prior to the last store at `fence.iAck` are overwritten and irrelevant).
   * - Each byte of `rp` independently comes from some allowed version: `baseLine` plus
   *   an oldest-first prefix `ws_used` of `writes_after`, chosen per byte. So a byte is
   *   its value at the last ack or the value of some later write covering it.
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
    forall i : nat,
      exists ws_used,
        isSuffix ws_used writes_after /\
        rpByte rp i =
          rpByte (evalLineWriteRqTrace (fun _ => baseLine) ws_used lineAddr) i.

  (* The spec answers each fetch request in the same action, so its response is for the
   * newest request, `hd fetchRqs`. *)

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
    eexists; intros i; exists []; split.
    - exists (firstn (length writes - fenceISnapshotCount fenceIWriteCount fenceIAck) writes).
      rewrite app_nil_r; reflexivity.
    - reflexivity.
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
    intros i; destruct (Henv1 i) as [ws_used [[pref Hpref] Hrp]].
    exists ws_used; split; [| exact Hrp].
    exists (ws_new ++ pref)%list.
    rewrite <- app_assoc, <- Hpref; reflexivity.
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
    (ir : TreeState ElemState (implExternalMemRegionTree r)) : list (bits AddrSz) :=
    acceptedOf ir.(Fst).(Fst).(Fst) ir.(Snd).(Fst).(Fst).

  Definition implFetchLineAddr (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r)) : bits AddrSz :=
    fifoRq Zmod.zero (implFetchAccRqs r ir) (length ir.(Fst).(Fst).(Snd).(Fst)).

  Definition EnvFetchLineReadRpValidConstraint (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r))
    (valid : bool) : Prop :=
    let sr := ir.(Fst) in
    let fetch_lineReadRp := sr.(Fst).(Snd).(Fst) in
    valid = true -> (length (implFetchAccRqs r ir) > length fetch_lineReadRp)%nat.

  (* Data requests and writes are sent by the port actions together with the receive of
   * `lineReadRqReady` / `lineWriteRqReady`; only accepted ones reach the memory. *)
  Definition implDataAccRqs (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r)) : list (bits AddrSz) :=
    acceptedOf ir.(Fst).(Snd).(Fst) ir.(Snd).(Snd).(Fst).

  Definition implAccWrites (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r))
    : list (type LineWriteRq) :=
    acceptedOf ir.(Fst).(Snd).(Snd).(Snd).(Fst) ir.(Snd).(Snd).(Snd).(Fst).

  Definition implDataLineAddr (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r)) : bits AddrSz :=
    fifoRq Zmod.zero (implDataAccRqs r ir) (length ir.(Fst).(Snd).(Snd).(Fst)).

  Definition EnvDataLineReadRpValidConstraint (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r))
    (valid : bool) : Prop :=
    let sr := ir.(Fst) in
    let data_lineReadRp := sr.(Snd).(Snd).(Fst) in
    valid = true -> (length (implDataAccRqs r ir) > length data_lineReadRp)%nat.

  Lemma EnvFetchLineReadRpValidConstraint_inhabited :
    forall (r : MemRegion) (ir : TreeState ElemState (implExternalMemRegionTree r)),
      exists valid, EnvFetchLineReadRpValidConstraint r ir valid.
  Proof.
    intros r ir; exists false; intros H; discriminate H.
  Qed.

  Lemma EnvDataLineReadRpValidConstraint_inhabited :
    forall (r : MemRegion) (ir : TreeState ElemState (implExternalMemRegionTree r)),
      exists valid, EnvDataLineReadRpValidConstraint r ir valid.
  Proof.
    intros r ir; exists false; intros H; discriminate H.
  Qed.

  (* Ready/valid bookkeeping of an impl ExternalMem region. Data responses leave the region
   * as soon as they are received (into the memory's single data response buffer), so only
   * the fetch side keeps a response here. *)
  Definition ImplExternalRegionHandshakeInv (r : MemRegion)
    (ir : TreeState ElemState (implExternalMemRegionTree r)) : Prop :=
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
           (ir : TreeState ElemState (implExternalMemRegionTree r)),
      InitStateConsistent (implExternalMemRegionTree r) ir ->
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

  Definition pExtFetchFenceIAck : RecvPath externalMemFetchTree :=
    Eval cbn in (getChildRecvPathTree externalMemFetchTree "fenceIAck").

  Opaque liftAction.

  (* The data response port receives the response of the outstanding line read, if it has
   * arrived, and returns it to the memory. *)

  Transparent liftAction.

  (* The staging and port actions below only move requests between `portRq` and the
   * region's spec-part request traces, and the invariant mentions none of those values.
   * So the proofs keep `evalExpr` opaque and case on the `if` guards as opaque booleans:
   * no request value is evaluated. *)

End ExternalMemEnvAndHandshake.

(* --- 6A. Env Combinators (`EnvCtx`, `envCtxCons`, `envNodeCons`) --- *)

Section EnvCombinators.
  (* An env fragment for subtree `t` whose leaf constraints read a context `S`
   * (e.g. the state of the enclosing memory region).
   * `Env t` is definitionally `EnvCtx (TreeState ElemState t) t`. *)
  Definition EnvCtx (S : Type) (t : Tree Elem) : Type :=
    S -> forall x : RecvPath t, type (getRecvKind x) -> Prop.

  Definition envCtxTrue {S : Type} {t : Tree Elem} : EnvCtx S t :=
    fun _ _ _ => True.

  Definition envCtxLeaf {S : Type} {name : string} {k : Kind}
    (P : S -> type k -> Prop) : EnvCtx S (Leaf name (ERecv k)) :=
    fun s _ v => P s v.

  Definition envCtxMap {S S' : Type} {t : Tree Elem}
    (f : S -> S') (e : EnvCtx S' t) : EnvCtx S t :=
    fun s => e (f s).

  (* Context-sharing cons: dispatch on the first step of the receive path. *)
  Definition envCtxCons {S : Type} {name : string}
    {c : Tree Elem} {cs : list (Tree Elem)}
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
    {c : Tree Elem} {cs : list (Tree Elem)}
    (e0 : Env c) (er : Env (Node name cs)) : Env (Node name (c :: cs)) :=
    envCtxCons
      (envCtxMap (fun s : TreeState ElemState (Node name (c :: cs)) => s.(Fst)) e0)
      (envCtxMap (fun s : TreeState ElemState (Node name (c :: cs)) => s.(Snd)) er).

  Definition EnvCtxInhabited {S : Type} {t : Tree Elem} (e : EnvCtx S t) : Prop :=
    forall s x, exists v, e s x v.

  Lemma envCtxTrue_inhabited :
    forall (S : Type) (t : Tree Elem), EnvCtxInhabited (@envCtxTrue S t).
  Proof.
    intros S t s x; exists (getDefault _); exact I.
  Qed.

  Lemma envCtxLeaf_inhabited :
    forall (S : Type) (name : string) (k : Kind) (P : S -> type k -> Prop),
      (forall s, exists v, P s v) ->
      EnvCtxInhabited (@envCtxLeaf S name k P).
  Proof.
    intros S name k P HP s x; exact (HP s).
  Qed.

  Lemma envCtxMap_inhabited :
    forall (S S' : Type) (t : Tree Elem) (f : S -> S') (e : EnvCtx S' t),
      EnvCtxInhabited e -> EnvCtxInhabited (envCtxMap f e).
  Proof.
    intros S S' t f e He s x; exact (He (f s) x).
  Qed.

  Lemma envCtxCons_inhabited :
    forall (S : Type) (name : string) (c : Tree Elem) (cs : list (Tree Elem))
           (e0 : EnvCtx S c) (er : EnvCtx S (Node name cs)),
      EnvCtxInhabited e0 -> EnvCtxInhabited er -> EnvCtxInhabited (envCtxCons e0 er).
  Proof.
    intros S name c cs e0 er H0 Hr s [rp pf].
    destruct rp as [p | q].
    - exact (H0 s (@Build_RecvPath c p pf)).
    - exact (Hr s (@Build_RecvPath (Node name cs) q pf)).
  Qed.

  Lemma envNodeCons_inhabited :
    forall (name : string) (c : Tree Elem) (cs : list (Tree Elem))
           (e0 : Env c) (er : Env (Node name cs)),
      EnvCtxInhabited e0 -> EnvCtxInhabited er -> EnvCtxInhabited (envNodeCons e0 er).
  Proof.
    intros name c cs e0 er H0 Hr.
    apply envCtxCons_inhabited; apply envCtxMap_inhabited; assumption.
  Qed.
End EnvCombinators.

(* --- 6B. Region Envs (`specRegionsEnv`, `implMemEnv`) --- *)

Section RegionEnvs.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  (* `fwc` is the region's own `fenceIWriteCount` oracle (ack index -> write count).
   * The external-memory envs read a context `S` (the receiving side's region state):
   * `getSr` gives the region's spec-part traces, `writesOf` the writes the memory has
   * accepted (newest first), and `fetchAddr` / `dataAddr` the lines the next fetch and
   * data responses are for. *)

  (* `externalMemFetchTree`: [ lineReadRq; lineReadRp; fenceIWait; fenceIRq; fenceIAck ] *)
  Definition extFetchEnvCtx {S : Type} (r : MemRegion) (fwc : nat -> nat)
    (getSr : S -> TreeState ElemState (externalMemRegionTree r))
    (writesOf : S -> list (type LineWriteRq))
    (fetchAddr : S -> bits AddrSz)
    : EnvCtx S externalMemFetchTree :=
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
    (getSr : S -> TreeState ElemState (externalMemRegionTree r))
    (writesOf : S -> list (type LineWriteRq))
    (fetchAddr dataAddr : S -> bits AddrSz)
    : EnvCtx S (externalMemRegionTree r) :=
    envCtxCons (extFetchEnvCtx r fwc getSr writesOf fetchAddr)
     (envCtxCons envCtxTrue
      (envCtxCons (envCtxLeaf (k := LineReadRp) (fun s rp =>
                     EnvDataLineReadRpAt (initLine r) (writesOf s) (dataAddr s) rp))
       (envCtxCons envCtxTrue envCtxTrue))).

  (* The spec answers each request in the same action (the newest request), after all
   * of its writes. *)
  Definition specExtRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (externalMemRegionTree r) :=
    extRegionEnvCtx r fwc (fun sr => sr) (fun sr => sr.(Snd).(Snd).(Snd).(Fst))
      (fun sr => hd Zmod.zero sr.(Fst).(Fst)) (fun sr => hd Zmod.zero sr.(Snd).(Fst)).

  (* `implExternalMemFetchTree`: [ lineReadRqReady; lineReadRpValid; lineReadRpReady; readRp ] *)
  Definition implExtFetchEnv (r : MemRegion)
    : EnvCtx (TreeState ElemState (implExternalMemRegionTree r)) implExternalMemFetchTree :=
    envCtxCons envCtxTrue
     (envCtxCons (envCtxLeaf (k := Bool) (fun ir valid =>
                    EnvFetchLineReadRpValidConstraint r ir valid))
      envCtxTrue).

  (* `implExternalMemRegionTree`:
   *   [ externalMemRegionTree; fetch; lineReadRqReady; lineWriteRqReady;
   *     lineReadRpValid; lineReadRpReady; portRq ]
   * The impl memory sees only accepted writes, and answers accepted requests in order
   * (`implFetchLineAddr`, `implDataLineAddr`). *)
  Definition implExtRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (implExternalMemRegionTree r) :=
    envCtxCons
      (extRegionEnvCtx r fwc
         (fun ir : TreeState ElemState (implExternalMemRegionTree r) => ir.(Fst))
         (implAccWrites r) (implFetchLineAddr r) (implDataLineAddr r))
      (envCtxCons (implExtFetchEnv r)
       (envCtxCons envCtxTrue
        (envCtxCons envCtxTrue
         (envCtxCons (envCtxLeaf (k := Bool) (fun ir valid =>
                        EnvDataLineReadRpValidConstraint r ir valid))
          envCtxTrue)))).

  Definition specRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (memRegionTree r) :=
    match r.(regionKind) as k return Env (memRegionKindTree r k) with
    | ExternalMem => specExtRegionEnv r fwc
    | CustomMem _ _ _ _ => envCtxTrue
    end.

  Definition implRegionEnv (r : MemRegion) (fwc : nat -> nat) : Env (implMemRegionTree r) :=
    match r.(regionKind) as k return Env (implMemRegionKindTree r k) with
    | ExternalMem => implExtRegionEnv r fwc
    | CustomMem _ _ _ _ => envCtxTrue
    end.

  (* `fwcs i` is the oracle of the region at position `i` of the list. *)
  Fixpoint specRegionsEnv (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : Env (specMemTree regions) :=
    match regions as rs return Env (specMemTree rs) with
    | [] => envCtxTrue
    | r :: rs =>
        envNodeCons (specRegionEnv r (fwcs 0%nat))
                    (envNodeCons (specRegionsEnv (fun i => fwcs (S i)) rs) envCtxTrue)
    end.

  Fixpoint implRegionsEnv (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : Env (implRegionsTree regions) :=
    match regions as rs return Env (implRegionsTree rs) with
    | [] => envCtxTrue
    | r :: rs =>
        envNodeCons (implRegionEnv r (fwcs 0%nat))
                    (envNodeCons (implRegionsEnv (fun i => fwcs (S i)) rs) envCtxTrue)
    end.

  (* `implMemTree`: [ implRegionsTree; state; requester; readRp ] *)
  Definition implMemEnv (fwcs : nat -> nat -> nat) (regions : list MemRegion)
    : Env (implMemTree regions) :=
    envNodeCons (implRegionsEnv fwcs regions) envCtxTrue.

  Lemma extRegionEnvCtx_inhabited :
    forall (S : Type) r fwc
           (getSr : S -> TreeState ElemState (externalMemRegionTree r))
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

End RegionEnvs.

(* --- 6C. System Envs (`specEnv`, `implEnv`) --- *)

Section SysEnvs.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity : nat.
  Variable mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  (* `fenceIWriteCount i k`: write count of the region at position `i` at its `k`-th ack. *)
  Variable fenceIWriteCount : nat -> nat -> nat.

  Local Abbreviation sTree := (@specSysTree pcAddrInit regions).
  Local Abbreviation iTree := (@implSysTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config regions).

  (* `specSysTree`: sys [ core [ rf; mem [ specMemTree ]; secondLine ] ] *)
  Definition specEnv : Env sTree :=
    envNodeCons
      (envNodeCons envCtxTrue
        (envNodeCons (envNodeCons (specRegionsEnv initLine fenceIWriteCount regions) envCtxTrue)
          envCtxTrue))
      envCtxTrue.

  (* `implSysTree`: sys [ core [ rf; waitBits; bp; mem [ implMemTree ];
   *                             fetch; decode; execute; dataMem; mulDiv ] ] *)
  Definition implEnv : Env iTree :=
    envNodeCons
      (envNodeCons envCtxTrue
        (envNodeCons envCtxTrue
          (envNodeCons envCtxTrue
            (envNodeCons (envNodeCons (implMemEnv initLine fenceIWriteCount regions) envCtxTrue)
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

