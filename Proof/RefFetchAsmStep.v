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

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint SpecRevoker Plic Spec.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplBranchPredictor.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel RefPeriph RefFrame.
From Cheriot.Proof Require Import RefSpecRead RefMemStep RefExecAux RefExecFrame RefDecodeStep RefPcEven RefFetchRqImpl
  RefFetchRqStep RefFetchAsmImpl RefFetchBits RefFetchWord DecodeFacts RefExecLive RefExecFlush RefRouteAt RefConsts
  RefBits RefRevTable.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ===========================================================================
 * MILESTONE 6: `fetchAssembleStage` (the spec stutters)
 * ===========================================================================
 * Branches (RefFetchAsmImpl.v): no `canProceed`, no head, no response or a full instBuf change
 * nothing the relation reads; a stale head is dropped with its response; a live head assembles an
 * instruction (or saves a straddle). *)

Local Abbreviation TS t := (TreeState ElemState t).


(* A valid response read for line `A` comes from the `readRp` of the ExternalMem region holding it *)
Lemma AllPorts_true :
  forall l (mi : TS (implRegionsTree l)), AllPorts (fun _ _ => True) l mi.
Proof.
  intros l; induction l as [| r rs IH]; intros mi; [exact I |].
  cbn [AllPorts]; split; [| apply IH].
  generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree; destruct (regionKind r); intros; exact I.
Qed.

Lemma fetchRpAt_valid_ports :
  forall l (mi : TS (implRegionsTree l)) A, lineUnique l A -> (fetchRpAt l mi A).(Snd).(Fst) = true ->
    AllPorts (fun r y => isRegionAddrB r A = true -> (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst)).(Snd).(Fst) = true) l mi.
Proof.
  intros l; induction l as [| r rs IH]; intros mi A Hu Hv; [exact I |].
  cbn [lineUnique] in Hu; cbn [fetchRpAt] in Hv; cbn [AllPorts].
  destruct (isRegionAddrB r A) eqn:Em.
  - split.
    + revert Hv; generalize (mi.(Fst)); unfold RegionPort, regionFetchRp, implMemRegionTree.
      destruct (regionKind r); intros y Hv; [| exact I].
      intros _; destruct (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst)); [reflexivity | exact Hv].
    + refine (AllPorts_none_impl _ _ A _ rs _ Hu (AllPorts_true _ _)).
      intros r' y Hf _ C; rewrite Hf in C; discriminate C.
  - split; [| exact (IH _ _ Hu Hv)].
    generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree; destruct (regionKind r);
      intros y; [intros C; rewrite Em in C; discriminate C | exact I].
Qed.

(* --- The live chain grows by one instruction at its frontier --- *)

Lemma LiveChainG_snoc :
  forall pre post revBase revPfB revPfA initLine fwcs pcc m (F : type Addr -> Prop) pc l fo pp,
    LiveChainG pre post revBase revPfB revPfA initLine fwcs pcc m
      (fun p => FetchAllowedInst initLine fwcs (specRegionsOf pre post revBase revPfB revPfA) m (pccWithAddr pcc p) fo /\
                (if foFault fo then True
                 else (needsPredOf (foInst fo) = false -> pp = seqPcOf p (foInst fo)) /\ F pp))
      pc l ->
    LiveChainG pre post revBase revPfB revPfA initLine fwcs pcc m F pc (l ++ [(fo, pp)]).
Proof.
  intros pre post revBase revPfB revPfA initLine fwcs pcc m F pc l fo pp; revert pc.
  induction l as [| [fo' pp'] l IH]; intros pc H; cbn [LiveChainG app] in *.
  - destruct H as [Hfa Hrest]; split; [exact Hfa |].
    destruct (foFault fo); [exact I |].
    destruct Hrest as [Hp HF]; split; [exact Hp |]; cbn [LiveChainG]; exact HF.
  - destruct H as [Hfa Hrest]; split; [exact Hfa |].
    destruct (foFault fo'); [exact I |].
    destruct Hrest as [Hp Hl]; split; [exact Hp | exact (IH pp' Hl)].
Qed.

(* --- Lines no ExternalMem region holds: the impl answers the default packet, the spec allows the
 * default response --- *)

Lemma lineKind_spec_impl :
  forall pre post revBase revPfB revPfA A,
    lineKind (specRegionsOf pre post revBase revPfB revPfA) A = lineKind (implRegionsOf pre post revBase revPfB revPfA) A.
Proof.
  intros pre post revBase revPfB revPfA A; unfold specRegionsOf, implRegionsOf.
  induction pre as [| r rs IH]; cbn [app lineKind]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma LineAllowed_default :
  forall initLine fwcs l m A,
    lineKind l A <> Some true -> LineAllowed initLine fwcs l m A (getDefault LineReadRp).
Proof.
  intros initLine fwcs l; revert fwcs; induction l as [| r rs IH]; intros fwcs m A Hk;
    cbn [LineAllowed lineKind] in *; [reflexivity |].
  change (evalExpr (isRegionAddr r (Var type Addr A))) with (isRegionAddrB r A).
  destruct (isRegionAddrB r A).
  - unfold RegionLineAllowed; generalize (m.(Fst)); unfold memRegionTree.
    destruct (regionKind r); [exfalso; apply Hk; reflexivity | intros _; exact I].
  - exact (IH _ _ _ Hk).
Qed.

Lemma fetchRpAt_custom :
  forall l (mi : TS (implRegionsTree l)) A, lineKind l A <> Some true -> fetchRpAt l mi A = someDefPkt.
Proof.
  intros l; induction l as [| r rs IH]; intros mi A Hk; cbn [fetchRpAt lineKind] in *; [reflexivity |].
  destruct (isRegionAddrB r A).
  - unfold regionFetchRp; generalize (mi.(Fst)); unfold implMemRegionTree.
    destruct (regionKind r); [exfalso; apply Hk; reflexivity | intros _; reflexivity].
  - exact (IH _ _ Hk).
Qed.

Lemma fetchPktOf_default : fetchPktOf (getDefault LineReadRp) = getDefault FetchPacket.
Proof.
  apply SameTuple_ext.
  destruct invariant_fetch as [HN [_ [HC _]]].
  assert (Hn : (0 < NumFetchParcels)%nat)
    by (apply Nat2Z.inj_lt; rewrite HN; apply Z.pow_pos_nonneg; [lia | destruct invariant_fetch as [_ [_ [_ [_ [_ [_ [_ [HF _]]]]]]]]; exact HF]).
  assert (Hlen : length (fetchPktOf (getDefault LineReadRp)).(tupleElems) = NumFetchParcels)
    by (apply Nat.eqb_eq, Is_true_eq_true; apply tupleSize).
  unfold FetchPacket; cbn [getDefault SameTupleDefault tupleElems].
  apply nth_ext with (d := Zmod.zero) (d' := Zmod.zero); [rewrite Hlen, repeat_length; reflexivity |].
  intros i Hi; rewrite Hlen in Hi.
  rewrite nth_repeat.
  rewrite fetchPktOf_arrays, (evalFromBitArray_nth_bits CompInstSz NumFetchParcels) by (first [lia | exact Hi]).
  assert (E0 : digits 8 (map Zmod.unsigned (getDefault LineReadRp).(Fst).(tupleElems)) = 0).
  { change ((getDefault LineReadRp).(Fst).(tupleElems)) with (repeat (Zmod.zero : bits 8) LineBytes).
    generalize LineBytes; intros n; induction n as [| n IHn]; cbn [repeat map digits]; [reflexivity |].
    rewrite Zmod.unsigned_0, IHn; lia. }
  match goal with |- context [@Zmod.unsigned ?m (evalToBitArray ?f ?t)] =>
    replace (@Zmod.unsigned m (evalToBitArray f t)) with 0
      by (etransitivity; [exact (eq_sym E0) | exact (eq_sym (evalToBitArray_digits 8 LineBytes _ (tupleSize t) ltac:(lia)))])
  end.
  apply Zmod.unsigned_inj; rewrite Zmod.unsigned_of_Z, Zmod.unsigned_0.
  rewrite Z.div_0_l, Z.mod_0_l; try reflexivity;
    pose proof (pow2_pos CompInstSz ltac:(lia)); pose proof (pow2_pos (CompInstSz * Z.of_nat i) ltac:(nia)); lia.
Qed.

(* The ExternalMem region holding line `A` of a port predicate, with the response it offers *)
Lemma fetchRpAt_ext :
  forall (P : forall r, TS (implExternalMemRegionTree r) -> Prop) l (mi : TS (implRegionsTree l)) A,
    lineUnique l A -> lineKind l A = Some true -> AllPorts P l mi ->
    exists r (y : TS (implExternalMemRegionTree r)),
      isRegionAddrB r A = true /\ P r y /\
      fetchRpAt l mi A =
        (if (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst)).(Snd).(Fst)
         then (fetchPktOf (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst)).(Fst) ,, (true ,, tt))
         else getDefault (Option FetchPacket)).
Proof.
  intros P l; induction l as [| r rs IH]; intros mi A Hu Hk HP; cbn [lineKind] in Hk; [discriminate Hk |].
  cbn [lineUnique] in Hu; cbn [fetchRpAt AllPorts] in *; destruct HP as [H0 H1].
  destruct (isRegionAddrB r A) eqn:Em.
  - revert H0 Hk; generalize (mi.(Fst)); unfold RegionPort, regionFetchRp, implMemRegionTree.
    destruct (regionKind r); intros y H0 Hk; [| discriminate Hk].
    exists r, y; split; [exact Em | split; [exact H0 | reflexivity]].
  - exact (IH _ _ Hu Hk H1).
Qed.

(* --- Small facts for the live-head branches --- *)

(* A modulus the unifier wrote out as a numeral, restated as `2 ^ AddrSz` for `lia` *)
Ltac addrBound := match goal with |- 0 <= ?a < _ => change (0 <= a < 2 ^ AddrSz) end.

Lemma eqAddrE_eval : forall a b : Expr type Addr, evalExpr (Eq a b) = Zmod.eqb (evalExpr a) (evalExpr b).
Proof. reflexivity. Qed.

Lemma FbChain_tail : forall f l pc, FbChain (f :: l) pc -> FbChain l pc.
Proof. intros f l pc H; destruct l as [| f' l]; [exact I | exact (proj2 H)]. Qed.

(* Clearing bit 0 of an even address is the identity *)
Lemma clearBit0_aligned : forall a : type Addr, pcAligned a -> clearBit0 a = a.
Proof.
  intros a Hal; apply pcAligned_iff in Hal.
  pose proof LgLineBytes_lt_AddrSz as HLA; pose proof LgLineBytes_nonneg as HLn.
  apply Zmod.unsigned_inj; unfold clearBit0; cbn [evalExpr].
  etransitivity;
    [exact (unsigned_app_add 1 (AddrSz - 1) Zmod.zero (Zmod_lastn (AddrSz - 1) a) ltac:(lia) ltac:(lia)) |].
  rewrite Zmod.unsigned_0.
  match goal with |- context [@Zmod.unsigned ?m (Zmod_lastn ?n ?x)] =>
    replace (@Zmod.unsigned m (Zmod_lastn n x)) with (Zmod.unsigned a / 2 ^ 1)
      by (symmetry; exact (to_Z_lastn' (AddrSz - 1) 1 a ltac:(lia) ltac:(lia)))
  end.
  change (2 ^ 1) with 2.
  pose proof (Z.div_mod (Zmod.unsigned a) 2 ltac:(lia)); lia.
Qed.

Section FetchAsmStep.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revI := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation Ghost := (Ghost pcAddrInit).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).
  Local Abbreviation STEPOK :=
    (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
  Local Abbreviation STAGE :=
    (@fetchAssembleStage pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions revI type).

  Local Abbreviation ACC f := (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRfA := (ACC iRf).
  Local Abbreviation iWbA := (ACC iWb).
  Local Abbreviation iMemA := (ACC iMem).
  Local Abbreviation iFetchA := (ACC iFetch).
  Local Abbreviation iDecodeA := (ACC iDecode).
  Local Abbreviation iExecA := (ACC iExec).
  Local Abbreviation iDmA := (ACC iDm).
  Local Abbreviation iMdA :=
    (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation iFlushA := (ACC iFlush).
  Local Abbreviation iRegionsA := (ACC iRegions).
  Local Abbreviation iFetchBufA := (ACC iFetchBuf).
  Local Abbreviation iInstBufA := (ACC iInstBuf).
  Local Abbreviation iD2aA := (ACC iD2a).
  Local Abbreviation iExecEpochA := (ACC iExecEpoch).
  Local Abbreviation iFenceIPendingA := (ACC iFenceIPending).
  Local Abbreviation iPccA := (ACC iPcc).
  Local Abbreviation iRevA := (ACC iRev).
  Local Abbreviation olderWritersA := (ACC olderWriters).
  Local Abbreviation daLiveA := (ACC daLive).
  Local Abbreviation aiLiveA := (ACC aiLive).
  Local Abbreviation fbLiveA := (ACC fbLive).
  Local Abbreviation liveInstsA := (ACC liveInsts).
  Local Abbreviation MEMC := (MemRelC pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).

  Local Opaque gprPathsWithKind scrPathsWithKind csrPathsWithKind gprWaitPathsWithKind.

  Local Abbreviation FASM := (FasmStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).

  (* Only fetch's `canProceed` changed *)
  Lemma asm_stutter_rel :
    forall g (s1 s1' : IState) (s2 : SState),
      FASM s1 s1' (iMemA s1) (ACC aF0 s1) -> RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] H.
    destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    destruct H as [_ _ Hl Hrp He _ _ _ Hf Hs Hfr Hw _].
    constructor; try assumption.
    - unfold FenceRel, NoLive, NoFenceIWait, daLive, aiLive, fbLive,
             iStraddle, iInstBuf, iFetchBuf, iPredEpoch in *;
        rewrite Ereg, Efe, Ed2a, Eep, Efip; exact Hf.
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - unfold FrontRel, LiveChain, FrontierRel, FetchRespRel, fbInRegion, liveInsts,
             daLive, aiLive, fbLive, iPcc, iFetchPc, iPredEpoch, iCurParcel, iStraddle,
             iFetchBuf, iInstBuf in *;
        rewrite Erf, Ereg, Efe, Ed2a, Eep; exact Hfr.
    - unfold WfRel, iCurParcel, iFetchBuf, iInstBuf, iPcc in *;
        rewrite ?Erf, ?Ed2a, ?ED, ?Efe, ?Edm, ?Emd, ?Ereg; exact Hw.
  Qed.

  Local Abbreviation FBF s1 := (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation IBF s1 := (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetchA s1)).
  Local Abbreviation FRREL := (FetchRespRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                 initLine fwcs).
  Local Abbreviation aEA := (ACC aE).

  Lemma fb_head :
    forall (s1 : IState),
      fifo_wf (FBF s1) -> (ACC aHead s1).(Snd).(Fst) = true ->
      exists rest, iFetchBufA s1 = aEA s1 :: rest /\ fifo_to_list (fifoDeqState (FBF s1)) = rest.
  Proof.
    intros s1 Hwf Hv.
    unfold aHead in Hv; rewrite (fifoFirstVal_valid _ _ _ Hwf) in Hv.
    unfold iFetchBuf; destruct (fifo_to_list (FBF s1)) as [| a rest] eqn:El; [discriminate Hv |].
    exists rest; split.
    - f_equal; unfold aE, aHead; symmetry; exact (fifoFirstVal_data _ _ _ a rest El).
    - rewrite (fifo_to_list_deq _ _ _ Hwf), El; reflexivity.
  Qed.

  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).

  (* --- The live head: what the relation says about it --- *)

  Lemma head_live_list :
    forall (s1 : IState), fifo_wf (FBF s1) -> (ACC aHead s1).(Snd).(Fst) = true -> ACC aMatch s1 = true ->
      exists rest, iFetchBufA s1 = aEA s1 :: rest /\ fbLiveA s1 (aEA s1) = true /\
        filter (fbLiveA s1) (iFetchBufA s1) = aEA s1 :: filter (fbLiveA s1) rest.
  Proof.
    intros s1 Hwf Hv Hm; destruct (fb_head s1 Hwf Hv) as [rest [Efb _]].
    assert (Hl : fbLiveA s1 (aEA s1) = true) by (rewrite <- (ACC aMatch_eq s1); exact Hm).
    exists rest; split; [exact Efb | split; [exact Hl |]].
    rewrite Efb; cbn [filter]; rewrite Hl; reflexivity.
  Qed.

  Local Abbreviation FRONTIER := (FrontierRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                    initLine fwcs).

  (* No straddle: the frontier is parcel `aK` of the head's line, with the head's pre-fault flags *)
  Lemma frontier_noSh :
    forall (s1 : IState) (s2 : SState) fp rest,
      iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true -> ACC aHasSh s1 = false ->
      FRONTIER s1 s2 fp ->
      fp = parcelAddrOf (ACC aAligned s1) (ACC aK s1) /\ ACC aPreExc s1 = preExcAt (iPccA s1) fp /\ pcAligned fp.
  Proof.
    intros s1 s2 fp rest Efb Hl Hsh H.
    unfold FrontierRel in H; cbv zeta in H.
    rewrite Efb in H; cbn [filter] in H; rewrite Hl in H.
    change (ACC aHasSh s1) with (optValid (ACC iStraddle s1)) in Hsh; rewrite Hsh in H.
    cbv beta iota in H; try rewrite Hl in H; cbn [andb] in H.
    destruct H as [_ [Hx [Hm Hal]]].
    rewrite (ACC aAligned_eq s1), (ACC aPreExc_eq s1).
    unfold aK; rewrite evalExpr_ITE.
    change (evalExpr ((Var type (Option (Bit LgFetchParcels)) (ACC iCurParcel s1))`"valid"))
      with (optValid (ACC iCurParcel s1)).
    change (evalExpr ((Var type (Option (Bit LgFetchParcels)) (ACC iCurParcel s1))`"data"))
      with (optData (ACC iCurParcel s1)).
    change (evalExpr (Var type (Bit LgFetchParcels) (ACC aStart s1))) with (ACC aStart s1).
    destruct (optValid (ACC iCurParcel s1)).
    - destruct Hm as [Hm1 Hm2]; split; [symmetry; exact Hm1 | split; [exact Hm2 | exact Hal]].
    - split; [| split; [rewrite (Forall_inv Hx), Hm; reflexivity | exact Hal]].
      unfold aStart; change (ACC aEntryPc s1) with (fbPcAddr (aEA s1)); rewrite Hm.
      symmetry; exact (parcelAddr_self fp Hal).
  Qed.

  (* A straddle: the frontier `fp` is the last parcel of the previous line, the head is its next line *)
  Lemma frontier_sh :
    forall (s1 : IState) (s2 : SState) fp rest,
      iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true -> ACC aHasSh s1 = true ->
      FRONTIER s1 s2 fp ->
      ACC aInstPc s1 = fp /\ Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 /\
      fbPcAddr (aEA s1) = evalExpr (memNextLineAddr (Var type Addr fp)) /\
      (ACC aSh s1).(Snd).(Fst) = preExcAt (iPccA s1) fp /\ excAny (preExcAt (iPccA s1) fp) = false /\
      topExcAt (iPccA s1) fp false = false /\ evalExpr (@isParcelCompressed type (ACC aSh s1).(Fst)) = false /\
      (exists rpPrev, LineAllowed initLine fwcs specRegions (sMemA s2) (lineAddrOf fp) rpPrev /\
                      (ACC aSh s1).(Fst) = pktParcel (fetchPktOf rpPrev) lastParcel) /\
      pcAligned fp /\ ACC aPreExc s1 = preExcAt (iPccA s1) (fbPcAddr (aEA s1)).
  Proof.
    intros s1 s2 fp rest Efb Hl Hsh H.
    pose proof Hsh as Hsh0.
    unfold FrontierRel in H; cbv zeta in H.
    rewrite Efb in H; cbn [filter] in H; rewrite Hl in H.
    change (ACC aHasSh s1) with (optValid (ACC iStraddle s1)) in Hsh; rewrite Hsh in H.
    cbv beta iota in H.
    destruct H as [_ [Hx [[Hne [Hlp [Hexc [Hx0 [Ht [Hu [Hrp Hd]]]]]]] Hal]]].
    change (ACC aSh s1) with (optData (ACC iStraddle s1)).
    pose proof (lastParcel_low fp Hal Hlp) as Ho.
    split; [| split; [exact Ho | split; [exact Hd | split; [exact Hexc | split; [exact Hx0 | split; [exact Ht |
      split; [exact Hu | split; [exact Hrp | split; [exact Hal |]]]]]]]]].
    - unfold aInstPc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh0, (ACC aAligned_eq s1), Hd.
      exact (straddle_pc fp Hal Hlp).
    - rewrite (ACC aPreExc_eq s1); exact (Forall_inv Hx).
  Qed.

  (* The head's packet comes from a response the spec may receive for its line *)
  Lemma head_packet :
    forall g (s1 : IState) (s2 : SState) rest,
      RELG g s1 s2 -> iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      ACC aPre s1 = false -> (ACC aPkt s1).(Snd).(Fst) = true ->
      exists rp, ACC aPktD s1 = fetchPktOf rp /\ LineAllowed initLine fwcs specRegions (sMemA s2) (ACC aAligned s1) rp.
  Proof.
    intros g s1 s2 rest Hg Efb Hl Hpre Hpv.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    pose proof Hg as [_ _ _ _ _ _ _ _ _ _ [_ [_ [_ [_ [_ [_ F7]]]]]] _ _].
    assert (EpD : ACC aPktD s1 = (fetchRpAt implRegions (iRegionsA s1) (ACC aAligned s1)).(Fst))
      by (unfold aPktD, aPkt; rewrite Hpre; reflexivity).
    unfold aPkt in Hpv; rewrite Hpre in Hpv.
    pose proof (ACC aPre_excAny s1) as HpX; rewrite Hpre in HpX.
    destruct (lineKind implRegions (ACC aAligned s1)) as [[|] |] eqn:Hk.
    - destruct (fetchRpAt_ext _ implRegions (iRegionsA s1) (ACC aAligned s1) (Hu _) Hk F7) as [r [y [Hr [HP Hrp]]]].
      cbv zeta in HP; destruct HP as [C [_ [_ HC3]]].
      rewrite Hrp in Hpv, EpD.
      destruct ((y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst)).(Snd).(Fst)) eqn:Hval; [| discriminate Hpv].
      destruct (HC3 Hval) as [f [E' [HE Hla]]].
      assert (Hf : f = aEA s1).
      { unfold fbInRegion in HE; rewrite Efb in HE; cbn [filter] in HE.
        rewrite <- HpX, <- (ACC aAligned_eq s1), Hr in HE; cbn [negb andb] in HE.
        injection HE as -> _; reflexivity. }
      subst f.
      exists (y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst)).(Fst); split; [exact EpD |].
      rewrite (ACC aAligned_eq s1); exact (Hla Hl).
    - exists (getDefault LineReadRp); split.
      + rewrite EpD, fetchRpAt_custom by (rewrite Hk; discriminate); rewrite fetchPktOf_default; reflexivity.
      + apply LineAllowed_default; rewrite lineKind_spec_impl, Hk; discriminate.
    - exists (getDefault LineReadRp); split.
      + rewrite EpD, fetchRpAt_custom by (rewrite Hk; discriminate); rewrite fetchPktOf_default; reflexivity.
      + apply LineAllowed_default; rewrite lineKind_spec_impl, Hk; discriminate.
  Qed.

  (* --- The assembled instruction is one the spec may fetch at the frontier --- *)

  Lemma specPreFault_eq :
    forall (pcc : type FullECapWithTag) (pc : type Addr), specPreFault (pccWithAddr pcc pc) = excAny (preExcAt pcc pc).
  Proof.
    intros pcc pc; unfold specPreFault; cbv zeta; rewrite or4_excAny.
    unfold preExcAt; cbv zeta; rewrite pccWithAddr_addr, pccWithAddr_ecap.
    destruct pcc as [t [e [a []]]]; reflexivity.
  Qed.

  (* The fetch output, from its pre-fault flags, raw word and top check *)
  Lemma aFo_eq :
    forall (s1 : IState),
      ACC aFo s1 = (evalExpr ((Var type ECap (ACC aECap s1))`"perms"`"SR") ,, (ACC aExp s1 ,, (ACC aComb s1 ,, tt))).
  Proof. intros s1; reflexivity. Qed.

  Lemma aComb_eq :
    forall (s1 : IState),
      ACC aComb s1 =
      ((ACC aPktExc s1).(Fst) ,, ((ACC aPktExc s1).(Snd).(Fst) ,, ((ACC aPktExc s1).(Snd).(Snd).(Fst) ,,
        (orb (ACC aPktExc s1).(Snd).(Snd).(Snd).(Fst) (ACC aTop s1) ,, tt)))).
  Proof.
    intros s1; unfold aComb; generalize (ACC aPktExc s1); intros [t [sl [p [b []]]]].
    generalize (ACC aTop s1); intros tp; destruct b, tp; reflexivity.
  Qed.

  Lemma pccWithAddr_tag :
    forall (pcc : type FullECapWithTag) (pc : type Addr),
      evalExpr (Not ((Var type FullECapWithTag (pccWithAddr pcc pc))`"tag")) =
      evalExpr (Not ((Var type FullECapWithTag pcc)`"tag")).
  Proof. intros [t [e [a []]]] pc; reflexivity. Qed.

  Lemma or2v_eval : forall a b : bool, evalExpr (Or [Var type Bool a; Var type Bool b]) = orb a b.
  Proof. intros [|] [|]; reflexivity. Qed.

  (* fetch's PCC copy has the architectural PCC's bounds and permissions (item 3.4) *)
  Definition PccOK (s1 : IState) : Prop := ACC aECap s1 = (iPccA s1).(Snd).(Fst).

  Lemma fo_of :
    forall (s1 : IState) fp raw topv,
      PccOK s1 -> ACC aPktExc s1 = preExcAt (iPccA s1) fp -> ACC aRaw s1 = raw -> ACC aTop s1 = topv ->
      ACC aFo s1 = specFetchOutOf (pccWithAddr (iPccA s1) fp) (evalLetExpr (preDecode (ty := type) raw)) topv.
  Proof.
    intros s1 fp raw topv Hpok Hx Hr Ht.
    rewrite aFo_eq, aComb_eq, Hx; unfold aExp; rewrite Hr, Ht.
    unfold specFetchOutOf; cbv zeta; rewrite pccWithAddr_addr, pccWithAddr_ecap, pccWithAddr_tag, or2v_eval.
    unfold preExcAt; cbv zeta; cbn [Fst Snd].
    rewrite Hpok; reflexivity.
  Qed.

  Lemma aTop_eq :
    forall (s1 : IState) fp c, PccOK s1 -> ACC aInstPc s1 = fp -> ACC aIsCompI s1 = c -> ACC aTop s1 = topExcAt (iPccA s1) fp c.
  Proof.
    intros s1 fp c Hpok Hpc Hc; unfold aTop, aEnd, aLg, topExcAt, pccTopOf; cbv zeta; rewrite Hpok, Hpc, Hc; reflexivity.
  Qed.

  Lemma fp_bound :
    forall fp : type Addr, pcAligned fp -> Zmod.unsigned fp + 2 ^ Z.log2 (CompInstSz / 8) <= 2 ^ AddrSz.
  Proof.
    intros fp Hal; apply pcAligned_iff in Hal; change (Zmod.to_Z fp) with (Zmod.unsigned fp) in Hal.
    destruct invariant_fetch as [_ [HL [HC _]]].
    pose proof LgLineBytes_lt_AddrSz as HLA.
    destruct invariant_fetch as [_ [_ [_ [_ [_ [_ [_ [HF _]]]]]]]].
    assert (Hfp : 0 <= Zmod.unsigned fp < 2 ^ AddrSz) by exact (bits.unsigned_range fp ltac:(cbv; congruence)).
    assert (H2 : 2 ^ AddrSz = 2 * 2 ^ (AddrSz - 1))
      by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite HC; change (2 ^ Z.log2 (2 * 8 / 8)) with 2.
    assert (Hq : Zmod.unsigned fp = 2 * (Zmod.unsigned fp / 2))
      by (rewrite (Z.div_mod (Zmod.unsigned fp) 2) at 1 by lia; lia).
    rewrite Hq, H2 in *; lia.
  Qed.

  (* A pre-faulted head: the instruction reads as 0 and faults as the spec's pre-faulted fetch *)
  Lemma allowed_pre :
    forall (s1 : IState) (s2 : SState) fp,
      PccOK s1 -> ACC aPre s1 = true -> ACC aHasSh s1 = false -> ACC aInstPc s1 = fp ->
      ACC aPreExc s1 = preExcAt (iPccA s1) fp -> pcAligned fp ->
      FetchAllowedInst initLine fwcs specRegions (sMemA s2) (pccWithAddr (iPccA s1) fp) (ACC aFo s1).
  Proof.
    intros s1 s2 fp Hpok Hpre Hsh Hpc Hexc Hal.
    pose proof (ACC aPre_excAny s1) as Hx; rewrite Hpre, <- (ACC aPreExc_eq s1), Hexc in Hx.
    unfold FetchAllowedInst; cbv zeta.
    rewrite specPreFault_eq, <- Hx.
    assert (HpD : ACC aPktD s1 = getDefault FetchPacket) by (unfold aPktD, aPkt; rewrite Hpre; reflexivity).
    assert (HpK : ACC aParcelK s1 = Zmod.zero) by (unfold aParcelK; rewrite HpD; exact (pktParcel_default _)).
    assert (HiC : ACC aIsComp s1 = true)
      by (unfold aIsComp; rewrite HpK, df_isParcelCompressed_eval; vm_compute; reflexivity).
    assert (HiCI : ACC aIsCompI s1 = true) by (unfold aIsCompI; rewrite and2nv_eval, Hsh, HiC; reflexivity).
    assert (Hcross : ACC aCross s1 = false) by (unfold aCross; rewrite and3n_eval, Hsh, HiC; reflexivity).
    assert (Hhigh : ACC aHigh s1 = Zmod.zero).
    { unfold aHigh; rewrite ITE0_eval, notVar_eval, Hcross; cbn [negb]; rewrite HpD; exact (pktParcel_default _). }
    assert (Hlow : ACC aLow s1 = Zmod.zero).
    { unfold aLow; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact HpK. }
    assert (Hraw : ACC aRaw s1 = Zmod.zero) by (unfold aRaw; rewrite Hhigh, Hlow; exact implWord_zero).
    assert (HpX : ACC aPktExc s1 = preExcAt (iPccA s1) fp).
    { unfold aPktExc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact Hexc. }
    rewrite (fo_of s1 fp Zmod.zero _ Hpok HpX Hraw (aTop_eq s1 fp true Hpok Hpc HiCI)).
    rewrite preDecode_zero, specPreFaultTopExc_eq by exact (fp_bound fp Hal).
    reflexivity.
  Qed.

  Lemma pccTopOf_withAddr :
    forall (pcc : type FullECapWithTag) (pc : type Addr), pccTopOf (pccWithAddr pcc pc) = pccTopOf pcc.
  Proof. intros [t [e [a []]]] pc; reflexivity. Qed.

  Lemma specReads2_eval :
    forall pc top raw0, specReads2 pc top raw0 = andb (specCrosses pc raw0) (negb (specTopExc pc top raw0)).
  Proof. intros pc top raw0; unfold specReads2; apply and2_eval. Qed.

  Lemma specTopExc_eq :
    forall (pcc : type FullECapWithTag) pc raw0,
      specTopExc pc (pccTopOf pcc) raw0 = topExcAt pcc pc (evalExpr (@isCompressed type raw0)).
  Proof. reflexivity. Qed.

  (* Common facts of a non-faulting head without a straddle *)
  Lemma noSh_facts :
    forall (s1 : IState) fp rp,
      PccOK s1 -> ACC aPre s1 = false -> ACC aHasSh s1 = false -> ACC aPktD s1 = fetchPktOf rp ->
      fp = parcelAddrOf (ACC aAligned s1) (ACC aK s1) -> ACC aPreExc s1 = preExcAt (iPccA s1) fp ->
      Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 * Zmod.unsigned (ACC aK s1) /\
      excAny (preExcAt (iPccA s1) fp) = false /\
      ACC aPktExc s1 = preExcAt (iPccA s1) fp /\
      ACC aLow s1 = pktParcel (fetchPktOf rp) (ACC aK s1) /\
      evalExpr (@isCompressed type (ACC aRaw s1)) = ACC aIsComp s1 /\
      ACC aTop s1 = topExcAt (iPccA s1) fp (ACC aIsComp s1) /\
      ACC aCross s1 = andb (negb (ACC aIsComp s1)) (ACC aIsLast s1) /\
      (ACC aIsLast s1 = true <-> Zmod.unsigned (ACC aK s1) = 2 ^ LgFetchParcels - 1) /\
      (ACC aCross s1 = false -> ACC aHigh s1 = pktParcel (fetchPktOf rp) (ACC aK1 s1)) /\
      (ACC aCross s1 = true -> ACC aHigh s1 = Zmod.zero) /\
      lineAddrOf fp = ACC aAligned s1.
  Proof.
    intros s1 fp rp Hpok Hpre Hsh HpD Hfp Hexc.
    destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
    pose proof (lineAddr_aligned (fbPcAddr (aEA s1))) as HA; rewrite <- (ACC aAligned_eq s1) in HA.
    pose proof (parcelAddr_off (ACC aAligned s1) (ACC aK s1) HA) as Hoff; rewrite <- Hfp in Hoff.
    pose proof (ACC aPre_excAny s1) as Hx; rewrite Hpre, <- (ACC aPreExc_eq s1), Hexc in Hx.
    assert (HpK : ACC aParcelK s1 = pktParcel (fetchPktOf rp) (ACC aK s1)) by (unfold aParcelK; rewrite HpD; reflexivity).
    assert (HiCI : ACC aIsCompI s1 = ACC aIsComp s1) by (unfold aIsCompI; rewrite and2nv_eval, Hsh; reflexivity).
    assert (Hlow : ACC aLow s1 = pktParcel (fetchPktOf rp) (ACC aK s1)).
    { unfold aLow; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact HpK. }
    split; [exact Hoff | split; [symmetry; exact Hx | split; [| split; [exact Hlow | split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
    - unfold aPktExc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact Hexc.
    - unfold aRaw; rewrite isCompressed_concat_parcels, Hlow; unfold aIsComp; rewrite HpK; reflexivity.
    - apply (aTop_eq s1 fp (ACC aIsComp s1) Hpok); [| exact HiCI].
      unfold aInstPc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact (eq_sym Hfp).
    - unfold aCross; rewrite and3n_eval, Hsh; reflexivity.
    - unfold aIsLast; rewrite isAllOnes_eval; change (evalExpr (Var type (Bit LgFetchParcels) (ACC aK s1))) with (ACC aK s1).
      split; intros E.
      + apply Zmod.eqb_eq in E; rewrite E, unsigned_invDefault, Z.ones_equiv by exact HF; lia.
      + apply Zmod.eqb_eq; apply Zmod.unsigned_inj; rewrite E, unsigned_invDefault, Z.ones_equiv by exact HF; lia.
    - intros Hc; unfold aHigh; rewrite ITE0_eval, notVar_eval, Hc; cbn [negb]; rewrite HpD.
      unfold aHiIdx; rewrite ITE0_eval, notVar_eval, Hsh; cbn [negb]; reflexivity.
    - intros Hc; unfold aHigh; rewrite ITE0_eval, notVar_eval, Hc; reflexivity.
    - rewrite Hfp; exact (lineAddr_parcelAddr _ _ HA).
  Qed.

  (* The spec's fetch of the raw word `raw` with top check `topv`, when the instruction does not
   * cross its line *)
  Lemma allowed_of_noCross :
    forall (s1 : IState) (s2 : SState) fp rp raw,
      PccOK s1 -> excAny (preExcAt (iPccA s1) fp) = false ->
      LineAllowed initLine fwcs specRegions (sMemA s2) (lineAddrOf fp) rp ->
      specWord fp (specPkt fp rp) = raw ->
      specCrosses fp raw = false ->
      ACC aPktExc s1 = preExcAt (iPccA s1) fp -> ACC aRaw s1 = raw ->
      ACC aTop s1 = topExcAt (iPccA s1) fp (evalExpr (@isCompressed type raw)) ->
      FetchAllowedInst initLine fwcs specRegions (sMemA s2) (pccWithAddr (iPccA s1) fp) (ACC aFo s1).
  Proof.
    intros s1 s2 fp rp raw Hpok Hx Hla Hw Hcr HpX Hraw Htop.
    unfold FetchAllowedInst; cbv zeta.
    rewrite pccWithAddr_addr, specPreFault_eq, Hx, pccTopOf_withAddr.
    exists rp, rp; split; [exact Hla |].
    unfold specFetchRd; cbv zeta; rewrite Hw, specReads2_eval, Hcr; cbn [andb fst snd].
    split; [intros C; discriminate C |].
    rewrite evalExpr_ITE; change (evalExpr (Var type Bool false)) with false; cbv iota.
    change (evalExpr (Var type CapPacket (specPkt fp rp))) with (specPkt fp rp); rewrite Hw.
    rewrite specTopExc_eq.
    exact (fo_of s1 fp raw _ Hpok HpX Hraw Htop).
  Qed.

  (* A non-faulting head without a straddle whose instruction stays in its line *)
  Lemma allowed_inline :
    forall (s1 : IState) (s2 : SState) fp rp,
      PccOK s1 -> ACC aPre s1 = false -> ACC aHasSh s1 = false -> ACC aCross s1 = false ->
      ACC aPktD s1 = fetchPktOf rp -> LineAllowed initLine fwcs specRegions (sMemA s2) (ACC aAligned s1) rp ->
      fp = parcelAddrOf (ACC aAligned s1) (ACC aK s1) -> ACC aPreExc s1 = preExcAt (iPccA s1) fp ->
      FetchAllowedInst initLine fwcs specRegions (sMemA s2) (pccWithAddr (iPccA s1) fp) (ACC aFo s1).
  Proof.
    intros s1 s2 fp rp Hpok Hpre Hsh Hcross HpD Hla Hfp Hexc.
    destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
    pose proof lineBytes_parcels as HL2.
    pose proof (pow2_pos LgFetchParcels HF) as HFp.
    pose proof (bits.unsigned_range (ACC aK s1) HF) as Hk.
    destruct (noSh_facts s1 fp rp Hpok Hpre Hsh HpD Hfp Hexc)
      as [Hoff [Hx [HpX [Hlow [Hcomp [Htop [HcrossE [HlastE [Hhigh [_ HlA]]]]]]]]]].
    rewrite <- HlA in Hla.
    pose proof Hcross as Hcross0; rewrite HcrossE in Hcross.
    assert (Hw : specWord fp (specPkt fp rp) = ACC aRaw s1).
    { destruct (ACC aIsLast s1) eqn:Hlast.
      - pose proof (proj1 HlastE eq_refl) as HkL.
        assert (Ho : Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2) by lia.
        assert (Hk1 : ACC aK1 s1 = Zmod.zero).
        { unfold aK1; apply Zmod.unsigned_inj; rewrite to_Z_Add2, to_Z_Var, to_Z_const, Zmod.unsigned_0.
          rewrite (Z.mod_small 1) by (pose proof parcels_ge2; lia); rewrite HkL.
          replace (2 ^ LgFetchParcels - 1 + 1) with (2 ^ LgFetchParcels) by lia; apply Z.mod_same; lia. }
        rewrite specWord_lastWrap by exact Ho.
        unfold aRaw; rewrite (Hhigh Hcross0), Hlow, Hk1.
        unfold implWord; repeat f_equal.
        apply Zmod.unsigned_inj; rewrite lastParcel_unsigned, HkL; reflexivity.
      - assert (HkLt : Zmod.unsigned (ACC aK s1) + 1 < 2 ^ LgFetchParcels).
        { assert (Hne : Zmod.unsigned (ACC aK s1) <> 2 ^ LgFetchParcels - 1)
            by (intros E; pose proof (proj2 HlastE E) as E2; rewrite ?Hlast in E2; discriminate E2). lia. }
        assert (Hk1 : Zmod.unsigned (ACC aK1 s1) = Zmod.unsigned (ACC aK s1) + 1).
        { unfold aK1; rewrite to_Z_Add2, to_Z_Var, to_Z_const.
          rewrite (Z.mod_small 1) by (pose proof parcels_ge2; lia); apply Z.mod_small; lia. }
        rewrite (specWord_inline fp (ACC aK s1) (ACC aK1 s1) rp Hoff Hk1 HkLt).
        unfold aRaw; rewrite (Hhigh Hcross0), Hlow; reflexivity. }
    assert (Hcr : specCrosses fp (ACC aRaw s1) = false).
    { rewrite specCrosses_eval, Hcomp.
      destruct (ACC aIsComp s1) eqn:HiC; [reflexivity |].
      cbn [negb andb] in Hcross.
      assert (HkLt : Zmod.unsigned (ACC aK s1) + 1 < 2 ^ LgFetchParcels).
      { assert (Hne : Zmod.unsigned (ACC aK s1) <> 2 ^ LgFetchParcels - 1)
          by (intros E; rewrite (proj2 HlastE E) in Hcross; discriminate Hcross). lia. }
      rewrite (specCross_inline fp (ACC aK s1) Hoff HkLt); reflexivity. }
    rewrite <- Hcomp in Htop.
    exact (allowed_of_noCross s1 s2 fp rp (ACC aRaw s1) Hpok Hx Hla Hw Hcr HpX eq_refl Htop).
  Qed.

  (* A non-faulting head without a straddle whose 4-byte instruction spills into the next line but
   * fails the top check: its upper parcel reads 0 on both sides *)
  Lemma allowed_lastTop :
    forall (s1 : IState) (s2 : SState) fp rp,
      PccOK s1 -> ACC aPre s1 = false -> ACC aHasSh s1 = false -> ACC aCross s1 = true -> ACC aInit s1 = false ->
      ACC aPktD s1 = fetchPktOf rp -> LineAllowed initLine fwcs specRegions (sMemA s2) (ACC aAligned s1) rp ->
      fp = parcelAddrOf (ACC aAligned s1) (ACC aK s1) -> ACC aPreExc s1 = preExcAt (iPccA s1) fp ->
      FetchAllowedInst initLine fwcs specRegions (sMemA s2) (pccWithAddr (iPccA s1) fp) (ACC aFo s1).
  Proof.
    intros s1 s2 fp rp Hpok Hpre Hsh Hcross Hinit HpD Hla Hfp Hexc.
    destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
    pose proof lineBytes_parcels as HL2.
    pose proof (pow2_pos LgFetchParcels HF) as HFp.
    pose proof (bits.unsigned_range (ACC aK s1) HF) as Hk.
    destruct (noSh_facts s1 fp rp Hpok Hpre Hsh HpD Hfp Hexc)
      as [Hoff [Hx [HpX [Hlow [Hcomp [Htop [HcrossE [HlastE [_ [Hhigh HlA]]]]]]]]]].
    rewrite <- HlA in Hla.
    pose proof Hcross as Hcross0; rewrite HcrossE in Hcross.
    apply andb_true_iff in Hcross; destruct Hcross as [HnC Hlast]; apply negb_true_iff in HnC.
    pose proof (proj1 HlastE Hlast) as HkL.
    assert (Ho : Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2) by lia.
    assert (HkE : ACC aK s1 = lastParcel) by (apply Zmod.unsigned_inj; rewrite lastParcel_unsigned; exact HkL).
    assert (Htrue : ACC aTop s1 = true).
    { unfold aInit in Hinit; rewrite and2_eval, Hcross0 in Hinit; cbn [andb] in Hinit.
      apply negb_false_iff in Hinit; exact Hinit. }
    assert (HiC' : evalExpr (@isParcelCompressed type (pktParcel (fetchPktOf rp) (ACC aK s1))) = false)
      by (unfold aIsComp, aParcelK in HnC; rewrite HpD in HnC; exact HnC).
    assert (Hc0 : evalExpr (@isCompressed type (specWord fp (specPkt fp rp))) = false).
    { rewrite specWord_lastWrap by exact Ho; unfold implWord; rewrite isCompressed_concat_parcels, <- HkE; exact HiC'. }
    assert (Hraw : ACC aRaw s1 = implWord Zmod.zero (pktParcel (fetchPktOf rp) lastParcel))
      by (unfold aRaw; rewrite (Hhigh Hcross0), Hlow, HkE; reflexivity).
    rewrite HnC in Htop; rewrite Htrue in Htop.
    unfold FetchAllowedInst; cbv zeta.
    rewrite pccWithAddr_addr, specPreFault_eq, Hx, pccTopOf_withAddr.
    exists rp, rp; split; [exact Hla |].
    unfold specFetchRd; cbv zeta.
    rewrite specReads2_eval, specTopExc_eq, Hc0, <- Htop, specCrosses_eval, Hc0, specCross_last by exact Ho.
    cbn [negb andb fst snd].
    split; [intros C; discriminate C |].
    rewrite evalExpr_ITE; change (evalExpr (Var type Bool true)) with true; cbv iota.
    rewrite specWord_lastTop by exact Ho.
    rewrite <- Hraw.
    exact (fo_of s1 fp _ true Hpok HpX eq_refl Htrue).
  Qed.

  (* A straddle completed with the next line's packet *)
  Lemma allowed_sh :
    forall (s1 : IState) (s2 : SState) fp rp rpPrev,
      PccOK s1 -> ACC aPre s1 = false -> ACC aHasSh s1 = true -> ACC aInstPc s1 = fp ->
      Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2 ->
      fbPcAddr (aEA s1) = evalExpr (memNextLineAddr (Var type Addr fp)) ->
      (ACC aSh s1).(Snd).(Fst) = preExcAt (iPccA s1) fp -> excAny (preExcAt (iPccA s1) fp) = false ->
      topExcAt (iPccA s1) fp false = false -> evalExpr (@isParcelCompressed type (ACC aSh s1).(Fst)) = false ->
      LineAllowed initLine fwcs specRegions (sMemA s2) (lineAddrOf fp) rpPrev ->
      (ACC aSh s1).(Fst) = pktParcel (fetchPktOf rpPrev) lastParcel ->
      ACC aPktD s1 = fetchPktOf rp -> LineAllowed initLine fwcs specRegions (sMemA s2) (ACC aAligned s1) rp ->
      FetchAllowedInst initLine fwcs specRegions (sMemA s2) (pccWithAddr (iPccA s1) fp) (ACC aFo s1).
  Proof.
    intros s1 s2 fp rp rpPrev Hpok Hpre Hsh Hpc Ho Hnext Hexc Hx Ht Hu HlaP HshLow HpD Hla.
    destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
    pose proof lineBytes_parcels as HL2.
    assert (HlA : ACC aAligned s1 = evalExpr (memNextLineAddr (Var type Addr fp)))
      by (rewrite (ACC aAligned_eq s1), Hnext; apply lineAddr_nextLine).
    rewrite HlA in Hla.
    assert (HiCI : ACC aIsCompI s1 = false) by (unfold aIsCompI; rewrite and2nv_eval, Hsh; reflexivity).
    pose proof (aTop_eq s1 fp false Hpok Hpc HiCI) as Htop; rewrite Ht in Htop.
    assert (HpX : ACC aPktExc s1 = preExcAt (iPccA s1) fp).
    { unfold aPktExc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact Hexc. }
    assert (Hlow : ACC aLow s1 = pktParcel (fetchPktOf rpPrev) lastParcel).
    { unfold aLow; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh; exact HshLow. }
    assert (Hcross : ACC aCross s1 = false) by (unfold aCross; rewrite and3n_eval, Hsh; reflexivity).
    assert (Hhigh : ACC aHigh s1 = pktParcel (fetchPktOf rp) Zmod.zero).
    { unfold aHigh; rewrite ITE0_eval, notVar_eval, Hcross; cbn [negb]; rewrite HpD.
      unfold aHiIdx; rewrite ITE0_eval, notVar_eval, Hsh; cbn [negb]; reflexivity. }
    assert (Hraw : ACC aRaw s1 = implWord (pktParcel (fetchPktOf rp) Zmod.zero) (pktParcel (fetchPktOf rpPrev) lastParcel))
      by (unfold aRaw; rewrite Hhigh, Hlow; reflexivity).
    assert (Hc0 : evalExpr (@isCompressed type (specWord fp (specPkt fp rpPrev))) = false).
    { rewrite (isCompressed_lowParcel _ (pktParcel (fetchPktOf rpPrev) lastParcel)); [rewrite <- HshLow; exact Hu |].
      apply specWord_low; rewrite lastParcel_unsigned; lia. }
    unfold FetchAllowedInst; cbv zeta.
    rewrite pccWithAddr_addr, specPreFault_eq, Hx, pccTopOf_withAddr.
    exists rpPrev, rp; split; [exact HlaP |].
    unfold specFetchRd; cbv zeta.
    rewrite specReads2_eval, specTopExc_eq, Hc0, Ht, specCrosses_eval, Hc0, specCross_last by exact Ho.
    cbn [negb andb fst snd].
    split; [intros _; exact Hla |].
    rewrite evalExpr_ITE; change (evalExpr (Var type Bool true)) with true; cbv iota.
    rewrite specWord_straddle by exact Ho.
    rewrite <- Hraw.
    exact (fo_of s1 fp _ false Hpok HpX eq_refl Htop).
  Qed.

  Lemma MemRelC_fetchDeq :
    forall g (s1 s1' : IState) (s2 : SState) mr' A,
      iRegionsA s1' = mr' -> FetchDeqAtL A implRegions (iRegionsA s1) mr' -> MEMC g s1 s2 -> MEMC g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' A Ei Hat Hm.
    unfold MemRelC, MemRel, DevInv in *; rewrite Ei.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    unfold implClintState, implPlicState, implRevState in *.
    rewrite !(regionStateAt_fetchDeqAt _ _ _ _ _ _ _ Hat) by exact I.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    eapply MemRelPre_fetchDeqAt; [exact Hat | exact Hpre].
  Qed.

  (* The components that read neither the frontend nor the wait bits, across a response dequeue *)
  Lemma core_fetchDeq :
    forall g (s1 s1' : IState) (s2 : SState) mr' A,
      iRfA s1' = iRfA s1 -> iMemA s1' = (mr' ,, (iMemA s1).(Snd)) -> iDmA s1' = iDmA s1 -> iMdA s1' = iMdA s1 ->
      FetchDeqAtL A implRegions (iRegionsA s1) mr' ->
      RELG g s1 s2 ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 /\
      MEMC g s1' s2 /\
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' /\
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' A Erf Emem Edm Emd Hat H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    assert (Ei : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
    assert (HP : forall P, (forall r y, P r (clearReadRp r y) = P r y) ->
                   AllPorts P implRegions (iRegionsA s1') = AllPorts P implRegions (iRegionsA s1))
      by (intros P HP; rewrite Ei; exact (AllPorts_fetchDeqAt P HP _ _ _ _ Hat)).
    assert (HR : iRevA s1' = iRevA s1).
    { unfold iRev, implRevState; rewrite Ei.
      rewrite (regionStateAt_fetchDeqAt _ _ _ _ _ _ _ Hat) by exact I; reflexivity. }
    destruct H as [Hrf Hm _ _ _ Ha Hc Hd _ _ _ _ Hrk].
    split; [unfold RfRel in *; rewrite Efl; exact Hrf |].
    split; [exact (MemRelC_fetchDeq g s1 s1' s2 mr' A Ei Hat Hm) |].
    split.
    { eapply AccessRel_frame_ports with (s1 := s1) (s2 := s2); try reflexivity.
      - unfold PortsQuiet; apply HP; intros r y; reflexivity.
      - intros L; unfold PortsReadStaged; apply HP; intros r y; reflexivity.
      - intros L; unfold PortsReadOut; apply HP; intros r y; reflexivity.
      - intros L rq; unfold PortsWriteStaged; apply HP; intros r y; reflexivity.
      - exact HR.
      - unfold iMemSt; rewrite Emem; reflexivity.
      - unfold iRdBufs; rewrite Emem; reflexivity.
      - unfold iRequester; rewrite Emem; reflexivity.
      - unfold iDmSt; rewrite Edm; reflexivity.
      - exact Ha. }
    split; [unfold CnwbRel in *; unfold iDmSt in *; rewrite Edm; exact Hc |].
    split; [unfold DmQueueRel, iDmBuf in *; rewrite Edm; exact Hd |].
    eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2); try reflexivity; [exact HR | exact Hrk].
  Qed.

  (* A stale head leaves fetchBuf and no parcel is assembled any more *)
  Lemma FrontierRel_drop :
    forall (s1 s1' : IState) (s2 : SState) h rest fp,
      iFetchBufA s1 = h :: rest -> iFetchBufA s1' = rest -> fbLiveA s1 h = false ->
      optValid (ACC iCurParcel s1') = false -> ACC iStraddle s1' = ACC iStraddle s1 ->
      ACC iFetchPc s1' = ACC iFetchPc s1 -> fbLiveA s1' = fbLiveA s1 -> iPccA s1' = iPccA s1 ->
      FRONTIER s1 s2 fp -> FRONTIER s1' s2 fp.
  Proof.
    intros s1 s1' s2 h rest fp Efb0 Efb Hst Ecp Estr Efpc Elv Epcc H.
    unfold FrontierRel in *; cbv zeta in *.
    rewrite Efb0 in H; rewrite Efb, Elv, Estr, Efpc, Epcc, Ecp.
    cbn [filter] in H; rewrite Hst in H.
    destruct H as [Hch [Hx [Hm Hal]]].
    split; [exact Hch | split; [exact Hx | split; [| exact Hal]]].
    destruct (optValid (ACC iStraddle s1)); [exact Hm |].
    destruct (filter (fbLiveA s1) rest) as [| f l]; [exact Hm |].
    rewrite andb_false_r; cbn [andb] in Hm; exact Hm.
  Qed.

  Lemma NoLive_drop :
    forall (s1 s1' : IState) h rest,
      iFetchBufA s1 = h :: rest -> iFetchBufA s1' = rest -> fbLiveA s1' = fbLiveA s1 ->
      iD2aA s1' = iD2aA s1 -> iInstBufA s1' = iInstBufA s1 -> iExecEpochA s1' = iExecEpochA s1 ->
      ACC NoLive s1 -> ACC NoLive s1'.
  Proof.
    intros s1 s1' h rest Efb0 Efb Elv Ed2a Eib Eep [N1 [N2 N3]].
    unfold NoLive, daLive, aiLive in *; rewrite Ed2a, Eib, Eep.
    split; [exact N1 | split; [exact N2 |]].
    rewrite Efb, Elv; rewrite Efb0 in N3; exact (Forall_inv_tail N3).
  Qed.

  (* The relation after dropping a stale head; the memory side is given by the caller *)
  Lemma asm_drop_rel :
    forall g (s1 s1' : IState) (s2 : SState) m,
      FASM s1 s1' m (ACC aFDrop s1) ->
      (ACC aHead s1).(Snd).(Fst) = true -> fbLiveA s1 (aEA s1) = false ->
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 ->
      MEMC g s1' s2 ->
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' ->
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 ->
      ACC NoFenceIWait s1' = ACC NoFenceIWait s1 ->
      (AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1) ->
       AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1')) ->
      (iFetchBufA s1' = tl (iFetchBufA s1) -> fbLiveA s1' = fbLiveA s1 -> FRREL s1' s2) ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 m [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]] Hv Hst Crf Cm Ca Cc Cd Crk HNF HW Cfr H.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Eib : iInstBufA s1' = iInstBufA s1) by (unfold iInstBuf; rewrite Efe; reflexivity).
    assert (Epe : ACC iPredEpoch s1' = ACC iPredEpoch s1) by (unfold iPredEpoch; rewrite Efe; reflexivity).
    assert (Ecp : optValid (ACC iCurParcel s1') = false) by (unfold iCurParcel; rewrite Efe; reflexivity).
    assert (Estr : ACC iStraddle s1' = ACC iStraddle s1) by (unfold iStraddle; rewrite Efe; reflexivity).
    assert (Efpc : ACC iFetchPc s1' = ACC iFetchPc s1) by (unfold iFetchPc; rewrite Efe; reflexivity).
    assert (Edl : daLiveA s1' = daLiveA s1) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA s1' = aiLiveA s1) by (unfold aiLive; rewrite Eep; reflexivity).
    assert (Elv : fbLiveA s1' = fbLiveA s1) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
    destruct H as [_ _ Hl Hrp He' _ _ _ Hfe Hs Hfr Hwf].
    destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (fb_head s1 W1a Hv) as [rest [Efb0 Erest]].
    assert (Efb : iFetchBufA s1' = rest).
    { unfold iFetchBuf; rewrite Efe.
      change (fifo_to_list (fifoDeqState (FBF s1)) = rest); exact Erest. }
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - unfold FenceRel in *; rewrite HNF, Efip, Estr.
      pose proof (NoLive_drop s1 s1' _ rest Efb0 Efb Elv Ed2a Eib Eep) as HNL.
      destruct Hfe as [Hf1 [Hf2 Hf3]]; split; [| split; [| exact Hf3]].
      + intros Hp; destruct (Hf1 Hp) as [Hn Hr]; exact (conj (HNL Hn) Hr).
      + intros Hq; destruct (Hf2 Hq) as [Hp [Hn Hr]]; exact (conj Hp (conj (HNL Hn) Hr)).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel; rewrite Ed2a, Edl, Eib, Eal, Efb, Elv, Eep.
      rewrite Efb0 in F3, F5.
      refine (conj F1 (conj F2 (conj (StalePrefix_tail _ _ _ F3) (conj F4 (conj _ (conj _ _)))))).
      + intros Hx; exact (Forall_inv_tail (F5 Hx)).
      + assert (Elive : liveInstsA g s1' = liveInstsA g s1)
          by (unfold liveInsts; rewrite Ed2a, Eib, Edl, Eal; reflexivity).
        unfold LiveChain in *; rewrite Elive, Epcc.
        refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                  (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
        intros p Hp; exact (FrontierRel_drop s1 s1' s2 _ rest p Efb0 Efb Hst Ecp Estr Efpc Elv Epcc Hp).
      + apply Cfr; [rewrite Efb, Efb0; reflexivity | exact Elv].
    - unfold WfRel; rewrite Efb, Epcc, Ed2a, Eib.
      split; [split; [rewrite Efe; exact (fifo_wf_deq _ _ _ W1a) |] |].
      + split; [intros C; rewrite Ecp in C; discriminate C |].
        rewrite Efb0 in W1f.
        split; [exact W1c |]; split; [exact W1d |]; split; [exact W1e | exact (Forall_inv_tail W1f)].
      + split; [rewrite Efe; exact W2 |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact (HW W6)].
    - exact Crk.
  Qed.

  Lemma asm_stale_rel :
    forall g (s1 s1' : IState) (s2 : SState) mr',
      (ACC aPre s1 = true -> mr' = iRegionsA s1) ->
      (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) mr') ->
      FASM s1 s1' (mr' ,, (iMemA s1).(Snd)) (ACC aFDrop s1) ->
      (ACC aHead s1).(Snd).(Fst) = true -> (ACC aPkt s1).(Snd).(Fst) = true -> ACC aMatch s1 = false ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 mr' Hmr1 Hmr2 Hst Hv Hpv Hm H.
    pose proof Hst as [Erf [_ [Emem [Efe [_ [Eex [Edm Emd]]]]]]].
    assert (Hsl : fbLiveA s1 (aEA s1) = false) by (rewrite <- (ACC aMatch_eq s1); exact Hm).
    pose proof H as [_ _ _ _ _ _ _ _ _ _ Hfr0 Hw0 _].
    destruct (fb_head s1 (proj1 (proj1 Hw0)) Hv) as [rest [Efb0 Erest]].
    assert (Efb : iFetchBufA s1' = rest).
    { unfold iFetchBuf; rewrite Efe.
      change (fifo_to_list (fifoDeqState (FBF s1)) = rest); exact Erest. }
    assert (Elv : fbLiveA s1' = fbLiveA s1) by (unfold fbLive, iExecEpoch, iPredEpoch; rewrite Eex, Efe; reflexivity).
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hfr0)))))) as F7.
    destruct (ACC aPre s1) eqn:Hpre.
    - assert (Emem' : iMemA s1' = iMemA s1) by (rewrite Emem, (Hmr1 eq_refl); reflexivity).
      assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem'; reflexivity).
      destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem' Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
      refine (asm_drop_rel g s1 s1' s2 _ Hst Hv Hsl Crf Cm Ca Cc Cd Crk _ _ _ H).
      + unfold NoFenceIWait; rewrite Ereg; reflexivity.
      + rewrite Ereg; exact (fun X => X).
      + intros _ _.
        assert (Hx : excAny (fbFetchExc (aEA s1)) = true) by (rewrite <- (ACC aPre_excAny s1); exact Hpre).
        unfold FetchRespRel in *; rewrite Ereg.
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                     fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r)
          by (unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx; reflexivity).
        rewrite EE, Elv; exact HC.
    - pose proof (Hmr2 eq_refl) as Hat.
      assert (Ei : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
      destruct (core_fetchDeq g s1 s1' s2 mr' _ Erf Emem Edm Emd Hat H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
      pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
      refine (asm_drop_rel g s1 s1' s2 _ Hst Hv Hsl Crf Cm Ca Cc Cd Crk _ _ _ H).
      + unfold NoFenceIWait; rewrite Ei; refine (AllPorts_fetchDeqAt _ _ _ _ _ _ Hat); intros r y; reflexivity.
      + rewrite Ei; intros W; refine (AllPorts_fetchDeqAt_impl _ _ (ACC aAligned s1) _ _ _ _ _ (Hu _) Hat W).
        * intros r y _ [[H1 [H2 [H3 [H4 H5]]]] H6].
          refine (conj (conj H1 (conj H2 (conj _ (conj H4 H5)))) H6).
          intros C; discriminate C.
        * intros r y _ X; exact X.
      + intros _ _.
        assert (Hrp : (fetchRpAt implRegions (iRegionsA s1) (ACC aAligned s1)).(Snd).(Fst) = true)
          by (unfold aPkt in Hpv; rewrite Hpre in Hpv; exact Hpv).
        pose proof (AllPorts_conj _ _ _ _ F7 (fetchRpAt_valid_ports _ _ _ (Hu _) Hrp)) as F7'.
        assert (Hx : excAny (fbFetchExc (aEA s1)) = false) by (rewrite <- (ACC aPre_excAny s1); exact Hpre).
        unfold FetchRespRel; rewrite Ei.
        refine (AllPorts_fetchDeqAt_impl _ _ _ _ _ _ _ _ (Hu _) Hat F7').
        * intros r y Hr [HC Hval]; cbv zeta in HC |- *.
          destruct HC as [C [HC1 [HC2 _]]].
          assert (EE0 : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r =
                        aEA s1 :: fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r).
          { unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx.
            rewrite (ACC aAligned_eq s1) in Hr; rewrite Hr; reflexivity. }
          rewrite EE0 in HC1.
          exists (lineAddrOf (fbPcAddr (aEA s1)) :: C); split; [| split].
          -- change (implFetchAccRqs r y = (rev (map (fun f => lineAddrOf (fbPcAddr f))
                       (fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                          mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r))
                     ++ lineAddrOf (fbPcAddr (aEA s1)) :: C)%list).
             rewrite HC1; cbn [map rev]; rewrite <- app_assoc; reflexivity.
          -- unfold optValid in HC2; rewrite (Hval Hr) in HC2.
             change (S (length C) + 0 = length (Fst (Snd (Fst (Fst y)))))%nat; lia.
          -- intros C0; discriminate C0.
        * intros r y Hr [HC _]; cbv zeta in HC |- *.
          assert (EE : fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1' r =
                       fbInRegion pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                         mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA s1 r).
          { unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx.
            rewrite (ACC aAligned_eq s1) in Hr; rewrite Hr; reflexivity. }
          rewrite EE, Elv; exact HC.
  Qed.
  (* =========================================================================
   * The live-head branches: a parcel that stays in its line (`fStay`), the end of a line
   * (`fEol`: redirect, straddle start or enqueue)
   * ========================================================================= *)

  (* --- The fetch state after the end of a line, component by component --- *)

  Lemma fEol_fbFifo : forall (s1 : IState) l2,
    fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (ACC fEol s1 l2) = fifoDeqState (FBF s1).
  Proof. intros s1 l2; unfold fEol; destruct (ACC aInit s1), (ACC aMis s1 l2); reflexivity. Qed.

  Lemma fEol_curParcel : forall (s1 : IState) l2,
    optValid (fetch_curParcelOpt pcAddrInit fetchCapacity instCapacity (ACC fEol s1 l2)) = false.
  Proof. intros s1 l2; unfold fEol; destruct (ACC aInit s1), (ACC aMis s1 l2); reflexivity. Qed.

  Lemma fEol_straddle : forall (s1 : IState) l2,
    fetch_straddleOpt pcAddrInit fetchCapacity instCapacity (ACC fEol s1 l2) =
    (if ACC aInit s1 then ACC aSomeSh s1 else getDefault (Option StraddleHalf)).
  Proof. intros s1 l2; unfold fEol; destruct (ACC aInit s1), (ACC aMis s1 l2); reflexivity. Qed.

  Lemma fEol_instFifo : forall (s1 : IState) l2,
    fetch_instFifo pcAddrInit fetchCapacity instCapacity (ACC fEol s1 l2) =
    (if ACC aInit s1 then IBF s1 else fifoEnqState (IBF s1) (ACC aAsm s1 l2)).
  Proof. intros s1 l2; unfold fEol; destruct (ACC aInit s1), (ACC aMis s1 l2); reflexivity. Qed.

  Lemma fEol_predEpoch : forall (s1 : IState) l2,
    fetch_predEpoch pcAddrInit fetchCapacity instCapacity (ACC fEol s1 l2) =
    (if ACC aMis s1 l2 then ACC aNpe s1 else ACC iPredEpoch s1).
  Proof. intros s1 l2; unfold fEol; destruct (ACC aInit s1), (ACC aMis s1 l2); reflexivity. Qed.

  Lemma fEol_pc : forall (s1 : IState) l2,
    fetch_pc pcAddrInit fetchCapacity instCapacity (ACC fEol s1 l2) = (if ACC aMis s1 l2 then l2 else ACC iFetchPc s1).
  Proof. intros s1 l2; unfold fEol; destruct (ACC aInit s1), (ACC aMis s1 l2); reflexivity. Qed.

  (* --- The assembled instruction's fault, prediction need and sequential PC --- *)

  Lemma aFault_excAny : forall s1 : IState, ACC aFault s1 = excAny (ACC aComb s1).
  Proof.
    intros s1; unfold aFault; generalize (ACC aComb s1); intros [t [sl [p [b []]]]]; destruct t, sl, p, b; reflexivity.
  Qed.

  Lemma foFault_aFo : forall s1 : IState, foFault (ACC aFo s1) = ACC aFault s1.
  Proof. intros s1; rewrite aFault_excAny; unfold foFault, foExc; rewrite aFo_eq; reflexivity. Qed.

  Lemma aFault_false : forall s1 : IState, ACC aFault s1 = false -> excAny (ACC aPktExc s1) = false /\ ACC aTop s1 = false.
  Proof.
    intros s1 H; rewrite aFault_excAny, aComb_eq in H; revert H; unfold excAny.
    generalize (ACC aPktExc s1) (ACC aTop s1); intros [t [sl [p [b []]]]] tp; cbn [Fst Snd].
    destruct t, sl, p, b, tp; intros H; first [discriminate H | split; reflexivity].
  Qed.

  Lemma needsPred_aFo : forall s1 : IState, needsPredOf (foInst (ACC aFo s1)) = ACC aNeeds s1.
  Proof. intros s1; unfold needsPredOf, foInst, aNeeds, aPb; rewrite aFo_eq; reflexivity. Qed.

  Lemma seqPc_aFo :
    forall (s1 : IState) p, ACC aInstPc s1 = p -> evalExpr (@isCompressed type (ACC aExp s1)) = ACC aIsCompI s1 ->
      seqPcOf p (foInst (ACC aFo s1)) = ACC aSeqPc s1.
  Proof.
    intros s1 p Hpc Hc; unfold foInst; rewrite aFo_eq; cbn [Fst Snd].
    unfold seqPcOf, aSeqPc, aStep; rewrite Hpc.
    apply Zmod.unsigned_inj; rewrite !to_Z_Add2, !to_Z_Var, !evalExpr_ITE, Hc.
    change (evalExpr (Var type Bool (ACC aIsCompI s1))) with (ACC aIsCompI s1); reflexivity.
  Qed.

  (* A parcel that is not the last of its instruction's line cannot start a straddle *)
  Lemma init_false_of_last :
    forall s1 : IState, evalExpr (isAllOnes (Var type (Bit LgFetchParcels) (ACC aLastP s1))) = false -> ACC aInit s1 = false.
  Proof.
    intros s1 Hlast; unfold aInit; rewrite and2_eval.
    destruct (ACC aCross s1) eqn:Hc; [exfalso | reflexivity].
    unfold aCross in Hc; rewrite and3n_eval in Hc.
    apply andb_prop in Hc as [Hc HL]; apply andb_prop in Hc as [Hsh HiC]; apply negb_true_iff in Hsh, HiC.
    unfold aLastP in Hlast; rewrite ITE0_eval, notVar_eval, Hsh in Hlast; cbn [negb] in Hlast.
    rewrite evalExpr_ITE, or2v_eval, HiC, HL in Hlast; cbn [orb] in Hlast.
    change (evalExpr (Var type (Bit LgFetchParcels) (ACC aK s1))) with (ACC aK s1) in Hlast.
    unfold aIsLast in HL; rewrite HL in Hlast; discriminate Hlast.
  Qed.

  Lemma aMis_false : forall (s1 : IState) l2, ACC aMis s1 l2 = false -> fbPredPc (aEA s1) = l2.
  Proof.
    intros s1 l2 H; unfold aMis in H; rewrite notE_eval, eqAddrE_eval in H.
    apply negb_false_iff, Zmod.eqb_eq in H; exact H.
  Qed.

  (* The instruction PC and the sequential PC are even *)
  Lemma aInstPc_even : forall s1 : IState, pcAligned (ACC aInstPc s1).
  Proof.
    intros s1.
    assert (HaA : Zmod.unsigned (ACC aAligned s1) mod 2 ^ LgLineBytes = 0)
      by (rewrite (ACC aAligned_eq s1); apply lineAddr_aligned).
    unfold aInstPc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
    destruct (ACC aHasSh s1); [| exact (parcelAddr_even _ _ HaA)].
    apply pcAligned_iff.
    pose proof LgLineBytes_lt_AddrSz as HLA; pose proof LgLineBytes_nonneg as HLn.
    pose proof lineBytes_parcels as HL2; pose proof parcels_ge2 as HF2; pose proof lineBytes_lt_addrBytes as HLB.
    pose proof lineBytes_pos as Hlb; pose proof addrBytes_pos as Hab.
    assert (Hd2 : (2 | 2 ^ AddrSz)).
    { exists (2 ^ (AddrSz - 1)); rewrite Z.mul_comm, <- Z.pow_succ_r by lia; f_equal; lia. }
    assert (HdL : (2 | 2 ^ LgLineBytes)) by (exists (2 ^ LgFetchParcels); lia).
    assert (Heven : Zmod.unsigned (ACC aAligned s1) mod 2 = 0)
      by (rewrite <- (Z.mod_mod_divide _ _ _ HdL), HaA; reflexivity).
    rewrite (to_Z_Sub AddrSz _ _ ltac:(lia)), to_Z_Var, to_Z_const, (Z.mod_small 2) by lia.
    rewrite (Z.mod_mod_divide _ _ _ Hd2).
    change (Zmod.to_Z (ACC aAligned s1)) with (Zmod.unsigned (ACC aAligned s1)).
    pose proof (Z.div_mod (Zmod.unsigned (ACC aAligned s1)) 2 ltac:(lia)) as D1.
    pose proof (Z.div_mod (Zmod.unsigned (ACC aAligned s1) - 2) 2 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (Zmod.unsigned (ACC aAligned s1) - 2) 2 ltac:(lia)) as B2.
    lia.
  Qed.

  Lemma seqPc_even : forall s1 : IState, pcAligned (ACC aSeqPc s1).
  Proof. intros s1; unfold aSeqPc, aStep; exact (pcAligned_seq _ _ (aInstPc_even s1)). Qed.

  (* --- Liveness: a live head makes every fetchBuf entry live and rules out a fence.i wait --- *)

  Lemma fb_all_live :
    forall g (s1 : IState) (s2 : SState) rest,
      RELG g s1 s2 -> iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      Forall (fun f => fbLiveA s1 f = true) rest.
  Proof.
    intros g s1 s2 rest Hg Efb Hl.
    pose proof Hg as [_ _ _ _ _ _ _ _ _ _ [_ [_ [F3 _]]] _ _].
    rewrite Efb in F3; exact (StalePrefix_live_head _ _ _ F3 Hl).
  Qed.

  Lemma fence_live :
    forall g (s1 s1' : IState) (s2 : SState) rest,
      RELG g s1 s2 -> iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      iFenceIPendingA s1' = iFenceIPendingA s1 -> ACC NoFenceIWait s1' = ACC NoFenceIWait s1 ->
      FenceRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1'.
  Proof.
    intros g s1 s1' s2 rest Hg Efb Hl Efip HNF.
    pose proof Hg as [_ _ _ _ _ _ _ _ Hfe _ _ _ _].
    assert (HNL : ~ ACC NoLive s1).
    { intros [_ [_ N3]]; rewrite Efb in N3; rewrite (Forall_inv N3) in Hl; discriminate Hl. }
    destruct Hfe as [Hf1 [Hf2 Hf3]].
    assert (Hfip : iFenceIPendingA s1 = false).
    { destruct (iFenceIPendingA s1) eqn:E; [exfalso; exact (HNL (proj1 (Hf1 eq_refl))) | reflexivity]. }
    unfold FenceRel; rewrite Efip, Hfip, HNF.
    split; [intros C; discriminate C | split; [intros C; exfalso; exact (HNL (proj1 (proj2 (Hf2 C)))) |]].
    intros G1 e G2 Hc Hfi; destruct (Hf3 G1 e G2 Hc Hfi) as [Hp _]; rewrite Hfip in Hp; discriminate Hp.
  Qed.

  (* --- Fetch responses after the head is dropped (and its response dequeued unless it was
   * prefaulted); the surviving entries may be less live than before --- *)

  Lemma FetchRespRel_drop :
    forall (s1 s1' : IState) (s2 : SState) rest,
      iFetchBufA s1 = aEA s1 :: rest -> iFetchBufA s1' = rest ->
      (forall f, In f rest -> fbLiveA s1' f = true -> fbLiveA s1 f = true) ->
      (ACC aPre s1 = true -> iRegionsA s1' = iRegionsA s1) ->
      (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) (iRegionsA s1')) ->
      (ACC aPkt s1).(Snd).(Fst) = true ->
      FRREL s1 s2 -> FRREL s1' s2.
  Proof.
    intros s1 s1' s2 rest Efb0 Efb Hlv Hr1 Hr2 Hpv F7.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    assert (Hin : forall r f E', ACC fbInRegion s1' r = f :: E' -> In f rest).
    { intros r f E' HE; unfold fbInRegion in HE; rewrite Efb in HE.
      assert (HIn : In f (f :: E')) by (left; reflexivity).
      rewrite <- HE in HIn; exact (proj1 (proj1 (filter_In _ _ _) HIn)). }
    destruct (ACC aPre s1) eqn:Hpre.
    - pose proof (Hr1 eq_refl) as Ereg.
      assert (Hx : excAny (fbFetchExc (aEA s1)) = true) by (rewrite <- (ACC aPre_excAny s1); exact Hpre).
      unfold FetchRespRel in *; rewrite Ereg.
      revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
      assert (EE : ACC fbInRegion s1' r = ACC fbInRegion s1 r)
        by (unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx; reflexivity).
      destruct HC as [C [HC1 [HC2 HC3]]]; exists C; rewrite EE.
      split; [exact HC1 | split; [exact HC2 |]].
      intros Hval; destruct (HC3 Hval) as [f [E' [HE HL]]]; exists f, E'; split; [exact HE |].
      intros Hl; apply HL, (Hlv f (Hin r f E' ltac:(rewrite EE; exact HE))); exact Hl.
    - pose proof (Hr2 eq_refl) as Hat.
      assert (Hrp : (fetchRpAt implRegions (iRegionsA s1) (ACC aAligned s1)).(Snd).(Fst) = true)
        by (unfold aPkt in Hpv; rewrite Hpre in Hpv; exact Hpv).
      pose proof (AllPorts_conj _ _ _ _ F7 (fetchRpAt_valid_ports _ _ _ (Hu _) Hrp)) as F7'.
      assert (Hx : excAny (fbFetchExc (aEA s1)) = false) by (rewrite <- (ACC aPre_excAny s1); exact Hpre).
      unfold FetchRespRel.
      refine (AllPorts_fetchDeqAt_impl _ _ _ _ _ _ _ _ (Hu _) Hat F7').
      + intros r y Hr [HC Hval]; cbv zeta in HC |- *.
        destruct HC as [C [HC1 [HC2 _]]].
        assert (EE0 : ACC fbInRegion s1 r = aEA s1 :: ACC fbInRegion s1' r).
        { unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx.
          rewrite (ACC aAligned_eq s1) in Hr; rewrite Hr; reflexivity. }
        rewrite EE0 in HC1.
        exists (lineAddrOf (fbPcAddr (aEA s1)) :: C); split; [| split].
        * change (implFetchAccRqs r y = (rev (map (fun f => lineAddrOf (fbPcAddr f)) (ACC fbInRegion s1' r))
                     ++ lineAddrOf (fbPcAddr (aEA s1)) :: C)%list).
          rewrite HC1; cbn [map rev]; rewrite <- app_assoc; reflexivity.
        * unfold optValid in HC2; rewrite (Hval Hr) in HC2.
          change (S (length C) + 0 = length (Fst (Snd (Fst (Fst y)))))%nat; lia.
        * intros C0; discriminate C0.
      + intros r y Hr [HC _]; cbv zeta in HC |- *.
        assert (EE : ACC fbInRegion s1' r = ACC fbInRegion s1 r).
        { unfold fbInRegion; rewrite Efb, Efb0; cbn [filter]; rewrite Hx.
          rewrite (ACC aAligned_eq s1) in Hr; rewrite Hr; reflexivity. }
        destruct HC as [C [HC1 [HC2 HC3]]]; exists C; rewrite EE.
        split; [exact HC1 | split; [exact HC2 |]].
        intros Hval; destruct (HC3 Hval) as [f [E' [HE HL]]]; exists f, E'; split; [exact HE |].
        intros Hl; apply HL, (Hlv f (Hin r f E' ltac:(rewrite EE; exact HE))); exact Hl.
  Qed.

  (* --- What the frontier says about a live head: its instruction PC, pre-fault flags,
   * compressedness and (unless a straddle starts) that the spec may fetch the assembled
   * instruction there --- *)

  Lemma head_facts :
    forall g (s1 : IState) (s2 : SState) rest p,
      PccOK s1 -> RELG g s1 s2 -> iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      (ACC aPkt s1).(Snd).(Fst) = true -> FRONTIER s1 s2 p ->
      ACC aInstPc s1 = p /\ pcAligned p /\ ACC aPktExc s1 = preExcAt (iPccA s1) p /\
      evalExpr (@isCompressed type (ACC aExp s1)) = ACC aIsCompI s1 /\
      (ACC aInit s1 = false ->
         FetchAllowedInst initLine fwcs specRegions (sMemA s2) (pccWithAddr (iPccA s1) p) (ACC aFo s1)).
  Proof.
    intros g s1 s2 rest p Hpok Hg Efb Hl Hpv Hfr.
    destruct invariant_fetch as [_ [_ [HC [HI _]]]].
    destruct (ACC aHasSh s1) eqn:Hsh.
    - destruct (frontier_sh s1 s2 p rest Efb Hl Hsh Hfr)
        as [Hpc [Ho [Hnext [Hexc [Hx [Ht [Hu [[rpPrev [HlaP HshLow]] [Hal HpE]]]]]]]]].
      assert (HiCI : ACC aIsCompI s1 = false) by (unfold aIsCompI; rewrite and2nv_eval, Hsh; reflexivity).
      assert (HpX : ACC aPktExc s1 = preExcAt (iPccA s1) p).
      { unfold aPktExc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
        rewrite Hsh; exact Hexc. }
      assert (Hlow : ACC aLow s1 = (ACC aSh s1).(Fst)).
      { unfold aLow; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
        rewrite Hsh; reflexivity. }
      assert (Hpre : ACC aPre s1 = false).
      { rewrite (ACC aPre_excAny s1), <- (ACC aPreExc_eq s1), HpE, Hnext.
        destruct (topExcAt_false_bound _ _ _ Ht) as [Hb _].
        change (if false then CompInstSz / 8 else InstSz / 8) with (InstSz / 8) in Hb.
        rewrite HI, HC in Hb; change (2 ^ Z.log2 ((2 * 8 + 2 * 8) / 8)) with 4 in Hb.
        rewrite (preExcAt_above _ p _ Hx); [exact Hx |].
        rewrite nextLine_last by (first [exact Ho | lia]); lia. }
      split; [exact Hpc | split; [exact Hal | split; [exact HpX | split]]].
      + rewrite HiCI; unfold aExp; rewrite preDecode_isCompressed.
        rewrite (isCompressed_lowParcel _ (ACC aLow s1)); [rewrite Hlow; exact Hu |].
        unfold aRaw.
        change (evalExpr {< Var type (Bit CompInstSz) (ACC aHigh s1), Var type (Bit CompInstSz) (ACC aLow s1) >})
          with (implWord (ACC aHigh s1) (ACC aLow s1)).
        rewrite implWord_unsigned, Z.mul_comm, Z_mod_plus_full, Z.mod_small;
          [reflexivity | exact (bits.unsigned_range (ACC aLow s1) ltac:(lia))].
      + intros _.
        destruct (head_packet g s1 s2 rest Hg Efb Hl Hpre Hpv) as [rp [HpD Hla]].
        exact (allowed_sh s1 s2 p rp rpPrev Hpok Hpre Hsh Hpc Ho Hnext Hexc Hx Ht Hu HlaP HshLow HpD Hla).
    - destruct (frontier_noSh s1 s2 p rest Efb Hl Hsh Hfr) as [Hfp [Hexc Hal]].
      assert (Hpc : ACC aInstPc s1 = p).
      { unfold aInstPc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
        rewrite Hsh, Hfp; reflexivity. }
      assert (HpX : ACC aPktExc s1 = preExcAt (iPccA s1) p).
      { unfold aPktExc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
        rewrite Hsh; exact Hexc. }
      split; [exact Hpc | split; [exact Hal | split; [exact HpX |]]].
      destruct (ACC aPre s1) eqn:Hpre.
      + assert (HpD : ACC aPktD s1 = getDefault FetchPacket) by (unfold aPktD, aPkt; rewrite Hpre; reflexivity).
        assert (HpK : ACC aParcelK s1 = Zmod.zero) by (unfold aParcelK; rewrite HpD; exact (pktParcel_default _)).
        assert (HiC : ACC aIsComp s1 = true)
          by (unfold aIsComp; rewrite HpK, df_isParcelCompressed_eval; vm_compute; reflexivity).
        assert (HiCI : ACC aIsCompI s1 = true) by (unfold aIsCompI; rewrite and2nv_eval, Hsh, HiC; reflexivity).
        assert (Hcross : ACC aCross s1 = false) by (unfold aCross; rewrite and3n_eval, Hsh, HiC; reflexivity).
        assert (Hhigh : ACC aHigh s1 = Zmod.zero).
        { unfold aHigh; rewrite ITE0_eval, notVar_eval, Hcross; cbn [negb]; rewrite HpD; exact (pktParcel_default _). }
        assert (Hlow : ACC aLow s1 = Zmod.zero).
        { unfold aLow; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
          rewrite Hsh; exact HpK. }
        assert (Hraw : ACC aRaw s1 = Zmod.zero) by (unfold aRaw; rewrite Hhigh, Hlow; exact implWord_zero).
        split; [| intros _; exact (allowed_pre s1 s2 p Hpok Hpre Hsh Hpc Hexc Hal)].
        rewrite HiCI; unfold aExp; rewrite Hraw, preDecode_zero; vm_compute; reflexivity.
      + destruct (head_packet g s1 s2 rest Hg Efb Hl Hpre Hpv) as [rp [HpD Hla]].
        destruct (noSh_facts s1 p rp Hpok Hpre Hsh HpD Hfp Hexc) as [_ [_ [_ [_ [Hcomp _]]]]].
        assert (HiCI : ACC aIsCompI s1 = ACC aIsComp s1) by (unfold aIsCompI; rewrite and2nv_eval, Hsh; reflexivity).
        split; [rewrite HiCI; unfold aExp; rewrite preDecode_isCompressed; exact Hcomp |].
        intros Hinit.
        destruct (ACC aCross s1) eqn:Hcross.
        * exact (allowed_lastTop s1 s2 p rp Hpok Hpre Hsh Hcross Hinit HpD Hla Hfp Hexc).
        * exact (allowed_inline s1 s2 p rp Hpok Hpre Hsh Hcross HpD Hla Hfp Hexc).
  Qed.

  (* --- A parcel that stays in its line: the next parcel is the sequential PC, with the
   * head's pre-fault flags --- *)

  Lemma stay_next :
    forall (s1 : IState) (s2 : SState) fp rest,
      iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      evalExpr (isAllOnes (Var type (Bit LgFetchParcels) (ACC aLastP s1))) = false ->
      excAny (ACC aPktExc s1) = false ->
      FRONTIER s1 s2 fp ->
      parcelAddrOf (ACC aAligned s1) (ACC aNextK s1) = ACC aSeqPc s1 /\
      preExcAt (iPccA s1) (ACC aSeqPc s1) = fbFetchExc (aEA s1).
  Proof.
    intros s1 s2 fp rest Efb Hl Hlast HxP H.
    destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
    pose proof lineBytes_parcels as HL2; pose proof parcels_ge2 as HF2.
    pose proof lineBytes_lt_addrBytes as HLB; pose proof (pow2_pos LgFetchParcels HF) as HFp.
    rewrite isAllOnes_eval in Hlast.
    change (evalExpr (Var type (Bit LgFetchParcels) (ACC aLastP s1))) with (ACC aLastP s1) in Hlast.
    pose proof (eqb_invDefault_false _ Hlast) as HlastU.
    assert (HaA : Zmod.unsigned (ACC aAligned s1) mod 2 ^ LgLineBytes = 0)
      by (rewrite (ACC aAligned_eq s1); apply lineAddr_aligned).
    pose proof (aligned_line_bound _ HaA) as HaB.
    assert (HaR : 0 <= Zmod.unsigned (ACC aAligned s1) < 2 ^ AddrSz)
      by exact (bits.unsigned_range (ACC aAligned s1) ltac:(cbv; congruence)).
    assert (HfpR : 0 <= Zmod.unsigned fp < 2 ^ AddrSz) by exact (bits.unsigned_range fp ltac:(cbv; congruence)).
    destruct (ACC aHasSh s1) eqn:Hsh.
    - (* straddle completion: the next parcel is parcel 1 of the head's line *)
      destruct (frontier_sh s1 s2 fp rest Efb Hl Hsh H) as [Hpc [Ho [Hnext [_ [Hx [Ht [_ [_ [Hal HpE]]]]]]]]].
      assert (HiCI : ACC aIsCompI s1 = false) by (unfold aIsCompI; rewrite and2nv_eval, Hsh; reflexivity).
      assert (HlP : ACC aLastP s1 = Zmod.zero) by (unfold aLastP; rewrite ITE0_eval, notVar_eval, Hsh; reflexivity).
      assert (HnK : Zmod.unsigned (ACC aNextK s1) = 1).
      { unfold aNextK; rewrite to_Z_Add2, to_Z_Var, to_Z_const, HlP, Zmod.unsigned_0, Z.add_0_l.
        rewrite Z.mod_mod by lia; apply Z.mod_small; lia. }
      destruct (topExcAt_false_bound _ _ _ Ht) as [Hb _].
      change (if false then CompInstSz / 8 else InstSz / 8) with (InstSz / 8) in Hb.
      rewrite HI, HC in Hb; change (2 ^ Z.log2 ((2 * 8 + 2 * 8) / 8)) with 4 in Hb.
      pose proof (seq_no_wrap fp Ho Hb) as Hb4.
      assert (HaU : Zmod.unsigned (ACC aAligned s1) = Zmod.unsigned fp + 2).
      { rewrite (ACC aAligned_eq s1), Hnext, lineAddr_nextLine; apply nextLine_last; [exact Ho | lia]. }
      assert (HseqU : Zmod.unsigned (ACC aSeqPc s1) = Zmod.unsigned fp + 4).
      { unfold aSeqPc; rewrite to_Z_Add2, !to_Z_Var, Hpc.
        unfold aStep; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aIsCompI s1))) with (ACC aIsCompI s1).
        rewrite HiCI; cbv iota; rewrite to_Z_const, HI, HC; change ((2 * 8 + 2 * 8) / 8) with 4.
        rewrite (Z.mod_small 4) by lia; apply Z.mod_small; addrBound; lia. }
      split.
      + apply Zmod.unsigned_inj; rewrite (parcelAddr_unsigned _ _ HaA), HnK, HaU, HseqU; lia.
      + rewrite <- (ACC aPreExc_eq s1), HpE, Hnext.
        rewrite (preExcAt_above _ fp (ACC aSeqPc s1) Hx) by (rewrite HseqU; lia).
        rewrite (preExcAt_above _ fp (evalExpr (memNextLineAddr (Var type Addr fp))) Hx)
          by (rewrite nextLine_last by (first [exact Ho | lia]); lia).
        reflexivity.
    - destruct (frontier_noSh s1 s2 fp rest Efb Hl Hsh H) as [Hfp [Hexc Hal]].
      assert (Hpc : ACC aInstPc s1 = fp).
      { unfold aInstPc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
        rewrite Hsh, Hfp; reflexivity. }
      assert (HpX : ACC aPktExc s1 = preExcAt (iPccA s1) fp).
      { unfold aPktExc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
        rewrite Hsh; exact Hexc. }
      rewrite HpX in HxP.
      assert (HiCI : ACC aIsCompI s1 = ACC aIsComp s1) by (unfold aIsCompI; rewrite and2nv_eval, Hsh; reflexivity).
      assert (HfpU : Zmod.unsigned fp = Zmod.unsigned (ACC aAligned s1) + 2 * Zmod.unsigned (ACC aK s1))
        by (rewrite Hfp; apply parcelAddr_unsigned; exact HaA).
      pose proof (bits.unsigned_range (ACC aK s1) HF) as Hk.
      assert (HlP : ACC aLastP s1 = (if orb (ACC aIsComp s1) (ACC aIsLast s1) then ACC aK s1 else ACC aK1 s1)).
      { unfold aLastP; rewrite ITE0_eval, notVar_eval, Hsh; cbn [negb]; rewrite evalExpr_ITE, or2v_eval; reflexivity. }
      assert (HisLast : ACC aIsLast s1 = Zmod.eqb (ACC aK s1) (InvDefault (Bit LgFetchParcels)))
        by (unfold aIsLast; rewrite isAllOnes_eval; reflexivity).
      assert (HK1 : Zmod.unsigned (ACC aK s1) + 1 < 2 ^ LgFetchParcels ->
                    Zmod.unsigned (ACC aK1 s1) = Zmod.unsigned (ACC aK s1) + 1).
      { intros Hb; unfold aK1; rewrite to_Z_Add2, to_Z_Var, to_Z_const, (Z.mod_small 1) by lia; apply Z.mod_small; lia. }
      assert (Hpre1 : forall a, preExcAt (iPccA s1) a = preExcAt (iPccA s1) fp -> preExcAt (iPccA s1) a = fbFetchExc (aEA s1))
        by (intros a E; rewrite E, <- (ACC aPreExc_eq s1); symmetry; exact Hexc).
      destruct (ACC aIsComp s1) eqn:HiC.
      + cbn [orb] in HlP; rewrite HlP in HlastU.
        assert (HnK : Zmod.unsigned (ACC aNextK s1) = Zmod.unsigned (ACC aK s1) + 1).
        { unfold aNextK; rewrite to_Z_Add2, to_Z_Var, to_Z_const, HlP.
          rewrite (Z.mod_small 1) by lia; apply Z.mod_small; lia. }
        assert (HseqU : Zmod.unsigned (ACC aSeqPc s1) = Zmod.unsigned fp + 2).
        { unfold aSeqPc; rewrite to_Z_Add2, !to_Z_Var, Hpc.
          unfold aStep; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aIsCompI s1))) with (ACC aIsCompI s1).
          rewrite HiCI; cbv iota; rewrite to_Z_const, HC; change (2 * 8 / 8) with 2.
          rewrite (Z.mod_small 2) by lia; apply Z.mod_small; addrBound; lia. }
        split.
        * apply Zmod.unsigned_inj; rewrite (parcelAddr_unsigned _ _ HaA), HnK, HseqU, HfpU; lia.
        * apply Hpre1, (preExcAt_above _ fp _ HxP); rewrite HseqU; lia.
      + destruct (ACC aIsLast s1) eqn:HiL.
        { exfalso; cbn [orb] in HlP; rewrite HlP in HlastU.
          exact (HlastU (eqb_invDefault_true _ (eq_sym HisLast))). }
        cbn [orb] in HlP; rewrite HlP in HlastU.
        pose proof (eqb_invDefault_false _ (eq_sym HisLast)) as HkL.
        assert (Hk1 : Zmod.unsigned (ACC aK1 s1) = Zmod.unsigned (ACC aK s1) + 1) by (apply HK1; lia).
        assert (HnK : Zmod.unsigned (ACC aNextK s1) = Zmod.unsigned (ACC aK s1) + 1 + 1).
        { unfold aNextK; rewrite to_Z_Add2, to_Z_Var, to_Z_const, HlP, Hk1.
          rewrite (Z.mod_small 1) by lia; apply Z.mod_small; lia. }
        assert (HseqU : Zmod.unsigned (ACC aSeqPc s1) = Zmod.unsigned fp + 4).
        { unfold aSeqPc; rewrite to_Z_Add2, !to_Z_Var, Hpc.
          unfold aStep; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aIsCompI s1))) with (ACC aIsCompI s1).
          rewrite HiCI; cbv iota; rewrite to_Z_const, HI, HC; change ((2 * 8 + 2 * 8) / 8) with 4.
          rewrite (Z.mod_small 4) by lia; apply Z.mod_small; addrBound; lia. }
        split.
        * apply Zmod.unsigned_inj; rewrite (parcelAddr_unsigned _ _ HaA), HnK, HseqU, HfpU; lia.
        * apply Hpre1, (preExcAt_above _ fp _ HxP); rewrite HseqU; lia.
  Qed.

  Lemma frontier_stay :
    forall (s1 s1' : IState) (s2 : SState) fp rest,
      iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      iFetchBufA s1' = iFetchBufA s1 -> fbLiveA s1' = fbLiveA s1 -> ACC iFetchPc s1' = ACC iFetchPc s1 ->
      iPccA s1' = iPccA s1 -> optValid (ACC iStraddle s1') = false -> ACC iCurParcel s1' = ACC aSomeNext s1 ->
      evalExpr (isAllOnes (Var type (Bit LgFetchParcels) (ACC aLastP s1))) = false ->
      excAny (ACC aPktExc s1) = false ->
      FRONTIER s1 s2 fp -> FRONTIER s1' s2 (ACC aSeqPc s1).
  Proof.
    intros s1 s1' s2 fp rest Efb0 Hl Efb Elv Efpc Epcc Estr Ecp Hlast HxP H.
    destruct (stay_next s1 s2 fp rest Efb0 Hl Hlast HxP H) as [Hn1 Hn2].
    pose proof H as H0; unfold FrontierRel in H0; cbv zeta in H0.
    rewrite Efb0 in H0; cbn [filter] in H0; rewrite Hl in H0; cbv beta iota in H0; try rewrite Hl in H0; cbn [andb] in H0.
    destruct H0 as [Hch [Hx _]].
    unfold FrontierRel; cbv zeta.
    rewrite Efb, Elv, Efpc, Epcc, Estr, Ecp, Efb0; cbn [filter]; rewrite Hl; cbv beta iota; try rewrite Hl; cbn [andb].
    split; [exact Hch | split; [exact Hx | split; [| exact (seqPc_even s1)]]].
    change (optValid (ACC aSomeNext s1)) with true; cbv iota.
    change (optData (ACC aSomeNext s1)) with (ACC aNextK s1).
    rewrite <- (ACC aAligned_eq s1).
    split; [exact Hn1 | exact (eq_sym Hn2)].
  Qed.

  (* The relation after a parcel that stays in its line *)
  Lemma asm_stay_rel :
    forall g (s1 s1' : IState) (s2 : SState) cp,
      PccOK s1 -> FASM s1 s1' (iMemA s1) (ACC fStay s1 cp (ACC aSeqPc s1)) ->
      (ACC aHead s1).(Snd).(Fst) = true -> (ACC aPkt s1).(Snd).(Fst) = true -> ACC aMatch s1 = true ->
      ACC aIbFull s1 = false ->
      evalExpr (isAllOnes (Var type (Bit LgFetchParcels) (ACC aLastP s1))) = false ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 cp Hpok Hst Hv Hpv Hm Hf Hlast H.
    pose proof Hst as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
    destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    pose proof (init_false_of_last s1 Hlast) as Hinit.
    assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Efb : iFetchBufA s1' = iFetchBufA s1) by (unfold iFetchBuf; rewrite Efe; reflexivity).
    assert (Epe : ACC iPredEpoch s1' = ACC iPredEpoch s1) by (unfold iPredEpoch; rewrite Efe; reflexivity).
    assert (Ecp : ACC iCurParcel s1' = ACC aSomeNext s1) by (unfold iCurParcel; rewrite Efe; reflexivity).
    assert (Estr : optValid (ACC iStraddle s1') = false) by (unfold iStraddle; rewrite Efe; reflexivity).
    assert (Efpc : ACC iFetchPc s1' = ACC iFetchPc s1) by (unfold iFetchPc; rewrite Efe; reflexivity).
    assert (Edl : daLiveA s1' = daLiveA s1) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA s1' = aiLiveA s1) by (unfold aiLive; rewrite Eep; reflexivity).
    assert (Elv : fbLiveA s1' = fbLiveA s1) by (unfold fbLive; rewrite Eep, Epe; reflexivity).
    assert (HNF : ACC NoFenceIWait s1' = ACC NoFenceIWait s1) by (unfold NoFenceIWait; rewrite Ereg; reflexivity).
    pose proof H as [_ _ Hl Hrp He' _ _ _ _ Hs Hfr Hwf _].
    destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (head_live_list s1 W1a Hv Hm) as [rest [Efb0 [Hlh _]]].
    assert (Eib : iInstBufA s1' = (iInstBufA s1 ++ [ACC aAsm s1 (ACC aSeqPc s1)])%list).
    { unfold iInstBuf; rewrite Efe.
      change (fifo_to_list (fifoEnqState (IBF s1) (ACC aAsm s1 (ACC aSeqPc s1))) =
              (fifo_to_list (IBF s1) ++ [ACC aAsm s1 (ACC aSeqPc s1)])%list).
      exact (fifo_to_list_enq_nf _ _ _ _ W2 Hf). }
    assert (Ha : aiLiveA s1 (ACC aAsm s1 (ACC aSeqPc s1)) = true)
      by (unfold aiLive; change (Zmod.eqb (iExecEpochA s1) (iExecEpochA s1) = true); apply Zmod.eqb_refl).
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - exact (fence_live g s1 s1' s2 rest H Efb0 Hlh Efip HNF).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel; rewrite Ed2a, Edl, Eib, Eal, Efb, Elv, Eep.
      refine (conj F1 (conj (StalePrefix_snoc _ _ _ F2 Ha) (conj F3 (conj _ (conj _ (conj _ _)))))).
      + intros Hx; apply Forall_app; split; [exact (F4 Hx) | constructor; [exact Ha | constructor]].
      + intros _; rewrite Efb0; constructor; [exact (proj1 (andb_prop _ _ Hlh)) |].
        refine (Forall_impl _ _ (fb_all_live g s1 s2 rest H Efb0 Hlh)); intros f Hf'; exact (proj1 (andb_prop _ _ Hf')).
      + assert (Elive : liveInstsA g s1' = (liveInstsA g s1 ++ [(ACC aFo s1, ACC aSeqPc s1)])%list).
        { unfold liveInsts; rewrite Ed2a, Eib, Edl, Eal, filter_app, map_app, app_assoc.
          cbn [filter map]; rewrite Ha; reflexivity. }
        unfold LiveChain in *; rewrite Elive, Epcc.
        apply LiveChainG_snoc.
        refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                  (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
        intros p Hp.
        destruct (head_facts g s1 s2 rest p Hpok H Efb0 Hlh Hpv Hp) as [Hpc [Hal [HpX [Hcomp Hallow]]]].
        split; [exact (Hallow Hinit) |].
        rewrite foFault_aFo; destruct (ACC aFault s1) eqn:Hfault; [exact I |].
        split; [intros _; symmetry; exact (seqPc_aFo s1 p Hpc Hcomp) |].
        exact (frontier_stay s1 s1' s2 p rest Efb0 Hlh Efb Elv Efpc Epcc Estr Ecp Hlast
                 (proj1 (aFault_false s1 Hfault)) Hp).
      + exact (FetchRespRel_ib pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                 initLine fwcs s1 s1' s2 Efb Epe Eep Ereg F7).
    - unfold WfRel; rewrite Efb, Epcc, Ed2a, Eib, Ereg.
      split; [split; [rewrite Efe; exact W1a |] |].
      + split; [intros _; rewrite Efb0; discriminate |].
        split; [exact W1c |]; split; [exact W1d |]; split; [| exact W1f].
        apply Forall_app; split; [exact W1e | constructor; [exact (seqPc_even s1) | constructor]].
      + split; [rewrite Efe; exact (fifo_wf_enq _ _ _ _ W2) |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact W6].
    - exact Crk.
  Qed.

  (* --- The end of a line --- *)

  (* A straddle starts: the frontier stays at the 4-byte instruction's PC, now described by the
   * saved half *)
  Lemma frontier_strad :
    forall g (s1 s1' : IState) (s2 : SState) fp rest l2,
      PccOK s1 -> RELG g s1 s2 -> iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      (ACC aPkt s1).(Snd).(Fst) = true -> ACC aInit s1 = true -> l2 = ACC aNextLine s1 ->
      iFetchBufA s1' = rest -> iPccA s1' = iPccA s1 -> ACC iStraddle s1' = ACC aSomeSh s1 ->
      filter (fbLiveA s1') rest = (if ACC aMis s1 l2 then [] else filter (fbLiveA s1) rest) ->
      ACC iFetchPc s1' = (if ACC aMis s1 l2 then l2 else ACC iFetchPc s1) ->
      FRONTIER s1 s2 fp -> FRONTIER s1' s2 fp.
  Proof.
    intros g s1 s1' s2 fp rest l2 Hpok Hg Efb0 Hl Hpv Hinit Hl2 Efb Epcc Estr Hlive Efpc H.
    destruct invariant_fetch as [HN [HL [HC [HI [_ [_ [_ [HF _]]]]]]]].
    pose proof lineBytes_parcels as HL2; pose proof parcels_ge2 as HF2.
    pose proof invariant_LineBytes as HLB; pose proof lineBytes_lt_addrBytes as HLA; pose proof lineBytes_pos as Hlb.
    unfold aInit in Hinit; rewrite and2_eval in Hinit; apply andb_prop in Hinit as [Hcross Htop].
    apply negb_true_iff in Htop.
    unfold aCross in Hcross; rewrite and3n_eval in Hcross.
    apply andb_prop in Hcross as [Hc HiL]; apply andb_prop in Hc as [Hsh HiC]; apply negb_true_iff in Hsh, HiC.
    destruct (frontier_noSh s1 s2 fp rest Efb0 Hl Hsh H) as [Hfp [Hexc Hal]].
    assert (Hpre : ACC aPre s1 = false).
    { destruct (ACC aPre s1) eqn:Hpre; [exfalso | reflexivity].
      assert (HpD : ACC aPktD s1 = getDefault FetchPacket) by (unfold aPktD, aPkt; rewrite Hpre; reflexivity).
      assert (HpK : ACC aParcelK s1 = Zmod.zero) by (unfold aParcelK; rewrite HpD; exact (pktParcel_default _)).
      unfold aIsComp in HiC; rewrite HpK, df_isParcelCompressed_eval in HiC; vm_compute in HiC; discriminate HiC. }
    destruct (head_packet g s1 s2 rest Hg Efb0 Hl Hpre Hpv) as [rp [HpD Hla]].
    assert (HaA : Zmod.unsigned (ACC aAligned s1) mod 2 ^ LgLineBytes = 0)
      by (rewrite (ACC aAligned_eq s1); apply lineAddr_aligned).
    unfold aIsLast in HiL; rewrite isAllOnes_eval in HiL.
    change (evalExpr (Var type (Bit LgFetchParcels) (ACC aK s1))) with (ACC aK s1) in HiL.
    pose proof (eqb_invDefault_true _ HiL) as HkL.
    assert (HkLast : ACC aK s1 = lastParcel)
      by (apply Zmod.unsigned_inj; rewrite HkL, lastParcel_unsigned; reflexivity).
    assert (Ho : Zmod.unsigned fp mod 2 ^ LgLineBytes = 2 ^ LgLineBytes - 2)
      by (rewrite Hfp, (parcelAddr_off _ _ HaA), HkL; lia).
    assert (HiCI : ACC aIsCompI s1 = false) by (unfold aIsCompI; rewrite and2nv_eval, Hsh, HiC; reflexivity).
    assert (Hpc : ACC aInstPc s1 = fp).
    { unfold aInstPc; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aHasSh s1))) with (ACC aHasSh s1).
      rewrite Hsh, Hfp; reflexivity. }
    pose proof (aTop_eq s1 fp false Hpok Hpc HiCI) as HtopE; rewrite Htop in HtopE.
    assert (HpX : excAny (preExcAt (iPccA s1) fp) = false)
      by (rewrite <- Hexc, (ACC aPreExc_eq s1), <- (ACC aPre_excAny s1); exact Hpre).
    assert (HlA : lineAddrOf fp = ACC aAligned s1) by (rewrite Hfp; apply lineAddr_parcelAddr; exact HaA).
    assert (Hnl : ACC aNextLine s1 = evalExpr (memNextLineAddr (Var type Addr fp))).
    { apply Zmod.unsigned_inj; rewrite nextLine_unsigned, HlA.
      unfold aNextLine; rewrite to_Z_Add2, to_Z_Var, to_Z_const, HLB.
      rewrite (Z.mod_small (2 ^ LgLineBytes)) by (addrBound; lia); reflexivity. }
    pose proof H as H0; unfold FrontierRel in H0; cbv zeta in H0.
    rewrite Efb0 in H0; cbn [filter] in H0; rewrite Hl in H0; cbv beta iota in H0; try rewrite Hl in H0; cbn [andb] in H0.
    destruct H0 as [Hch [Hx _]].
    unfold FrontierRel; cbv zeta.
    rewrite Efb, Epcc, Estr, Efpc, Hlive.
    change (optValid (ACC aSomeSh s1)) with true; cbv iota.
    change (optData (ACC aSomeSh s1)) with (ACC aNewSh s1).
    change ((ACC aNewSh s1).(Snd).(Fst)) with (ACC aPreExc s1).
    change ((ACC aNewSh s1).(Fst)) with (ACC aParcelK s1).
    refine (conj _ (conj _ (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) Hal))).
    - destruct (ACC aMis s1 l2); [exact I | exact (FbChain_tail _ _ _ Hch)].
    - destruct (ACC aMis s1 l2); [constructor | exact (Forall_inv_tail Hx)].
    - intros E; apply (f_equal Zmod.unsigned) in E.
      pose proof (lineAddr_aligned fp) as HA0; rewrite E, Ho in HA0; lia.
    - rewrite Hfp, (packetParcel_parcelAddr _ _ HaA); exact HkLast.
    - exact Hexc.
    - exact HpX.
    - exact (eq_sym HtopE).
    - exact HiC.
    - exists rp; split; [rewrite HlA; exact Hla |].
      unfold aParcelK; rewrite HpD, HkLast; reflexivity.
    - destruct (ACC aMis s1 l2) eqn:Hmis; cbv beta iota; [rewrite Hl2; exact Hnl |].
      pose proof (aMis_false s1 l2 Hmis) as Hpp; rewrite Hl2, Hnl in Hpp.
      destruct (filter (fbLiveA s1) rest) as [| f l]; cbn [FbChain] in Hch.
      + rewrite <- Hch; exact Hpp.
      + rewrite <- (proj1 Hch); exact Hpp.
  Qed.

  (* An instruction ends the line: the frontier is its predicted PC *)
  Lemma frontier_eol :
    forall (s1 s1' : IState) (s2 : SState) fp rest l2,
      iFetchBufA s1 = aEA s1 :: rest -> fbLiveA s1 (aEA s1) = true ->
      iFetchBufA s1' = rest -> iPccA s1' = iPccA s1 -> optValid (ACC iStraddle s1') = false ->
      optValid (ACC iCurParcel s1') = false ->
      filter (fbLiveA s1') rest = (if ACC aMis s1 l2 then [] else filter (fbLiveA s1) rest) ->
      ACC iFetchPc s1' = (if ACC aMis s1 l2 then l2 else ACC iFetchPc s1) ->
      pcAligned l2 -> FRONTIER s1 s2 fp -> FRONTIER s1' s2 l2.
  Proof.
    intros s1 s1' s2 fp rest l2 Efb0 Hl Efb Epcc Estr Ecp Hlive Efpc Hal H.
    pose proof H as H0; unfold FrontierRel in H0; cbv zeta in H0.
    rewrite Efb0 in H0; cbn [filter] in H0; rewrite Hl in H0; cbv beta iota in H0; try rewrite Hl in H0; cbn [andb] in H0.
    destruct H0 as [Hch [Hx _]].
    unfold FrontierRel; cbv zeta.
    rewrite Efb, Epcc, Estr, Ecp, Efpc, Hlive, andb_false_r.
    refine (conj _ (conj _ (conj _ Hal))).
    - destruct (ACC aMis s1 l2); [exact I | exact (FbChain_tail _ _ _ Hch)].
    - destruct (ACC aMis s1 l2); [constructor | exact (Forall_inv_tail Hx)].
    - destruct (ACC aMis s1 l2) eqn:Hmis; cbv beta iota; [reflexivity |].
      pose proof (aMis_false s1 l2 Hmis) as Hpp.
      destruct (filter (fbLiveA s1) rest) as [| f l]; cbn [FbChain] in Hch.
      + rewrite <- Hch; exact Hpp.
      + rewrite <- (proj1 Hch); exact Hpp.
  Qed.

  (* The relation after the end of a line: the head is dropped (with its response), no parcel is
   * current, a misprediction redirects fetch, and either a straddle is saved or the instruction
   * is enqueued with the level-2 prediction `l2` *)
  Lemma asm_eol_rel :
    forall g (s1 s1' : IState) (s2 : SState) l2 mr',
      PccOK s1 -> (ACC aPre s1 = true -> mr' = iRegionsA s1) ->
      (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) mr') ->
      FASM s1 s1' (mr' ,, (iMemA s1).(Snd)) (ACC fEol s1 l2) ->
      (ACC aHead s1).(Snd).(Fst) = true -> (ACC aPkt s1).(Snd).(Fst) = true -> ACC aMatch s1 = true ->
      ACC aIbFull s1 = false ->
      (andb (negb (ACC aInit s1)) (negb (ACC aFault s1)) = false -> l2 = ACC aDefPred s1) ->
      (andb (negb (ACC aInit s1)) (negb (ACC aFault s1)) = true ->
         pcAligned l2 /\ (ACC aNeeds s1 = false -> l2 = clearBit0 (ACC aSeqPc s1))) ->
      RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 l2 mr' Hpok Hmr1 Hmr2 Hst Hv Hpv Hm Hf Hl2a Hl2b H.
    pose proof Hst as [Erf [Ewb [Emem [Efe [ED [Eex [Edm Emd]]]]]]].
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    pose proof (iFlush_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Erf Emd) as Efl.
    pose proof (olderWriters_ext pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  s1 s1' Edm Emd) as Eow.
    assert (Ei : iRegionsA s1' = mr') by (unfold iRegions; rewrite Emem; reflexivity).
    assert (Core :
      RfRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' s2 /\
      MEMC g s1' s2 /\
      AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      CnwbRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      DmQueueRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA g s1' /\
      RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
        mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA initLine g s1' s2 /\
      ACC NoFenceIWait s1' = ACC NoFenceIWait s1 /\
      (AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1) ->
       AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst)) implRegions (iRegionsA s1')) /\
      (ACC aPre s1 = true -> iRegionsA s1' = iRegionsA s1) /\
      (ACC aPre s1 = false -> FetchDeqAtL (ACC aAligned s1) implRegions (iRegionsA s1) (iRegionsA s1'))).
    { destruct (ACC aPre s1) eqn:Hpre.
      - assert (Emem' : iMemA s1' = iMemA s1) by (rewrite Emem, (Hmr1 eq_refl); reflexivity).
        assert (Ereg : iRegionsA s1' = iRegionsA s1) by (unfold iRegions; rewrite Emem'; reflexivity).
        destruct (decode_core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    clintS clint plicS plic initLine fwcs g s1 s1' s2 Erf Emem' Edm Emd H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
        refine (conj Crf (conj Cm (conj Ca (conj Cc (conj Cd (conj Crk (conj _ (conj _ (conj _ _))))))))).
        + unfold NoFenceIWait; rewrite Ereg; reflexivity.
        + rewrite Ereg; exact (fun X => X).
        + intros _; exact Ereg.
        + intros C; discriminate C.
      - pose proof (Hmr2 eq_refl) as Hat.
        destruct (core_fetchDeq g s1 s1' s2 mr' _ Erf Emem Edm Emd Hat H) as [Crf [Cm [Ca [Cc [Cd Crk]]]]].
        refine (conj Crf (conj Cm (conj Ca (conj Cc (conj Cd (conj Crk (conj _ (conj _ (conj _ _))))))))).
        + unfold NoFenceIWait; rewrite Ei; refine (AllPorts_fetchDeqAt _ _ _ _ _ _ Hat); intros r y; reflexivity.
        + rewrite Ei; intros W; refine (AllPorts_fetchDeqAt_impl _ _ (ACC aAligned s1) _ _ _ _ _ (Hu _) Hat W).
          * intros r y _ [[H1 [H2 [H3 [H4 H5]]]] H6].
            refine (conj (conj H1 (conj H2 (conj _ (conj H4 H5)))) H6).
            intros C; discriminate C.
          * intros r y _ X; exact X.
        + intros C; discriminate C.
        + intros _; rewrite Ei; exact Hat. }
    destruct Core as [Crf [Cm [Ca [Cc [Cd [Crk [HNF [HW [Hr1 Hr2]]]]]]]]].
    assert (Ed2a : iD2aA s1' = iD2aA s1) by (unfold iD2a; rewrite ED; reflexivity).
    assert (Eep : iExecEpochA s1' = iExecEpochA s1) by (unfold iExecEpoch; rewrite Eex; reflexivity).
    assert (Efip : iFenceIPendingA s1' = iFenceIPendingA s1) by (unfold iFenceIPending; rewrite Eex; reflexivity).
    assert (Epcc : iPccA s1' = iPccA s1) by (unfold iPcc; rewrite Erf; reflexivity).
    assert (Edl : daLiveA s1' = daLiveA s1) by (unfold daLive; rewrite Eep; reflexivity).
    assert (Eal : aiLiveA s1' = aiLiveA s1) by (unfold aiLive; rewrite Eep; reflexivity).
    pose proof H as [_ _ Hl Hrp He' _ _ _ _ Hs Hfr Hwf _].
    destruct Hwf as [[W1a [W1b [W1c [W1d [W1e W1f]]]]] [W2 [W3 [W4 [W5 W6]]]]].
    destruct (head_live_list s1 W1a Hv Hm) as [rest [Efb0 [Hlh _]]].
    pose proof (fb_all_live g s1 s2 rest H Efb0 Hlh) as Hall.
    assert (Efb : iFetchBufA s1' = rest).
    { unfold iFetchBuf; rewrite Efe, fEol_fbFifo, (fifo_to_list_deq _ _ _ W1a).
      change (tl (iFetchBufA s1) = rest); rewrite Efb0; reflexivity. }
    assert (Ecp : optValid (ACC iCurParcel s1') = false) by (unfold iCurParcel; rewrite Efe; apply fEol_curParcel).
    assert (Estr : ACC iStraddle s1' = (if ACC aInit s1 then ACC aSomeSh s1 else getDefault (Option StraddleHalf)))
      by (unfold iStraddle; rewrite Efe; apply fEol_straddle).
    assert (Eib : iInstBufA s1' = (if ACC aInit s1 then iInstBufA s1 else (iInstBufA s1 ++ [ACC aAsm s1 l2])%list)).
    { unfold iInstBuf; rewrite Efe, fEol_instFifo; destruct (ACC aInit s1); [reflexivity |].
      exact (fifo_to_list_enq_nf _ _ _ _ W2 Hf). }
    assert (Epe : ACC iPredEpoch s1' = (if ACC aMis s1 l2 then ACC aNpe s1 else ACC iPredEpoch s1))
      by (unfold iPredEpoch; rewrite Efe; apply fEol_predEpoch).
    assert (Efpc : ACC iFetchPc s1' = (if ACC aMis s1 l2 then l2 else ACC iFetchPc s1))
      by (unfold iFetchPc; rewrite Efe; apply fEol_pc).
    assert (Elv : forall f, In f rest -> fbLiveA s1' f = (if ACC aMis s1 l2 then false else fbLiveA s1 f)).
    { intros f Hin; unfold fbLive; rewrite Eep, Epe.
      destruct (ACC aMis s1 l2); [| reflexivity].
      pose proof (proj1 (Forall_forall _ _) Hall f Hin) as Hf'; unfold fbLive in Hf'.
      apply andb_prop in Hf' as [_ Hf']; apply Zmod.eqb_eq in Hf'; rewrite Hf'.
      unfold aNpe; rewrite zmod_epoch_add1_neq; apply andb_false_r. }
    assert (Hlive : filter (fbLiveA s1') rest = (if ACC aMis s1 l2 then [] else filter (fbLiveA s1) rest)).
    { destruct (ACC aMis s1 l2) eqn:Hmis.
      - apply filter_all_false, Forall_forall; intros f Hin; rewrite (Elv f Hin); reflexivity.
      - apply filter_ext_in; intros f Hin; rewrite (Elv f Hin); reflexivity. }
    assert (Elv' : forall f, In f rest -> fbLiveA s1' f = true -> fbLiveA s1 f = true).
    { intros f Hin Ht; rewrite (Elv f Hin) in Ht; destruct (ACC aMis s1 l2); [discriminate Ht | exact Ht]. }
    assert (Ha : aiLiveA s1 (ACC aAsm s1 l2) = true)
      by (unfold aiLive; change (Zmod.eqb (iExecEpochA s1) (iExecEpochA s1) = true); apply Zmod.eqb_refl).
    assert (Hinit_nl : ACC aInit s1 = true -> l2 = ACC aNextLine s1).
    { intros Hinit; rewrite (Hl2a ltac:(rewrite Hinit; reflexivity)).
      unfold aDefPred; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aInit s1))) with (ACC aInit s1).
      rewrite Hinit; reflexivity. }
    assert (Hl2al : ACC aInit s1 = false -> pcAligned l2).
    { intros Hinit; destruct (ACC aFault s1) eqn:Hfault.
      - rewrite (Hl2a ltac:(rewrite Hinit; reflexivity)).
        unfold aDefPred; rewrite evalExpr_ITE; change (evalExpr (Var type Bool (ACC aInit s1))) with (ACC aInit s1).
        rewrite Hinit; cbv iota; change (pcAligned (ACC aInstPred s1)).
        unfold aInstPred; rewrite evalExpr_ITE.
        destruct (evalExpr (Eq (Var type (Bit LgFetchParcels) (ACC aLastP s1)) (Var type (Bit LgFetchParcels) (ACC aExit s1)))).
        + change (pcAligned (fbPredPc (aEA s1))); rewrite Efb0 in W1f; exact (Forall_inv W1f).
        + exact (seqPc_even s1).
      - exact (proj1 (Hl2b ltac:(rewrite Hinit; reflexivity))). }
    constructor.
    - exact Crf.
    - exact Cm.
    - exact Hl.
    - exact Hrp.
    - exact He'.
    - exact Ca.
    - exact Cc.
    - exact Cd.
    - exact (fence_live g s1 s1' s2 rest H Efb0 Hlh Efip HNF).
    - unfold ScoreRel, daLive in *; rewrite Eow, Ed2a, Ewb, Efl, Eep; exact Hs.
    - destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      unfold FrontRel; rewrite Ed2a, Edl, Eal, Efb, Eep.
      refine (conj F1 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      + rewrite Eib; destruct (ACC aInit s1); [exact F2 | exact (StalePrefix_snoc _ _ _ F2 Ha)].
      + destruct (ACC aMis s1 l2) eqn:Hmis.
        * apply StalePrefix_all_false, Forall_forall; intros f Hin; rewrite (Elv f Hin); reflexivity.
        * exists [], rest; split; [reflexivity | split; [constructor |]].
          apply Forall_forall; intros f Hin; rewrite (Elv f Hin); exact (proj1 (Forall_forall _ _) Hall f Hin).
      + rewrite Eib; intros Hx; destruct (ACC aInit s1); [exact (F4 Hx) |].
        apply Forall_app; split; [exact (F4 Hx) | constructor; [exact Ha | constructor]].
      + intros _; refine (Forall_impl _ _ Hall); intros f Hf'; exact (proj1 (andb_prop _ _ Hf')).
      + unfold LiveChain in *; rewrite Epcc.
        destruct (ACC aInit s1) eqn:Hinit.
        * assert (Elive : liveInstsA g s1' = liveInstsA g s1)
            by (unfold liveInsts; rewrite Ed2a, Eib, Edl, Eal; reflexivity).
          rewrite Elive.
          refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                    (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
          intros p Hp.
          exact (frontier_strad g s1 s1' s2 p rest l2 Hpok H Efb0 Hlh Hpv Hinit (Hinit_nl eq_refl) Efb Epcc Estr Hlive Efpc Hp).
        * assert (Elive : liveInstsA g s1' = (liveInstsA g s1 ++ [(ACC aFo s1, l2)])%list).
          { unfold liveInsts; rewrite Ed2a, Eib, Edl, Eal; cbv beta iota; rewrite filter_app, map_app, app_assoc.
            cbn [filter map]; rewrite Ha; reflexivity. }
          assert (Estr' : optValid (ACC iStraddle s1') = false) by (rewrite Estr; reflexivity).
          rewrite Elive; apply LiveChainG_snoc.
          refine (LiveChainG_mono pre post revBase revPfB revPfA initLine fwcs _ _ _ _ _ _ _
                    (proj2 (proj2 Cm)) (FetchViewExt_refl _ _) _ F6).
          intros p Hp.
          destruct (head_facts g s1 s2 rest p Hpok H Efb0 Hlh Hpv Hp) as [Hpc [Hal [HpX [Hcomp Hallow]]]].
          split; [exact (Hallow Hinit) |].
          rewrite foFault_aFo; destruct (ACC aFault s1) eqn:Hfault; [exact I |].
          destruct (Hl2b eq_refl) as [Hal2 Hseq].
          split.
          -- intros Hn; rewrite needsPred_aFo in Hn; rewrite (Hseq Hn), clearBit0_aligned by exact (seqPc_even s1).
             symmetry; exact (seqPc_aFo s1 p Hpc Hcomp).
          -- exact (frontier_eol s1 s1' s2 p rest l2 Efb0 Hlh Efb Epcc Estr' Ecp Hlive Efpc Hal2 Hp).
      + exact (FetchRespRel_drop s1 s1' s2 rest Efb0 Efb Elv' Hr1 Hr2 Hpv F7).
    - unfold WfRel; rewrite Efb, Epcc, Ed2a, Eib.
      split; [split; [rewrite Efe, fEol_fbFifo; exact (fifo_wf_deq _ _ _ W1a) |] |].
      + split; [rewrite Ecp; intros C; discriminate C |].
        rewrite Efb0 in W1f.
        split; [exact W1c |]; split; [exact W1d |]; split; [| exact (Forall_inv_tail W1f)].
        destruct (ACC aInit s1) eqn:Hinit; [exact W1e |].
        apply Forall_app; split; [exact W1e | constructor; [exact (Hl2al eq_refl) | constructor]].
      + split; [rewrite Efe, fEol_instFifo; destruct (ACC aInit s1); [exact W2 | exact (fifo_wf_enq _ _ _ _ W2)] |].
        split; [rewrite ED; exact W3 |]; split; [rewrite Edm; exact W4 |]; split; [rewrite Emd; exact W5 | exact (HW W6)].
    - exact Crk.
  Qed.

  (* =========================================================================
   * The theorem: one `fetchAssembleStage` step is matched by a spec stutter
   * ========================================================================= *)

  (* With no redirect pending, fetch's PCC copy stands for the architectural PCC *)
  Theorem fetchAsm_live :
    forall g (s1 s1' : IState) (s2 : SState),
      SemAction (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                   mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs)
        STAGE s1 s1' Zmod.zero ->
      PccOK s1 -> RELG g s1 s2 -> RELG g s1' s2.
  Proof.
    intros g s1 s1' s2 Hsem Hpok Hg.
    pose proof (fun A => lineUnique_implRegions pre post revBase revPfB revPfA A (Is_true_eq_true _ Hdisj)) as Hu.
    destruct (ACC aCp s1) eqn:Hcp.
    2: { rewrite (asm_idle pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    _ s1 s1' Hsem Hcp); exact Hg. }
    destruct ((ACC aHead s1).(Snd).(Fst)) eqn:Hv.
    2: { exact (asm_stutter_rel g s1 s1' s2
                  (asm_noHead pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                     _ Hu s1 s1' Hsem Hcp Hv) Hg). }
    destruct ((ACC aPkt s1).(Snd).(Fst)) eqn:Hpv.
    2: { exact (asm_stutter_rel g s1 s1' s2
                  (asm_noPkt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                     _ Hu s1 s1' Hsem Hcp Hv Hpv) Hg). }
    destruct (ACC aMatch s1) eqn:Hm.
    2: { destruct (asm_stale pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                     _ Hu s1 s1' Hsem Hcp Hv Hpv Hm) as [mr' [Hmr1 [Hmr2 Hst]]].
         exact (asm_stale_rel g s1 s1' s2 mr' Hmr1 Hmr2 Hst Hv Hpv Hm Hg). }
    destruct (ACC aIbFull s1) eqn:Hf.
    { exact (asm_stutter_rel g s1 s1' s2
               (asm_ibFullStall pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  _ Hu s1 s1' Hsem Hcp Hv Hpv Hm Hf) Hg). }
    destruct (ACC aIsSeq s1) eqn:Hseq.
    - pose proof (asm_seq pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                    mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                    _ Hu s1 s1' Hsem Hcp Hv Hpv Hm Hf Hseq) as Hst.
      refine (asm_stay_rel g s1 s1' s2 true Hpok Hst Hv Hpv Hm Hf _ Hg).
      unfold aIsSeq in Hseq; rewrite and3E_eval in Hseq.
      apply andb_prop in Hseq as [Hseq _]; apply andb_prop in Hseq as [Hseq _].
      rewrite notE_eval in Hseq; apply negb_true_iff in Hseq; exact Hseq.
    - destruct (asm_eol pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                  _ Hu s1 s1' Hsem Hcp Hv Hpv Hm Hf Hseq) as [l2 [mr' [Hl2a [Hl2b [Hmr1 [Hmr2 [Heol Hstay]]]]]]].
      destruct (ACC aEol s1 l2) eqn:He.
      + exact (asm_eol_rel g s1 s1' s2 l2 mr' Hpok Hmr1 (fun Hp => Hmr2 Hp eq_refl) (Heol eq_refl) Hv Hpv Hm Hf Hl2a Hl2b Hg).
      + pose proof (Hstay eq_refl) as Hst.
        unfold aEol in He; rewrite or2_eval, notE_eval, eqAddrE_eval in He.
        apply orb_false_iff in He as [He1 He2]; apply negb_false_iff, Zmod.eqb_eq in He1.
        change (l2 = ACC aSeqPc s1) in He1; rewrite He1 in Hst.
        exact (asm_stay_rel g s1 s1' s2 false Hpok Hst Hv Hpv Hm Hf He2 Hg).
  Qed.

End FetchAsmStep.
