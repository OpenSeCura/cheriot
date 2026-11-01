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
From Cheriot Require Import SpecDefines SpecDevice Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefMemRel RefCoreRel RefFrame RefPeriph.
From Cheriot.Proof Require Import RefRevoker RefRevokerStep ImplSpec RefFetch RefBits.

Import ListNotations.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4: the step that empties the data response buffer (`implMemReadRpStep`).
 *
 * 1. `readRpStep_noRp`, `readRpStep_valid`: with the buffer empty nothing changes; with a
 *    response `rp` in the buffer and `state` = ReadRqSent, the buffer is emptied and `state`
 *    becomes ReadRq for the second line (after the first line of a crossing access, with the
 *    first line's packet saved) or ReadRpReady with the read's value (`ReadRpNext`).
 * 2. `stepOK_readRpStep`: the spec stutters; the access in flight moves from RdArrived to
 *    RdPend true or to RdReady (`rpStepAcc`). *)

(* --- 1. The Step on the Memory Subtree --- *)

Lemma msReadRpReadyV_build :
  forall e : Expr type FullCapWithTag,
    msReadRpReadyV (evalExpr (BuildUnion (ls := MemStateList) (@Build_FinType (length MemStateList) 3 I) e)) =
    evalExpr e.
Proof. intros e; exact (evalExpr_ReadUnionData_BuildUnion MemStateList (@Build_FinType (length MemStateList) 3 I) e eq_refl). Qed.

(* The fields of a `ReadRqSent` payload: { crosses; step = { isSecond; op = { addr; memSize; pkt } } } *)
Definition rsCrosses (i : type MemReadRqSent) : bool := i.(Fst).
Definition rsSecond (i : type MemReadRqSent) : bool := i.(Snd).(Fst).(Fst).
Definition rsAddr (i : type MemReadRqSent) : type Addr := i.(Snd).(Fst).(Snd).(Fst).(Fst).
Definition rsSize (i : type MemReadRqSent) : type (Bit LgLgNumBytesFullCapSz) := i.(Snd).(Fst).(Snd).(Fst).(Snd).(Fst).
Definition rsPkt (i : type MemReadRqSent) : type CapPacket := i.(Snd).(Fst).(Snd).(Fst).(Snd).(Snd).(Fst).

(* The value of a read whose line `b` got response `rp` (`pkt0`: the first line's packet when
 * `b` is the second line) *)
Definition readRpRes (b : bool) (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) (pkt0 : type CapPacket)
  (rp : type LineReadRp) : type FullCapWithTag :=
  evalLetExpr (memAssembleCapRead (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)
                 (Var type CapPacket
                    (if b
                     then evalExpr (memMergeCapPacket (Var type Addr addr) (Var type CapPacket pkt0)
                                      (Var type CapPacket (specPkt addr rp)))
                     else specPkt addr rp))).

(* The `state` after the response `rp` of the read described by `i` left the buffer *)
Definition ReadRpNext (i : type MemReadRqSent) (rp : type LineReadRp) (st' : type MemState) : Prop :=
  if andb (negb (rsSecond i)) (rsCrosses i)
  then msReadRq st' = true /\ msReadRqV st' = stepOf true (rsAddr i) (rsSize i) (specPkt (rsAddr i) rp)
  else msReadRpReady st' = true /\ msReadRpReadyV st' = readRpRes (rsSecond i) (rsAddr i) (rsSize i) (rsPkt i) rp.

Lemma ReadRpNext_step :
  forall c b addr size pkt0 rp st',
    ReadRpNext (c ,, (stepOf b addr size pkt0 ,, tt)) rp st' ->
    if andb (negb b) c
    then msReadRq st' = true /\ msReadRqV st' = stepOf true addr size (specPkt addr rp)
    else msReadRpReady st' = true /\ msReadRpReadyV st' = readRpRes b addr size pkt0 rp.
Proof. intros c b addr size pkt0 rp st' H; exact H. Qed.

Section ReadRpChar.
  Variable regions : list MemRegion.

  Ltac mem_cbn H :=
    cbn -[evalExpr evalLetExpr toAction memExtractCapPacket memAssembleCapRead memMergeCapPacket] in H.

  (* An empty buffer: nothing changes *)
  Lemma readRpStep_noRp :
    forall env mr mst mrq mrp m' v,
      optValid mrp = false ->
      SemAction env (@implMemReadRpStep regions type) (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))).
  Proof.
    intros env mr mst mrq mrp m' v Hv H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemReadRpStep in H.
    cbn [evalActionPropGen] in H.
    mem_cbn H.
    match type of H with context [if ?cd then _ else _] =>
      replace cd with false in H
        by (symmetry; change (andb (msReadRqSent mst) (optValid mrp) = false); rewrite Hv; apply andb_false_r)
    end.
    mem_cbn H.
    destruct H as [H _]; symmetry; exact H.
  Qed.

  (* A full buffer while a line read is out: the buffer empties and `state` moves on *)
  Lemma readRpStep_valid :
    forall env mr mst mrq rp m' v,
      msReadRqSent mst = true ->
      SemAction env (@implMemReadRpStep regions type) (mr ,, (mst ,, (mrq ,, ((rp ,, (true ,, tt)) ,, tt)))) m' v ->
      exists st', m' = (mr ,, (st' ,, (mrq ,, (getDefault (Option LineReadRp) ,, tt)))) /\
        ReadRpNext (msReadRqSentV mst) rp st'.
  Proof.
    intros env mr mst mrq rp m' v Hs H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemReadRpStep in H.
    cbn [evalActionPropGen] in H.
    mem_cbn H.
    match type of H with context [if ?cd then _ else _] =>
      replace cd with true in H
        by (symmetry; change (andb (msReadRqSent mst) true = true); rewrite Hs; reflexivity)
    end.
    mem_cbn H.
    apply evalActionPropGen_toAction in H; mem_cbn H.
    unfold ReadRpNext.
    match type of H with context [if ?cd then _ else _] => destruct cd eqn:Ec end.
    - assert (E : andb (negb (rsSecond (msReadRqSentV mst))) (rsCrosses (msReadRqSentV mst)) = true) by exact Ec.
      mem_cbn H.
      destruct H as [H _]; subst m'.
      eexists; split; [reflexivity |].
      rewrite E; split; [reflexivity |].
      rewrite msReadRqV_build; reflexivity.
    - assert (E : andb (negb (rsSecond (msReadRqSentV mst))) (rsCrosses (msReadRqSentV mst)) = false) by exact Ec.
      mem_cbn H.
      apply evalActionPropGen_toAction in H; mem_cbn H.
      destruct H as [H _]; subst m'.
      eexists; split; [reflexivity |].
      rewrite E; split; [reflexivity |].
      rewrite msReadRpReadyV_build; reflexivity.
  Qed.
End ReadRpChar.

(* --- 2. The Access in Flight after the Step --- *)

(* The value `state` gets is the relation's value of the read *)
Lemma readRpRes_first : forall a sz p rp, readRpRes false a sz p rp = lineVal a sz rp.
Proof. intros a sz p rp; reflexivity. Qed.

Lemma readRpRes_second : forall ld pkt0 rp,
  readRpRes true (ldAddr ld) (plSize (ldPending ld)) pkt0 rp = mergedLoadVal ld pkt0 rp.
Proof. intros ld pkt0 rp; reflexivity. Qed.

Lemma lineVal_single : forall ld rp, lineVal (ldAddr ld) (plSize (ldPending ld)) rp = singleLoadVal ld rp.
Proof. intros ld rp; reflexivity. Qed.

Section ReadRpStep.
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

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation NPMI := (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation NPMS := (Spec.np_mem pcAddrInit specRegions).

  Local Abbreviation iMemA := (iMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA := (iMemSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA := (iRequester pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iReadRpA := (iReadRp pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iDmStA := (iDmSt pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iRevPhaseA := (iRevPhase pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation iScanAddrA := (iScanAddr pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB
                                      revPfA).
  Local Abbreviation iRevScanBaseA := (iRevScanBase pcAddrInit fetchCapacity instCapacity decodeCapacity
                                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config pre
                                         post revBase revPfB revPfA).
  Local Abbreviation RNR := (revNotReading pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation DNA := (dmNotAccessing pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem pcAddrInit pre post revBase revPfB revPfA).

  Local Abbreviation ACC := (AccessRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation REVK := (RevokerRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation RACC := (RevAccRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation PQ := (PortsQuiet pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).
  Local Abbreviation RELG := (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).

  (* The ghost with another access in flight *)
  Definition gWithAcc (g : Ghost pcAddrInit) (a : Access) : Ghost pcAddrInit :=
    mkGhost pcAddrInit (g_chain pcAddrInit g) (g_rf0 pcAddrInit g) (g_cnwb pcAddrInit g)
            (g_revOff pcAddrInit g) (g_d2aFo pcAddrInit g) a.

  (* A full data response buffer: the access in flight is a read whose line response arrived *)
  Lemma AccessRel_rpValid :
    forall g (s1 : IState) (s2 : SState),
      ACC g s1 s2 -> optValid (iReadRpA s1) = true ->
      exists b rp, iReadRpA s1 = (rp ,, (true ,, tt)) /\
        ((exists ld pkt0, g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived b rp)) \/
         (exists rc, g_acc pcAddrInit g = AccDmRev rc (RdArrived b rp)) \/
         g_acc pcAddrInit g = AccRevCap (RdArrived b rp) \/
         g_acc pcAddrInit g = AccRevBit (RdArrived b rp)).
  Proof.
    intros g s1 s2 Ha Hv.
    unfold AccessRel in Ha.
    destruct (g_acc pcAddrInit g) as [| addr size pkt [b|b] | ld pkt0 [b|b|b|b rp|res]
                                     | rc [b|b|b|b rp|res] | [b|b|b|b rp|res]
                                     | [b|b|b|b rp|res] | addr pkt [b|b]];
      unfold WrStageRel, RdStageRel in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (exfalso; match goal with H : optValid ?x = false |- _ => rewrite H in Hv; discriminate Hv end).
    - exists b, rp; split; [assumption | left; exists ld, pkt0; reflexivity].
    - exists b, rp; split; [assumption | right; left; exists rc; reflexivity].
    - exists b, rp; split; [assumption | right; right; left; reflexivity].
    - exists b, rp; split; [assumption | right; right; right; reflexivity].
  Qed.

  Lemma RevAccRel_iRev :
    forall g (s1 s1' : IState) (s2 : SState), iRevA s1' = iRevA s1 -> RACC g s1 s2 -> RACC g s1' s2.
  Proof.
    intros g s1 s1' s2 HR H.
    unfold RevAccRel, RevCapOK, RevWriteOK, iScanAddr, iRevScanBase, iRevArch in *.
    rewrite HR; exact H.
  Qed.

  (* The revoker facts after the step: the revoker is unchanged, and the values of its reads
   * carry over *)
  Lemma RevokerRel_rpStep :
    forall g a' (s1 s1' : IState) (s2 : SState),
      iRevA s1' = iRevA s1 -> (RACC g s1 s2 -> RACC (gWithAcc g a') s1 s2) ->
      REVK g s1 s2 -> REVK (gWithAcc g a') s1' s2.
  Proof.
    intros g a' s1 s1' s2 HR Hacc H.
    pose proof (RevAccRel_iRev (gWithAcc g a') s1 s1' s2 HR) as Hi.
    unfold RevokerRel in *.
    destruct H as [R1 [R2 [R3 [R4 R5]]]].
    split; [| split; [| split; [| split]]].
    - unfold iRevArch, iRevPhase in *; rewrite HR; exact R1.
    - unfold iRevPhase, iRevScanCap, iRevScanBase, iScanAddr in *; rewrite HR; exact R2.
    - unfold iRevPhase, iRevSnoopHit, iRevScanCap, iScanAddr in *; rewrite HR; exact R3.
    - unfold iRevPhase, iRevSnoopHit, iRevScanBase in *; rewrite HR; exact R4.
    - exact (Hi (Hacc R5)).
  Qed.

  (* The impl state after the buffer was emptied: only `state` and `readRp` changed *)
  Record RpStepped (s1 s1' : IState) (st' : type MemState) : Prop := {
    rs_reg : iRegionsA s1' = iRegionsA s1 ;
    rs_st  : iMemStA s1' = st' ;
    rs_rp  : optValid (iReadRpA s1') = false ;
    rs_req : iRequesterA s1' = iRequesterA s1 ;
    rs_dm  : iDmStA s1' = iDmStA s1 ;
    rs_rev : iRevA s1' = iRevA s1
  }.

  Lemma rpStepped_PQ : forall s1 s1' st', RpStepped s1 s1' st' -> PQ s1' = PQ s1.
  Proof. intros s1 s1' st' H; unfold PortsQuiet; rewrite (rs_reg _ _ _ H); reflexivity. Qed.

  Lemma rpStepped_RNR : forall s1 s1' st', RpStepped s1 s1' st' -> RNR s1' = RNR s1.
  Proof. intros s1 s1' st' H; unfold revNotReading, iRevPhase; rewrite (rs_rev _ _ _ H); reflexivity. Qed.

  Lemma rpStepped_DNA : forall s1 s1' st', RpStepped s1 s1' st' -> DNA s1' = DNA s1.
  Proof. intros s1 s1' st' H; unfold dmNotAccessing; rewrite (rs_dm _ _ _ H); reflexivity. Qed.

  Lemma rpStepped_phase : forall s1 s1' st', RpStepped s1 s1' st' -> iRevPhaseA s1' = iRevPhaseA s1.
  Proof. intros s1 s1' st' H; unfold iRevPhase; rewrite (rs_rev _ _ _ H); reflexivity. Qed.

  (* The relation after the step, given the access in flight and its revoker facts *)
  Lemma readRp_frame :
    forall g a' (s1 s1' : IState) (s2 : SState) m' st',
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      accTakesHead a' = accTakesHead (g_acc pcAddrInit g) ->
      ACC (gWithAcc g a') s1' s2 ->
      (RACC g s1 s2 -> RACC (gWithAcc g a') s1 s2) ->
      RELG g s1 s2 -> RELG (gWithAcc g a') s1' s2.
  Proof.
    intros g a' s1 s1' s2 m' st' E1 HS Etk Hacc Hracc Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ Hm Hl _ _ _ _ _ _ _ _ _ Hrk].
    eapply (RefRelG_mem_frame pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
              clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
      [exact E1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Etk
      | intros P; rewrite (rs_reg _ _ _ HS); reflexivity | intros L; reflexivity | apply FetchViewExt_refl
      | | exact Hl | exact Hacc | | exact Hg].
    - unfold MemRelC in *; cbn [gWithAcc g_revOff]; rewrite (rs_reg _ _ _ HS); exact Hm.
    - exact (RevokerRel_rpStep g a' s1 s1' s2 (rs_rev _ _ _ HS) Hracc Hrk).
  Qed.

  (* The second line of a crossing load arrived: the merged value is ready *)
  Lemma rpAcc_load2 :
    forall g (s1 s1' : IState) (s2 : SState) st' ld pkt0 rp,
      RpStepped s1 s1' st' -> g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived true rp) ->
      msReadRpReady st' = true -> msReadRpReadyV st' = mergedLoadVal ld pkt0 rp ->
      ACC g s1 s2 -> ACC (gWithAcc g (AccLoad ld pkt0 (RdReady (mergedLoadVal ld pkt0 rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 st' ld pkt0 rp HS Eacc Hry HryV Ha.
    unfold AccessRel in Ha |- *; rewrite Eacc in Ha; cbn [gWithAcc g_acc g_revOff g_cnwb].
    unfold RdStageRel in Ha |- *; cbv beta iota zeta in Ha |- *.
    destruct Ha as [[_ [_ Hq0]] [Hreq [Hdl [HdlV [Hrn0 [Hoff [_ [Hsec Hcn]]]]]]]].
    rewrite (rs_st _ _ _ HS), (rpStepped_PQ _ _ _ HS), (rs_req _ _ _ HS), (rs_dm _ _ _ HS), (rpStepped_RNR _ _ _ HS).
    exact (conj (conj Hry (conj HryV (conj (rs_rp _ _ _ HS) Hq0)))
                (conj Hreq (conj Hdl (conj HdlV (conj Hrn0 (conj Hoff (conj Hsec Hcn))))))).
  Qed.

  (* The first line of a crossing load arrived: the second line is next *)
  Lemma rpAcc_load1x :
    forall g (s1 s1' : IState) (s2 : SState) st' ld pkt0 rp,
      RpStepped s1 s1' st' -> g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived false rp) ->
      crossesB (ldAddr ld) (plSize (ldPending ld)) = true ->
      msReadRq st' = true ->
      msReadRqV st' = stepOf true (ldAddr ld) (plSize (ldPending ld)) (specPkt (ldAddr ld) rp) ->
      ACC g s1 s2 -> ACC (gWithAcc g (AccLoad ld (specPkt (ldAddr ld) rp) (RdPend true))) s1' s2.
  Proof.
    intros g s1 s1' s2 st' ld pkt0 rp HS Eacc Hcr Hrq HrqV Ha.
    unfold AccessRel in Ha |- *; rewrite Eacc in Ha; cbn [gWithAcc g_acc g_revOff g_cnwb].
    unfold RdStageRel in Ha |- *; cbv beta iota zeta in Ha |- *.
    rewrite Hcr in Ha |- *; cbv iota in Ha.
    destruct Ha as [[_ [_ Hq0]] [Hreq [Hdl [HdlV [Hrn0 [Hoff [_ [Hsec Hcn]]]]]]]].
    rewrite (rs_st _ _ _ HS), (rpStepped_PQ _ _ _ HS), (rs_req _ _ _ HS), (rs_dm _ _ _ HS), (rpStepped_RNR _ _ _ HS).
    exact (conj (conj Hrq (conj HrqV (conj (rs_rp _ _ _ HS) Hq0)))
                (conj Hreq (conj Hdl (conj HdlV (conj Hrn0 (conj Hoff (conj eq_refl (conj Hcn Hsec)))))))).
  Qed.

  (* A single-line load arrived: its value is ready *)
  Lemma rpAcc_load1 :
    forall g (s1 s1' : IState) (s2 : SState) st' ld pkt0 rp,
      RpStepped s1 s1' st' -> g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived false rp) ->
      crossesB (ldAddr ld) (plSize (ldPending ld)) = false ->
      msReadRpReady st' = true -> msReadRpReadyV st' = singleLoadVal ld rp ->
      ACC g s1 s2 -> ACC (gWithAcc g (AccLoad ld pkt0 (RdReady (singleLoadVal ld rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 st' ld pkt0 rp HS Eacc Hcr Hry HryV Ha.
    unfold AccessRel in Ha |- *; rewrite Eacc in Ha; cbn [gWithAcc g_acc g_revOff g_cnwb].
    unfold RdStageRel in Ha |- *; cbv beta iota zeta in Ha |- *.
    rewrite Hcr in Ha; cbv iota in Ha.
    destruct Ha as [[_ [_ Hq0]] [Hreq [Hdl [HdlV [Hrn0 [Hoff [_ [Hsec Hcn]]]]]]]].
    rewrite (rs_st _ _ _ HS), (rpStepped_PQ _ _ _ HS), (rs_req _ _ _ HS), (rs_dm _ _ _ HS), (rpStepped_RNR _ _ _ HS).
    exact (conj (conj Hry (conj HryV (conj (rs_rp _ _ _ HS) Hq0)))
                (conj Hreq (conj Hdl (conj HdlV (conj Hrn0 (conj Hoff (conj Hsec Hcn))))))).
  Qed.

  (* dataMem's rev-bit read arrived: the rev byte is ready *)
  Lemma rpAcc_dmRev :
    forall g (s1 s1' : IState) (s2 : SState) st' rc b rp,
      RpStepped s1 s1' st' -> g_acc pcAddrInit g = AccDmRev rc (RdArrived b rp) ->
      msReadRpReady st' = true -> msReadRpReadyV st' = lineVal (revByteAddrOf config (rcBase rc)) byteSz rp ->
      ACC g s1 s2 ->
      ACC (gWithAcc g (AccDmRev rc (RdReady (lineVal (revByteAddrOf config (rcBase rc)) byteSz rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 st' rc b rp HS Eacc Hry HryV Ha.
    unfold AccessRel in Ha |- *; rewrite Eacc in Ha; cbn [gWithAcc g_acc g_revOff g_cnwb].
    unfold RdStageRel in Ha |- *; cbv beta iota zeta in Ha |- *.
    destruct Ha as [[_ [_ Hq0]] [Hreq [Hdr [HdrV [Hrn0 [Hoff [Hsec [Hcn [_ [Hbr Hval]]]]]]]]]].
    rewrite (rs_st _ _ _ HS), (rpStepped_PQ _ _ _ HS), (rs_req _ _ _ HS), (rs_dm _ _ _ HS), (rpStepped_RNR _ _ _ HS).
    exact (conj (conj Hry (conj HryV (conj (rs_rp _ _ _ HS) Hq0)))
                (conj Hreq (conj Hdr (conj HdrV (conj Hrn0 (conj Hoff
                  (conj Hsec (conj Hcn (conj eq_refl (conj Hbr Hval)))))))))).
  Qed.

  (* The revoker's cap read arrived *)
  Lemma rpAcc_revCap :
    forall g (s1 s1' : IState) (s2 : SState) st' b rp,
      RpStepped s1 s1' st' -> g_acc pcAddrInit g = AccRevCap (RdArrived b rp) ->
      msReadRpReady st' = true -> msReadRpReadyV st' = lineVal (iScanAddrA s1) capSz rp ->
      ACC g s1 s2 -> ACC (gWithAcc g (AccRevCap (RdReady (lineVal (iScanAddrA s1) capSz rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 st' b rp HS Eacc Hry HryV Ha.
    unfold AccessRel in Ha |- *; rewrite Eacc in Ha; cbn [gWithAcc g_acc g_revOff g_cnwb].
    unfold RdStageRel in Ha |- *; cbv beta iota zeta in Ha |- *.
    destruct Ha as [[_ [_ Hq0]] [Hreq [Hph [Hdn0 [Hoff [Hsec _]]]]]].
    rewrite (rs_st _ _ _ HS), (rpStepped_PQ _ _ _ HS), (rs_req _ _ _ HS), (rpStepped_DNA _ _ _ HS),
      (rpStepped_phase _ _ _ HS).
    exact (conj (conj Hry (conj HryV (conj (rs_rp _ _ _ HS) Hq0)))
                (conj Hreq (conj Hph (conj Hdn0 (conj Hoff (conj Hsec eq_refl)))))).
  Qed.

  (* The revoker's rev-bit read arrived *)
  Lemma rpAcc_revBit :
    forall g (s1 s1' : IState) (s2 : SState) st' b rp,
      RpStepped s1 s1' st' -> g_acc pcAddrInit g = AccRevBit (RdArrived b rp) ->
      msReadRpReady st' = true -> msReadRpReadyV st' = lineVal (revByteAddrOf config (iRevScanBaseA s1)) byteSz rp ->
      ACC g s1 s2 ->
      ACC (gWithAcc g (AccRevBit (RdReady (lineVal (revByteAddrOf config (iRevScanBaseA s1)) byteSz rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 st' b rp HS Eacc Hry HryV Ha.
    unfold AccessRel in Ha |- *; rewrite Eacc in Ha; cbn [gWithAcc g_acc g_revOff g_cnwb].
    unfold RdStageRel in Ha |- *; cbv beta iota zeta in Ha |- *.
    destruct Ha as [[_ [_ Hq0]] [Hreq [Hph [Hdn0 [Hoff [Hsec _]]]]]].
    rewrite (rs_st _ _ _ HS), (rpStepped_PQ _ _ _ HS), (rs_req _ _ _ HS), (rpStepped_DNA _ _ _ HS),
      (rpStepped_phase _ _ _ HS).
    exact (conj (conj Hry (conj HryV (conj (rs_rp _ _ _ HS) Hq0)))
                (conj Hreq (conj Hph (conj Hdn0 (conj Hoff (conj Hsec eq_refl)))))).
  Qed.

  Lemma rpRacc_revCap :
    forall g (s1 : IState) (s2 : SState) b rp,
      g_acc pcAddrInit g = AccRevCap (RdArrived b rp) ->
      RACC g s1 s2 -> RACC (gWithAcc g (AccRevCap (RdReady (lineVal (iScanAddrA s1) capSz rp)))) s1 s2.
  Proof.
    intros g s1 s2 b rp Eacc H.
    unfold RevAccRel, RevCapOK in H |- *; rewrite Eacc in H; cbn [gWithAcc g_acc g_revOff]; exact H.
  Qed.

  Lemma rpRacc_revBit :
    forall g (s1 : IState) (s2 : SState) b rp,
      g_acc pcAddrInit g = AccRevBit (RdArrived b rp) ->
      RACC g s1 s2 ->
      RACC (gWithAcc g (AccRevBit (RdReady (lineVal (revByteAddrOf config (iRevScanBaseA s1)) byteSz rp)))) s1 s2.
  Proof.
    intros g s1 s2 b rp Eacc H.
    unfold RevAccRel in H |- *; rewrite Eacc in H; cbn [gWithAcc g_acc]; exact H.
  Qed.

  Lemma iScanAddr_scanFull :
    forall (s1 : IState), iScanAddrA s1 = scanFull (revScanAddr (projImplRevokerArchState (iRevA s1))).
  Proof. reflexivity. Qed.

  Lemma iMem_read' : forall (s1 : IState), readSubTreeState NPMI s1 = iMemA s1.
  Proof. reflexivity. Qed.

  (* What the step changed, read off the memory subtree *)
  Lemma rpStepped_of :
    forall (s1 s1' : IState) mr mst mrq mrp st',
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr ,, (st' ,, (mrq ,, (getDefault (Option LineReadRp) ,, tt)))) ->
      RpStepped s1 s1' st'.
  Proof.
    intros s1 s1' mr mst mrq mrp st' EM E1.
    assert (EM' : iMemA s1' = (mr ,, (st' ,, (mrq ,, (getDefault (Option LineReadRp) ,, tt)))))
      by (rewrite E1; reflexivity).
    constructor.
    - unfold iRegions; rewrite EM', EM; reflexivity.
    - unfold iMemSt; rewrite EM'; reflexivity.
    - unfold iReadRp; rewrite EM'; reflexivity.
    - unfold iRequester; rewrite EM', EM; reflexivity.
    - rewrite E1; reflexivity.
    - unfold iRev, iRegions; rewrite EM', EM; reflexivity.
  Qed.

  (* An empty buffer: nothing changed *)
  Lemma readRp_same :
    forall (s1 s1' : IState) mr mst mrq mrp,
      iMemA s1 = (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) ->
      s1' = writeSubTreeState NPMI s1 (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) -> s1' = s1.
  Proof.
    intros s1 s1' mr mst mrq mrp EM E1.
    rewrite E1; transitivity (writeSubTreeState NPMI s1 (iMemA s1)); [f_equal; symmetry; exact EM | reflexivity].
  Qed.

  (* The read in flight is out: `state` = ReadRqSent *)
  Lemma readRp_sent :
    forall g (s1 : IState) (s2 : SState) b rp,
      ACC g s1 s2 ->
      ((exists ld pkt0, g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived b rp)) \/
       (exists rc, g_acc pcAddrInit g = AccDmRev rc (RdArrived b rp)) \/
       g_acc pcAddrInit g = AccRevCap (RdArrived b rp) \/
       g_acc pcAddrInit g = AccRevBit (RdArrived b rp)) ->
      msReadRqSent (iMemStA s1) = true.
  Proof.
    intros g s1 s2 b rp Ha Hcases; unfold AccessRel in Ha.
    destruct Hcases as [[ld [pkt0 Eacc]] | [[rc Eacc] | [Eacc | Eacc]]]; rewrite Eacc in Ha;
      unfold RdStageRel in Ha; cbv beta iota zeta in Ha; exact (proj1 (proj1 (proj1 Ha))).
  Qed.

  (* A core load's second line arrived *)
  Lemma readRp_load2 :
    forall g (s1 s1' : IState) (s2 : SState) m' st' ld pkt0 rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived true rp) ->
      msReadRpReady st' = true -> msReadRpReadyV st' = mergedLoadVal ld pkt0 rp ->
      RELG g s1 s2 -> RELG (gWithAcc g (AccLoad ld pkt0 (RdReady (mergedLoadVal ld pkt0 rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' ld pkt0 rp E1 HS Eacc Hry HryV Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    apply (readRp_frame g _ s1 s1' s2 _ st' E1 HS); [rewrite Eacc; reflexivity | | | exact Hg].
    - exact (rpAcc_load2 g s1 s1' s2 st' ld pkt0 rp HS Eacc Hry HryV Ha).
    - intros _; unfold RevAccRel; exact I.
  Qed.

  (* A core load's first line arrived and the load crosses *)
  Lemma readRp_load1x :
    forall g (s1 s1' : IState) (s2 : SState) m' st' ld pkt0 rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived false rp) ->
      crossesB (ldAddr ld) (plSize (ldPending ld)) = true ->
      msReadRq st' = true ->
      msReadRqV st' = stepOf true (ldAddr ld) (plSize (ldPending ld)) (specPkt (ldAddr ld) rp) ->
      RELG g s1 s2 -> RELG (gWithAcc g (AccLoad ld (specPkt (ldAddr ld) rp) (RdPend true))) s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' ld pkt0 rp E1 HS Eacc Ecr Hrq HrqV Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    apply (readRp_frame g _ s1 s1' s2 _ st' E1 HS); [rewrite Eacc; reflexivity | | | exact Hg].
    - exact (rpAcc_load1x g s1 s1' s2 st' ld pkt0 rp HS Eacc Ecr Hrq HrqV Ha).
    - intros _; unfold RevAccRel; exact I.
  Qed.

  (* A single-line core load arrived *)
  Lemma readRp_load1 :
    forall g (s1 s1' : IState) (s2 : SState) m' st' ld pkt0 rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived false rp) ->
      crossesB (ldAddr ld) (plSize (ldPending ld)) = false ->
      msReadRpReady st' = true -> msReadRpReadyV st' = singleLoadVal ld rp ->
      RELG g s1 s2 -> RELG (gWithAcc g (AccLoad ld pkt0 (RdReady (singleLoadVal ld rp)))) s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' ld pkt0 rp E1 HS Eacc Ecr Hry HryV Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    apply (readRp_frame g _ s1 s1' s2 _ st' E1 HS); [rewrite Eacc; reflexivity | | | exact Hg].
    - exact (rpAcc_load1 g s1 s1' s2 st' ld pkt0 rp HS Eacc Ecr Hry HryV Ha).
    - intros _; unfold RevAccRel; exact I.
  Qed.

  (* A core load's line response left the buffer *)
  Lemma readRp_load :
    forall g (s1 s1' : IState) (s2 : SState) m' st' ld pkt0 b rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccLoad ld pkt0 (RdArrived b rp) ->
      ReadRpNext (msReadRqSentV (iMemStA s1)) rp st' ->
      RELG g s1 s2 -> exists g', RELG g' s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' ld pkt0 b rp E1 HS Eacc Hnext Hg.
    assert (HsV : msReadRqSentV (iMemStA s1) =
                  (crossesB (ldAddr ld) (plSize (ldPending ld)) ,,
                   (stepOf b (ldAddr ld) (plSize (ldPending ld)) pkt0 ,, tt))).
    { pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha0 _ _ _ _ _ _ _].
      unfold AccessRel in Ha0; rewrite Eacc in Ha0.
      unfold RdStageRel in Ha0; cbv beta iota zeta in Ha0.
      exact (proj2 (proj1 (proj1 Ha0))). }
    rewrite HsV in Hnext; apply ReadRpNext_step in Hnext.
    destruct b.
    - destruct Hnext as [Hry HryV].
      exact (ex_intro _ _ (readRp_load2 g s1 s1' s2 m' st' ld pkt0 rp E1 HS Eacc Hry
                             (eq_trans HryV (readRpRes_second ld pkt0 rp)) Hg)).
    - destruct (crossesB (ldAddr ld) (plSize (ldPending ld))) eqn:Ecr.
      + destruct Hnext as [Hrq HrqV].
        exact (ex_intro _ _ (readRp_load1x g s1 s1' s2 m' st' ld pkt0 rp E1 HS Eacc Ecr Hrq HrqV Hg)).
      + destruct Hnext as [Hry HryV].
        exact (ex_intro _ _ (readRp_load1 g s1 s1' s2 m' st' ld pkt0 rp E1 HS Eacc Ecr Hry
                               (eq_trans HryV (eq_trans (readRpRes_first _ _ _ rp) (lineVal_single ld rp))) Hg)).
  Qed.

  (* dataMem's rev-bit read: a single byte, never crossing *)
  Lemma readRp_dmRev :
    forall g (s1 s1' : IState) (s2 : SState) m' st' rc b rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccDmRev rc (RdArrived b rp) ->
      ReadRpNext (msReadRqSentV (iMemStA s1)) rp st' ->
      RELG g s1 s2 -> exists g', RELG g' s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' rc b rp E1 HS Eacc Hnext Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    pose proof Ha as Ha0; unfold AccessRel in Ha0; rewrite Eacc in Ha0.
    unfold RdStageRel in Ha0; cbv beta iota zeta in Ha0.
    destruct Ha0 as [[[_ HsV] _] [_ [_ [_ [_ [_ [_ [_ [Hsnd _]]]]]]]]].
    cbn [rdSecond] in Hsnd; subst b.
    rewrite HsV in Hnext; apply ReadRpNext_step in Hnext.
    rewrite crossesB_byte in Hnext; cbn [andb negb] in Hnext; destruct Hnext as [Hry HryV].
    rewrite readRpRes_first in HryV.
    exists (gWithAcc g (AccDmRev rc (RdReady (lineVal (revByteAddrOf config (rcBase rc)) byteSz rp)))).
    apply (readRp_frame g _ s1 s1' s2 _ st' E1 HS); [rewrite Eacc; reflexivity | | | exact Hg].
    - exact (rpAcc_dmRev g s1 s1' s2 st' rc false rp HS Eacc Hry HryV Ha).
    - intros _; unfold RevAccRel; exact I.
  Qed.

  (* The revoker's cap read: capability-aligned, never crossing *)
  Lemma readRp_revCap :
    forall g (s1 s1' : IState) (s2 : SState) m' st' b rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccRevCap (RdArrived b rp) ->
      ReadRpNext (msReadRqSentV (iMemStA s1)) rp st' ->
      RELG g s1 s2 -> exists g', RELG g' s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' b rp E1 HS Eacc Hnext Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    pose proof Ha as Ha0; unfold AccessRel in Ha0; rewrite Eacc in Ha0.
    unfold RdStageRel in Ha0; cbv beta iota zeta in Ha0.
    destruct Ha0 as [[[_ HsV] _] [_ [_ [_ [_ [_ Hsnd]]]]]].
    cbn [rdSecond] in Hsnd; subst b.
    rewrite HsV in Hnext; apply ReadRpNext_step in Hnext.
    rewrite iScanAddr_scanFull, crossesB_scanFull, <- iScanAddr_scanFull in Hnext.
    cbn [andb negb] in Hnext; destruct Hnext as [Hry HryV].
    rewrite readRpRes_first in HryV.
    exists (gWithAcc g (AccRevCap (RdReady (lineVal (iScanAddrA s1) capSz rp)))).
    apply (readRp_frame g _ s1 s1' s2 _ st' E1 HS); [rewrite Eacc; reflexivity | | | exact Hg].
    - exact (rpAcc_revCap g s1 s1' s2 st' false rp HS Eacc Hry HryV Ha).
    - exact (rpRacc_revCap g s1 s2 false rp Eacc).
  Qed.

  (* The revoker's rev-bit read: a single byte, never crossing *)
  Lemma readRp_revBit :
    forall g (s1 s1' : IState) (s2 : SState) m' st' b rp,
      s1' = writeSubTreeState NPMI s1 m' -> RpStepped s1 s1' st' ->
      g_acc pcAddrInit g = AccRevBit (RdArrived b rp) ->
      ReadRpNext (msReadRqSentV (iMemStA s1)) rp st' ->
      RELG g s1 s2 -> exists g', RELG g' s1' s2.
  Proof.
    intros g s1 s1' s2 m' st' b rp E1 HS Eacc Hnext Hg.
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    pose proof Ha as Ha0; unfold AccessRel in Ha0; rewrite Eacc in Ha0.
    unfold RdStageRel in Ha0; cbv beta iota zeta in Ha0.
    destruct Ha0 as [[[_ HsV] _] [_ [_ [_ [_ [_ Hsnd]]]]]].
    cbn [rdSecond] in Hsnd; subst b.
    rewrite HsV in Hnext; apply ReadRpNext_step in Hnext.
    rewrite crossesB_byte in Hnext; cbn [andb negb] in Hnext; destruct Hnext as [Hry HryV].
    rewrite readRpRes_first in HryV.
    exists (gWithAcc g (AccRevBit (RdReady (lineVal (revByteAddrOf config (iRevScanBaseA s1)) byteSz rp)))).
    apply (readRp_frame g _ s1 s1' s2 _ st' E1 HS); [rewrite Eacc; reflexivity | | | exact Hg].
    - exact (rpAcc_revBit g s1 s1' s2 st' false rp HS Eacc Hry HryV Ha).
    - exact (rpRacc_revBit g s1 s2 false rp Eacc).
  Qed.

  (* The data response buffer is emptied: the spec stutters, and the access in flight moves from
   * RdArrived to RdPend true (first line of a crossing load) or to RdReady *)
  Theorem stepOK_readRpStep :
    STEPOK (@readRpStep pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions type).
  Proof.
    intros s1 s1' s2 Hsem [g Hg].
    unfold readRpStep in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    rewrite iMem_read' in Hm'.
    remember (iMemA s1) as m eqn:EM; symmetry in EM.
    destruct m as [mr [mst [mrq [mrp []]]]].
    exists s2; split; [apply NilAction; reflexivity |].
    destruct (optValid mrp) eqn:Hv.
    2: { pose proof (readRpStep_noRp implRegions _ mr mst mrq mrp m' _ Hv Hm') as Em'; subst m'.
         exists g; rewrite (readRp_same s1 s1' mr mst mrq mrp EM E1); exact Hg. }
    pose proof Hg as Hg0; destruct Hg0 as [_ _ _ _ _ Ha _ _ _ _ _ _ _].
    assert (Erp0 : iReadRpA s1 = mrp) by (unfold iReadRp; rewrite EM; reflexivity).
    destruct (AccessRel_rpValid g s1 s2 Ha ltac:(rewrite Erp0; exact Hv)) as [b [rp [Erp Hcases]]].
    rewrite Erp0 in Erp; clear Erp0; subst mrp.
    assert (Est0 : iMemStA s1 = mst) by (unfold iMemSt; rewrite EM; reflexivity).
    pose proof (readRp_sent g s1 s2 b rp Ha Hcases) as Hsent; rewrite Est0 in Hsent.
    destruct (readRpStep_valid implRegions _ mr mst mrq rp m' _ Hsent Hm') as [st' [Em' Hnext]]; subst m'.
    pose proof (rpStepped_of s1 s1' mr mst mrq _ st' EM E1) as HS.
    rewrite <- Est0 in Hnext.
    destruct Hcases as [[ld [pkt0 Eacc]] | [[rc Eacc] | [Eacc | Eacc]]].
    - exact (readRp_load g s1 s1' s2 _ st' ld pkt0 b rp E1 HS Eacc Hnext Hg).
    - exact (readRp_dmRev g s1 s1' s2 _ st' rc b rp E1 HS Eacc Hnext Hg).
    - exact (readRp_revCap g s1 s1' s2 _ st' b rp E1 HS Eacc Hnext Hg).
    - exact (readRp_revBit g s1 s1' s2 _ st' b rp E1 HS Eacc Hnext Hg).
  Qed.
End ReadRpStep.
