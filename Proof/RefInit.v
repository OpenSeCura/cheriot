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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel RefCoreRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE REFINEMENT RELATION HOLDS ON INITIAL STATES
 * =========================================================================== *)

Local Abbreviation TS t := (TreeState DomainElemState t).

(* --- 1. Region Trees --- *)

Lemma InitStateConsistent_regionsTree_cons :
  forall (regionTree : MemRegion -> Tree DomainElem) (r : MemRegion) (rs : list MemRegion)
         (s : TS (regionsTree regionTree (r :: rs))),
    InitStateConsistent (regionsTree regionTree (r :: rs)) s ->
    InitStateConsistent (regionTree r) s.(Fst) /\ InitStateConsistent (regionsTree regionTree rs) s.(Snd).(Fst).
Proof.
  intros regionTree r rs s H.
  exact (conj (proj1 H) (proj1 (proj2 H))).
Qed.

Lemma InitStateConsistent_regionStateAt :
  forall (regionTree : MemRegion -> Tree DomainElem) (idx : nat) (regions : list MemRegion)
         (r0 : MemRegion) (pf : nth_error regions idx = Some r0) (s : TS (regionsTree regionTree regions)),
    InitStateConsistent (regionsTree regionTree regions) s ->
    InitStateConsistent (regionTree r0) (regionStateAt regionTree idx regions r0 pf s).
Proof.
  intros regionTree idx regions; revert idx.
  induction regions as [| r rs IH]; intros [| i'] r0 pf s Hs; try discriminate pf.
  - cbn [regionStateAt].
    set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                with eq_refl => eq_refl end).
    clearbody Heq; clear pf; destruct Heq.
    cbv beta iota.
    exact (proj1 (InitStateConsistent_regionsTree_cons regionTree r0 rs s Hs)).
  - cbn [regionStateAt].
    apply IH.
    exact (proj2 (InitStateConsistent_regionsTree_cons regionTree r rs s Hs)).
Qed.

Section RegionInit.
  Variable core : string.

  Lemma ExtRel_init :
    forall r (x : TS (externalMemRegionTree core r)) (y : TS (implExternalMemRegionTree core r)),
      InitStateConsistent (externalMemRegionTree core r) x ->
      InitStateConsistent (implExternalMemRegionTree core r) y ->
      ExtRel core r x y.
  Proof.
    intros r [[frq [frp [fw [fiq [fia []]]]]] [rq [rp [wr []]]]]
             [[[ifrq [ifrp [ifw [ifiq [ifia []]]]]] [irq [irp [iwr []]]]]
              [[frdy [fval [frpr [frd []]]]] [rqr [wrr [rpv [rpr [prq []]]]]]]]
           Hx Hy.
    cbn in Hx, Hy.
    destruct Hx as [[_ [_ [Hfw [Hfiq [Hfia _]]]]] [_ [_ [Hwr _]]]].
    destruct Hy as [[[_ [_ [Hifw [Hifiq [Hifia _]]]]] [_ [_ [Hiwr _]]]]
                    [_ [_ [Hwrr _]]]].
    subst.
    unfold ExtRel, implAccWrites; cbn.
    repeat split; reflexivity.
  Qed.

  Lemma RegionRelAt_init :
    forall cp pp i r (x : TS (memRegionTree core r)) (y : TS (implMemRegionTree core r)),
      allTreeInitDet (memRegionTree core r) = true ->
      InitStateConsistent (memRegionTree core r) x ->
      InitStateConsistent (implMemRegionTree core r) y ->
      RegionRelAt core cp pp i r x y.
  Proof.
    intros cp pp i r.
    unfold RegionRelAt, memRegionTree, implMemRegionTree.
    destruct (regionKind r) as [| children rdAct wrAct irq]; intros x y Hdet Hx Hy.
    - exact (ExtRel_init r x y Hx Hy).
    - right; right.
      destruct y as [y0 []]; cbn [Fst].
      exact (allTreeInitDet_InitStateConsistent_eq _ x y0 Hdet Hx (proj1 Hy)).
  Qed.

  Lemma MemRelPost_init :
    forall cp pp l i (ms : TS (specMemTree core l)) (mi : TS (implRegionsTree core l)),
      Forall (fun r => allTreeInitDet (memRegionTree core r) = true) l ->
      InitStateConsistent (specMemTree core l) ms ->
      InitStateConsistent (implRegionsTree core l) mi ->
      MemRelPost core cp pp i l ms mi.
  Proof.
    intros cp pp l; induction l as [| r l IH]; intros i ms mi Hdet Hms Hmi; cbn [MemRelPost]; [exact I |].
    inversion Hdet as [| ? ? Hr Hl]; subst.
    destruct (InitStateConsistent_regionsTree_cons (memRegionTree core) r l ms Hms) as [Hms0 Hms1].
    destruct (InitStateConsistent_regionsTree_cons (implMemRegionTree core) r l mi Hmi) as [Hmi0 Hmi1].
    split; [exact (RegionRelAt_init cp pp i r _ _ Hr Hms0 Hmi0) | exact (IH (S i) _ _ Hl Hms1 Hmi1)].
  Qed.

  Lemma MemRelPre_init :
    forall cp pp sRev iRev post l i
           (ms : TS (specMemTree core (l ++ sRev :: post))) (mi : TS (implRegionsTree core (l ++ iRev :: post))),
      Forall (fun r => allTreeInitDet (memRegionTree core r) = true) l ->
      Forall (fun r => allTreeInitDet (memRegionTree core r) = true) post ->
      InitStateConsistent (specMemTree core (l ++ sRev :: post)) ms ->
      InitStateConsistent (implRegionsTree core (l ++ iRev :: post)) mi ->
      MemRelPre core cp pp i l sRev iRev post ms mi.
  Proof.
    intros cp pp sRev iRev post l; induction l as [| r l IH]; intros i ms mi Hl Hpost Hms Hmi;
      cbn [MemRelPre].
    - destruct (InitStateConsistent_regionsTree_cons (memRegionTree core) sRev post ms Hms) as [_ Hms1].
      destruct (InitStateConsistent_regionsTree_cons (implMemRegionTree core) iRev post mi Hmi) as [_ Hmi1].
      exact (MemRelPost_init cp pp post (S i) _ _ Hpost Hms1 Hmi1).
    - inversion Hl as [| ? ? Hr Hl']; subst.
      destruct (InitStateConsistent_regionsTree_cons (memRegionTree core) r (l ++ sRev :: post) ms Hms)
        as [Hms0 Hms1].
      destruct (InitStateConsistent_regionsTree_cons (implMemRegionTree core) r (l ++ iRev :: post) mi Hmi)
        as [Hmi0 Hmi1].
      split; [exact (RegionRelAt_init cp pp i r _ _ Hr Hms0 Hmi0) | exact (IH (S i) _ _ Hl' Hpost Hms1 Hmi1)].
  Qed.

  Lemma AllPorts_init :
    forall (P : forall r, TS (implExternalMemRegionTree core r) -> Prop),
      (forall r y, InitStateConsistent (implExternalMemRegionTree core r) y -> P r y) ->
      forall l (mi : TS (implRegionsTree core l)),
        InitStateConsistent (implRegionsTree core l) mi -> AllPorts core P l mi.
  Proof.
    intros P HP l; induction l as [| r l IH]; intros mi Hmi; cbn [AllPorts]; [exact I |].
    destruct (InitStateConsistent_regionsTree_cons (implMemRegionTree core) r l mi Hmi) as [H0 H1].
    split; [| exact (IH _ H1)].
    revert H0; generalize (mi.(Fst)); unfold RegionPort, implMemRegionTree.
    destruct (regionKind r); intros y Hy; [exact (HP r y Hy) | exact I].
  Qed.

  Lemma SnapshotOK_init :
    forall l fwcs (m : TS (specMemTree core l)),
      InitStateConsistent (specMemTree core l) m -> SnapshotOK core fwcs l m.
  Proof.
    induction l as [| r l IH]; intros fwcs m Hm; cbn [SnapshotOK]; [exact I |].
    destruct (InitStateConsistent_regionsTree_cons (memRegionTree core) r l m Hm) as [H0 H1].
    split; [| exact (IH _ _ H1)].
    revert H0; generalize (m.(Fst)); unfold RegionSnapshotOK, memRegionTree.
    destruct (regionKind r); intros x Hx; [| exact I].
    destruct x as [[frq [frp [fw [fiq [fia []]]]]] [rq [rp [wr []]]]]; cbn in Hx |- *.
    destruct Hx as [[_ [_ [_ [_ [Hfia _]]]]] [_ [_ [Hwr _]]]].
    subst; cbn; lia.
  Qed.

  (* --- 2. Devices --- *)

  Lemma ClintRel_refl : forall x, ClintRel core x x.
  Proof.
    intros [a [b [c [d []]]]]; unfold ClintRel, clintWithSampled, clintSampled; cbn.
    split; [reflexivity | auto].
  Qed.

  Lemma PlicRelSame_refl : forall n x, PlicRelSame core n x x.
  Proof.
    intros n [a [b [c [d [e [f [g [h []]]]]]]]]; unfold PlicRelSame, plicWithMeip, plicMeipOf; cbn.
    split; [reflexivity | auto].
  Qed.

  Lemma allTreeInitDet_node_regs :
    forall (name : string) (g : nat -> string) (dom : string) (k : Kind) (v : type k) (l : list nat),
      allTreeInitDet (Node name (map (fun idx => Leaf (g idx) (dom, EReg (Build_Reg k (Some v) false))) l)) = true.
  Proof.
    intros name g dom k v l; induction l as [| a l IH]; [reflexivity |].
    cbn [map allTreeInitDet] in *; exact IH.
  Qed.

  Lemma allTreeInitDet_Node_cons :
    forall nm c cs, allTreeInitDet (Node nm (c :: cs)) = andb (allTreeInitDet c) (allTreeInitDet (Node nm cs)).
  Proof. reflexivity. Qed.

  Lemma allTreeInitDet_plicTree : forall n, allTreeInitDet (plicTree core n) = true.
  Proof.
    intros n.
    assert (H1 : allTreeInitDet (Node "priorities" (priorityLeaves core n)) = true)
      by (unfold priorityLeaves; apply allTreeInitDet_node_regs).
    assert (H2 : allTreeInitDet (Node "pending" (pendingLeaves core n)) = true)
      by (unfold pendingLeaves; apply allTreeInitDet_node_regs).
    assert (H3 : allTreeInitDet (Node "enables" (enableLeaves core n)) = true)
      by (unfold enableLeaves; apply allTreeInitDet_node_regs).
    assert (H4 : allTreeInitDet (Node "in_service" (inServiceLeaves core n)) = true)
      by (unfold inServiceLeaves; apply allTreeInitDet_node_regs).
    unfold plicTree, plicChildren.
    rewrite !allTreeInitDet_Node_cons, H1, H2, H3, H4.
    reflexivity.
  Qed.

  Lemma PlicRel_init :
    forall n1 n2 (e : n1 = n2) (x : TS (plicTree core n1)) (y : TS (plicTree core n2)),
      InitStateConsistent (plicTree core n1) x ->
      InitStateConsistent (plicTree core n2) y ->
      PlicRel core n1 n2 x y.
  Proof.
    intros n1 n2 e x y Hx Hy.
    exists e; destruct e; cbn [eq_rect].
    rewrite (allTreeInitDet_InitStateConsistent_eq _ x y (allTreeInitDet_plicTree n1) Hx Hy).
    apply PlicRelSame_refl.
  Qed.

  Lemma RevRel_init :
    forall (xs : TS (Node "revoker" (revokerChildren core []))) (xi : TS (implRevokerTree core)),
      InitStateConsistent (Node "revoker" (revokerChildren core [])) xs ->
      InitStateConsistent (implRevokerTree core) xi ->
      RevRel core false xs xi.
  Proof.
    intros [b [t [c [ep [ist [irq [sc []]]]]]]] [b' [t' [c' [ep' [ist' [irq' [sc' [ph [cap [bs [hit []]]]]]]]]]]]
           Hxs Hxi.
    cbn in Hxs, Hxi.
    destruct Hxs as [Hb [Ht [Hc [Hep [Hist [Hirq [Hsc _]]]]]]].
    destruct Hxi as [Hb' [Ht' [Hc' [Hep' [Hist' [Hirq' [Hsc' _]]]]]]].
    subst.
    unfold RevRel, projImplRevokerArchState, revWithScanAddr, revScanAddr; cbn.
    reflexivity.
  Qed.

  Lemma ClintInv_init :
    forall x, InitStateConsistent (Node "clint" (clintChildren core)) x -> ClintInv core x.
  Proof.
    intros [a [b [c [d []]]]] Hx; cbn in Hx.
    destruct Hx as [_ [_ [_ [Hd _]]]]; subst.
    unfold ClintInv, clintSampled; cbn; discriminate.
  Qed.

  Lemma PlicInv_init :
    forall n x, InitStateConsistent (plicTree core n) x -> PlicInv core x.
  Proof.
    intros n [a [b [c [d [e [f [g [h []]]]]]]]] Hx; cbn in Hx.
    destruct Hx as [_ [_ [_ [_ [_ [Hf _]]]]]]; subst.
    unfold PlicInv, plicMeipOf; cbn; discriminate.
  Qed.

End RegionInit.

(* --- 3. Register Reads --- *)

Lemma evalReadRegsList_head :
  forall (t : Tree DomainElem) (k : Kind) (sz : Z) (rk : RegOfKind (t:=t) k) (rest : list (RegOfKind (t:=t) k))
         (s : TS t),
    (Z.of_nat (S (length rest)) <= 2 ^ sz)%Z ->
    evalReadRegsList (rk :: rest) (Zmod.zero : bits sz) s = readRegOfKind rk s.
Proof.
  intros t k sz rk rest s Hpow.
  unfold evalReadRegsList; cbn [evalReadRegsListHelper].
  rewrite (isEq_Bit_of_Z_eq (Zmod.zero : bits sz) 0) by (rewrite Zmod.to_Z_0; reflexivity).
  rewrite evalReadRegsListHelper_above by (rewrite ?Zmod.to_Z_0; lia).
  cbn [fold_left].
  rewrite evalOrBinary_getDefault_l.
  reflexivity.
Qed.

Lemma readPcc_init_addr :
  forall (core : string) (pcAddrInit : Z) (rf : TS (rfTree core pcAddrInit)),
    InitStateConsistent (rfTree core pcAddrInit) rf ->
    (readPcc core pcAddrInit rf).(Snd).(Snd).(Fst) = (Zmod.of_Z _ pcAddrInit : bits AddrSz).
Proof.
  intros core pcAddrInit rf Hrf.
  rewrite (allTreeInitDet_InitState _ rf (allTreeInitDet_RfTree core pcAddrInit) Hrf).
  unfold readPcc, readGpr, gprPathsWithKind.
  rewrite evalReadRegsList_head by (cbn; lia).
  unfold readRegOfKind.
  rewrite eq_rect_Kind_refl.
  reflexivity.
Qed.

Lemma length_genCollect_cons :
  forall (regionTree : MemRegion -> Tree DomainElem) (k : Kind)
         (getActions : forall r : MemRegion, list (forall ty, Action ty (regionTree r) k)) r rs,
    length (@genCollectRegionActions regionTree k getActions (r :: rs)) =
    (length (getActions r) + length (@genCollectRegionActions regionTree k getActions rs))%nat.
Proof.
  intros; cbn [genCollectRegionActions]; rewrite length_app, !length_map; reflexivity.
Qed.

(* --- 4. The Relation on Initial States --- *)

Section RefInitMain.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf core pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf core pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance core specRegions.
  Variable clint : @ClintInstance core implRegions.
  Variable plicS : @PlicInstance core (S (S (length (collectIrqActions core specRegions)))) specRegions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions core implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  (* The regions shared by both lists start in a determined state *)
  Hypothesis HdetPre : Forall (fun r => allTreeInitDet (memRegionTree core r) = true) pre.
  Hypothesis HdetPost : Forall (fun r => allTreeInitDet (memRegionTree core r) = true) post.

  Local Abbreviation ITree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation STree := (SpecTree core pcAddrInit specRegions).

  Lemma length_collectIrqActions_pre :
    forall l,
      length (collectIrqActions core (l ++ specRevRegion core revBase revPfB revPfA :: post)) =
      length (collectIrqActions core (l ++ implRevRegion core revBase revPfB revPfA :: post)).
  Proof.
    induction l as [| r l IH]; cbn [app]; unfold collectIrqActions in *;
      rewrite !length_genCollect_cons; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma nIrq_eq :
    S (S (length (collectIrqActions core specRegions))) = S (S (length (collectIrqActions core implRegions))).
  Proof.
    unfold specRegionsOf, implRegionsOf; rewrite length_collectIrqActions_pre; reflexivity.
  Qed.

  Variable s1 : TS ITree.
  Variable s2 : TS STree.
  Hypothesis H1 : InitStateConsistent ITree s1.
  Hypothesis H2 : InitStateConsistent STree s2.

  Local Abbreviation IMEM := (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IFETCH := (impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IDEC := (impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IEXEC := (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IDM := (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IWB := (impl_waitBits core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IRF := (impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).
  Local Abbreviation IMD := (impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1).

  Lemma init_mem : InitStateConsistent (implMemTree core implRegions) IMEM.
  Proof. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj1 H1)))))). Qed.
  Lemma init_fetch : InitStateConsistent (implFetchTree core pcAddrInit fetchCapacity instCapacity) IFETCH.
  Proof. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 H1))))))). Qed.
  Lemma init_dec : InitStateConsistent (implDecodeTree core decodeCapacity) IDEC.
  Proof. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H1)))))))). Qed.
  Lemma init_exec : InitStateConsistent (implExecuteTree core) IEXEC.
  Proof. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H1))))))))). Qed.
  Lemma init_dm : InitStateConsistent (implDataMemTree core dataMemCapacity) IDM.
  Proof. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H1)))))))))). Qed.
  Lemma init_wb : InitStateConsistent (waitBitsTree core) IWB.
  Proof. exact (proj1 (proj1 (proj2 (proj1 H1)))). Qed.
  Lemma init_rf : InitStateConsistent (rfTree core pcAddrInit) IRF.
  Proof. exact (proj1 (proj1 (proj1 H1))). Qed.
  Lemma init_srf : InitStateConsistent (rfTree core pcAddrInit) (spec_rf core pcAddrInit specRegions s2).
  Proof. exact (proj1 (proj1 (proj1 H2))). Qed.
  Lemma init_smem : InitStateConsistent (specMemTree core specRegions) (spec_mem core pcAddrInit specRegions s2).
  Proof. exact (proj1 (proj1 (proj2 (proj1 H2)))). Qed.

  Lemma init_regions : InitStateConsistent (implRegionsTree core implRegions) IMEM.(Fst).
  Proof. exact (proj1 init_mem). Qed.

  Lemma init_flush_eq :
    flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1 =
    spec_rf core pcAddrInit specRegions s2.
  Proof.
    rewrite (InitStateConsistent_flushMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1 H1).
    exact (allTreeInitDet_InitStateConsistent_eq _ _ _ (allTreeInitDet_RfTree core pcAddrInit) init_rf init_srf).
  Qed.

  Lemma readWaitBit_init : forall r, readWaitBit core r IWB = false.
  Proof.
    intros r.
    rewrite (allTreeInitDet_InitState _ _ (eq_refl : allTreeInitDet (waitBitsTree core) = true) init_wb).
    unfold readWaitBit, evalReadRegsList.
    assert (Hall : forall (paths : list (RegOfKind (t:=waitBitsTree core) Bool)) curr (acc : list (type Bool)),
               (forall rk, In rk paths -> readRegOfKind rk (InitState (waitBitsTree core)) = false) ->
               Forall (fun b => b = false) acc ->
               evalReadRegsListHelper curr acc paths r (InitState (waitBitsTree core)) = false).
    { induction paths as [| rk rest IH]; intros curr acc Hp Hacc; cbn [evalReadRegsListHelper].
      - rewrite (@fold_left_evalOrBinary_default Bool acc (getDefault Bool)); [reflexivity |].
        eapply Forall_impl; [| exact Hacc]; intros b Hb; cbv beta in Hb |- *; rewrite Hb; reflexivity.
      - apply IH; [intros rk' Hin; apply Hp; right; exact Hin |].
        constructor; [| exact Hacc].
        destruct (isEq _ _); [apply Hp; left; reflexivity | reflexivity]. }
    apply Hall; [| constructor].
    intros rk Hin.
    unfold gprWaitPathsWithKind in Hin; cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [unfold readRegOfKind; rewrite eq_rect_Kind_refl; reflexivity |]).
    destruct Hin.
  Qed.

  Definition ghost0 : Ghost core pcAddrInit :=
    mkGhost core pcAddrInit [] (spec_rf core pcAddrInit specRegions s2) None false [] AccNone.

  Theorem RefRel_init :
    RefRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
      mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
      clintS clint plicS plic initLine fwcs s1 s2.
  Proof.
    pose proof init_fetch as Hf.
    pose proof init_dec as Hd.
    pose proof init_exec as He.
    pose proof init_dm as Hdm.
    pose proof init_mem as Hm.
    exists ghost0; constructor.
    - (* RfRel *)
      unfold RfRel; cbn [g_chain g_rf0 g_cnwb ghost0 cnwbApply].
      split; [reflexivity |].
      split; [unfold iFlush; rewrite init_flush_eq; apply GChainNil |].
      split; [intros d v Hc; discriminate Hc |].
      intros G1 e G2 HG; destruct G1; discriminate HG.
    - (* MemRelC *)
      unfold MemRelC, MemRel; cbn [g_revAdv ghost0].
      split; [| split].
      + split; [| split; [| split]].
        * exact (MemRelPre_init core _ _ _ _ post pre 0 _ _ HdetPre HdetPost init_smem init_regions).
        * unfold sClint, iClint, specClintState, implClintState, sMem, iRegions, iMem.
          rewrite (allTreeInitDet_InitStateConsistent_eq (Node "clint" (clintChildren core)) _ _ eq_refl
                     (InitStateConsistent_regionStateAt (memRegionTree core) clintS.(clintIdx) specRegions (clintRegion clintS) clintS.(pfClint) _ init_smem)
                     (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) clint.(clintIdx) implRegions (clintRegion clint) clint.(pfClint) _ init_regions))).
          apply ClintRel_refl.
        * exact (PlicRel_init core (S (S (length (collectIrqActions core specRegions)))) (S (S (length (collectIrqActions core implRegions)))) nIrq_eq _ _
                   (InitStateConsistent_regionStateAt (memRegionTree core) plicS.(plicIdx) specRegions (plicRegion plicS) plicS.(pfPlic) _ init_smem)
                   (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) plic.(plicIdx) implRegions (plicRegion plic) plic.(pfPlic) _ init_regions))).
        * exact (RevRel_init core _ _
                   (InitStateConsistent_regionStateAt (memRegionTree core) (length pre) specRegions (specRevRegion core revBase revPfB revPfA) (nth_error_app_cons_len pre (specRevRegion core revBase revPfB revPfA) post) _ init_smem)
                   (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) (length pre) implRegions (implRevRegion core revBase revPfB revPfA) (nth_error_app_cons_len pre (implRevRegion core revBase revPfB revPfA) post) _ init_regions))).
      + split.
        * exact (ClintInv_init core _
                   (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) clint.(clintIdx) implRegions (clintRegion clint) clint.(pfClint) _ init_regions))).
        * exact (PlicInv_init core (S (S (length (collectIrqActions core implRegions)))) _
                   (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) plic.(plicIdx) implRegions (plicRegion plic) plic.(pfPlic) _ init_regions))).
      + exact (SnapshotOK_init core _ fwcs _ init_smem).
    - (* LatchRel *)
      intros e Hin; destruct Hin.
    - (* ReplayRel *)
      intros G1 e G2 rfe HG; destruct G1; discriminate HG.
    - (* EagerRel *)
      left; reflexivity.
    - (* AccessRel *)
      unfold AccessRel; cbn [g_acc ghost0 g_revAdv].
      pose proof (proj1 (proj2 Hm)) as Hst; pose proof (proj1 (proj2 (proj2 (proj2 Hm)))) as Hrp.
      cbn in Hst, Hrp.
      unfold iMemSt, iReadRp, iMem; rewrite Hst, Hrp.
      split; [reflexivity |]; split; [reflexivity |].
      split.
      { unfold PortsQuiet.
        apply (AllPorts_init core); [| exact init_regions].
        intros r y Hy.
        destruct y as [[[ifrq [ifrp [ifw [ifiq [ifia []]]]]] [irq [irp [iwr []]]]]
                       [[frdy [fval [frpr [frd []]]]] [rqr [wrr [rpv [rpr [prq []]]]]]]].
        cbn in Hy.
        destruct Hy as [[[_ [_ [_ [_ [_ _]]]]] [Hirq [Hirp [_ _]]]] [_ [Hrqr [_ [_ [_ [Hprq _]]]]]]].
        subst.
        unfold extPortRq, extDataQuiet, implDataAccRqs; cbn.
        split; reflexivity. }
      split; [reflexivity |].
      split.
      { pose proof (proj2 Hdm) as Hdst; cbn in Hdst.
        unfold dmNotAccessing, iDmSt, iDm; unfold dataMem_state; rewrite (proj1 Hdst).
        split; reflexivity. }
      split.
      { pose proof (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) (length pre) implRegions (implRevRegion core revBase revPfB revPfA) (nth_error_app_cons_len pre (implRevRegion core revBase revPfB revPfA) post) _ init_regions))
          as Hrev.
        unfold revNotReading, iRevPhase, iRev, implRevState, iRegions, iMem.
        set (xi := (regionStateAt (implMemRegionTree core) (length pre) implRegions
                      (implRevRegion core revBase revPfB revPfA)
                      (nth_error_app_cons_len pre (implRevRegion core revBase revPfB revPfA) post)
                      IMEM.(Fst)).(Fst)) in *.
        clearbody xi.
        destruct xi as [b [t [c [ep [ist [irq [sc [ph [cap [bs [hit []]]]]]]]]]]].
        cbn in Hrev.
        destruct Hrev as [_ [_ [_ [_ [_ [_ [_ [Hph _]]]]]]]].
        cbn; rewrite Hph.
        split; reflexivity. }
      pose proof (proj1 (proj2 (proj2 (proj1 H2)))) as Hsl; cbn in Hsl.
      unfold sSecond, spec_core; rewrite Hsl; reflexivity.
    - (* CnwbRel *)
      unfold CnwbRel; cbn [g_cnwb ghost0].
      split; [intros _; reflexivity |].
      pose proof (proj2 Hdm) as Hdst; cbn in Hdst.
      unfold iDmSt, iDm, dataMem_state; rewrite (proj1 Hdst).
      intros Hc; discriminate Hc.
    - (* DmQueueRel *)
      unfold DmQueueRel, iDmBuf, iDm, dataMem_fifo; cbn [g_chain g_acc ghost0].
      rewrite (InitStateConsistent_fifo_to_list core dataMemCapacity MemFenceReq _ (proj1 (proj1 Hdm))).
      reflexivity.
    - (* FenceRel *)
      unfold FenceRel.
      split.
      { unfold iFenceIPending, iExec, exec_fenceIPending.
        rewrite (proj1 (proj2 He)); intros Hc; discriminate Hc. }
      intros Hnot; exfalso; apply Hnot.
      unfold NoFenceIWait.
      apply (AllPorts_init core); [| exact init_regions].
      intros r y Hy.
      destruct y as [[[ifrq [ifrp [ifw [ifiq [ifia []]]]]] [irq [irp [iwr []]]]] rest].
      cbn in Hy |- *.
      exact (proj1 (proj2 (proj2 (proj1 (proj1 Hy))))).
    - (* ScoreRel *)
      unfold ScoreRel, olderWriters, dmInFlightDst, d2aWriters, iD2a, iDmBuf, iDmSt, iDm, iDecode,
        dataMem_fifo, dataMem_state, decode_toAluFifo.
      cbn [g_d2aFo ghost0].
      pose proof (proj2 Hdm) as Hdst; cbn in Hdst; rewrite (proj1 Hdst).
      rewrite (InitStateConsistent_fifo_to_list core dataMemCapacity MemFenceReq _ (proj1 (proj1 Hdm))).
      rewrite (InitStateConsistent_fifo_to_list core decodeCapacity DecodeToAluEntry _ (proj1 (proj1 (proj2 Hd)))).
      rewrite (InitStateConsistent_extractMulDivEntries core mulCapacity divCapacity mulStages divStages mulDivMode
                 _ (InitStateConsistent_impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                      dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config implRegions s1 H1)).
      cbv zeta.
      change (dmLoadRp (getDefault DataMemState)) with false.
      change (dmRevRq (getDefault DataMemState)) with false.
      change (dmRevRp (getDefault DataMemState)) with false.
      cbn [filter map app fst length].
      split; [constructor |].
      split; [intros r; unfold iWb; rewrite readWaitBit_init; split; [discriminate | intros []] |].
      split; [reflexivity |].
      intros l1 j l2 fo Hd2a; destruct l1; discriminate Hd2a.
    - (* FrontRel *)
      unfold FrontRel, iD2a, iInstBuf, iFetchBuf, iDecode, iFetch, decode_toAluFifo, fetch_instFifo,
        fetch_fetchBufFifo.
      rewrite (InitStateConsistent_fifo_to_list core decodeCapacity DecodeToAluEntry _ (proj1 (proj1 (proj2 Hd)))).
      rewrite (InitStateConsistent_fifo_to_list core instCapacity AssembledInst _
                 (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hf))))))))).
      rewrite (InitStateConsistent_fifo_to_list core fetchCapacity FetchBufEntry _
                 (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hf)))))))).
      split; [exists [], []; split; [reflexivity | split; constructor] |].
      split; [exists [], []; split; [reflexivity | split; constructor] |].
      split; [exists [], []; split; [reflexivity | split; constructor] |].
      split; [intros Hex; inversion Hex |].
      split; [intros [Hex | Hex]; inversion Hex |].
      split.
      + unfold liveInsts; cbn [combine filter map app g_d2aFo ghost0].
        unfold iD2a, iInstBuf, iDecode, iFetch, decode_toAluFifo, fetch_instFifo.
        rewrite (InitStateConsistent_fifo_to_list core decodeCapacity DecodeToAluEntry _ (proj1 (proj1 (proj2 Hd)))).
        rewrite (InitStateConsistent_fifo_to_list core instCapacity AssembledInst _
                   (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hf))))))))).
        unfold LiveChain; cbn [LiveChainG combine filter map app].
        unfold FrontierRel, iFetchBuf, iFetch, fetch_fetchBufFifo.
        rewrite (InitStateConsistent_fifo_to_list core fetchCapacity FetchBufEntry _
                   (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hf)))))))).
        cbn [filter FbChain].
        split; [exact I |]; split; [constructor |].
        unfold iStraddle, iFetch, fetch_straddleOpt.
        rewrite (proj1 (proj2 (proj2 (proj2 Hf)))).
        change (optValid (getDefault (Option StraddleHalf))) with false.
        cbv iota beta.
        unfold iFetchPc, iFetch, fetch_pc, iPcc, iRf.
        rewrite (proj1 Hf), (readPcc_init_addr core pcAddrInit _ init_rf).
        reflexivity.
      + unfold FetchRespRel.
        apply (AllPorts_init core); [| exact init_regions].
        intros r y Hy.
        unfold fbInRegion, iFetchBuf, iFetch, fetch_fetchBufFifo.
        rewrite (InitStateConsistent_fifo_to_list core fetchCapacity FetchBufEntry _
                   (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hf)))))))).
        destruct y as [[[ifrq [ifrp [ifw [ifiq [ifia []]]]]] [irq [irp [iwr []]]]]
                       [[frdy [fval [frpr [frd []]]]] [rqr [wrr [rpv [rpr [prq []]]]]]]].
        cbn in Hy.
        destruct Hy as [[[Hifrq [Hifrp _]] _] [[Hfrdy [_ [_ [Hfrd _]]]] _]].
        subst.
        exists []; unfold implFetchAccRqs; cbn.
        split; [reflexivity |]; split; [reflexivity |].
        intros Hc; discriminate Hc.
    - (* WfRel *)
      unfold WfRel, iFetch, iDecode, iDm.
      split; [exact (InitStateConsistent_fifo_wf core fetchCapacity FetchBufEntry _
                       (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hf)))))))) |].
      split; [exact (InitStateConsistent_fifo_wf core instCapacity AssembledInst _
                       (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hf))))))))) |].
      split; [exact (InitStateConsistent_fifo_wf core decodeCapacity DecodeToAluEntry _ (proj1 (proj1 (proj2 Hd)))) |].
      split; [exact (InitStateConsistent_fifo_wf core dataMemCapacity MemFenceReq _ (proj1 (proj1 Hdm))) |].
      apply (AllPorts_init core); [| exact init_regions].
      intros r y Hy; split.
      + exact (InitStateConsistent_ImplExternalRegionHandshakeInv core r y Hy).
      + exact (InitStateConsistent_RegionFenceICountInv core r y.(Fst) (proj1 Hy)).
    - (* RevokerRel: the revoker starts Idle and no access is in flight *)
      pose proof (proj1 (InitStateConsistent_regionStateAt (implMemRegionTree core) (length pre) implRegions (implRevRegion core revBase revPfB revPfA) (nth_error_app_cons_len pre (implRevRegion core revBase revPfB revPfA) post) _ init_regions))
        as Hrev.
      unfold RevokerRel, RevAccRel; cbn [g_acc ghost0].
      unfold iRevPhase, iRev, implRevState, iRegions, iMem.
      set (xi := (regionStateAt (implMemRegionTree core) (length pre) implRegions
                    (implRevRegion core revBase revPfB revPfA)
                    (nth_error_app_cons_len pre (implRevRegion core revBase revPfB revPfA) post)
                    IMEM.(Fst)).(Fst)) in *.
      clearbody xi.
      destruct xi as [b [t [c [ep [ist [irq [sc [ph [cap [bs [hit []]]]]]]]]]]].
      cbn in Hrev.
      destruct Hrev as [_ [_ [_ [_ [_ [_ [_ [Hph _]]]]]]]].
      cbn [Fst Snd]; rewrite Hph.
      split; [intros Hc; discriminate Hc |].
      split; [intros Hc; discriminate Hc |].
      split; [intros Hc; discriminate Hc |].
      split; [intros Hc; discriminate Hc | exact I].
  Qed.

End RefInitMain.
