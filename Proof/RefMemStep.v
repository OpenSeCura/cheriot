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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefMemRel RefCoreRel RefFrame RefPeriph RefSpecRead.
From Cheriot.Proof Require Import RefRevoker ImplSpec RefFetch.

Import ListNotations.
Local Abbreviation TS t := (TreeState DomainElemState t).

(* Milestone 4: the memory `state` machine and the region ports refine the spec.
 *
 * 1. `RdRqPortRegion`: one data read-request port step of an ExternalMem region
 *    (`implExternalLineReadRqPort`): nothing when no read is staged, otherwise the staged read is
 *    sent and, when accepted, leaves `portRq` (`rdRqPort_cases`, `rdRqSent`); over a region list,
 *    one ExternalMem position steps and the others are unchanged (`rdRqPorts_step`). *)

Section RdRqPortRegion.
  Variable core : string.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree core r)).

  (* The staged request of the region's data port: valid, a Read, and its address *)
  Definition portRqIsRead r (y : ExtI r) : bool :=
    andb y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst)
         (Zmod.eqb y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).(Snd) (Zmod.of_Z _ 0)).
  Definition portRqAddr r (y : ExtI r) : type Addr :=
    Zmod.of_Z _ (Zmod.to_Z y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst).(Fst)).

  (* The region after its port sent the read of line `L`, accepted or not *)
  Definition rdRqSent r (y : ExtI r) (L : type Addr) (rdy : bool) : ExtI r :=
    ((y.(Fst).(Fst) ,, ((L :: y.(Fst).(Snd).(Fst)) ,, y.(Fst).(Snd).(Snd))) ,,
     (y.(Snd).(Fst) ,, ((rdy :: y.(Snd).(Snd).(Fst)) ,,
       (if rdy
        then (y.(Snd).(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
               (y.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
                (getDefault (Option PortRq) ,, y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))
        else y.(Snd).(Snd).(Snd))))).

  Lemma rdRqPort_cases :
    forall r (env : Env (implExternalMemRegionTree core r)) (y y' : ExtI r) v,
      SemAction env (@implExternalLineReadRqPort core r type) y y' v ->
      (portRqIsRead r y = false /\ y' = y) \/
      (portRqIsRead r y = true /\ exists rdy, y' = rdRqSent r y (portRqAddr r y) rdy).
  Proof.
    intros r env y y' v Hsem.
    unfold implExternalLineReadRqPort in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn in Hsem.
    unfold portRqIsRead; destruct (andb _ _) eqn:Ec.
    - right; split; [reflexivity |].
      destruct Hsem as [rdy [_ Hrest]]; exists rdy.
      unfold cast_send_expr in Hrest.
      match type of Hrest with context [@eq_rect Kind ?k1 ?P ?v ?k2 ?pf] =>
        rewrite (eq_rect_Kind_refl k1 P v pf : @eq_rect Kind k1 P v k2 pf = v) in Hrest end.
      destruct rdy; destruct Hrest as [<- _]; reflexivity.
    - left; split; [reflexivity |]; destruct Hsem as [<- _]; reflexivity.
  Qed.

  Lemma extPortRq_someRead :
    forall r (y : ExtI r) L, extPortRq core r y = someRead L -> portRqIsRead r y = true /\ portRqAddr r y = L.
  Proof.
    intros r y L H; unfold portRqIsRead, portRqAddr; unfold extPortRq in H; rewrite H.
    cbn; split; [reflexivity |].
    match goal with |- context [(@Zmod.unsigned ?m L mod _)%Z] =>
      pose proof (@Zmod.unsigned_pos_bound m L ltac:(reflexivity)) as HL;
      change (0 <= @Zmod.unsigned m L < 4294967296)%Z in HL end.
    rewrite Z.mod_small by lia.
    match goal with |- context [(Z.sgn ?u =? -1)%Z] =>
      replace (Z.sgn u =? -1)%Z with false
        by (symmetry; apply Z.eqb_neq; pose proof (proj2 (Z.sgn_nonneg u) (proj1 HL)); lia) end.
    rewrite Z.abs_eq, (proj2 (Z.ltb_lt _ _)) by lia; cbn [negb andb].
    apply Zmod.of_Z_to_Z.
  Qed.
  (* What the relation reads from a region after its port sent a read *)
  Lemma implDataAccRqs_rdRqSent : forall r (y : ExtI r) L rdy,
    implDataAccRqs core r (rdRqSent r y L rdy) = if rdy then L :: implDataAccRqs core r y else implDataAccRqs core r y.
  Proof. intros r y L [|]; reflexivity. Qed.

  Lemma extPortRq_rdRqSent : forall r (y : ExtI r) L rdy,
    extPortRq core r (rdRqSent r y L rdy) = if rdy then getDefault (Option PortRq) else extPortRq core r y.
  Proof. intros r y L [|]; reflexivity. Qed.

  Lemma rdRqSent_rps : forall r (y : ExtI r) L rdy,
    (rdRqSent r y L rdy).(Fst).(Snd).(Snd).(Fst) = y.(Fst).(Snd).(Snd).(Fst).
  Proof. reflexivity. Qed.

  Lemma rdRqSent_fetch : forall r (y : ExtI r) L rdy,
    (rdRqSent r y L rdy).(Fst).(Fst) = y.(Fst).(Fst) /\ (rdRqSent r y L rdy).(Snd).(Fst) = y.(Snd).(Fst).
  Proof. split; reflexivity. Qed.

  Lemma implAccWrites_rdRqSent : forall r (y : ExtI r) L rdy,
    implAccWrites core r (rdRqSent r y L rdy) = implAccWrites core r y.
  Proof. intros r y L [|]; reflexivity. Qed.

  Lemma ExtRel_rdRqSent : forall r x (y : ExtI r) L rdy,
    ExtRel core r x y -> ExtRel core r x (rdRqSent r y L rdy).
  Proof. intros r x y L [|] H; exact H. Qed.
  (* One region's read-request port step *)
  Definition RegionRdRqStep (r : MemRegion) : TS (implMemRegionTree core r) -> TS (implMemRegionTree core r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree core r k) -> TS (implMemRegionKindTree core r k) -> Prop with
    | ExternalMem => fun y y' => (portRqIsRead r y = false /\ y' = y) \/
                                 (portRqIsRead r y = true /\ exists rdy, y' = rdRqSent r y (portRqAddr r y) rdy)
    | CustomMem _ _ _ _ => fun _ _ => False
    end.

  (* One position of the list takes a read-request port step, the others are unchanged *)
  Fixpoint RdRqPortStepL (l : list MemRegion) : TS (implRegionsTree core l) -> TS (implRegionsTree core l) -> Prop :=
    match l as l0 return TS (implRegionsTree core l0) -> TS (implRegionsTree core l0) -> Prop with
    | [] => fun _ _ => False
    | r :: rs => fun mi mi' =>
        (RegionRdRqStep r mi.(Fst) mi'.(Fst) /\ mi'.(Snd) = mi.(Snd)) \/
        (mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\ RdRqPortStepL rs mi.(Snd).(Fst) mi'.(Snd).(Fst))
    end.

  Lemma rdRqPorts_step :
    forall l (aI : forall ty, Action ty (implRegionsTree core l) (Bit 0)) env mi mi' v,
      In aI (implCollectLineReadRqPorts core l) ->
      SemAction env (aI type) mi mi' v -> RdRqPortStepL l mi mi'.
  Proof.
    induction l as [| r rs IH]; intros aI env mi mi' v Hin Hsem; [destruct Hin |].
    unfold implCollectLineReadRqPorts, implCollectRegionActions in Hin; cbn [genCollectRegionActions] in Hin.
    apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as [f [<- Hf]].
    - left; apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
      split; [| reflexivity]; cbn [writeSubTreeState readSubTreeState] in Hy' |- *.
      revert f Hf Hy'; destruct r as [nm bs sz kd sn im ba sa]; destruct kd;
        cbn [implMemRegionLineReadRqPorts regionKind In RegionRdRqStep]; intros f Hf Hy'; try contradiction.
      destruct Hf as [<- | []]; exact (rdRqPort_cases _ _ _ _ _ Hy').
    - right; apply SemAction_liftAction_iff in Hsem as [z' [Hz' ->]].
      split; [reflexivity | split; [reflexivity |]].
      exact (IH f _ _ _ _ Hf Hz').
  Qed.
  (* A request-port step leaves the port predicates that ignore the data requests and `portRq` *)
  Lemma RqInsensitive_rdRqSent :
    forall P, RqInsensitive core P -> forall r (y : ExtI r) L rdy, P r (rdRqSent r y L rdy) = P r y.
  Proof. intros P HP r y L rdy; apply HP; destruct rdy; reflexivity. Qed.

  Lemma AllPorts_rdRqStep :
    forall P, RqInsensitive core P ->
      forall l mi mi', RdRqPortStepL l mi mi' -> AllPorts core P l mi' = AllPorts core P l mi.
  Proof.
    intros P HP; induction l as [| r rs IH]; intros mi mi' Hst; [destruct Hst |].
    cbn [RdRqPortStepL] in Hst; cbn [AllPorts].
    destruct Hst as [[Hr Hs] | [Hf [Hs Hl]]].
    - rewrite Hs; f_equal.
      revert Hr; generalize (mi.(Fst)) (mi'.(Fst)).
      unfold RegionPort, RegionRdRqStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hr; [| contradiction].
      destruct Hr as [[_ ->] | [_ [rdy ->]]]; [reflexivity | apply (RqInsensitive_rdRqSent P HP)].
    - rewrite Hf, (IH _ _ Hl); reflexivity.
  Qed.
  (* Device (CustomMem) positions are untouched by a request-port step *)
  Lemma regionStateAt_rdRqStep :
    forall l j r0 (pf : nth_error l j = Some r0) (mi mi' : TS (implRegionsTree core l)),
      RdRqPortStepL l mi mi' -> isCustomR r0 ->
      regionStateAt (implMemRegionTree core) j l r0 pf mi' = regionStateAt (implMemRegionTree core) j l r0 pf mi.
  Proof.
    induction l as [| r rs IH]; intros [| j'] r0 pf mi mi' H Hc; try discriminate pf;
      cbn [RdRqPortStepL] in H.
    - cbn [regionStateAt].
      set (Heq := match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end
                  with eq_refl => eq_refl end).
      clearbody Heq; clear pf; destruct Heq.
      cbv beta iota.
      destruct H as [[Hs _] | [Hf _]]; [| rewrite Hf; reflexivity].
      exfalso; revert Hs; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionRdRqStep, isCustomR, implMemRegionTree in *.
      destruct (regionKind r0); [contradiction | intros y' y Hy; exact Hy].
    - cbn [regionStateAt].
      destruct H as [[_ Hs] | [_ [_ Hrest]]].
      + rewrite Hs; reflexivity.
      + exact (IH j' r0 pf _ _ Hrest Hc).
  Qed.

  (* No port holds a Read: nothing changes *)
  Lemma portRqIsRead_invalid :
    forall r (y : ExtI r), optValid (extPortRq core r y) = false -> portRqIsRead r y = false.
  Proof. intros r y H; unfold portRqIsRead; unfold extPortRq, optValid in H; rewrite H; reflexivity. Qed.

  Lemma portRqIsRead_write :
    forall r (y : ExtI r) w, extPortRq core r y = someWrite w -> portRqIsRead r y = false.
  Proof. intros r y w H; unfold portRqIsRead; unfold extPortRq in H; rewrite H; reflexivity. Qed.

  Lemma rdRqStep_noRead :
    forall l mi mi', AllPorts core (fun r y => portRqIsRead r y = false) l mi -> RdRqPortStepL l mi mi' -> mi' = mi.
  Proof.
    induction l as [| r rs IH]; intros mi mi' Hn Hst; [destruct Hst |].
    cbn [AllPorts] in Hn; destruct Hn as [Hn0 Hn1]; cbn [RdRqPortStepL] in Hst.
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - apply prod_ext; [| exact Ht].
      revert Hn0 Hs; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, RegionRdRqStep, implMemRegionTree.
      destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hn Hs; [| contradiction].
      destruct Hs as [[_ ->] | [Hb _]]; [reflexivity | rewrite Hn in Hb; discriminate].
    - apply prod_ext; [exact Hf |]; apply prod_ext; [exact (IH _ _ Hn1 Hrest) | exact Ht].
  Qed.

  (* The port predicates of a read of line `L` staged (`PortsReadStaged`) or accepted (`PortsReadOut`) *)
  Definition stagedP (L : type Addr) : forall r, ExtI r -> Prop :=
    fun r y => extDataQuiet core r y /\
               (if isRegionAddrB r L then extPortRq core r y = someRead L else optValid (extPortRq core r y) = false).
  Definition outP (L : type Addr) : forall r, ExtI r -> Prop :=
    fun r y => optValid (extPortRq core r y) = false /\
               (if isRegionAddrB r L then extDataOut core r y else extDataQuiet core r y).

  Lemma lineKind_none_unique : forall rs L, lineKind rs L = None -> lineUnique rs L.
  Proof.
    induction rs as [| r rs IH]; intros L Hk; [exact I |].
    cbn [lineKind] in Hk; cbn [lineUnique]; destruct (isRegionAddrB r L); [discriminate | exact (IH L Hk)].
  Qed.

  Lemma stagedP_outP_none :
    forall rs L z, lineKind rs L = None -> AllPorts core (stagedP L) rs z -> AllPorts core (outP L) rs z.
  Proof.
    induction rs as [| r rs IH]; intros L z Hk H; [exact I |].
    cbn [lineKind] in Hk; destruct (isRegionAddrB r L) eqn:Hm; [discriminate |].
    cbn [AllPorts] in H |- *; destruct H as [H0 H1]; split; [| exact (IH _ _ Hk H1)].
    revert H0 Hm; generalize (z.(Fst)); unfold RegionPort, stagedP, outP, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; [| intros; exact I].
    intros y [Hq Hp] Hm; rewrite Hm in Hp |- *; exact (conj Hp Hq).
  Qed.

  (* A step with no read staged in the stepping region changes nothing there *)
  Lemma regionRdRqStep_noRead :
    forall r (y y' : TS (implMemRegionTree core r)),
      RegionPort core (fun r y => portRqIsRead r y = false) r y -> RegionRdRqStep r y y' -> y' = y.
  Proof.
    intros r y y'; unfold RegionPort, RegionRdRqStep, implMemRegionTree.
    revert y y'; destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' Hn Hs;
      [| contradiction].
    destruct Hs as [[_ ->] | [Hb _]]; [reflexivity | rewrite Hn in Hb; discriminate].
  Qed.

  Lemma regionStaged_out_other :
    forall r L (y : TS (implMemRegionTree core r)), isRegionAddrB r L = false ->
      RegionPort core (stagedP L) r y -> RegionPort core (outP L) r y /\ RegionPort core (fun r y => portRqIsRead r y = false) r y.
  Proof.
    intros r L y Hm; revert y Hm; unfold RegionPort, stagedP, outP, implMemRegionTree.
    destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; [| intros; exact (conj I I)].
    intros y Hm [Hq Hp]; rewrite Hm in Hp |- *; exact (conj (conj Hp Hq) (portRqIsRead_invalid _ _ Hp)).
  Qed.

  Lemma stagedP_noRead_none :
    forall rs L z, lineKind rs L = None -> AllPorts core (stagedP L) rs z -> AllPorts core (fun r y => portRqIsRead r y = false) rs z.
  Proof.
    induction rs as [| r rs IH]; intros L z Hk H; [exact I |].
    cbn [lineKind] in Hk; destruct (isRegionAddrB r L) eqn:Hm; [discriminate |].
    cbn [AllPorts] in H |- *; destruct H as [H0 H1].
    exact (conj (proj2 (regionStaged_out_other r L _ Hm H0)) (IH _ _ Hk H1)).
  Qed.

  (* A read of line `L` staged in the one region containing `L`: the step changes nothing, keeps
   * it staged (not accepted), or moves it out (accepted) *)
  Lemma rdRqStep_staged :
    forall l L mi mi', lineUnique l L -> AllPorts core (stagedP L) l mi -> RdRqPortStepL l mi mi' ->
      mi' = mi \/ AllPorts core (stagedP L) l mi' \/ AllPorts core (outP L) l mi'.
  Proof.
    induction l as [| r rs IH]; intros L mi mi' Hu H Hst; [destruct Hst |].
    cbn [lineUnique] in Hu; cbn [AllPorts] in H |- *; destruct H as [H0 H1]; cbn [RdRqPortStepL] in Hst.
    destruct (isRegionAddrB r L) eqn:Hm.
    - destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
      + rewrite Ht.
        revert H0 Hs Hm; generalize (mi.(Fst)) (mi'.(Fst)); unfold RegionPort, RegionRdRqStep, stagedP, outP, implMemRegionTree.
        destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind]; intros y y' H0 Hs Hm; [| contradiction].
        rewrite Hm in H0 |- *; destruct H0 as [Hq Hp].
        destruct (extPortRq_someRead _ _ _ Hp) as [Hb Ha].
        destruct Hs as [[Hb' _] | [_ [rdy ->]]]; [rewrite Hb in Hb'; discriminate |].
        rewrite Ha; destruct rdy.
        * right; right; split; [| exact (stagedP_outP_none _ _ _ Hu H1)].
          split; [reflexivity |].
          unfold extDataOut, extDataQuiet in *; rewrite implDataAccRqs_rdRqSent, rdRqSent_rps; cbn [length]; rewrite Hq; reflexivity.
        * right; left; split; [| exact H1].
          split; [unfold extDataQuiet in *; rewrite implDataAccRqs_rdRqSent, rdRqSent_rps; exact Hq |].
          rewrite extPortRq_rdRqSent; exact Hp.
      + left; pose proof (rdRqStep_noRead _ _ _ (stagedP_noRead_none _ _ _ Hu H1) Hrest) as E.
        apply prod_ext; [exact Hf |]; apply prod_ext; [exact E | exact Ht].
    - destruct (regionStaged_out_other r L _ Hm H0) as [Ho Hn].
      destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
      + left; apply prod_ext; [exact (regionRdRqStep_noRead _ _ _ Hn Hs) | exact Ht].
      + rewrite Hf; destruct (IH L _ _ Hu H1 Hrest) as [E | [Hs' | Ho']].
        * left; apply prod_ext; [exact Hf |]; apply prod_ext; [exact E | exact Ht].
        * right; left; exact (conj H0 Hs').
        * right; right; exact (conj Ho Ho').
  Qed.

  Variables cp pp : nat.

  Lemma RegionRelAt_rdRqStep :
    forall i r x (y y' : TS (implMemRegionTree core r)),
      RegionRdRqStep r y y' -> RegionRelAt core cp pp i r x y -> RegionRelAt core cp pp i r x y'.
  Proof.
    intros i r x y y'; unfold RegionRelAt, RegionRdRqStep, implMemRegionTree, memRegionTree in *.
    revert x y y'; destruct r as [nm bs sz kd sn im ba sa]; destruct kd; cbn [regionKind];
      intros x y y' Hs Hr; [| contradiction].
    destruct Hs as [[_ ->] | [_ [rdy ->]]]; [exact Hr | exact (ExtRel_rdRqSent _ _ _ _ _ Hr)].
  Qed.

  Lemma MemRelPost_rdRqStep :
    forall l i ms mi mi', RdRqPortStepL l mi mi' -> MemRelPost core cp pp i l ms mi -> MemRelPost core cp pp i l ms mi'.
  Proof.
    induction l as [| r rs IH]; intros i ms mi mi' Hst H; [destruct Hst |].
    cbn [RdRqPortStepL] in Hst; cbn [MemRelPost] in H |- *; destruct H as [Hr Hl].
    destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
    - rewrite Ht; split; [exact (RegionRelAt_rdRqStep _ _ _ _ _ Hs Hr) | exact Hl].
    - rewrite Hf; split; [exact Hr | exact (IH _ _ _ _ Hrest Hl)].
  Qed.

  Lemma MemRelPre_rdRqStep :
    forall sRev iRev post l i ms mi mi', isCustomR iRev ->
      RdRqPortStepL (l ++ iRev :: post) mi mi' ->
      MemRelPre core cp pp i l sRev iRev post ms mi -> MemRelPre core cp pp i l sRev iRev post ms mi'.
  Proof.
    intros sRev iRev post; induction l as [| r rs IH]; intros i ms mi mi' Hc Hst H.
    - cbn [app RdRqPortStepL] in Hst; cbn [MemRelPre] in H |- *.
      destruct Hst as [[Hs _] | [_ [_ Hrest]]]; [| exact (MemRelPost_rdRqStep _ _ _ _ _ Hrest H)].
      exfalso; revert Hs; generalize (mi'.(Fst)) (mi.(Fst)); unfold RegionRdRqStep, isCustomR, implMemRegionTree in *.
      destruct (regionKind iRev); [contradiction | intros y' y Hy; exact Hy].
    - cbn [app RdRqPortStepL] in Hst; cbn [MemRelPre] in H |- *; destruct H as [Hr Hl].
      destruct Hst as [[Hs Ht] | [Hf [Ht Hrest]]].
      + rewrite Ht; split; [exact (RegionRelAt_rdRqStep _ _ _ _ _ Hs Hr) | exact Hl].
      + rewrite Hf; split; [exact Hr | exact (IH _ _ _ _ Hc Hrest Hl)].
  Qed.
End RdRqPortRegion.

(* --- 2. The Read-Request Ports Refine the Spec (it stutters) --- *)

(* A staged read accepted by its region moves from RdStaged to RdOut *)
Definition rdOutStage (st : RdStage) : RdStage :=
  match st with RdStaged b => RdOut b | _ => st end.

Definition rdOutAcc (a : Access) : Access :=
  match a with
  | AccLoad ld pkt0 st => AccLoad ld pkt0 (rdOutStage st)
  | AccDmRev rc st => AccDmRev rc (rdOutStage st)
  | AccRevCap st => AccRevCap (rdOutStage st)
  | AccRevBit st => AccRevBit (rdOutStage st)
  | _ => a
  end.

Lemma accTakesHead_rdOut : forall a, accTakesHead (rdOutAcc a) = accTakesHead a.
Proof. intros [| | ld pkt0 [[|]|[|]|[|]|[|] rp|res] | | | |]; reflexivity. Qed.

(* Disjoint spec regions make each line unique in the impl regions (same addresses) *)
Lemma lineUnique_implRegions :
  forall core pre post revBase revPfB revPfA L,
    pairwiseDisjoint (specRegionsOf core pre post revBase revPfB revPfA) = true ->
    lineUnique (implRegionsOf core pre post revBase revPfB revPfA) L.
Proof.
  intros core pre post revBase revPfB revPfA L Hd.
  pose proof (lineUnique_disjoint _ L Hd) as H; clear Hd; revert H; unfold specRegionsOf, implRegionsOf.
  induction pre as [| r rs IH]; cbn [app lineUnique]; [exact (fun H => H) |].
  assert (E : lineKind (rs ++ specRevRegion core revBase revPfB revPfA :: post) L =
              lineKind (rs ++ implRevRegion core revBase revPfB revPfA :: post) L).
  { clear IH; induction rs as [| r' rs' IH']; cbn [app lineKind]; [reflexivity | rewrite IH'; reflexivity]. }
  rewrite E; destruct (isRegionAddrB r L); [exact (fun H => H) | exact IH].
Qed.

Section ReadRqPorts.
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

  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation SState := (SpecState core pcAddrInit specRegions).
  Local Abbreviation NPMI := (Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions).
  Local Abbreviation NPMS := (Spec.np_mem core pcAddrInit specRegions).
  Local Abbreviation revI := (revImplOf core pre post revBase revPfB revPfA).

  Local Abbreviation iMemA := (iMem core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRegionsA := (iRegions core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iMemStA := (iMemSt core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRequesterA := (iRequester core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRevA := (iRev core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iRevPhaseA := (iRevPhase core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation sMemA := (sMem core pcAddrInit pre post revBase revPfB revPfA).
  Local Abbreviation revOfRA := (revOfR core pre post revBase revPfB revPfA).
  Local Abbreviation setRevRA := (setRevR core pre post revBase revPfB revPfA).

  Local Abbreviation ACC := (AccessRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                               initLine).
  Local Abbreviation MEMC := (MemRelC core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                clintS clint plicS plic fwcs).
  Local Abbreviation PWS := (PortsWriteStaged core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation STEPOK := (StepOK core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).

  Local Abbreviation RELG := (RefRelG core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                clintS clint plicS plic initLine fwcs).

  Lemma iRegions_write : forall (s1 : IState) mi', iRegionsA (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd))) = mi'.
  Proof. reflexivity. Qed.

  (* The memory relation only sees ExternalMem regions through ExtRel and the devices directly *)
  Lemma MemRelC_rdRqStep :
    forall g (s1 : IState) (s2 : SState) mi',
      RdRqPortStepL core implRegions (iRegionsA s1) mi' ->
      MEMC g s1 s2 -> MEMC g (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd))) s2.
  Proof.
    intros g s1 s2 mi' Hst Hm.
    unfold MemRelC, MemRel, DevInv in *; rewrite iRegions_write.
    destruct Hm as [[Hpre [Hcl [Hpl Hrv]]] [[Hci Hpi] Hsnap]].
    assert (Ec : implClintState core pre post revBase revPfB revPfA clint mi' =
                 implClintState core pre post revBase revPfB revPfA clint (iRegionsA s1)).
    { unfold implClintState; rewrite (regionStateAt_rdRqStep core _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    assert (Ep : implPlicState core pre post revBase revPfB revPfA plic mi' =
                 implPlicState core pre post revBase revPfB revPfA plic (iRegionsA s1)).
    { unfold implPlicState; rewrite (regionStateAt_rdRqStep core _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    assert (Er : implRevState core pre post revBase revPfB revPfA mi' =
                 implRevState core pre post revBase revPfB revPfA (iRegionsA s1)).
    { unfold implRevState; rewrite (regionStateAt_rdRqStep core _ _ _ _ _ _ Hst); [reflexivity | exact I]. }
    rewrite Ec, Ep, Er.
    refine (conj (conj _ (conj Hcl (conj Hpl Hrv))) (conj (conj Hci Hpi) Hsnap)).
    eapply MemRelPre_rdRqStep; [exact I | exact Hst | exact Hpre].
  Qed.

  Local Abbreviation REVK := (RevokerRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                                initLine).
  Local Abbreviation RDS := (RdStageRel core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation PQ := (PortsQuiet core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                              mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation PRO := (PortsReadOut core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                               mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA).
  Local Abbreviation iScanAddrA := (iScanAddr core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                      mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB
                                      revPfA).
  Local Abbreviation iRevScanBaseA := (iRevScanBase core pcAddrInit fetchCapacity instCapacity decodeCapacity
                                         dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config pre
                                         post revBase revPfB revPfA).

  (* The impl state after the region ports took a step *)
  Local Abbreviation UPD s1 mi' := (writeSubTreeState NPMI s1 (mi' ,, (iMemA s1).(Snd))).

  (* The ghost after the region accepted the staged read *)
  Definition gRdOut (g : Ghost core pcAddrInit) : Ghost core pcAddrInit :=
    mkGhost core pcAddrInit (g_chain core pcAddrInit g) (g_rf0 core pcAddrInit g) (g_cnwb core pcAddrInit g)
            (g_revOff core pcAddrInit g) (g_d2aFo core pcAddrInit g) (rdOutAcc (g_acc core pcAddrInit g)).

  (* The regions are pairwise disjoint, so each line is in at most one region *)
  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).

  Lemma rdRq_lineUnique : forall L, lineUnique implRegions L.
  Proof. intros L; apply lineUnique_implRegions, Is_true_eq_true; exact Hdisj. Qed.

  (* No port holds a Read while the ports are quiet, a read is out or a write is staged *)
  Lemma rdRq_quietNoRead : forall (s1 : IState), PQ s1 ->
    AllPorts core (fun r y => portRqIsRead core r y = false) implRegions (iRegionsA s1).
  Proof.
    intros s1 H; unfold PortsQuiet in H; revert H; apply AllPorts_impl.
    intros r y [Hv _]; exact (portRqIsRead_invalid core r y Hv).
  Qed.

  Lemma rdRq_outNoRead : forall L (s1 : IState), PRO L s1 ->
    AllPorts core (fun r y => portRqIsRead core r y = false) implRegions (iRegionsA s1).
  Proof.
    intros L s1 H; unfold PortsReadOut in H; revert H; apply AllPorts_impl.
    intros r y [Hv _]; exact (portRqIsRead_invalid core r y Hv).
  Qed.

  Lemma rdRq_wstagedNoRead : forall L rq (s1 : IState), PWS L rq s1 ->
    AllPorts core (fun r y => portRqIsRead core r y = false) implRegions (iRegionsA s1).
  Proof.
    intros L rq s1 H; unfold PortsWriteStaged in H; revert H; apply AllPorts_impl.
    intros r y [_ Hp]; destruct (isRegionAddrB r L).
    - exact (portRqIsRead_write core r y rq Hp).
    - exact (portRqIsRead_invalid core r y Hp).
  Qed.

  Lemma rdRq_updSame : forall (s1 : IState), UPD s1 (iRegionsA s1) = s1.
  Proof.
    intros s1; first [reflexivity |
      transitivity (writeSubTreeState NPMI s1 (readSubTreeState NPMI s1)); [| apply writeSubTreeState_readSubTreeState];
      f_equal; apply prod_ext; reflexivity].
  Qed.

  (* The revoker is a device: the port step leaves it *)
  Lemma rdRq_iRevUpd : forall (s1 : IState) mi', RdRqPortStepL core implRegions (iRegionsA s1) mi' ->
    iRevA (UPD s1 mi') = iRevA s1.
  Proof.
    intros s1 mi' Hst.
    change (implRevState core pre post revBase revPfB revPfA mi' =
            implRevState core pre post revBase revPfB revPfA (iRegionsA s1)).
    unfold implRevState; rewrite (regionStateAt_rdRqStep core _ _ _ _ _ _ Hst); [reflexivity | exact I].
  Qed.

  (* A line read in progress: nothing changes, it stays staged, or the region accepts it *)
  Lemma RdStageRel_rdRq :
    forall addr size pkt0 st (s1 : IState) mi',
      RdRqPortStepL core implRegions (iRegionsA s1) mi' -> RDS addr size pkt0 st s1 ->
      mi' = iRegionsA s1 \/ RDS addr size pkt0 st (UPD s1 mi') \/
      (exists b, st = RdStaged b /\ RDS addr size pkt0 (RdOut b) (UPD s1 mi')).
  Proof.
    intros addr size pkt0 st s1 mi' Hst H.
    destruct st as [b | b | b | b rp | res].
    - left; destruct H as [_ [_ [_ Hq]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_quietNoRead s1 Hq) Hst).
    - destruct H as [Hs [Hr [Hk Hp]]].
      destruct (rdRqStep_staged core implRegions (lineOf b addr) (iRegionsA s1) mi' (rdRq_lineUnique _) Hp Hst)
        as [E | [Hp' | Hp']].
      + left; exact E.
      + right; left; exact (conj Hs (conj Hr (conj Hk Hp'))).
      + right; right; exists b; split; [reflexivity | exact (conj Hs (conj Hr (conj Hk Hp')))].
    - left; destruct H as [_ [_ [_ Hp]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_outNoRead _ s1 Hp) Hst).
    - left; destruct H as [_ [_ Hq]]; exact (rdRqStep_noRead core _ _ _ (rdRq_quietNoRead s1 Hq) Hst).
    - left; destruct H as [_ [_ [_ Hq]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_quietNoRead s1 Hq) Hst).
  Qed.

  (* The access in flight after the port step: only a staged read can move (to RdOut) *)
  Lemma AccessRel_rdRq :
    forall g (s1 : IState) (s2 : SState) mi',
      RdRqPortStepL core implRegions (iRegionsA s1) mi' -> ACC g s1 s2 ->
      mi' = iRegionsA s1 \/ ACC g (UPD s1 mi') s2 \/ ACC (gRdOut g) (UPD s1 mi') s2.
  Proof.
    intros g s1 s2 mi' Hst Ha.
    pose proof (rdRq_iRevUpd s1 mi' Hst) as HR.
    assert (EP : iRevPhaseA (UPD s1 mi') = iRevPhaseA s1) by (unfold iRevPhase; rewrite HR; reflexivity).
    assert (ES : iScanAddrA (UPD s1 mi') = iScanAddrA s1) by (unfold iScanAddr; rewrite HR; reflexivity).
    assert (EB : iRevScanBaseA (UPD s1 mi') = iRevScanBaseA s1) by (unfold iRevScanBase; rewrite HR; reflexivity).
    unfold AccessRel, HeadReq, gRdOut in *; cbn [g_acc g_revOff g_cnwb g_chain].
    unfold revNotReading, dmNotAccessing in *.
    destruct (g_acc core pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | st | st | addr pkt st];
      cbn [rdOutAcc]; rewrite ?EP, ?ES, ?EB.
    - left; destruct Ha as [_ [_ [Hq _]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_quietNoRead s1 Hq) Hst).
    - left; destruct Ha as [Hw _]; unfold WrStageRel in Hw; destruct st as [b | b].
      + destruct Hw as [_ [_ [_ Hq]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_quietNoRead s1 Hq) Hst).
      + destruct Hw as [_ [_ [_ Hq]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_wstagedNoRead _ _ s1 Hq) Hst).
    - destruct Ha as [Hrd Hrest].
      destruct (RdStageRel_rdRq _ _ _ _ s1 mi' Hst Hrd) as [E | [Hrd' | [b [-> Hrd']]]].
      + left; exact E.
      + right; left; exact (conj Hrd' Hrest).
      + right; right; cbn [rdOutStage]; destruct b; exact (conj Hrd' Hrest).
    - destruct Ha as [Hrd Hrest].
      destruct (RdStageRel_rdRq _ _ _ _ s1 mi' Hst Hrd) as [E | [Hrd' | [b [-> Hrd']]]].
      + left; exact E.
      + right; left; exact (conj Hrd' Hrest).
      + right; right; cbn [rdOutStage]; exact (conj Hrd' Hrest).
    - destruct Ha as [Hrd Hrest].
      destruct (RdStageRel_rdRq _ _ _ _ s1 mi' Hst Hrd) as [E | [Hrd' | [b [-> Hrd']]]].
      + left; exact E.
      + right; left; exact (conj Hrd' Hrest).
      + right; right; cbn [rdOutStage]; exact (conj Hrd' Hrest).
    - destruct Ha as [Hrd Hrest].
      destruct (RdStageRel_rdRq _ _ _ _ s1 mi' Hst Hrd) as [E | [Hrd' | [b [-> Hrd']]]].
      + left; exact E.
      + right; left; exact (conj Hrd' Hrest).
      + right; right; cbn [rdOutStage]; exact (conj Hrd' Hrest).
    - left; destruct Ha as [Hw _]; unfold WrStageRel in Hw; destruct st as [b | b].
      + destruct Hw as [_ [_ [_ Hq]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_quietNoRead s1 Hq) Hst).
      + destruct Hw as [_ [_ [_ Hq]]]; exact (rdRqStep_noRead core _ _ _ (rdRq_wstagedNoRead _ _ s1 Hq) Hst).
  Qed.

  (* The revoker facts hold for the moved access: its read values are not yet known *)
  Lemma RevokerRel_rdOut :
    forall g (s1 s1' : IState) (s2 : SState),
      iRevA s1' = iRevA s1 -> REVK g s1 s2 -> REVK (gRdOut g) s1' s2.
  Proof.
    intros g s1 s1' s2 HR H.
    unfold RevokerRel, RevAccRel, RevCapOK, RevWriteOK, gRdOut in *; cbn [g_acc g_revOff].
    unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *.
    rewrite HR; revert H.
    destruct (g_acc core pcAddrInit g) as [| addr size pkt st | ld pkt0 st | rc st | [b|b|b|b rp|res]
                                          | [b|b|b|b rp|res] | addr pkt st];
      cbn [rdOutAcc rdOutStage]; intros H; exact H.
  Qed.

  (* The data read-request ports: the spec stutters; a staged read the region accepts is out *)
  Theorem stepOK_readRqPorts :
    forall act,
      In act (@readRqPorts core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config implRegions type) ->
      STEPOK act.
  Proof.
    intros act Hin s1 s1' s2 Hsem [g Hg].
    unfold readRqPorts, implMemCollectLineReadRqPorts in Hin.
    rewrite map_map in Hin; apply in_map_iff in Hin as [f [<- Hf]]; cbv beta in Hsem.
    apply SemAction_liftAction_iff in Hsem as [m' [Hm' E1]].
    apply SemAction_liftAction_iff in Hm' as [mi' [Hmi' Em]].
    pose proof (rdRqPorts_step core implRegions f _ _ _ _ Hf Hmi') as Hst.
    change (RdRqPortStepL core implRegions (iRegionsA s1) mi') in Hst.
    assert (Es1 : s1' = UPD s1 mi') by (rewrite E1, Em; reflexivity).
    exists s2; split; [apply NilAction; reflexivity |].
    pose proof Hg as Hg0; destruct Hg0 as [Hrf Hm Hl Hrp He Ha Hc Hd Hfe Hs Hfr Hw Hrk].
    pose proof (rdRq_iRevUpd s1 mi' Hst) as HR.
    assert (HP : forall P, RqInsensitive core P ->
                   AllPorts core P implRegions (iRegionsA s1') = AllPorts core P implRegions (iRegionsA s1)).
    { intros P HPi; rewrite Es1, iRegions_write; exact (AllPorts_rdRqStep core P HPi _ _ _ Hst). }
    assert (Hmem : forall g', g_revOff core pcAddrInit g' = g_revOff core pcAddrInit g -> MEMC g' s1' s2).
    { intros g' Eo; rewrite Es1; unfold MemRelC; rewrite Eo; exact (MemRelC_rdRqStep g s1 s2 mi' Hst Hm). }
    destruct (AccessRel_rdRq g s1 s2 mi' Hst Ha) as [E | [Ha' | Ha']].
    - exists g; rewrite Es1, E, rdRq_updSame; exact Hg.
    - exists g.
      eapply (RefRelG_rq_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact Es1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | exact (Hmem g eq_refl) | exact Hl
        | rewrite Es1; exact Ha' | | exact Hg].
      rewrite Es1.
      eapply RevokerRel_frame with (g := g) (s1 := s1) (s2 := s2);
        [reflexivity | reflexivity | exact HR | intros L; reflexivity | exact Hrk].
    - exists (gRdOut g).
      eapply (RefRelG_rq_frame core pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode config pre post revBase revPfB revPfA
                clintS clint plicS plic initLine fwcs) with (g := g) (s1 := s1) (s2 := s2) (ms' := sMemA s2);
        [exact Es1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact (accTakesHead_rdOut _) | exact HP
        | intros L; reflexivity | apply FetchViewExt_refl | exact (Hmem (gRdOut g) eq_refl) | exact Hl
        | rewrite Es1; exact Ha' | rewrite Es1; exact (RevokerRel_rdOut g s1 _ s2 HR Hrk) | exact Hg].
  Qed.
End ReadRqPorts.
