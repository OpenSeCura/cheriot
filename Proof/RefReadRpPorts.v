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
From Cheriot.Proof Require Import ImplSpec RefFetch RefMemStep RefFetchRp.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4: the data response ports (`readRpPorts`: `implMemLineRpPort` around
 * `implExternalLineRpPort`, one per ExternalMem region).
 * 1. One port step (`dataRpPort_cases`): a `false` valid (no response), or a response taken (the
 *    env makes it the line content of the oldest unanswered accepted read, `implDataLineAddr`, as
 *    the accepted writes left it). Over the region list one ExternalMem position steps
 *    (`dataRpPorts_step`). *)

(* --- 1. One Data Response Port Step --- *)

Section DataRpPortRegion.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation ExtI r := (TS (implExternalMemRegionTree r)).

  (* The data responses the region received *)
  Definition dataRcv r (y : ExtI r) : list (type LineReadRp) := y.(Fst).(Snd).(Snd).(Fst).

  (* The region after its data port saw no response *)
  Definition dataRpNone r (y : ExtI r) : ExtI r :=
    (y.(Fst) ,, (y.(Snd).(Fst) ,, (y.(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Fst) ,,
      ((false :: y.(Snd).(Snd).(Snd).(Snd).(Fst)) ,, y.(Snd).(Snd).(Snd).(Snd).(Snd)))))).

  (* The region after its data port took the response `rp` (`z`: the value sent on
   * lineReadRpReady) *)
  Definition dataRpTaken r (y : ExtI r) (rp : type LineReadRp) (z : type (Bit 0)) : ExtI r :=
    ((y.(Fst).(Fst) ,, (y.(Fst).(Snd).(Fst) ,, ((rp :: y.(Fst).(Snd).(Snd).(Fst)) ,, y.(Fst).(Snd).(Snd).(Snd)))) ,,
     (y.(Snd).(Fst) ,, (y.(Snd).(Snd).(Fst) ,, (y.(Snd).(Snd).(Snd).(Fst) ,,
       ((true :: y.(Snd).(Snd).(Snd).(Snd).(Fst)) ,,
        ((z :: y.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)) ,, y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))).

  Local Opaque liftAction.

  Lemma dataRpPort_cases :
    forall r fwc (eR : Env (implExternalMemRegionTree r)) (y y' : ExtI r) o,
      (forall s x w, eR s x w -> implExtRegionEnv initLine r fwc s x w) ->
      SemAction eR (@implExternalLineRpPort r type) y y' o ->
      (optValid o = false /\ y' = dataRpNone r y) \/
      ((length (dataRcv r y) < length (implDataAccRqs r y))%nat /\
       exists rp z, rp = evalLineWriteRqTrace (initLine r) (implAccWrites r y) (implDataLineAddr r y) /\
                    o = (rp ,, (true ,, tt)) /\ y' = dataRpTaken r y rp z).
  Proof.
    intros r fwc eR
           [[[f_rq [f_rp [f_wait [f_fiRq [f_fiAck []]]]]]
             [d_rq [d_rp [d_wr []]]]]
            [[if_rqRdy [if_rpVal [if_rpRdy [[if_rdRpData [if_rdRpVal []]] []]]]]
             [id_rqRdy [id_wrRdy [id_rpVal [id_rpRdy [id_portRq []]]]]]]]
           y' o HE Hsem.
    unfold implExternalLineRpPort, externalLineReadRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn in Hsem.
    destruct Hsem as [valid [Hvenv Hbr]].
    destruct valid; cbn in Hbr.
    - rewrite !evalActionPropGen_liftAction in Hbr; cbn in Hbr.
      destruct Hbr as [rp [Hrpenv Hrest]].
      cbn in Hrest; destruct Hrest as [<- <-].
      right; split.
      + unfold subEnv, cast_recv_inv in Hvenv; apply HE in Hvenv.
        unfold implExtRegionEnv, extRegionEnvCtx in Hvenv.
        cbn -[eq_rect EnvDataLineReadRpValidConstraint] in Hvenv.
        rewrite ?eq_rect_Kind_refl in Hvenv.
        exact (Hvenv eq_refl).
      + eexists rp, _; split; [| split; reflexivity].
        unfold subEnv, cast_recv_inv in Hrpenv; apply HE in Hrpenv.
        unfold implExtRegionEnv, extRegionEnvCtx in Hrpenv.
        cbn -[eq_rect evalLineWriteRqTrace implAccWrites implDataLineAddr] in Hrpenv.
        rewrite ?eq_rect_Kind_refl in Hrpenv.
        exact Hrpenv.
    - destruct Hbr as [<- <-].
      left; split; reflexivity.
  Qed.

  (* One region's data response port step, with the port's output *)
  Definition RegionDataRpStep (fwc : nat -> nat) (r : MemRegion)
    : TS (implMemRegionTree r) -> TS (implMemRegionTree r) -> type (Option LineReadRp) -> Prop :=
    match r.(regionKind) as k
          return TS (implMemRegionKindTree r k) -> TS (implMemRegionKindTree r k) -> type (Option LineReadRp) -> Prop with
    | ExternalMem => fun y y' o =>
        (optValid o = false /\ y' = dataRpNone r y) \/
        ((length (dataRcv r y) < length (implDataAccRqs r y))%nat /\
         exists rp z, rp = evalLineWriteRqTrace (initLine r) (implAccWrites r y) (implDataLineAddr r y) /\
                      o = (rp ,, (true ,, tt)) /\ y' = dataRpTaken r y rp z)
    | CustomMem _ _ _ _ => fun _ _ _ => False
    end.

  (* One position of the list takes a data response port step, the others are unchanged *)
  Fixpoint DataRpPortStepL (fwcs : nat -> nat -> nat) (l : list MemRegion)
    : TS (implRegionsTree l) -> TS (implRegionsTree l) -> type (Option LineReadRp) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> TS (implRegionsTree l0) -> type (Option LineReadRp) -> Prop with
    | [] => fun _ _ _ => False
    | r :: rs => fun mi mi' o =>
        (RegionDataRpStep (fwcs 0%nat) r mi.(Fst) mi'.(Fst) o /\ mi'.(Snd) = mi.(Snd)) \/
        (mi'.(Fst) = mi.(Fst) /\ mi'.(Snd).(Snd) = mi.(Snd).(Snd) /\
         DataRpPortStepL (fun i => fwcs (S i)) rs mi.(Snd).(Fst) mi'.(Snd).(Fst) o)
    end.

  Lemma dataRpPorts_step :
    forall l fwcs (aI : forall ty, Action ty (implRegionsTree l) (Option LineReadRp)) env mi mi' o,
      ImplEnvOK initLine l fwcs env ->
      In aI (implCollectLineRpPorts l) ->
      SemAction env (aI type) mi mi' o -> DataRpPortStepL fwcs l mi mi' o.
  Proof.
    induction l as [| r rs IH]; intros fwcs aI env mi mi' o HE Hin Hsem; [destruct Hin |].
    unfold implCollectLineRpPorts, implCollectRegionActions in Hin; cbn [genCollectRegionActions] in Hin.
    apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as [f [<- Hf]].
    - left; apply SemAction_liftAction_iff in Hsem as [y' [Hy' ->]].
      split; [| reflexivity]; cbn [writeSubTreeState readSubTreeState] in Hy' |- *.
      pose proof (ImplEnvOK_head initLine r rs fwcs env mi HE) as HE0.
      revert f Hf Hy' HE0; destruct r as [nm bs sz kd sn im ba sa]; destruct kd;
        cbn [implMemRegionLineRpPorts regionKind In RegionDataRpStep implRegionEnv];
        intros f Hf Hy' HE0; try contradiction.
      destruct Hf as [<- | []].
      exact (dataRpPort_cases _ _ _ _ _ _ HE0 Hy').
    - right; apply SemAction_liftAction_iff in Hsem as [z' [Hz' ->]].
      split; [reflexivity | split; [reflexivity |]].
      exact (IH _ f _ _ _ _ (ImplEnvOK_tail initLine r rs fwcs env mi HE) Hf Hz').
  Qed.
End DataRpPortRegion.

(* --- 2. The Port on the Memory Subtree --- *)

Section MemLineRpPort.
  Variable regions : list MemRegion.

  Ltac mem_cbn H := cbn -[evalExpr evalLetExpr toAction liftAction] in H.

  (* `implMemLineRpPort port`: with `readRp` full nothing changes; otherwise the port runs on the
   * regions and a valid output fills `readRp` *)
  Lemma memLineRpPort_char :
    forall (port : Action type (implRegionsTree regions) (Option LineReadRp)) env mr mst mrq mrp m' v,
      SemAction env (@implMemLineRpPort regions type port) (mr ,, (mst ,, (mrq ,, (mrp ,, tt)))) m' v ->
      (optValid mrp = true /\ m' = (mr ,, (mst ,, (mrq ,, (mrp ,, tt))))) \/
      (optValid mrp = false /\ exists mr' o,
         SemAction (subEnv child0Path env (mr ,, (mst ,, (mrq ,, (mrp ,, tt))))) port mr mr' o /\
         m' = (mr' ,, (mst ,, (mrq ,, ((if optValid o then o else mrp) ,, tt))))).
  Proof.
    intros port env mr mst mrq mrp m' v H.
    rewrite SemAction_iff_evalActionPropGen in H.
    unfold implMemLineRpPort in H; cbn [evalActionPropGen] in H.
    mem_cbn H.
    match type of H with context [if ?cd then _ else _] =>
      replace cd with (negb (optValid mrp)) in H by reflexivity
    end.
    destruct (optValid mrp) eqn:Ev; cbn [negb] in H.
    - left; split; [reflexivity |].
      mem_cbn H; destruct H as [H _]; symmetry; exact H.
    - right; split; [reflexivity |].
      rewrite evalActionPropGen_liftAction in H.
      apply evalActionPropGen_to_SemAction in H as [mr' [o [Hp Hpost]]].
      exists mr', o; split; [exact Hp |].
      mem_cbn Hpost.
      match type of Hpost with context [if ?cd then _ else _] =>
        replace cd with (optValid o) in Hpost by reflexivity
      end.
      destruct (optValid o) eqn:Eo; mem_cbn Hpost; destruct Hpost as [Hpost _]; symmetry; exact Hpost.
  Qed.
End MemLineRpPort.
