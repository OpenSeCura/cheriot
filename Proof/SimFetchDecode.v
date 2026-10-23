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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems ActionSim.
From Cheriot Require Export SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecMulDiv Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Export Impl ImplCommon ImplDevice ImplRevoker ImplFetch ImplDecode ImplExecute ImplDataMem ImplMulDiv ImplMulDivProof ImplBranchPredictor.
From Cheriot.Proof Require Export TreeLemmas StateRel SimDevices.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. `implFetchTree` AND `implDecodeTree` STATE ACCESSORS & ACTION LEMMAS
 * =========================================================================== *)

Section FetchDecodeTreeHelpers.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity : nat.

  Local Abbreviation fTree := (implFetchTree dom pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (implDecodeTree dom decodeCapacity).

  (* --- 1A. `implFetchTree` Updaters & Simplification Lemmas --- *)

  Definition fetch_withPc (sf : TreeState DomainElemState fTree) (v : type Addr)
    : TreeState DomainElemState fTree :=
    (v ,, sf.(Snd)).

  Definition fetch_withPredEpoch (sf : TreeState DomainElemState fTree) (v : type Epoch)
    : TreeState DomainElemState fTree :=
    (sf.(Fst) ,, (v ,, sf.(Snd).(Snd))).

  Definition fetch_withCurParcelOpt (sf : TreeState DomainElemState fTree)
    (v : type (Option (Bit LgFetchParcels)))
    : TreeState DomainElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (v ,, sf.(Snd).(Snd).(Snd)))).

  Definition fetch_withStraddleOpt (sf : TreeState DomainElemState fTree)
    (v : type (Option StraddleHalf))
    : TreeState DomainElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,, (v ,, sf.(Snd).(Snd).(Snd).(Snd))))).

  Definition fetch_withCanProceed (sf : TreeState DomainElemState fTree) (v : bool)
    : TreeState DomainElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Fst) ,, (v ,, sf.(Snd).(Snd).(Snd).(Snd).(Snd)))))).

  Definition fetch_withFetchBufFifo (sf : TreeState DomainElemState fTree)
    (v : TreeState DomainElemState (fifoTree dom fetchCapacity FetchBufEntry))
    : TreeState DomainElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Fst) ,, (sf.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd))))))).

  Definition fetch_withInstFifo (sf : TreeState DomainElemState fTree)
    (v : TreeState DomainElemState (fifoTree dom instCapacity AssembledInst))
    : TreeState DomainElemState fTree :=
    (sf.(Fst) ,, (sf.(Snd).(Fst) ,, (sf.(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Fst) ,, (sf.(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      (sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((v ,, sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       sf.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))))).

  Lemma evalActionPropGen_readFetchPc :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@readFetchPc dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_pc dom pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writeFetchPc :
    forall (val : type Addr) (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@writeFetchPc dom pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withPc sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readPredEpoch :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@readPredEpoch dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_predEpoch dom pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writePredEpoch :
    forall (val : type Epoch) (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@writePredEpoch dom pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withPredEpoch sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readCurParcelOpt :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@readCurParcelOpt dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_curParcelOpt dom pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writeCurParcelOpt :
    forall (val : type (Option (Bit LgFetchParcels))) (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@writeCurParcelOpt dom pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withCurParcelOpt sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readStraddleOpt :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@readStraddleOpt dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_straddleOpt dom pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_writeStraddleOpt :
    forall (val : type (Option StraddleHalf)) (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@writeStraddleOpt dom pcAddrInit fetchCapacity instCapacity type val) sf P <->
      P (fetch_withStraddleOpt sf val) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_clearStraddle :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@clearStraddle dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P (fetch_withStraddleOpt sf (getDefault (Option StraddleHalf))) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_readFetchCanProceed :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@readFetchCanProceed dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P sf (fetch_canProceed dom pcAddrInit fetchCapacity instCapacity sf).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_setFetchCanProceed :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@setFetchCanProceed dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P (fetch_withCanProceed sf true) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_clearFetchCanProceed :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@clearFetchCanProceed dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      P (fetch_withCanProceed sf false) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_fetchInstFirst :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@fetchInstFirst dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      evalActionPropGen (@first dom instCapacity AssembledInst type)
        (fetch_instFifo dom pcAddrInit fetchCapacity instCapacity sf)
        (fun f' res => P (fetch_withInstFifo sf f') res).
  Proof.
    intros sf P.
    unfold fetchInstFirst.
    rewrite (evalActionPropGen_liftAction (@np_fetchInstFifo dom pcAddrInit fetchCapacity instCapacity)).
    reflexivity.
  Qed.

  Lemma evalActionPropGen_fetchInstDeq :
    forall (sf : TreeState DomainElemState fTree) P,
      evalActionPropGen (@fetchInstDeq dom pcAddrInit fetchCapacity instCapacity type) sf P <->
      evalActionPropGen (@deq dom instCapacity AssembledInst type)
        (fetch_instFifo dom pcAddrInit fetchCapacity instCapacity sf)
        (fun f' res => P (fetch_withInstFifo sf f') res).
  Proof.
    intros sf P.
    unfold fetchInstDeq.
    rewrite (evalActionPropGen_liftAction (@np_fetchInstFifo dom pcAddrInit fetchCapacity instCapacity)).
    reflexivity.
  Qed.

  (* --- 1B. `implDecodeTree` Updaters & Simplification Lemmas --- *)

  Definition decode_withCanProceed (sd : TreeState DomainElemState decTree) (v : bool)
    : TreeState DomainElemState decTree :=
    (v ,, sd.(Snd)).

  Definition decode_withToAluFifo (sd : TreeState DomainElemState decTree)
    (v : TreeState DomainElemState (fifoTree dom decodeCapacity DecodeToAluEntry))
    : TreeState DomainElemState decTree :=
    (sd.(Fst) ,, ((v ,, sd.(Snd).(Fst).(Snd)) ,, sd.(Snd).(Snd))).

  Lemma evalActionPropGen_readDecodeCanProceed :
    forall (sd : TreeState DomainElemState decTree) P,
      evalActionPropGen (@readDecodeCanProceed dom decodeCapacity type) sd P <->
      P sd (decode_canProceed dom decodeCapacity sd).
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_setDecodeCanProceed :
    forall (sd : TreeState DomainElemState decTree) P,
      evalActionPropGen (@setDecodeCanProceed dom decodeCapacity type) sd P <->
      P (decode_withCanProceed sd true) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_clearDecodeCanProceed :
    forall (sd : TreeState DomainElemState decTree) P,
      evalActionPropGen (@clearDecodeCanProceed dom decodeCapacity type) sd P <->
      P (decode_withCanProceed sd false) Zmod.zero.
  Proof. reflexivity. Qed.

  Lemma evalActionPropGen_decodeFirst :
    forall (sd : TreeState DomainElemState decTree) P,
      evalActionPropGen (@decodeFirst dom decodeCapacity type) sd P <->
      evalActionPropGen (@first dom decodeCapacity DecodeToAluEntry type)
        (decode_toAluFifo dom decodeCapacity sd)
        (fun f' res => P (decode_withToAluFifo sd f') res).
  Proof.
    intros sd P.
    unfold decodeFirst.
    rewrite (evalActionPropGen_liftAction (@np_decToAluFifo dom decodeCapacity)).
    reflexivity.
  Qed.

  Lemma evalActionPropGen_decodeDeq :
    forall (sd : TreeState DomainElemState decTree) P,
      evalActionPropGen (@decodeDeq dom decodeCapacity type) sd P <->
      evalActionPropGen (@deq dom decodeCapacity DecodeToAluEntry type)
        (decode_toAluFifo dom decodeCapacity sd)
        (fun f' res => P (decode_withToAluFifo sd f') res).
  Proof.
    intros sd P.
    unfold decodeDeq.
    rewrite (evalActionPropGen_liftAction (@np_decToAluFifo dom decodeCapacity)).
    reflexivity.
  Qed.

End FetchDecodeTreeHelpers.

(* ===========================================================================
 * 2. MEMORY FETCH CHANNEL LEMMAS (`fetchRqs`, `fetchRps`, `FetchRp`, `DeqRp`)
 * =========================================================================== *)

Section MemFetchChannelLemmas.
  Variable core : string.
  Local Opaque liftAction.

  (* --- 2A. `fetchRqs` is empty (`[]`) for all region lists --- *)

  Lemma implMemRegionFetchRqActions_nil :
    forall (r : MemRegion core),
      implMemRegionFetchRqActions r = [].
  Proof.
    intros r; unfold implMemRegionFetchRqActions, implMemRegionTree.
    destruct (r.(regionKind)); reflexivity.
  Qed.

  Lemma implCollectFetchRqActions_nil :
    forall (rs : list (MemRegion core)),
      implCollectFetchRqActions rs = [].
  Proof.
    unfold implCollectFetchRqActions.
    induction rs as [| r rs IH]; cbn [implCollectRegionActions].
    - reflexivity.
    - rewrite implMemRegionFetchRqActions_nil, IH; reflexivity.
  Qed.

  Lemma implMemCollectFetchRqActions_nil :
    forall (rs : list (MemRegion core)) (ty : Kind -> Type),
      implMemCollectFetchRqActions rs ty = [].
  Proof.
    intros rs ty; unfold implMemCollectFetchRqActions.
    rewrite implCollectFetchRqActions_nil; reflexivity.
  Qed.

  (* --- 2B. `mapCpsWithLen` and `ArrayBuilderAction` State Preservation --- *)

  Lemma SemAction_mapCpsWithLen_preserves_state :
    forall {A B : Type} {t : Tree DomainElem} {K : Kind}
           (step : A -> (B -> Action type t K) -> Action type t K)
           (Hstep : forall (x : A) (cont : B -> Action type t K)
                           (s s' : TreeState DomainElemState t) (v : type K),
                      SemAction (step x cont) s s' v ->
                      exists y : B, SemAction (cont y) s s' v)
           (ls : list A)
           (k : forall ys : list B, length ys = length ls -> Action type t K)
           (Hk : forall (ys : list B) (Hlen : length ys = length ls)
                        (s s' : TreeState DomainElemState t) (v : type K),
                   SemAction (k ys Hlen) s s' v -> s' = s)
           (s s' : TreeState DomainElemState t) (v : type K),
      SemAction (mapCpsWithLen step ls k) s s' v ->
      s' = s.
  Proof.
    intros A B t K step Hstep ls.
    induction ls as [| x xs IH]; intros k Hk s s' v Hsem; cbn [mapCpsWithLen] in Hsem.
    - exact (Hk nil eq_refl s s' v Hsem).
    - destruct (Hstep x _ s s' v Hsem) as [y Hy].
      eapply (IH (fun ys Hlen => k (y :: ys) (f_equal S Hlen))); [| exact Hy].
      intros ys Hlen s0 s0' v0 Hk0.
      exact (Hk (y :: ys) (f_equal S Hlen) s0 s0' v0 Hk0).
  Qed.

  Lemma SemAction_ArrayBuilderAction_ReadRpMem_preserves_state :
    forall {t : Tree DomainElem} {n : nat} {k : Kind}
           (step : FinType n -> (Expr type k -> Action type t (Array n k)) -> Action type t (Array n k))
           (Hstep : forall (idx : FinType n) (cont : Expr type k -> Action type t (Array n k))
                           (s s' : TreeState DomainElemState t) (v : type (Array n k)),
                      SemAction (step idx cont) s s' v ->
                      exists e : Expr type k, SemAction (cont e) s s' v)
           (s s' : TreeState DomainElemState t) (v : type (Array n k)),
      SemAction (@ArrayBuilderAction type t n k step) s s' v ->
      s' = s.
  Proof.
    intros t n k step Hstep s s' v Hsem.
    unfold ArrayBuilderAction in Hsem.
    eapply SemAction_mapCpsWithLen_preserves_state; [exact Hstep | | exact Hsem].
    intros ys Hlen s0 s0' v0 Hret.
    apply InversionSemAction in Hret as [Hs0' _]; exact Hs0'.
  Qed.

  Lemma SemAction_internalMemRegionGetFetchRp_preserves_state :
    forall (r : MemRegion core) (isAccessible : bool)
           (s s' : TreeState DomainElemState (internalMemRegionTree r isAccessible))
           (rp : type (LineReadRp r.(regionLineCfg) true)),
      SemAction (@internalMemRegionGetFetchRp core r isAccessible type) s s' rp ->
      s' = s.
  Proof.
    intros r isAccessible s s' rp Hsem.
    unfold internalMemRegionGetFetchRp in Hsem.
    apply InversionSemAction in Hsem as [midState [dataBytes [Harr Hret]]].
    apply InversionSemAction in Hret as [Hs' _]; subst s'.
    eapply SemAction_ArrayBuilderAction_ReadRpMem_preserves_state; [| exact Harr].
    intros idx cont s0 s0' v0 Hrd.
    apply InversionSemAction in Hrd.
    eexists; exact Hrd.
  Qed.

  Lemma evalActionPropGen_liftChild1OptAction_preserves_Fst :
    forall {rootName name : string} {c0 : Tree DomainElem} {b : bool}
           {children rest : list (Tree DomainElem)} {k : Kind}
           (act : Action type (Node name children) k)
           (s : TreeState DomainElemState (Node rootName (c0 :: optNode name b children :: rest)))
           (P : TreeState DomainElemState (Node rootName (c0 :: optNode name b children :: rest)) -> type k -> Prop),
      evalActionPropGen (liftChild1OptAction act) s P ->
      exists s1 (v : type k),
        Fst s1 = Fst s /\
        P s1 v.
  Proof.
    intros rootName name c0 b children rest k act s P H.
    unfold liftChild1OptAction in H.
    destruct b.
    - rewrite (evalActionPropGen_liftAction child1Path) in H.
      destruct (evalActionPropGen_to_SemAction _ _ _ H) as [sub1' [v [_ HP]]].
      exists (writeSubTreeState child1Path s sub1'), v; split; [reflexivity | exact HP].
    - cbn [evalActionPropGen] in H.
      eexists s, _; split; [reflexivity | exact H].
  Qed.

  Lemma evalActionPropGen_liftChild1OptAction_readOnly :
    forall {rootName name : string} {c0 : Tree DomainElem} {b : bool}
           {children rest : list (Tree DomainElem)} {k : Kind}
           (act : Action type (Node name children) k)
           (Hro : forall sub sub' v, SemAction act sub sub' v -> sub' = sub)
           (s : TreeState DomainElemState (Node rootName (c0 :: optNode name b children :: rest)))
           (P : TreeState DomainElemState (Node rootName (c0 :: optNode name b children :: rest)) -> type k -> Prop),
      evalActionPropGen (liftChild1OptAction act) s P ->
      exists v : type k, P s v.
  Proof.
    intros rootName name c0 b children rest k act Hro s P H.
    unfold liftChild1OptAction in H.
    destruct b.
    - rewrite (evalActionPropGen_liftAction child1Path) in H.
      destruct (evalActionPropGen_to_SemAction _ _ _ H) as [sub1' [v [Hact HP]]].
      apply Hro in Hact; subst sub1'.
      destruct s as [s0 [s1 srest]]; eexists v; exact HP.
    - cbn [evalActionPropGen] in H.
      eexists _; exact H.
  Qed.

  Lemma SemAction_implInternalMemRegionFetchResponsePort_preserves_spec :
    forall (r : MemRegion core) (isAccessible : bool)
           (s s' : TreeState DomainElemState (implInternalMemRegionTree r isAccessible))
           (v : bits 0),
      SemAction (@implInternalMemRegionFetchResponsePort core r isAccessible type) s s' v ->
      Fst s' = Fst s.
  Proof.
    intros r isAccessible s s' v Hsem.
    unfold implInternalMemRegionFetchResponsePort in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    cbn [evalActionPropGen] in Hsem.
    apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem as [s1 [readRp [Hs1 Hsem]]].
    cbn [evalActionPropGen] in Hsem.
    lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end.
    - cbn [evalActionPropGen] in Hsem.
      apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem as [s2 [rpValid [Hs2 Hsem]]].
      cbn [evalActionPropGen] in Hsem.
      lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [rp [Hget Hsem1]]].
        pose proof (SemAction_internalMemRegionGetFetchRp_preserves_state r isAccessible _ _ _ Hget) as Hsub0'.
        subst sub0'.
        rewrite writeSubTreeState_readSubTreeState in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem1 as [s3 [_ [Hs3 Hsem2]]].
        apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem2 as [s4 [_ [Hs4 [Hs' _]]]].
        subst s'; congruence.
      + cbn [evalActionPropGen] in Hsem.
        destruct Hsem as [Hs' _]; subst s'; congruence.
    - cbn [evalActionPropGen] in Hsem.
      destruct Hsem as [Hs' _]; subst s'; congruence.
  Qed.

  (* --- 2C. `implRegionsReadFenceIWait`, `implRegionsFetchRp`, `implRegionsDeqRp` --- *)

  Lemma SemAction_memRegionReadFenceIWait_preserves_state :
    forall (r : MemRegion core)
           (sr sr' : TreeState DomainElemState (memRegionTree r))
           (wait : bool),
      SemAction (@memRegionReadFenceIWait core r type) sr sr' wait ->
      sr' = sr.
  Proof.
    intros r sr sr' wait Hsem.
    unfold memRegionReadFenceIWait, memRegionTree in *.
    revert sr sr' Hsem.
    destruct (r.(regionKind)) as [isAcc initD initT | | children rdAct wrAct irqAct fiAct];
      intros sr sr' Hsem.
    - apply InversionSemAction in Hsem as [Hsr' _]; exact Hsr'.
    - unfold externalMemRegionReadFenceIWait in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      eapply evalActionPropGen_liftChild1OptAction_readOnly in Hsem as [? [Hsr' _]].
      + symmetry; exact Hsr'.
      + intros sub sub' v Hsub; apply InversionSemAction in Hsub; apply InversionSemAction in Hsub as [? _]; assumption.
    - unfold customMemRegionReadFenceIWait, customMemRegionTree, customMemChildren in *.
      revert sr sr' Hsem.
      destruct (hasFenceIPort r.(hasExtraFetchPort)); intros sr sr' Hsem;
        rewrite SemAction_iff_evalActionPropGen in Hsem;
        cbn [evalActionPropGen liftAction child0Path customMemFenceIReadWait] in Hsem;
        destruct Hsem as [Hsr' _]; symmetry; exact Hsr'.
  Qed.

  Theorem SemAction_implRegionsReadFenceIWait_preserves_state :
    forall (rs : list (MemRegion core))
           (sm sm' : TreeState DomainElemState (implRegionsTree rs))
           (wait : bool),
      SemAction (@implRegionsReadFenceIWait core type rs) sm sm' wait ->
      sm' = sm.
  Proof.
    induction rs as [| r rs IH]; intros sm sm' wait Hsem.
    - apply InversionSemAction in Hsem as [Hsm' _]; exact Hsm'.
    - cbn [implRegionsReadFenceIWait] in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      rewrite evalActionPropGen_liftAction in Hsem.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [devWait [Hdev Hsem1]]].
      apply SemAction_liftToImplRegion in Hdev as [spec0' [Hspec0' Hsub0']].
      pose proof (SemAction_memRegionReadFenceIWait_preserves_state r _ _ _ Hspec0') as Hspec_eq.
      rewrite Hspec_eq, writeImplRegionSpecState_projImplRegionSpecState in Hsub0'.
      cbn [evalActionPropGen] in Hsem1.
      rewrite evalActionPropGen_liftAction in Hsem1.
      destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [sub1' [restWait [Hrest [Hsm' _]]]].
      pose proof (IH _ _ _ Hrest) as Hsub1'.
      subst sm' sub0' sub1'.
      destruct sm as [s0 [s1 []]]; reflexivity.
  Qed.

  Lemma SemAction_implMemRegionLineReadRp_preserves_state :
    forall (r : MemRegion core) (req : MemRequester)
           (sr sr' : TreeState DomainElemState (implMemRegionTree r))
           (rpOpt : type (Option (LineReadRp r.(regionLineCfg) (isInternalMem r)))),
      SemAction (@implMemRegionLineReadRp core r type req) sr sr' rpOpt ->
      sr' = sr.
  Proof.
    intros r req sr sr' rpOpt Hsem.
    unfold implMemRegionLineReadRp, implMemRegionTree, isInternalMem in *.
    revert sr sr' rpOpt Hsem.
    destruct (r.(regionKind)) as [isAcc initD initT | | children rdAct wrAct irqAct fiAct];
      intros sr sr' rpOpt Hsem.
    - unfold implInternalMemRegionLineReadRp in Hsem.
      destruct (isFetchRequester req && hasFetchPort r.(hasExtraFetchPort)).
      + unfold implInternalMemRegionFetchLineReadRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        eapply evalActionPropGen_liftChild1OptAction_readOnly in Hsem as [? [Hsr' _]].
        * symmetry; exact Hsr'.
        * intros sub sub' v Hsub; apply InversionSemAction in Hsub; apply InversionSemAction in Hsub as [? _]; assumption.
      + unfold implInternalMemRegionDataLineReadRp, implInternalMemRegionPortReadRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        cbn [evalActionPropGen] in Hsem.
        lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end;
          cbn [evalActionPropGen] in Hsem;
          destruct Hsem as [Hsr' _]; symmetry; exact Hsr'.
    - unfold implExternalMemRegionLineReadRp in Hsem.
      destruct (isFetchRequester req && hasFetchPort r.(hasExtraFetchPort)).
      + unfold implExternalMemRegionFetchLineReadRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        eapply evalActionPropGen_liftChild1OptAction_readOnly in Hsem as [? [Hsr' _]].
        * symmetry; exact Hsr'.
        * intros sub sub' v Hsub; apply InversionSemAction in Hsub; apply InversionSemAction in Hsub as [? _]; assumption.
      + unfold implExternalMemRegionDataLineReadRp, implExternalMemRegionPortReadRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        cbn [evalActionPropGen] in Hsem.
        lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end;
          cbn [evalActionPropGen] in Hsem;
          destruct Hsem as [Hsr' _]; symmetry; exact Hsr'.
    - unfold implCustomMemRegionLineReadRp in Hsem.
      destruct (isFetchRequester req && hasFetchPort r.(hasExtraFetchPort)).
      + unfold implCustomMemRegionFetchLineReadRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        eapply evalActionPropGen_liftChild1OptAction_readOnly in Hsem as [? [Hsr' _]].
        * symmetry; exact Hsr'.
        * intros sub sub' v Hsub; apply InversionSemAction in Hsub; apply InversionSemAction in Hsub as [? _]; assumption.
      + unfold implCustomMemRegionDataLineReadRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        cbn [evalActionPropGen] in Hsem.
        lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end;
          cbn [evalActionPropGen] in Hsem;
          destruct Hsem as [Hsr' _]; symmetry; exact Hsr'.
  Qed.

  Lemma SemAction_implMemRegionFetchRp_preserves_state :
    forall (r : MemRegion core) (addr : type Addr)
           (sr sr' : TreeState DomainElemState (implMemRegionTree r))
           (pktOpt : type (Option FetchPacket)),
      SemAction (@implMemRegionFetchRp core r type addr) sr sr' pktOpt ->
      sr' = sr.
  Proof.
    intros r addr sr sr' pktOpt Hsem.
    unfold implMemRegionFetchRp in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    cbn [evalActionPropGen] in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sr1 [rpOpt [Hrp Hsem1]]].
    pose proof (SemAction_implMemRegionLineReadRp_preserves_state r ReqFetch sr sr1 rpOpt Hrp) as Hsr1.
    subst sr1.
    cbn [evalActionPropGen] in Hsem1.
    lazymatch type of Hsem1 with | (if ?b then _ else _) => destruct b end;
      cbn [evalActionPropGen] in Hsem1;
      destruct Hsem1 as [Hsr' _]; symmetry; exact Hsr'.
  Qed.

  Theorem SemAction_implRegionsFetchRp_preserves_state :
    forall (rs : list (MemRegion core)) (addr : type Addr)
           (sm sm' : TreeState DomainElemState (implRegionsTree rs))
           (pktOpt : type (Option FetchPacket)),
      SemAction (@implRegionsFetchRp core type rs addr) sm sm' pktOpt ->
      sm' = sm.
  Proof.
    induction rs as [| r rs IH]; intros addr sm sm' pktOpt Hsem.
    - apply InversionSemAction in Hsem as [Hsm' _]; exact Hsm'.
    - cbn [implRegionsFetchRp] in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [devRp [Hdev Hsem1]]].
        pose proof (SemAction_implMemRegionFetchRp_preserves_state r addr _ _ _ Hdev) as Hsub0'.
        cbn [evalActionPropGen] in Hsem1.
        rewrite evalActionPropGen_liftAction in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [sub1' [restRp [Hrest [Hsm' _]]]].
        pose proof (IH addr _ _ _ Hrest) as Hsub1'.
        subst sm' sub0' sub1'.
        destruct sm as [s0 [s1 []]]; reflexivity.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub1' [restRp [Hrest [Hsm' _]]]].
        pose proof (IH addr _ _ _ Hrest) as Hsub1'.
        subst sm' sub1'.
        destruct sm as [s0 [s1 []]]; reflexivity.
  Qed.

  Lemma SemAction_implMemRegionDeqRp_preserves_spec :
    forall (r : MemRegion core) (req : MemRequester)
           (sr sr' : TreeState DomainElemState (implMemRegionTree r))
           (v : bits 0),
      SemAction (@implMemRegionDeqRp core r type req) sr sr' v ->
      projImplRegionSpecState core r sr' = projImplRegionSpecState core r sr.
  Proof.
    intros r req sr sr' v Hsem.
    unfold implMemRegionDeqRp, projImplRegionSpecState, implMemRegionTree, memRegionTree in *.
    revert sr sr' Hsem.
    destruct (r.(regionKind)) as [isAcc initD initT | | children rdAct wrAct irqAct fiAct];
      intros sr sr' Hsem.
    - unfold implInternalMemRegionDeqRp in Hsem.
      destruct (isFetchRequester req && hasFetchPort r.(hasExtraFetchPort)).
      + unfold implInternalMemRegionFetchDeqRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem as [s1 [_ [Hs1 [Hsr' _]]]].
        subst sr'; exact Hs1.
      + unfold implInternalMemRegionDataDeqRp, implInternalMemRegionPortDeqRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem;
          cbn [evalActionPropGen] in Hsem;
          destruct Hsem as [Hsr' _]; subst sr'; reflexivity.
    - unfold implExternalMemRegionDeqRp in Hsem.
      destruct (isFetchRequester req && hasFetchPort r.(hasExtraFetchPort)).
      + unfold implExternalMemRegionFetchDeqRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem as [s1 [_ [Hs1 [Hsr' _]]]].
        subst sr'; exact Hs1.
      + unfold implExternalMemRegionDataDeqRp, implExternalMemRegionPortDeqRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem;
          cbn [evalActionPropGen] in Hsem;
          destruct Hsem as [Hsr' _]; subst sr'; reflexivity.
    - unfold implCustomMemRegionDeqRp in Hsem.
      destruct (isFetchRequester req && hasFetchPort r.(hasExtraFetchPort)).
      + unfold implCustomMemRegionFetchDeqRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem.
        apply evalActionPropGen_liftChild1OptAction_preserves_Fst in Hsem as [s1 [_ [Hs1 [Hsr' _]]]].
        subst sr'; exact Hs1.
      + unfold implCustomMemRegionDataDeqRp in Hsem.
        rewrite SemAction_iff_evalActionPropGen in Hsem;
          cbn [evalActionPropGen] in Hsem;
          destruct Hsem as [Hsr' _]; subst sr'; reflexivity.
  Qed.

  Theorem SemAction_implRegionsDeqRp_preserves_spec :
    forall (rs : list (MemRegion core)) (req : MemRequester) (addr : type Addr)
           (sm sm' : TreeState DomainElemState (implRegionsTree rs))
           (v : bits 0),
      SemAction (@implRegionsDeqRp core type rs req addr) sm sm' v ->
      StateRel.projImplMemSpecState core rs sm' = StateRel.projImplMemSpecState core rs sm.
  Proof.
    induction rs as [| r rs IH]; intros req addr sm sm' v Hsem.
    - apply InversionSemAction in Hsem as [Hsm' _]; subst sm'; reflexivity.
    - destruct sm as [s0 [s1 []]].
      cbn [implRegionsDeqRp] in Hsem.
      rewrite SemAction_iff_evalActionPropGen in Hsem.
      cbn [evalActionPropGen] in Hsem.
      lazymatch type of Hsem with | (if ?b then _ else _) => destruct b end.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub0' [v0 [Hdeq0 Hsem1]]].
        pose proof (SemAction_implMemRegionDeqRp_preserves_spec r req _ _ _ Hdeq0) as Hsub0'.
        rewrite evalActionPropGen_liftAction in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [sub1' [v1 [Hdeq1 [Hsm' _]]]].
        pose proof (IH req addr _ _ _ Hdeq1) as Hsub1'.
        subst sm'.
        cbn [StateRel.projImplMemSpecState projImplMemRegions implRegionsTree implRegionsChildren child0Path child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsub0', Hsub1' |- *.
        change (projImplRegionSpecState core r) with (StateRel.projImplRegionSpecState core r) in Hsub0'.
        unfold StateRel.projImplMemSpecState in Hsub1'.
        rewrite Hsub0', Hsub1'; reflexivity.
      + cbn [evalActionPropGen] in Hsem.
        rewrite evalActionPropGen_liftAction in Hsem.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [sub1' [v1 [Hdeq1 [Hsm' _]]]].
        pose proof (IH req addr _ _ _ Hdeq1) as Hsub1'.
        subst sm'.
        cbn [StateRel.projImplMemSpecState projImplMemRegions implRegionsTree implRegionsChildren child0Path child1Path readSubTreeState readSubTreeState_child writeSubTreeState writeSubTreeState_child Fst Snd] in Hsub1' |- *.
        unfold StateRel.projImplMemSpecState in Hsub1'.
        rewrite Hsub1'; reflexivity.
  Qed.

End MemFetchChannelLemmas.

(* ===========================================================================
 * 3. SCOREBOARD `mulDivWaitMask` & `regRead` COMMUTATION WITH `flushMulDiv`
 * =========================================================================== *)

Section RegReadScoreboardLemmas.
  Variable core : string.
  Variable pcAddrInit : Z.

  Local Abbreviation rTree := (RfTree core pcAddrInit).
  Local Opaque gprPathsWithKind.

  Definition evalRegRead (regReadIn : type RegReadIn) (rf : RfState core pcAddrInit)
    : type AluInInstGroup :=
    let decodeOut : type DecodeOut           := evalExpr (##regReadIn`"decodeOut") in
    let fetchExc  : type FetchException      := evalExpr (##regReadIn`"fetchExc") in
    let cs1Idx    : type (Bit RegIdxSzReal)  := evalExpr (##decodeOut`"cs1Idx") in
    let cs2Idx    : type (Bit RegIdxSzReal)  := evalExpr (##decodeOut`"cs2Idx") in
    let cs1Raw    : type FullECapWithTag     := evalReadRegsList (gprPathsWithKind core pcAddrInit) cs1Idx rf in
    let cs1       : type FullECapWithTag     := evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw) in
    let cs2Raw    : type FullECapWithTag     := evalReadRegsList (gprPathsWithKind core pcAddrInit) cs2Idx rf in
    let cs2       : type FullECapWithTag     := evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw) in
    evalExpr (STRUCT {
      "writesCd"        ::= ##decodeOut`"writesCd" ;
      "readWriteScrIdx" ::= ##decodeOut`"readWriteScrIdx" ;
      "readWriteCsrIdx" ::= ##decodeOut`"readWriteCsrIdx" ;
      "inst"            ::= ##regReadIn`"inst" ;
      "decodeExc"       ::= ##decodeOut`"decodeExc" ;
      "fetchExc"        ::= #fetchExc ;
      "cs1"             ::= #cs1 ;
      "cs2"             ::= #cs2 ;
      "instGroup"       ::= ##decodeOut`"instGroup"
    } : Expr type AluInInstGroup).

  Lemma evalActionPropGen_regRead :
    forall (regReadIn : type RegReadIn) (rf : RfState core pcAddrInit) P,
      evalActionPropGen (@regRead core pcAddrInit type regReadIn) rf P <->
      P rf (evalRegRead regReadIn rf).
  Proof.
    intros regReadIn rf P.
    unfold regRead, evalRegRead.
    split; intros H.
    - cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_readRegsList (gprPathsWithKind core pcAddrInit) _ _ _)) in H.
      cbn [evalActionPropGen] in H.
      apply (proj1 (evalActionPropGen_readRegsList (gprPathsWithKind core pcAddrInit) _ _ _)) in H.
      cbn [evalActionPropGen] in H; exact H.
    - cbn [evalActionPropGen].
      apply (proj2 (evalActionPropGen_readRegsList (gprPathsWithKind core pcAddrInit) _ _ _)).
      cbn [evalActionPropGen].
      apply (proj2 (evalActionPropGen_readRegsList (gprPathsWithKind core pcAddrInit) _ _ _)).
      cbn [evalActionPropGen]; exact H.
  Qed.

  Lemma SemAction_regRead_iff :
    forall (regReadIn : type RegReadIn) (rf rf' : RfState core pcAddrInit) (out : type AluInInstGroup),
      SemAction (@regRead core pcAddrInit type regReadIn) rf rf' out <->
      rf' = rf /\ out = evalRegRead regReadIn rf.
  Proof.
    intros regReadIn rf rf' out.
    rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_regRead.
    split; intros [H1 H2]; subst; split; reflexivity.
  Qed.

  Lemma mulDivWaitMask_false_inv :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           (baseMask : bits RegIdxSzReal -> bool)
           (idx : bits RegIdxSzReal),
      mulDivWaitMask entries baseMask idx = false ->
      baseMask idx = false /\
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         idx <> dstIdx).
  Proof.
    intros entries baseMask idx Hmask.
    unfold mulDivWaitMask in Hmask.
    apply orb_false_iff in Hmask as [Hbase Hexists].
    split; [exact Hbase |].
    induction entries as [| [d r] rest IH]; intros dstIdx resCap Hin Hnz Heq.
    - contradiction.
    - cbn [existsb] in Hexists.
      apply orb_false_iff in Hexists as [Hdr Hrest].
      destruct Hin as [Hin | Hin].
      + inversion Hin; subst d r idx.
        rewrite Hnz, Zmod.eqb_refl in Hdr; discriminate Hdr.
      + exact (IH Hrest dstIdx resCap Hin Hnz Heq).
  Qed.

  Lemma evalExpr_ITE0_isNotZero_regIdx :
    forall (idx : type (Bit RegIdxSzReal)) (v1 v2 : type FullECapWithTag),
      (Zmod.eqb idx Zmod.zero = false -> v1 = v2) ->
      evalExpr (ITE0 (isNotZero #idx) #v1) = evalExpr (ITE0 (isNotZero #idx) #v2).
  Proof.
    intros idx v1 v2 Heq.
    unfold ITE0.
    set (defCap := Const type FullECapWithTag (getDefault FullECapWithTag)).
    cbn [evalExpr isNotZero isZero evalNot isEq KindCustomInd].
    change (getDefault (Bit RegIdxSzReal)) with (@Zmod.zero (2 ^ RegIdxSzReal)).
    destruct (Zmod.eqb idx Zmod.zero) eqn:Hz; cbn [negb].
    - reflexivity.
    - rewrite (Heq eq_refl); reflexivity.
  Qed.

  Lemma evalRegRead_writeGprVal :
    forall (dstIdx : bits RegIdxSzReal) (resCap : type FullECapWithTag)
           (regReadIn : type RegReadIn) (rf : RfState core pcAddrInit),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs2Idx") in
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb cs1Idx Zmod.zero = false ->
       cs1Idx <> dstIdx) ->
      (Zmod.eqb dstIdx Zmod.zero = false ->
       Zmod.eqb cs2Idx Zmod.zero = false ->
       cs2Idx <> dstIdx) ->
      evalRegRead regReadIn (writeGprVal core pcAddrInit dstIdx resCap rf) =
      evalRegRead regReadIn rf.
  Proof.
    intros dstIdx resCap regReadIn rf decodeOut cs1Idx cs2Idx Hcs1 Hcs2.
    unfold writeGprVal.
    destruct (Zmod.eqb dstIdx Zmod.zero) eqn:Hdst; cbn [negb].
    - reflexivity.
    - unfold evalRegRead; fold decodeOut cs1Idx cs2Idx.
      set (rf' := evalWriteRegsList (gprPathsWithKind core pcAddrInit) dstIdx resCap rf).
      set (cs1Raw1 := evalReadRegsList (gprPathsWithKind core pcAddrInit) cs1Idx rf').
      set (cs1Raw0 := evalReadRegsList (gprPathsWithKind core pcAddrInit) cs1Idx rf).
      set (cs2Raw1 := evalReadRegsList (gprPathsWithKind core pcAddrInit) cs2Idx rf').
      set (cs2Raw0 := evalReadRegsList (gprPathsWithKind core pcAddrInit) cs2Idx rf).
      replace (evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw1))
        with (evalExpr (ITE0 (isNotZero #cs1Idx) #cs1Raw0)).
      + replace (evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw1))
          with (evalExpr (ITE0 (isNotZero #cs2Idx) #cs2Raw0)).
        * reflexivity.
        * symmetry; apply evalExpr_ITE0_isNotZero_regIdx; intros Hc2.
          unfold cs2Raw1, cs2Raw0, rf'.
          rewrite evalReadRegsList_evalWriteRegsList_other;
            [reflexivity | apply NoDup_gprPathsWithKind | exact (Hcs2 eq_refl Hc2)].
      + symmetry; apply evalExpr_ITE0_isNotZero_regIdx; intros Hc1.
        unfold cs1Raw1, cs1Raw0, rf'.
        rewrite evalReadRegsList_evalWriteRegsList_other;
          [reflexivity | apply NoDup_gprPathsWithKind | exact (Hcs1 eq_refl Hc1)].
  Qed.

  Theorem evalRegRead_flushMulDivCaps :
    forall (entries : list (bits RegIdxSzReal * type FullECapWithTag))
           (regReadIn : type RegReadIn)
           (rf : RfState core pcAddrInit),
      let decodeOut : type DecodeOut := evalExpr (##regReadIn`"decodeOut") in
      let cs1Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs1Idx") in
      let cs2Idx : type (Bit RegIdxSzReal) := evalExpr (##decodeOut`"cs2Idx") in
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb cs1Idx Zmod.zero = false ->
         cs1Idx <> dstIdx) ->
      (forall dstIdx resCap,
         In (dstIdx, resCap) entries ->
         Zmod.eqb dstIdx Zmod.zero = false ->
         Zmod.eqb cs2Idx Zmod.zero = false ->
         cs2Idx <> dstIdx) ->
      evalRegRead regReadIn (flushMulDivCaps core pcAddrInit entries rf) =
      evalRegRead regReadIn rf.
  Proof.
    induction entries as [| [dstIdx resCap] rest IH];
      intros regReadIn rf decodeOut cs1Idx cs2Idx Hcs1 Hcs2; cbn [flushMulDivCaps].
    - reflexivity.
    - rewrite IH.
      + apply evalRegRead_writeGprVal.
        * intros Hdst Hc1; exact (Hcs1 dstIdx resCap (or_introl eq_refl) Hdst Hc1).
        * intros Hdst Hc2; exact (Hcs2 dstIdx resCap (or_introl eq_refl) Hdst Hc2).
      + intros d r Hin Hdst Hc1; exact (Hcs1 d r (or_intror Hin) Hdst Hc1).
      + intros d r Hin Hdst Hc2; exact (Hcs2 d r (or_intror Hin) Hdst Hc2).
  Qed.

End RegReadScoreboardLemmas.

(* ===========================================================================
 * 4. CORE-LEVEL FRAME LEMMAS (`fetchRq`, `fetchAssemble`, `decodeAndRegRead`)
 * =========================================================================== *)

Section CoreStageFrameLemmas.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.

  Local Abbreviation rTree := (RfTree core pcAddrInit).
  Local Abbreviation bpT := BpTree.
  Local Abbreviation mTree := (ImplMemSubTree core regions).
  Local Abbreviation fTree := (FetchTree core pcAddrInit fetchCapacity instCapacity).
  Local Abbreviation decTree := (DecodeTree core decodeCapacity).
  Local Abbreviation eTree := (ExecuteTree core).
  Local Abbreviation dmTree := (DataMemTree core dataMemCapacity).
  Local Abbreviation mdTree := (MulDivSubTree core mulCapacity divCapacity mulStages divStages mulDivMode).
  Local Abbreviation cTree := (coreTree core rTree bpT mTree fTree decTree eTree dmTree mdTree).

  Local Abbreviation noInstIfc := (fun ty => @implNoInstIfc ty).
  Local Abbreviation withInstIfc := (fun ty => @implWithInstIfc noInstIfc ty).
  Local Abbreviation memIfc := (fun ty => @implMemIfc core config regions ty rev).
  Local Abbreviation fetchIfc := (fun ty => @implFetchIfc core pcAddrInit fetchCapacity instCapacity ty).
  Local Abbreviation executeIfc := (fun ty => @implExecuteIfc core ty).
  Local Abbreviation dataMemIfc := (fun ty => @implDataMemIfc core dataMemCapacity ty).

  Lemma evalActionPropGen_toAction :
    forall {t : Tree DomainElem} {k : Kind} (le : LetExpr type k)
           (s0 : TreeState DomainElemState t) P,
      evalActionPropGen (@toAction type t k le) s0 P <->
      P s0 (evalLetExpr le).
  Proof.
    intros t k le.
    induction le; intros s0 P; cbn [toAction evalActionPropGen evalLetExpr].
    - reflexivity.
    - apply IHle.
    - rewrite IHle; apply H.
    - destruct (evalExpr p); [rewrite IHle1 | rewrite IHle2]; apply H.
  Qed.

  Lemma evalActionPropGen_LetAction :
    forall {t : Tree DomainElem} {k k' : Kind} (s : string)
           (a : @Action type t k') (cont : type k' -> @Action type t k)
           (s0 : TreeState DomainElemState t) P,
      evalActionPropGen (LetAction s a cont) s0 P ->
      evalActionPropGen a s0 (fun midState midRet => evalActionPropGen (cont midRet) midState P).
  Proof. exact (fun _ _ _ _ _ _ _ _ H => H). Qed.

  Lemma evalActionPropGen_LetExp_ex :
    forall {t : Tree DomainElem} {k k' : Kind} (s : string) (e : Expr type k')
           (cont : type k' -> @Action type t k)
           (s0 : TreeState DomainElemState t) P,
      evalActionPropGen (LetExp s e cont) s0 P ->
      exists v : type k', evalActionPropGen (cont v) s0 P.
  Proof. intros t k k' s e cont s0 P H; exists (evalExpr e); exact H. Qed.

  Lemma evalActionPropGen_IfElse_or :
    forall {t : Tree DomainElem} {k k' : Kind} (s : string) (p : Expr type Bool)
           (t_branch f_branch : @Action type t k') (cont : type k' -> @Action type t k)
           (s0 : TreeState DomainElemState t) P,
      evalActionPropGen (IfElse s p t_branch f_branch cont) s0 P ->
      evalActionPropGen t_branch s0 (fun midState midRet => evalActionPropGen (cont midRet) midState P) \/
      evalActionPropGen f_branch s0 (fun midState midRet => evalActionPropGen (cont midRet) midState P).
  Proof.
    intros t k k' s p tb fb cont s0 P H; cbn [evalActionPropGen] in H.
    destruct (evalExpr p); [left | right]; exact H.
  Qed.

  Lemma evalActionPropGen_Return_ex :
    forall {t : Tree DomainElem} {k : Kind} (e : Expr type k)
           (s0 : TreeState DomainElemState t) P,
      evalActionPropGen (Return e) s0 P ->
      exists v : type k, P s0 v.
  Proof. intros t k e s0 P H; exists (evalExpr e); exact H. Qed.

  Lemma evalActionPropGen_toAction_ex :
    forall {t : Tree DomainElem} {k : Kind} (le : LetExpr type k)
           (s0 : TreeState DomainElemState t) P,
      evalActionPropGen (@toAction type t k le) s0 P ->
      exists v : type k, P s0 v.
  Proof.
    intros t k le s0 P H.
    apply (proj1 (evalActionPropGen_toAction le s0 P)) in H.
    exists (evalLetExpr le); exact H.
  Qed.

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList
               toAction evalLetExpr preDecode preDecodeBranch wrappedDecode.

  Lemma SemAction_readRegsList :
    forall {k sz t} (paths : list (RegOfKind (t:=t) k))
           (idx : Expr type (Bit sz))
           (s s' : TreeState DomainElemState t) (out : type k),
      SemAction (@readRegsList type k sz t paths idx) s s' out ->
      s' = s /\ out = evalReadRegsList paths (evalExpr idx) s.
  Proof.
    intros k sz t paths idx s s' out Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_readRegsList paths _ _ _)) in Hsem.
    destruct Hsem as [-> <-]; split; reflexivity.
  Qed.

  (* --- 4A. `fetchRq` Core-Level Frame --- *)

  Theorem fetchRq_core_frame :
    forall (c c' : TreeState DomainElemState cTree) (v : bits 0),
      SemAction
        (@fetchRq core pcAddrInit fetchCapacity instCapacity
                  noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type)
        c c' v ->
      c'.(Fst) = c.(Fst) /\
      c'.(Snd).(Fst) = c.(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd) /\
      fetch_instFifo core pcAddrInit fetchCapacity instCapacity (c'.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) =
        fetch_instFifo core pcAddrInit fetchCapacity instCapacity (c.(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) /\
      (c'.(Snd).(Snd).(Snd).(Fst).(Fst) = c.(Snd).(Snd).(Snd).(Fst).(Fst) \/
       (exec_fenceIPending core (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) = false /\
        exists alignedPc canEnq,
          SemAction (@implReadInstRq core regions type alignedPc)
            (c.(Snd).(Snd).(Snd).(Fst).(Fst))
            (c'.(Snd).(Snd).(Snd).(Fst).(Fst))
            canEnq)).
  Proof.
    intros c c' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    unfold fetchRq in Hsem.
    cbn [evalActionPropGen] in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@np_fetchFifo core pcAddrInit fetchCapacity instCapacity
                                   noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem.
    cbn [evalActionPropGen isFull] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    cbn [evalActionPropGen] in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_execute core pcAddrInit fetchCapacity instCapacity
                                           noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem.
    cbn [evalActionPropGen execute_readFenceIPend implExecuteIfc readFenceIPending] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_mem core pcAddrInit fetchCapacity instCapacity
                                       noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [m1 [fenceIWait [Hm1 Hsem1]]].
    pose proof (SemAction_implRegionsReadFenceIWait_preserves_state core regions _ _ _ Hm1) as Hm1_eq.
    subst m1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    cbn [evalActionPropGen] in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_fetch core pcAddrInit fetchCapacity instCapacity
                                         noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    cbn [evalActionPropGen readFetchPc] in Hsem1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_execute core pcAddrInit fetchCapacity instCapacity
                                           noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    cbn [evalActionPropGen execute_readExecEpoch implExecuteIfc readExecEpoch] in Hsem1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_fetch core pcAddrInit fetchCapacity instCapacity
                                         noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    cbn [evalActionPropGen readPredEpoch] in Hsem1.
    rewrite !writeSubTreeState_readSubTreeState in Hsem1.
    apply (proj1 (evalActionPropGen_liftAction
                    (@ImplFetch.np_rf core pcAddrInit fetchCapacity instCapacity
                                      noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [rf1 [pcc [Hrf1 Hsem2]]].
    apply SemAction_readRegsList in Hrf1 as [-> _].
    rewrite !writeSubTreeState_readSubTreeState in Hsem2.
    clear Hsem1; rename Hsem2 into Hsem1.
    cbn [evalActionPropGen] in Hsem1.
    lazymatch type of Hsem1 with
    | context[if ?cond then _ else _] => destruct cond eqn:Hcond
    end.
    - (* Precondition holds *)
      assert (Hfip : exec_fenceIPending core (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Fst)) = false).
      { cbn [evalExpr fold_left map evalAndBinary evalBinary evalNot KindCustomInd InvDefault andb] in Hcond.
        apply andb_prop in Hcond as [Hcond _].
        apply andb_prop in Hcond as [_ Hfip'].
        apply negb_true_iff in Hfip'; exact Hfip'. }
      cbn [evalActionPropGen] in Hsem1.
      lazymatch type of Hsem1 with
      | context[if evalExpr (Var type Bool ?hp) then _ else _] => destruct hp eqn:Hhp
      end.
      + (* hasPreFault = true *)
        change (evalExpr (Var type Bool true)) with true in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        change (evalExpr (Var type Bool (evalExpr (ConstBool true)))) with true in Hsem1.
        change (evalExpr (Not (Var type Bool true))) with false in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        apply (proj1 (evalActionPropGen_liftAction
                        (@np_fetchFifo core pcAddrInit fetchCapacity instCapacity
                                       noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [ff' [_ [_ Hsem2]]].
        apply (proj1 (evalActionPropGen_liftAction
                        (@ImplFetch.np_fetch core pcAddrInit fetchCapacity instCapacity
                                             noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem2.
        cbn [evalActionPropGen writeFetchPc] in Hsem2.
        destruct Hsem2 as [<- _].
        repeat split; try reflexivity; left; reflexivity.
      + (* hasPreFault = false *)
        change (evalExpr (Var type Bool false)) with false in Hsem1.
        cbn [evalActionPropGen] in Hsem1.
        apply (proj1 (evalActionPropGen_liftAction
                        (@ImplFetch.np_mem core pcAddrInit fetchCapacity instCapacity
                                           noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem1.
        destruct (evalActionPropGen_to_SemAction _ _ _ Hsem1) as [m2 [canEnq [Hm2 Hsem2]]].
        cbn [evalActionPropGen] in Hsem2.
        change (evalExpr (Var type Bool canEnq)) with canEnq in Hsem2.
        destruct canEnq.
        * change (evalExpr (Not (Var type Bool false))) with true in Hsem2.
          cbn [evalActionPropGen] in Hsem2.
          apply (proj1 (evalActionPropGen_liftAction
                          (@np_noInst core pcAddrInit fetchCapacity instCapacity
                                      noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem2.
          destruct (evalActionPropGen_to_SemAction _ _ _ Hsem2) as [ni' [noInstOut [_ Hsem3]]].
          cbn [evalActionPropGen] in Hsem3.
          apply (proj1 (evalActionPropGen_liftAction
                          (@np_fetchFifo core pcAddrInit fetchCapacity instCapacity
                                         noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem3.
          destruct (evalActionPropGen_to_SemAction _ _ _ Hsem3) as [ff' [_ [_ Hsem4]]].
          apply (proj1 (evalActionPropGen_liftAction
                          (@ImplFetch.np_fetch core pcAddrInit fetchCapacity instCapacity
                                               noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type) _ _ _)) in Hsem4.
          cbn [evalActionPropGen writeFetchPc] in Hsem4.
          destruct Hsem4 as [<- _].
          repeat split; try reflexivity.
          right; split; [exact Hfip |].
          eexists _, true; exact Hm2.
        * cbn [evalActionPropGen] in Hsem2.
          destruct Hsem2 as [<- _].
          repeat split; try reflexivity.
          right; split; [exact Hfip |].
          eexists _, false; exact Hm2.
    - (* Precondition false *)
      cbn [evalActionPropGen] in Hsem1.
      destruct Hsem1 as [<- _].
      repeat split; try reflexivity; left; reflexivity.
  Qed.

  (* --- Compositional `preserves_rel` Combinators --- *)

  Definition preserves_rel {t : Tree DomainElem}
    (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
    {k : Kind} (a : @Action type t k) : Prop :=
    forall s s' v, SemAction a s s' v -> R s' s.

  Lemma preserves_rel_Return :
    forall {t : Tree DomainElem} (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
           (Hrefl : forall s, R s s) {k : Kind} (e : Expr type k),
      preserves_rel R (Return e).
  Proof.
    intros t R Hrefl k e s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    destruct Hsem as [<- _]; apply Hrefl.
  Qed.

  Lemma preserves_rel_LetExp :
    forall {t : Tree DomainElem} (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
           {k k' : Kind} (nm : string) (e : Expr type k') (cont : type k' -> @Action type t k),
      (forall x, preserves_rel R (cont x)) ->
      preserves_rel R (LetExp nm e cont).
  Proof.
    intros t R k k' nm e cont Hcont s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    rewrite <- SemAction_iff_evalActionPropGen in Hsem.
    eapply Hcont; exact Hsem.
  Qed.

  Lemma preserves_rel_LetAction :
    forall {t : Tree DomainElem} (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
           (Htrans : forall s1 s2 s3, R s3 s2 -> R s2 s1 -> R s3 s1)
           {k k' : Kind} (nm : string) (a : @Action type t k') (cont : type k' -> @Action type t k),
      preserves_rel R a ->
      (forall x, preserves_rel R (cont x)) ->
      preserves_rel R (LetAction nm a cont).
  Proof.
    intros t R Htrans k k' nm a cont Ha Hcont s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    apply (evalActionPropGen_to_SemAction a s _) in Hsem as [midState [midRet [H1 H2]]].
    rewrite <- SemAction_iff_evalActionPropGen in H2.
    eapply Htrans; [eapply Hcont; exact H2 | eapply Ha; exact H1].
  Qed.

  Lemma preserves_rel_IfElse :
    forall {t : Tree DomainElem} (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
           (Htrans : forall s1 s2 s3, R s3 s2 -> R s2 s1 -> R s3 s1)
           {k k' : Kind} (nm : string) (p : Expr type Bool)
           (tb fb : @Action type t k') (cont : type k' -> @Action type t k),
      preserves_rel R tb ->
      preserves_rel R fb ->
      (forall x, preserves_rel R (cont x)) ->
      preserves_rel R (IfElse nm p tb fb cont).
  Proof.
    intros t R Htrans k k' nm p tb fb cont Htb Hfb Hcont s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem; cbn [evalActionPropGen] in Hsem.
    destruct (evalExpr p).
    - apply (evalActionPropGen_to_SemAction tb s _) in Hsem as [midState [midRet [H1 H2]]].
      rewrite <- SemAction_iff_evalActionPropGen in H2.
      eapply Htrans; [eapply Hcont; exact H2 | eapply Htb; exact H1].
    - apply (evalActionPropGen_to_SemAction fb s _) in Hsem as [midState [midRet [H1 H2]]].
      rewrite <- SemAction_iff_evalActionPropGen in H2.
      eapply Htrans; [eapply Hcont; exact H2 | eapply Hfb; exact H1].
  Qed.

  Lemma preserves_rel_toAction :
    forall {t : Tree DomainElem} (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
           (Hrefl : forall s, R s s) {k : Kind} (le : LetExpr type k),
      preserves_rel R (@toAction type t k le).
  Proof.
    intros t R Hrefl k le s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_toAction le s _)) in Hsem as [<- _].
    apply Hrefl.
  Qed.

  Lemma preserves_rel_liftAction :
    forall {t : Tree DomainElem} (R : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop)
           (p : NodePath t) {k : Kind} (a : @Action type (getNode p) k),
      (forall s sub' v, SemAction a (readSubTreeState p s) sub' v -> R (writeSubTreeState p s sub') s) ->
      preserves_rel R (@liftAction type t p k a).
  Proof.
    intros t R p k a Hlift s s' v Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction p a s _)) in Hsem.
    apply (evalActionPropGen_to_SemAction a (readSubTreeState p s) _) in Hsem
      as [sub' [ret' [Hsub [<- _]]]].
    eapply Hlift; exact Hsub.
  Qed.

  (* --- 4B. `fetchAssemble` Core-Level Frame --- *)

  Definition fetchAssemble_rel (c' c : TreeState DomainElemState cTree) : Prop :=
    c'.(Fst) = c.(Fst) /\
    c'.(Snd).(Fst) = c.(Snd).(Fst) /\
    c'.(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd) /\
    projImplMemSpecState core regions (c'.(Snd).(Snd).(Snd).(Fst).(Fst)) =
      projImplMemSpecState core regions (c.(Snd).(Snd).(Snd).(Fst).(Fst)).

  Lemma fetchAssemble_rel_refl : forall c, fetchAssemble_rel c c.
  Proof. intro c; unfold fetchAssemble_rel; repeat split; reflexivity. Qed.

  Lemma fetchAssemble_rel_trans :
    forall c1 c2 c3, fetchAssemble_rel c3 c2 -> fetchAssemble_rel c2 c1 -> fetchAssemble_rel c3 c1.
  Proof.
    intros c1 c2 c3 [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]].
    unfold fetchAssemble_rel; repeat split; congruence.
  Qed.

  Local Ltac solve_fetchAssemble_lift :=
    intros s sub' v Hsub;
    try (
      unfold mem_getInstRp, implMemIfc, implGetInstRp in Hsub;
      pose proof (SemAction_implRegionsFetchRp_preserves_state core regions _ _ _ _ Hsub) as HrpEq;
      subst sub'
    );
    try (
      unfold mem_deqInstRp, implMemIfc, implDeqInstRp in Hsub;
      pose proof (SemAction_implRegionsDeqRp_preserves_spec core regions ReqFetch _ _ _ _ Hsub) as HdeqEq;
      cbn [ImplFetch.np_mem readSubTreeState readSubTreeState_child Fst Snd] in HdeqEq
    );
    try (
      unfold execute_readExecEpoch, implExecuteIfc, readExecEpoch in Hsub;
      apply InversionSemAction in Hsub;
      apply InversionSemAction in Hsub as [HexEq _];
      subst sub'
    );
    try (
      apply SemAction_readRegsList in Hsub as [HrfEq _];
      subst sub'
    );
    unfold fetchAssemble_rel;
    cbn [ImplFetch.np_mem ImplFetch.np_fetch np_fetchFifo np_instFifo
         ImplFetch.np_bp np_noInst ImplFetch.np_execute ImplFetch.np_rf
         writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child Fst Snd];
    repeat split; try reflexivity; eauto.

  Theorem fetchAssemble_core_frame :
    forall (c c' : TreeState DomainElemState cTree) (v : bits 0),
      SemAction
        (@fetchAssemble core pcAddrInit fetchCapacity instCapacity
                        noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type)
        c c' v ->
      c'.(Fst) = c.(Fst) /\
      c'.(Snd).(Fst) = c.(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd) /\
      projImplMemSpecState core regions (c'.(Snd).(Snd).(Snd).(Fst).(Fst)) =
        projImplMemSpecState core regions (c.(Snd).(Snd).(Snd).(Fst).(Fst)).
  Proof.
    change (preserves_rel fetchAssemble_rel
              (@fetchAssemble core pcAddrInit fetchCapacity instCapacity
                              noInstIfc withInstIfc memIfc executeIfc decTree dmTree mdTree type)).
    unfold fetchAssemble.
    repeat lazymatch goal with
    | |- forall _, _ => intro
    | |- preserves_rel _ (LetAction _ _ _) =>
        apply (preserves_rel_LetAction _ fetchAssemble_rel_trans)
    | |- preserves_rel _ (LetExp _ _ _) =>
        apply preserves_rel_LetExp
    | |- preserves_rel _ (IfElse _ _ _ _ _) =>
        apply (preserves_rel_IfElse _ fetchAssemble_rel_trans)
    | |- preserves_rel _ (Return _) =>
        apply (preserves_rel_Return _ fetchAssemble_rel_refl)
    | |- preserves_rel _ (@toAction _ _ _ _) =>
        apply (preserves_rel_toAction _ fetchAssemble_rel_refl)
    | |- preserves_rel _ (@liftAction _ _ _ _ _) =>
        apply preserves_rel_liftAction; solve_fetchAssemble_lift
    end.
  Qed.

  (* --- 4C. `decodeAndRegRead` Core-Level Frame --- *)

  Definition decodeAndRegRead_rel (c' c : TreeState DomainElemState cTree) : Prop :=
    c'.(Fst) = c.(Fst) /\
    c'.(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Fst) /\
    c'.(Snd).(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Snd).(Fst) /\
    c'.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).

  Lemma decodeAndRegRead_rel_refl : forall c, decodeAndRegRead_rel c c.
  Proof. intro c; unfold decodeAndRegRead_rel; repeat split; reflexivity. Qed.

  Lemma decodeAndRegRead_rel_trans :
    forall c1 c2 c3, decodeAndRegRead_rel c3 c2 -> decodeAndRegRead_rel c2 c1 -> decodeAndRegRead_rel c3 c1.
  Proof.
    intros c1 c2 c3 [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]].
    unfold decodeAndRegRead_rel; repeat split; congruence.
  Qed.

  Local Ltac solve_decodeAndRegRead_lift :=
    intros s sub' v Hsub;
    try (
      unfold execute_readExecEpoch, implExecuteIfc, readExecEpoch in Hsub;
      apply InversionSemAction in Hsub;
      apply InversionSemAction in Hsub as [HexEq _];
      subst sub'
    );
    try (
      apply SemAction_regRead_iff in Hsub as [HrfEq _];
      subst sub'
    );
    unfold decodeAndRegRead_rel;
    cbn [ImplDecode.np_decode np_decodeToAluFifo ImplDecode.np_fetch
         ImplDecode.np_execute ImplDecode.np_rf ImplDecode.np_waitBits
         writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child Fst Snd];
    repeat split; reflexivity.

  Theorem decodeAndRegRead_core_frame :
    forall (c c' : TreeState DomainElemState cTree) (v : bits 0),
      SemAction
        (@decodeAndRegRead core decodeCapacity pcAddrInit
                           bpT mdTree fetchIfc executeIfc dataMemIfc memIfc type)
        c c' v ->
      c'.(Fst) = c.(Fst) /\
      c'.(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Fst) = c.(Snd).(Snd).(Snd).(Fst) /\
      c'.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd) = c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).
  Proof.
    change (preserves_rel decodeAndRegRead_rel
              (@decodeAndRegRead core decodeCapacity pcAddrInit
                                 bpT mdTree fetchIfc executeIfc dataMemIfc memIfc type)).
    unfold decodeAndRegRead.
    repeat lazymatch goal with
    | |- forall _, _ => intro
    | |- preserves_rel _ (LetAction _ _ _) =>
        apply (preserves_rel_LetAction _ decodeAndRegRead_rel_trans)
    | |- preserves_rel _ (LetExp _ _ _) =>
        apply preserves_rel_LetExp
    | |- preserves_rel _ (IfElse _ _ _ _ _) =>
        apply (preserves_rel_IfElse _ decodeAndRegRead_rel_trans)
    | |- preserves_rel _ (Return _) =>
        apply (preserves_rel_Return _ decodeAndRegRead_rel_refl)
    | |- preserves_rel _ (@toAction _ _ _ _) =>
        apply (preserves_rel_toAction _ decodeAndRegRead_rel_refl)
    | |- preserves_rel _ (@liftAction _ _ _ _ _) =>
        apply preserves_rel_liftAction; solve_decodeAndRegRead_lift
    end.
  Qed.

End CoreStageFrameLemmas.

(* ===========================================================================
 * 5. SYSTEM-LEVEL SIMULATION FOR FETCH, DECODE & `setCanProceedSteps`
 * =========================================================================== *)

Section FetchDecodeSystemSim.
  Variable core : string.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable config : RevConfig.
  Variable regions : list (MemRegion core).
  Variable clint : @ClintInstance core regions.
  Variable rev : @RevokerInstance core (implRevokerExtraChildren core) regions.
  Variable revSpec : @RevokerInstance core [] regions.
  Variable plic : @PlicInstance core (S (S (length (collectIrqActions regions)))) regions.

  Local Abbreviation sTree := (SpecTree core pcAddrInit regions).
  Local Abbreviation iTree :=
    (ImplTree core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation SState := (SpecState core pcAddrInit regions).
  Local Abbreviation IState :=
    (ImplState core pcAddrInit fetchCapacity instCapacity decodeCapacity
               dataMemCapacity mulCapacity divCapacity mulStages divStages
               mulDivMode config regions).
  Local Abbreviation specMod := (@spec core pcAddrInit config regions clint revSpec plic).
  Local Abbreviation sRel :=
    (stateRel core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions).
  Local Abbreviation implRf :=
    (@SimDevices.implRf core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implWaitBits :=
    (@SimDevices.implWaitBits core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implBp :=
    (@SimDevices.implBp core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implMem :=
    (@SimDevices.implMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implFetch :=
    (@SimDevices.implFetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implDecode :=
    (@SimDevices.implDecode core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implExecute :=
    (@SimDevices.implExecute core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implDataMem :=
    (@SimDevices.implDataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).
  Local Abbreviation implMulDiv :=
    (@SimDevices.implMulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode config regions).

  Local Opaque gprPathsWithKind gprWaitPathsWithKind liftAction writeRegsList readRegsList
               toAction evalLetExpr preDecode preDecodeBranch wrappedDecode.

  (* --- 5A. General Stuttering & Frontend `stateRel` Preservation Helpers --- *)

  Theorem spec_stutter :
    forall (s2 : SState),
      SemActions (map snd (specMod type)) s2 s2.
  Proof.
    intros s2; apply NilAction; reflexivity.
  Qed.

  Lemma stateRel_preserved_by_frontend_step :
    forall (s1 s1' : IState) (s2 : SState),
      sRel s1 s2 ->
      impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions s1' =
        impl_rf core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions s1 ->
      StateRel.projImplMemSpecState core regions
        (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1') =
        StateRel.projImplMemSpecState core regions
          (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1) ->
      impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 ->
      impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                   dataMemCapacity mulCapacity divCapacity mulStages divStages
                   mulDivMode config regions s1' =
        impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                     dataMemCapacity mulCapacity divCapacity mulStages divStages
                     mulDivMode config regions s1 ->
      impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1' =
        impl_mulDiv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                    dataMemCapacity mulCapacity divCapacity mulStages divStages
                    mulDivMode config regions s1 ->
      (FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      sRel s1' s2.
  Proof.
    intros s1 s1' s2 Hrel Hrf Hmem Hexec Hdm Hmd Hfence.
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  (* --- 5B. `setCanProceedSteps` Simulation (`setFetchCanProceedStage`, `setDecodeCanProceedStage`, `setExecuteCanProceedStage`) --- *)

  Theorem sim_setFetchCanProceedStage :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@setFetchCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setFetchCanProceedStage_inv core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s1' v Hsem)
      as [_ [_ [Hrf [_ [_ [Hmem [Hdecode [Hexec [Hdm [Hmd [_ [_ [_ [_ [_ HrestFetch]]]]]]]]]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      rewrite Hmem; reflexivity.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive,
             StateRel.fetch_instFifo, fetch_instFifo in *.
      change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      change (impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      split.
      + rewrite Hexec, Hdm, Hmem, Hdecode, HrestFetch.
        exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  Theorem sim_setDecodeCanProceedStage :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@setDecodeCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hsem Hrel.
    pose proof (SemAction_setDecodeCanProceedStage_inv core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions s1 s1' v Hsem)
      as [_ [_ [Hrf [_ [_ [Hmem [Hfetch [Hexec [Hdm [Hmd [_ HrestDec]]]]]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      rewrite Hmem; reflexivity.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive,
             StateRel.decode_toAluFifo, decode_toAluFifo in *.
      change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      change (impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      split.
      + rewrite Hexec, Hdm, Hmem, Hfetch, HrestDec.
        exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  Theorem sim_setExecuteCanProceedStage :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@setExecuteCanProceedStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hsem Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_setCanProceedSteps :
    forall (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@setCanProceedSteps core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros act s1 s1' s2 v Hin Hsem Hrel.
    unfold setCanProceedSteps in Hin.
    destruct Hin as [<- | [<- | [<- | []]]].
    - exact (sim_setFetchCanProceedStage s1 s1' s2 v Hsem Hrel).
    - exact (sim_setDecodeCanProceedStage s1 s1' s2 v Hsem Hrel).
    - exact (sim_setExecuteCanProceedStage s1 s1' s2 v Hsem Hrel).
  Qed.

  (* --- 5C. `fetchRqs` and `fetchRps` Simulation --- *)

  Lemma fetchRqs_nil :
    @fetchRqs core pcAddrInit fetchCapacity instCapacity decodeCapacity
              dataMemCapacity mulCapacity divCapacity mulStages divStages
              mulDivMode config regions type = [].
  Proof.
    unfold fetchRqs; rewrite implMemCollectFetchRqActions_nil; reflexivity.
  Qed.

  Theorem sim_fetchRqs :
    forall (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@fetchRqs core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros act s1 s1' s2 v Hin.
    rewrite fetchRqs_nil in Hin; contradiction.
  Qed.

  Theorem fetchRps_frame :
    forall (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (v : bits 0),
      In act
        (@fetchRps core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction act s1 s1' v ->
      s1' = writeSubTreeState
              (@Impl.np_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions)
              s1 (implMem s1') /\
      implRf s1' = implRf s1 /\
      implWaitBits s1' = implWaitBits s1 /\
      implBp s1' = implBp s1 /\
      implFetch s1' = implFetch s1 /\
      implDecode s1' = implDecode s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1.
  Proof.
    intros act s1 s1' v Hin Hsem.
    unfold fetchRps in Hin.
    apply in_map_iff in Hin as [memAct [<- HinMem]].
    apply (SemAction_lift_np_mem_impl core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions) in Hsem as [m1' [_ Hs1']].
    subst s1'; repeat split; reflexivity.
  Qed.

  Theorem sim_fetchRps :
    forall (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@fetchRps core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction act s1 s1' v ->
      StateRel.projImplMemSpecState core regions (implMem s1') =
        StateRel.projImplMemSpecState core regions (implMem s1) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros act s1 s1' s2 v Hin Hsem Hmem Hrel.
    pose proof (fetchRps_frame act s1 s1' v Hin Hsem)
      as [_ [Hrf [_ [_ [Hfetch [Hdecode [Hexec [Hdm Hmd]]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      exact Hmem.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive in *.
      change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      change (impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      split.
      + rewrite Hexec, Hfetch, Hdecode, Hdm, Hmem; exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  (* --- 5D. `fetchRqStage` Simulation --- *)

  Theorem fetchRqStage_frame :
    forall (s1 s1' : IState) (v : bits 0),
      SemAction
        (@fetchRqStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      implRf s1' = implRf s1 /\
      implWaitBits s1' = implWaitBits s1 /\
      implDecode s1' = implDecode s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1 /\
      fetch_instFifo core pcAddrInit fetchCapacity instCapacity (implFetch s1') =
        fetch_instFifo core pcAddrInit fetchCapacity instCapacity (implFetch s1) /\
      (implMem s1' = implMem s1 \/
       (exec_fenceIPending core (implExecute s1) = false /\
        exists alignedPc canEnq,
          SemAction (@implReadInstRq core regions type alignedPc)
            (implMem s1) (implMem s1') canEnq)).
  Proof.
    intros s1 s1' v Hsem.
    unfold fetchRqStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    rewrite (evalActionPropGen_liftAction
               (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                  dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [Hc [Hs1' _]]]].
    subst s1'.
    pose proof (fetchRq_core_frame core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions rev (Fst s1) c' v' Hc)
      as [Hrf [Hwb [Hrest [Hinst Hmem]]]].
    unfold SimDevices.implRf, SimDevices.implWaitBits, SimDevices.implMem, SimDevices.implFetch,
           SimDevices.implDecode, SimDevices.implExecute, SimDevices.implDataMem, SimDevices.implMulDiv;
      cbn [writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child implSysTree Impl.np_core Fst Snd].
    rewrite Hrf, Hwb, Hrest, Hinst.
    repeat split; try reflexivity; exact Hmem.
  Qed.

  Theorem sim_fetchRqStage :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@fetchRqStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      StateRel.projImplMemSpecState core regions (implMem s1') =
        StateRel.projImplMemSpecState core regions (implMem s1) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hsem Hmem Hrel.
    pose proof (fetchRqStage_frame s1 s1' v Hsem)
      as [Hrf [_ [Hdecode [Hexec [Hdm [Hmd [Hinst _]]]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      exact Hmem.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - intros [Hquiescent Hcons].
      unfold FenceIInv, FenceIPipelineQuiescent, FenceIActive,
             StateRel.fetch_instFifo, fetch_instFifo in *.
      change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem in *.
      change (impl_execute core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implExecute in *.
      change (impl_dataMem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDataMem in *.
      change (impl_fetch core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implFetch in *.
      change (impl_decode core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implDecode in *.
      split.
      + rewrite Hexec, Hinst, Hdecode, Hdm, Hmem; exact Hquiescent.
      + rewrite Hmem; exact Hcons.
  Qed.

  (* --- 5E. `fetchAssembleStage` Simulation --- *)

  Theorem fetchAssembleStage_frame :
    forall (s1 s1' : IState) (v : bits 0),
      SemAction
        (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      implRf s1' = implRf s1 /\
      implWaitBits s1' = implWaitBits s1 /\
      implDecode s1' = implDecode s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1 /\
      StateRel.projImplMemSpecState core regions (implMem s1') =
        StateRel.projImplMemSpecState core regions (implMem s1).
  Proof.
    intros s1 s1' v Hsem.
    unfold fetchAssembleStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions) _ _ _)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [Hc [Hs1' _]]]].
    subst s1'.
    pose proof (fetchAssemble_core_frame core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions rev (Fst s1) c' v' Hc)
      as [Hrf [Hwb [Hrest Hmem]]].
    unfold SimDevices.implRf, SimDevices.implWaitBits, SimDevices.implMem,
           SimDevices.implDecode, SimDevices.implExecute, SimDevices.implDataMem, SimDevices.implMulDiv;
      cbn [writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child implSysTree Impl.np_core Fst Snd].
    rewrite Hrf, Hwb, Hrest.
    repeat split; try reflexivity; exact Hmem.
  Qed.

  Lemma evalActionPropGen_IfElse_false :
    forall {t : Tree DomainElem} {k k' : Kind} (s : string) (p : Expr type Bool)
           (t_branch f_branch : @Action type t k') (cont : type k' -> @Action type t k)
           (s0 : TreeState DomainElemState t) P,
      evalExpr p = false ->
      evalActionPropGen (IfElse s p t_branch f_branch cont) s0 P ->
      evalActionPropGen f_branch s0 (fun midState midRet => evalActionPropGen (cont midRet) midState P).
  Proof.
    intros t k k' s p tb fb cont s0 P Hp H; cbn [evalActionPropGen] in H.
    rewrite Hp in H; exact H.
  Qed.

  Lemma SemAction_fetchAssembleStage_notCanProceed :
    forall (s1 s1' : IState) (v : bits 0),
      fetch_canProceed core pcAddrInit fetchCapacity instCapacity (implFetch s1) = false ->
      SemAction
        (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      s1' = s1 /\ v = Zmod.zero.
  Proof.
    intros s1 s1' v Hcp Hsem.
    unfold fetchAssembleStage, fetchAssemble in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply evalActionPropGen_LetAction in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply (proj1 (evalActionPropGen_readFetchCanProceed _ _ _ _ _ _)) in Hsem.
    eapply evalActionPropGen_IfElse_false in Hsem; [| exact Hcp].
    cbn [evalActionPropGen] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    destruct Hsem as [<- <-]; split; reflexivity.
  Qed.

  Theorem sim_fetchAssembleStage_notCanProceed :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      fetch_canProceed core pcAddrInit fetchCapacity instCapacity (implFetch s1) = false ->
      SemAction
        (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hcp Hsem Hrel.
    destruct (SemAction_fetchAssembleStage_notCanProceed s1 s1' v Hcp Hsem) as [-> _].
    exists s2; split; [apply spec_stutter | exact Hrel].
  Qed.

  Theorem sim_fetchAssembleStage :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      (FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hsem Hfence Hrel.
    pose proof (fetchAssembleStage_frame s1 s1' v Hsem)
      as [Hrf [_ [_ [Hexec [Hdm [Hmd Hmem]]]]]].
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf Hmem Hexec Hdm Hmd Hfence).
  Qed.

  (* --- 5F. `decodeAndRegReadStage` Simulation --- *)

  Theorem decodeAndRegReadStage_frame :
    forall (s1 s1' : IState) (v : bits 0),
      SemAction
        (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      implRf s1' = implRf s1 /\
      implBp s1' = implBp s1 /\
      implMem s1' = implMem s1 /\
      implExecute s1' = implExecute s1 /\
      implDataMem s1' = implDataMem s1 /\
      implMulDiv s1' = implMulDiv s1.
  Proof.
    intros s1 s1' v Hsem.
    unfold decodeAndRegReadStage in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction
                    (@Impl.np_core core pcAddrInit fetchCapacity instCapacity decodeCapacity
                       dataMemCapacity mulCapacity divCapacity mulStages divStages
                       mulDivMode config regions) _ _ _)) in Hsem.
    destruct (evalActionPropGen_to_SemAction _ _ _ Hsem) as [c' [v' [Hc [Hs1' _]]]].
    subst s1'.
    pose proof (decodeAndRegRead_core_frame core pcAddrInit fetchCapacity instCapacity
                  decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
                  mulDivMode config regions rev (Fst s1) c' v' Hc)
      as [Hrf [Hbp [Hmem Hrest]]].
    unfold SimDevices.implRf, SimDevices.implBp, SimDevices.implMem,
           SimDevices.implExecute, SimDevices.implDataMem, SimDevices.implMulDiv;
      cbn [writeSubTreeState writeSubTreeState_child readSubTreeState readSubTreeState_child implSysTree Impl.np_core Fst Snd].
    rewrite Hrf, Hbp, Hmem, Hrest.
    repeat split; reflexivity.
  Qed.

  Lemma SemAction_decodeAndRegReadStage_notCanProceed :
    forall (s1 s1' : IState) (v : bits 0),
      decode_canProceed core decodeCapacity (implDecode s1) = false ->
      SemAction
        (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      s1' = s1 /\ v = Zmod.zero.
  Proof.
    intros s1 s1' v Hcp Hsem.
    unfold decodeAndRegReadStage, decodeAndRegRead in Hsem.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply evalActionPropGen_LetAction in Hsem.
    apply (proj1 (evalActionPropGen_liftAction _ _ _ _)) in Hsem.
    apply (proj1 (evalActionPropGen_readDecodeCanProceed _ _ _ _)) in Hsem.
    eapply evalActionPropGen_IfElse_false in Hsem; [| exact Hcp].
    cbn [evalActionPropGen] in Hsem.
    rewrite !writeSubTreeState_readSubTreeState in Hsem.
    destruct Hsem as [<- <-]; split; reflexivity.
  Qed.

  Theorem sim_decodeAndRegReadStage_notCanProceed :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      decode_canProceed core decodeCapacity (implDecode s1) = false ->
      SemAction
        (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hcp Hsem Hrel.
    destruct (SemAction_decodeAndRegReadStage_notCanProceed s1 s1' v Hcp Hsem) as [-> _].
    exists s2; split; [apply spec_stutter | exact Hrel].
  Qed.

  Theorem sim_decodeAndRegReadStage :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      (FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1 s2 ->
       FenceIInv core pcAddrInit fetchCapacity instCapacity decodeCapacity
                 dataMemCapacity mulCapacity divCapacity mulStages divStages
                 mulDivMode config regions s1' s2) ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v Hsem Hfence Hrel.
    pose proof (decodeAndRegReadStage_frame s1 s1' v Hsem)
      as [Hrf [_ [Hmem [Hexec [Hdm Hmd]]]]].
    exists s2; split; [apply spec_stutter |].
    apply (stateRel_preserved_by_frontend_step s1 s1' s2 Hrel Hrf).
    - change (impl_mem core pcAddrInit fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages
                mulDivMode config regions) with implMem.
      rewrite Hmem; reflexivity.
    - exact Hexec.
    - exact Hdm.
    - exact Hmd.
    - exact Hfence.
  Qed.

  Theorem sim_fetchRps_stateRel :
    forall (act : Action type iTree (Bit 0))
           (s1 s1' : IState) (s2 : SState) (v : bits 0),
      In act
        (@fetchRps core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions type) ->
      SemAction act s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros act s1 s1' s2 v _ _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_fetchRqStage_stateRel :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@fetchRqStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_fetchAssembleStage_stateRel :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@fetchAssembleStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

  Theorem sim_decodeAndRegReadStage_stateRel :
    forall (s1 s1' : IState) (s2 : SState) (v : bits 0),
      SemAction
        (@decodeAndRegReadStage core pcAddrInit fetchCapacity instCapacity
           decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
           mulDivMode config regions rev type)
        s1 s1' v ->
      sRel s1 s2 ->
      exists s2' : SState,
        SemActions (map snd (specMod type)) s2 s2' /\
        sRel s1' s2'.
  Proof.
    intros s1 s1' s2 v _ Hrel.
    exists s2; split; [apply spec_stutter |].
    exact (stateRel_step_stutter core pcAddrInit fetchCapacity instCapacity
             decodeCapacity dataMemCapacity mulCapacity divCapacity mulStages divStages
             mulDivMode config regions s1 s1' s2 Hrel).
  Qed.

End FetchDecodeSystemSim.
