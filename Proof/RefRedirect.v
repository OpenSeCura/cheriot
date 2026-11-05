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
From Cheriot Require Import SpecDefines SpecDevice SpecFetchDeferred Impl.ImplDevice.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimExecute SimFetchDecode RefRel RefRegion RefGhost RefFetch
  RefMemRel RefCoreRel.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* ===========================================================================
 * EXECUTE'S LATCHED REDIRECT (item 3.4)
 * ===========================================================================
 * Execute records a redirect in `redirect` (execute tree); `applyRedirect`, first in every cycle,
 * applies it (fetchPc, execEpoch + 1, no straddle, fetch's PCC copy). The relation looks at the
 * state with a pending redirect already applied (`effS`): `applyP` does the part the relation
 * reads (fetchPc, straddle, execEpoch). `RedirInv` relates fetch's PCC and fence.i copies to the
 * architectural ones and keeps every frontend entry in the old epoch while a redirect is pending
 * (they are dead in the applied view). *)

Section Redirect.
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
  Local Abbreviation ACC f :=
    (f pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
       mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation RELG :=
    (RefRelG pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
             clintS clint plicS plic initLine fwcs).

  (* --- 1. Accessors --- *)

  Definition iRedirect (s1 : IState) : type (Option FullECapWithTag) := ex_redirect (ACC iExec s1).
  Definition iRedirValid (s1 : IState) : bool := ex_redirValid (ACC iExec s1).
  (* the redirect holds the new PCC = { tag; ecap; addr }; the target is its address *)
  Definition redirPcc (s1 : IState) : type FullECapWithTag := (iRedirect s1).(Fst).
  Definition redirTarget (s1 : IState) : type Addr := (redirPcc s1).(Snd).(Snd).(Fst).
  (* fetch = [ fetchPc; predEpoch; curParcelOpt; straddleOpt; canProceed; fetchBuf; instBuf;
   *          fetchPcc; fetchFenceIPending ] *)
  Definition iFetchPcc (s1 : IState) : type FullECapWithTag :=
    fetch_pccCopy pcAddrInit fetchCapacity instCapacity (ACC iFetch s1).
  Definition iFetchFip (s1 : IState) : bool :=
    fetch_fipCopy pcAddrInit fetchCapacity instCapacity (ACC iFetch s1).

  Definition nextEpoch (e : type Epoch) : type Epoch :=
    evalExpr (Add [ Var type Epoch e ; ($1 : Expr type Epoch) ]).

  (* the parts of a PCC fetch reads: tag and bounds *)
  Definition tagEcap (p : type FullECapWithTag) := (p.(Fst), p.(Snd).(Fst)).

  (* --- 2. The Applied View --- *)

  (* core = [ rf; waitBits; bp; mem; fetch; decode; execute; dataMem; mulDiv ] *)
  Definition applyP (s1 : IState) : IState :=
    let c := s1.(Fst) in
    ((c.(Fst) ,, (c.(Snd).(Fst) ,, (c.(Snd).(Snd).(Fst) ,, (c.(Snd).(Snd).(Snd).(Fst) ,,
      ((fetch_withPc pcAddrInit fetchCapacity instCapacity
          (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (ACC iFetch s1)
             (getDefault (Option StraddleHalf)))
          (redirTarget s1) ,, c.(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
      (c.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
      ((ex_withExecEpoch (ACC iExec s1) (nextEpoch (ACC iExecEpoch s1)) ,,
        c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd)) ,,
       c.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd)))))))) ,, s1.(Snd)).

  Definition effS (s1 : IState) : IState := if iRedirValid s1 then applyP s1 else s1.

  Lemma effS_false : forall s1, iRedirValid s1 = false -> effS s1 = s1.
  Proof. intros s1 H; unfold effS; rewrite H; reflexivity. Qed.

  Lemma effS_true : forall s1, iRedirValid s1 = true -> effS s1 = applyP s1.
  Proof. intros s1 H; unfold effS; rewrite H; reflexivity. Qed.

  (* What the applied view changes, and what it keeps *)
  Lemma applyP_rf : forall s1, ACC iRf (applyP s1) = ACC iRf s1.
  Proof. reflexivity. Qed.
  Lemma applyP_wb : forall s1, ACC iWb (applyP s1) = ACC iWb s1.
  Proof. reflexivity. Qed.
  Lemma applyP_mem : forall s1, ACC iMem (applyP s1) = ACC iMem s1.
  Proof. reflexivity. Qed.
  Lemma applyP_decode : forall s1, ACC iDecode (applyP s1) = ACC iDecode s1.
  Proof. reflexivity. Qed.
  Lemma applyP_dm : forall s1, ACC iDm (applyP s1) = ACC iDm s1.
  Proof. reflexivity. Qed.
  Lemma applyP_md :
    forall s1,
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions (applyP s1) =
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Proof. reflexivity. Qed.
  Lemma applyP_fetch :
    forall s1,
      ACC iFetch (applyP s1) =
      fetch_withPc pcAddrInit fetchCapacity instCapacity
        (fetch_withStraddleOpt pcAddrInit fetchCapacity instCapacity (ACC iFetch s1) (getDefault (Option StraddleHalf)))
        (redirTarget s1).
  Proof. reflexivity. Qed.
  Lemma applyP_exec :
    forall s1, ACC iExec (applyP s1) = ex_withExecEpoch (ACC iExec s1) (nextEpoch (ACC iExecEpoch s1)).
  Proof. reflexivity. Qed.
  Lemma applyP_epoch : forall s1, ACC iExecEpoch (applyP s1) = nextEpoch (ACC iExecEpoch s1).
  Proof. reflexivity. Qed.
  Lemma applyP_fip : forall s1, ACC iFenceIPending (applyP s1) = ACC iFenceIPending s1.
  Proof. reflexivity. Qed.
  Lemma applyP_redir : forall s1, iRedirect (applyP s1) = iRedirect s1.
  Proof. reflexivity. Qed.
  Lemma applyP_valid : forall s1, iRedirValid (applyP s1) = iRedirValid s1.
  Proof. reflexivity. Qed.

  Lemma effS_rf : forall s1, ACC iRf (effS s1) = ACC iRf s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_wb : forall s1, ACC iWb (effS s1) = ACC iWb s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_mem : forall s1, ACC iMem (effS s1) = ACC iMem s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_decode : forall s1, ACC iDecode (effS s1) = ACC iDecode s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_dm : forall s1, ACC iDm (effS s1) = ACC iDm s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_md :
    forall s1,
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions (effS s1) =
      impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_fip : forall s1, ACC iFenceIPending (effS s1) = ACC iFenceIPending s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1); reflexivity. Qed.
  Lemma effS_valid : forall s1, iRedirValid (effS s1) = iRedirValid s1.
  Proof. intros s1; unfold effS; destruct (iRedirValid s1) eqn:E; exact E. Qed.

  (* --- 3. The Invariant --- *)

  Definition RedirInv (s1 : IState) : Prop :=
    (iRedirValid s1 = false -> tagEcap (iFetchPcc s1) = tagEcap (ACC iPcc s1)) /\
    (iRedirValid s1 = false -> ACC iFenceIPending s1 = true -> iFetchFip s1 = true) /\
    (iRedirValid s1 = true ->
       tagEcap (redirPcc s1) = tagEcap (ACC iPcc s1) /\
       Forall (fun j => daExecEpoch j = ACC iExecEpoch s1) (ACC iD2a s1) /\
       Forall (fun a => aiExecEpoch a = ACC iExecEpoch s1) (ACC iInstBuf s1) /\
       Forall (fun f => fbExecEpoch f = ACC iExecEpoch s1) (ACC iFetchBuf s1)).

  Lemma RedirInv_frame :
    forall s s',
      iRedirValid s' = iRedirValid s -> tagEcap (iFetchPcc s') = tagEcap (iFetchPcc s) -> iFetchFip s' = iFetchFip s ->
      ACC iFenceIPending s' = ACC iFenceIPending s -> redirPcc s' = redirPcc s ->
      tagEcap (ACC iPcc s') = tagEcap (ACC iPcc s) -> ACC iExecEpoch s' = ACC iExecEpoch s ->
      ACC iD2a s' = ACC iD2a s -> ACC iInstBuf s' = ACC iInstBuf s -> ACC iFetchBuf s' = ACC iFetchBuf s ->
      RedirInv s -> RedirInv s'.
  Proof.
    intros s s' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 H; unfold RedirInv in *.
    rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10; exact H.
  Qed.

  Lemma RedirInv_np_of :
    forall s,
      iRedirValid s = false -> tagEcap (iFetchPcc s) = tagEcap (ACC iPcc s) ->
      (ACC iFenceIPending s = true -> iFetchFip s = true) -> RedirInv s.
  Proof.
    intros s Hv H1 H2; unfold RedirInv; rewrite Hv.
    split; [intros _; exact H1 | split; [intros _; exact H2 | intros C; discriminate C]].
  Qed.

  Lemma RedirInv_p_of :
    forall s,
      iRedirValid s = true -> tagEcap (redirPcc s) = tagEcap (ACC iPcc s) ->
      Forall (fun j => daExecEpoch j = ACC iExecEpoch s) (ACC iD2a s) ->
      Forall (fun a => aiExecEpoch a = ACC iExecEpoch s) (ACC iInstBuf s) ->
      Forall (fun f => fbExecEpoch f = ACC iExecEpoch s) (ACC iFetchBuf s) ->
      RedirInv s.
  Proof.
    intros s Hv H1 H2 H3 H4; unfold RedirInv; rewrite Hv.
    split; [intros C; discriminate C | split; [intros C; discriminate C | intros _]].
    exact (conj H1 (conj H2 (conj H3 H4))).
  Qed.

  (* --- 4. The Relation --- *)

  Definition RefRelR (s1 : IState) (s2 : SState) : Prop :=
    RedirInv s1 /\ exists g, RELG g (effS s1) s2.

End Redirect.
