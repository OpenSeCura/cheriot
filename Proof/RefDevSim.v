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
From Cheriot Require Import SpecDefines SpecDevice Clint Plic SpecRevoker Impl.ImplRevoker.
From Cheriot.Proof Require Import TreeLemmas StateRel RefRel RefMemRel.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the devices' line actions on related states: an impl run of a device's line read
 * or write is matched by a spec run that keeps the device relation (CLINT: `ClintRel`; PLIC:
 * `PlicRelSame`; revoker: the arch registers). *)

(* --- 1. The CLINT --- *)

Section ClintSim.
  Variable base : Z.
  Local Abbreviation CS := (TS (Node "clint" clintChildren)).

  Lemma clintWrite_sim :
    forall env1 env2 (xs xi xi' : CS) addr data mask v,
      ClintRel xs xi ->
      SemAction env1 (@clintLineWriteAction base type addr data mask) xi xi' v ->
      exists xs', SemAction env2 (@clintLineWriteAction base type addr data mask) xs xs' v /\
        ClintRel xs' xi' /\ (clintSampled xs' = true -> clintSampled xs = true) /\
        (ClintInv xi -> ClintInv xi').
  Proof.
    intros env1 env2 xs xi xi' addr data mask v [E1 E2] H.
    rewrite SemAction_iff_evalActionPropGen in H.
    destruct xi as [mt [mc [mp [sp []]]]].
    unfold clintWithSampled, clintSampled in E1; cbn [Fst Snd] in E1.
    set (s := xs.(Snd).(Snd).(Snd).(Fst)) in E1.
    unfold clintLineWriteAction in H; cbn -[evalExpr] in H.
    rewrite E1; clear E1.
    unfold clintSampled in E2; cbn [Fst Snd] in E2; fold s in E2.
    repeat match type of H with context [if ?c then _ else _] => let E := fresh "Ec" in destruct c eqn:E end;
    destruct H as [<- <-];
    eexists; rewrite SemAction_iff_evalActionPropGen;
    unfold clintLineWriteAction; cbn -[evalExpr];
    repeat match goal with E : ?c = ?b |- context [if ?c then _ else _] => rewrite E end;
    (split; [split; reflexivity |]);
    unfold ClintRel, ClintInv, clintWithSampled, clintSampled, clintMtip; cbn [Fst Snd];
    (split; [split; [reflexivity | first [exact E2 | intros Hf; exact Hf]] |]);
    split; first [intros Hf; exact Hf | intros Hf; discriminate Hf | intros Hi Hf; exact (Hi Hf)
                 | intros _ Hf; exact Hf].
  Qed.

  Lemma clintRead_sim :
    forall env1 env2 (xs xi xi' : CS) addr mask v,
      ClintRel xs xi ->
      SemAction env1 (@clintLineReadAction base type addr mask) xi xi' v ->
      xi' = xi /\ SemAction env2 (@clintLineReadAction base type addr mask) xs xs v.
  Proof.
    intros env1 env2 xs xi xi' addr mask v [E1 E2] H.
    rewrite SemAction_iff_evalActionPropGen in H.
    destruct xi as [mt [mc [mp [sp []]]]].
    unfold clintWithSampled, clintSampled in E1; cbn [Fst Snd] in E1.
    unfold clintLineReadAction in H; cbn -[evalExpr] in H.
    destruct H as [<- <-]; split; [reflexivity |].
    rewrite E1, SemAction_iff_evalActionPropGen.
    unfold clintLineReadAction; cbn -[evalExpr].
    split; reflexivity.
  Qed.
End ClintSim.

(* --- 2. Simulation of Two Actions, Constructor by Constructor --- *)

(* `SimA a1 a2`: from related states, every run of `a1` is matched by a run of `a2` that ends in
 * related states with the same value. Proven by one lemma per constructor, so that sequential
 * `If`s are not unfolded into a tree of paths. *)
Section SimA.
  Variables t1 t2 : Tree Elem.
  Variable R : TS t1 -> TS t2 -> Prop.
  Variable env1 : Env t1.
  Variable env2 : Env t2.

  Definition SimAt {k} (s1 : TS t1) (s2 : TS t2) (a1 : Action type t1 k) (a2 : Action type t2 k) : Prop :=
    forall P1 P2, (forall s1' s2' v, R s1' s2' -> P1 s1' v -> P2 s2' v) ->
      evalActionPropGen env1 a1 s1 P1 -> evalActionPropGen env2 a2 s2 P2.

  Definition SimA {k} (a1 : Action type t1 k) (a2 : Action type t2 k) : Prop :=
    forall s1 s2, R s1 s2 -> SimAt s1 s2 a1 a2.

  Lemma simAt_of : forall k s1 s2 (a1 : Action type t1 k) a2, R s1 s2 -> SimA a1 a2 -> SimAt s1 s2 a1 a2.
  Proof. intros k s1 s2 a1 a2 HR H; exact (H s1 s2 HR). Qed.

  Lemma sim_return : forall k (e1 e2 : Expr type k), evalExpr e1 = evalExpr e2 -> SimA (Return e1) (Return e2).
  Proof. intros k e1 e2 E s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *; rewrite <- E; exact (HP _ _ _ HR H). Qed.

  Lemma sim_letExp :
    forall k k' n1 n2 (e1 e2 : Expr type k') (c1 : type k' -> Action type t1 k) c2,
      evalExpr e1 = evalExpr e2 -> (forall v, SimA (c1 v) (c2 v)) -> SimA (LetExp n1 e1 c1) (LetExp n2 e2 c2).
  Proof. intros k k' n1 n2 e1 e2 c1 c2 E Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *; rewrite <- E; exact (Hc _ _ _ HR _ _ HP H). Qed.

  Lemma simAt_letExp :
    forall k k' s1 s2 n1 n2 (e1 e2 : Expr type k') (c1 : type k' -> Action type t1 k) c2,
      SimAt s1 s2 (c1 (evalExpr e1)) (c2 (evalExpr e2)) -> SimAt s1 s2 (LetExp n1 e1 c1) (LetExp n2 e2 c2).
  Proof. intros k k' s1 s2 n1 n2 e1 e2 c1 c2 Hc P1 P2 HP H; exact (Hc _ _ HP H). Qed.

  Lemma sim_letAction :
    forall k k' n1 n2 (a1 : Action type t1 k') (a2 : Action type t2 k') (c1 : type k' -> Action type t1 k) c2,
      SimA a1 a2 -> (forall v, SimA (c1 v) (c2 v)) -> SimA (LetAction n1 a1 c1) (LetAction n2 a2 c2).
  Proof.
    intros k k' n1 n2 a1 a2 c1 c2 Ha Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *.
    apply (Ha _ _ HR _ _ (fun s1' s2' v HR' H' => Hc v _ _ HR' _ _ HP H') H).
  Qed.

  Lemma sim_ifElse :
    forall k k' n1 n2 (c1 c2 : Expr type Bool) (a1 b1 : Action type t1 k') (a2 b2 : Action type t2 k')
           (k1 : type k' -> Action type t1 k) k2,
      evalExpr c1 = evalExpr c2 -> SimA a1 a2 -> SimA b1 b2 -> (forall v, SimA (k1 v) (k2 v)) ->
      SimA (IfElse n1 c1 a1 b1 k1) (IfElse n2 c2 a2 b2 k2).
  Proof.
    intros k k' n1 n2 c1 c2 a1 b1 a2 b2 k1 k2 E Ha Hb Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *.
    rewrite <- E; destruct (evalExpr c1).
    - apply (Ha _ _ HR _ _ (fun s1' s2' v HR' H' => Hc v _ _ HR' _ _ HP H') H).
    - apply (Hb _ _ HR _ _ (fun s1' s2' v HR' H' => Hc v _ _ HR' _ _ HP H') H).
  Qed.

  Lemma sim_writeReg :
    forall k (p1 : RegPath t1) (p2 : RegPath t2) v1 v2 (c1 : Action type t1 k) c2,
      (forall s1 s2, R s1 s2 ->
         R (writeTreeState t1 s1 p1.(regPath) (castStateRegInv p1 (evalExpr v1)))
           (writeTreeState t2 s2 p2.(regPath) (castStateRegInv p2 (evalExpr v2)))) ->
      SimA c1 c2 -> SimA (WriteReg p1 v1 c1) (WriteReg p2 v2 c2).
  Proof. intros k p1 p2 v1 v2 c1 c2 Hw Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *; exact (Hc _ _ (Hw _ _ HR) _ _ HP H). Qed.

  Lemma simAt_readReg :
    forall k s1 s2 n1 n2 (p1 : RegPath t1) (p2 : RegPath t2) (c1 : _ -> Action type t1 k) (c2 : _ -> Action type t2 k),
      SimAt s1 s2 (c1 (castStateReg p1 (readTreeState t1 s1 p1.(regPath))))
                  (c2 (castStateReg p2 (readTreeState t2 s2 p2.(regPath)))) ->
      SimAt s1 s2 (ReadReg n1 p1 c1) (ReadReg n2 p2 c2).
  Proof. intros k s1 s2 n1 n2 p1 p2 c1 c2 Hc P1 P2 HP H; exact (Hc _ _ HP H). Qed.

  (* The remaining constructors: the states after the step are those of `evalActionPropGen` *)
  Lemma simAt_readRqMem :
    forall k (s1 : TS t1) (s2 : TS t2) (x1 : MemPath t1) (x2 : MemPath t2)
           (i1 : Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x1).(memSize)))))
           (i2 : Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x2).(memSize)))))
           (p1 : FinType (getMemFromPath x1).(memPort)) (p2 : FinType (getMemFromPath x2).(memPort))
           (c1 : Action type t1 k) (c2 : Action type t2 k),
      SimAt (let arr := castStateMem x1 (readTreeState t1 s1 x1.(memPath)) in
             writeTreeState t1 s1 x1.(memPath)
               (castStateMemInv x1 (arr.(Fst) ,, updSameTuple arr.(Snd) p1
                  (nth (Z.to_nat (Zmod.to_Z (evalExpr i1))) arr.(Fst).(tupleElems) (getDefault _)))))
            (let arr := castStateMem x2 (readTreeState t2 s2 x2.(memPath)) in
             writeTreeState t2 s2 x2.(memPath)
               (castStateMemInv x2 (arr.(Fst) ,, updSameTuple arr.(Snd) p2
                  (nth (Z.to_nat (Zmod.to_Z (evalExpr i2))) arr.(Fst).(tupleElems) (getDefault _)))))
            c1 c2 ->
      SimAt s1 s2 (ReadRqMem x1 i1 p1 c1) (ReadRqMem x2 i2 p2 c2).
  Proof. intros k s1 s2 x1 x2 i1 i2 p1 p2 c1 c2 Hc P1 P2 HP H; exact (Hc _ _ HP H). Qed.

  Lemma simAt_readRpMem :
    forall k (s1 : TS t1) (s2 : TS t2) n1 n2 (x1 : MemPath t1) (x2 : MemPath t2)
           (p1 : FinType (getMemFromPath x1).(memPort)) (p2 : FinType (getMemFromPath x2).(memPort))
           (c1 : _ -> Action type t1 k) (c2 : _ -> Action type t2 k),
      SimAt s1 s2 (c1 (readSameTuple (castStateMem x1 (readTreeState t1 s1 x1.(memPath))).(Snd) p1))
                  (c2 (readSameTuple (castStateMem x2 (readTreeState t2 s2 x2.(memPath))).(Snd) p2)) ->
      SimAt s1 s2 (ReadRpMem n1 x1 p1 c1) (ReadRpMem n2 x2 p2 c2).
  Proof. intros k s1 s2 n1 n2 x1 x2 p1 p2 c1 c2 Hc P1 P2 HP H; exact (Hc _ _ HP H). Qed.

  Lemma simAt_writeMem :
    forall k (s1 : TS t1) (s2 : TS t2) (x1 : MemPath t1) (x2 : MemPath t2)
           (i1 : Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x1).(memSize)))))
           (i2 : Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x2).(memSize)))))
           (v1 : Expr type (getMemFromPath x1).(memKind)) (v2 : Expr type (getMemFromPath x2).(memKind))
           (c1 : Action type t1 k) (c2 : Action type t2 k),
      SimAt (let arr := castStateMem x1 (readTreeState t1 s1 x1.(memPath)) in
             writeTreeState t1 s1 x1.(memPath)
               (castStateMemInv x1 (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i1))) (evalExpr v1) ,, arr.(Snd))))
            (let arr := castStateMem x2 (readTreeState t2 s2 x2.(memPath)) in
             writeTreeState t2 s2 x2.(memPath)
               (castStateMemInv x2 (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i2))) (evalExpr v2) ,, arr.(Snd))))
            c1 c2 ->
      SimAt s1 s2 (WriteMem x1 i1 v1 c1) (WriteMem x2 i2 v2 c2).
  Proof. intros k s1 s2 x1 x2 i1 i2 v1 v2 c1 c2 Hc P1 P2 HP H; exact (Hc _ _ HP H). Qed.

  Lemma simAt_send :
    forall k (s1 : TS t1) (s2 : TS t2) (x1 : SendPath t1) (x2 : SendPath t2)
           (v1 : Expr type (getSendKind x1)) (v2 : Expr type (getSendKind x2))
           (c1 : Action type t1 k) (c2 : Action type t2 k),
      SimAt (writeTreeState t1 s1 x1.(sendPath)
               (castStateSendInv x1 (evalExpr v1 :: castStateSend x1 (readTreeState t1 s1 x1.(sendPath)))))
            (writeTreeState t2 s2 x2.(sendPath)
               (castStateSendInv x2 (evalExpr v2 :: castStateSend x2 (readTreeState t2 s2 x2.(sendPath)))))
            c1 c2 ->
      SimAt s1 s2 (Send x1 v1 c1) (Send x2 v2 c2).
  Proof. intros k s1 s2 x1 x2 v1 v2 c1 c2 Hc P1 P2 HP H; exact (Hc _ _ HP H). Qed.

  (* Every value the first env delivers is matched by one the second env accepts *)
  Lemma simAt_recv :
    forall k (s1 : TS t1) (s2 : TS t2) n1 n2 (x1 : RecvPath t1) (x2 : RecvPath t2)
           (c1 : type (getRecvKind x1) -> Action type t1 k) (c2 : type (getRecvKind x2) -> Action type t2 k),
      (forall r1, env1 s1 x1 r1 -> exists r2, env2 s2 x2 r2 /\
         SimAt (writeTreeState t1 s1 x1.(recvPath)
                  (castStateRecvInv x1 (r1 :: castStateRecv x1 (readTreeState t1 s1 x1.(recvPath)))))
               (writeTreeState t2 s2 x2.(recvPath)
                  (castStateRecvInv x2 (r2 :: castStateRecv x2 (readTreeState t2 s2 x2.(recvPath)))))
               (c1 r1) (c2 r2)) ->
      SimAt s1 s2 (Recv n1 x1 c1) (Recv n2 x2 c2).
  Proof.
    intros k s1 s2 n1 n2 x1 x2 c1 c2 Hc P1 P2 HP H; cbn [evalActionPropGen] in *.
    destruct H as [r1 [He1 H]]; destruct (Hc r1 He1) as [r2 [He2 Hs]].
    exists r2; split; [exact He2 | exact (Hs _ _ HP H)].
  Qed.

  Lemma simAt_nonDet :
    forall k k1 k2 (s1 : TS t1) (s2 : TS t2) n1 n2 (c1 : type k1 -> Action type t1 k) (c2 : type k2 -> Action type t2 k),
      (forall v1, exists v2, SimAt s1 s2 (c1 v1) (c2 v2)) ->
      SimAt s1 s2 (NonDet n1 k1 c1) (NonDet n2 k2 c2).
  Proof.
    intros k k1 k2 s1 s2 n1 n2 c1 c2 Hc P1 P2 HP H; cbn [evalActionPropGen] in *.
    destruct H as [v1 H]; destruct (Hc v1) as [v2 Hs].
    exists v2; exact (Hs _ _ HP H).
  Qed.

  Lemma sim_system :
    forall k ls1 ls2 (c1 : Action type t1 k) (c2 : Action type t2 k),
      SimA c1 c2 -> SimA (System ls1 c1) (System ls2 c2).
  Proof. intros k ls1 ls2 c1 c2 Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *; exact (Hc _ _ HR _ _ HP H). Qed.
End SimA.

(* --- 2. The Revoker's Registers --- *)

Lemma ev_let_inv :
  forall t k k' (env : Env t) s (e : Expr type k') (cont : type k' -> Action type t k) old P,
    evalActionPropGen env (LetExp s e cont) old P -> evalActionPropGen env (cont (evalExpr e)) old P.
Proof. intros t k k' env s e cont old P H; exact H. Qed.

Lemma ev_let_fwd :
  forall t k k' (env : Env t) s (e : Expr type k') (cont : type k' -> Action type t k) old P,
    evalActionPropGen env (cont (evalExpr e)) old P -> evalActionPropGen env (LetExp s e cont) old P.
Proof. intros t k k' env s e cont old P H; exact H. Qed.

Section RevSim.
  Variable base : Z.
  Local Abbreviation RI := (TS implRevokerTree).

  (* The impl-only registers of the revoker *)
  Definition revExtraOf (x : RI) := x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).

  (* The registers software cannot write: epoch, scanAddr, sweepTop *)
  Definition revKeyOf (x : RI) := (x.(Snd).(Snd).(Snd).(Fst), (x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst),
                                   x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst))).

  (* The spec revoker registers are the impl's arch part; the impl-only registers stay `E`, the
   * registers software cannot write stay `K` *)
  Definition RevArchR (E : TS (Node "" implRevokerExtraChildren)) K (xi : RI) (xs : TS (Node "revoker" (revokerChildren []))) : Prop :=
    xs = projImplRevokerArchState xi /\ revExtraOf xi = E /\ revKeyOf xi = K.

  Lemma revMmioWrite_sim :
    forall env1 env2 (xi xi' : RI) addr data mask v,
      SemAction env1 (@revokerLineWriteAction implRevokerExtraChildren base type addr data mask) xi xi' v ->
      SemAction env2 (@revokerLineWriteAction [] base type addr data mask)
        (projImplRevokerArchState xi) (projImplRevokerArchState xi') v /\
      revExtraOf xi' = revExtraOf xi /\ revKeyOf xi' = revKeyOf xi.
  Proof.
    intros env1 env2 xi xi' addr data mask v H.
    rewrite SemAction_iff_evalActionPropGen in H.
    assert (HS : SimAt _ _ (RevArchR (revExtraOf xi) (revKeyOf xi)) env1 env2 xi (projImplRevokerArchState xi)
                   (@revokerLineWriteAction implRevokerExtraChildren base type addr data mask)
                   (@revokerLineWriteAction [] base type addr data mask)).
    { destruct xi as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
      unfold revokerLineWriteAction, readRevokerLine.
      apply simAt_letExp.
      do 6 (apply simAt_readReg; cbv beta).
      apply simAt_letExp; apply simAt_letExp.
      apply simAt_of; [split; [reflexivity | split; reflexivity] |].
      Ltac rev_wr := intros s1 s2 [-> [HE HK]];
        split; [reflexivity | split; [exact HE | exact HK]].
      repeat first
        [ apply sim_letExp; [reflexivity | intros ?]
        | apply sim_letAction; [| intros ?]
        | apply sim_ifElse; [reflexivity | | | intros ?]
        | apply sim_writeReg; [rev_wr |]
        | apply sim_return; reflexivity ]. }
    assert (HP : forall s1' s2' r, RevArchR (revExtraOf xi) (revKeyOf xi) s1' s2' -> (s1' = xi' /\ r = v) ->
                   (s2' = projImplRevokerArchState xi' /\ r = v /\ revExtraOf xi' = revExtraOf xi /\
                    revKeyOf xi' = revKeyOf xi)).
    { intros s1' s2' r [E1 [E2 E5]] [E3 E4]; subst; split; [reflexivity | split; [reflexivity | split; [exact E2 | exact E5]]]. }
    pose proof (HS _ _ HP H) as H2.
    destruct (evalActionPropGen_to_SemAction _ _ _ H2) as [s2 [r [Hs [-> [-> [E EK]]]]]].
    split; [exact Hs | split; [exact E | exact EK]].
  Qed.

  Lemma revMmioRead_sim :
    forall env1 env2 (xi xi' : RI) addr mask v,
      SemAction env1 (@revokerLineReadAction implRevokerExtraChildren base type addr mask) xi xi' v ->
      xi' = xi /\
      SemAction env2 (@revokerLineReadAction [] base type addr mask)
        (projImplRevokerArchState xi) (projImplRevokerArchState xi) v.
  Proof.
    intros env1 env2 xi xi' addr mask v H.
    rewrite SemAction_iff_evalActionPropGen in H.
    destruct xi as [b [t [c [e [ist [ir [sa [st [ph [sc [sb [sh []]]]]]]]]]]]].
    unfold revokerLineReadAction, readRevokerLine in H;
      cbn -[evalExpr getMemOffset lineOffsetOf slotOf byteOf ArrayBuilder] in H.
    destruct H as [<- <-]; split; [reflexivity |].
    rewrite SemAction_iff_evalActionPropGen.
    unfold revokerLineReadAction, readRevokerLine, projImplRevokerArchState;
      cbn -[evalExpr getMemOffset lineOffsetOf slotOf byteOf ArrayBuilder].
    split; reflexivity.
  Qed.
End RevSim.

(* --- 4. The PLIC --- *)

Section SimS.
  Variable t : Tree Elem.
  Variable R : TS t -> TS t -> Prop.
  Variables env1 env2 : Env t.
  Local Abbreviation SimS a := (SimA t t R env1 env2 a a).

  Lemma simS_return : forall k (e : Expr type k), SimS (Return e).
  Proof. intros; apply sim_return; reflexivity. Qed.

  Lemma simS_letExp : forall k k' n (e : Expr type k') (c : type k' -> Action type t k),
      (forall v, SimS (c v)) -> SimS (LetExp n e c).
  Proof. intros; apply sim_letExp; [reflexivity | assumption]. Qed.

  Lemma simS_letAction : forall k k' n (a : Action type t k') (c : type k' -> Action type t k),
      SimS a -> (forall v, SimS (c v)) -> SimS (LetAction n a c).
  Proof. intros; apply sim_letAction; assumption. Qed.

  Lemma simS_ifElse : forall k k' n (c : Expr type Bool) (a b : Action type t k') (kc : type k' -> Action type t k),
      SimS a -> SimS b -> (forall v, SimS (kc v)) -> SimS (IfElse n c a b kc).
  Proof. intros; apply sim_ifElse; [reflexivity | assumption ..]. Qed.

  Lemma simS_writeReg : forall k (p : RegPath t) e (c : Action type t k),
      (forall s1 s2 v, R s1 s2 -> R (writeTreeState t s1 p.(regPath) v) (writeTreeState t s2 p.(regPath) v)) ->
      SimS c -> SimS (WriteReg p e c).
  Proof. intros k p e c Hw Hc; apply sim_writeReg; [intros s1 s2 HR; apply Hw; exact HR | exact Hc]. Qed.

  Lemma simS_readReg : forall k n (p : RegPath t) (c : _ -> Action type t k),
      (forall s1 s2, R s1 s2 -> readTreeState t s1 p.(regPath) = readTreeState t s2 p.(regPath)) ->
      (forall v, SimS (c v)) -> SimS (ReadReg n p c).
  Proof.
    intros k n p c Hr Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *.
    rewrite <- (Hr _ _ HR); exact (Hc _ _ _ HR _ _ HP H).
  Qed.

  (* The remaining constructors. A leaf that is read and then written (memories, traces) needs
   * equal reads and `R` kept by equal writes. *)
  Lemma simS_readRqMem : forall k (x : MemPath t) i p (c : Action type t k),
      (forall s1 s2, R s1 s2 -> readTreeState t s1 x.(memPath) = readTreeState t s2 x.(memPath)) ->
      (forall s1 s2 w, R s1 s2 -> R (writeTreeState t s1 x.(memPath) w) (writeTreeState t s2 x.(memPath) w)) ->
      SimS c -> SimS (ReadRqMem x i p c).
  Proof.
    intros k x i p c Hr Hw Hc s1 s2 HR; apply simAt_readRqMem; cbv zeta.
    rewrite (Hr _ _ HR); apply simAt_of; [apply Hw; exact HR | exact Hc].
  Qed.

  Lemma simS_readRpMem : forall k n (x : MemPath t) p (c : _ -> Action type t k),
      (forall s1 s2, R s1 s2 -> readTreeState t s1 x.(memPath) = readTreeState t s2 x.(memPath)) ->
      (forall v, SimS (c v)) -> SimS (ReadRpMem n x p c).
  Proof.
    intros k n x p c Hr Hc s1 s2 HR; apply simAt_readRpMem.
    rewrite (Hr _ _ HR); apply simAt_of; [exact HR | apply Hc].
  Qed.

  Lemma simS_writeMem : forall k (x : MemPath t) i v (c : Action type t k),
      (forall s1 s2, R s1 s2 -> readTreeState t s1 x.(memPath) = readTreeState t s2 x.(memPath)) ->
      (forall s1 s2 w, R s1 s2 -> R (writeTreeState t s1 x.(memPath) w) (writeTreeState t s2 x.(memPath) w)) ->
      SimS c -> SimS (WriteMem x i v c).
  Proof.
    intros k x i v c Hr Hw Hc s1 s2 HR; apply simAt_writeMem; cbv zeta.
    rewrite (Hr _ _ HR); apply simAt_of; [apply Hw; exact HR | exact Hc].
  Qed.

  Lemma simS_send : forall k (x : SendPath t) v (c : Action type t k),
      (forall s1 s2, R s1 s2 -> readTreeState t s1 x.(sendPath) = readTreeState t s2 x.(sendPath)) ->
      (forall s1 s2 w, R s1 s2 -> R (writeTreeState t s1 x.(sendPath) w) (writeTreeState t s2 x.(sendPath) w)) ->
      SimS c -> SimS (Send x v c).
  Proof.
    intros k x v c Hr Hw Hc s1 s2 HR; apply simAt_send.
    rewrite (Hr _ _ HR); apply simAt_of; [apply Hw; exact HR | exact Hc].
  Qed.

  Lemma simS_recv : forall k n (x : RecvPath t) (c : _ -> Action type t k),
      (forall s1 s2 r, R s1 s2 -> env1 s1 x r -> env2 s2 x r) ->
      (forall s1 s2, R s1 s2 -> readTreeState t s1 x.(recvPath) = readTreeState t s2 x.(recvPath)) ->
      (forall s1 s2 w, R s1 s2 -> R (writeTreeState t s1 x.(recvPath) w) (writeTreeState t s2 x.(recvPath) w)) ->
      (forall r, SimS (c r)) -> SimS (Recv n x c).
  Proof.
    intros k n x c He Hr Hw Hc s1 s2 HR; apply simAt_recv; intros r He1.
    exists r; split; [exact (He _ _ _ HR He1) |].
    rewrite (Hr _ _ HR); apply simAt_of; [apply Hw; exact HR | apply Hc].
  Qed.

  Lemma simS_nonDet : forall k k' n (c : type k' -> Action type t k),
      (forall v, SimS (c v)) -> SimS (NonDet n k' c).
  Proof.
    intros k k' n c Hc s1 s2 HR; apply simAt_nonDet; intros v.
    exists v; apply simAt_of; [exact HR | apply Hc].
  Qed.

  Lemma simS_system : forall k ls (c : Action type t k), SimS c -> SimS (System ls c).
  Proof. intros; apply sim_system; assumption. Qed.

  Lemma simS_writeRegsListHelper :
    forall k sz (paths : list (RegOfKind (t := t) k)) curr (idx : Expr type (Bit sz)) v,
      (forall rk, In rk paths -> forall s1 s2 w, R s1 s2 ->
         R (writeTreeState t s1 rk.(rk_path).(regPath) w) (writeTreeState t s2 rk.(rk_path).(regPath) w)) ->
      SimS (@writeRegsListHelper type curr k sz t paths idx v).
  Proof.
    intros k sz paths; induction paths as [| rk rest IH]; intros curr idx v Hw; cbn [writeRegsListHelper].
    - apply simS_return.
    - apply simS_ifElse.
      + apply simS_writeReg; [intros s1 s2 w; apply (Hw rk (or_introl eq_refl)) | apply simS_return].
      + apply simS_return.
      + intros _; apply IH; intros rk' Hin; apply Hw; right; exact Hin.
  Qed.
End SimS.

Section PlicSim.
  Variable n : nat.
  Variable base : Z.
  Local Abbreviation PS := (TS (plicTree n)).

  (* The spec PLIC lags in meip, and its meip only falls; the impl keeps its invariant *)
  Definition PlicR (xs0 : PS) (xi0 : PS) (xi xs : PS) : Prop :=
    PlicRelSame n xs xi /\ (plicMeipOf xs = true -> plicMeipOf xs0 = true) /\ (PlicInv xi0 -> PlicInv xi).

  Lemma PlicR_frame :
    forall xs0 xi0 (f : PS -> PS),
      (forall b x, f (plicWithMeip b x) = plicWithMeip b (f x)) -> (forall x, plicMeipOf (f x) = plicMeipOf x) ->
      (forall x, plicClaimOf (f x) = plicClaimOf x) ->
      forall xi xs, PlicR xs0 xi0 xi xs -> PlicR xs0 xi0 (f xi) (f xs).
  Proof.
    intros xs0 xi0 f Hc Hm Hcl xi xs [[E1 E2] [E3 E4]].
    split; [split |]; [| | split].
    - rewrite E1 at 1; rewrite Hc, Hm; f_equal; rewrite <- Hm, <- E1; reflexivity.
    - rewrite !Hm; exact E2.
    - rewrite Hm; exact E3.
    - intros Hi; unfold PlicInv in *; rewrite Hm, Hcl; exact (E4 Hi).
  Qed.

  (* Registers other than meip *)
  Definition NotMeip (p : RegPath (plicTree n)) : Prop :=
    (forall b (x : PS), readTreeState (plicTree n) (plicWithMeip b x) p.(regPath) = readTreeState (plicTree n) x p.(regPath)) /\
    (forall b (x : PS) w, writeTreeState (plicTree n) (plicWithMeip b x) p.(regPath) w =
                         plicWithMeip b (writeTreeState (plicTree n) x p.(regPath) w)) /\
    (forall (x : PS) w, plicMeipOf (writeTreeState (plicTree n) x p.(regPath) w) = plicMeipOf x).

  Definition NotMeipClaim (p : RegPath (plicTree n)) : Prop :=
    NotMeip p /\ (forall (x : PS) w, plicClaimOf (writeTreeState (plicTree n) x p.(regPath) w) = plicClaimOf x).

  Ltac nm_tac := split; [| split]; intros; reflexivity.

  Lemma NotMeipClaim_prio : forall rk, In rk (priorityPathsWithKind n) -> NotMeipClaim rk.(rk_path).
  Proof. intros rk Hin; unfold priorityPathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; split; [nm_tac | reflexivity]. Qed.
  Lemma NotMeipClaim_pend : forall rk, In rk (pendingPathsWithKind n) -> NotMeipClaim rk.(rk_path).
  Proof. intros rk Hin; unfold pendingPathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; split; [nm_tac | reflexivity]. Qed.
  Lemma NotMeipClaim_en : forall rk, In rk (enablesPathsWithKind n) -> NotMeipClaim rk.(rk_path).
  Proof. intros rk Hin; unfold enablesPathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; split; [nm_tac | reflexivity]. Qed.
  Lemma NotMeipClaim_insv : forall rk, In rk (inServicePathsWithKind n) -> NotMeipClaim rk.(rk_path).
  Proof. intros rk Hin; unfold inServicePathsWithKind in Hin; apply in_map_iff in Hin as [rk0 [<- _]]; split; [nm_tac | reflexivity]. Qed.
  Lemma NotMeipClaim_thresh : NotMeipClaim (plicThresholdPath n).
  Proof. split; [nm_tac | reflexivity]. Qed.
  Lemma NotMeip_claim : NotMeip (plicClaimPath n).
  Proof. nm_tac. Qed.

  Section Rel.
    Variables xs0 xi0 : PS.
    Variables env1 env2 : Env (plicTree n).
    Local Abbreviation RR := (PlicR xs0 xi0).
    Local Abbreviation SimS a := (SimA (plicTree n) (plicTree n) RR env1 env2 a a).

    Lemma PlicR_read :
      forall p, NotMeip p -> forall s1 s2, RR s1 s2 ->
        readTreeState (plicTree n) s1 p.(regPath) = readTreeState (plicTree n) s2 p.(regPath).
    Proof. intros p [Hr _] s1 s2 [[E1 _] _]; rewrite E1, Hr; reflexivity. Qed.

    Lemma PlicR_write :
      forall p, NotMeipClaim p -> forall s1 s2 w, RR s1 s2 ->
        RR (writeTreeState (plicTree n) s1 p.(regPath) w) (writeTreeState (plicTree n) s2 p.(regPath) w).
    Proof.
      intros p [[_ [Hw Hm]] Hc] s1 s2 w HR.
      exact (PlicR_frame xs0 xi0 (fun x => writeTreeState (plicTree n) x p.(regPath) w)
               (fun b x => Hw b x w) (fun x => Hm x w) (fun x => Hc x w) s1 s2 HR).
    Qed.

    Lemma simS_readRegs :
      forall k ans (paths : list (RegOfKind (t := plicTree n) k)) (kc : list (type k) -> Action type (plicTree n) ans),
        (forall rk, In rk paths -> NotMeip rk.(rk_path)) -> (forall vs, SimS (kc vs)) ->
        SimS (@readRegs n type k paths ans kc).
    Proof.
      intros k ans paths; induction paths as [| rk rest IH]; intros kc Hp Hk; cbn [readRegs]; [apply Hk |].
      apply simS_readReg; [exact (PlicR_read _ (Hp rk (or_introl eq_refl))) |].
      intros v; apply IH; [intros rk' Hin; apply Hp; right; exact Hin | intros vs; apply Hk].
    Qed.

    Lemma simS_readAllSources :
      forall ans prios pends insvs
             (kc : list (type (Bit Xlen)) -> list (type Bool) -> list (type Bool) -> Action type (plicTree n) ans),
        (forall rk, In rk prios -> NotMeip rk.(rk_path)) -> (forall rk, In rk pends -> NotMeip rk.(rk_path)) ->
        (forall rk, In rk insvs -> NotMeip rk.(rk_path)) -> (forall a b c, SimS (kc a b c)) ->
        SimS (@readAllSources n type prios pends insvs ans kc).
    Proof.
      intros ans prios; induction prios as [| rp rps IH]; intros [| rd rds] [| ri ris] kc Hp Hd Hi Hk;
        cbn [readAllSources]; try apply Hk.
      apply simS_readReg; [exact (PlicR_read _ (Hp rp (or_introl eq_refl))) | intros v1].
      apply simS_readReg; [exact (PlicR_read _ (Hd rd (or_introl eq_refl))) | intros v2].
      apply simS_readReg; [exact (PlicR_read _ (Hi ri (or_introl eq_refl))) | intros v3].
      apply IH; [intros rk Hin; apply Hp; right; exact Hin | intros rk Hin; apply Hd; right; exact Hin
                | intros rk Hin; apply Hi; right; exact Hin | intros a b c; apply Hk].
    Qed.

    Lemma simS_writeRegsList :
      forall k sz (paths : list (RegOfKind (t := plicTree n) k)) (idx : Expr type (Bit sz)) v,
        (forall rk, In rk paths -> NotMeipClaim rk.(rk_path)) -> SimS (@writeRegsList type k sz (plicTree n) paths idx v).
    Proof.
      intros k sz paths idx v Hp; apply simS_writeRegsListHelper.
      intros rk Hin s1 s2 w HR; exact (PlicR_write _ (Hp rk Hin) s1 s2 w HR).
    Qed.

    Lemma simS_writeLineWords :
      forall sz (paths : list (RegOfKind (t := plicTree n) (Bit Xlen))) (idx : Expr type (Bit sz)) words,
        (forall rk, In rk paths -> NotMeipClaim rk.(rk_path)) -> SimS (@writeLineWords n type sz paths idx words).
    Proof.
      intros sz paths idx words Hp; unfold writeLineWords.
      induction (genFinType NumLineWords) as [| i l IH]; cbn [fold_right]; [apply simS_return |].
      apply simS_letAction; [apply simS_writeRegsList; exact Hp | intros _; exact IH].
    Qed.

    (* claim := 0, then meip := false *)
    Lemma simS_claimMeip :
      forall k (n1 n2 : string) (e0 : Expr type (Bit Xlen)) (z1 z2 : Expr type (Bit 0))
             (c : type (Bit 0) -> Action type (plicTree n) k),
        evalExpr e0 = Zmod.zero ->
        (forall v, SimS (c v)) ->
        SimS (LetAction n1 (WriteReg (plicClaimPath n) e0 (Return z1))
                (fun _ => LetAction n2 (WriteReg (plicMeipPath n) (ConstBool false) (Return z2)) c)).
    Proof.
      intros k n1 n2 e0 z1 z2 c E0 Hc s1 s2 HR P1 P2 HP H; cbn [evalActionPropGen] in *.
      refine (Hc _ _ _ _ _ _ HP H).
      destruct HR as [[E1 E2] [E3 E4]].
      rewrite E1; clear E1 E2.
      destruct s1 as [pr [pe [en [th [cl [me [insv [ua []]]]]]]]].
      split; [split |]; [| | split].
      - cbn; reflexivity.
      - cbn; intros Hf; discriminate Hf.
      - cbn; intros Hf; discriminate Hf.
      - intros _; unfold PlicInv; cbn; intros Hf; discriminate Hf.
    Qed.

    Ltac nmc_list := intros rk Hin;
      first [ exact (NotMeipClaim_pend rk Hin) | exact (NotMeipClaim_insv rk Hin)
            | exact (NotMeipClaim_en rk Hin) | exact (NotMeipClaim_prio rk Hin) ].
    Ltac nm_list := intros rk Hin;
      first [ exact (proj1 (NotMeipClaim_pend rk Hin)) | exact (proj1 (NotMeipClaim_insv rk Hin))
            | exact (proj1 (NotMeipClaim_en rk Hin)) | exact (proj1 (NotMeipClaim_prio rk Hin)) ].
    Ltac plic_walk :=
      repeat first
        [ apply simS_claimMeip; [reflexivity | intros ?]
        | apply simS_readRegs; [nm_list | intros ?]
        | apply simS_readAllSources; [nm_list | nm_list | nm_list | intros ? ? ?]
        | apply simS_writeRegsList; nmc_list
        | apply simS_writeLineWords; nmc_list
        | apply simS_letExp; intros ?
        | apply simS_letAction; [| intros ?]
        | apply simS_ifElse; [| | intros ?]
        | apply simS_readReg; [first [exact (PlicR_read _ (proj1 NotMeipClaim_thresh))
                                     | exact (PlicR_read _ NotMeip_claim)] | intros ?]
        | apply simS_writeReg; [intros ? ? ?; exact (PlicR_write _ NotMeipClaim_thresh _ _ _) |]
        | apply simS_return ].

    Lemma plicWrite_simS : forall addr data mask, SimS (@plicLineWriteAction n base type addr data mask).
    Proof. intros addr data mask; unfold plicLineWriteAction, decodePlicLine, readPlicState, plicComplete; plic_walk. Qed.

    Lemma plicRead_simS : forall addr mask, SimS (@plicLineReadAction n base type addr mask).
    Proof. intros addr mask; unfold plicLineReadAction, decodePlicLine, readPlicState, plicClaim; plic_walk. Qed.
  End Rel.

  Lemma plicSim_of :
    forall env1 env2 k (a : Action type (plicTree n) k) (xs xi xi' : PS) v,
      (forall xs0 xi0, SimA (plicTree n) (plicTree n) (PlicR xs0 xi0) env1 env2 a a) ->
      PlicRelSame n xs xi -> SemAction env1 a xi xi' v ->
      exists xs', SemAction env2 a xs xs' v /\ PlicRelSame n xs' xi' /\
        (plicMeipOf xs' = true -> plicMeipOf xs = true) /\ (PlicInv xi -> PlicInv xi').
  Proof.
    intros env1 env2 k a xs xi xi' v HS HR H.
    rewrite SemAction_iff_evalActionPropGen in H.
    assert (HR0 : PlicR xs xi xi xs) by (split; [exact HR | split; intros Hx; exact Hx]).
    pose proof (HS xs xi xi xs HR0 (fun s r => s = xi' /\ r = v) (fun s r => r = v /\ PlicR xs xi xi' s)
                  (fun s1' s2' r HR' HP => match HP with conj E1 E2 =>
                     conj E2 (eq_ind s1' (fun z => PlicR xs xi z s2') HR' xi' E1) end) H) as H2.
    destruct (evalActionPropGen_to_SemAction _ _ _ H2) as [xs' [r [Hs [-> [E1 [E2 E3]]]]]].
    exists xs'; split; [exact Hs | split; [exact E1 | split; [exact E2 | exact E3]]].
  Qed.

  Lemma plicWrite_sim :
    forall env1 env2 (xs xi xi' : PS) addr data mask v,
      PlicRelSame n xs xi -> SemAction env1 (@plicLineWriteAction n base type addr data mask) xi xi' v ->
      exists xs', SemAction env2 (@plicLineWriteAction n base type addr data mask) xs xs' v /\
        PlicRelSame n xs' xi' /\ (plicMeipOf xs' = true -> plicMeipOf xs = true) /\ (PlicInv xi -> PlicInv xi').
  Proof. intros; eapply plicSim_of; [intros; apply plicWrite_simS | eassumption ..]. Qed.

  Lemma plicRead_sim :
    forall env1 env2 (xs xi xi' : PS) addr mask v,
      PlicRelSame n xs xi -> SemAction env1 (@plicLineReadAction n base type addr mask) xi xi' v ->
      exists xs', SemAction env2 (@plicLineReadAction n base type addr mask) xs xs' v /\
        PlicRelSame n xs' xi' /\ (plicMeipOf xs' = true -> plicMeipOf xs = true) /\ (PlicInv xi -> PlicInv xi').
  Proof. intros; eapply plicSim_of; [intros; apply plicRead_simS | eassumption ..]. Qed.
End PlicSim.
