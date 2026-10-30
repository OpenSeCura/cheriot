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
From Cheriot.Proof Require Import StateRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * FACTS ABOUT THE SHARED DECODER AND ALU USED BY THE REFINEMENT PROOF
 * ===========================================================================
 * Pre-decode, compressed-instruction and control-flow classification facts
 * connecting the impl front end (preDecodeBranch, parcel checks) to the shared
 * decoder and ALU.
 *
 * Main results:
 *   - [preDecode_zero]                  preDecode of the all-zero word is zero.
 *   - [preDecode_concat_hi_irrelevant]  preDecode {< hi, lo >} ignores hi when lo is compressed.
 *   - [isCompressed_preDecode], [isCompressed_concat_parcels], [isCompressed_preDecode_concat]
 *                                       compressed-ness is preserved by preDecode and is decided
 *                                       by the low parcel.
 *   - [preDecodeBranch_nonSeq]          a predicted Cjal/Branch/Cjalr makes the ALU op
 *                                       NonSequential (see also [preDecodeBranch_needsPred]).
 *   - [wrappedAlu_fetchExc_nonSeq]      a fetch fault makes the ALU op NonSequential/Exception.
 *   - [wrappedAlu_isComp], [wrappedAlu_isComp_decode]
 *                                       aluOut.isComp is isCompressed of the instruction. *)

(* Symbolic evaluation of the quadrant expansions (used by the locality lemmas): also
 * evaluates SignExtendTo, whose msbIsZero goes through a [castBits] over concrete widths. *)
Ltac df_cbn_quad :=
  cbn [evalLetExpr evalExpr ConstExtract getCd SignExtendTo SignExtend msbIsZero isZero castBits
       Z_cast positive_cast kindSize evalToBit KindCustomInd
       Z.add Z.sub Z.opp Z.pos_sub Z.double Z.succ_double Z.pred_double
       Pos.pred_double Pos.add Pos.add_carry Pos.succ].

(* ===========================================================================
 * A. ALU / DECODER CONVERSION FACTS
 * =========================================================================== *)

(* ControlFlow valid bit of the routing output *)
Lemma df_routing_cfValid : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  let grp : type InstGroup := evalExpr (##pkg`"instGroup") in
  (evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type pkg)))).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) =
  orb (orb (orb (evalExpr (##grp`"Branch")) (evalExpr (##grp`"Cjal"))) (evalExpr (##grp`"Cjalr")))
      (evalExpr (##grp`"Mret")).
Proof. intros pcc pkg grp. reflexivity. Qed.

(* The decoder's Cjal/Branch/Cjalr flags are the predictor's pre-decode flags *)
Lemma df_decode_flags : forall fo : type FetchOut,
  let rri : type RegReadIn := evalLetExpr (@wrappedDecode type fo) in
  let dout : type DecodeOut := evalExpr (##rri`"decodeOut") in
  let grp : type InstGroup := evalExpr (##dout`"instGroup") in
  let pb : type PreBranchInfo := evalLetExpr (@preDecodeBranch type (evalExpr (##fo`"inst"))) in
  evalExpr (##grp`"Cjal") = evalExpr (##pb`"isCjal") /\
  evalExpr (##grp`"Branch") = evalExpr (##pb`"isBranch") /\
  evalExpr (##grp`"Cjalr") = evalExpr (##pb`"isCjalr").
Proof. intros fo rri dout grp pb. split; [| split]; reflexivity. Qed.

(* Deliverable 6: aluOut.isComp = isCompressed (aluIn.inst) *)
Theorem wrappedAlu_isComp : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  let aluOut : type AluOutUnion := evalLetExpr (@wrappedAlu type pcc pkg) in
  evalExpr (##aluOut`"isComp") = evalExpr (@isCompressed type (evalExpr (##pkg`"inst"))).
Proof. intros pcc pkg aluOut. reflexivity. Qed.

(* The decoder's instGroup.isCompressed flag, and the instruction it forwards *)
Theorem decode_isCompressed : forall fo : type FetchOut,
  let rri : type RegReadIn := evalLetExpr (@wrappedDecode type fo) in
  let dout : type DecodeOut := evalExpr (##rri`"decodeOut") in
  let grp : type InstGroup := evalExpr (##dout`"instGroup") in
  evalExpr (##grp`"isCompressed") = evalExpr (@isCompressed type (evalExpr (##fo`"inst"))) /\
  evalExpr (##rri`"inst") = evalExpr (##fo`"inst").
Proof. intros fo rri dout grp. split; reflexivity. Qed.

(* Alu stage: a valid ControlFlow payload makes the op NonSequential *)
Lemma df_Alu_cf : forall ro : type AluOut,
  ro.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true ->
  evalExpr ((Var type AluOpUnion ((evalLetExpr (@Alu type ro)).(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = false /\
  evalExpr ((Var type AluOpUnion ((evalLetExpr (@Alu type ro)).(Snd).(Snd).(Snd).(Fst))) `? "NonSequential") = true.
Proof.
  intros ro Hcf.
  destruct ro as [isComp [dstIdx [dstValue [[excD [excV []]] [[dmD [dmV []]] [md [[cfD [cfV []]] [[scD [scV []]] []]]]]]]]].
  cbn [Fst Snd] in Hcf. subst cfV.
  destruct excV, dmV, scV; split; reflexivity.
Qed.

(* Routing stage: a fetch fault makes the Exception payload valid *)
Lemma df_routing_excValid : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  let fexc : type FetchException := evalExpr (##pkg`"fetchExc") in
  evalExpr (Or [##fexc`"tag"; ##fexc`"seal"; ##fexc`"perm"; ##fexc`"bounds"]) = true ->
  (evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type pkg)))).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true.
Proof.
  intros pcc pkg.
  destruct pkg as [wcd [scr [csr [inst [dexc [[ft [fs [fp [fb []]]]] [cs1 [cs2 [grp []]]]]]]]]].
  cbv zeta. intros Hf.
  destruct ft; [reflexivity |].
  destruct fs; [reflexivity |].
  destruct fp; [reflexivity |].
  destruct fb; [reflexivity |].
  exfalso. first [discriminate Hf | (vm_compute in Hf; discriminate Hf)].
Qed.

(* ===========================================================================
 * 1. GENERIC BIT-VECTOR HELPERS
 * =========================================================================== *)

Lemma df_testbit_high : forall a n i : Z,
  0 <= n <= i -> 0 <= a < 2 ^ n -> Z.testbit a i = false.
Proof.
  intros a n i Hni Ha.
  apply Z.testbit_false; [lia |].
  rewrite Z.div_small; [reflexivity |].
  split; [lia |].
  eapply Z.lt_le_trans; [exact (proj2 Ha) | apply Z.pow_le_mono_r; lia].
Qed.

Lemma df_or_zero_l : forall (n : Z) (x : bits n), Zmod.or Zmod.zero x = x.
Proof.
  intros n x. apply Zmod.unsigned_inj.
  rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l. reflexivity.
Qed.

Lemma df_or_zero_r : forall (n : Z) (x : bits n), Zmod.or x Zmod.zero = x.
Proof.
  intros n x. apply Zmod.unsigned_inj.
  rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_r. reflexivity.
Qed.

Lemma df_firstn_firstn : forall (n k w : Z) (a : bits w),
  0 <= n <= k -> @Zmod.firstn n k (@Zmod.firstn k w a) = @Zmod.firstn n w a.
Proof.
  intros n k w a Hnk. apply Zmod.unsigned_inj.
  rewrite !bits.unsigned_firstn.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i n); destruct (Z.ltb_spec i k); cbn [andb];
    first [reflexivity | exfalso; lia].
Qed.

Lemma df_lastn_same : forall (n w : Z) (a : bits w),
  w = n -> @Zmod_lastn n w a = @Zmod.firstn n w a.
Proof.
  intros n w a Hw. subst w.
  unfold Zmod_lastn, Zmod.firstn.
  rewrite Z.sub_diag, Z.shiftr_0_r. reflexivity.
Qed.

Lemma df_bits2_cases : forall q : bits 2,
  q = Zmod.of_Z (2 ^ 2) 0 \/ q = Zmod.of_Z (2 ^ 2) 1 \/
  q = Zmod.of_Z (2 ^ 2) 2 \/ q = Zmod.of_Z (2 ^ 2) 3.
Proof.
  intros q.
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  assert (H4 : 2 ^ 2 = 4) by reflexivity.
  assert (Hc : Zmod.unsigned q = 0 \/ Zmod.unsigned q = 1 \/
               Zmod.unsigned q = 2 \/ Zmod.unsigned q = 3) by lia.
  destruct Hc as [Hc | [Hc | [Hc | Hc]]];
    [left | right; left | right; right; left | right; right; right];
    apply Zmod.unsigned_inj; rewrite Hc, Zmod.unsigned_of_Z; reflexivity.
Qed.

Lemma df_bits2_neq01 : Zmod.of_Z (2 ^ 2) 0 <> Zmod.of_Z (2 ^ 2) 1.
Proof. intros H. apply (f_equal Zmod.unsigned) in H. vm_compute in H. discriminate H. Qed.

Lemma df_bits2_neq02 : Zmod.of_Z (2 ^ 2) 0 <> Zmod.of_Z (2 ^ 2) 2.
Proof. intros H. apply (f_equal Zmod.unsigned) in H. vm_compute in H. discriminate H. Qed.

Lemma df_bits2_neq12 : Zmod.of_Z (2 ^ 2) 1 <> Zmod.of_Z (2 ^ 2) 2.
Proof. intros H. apply (f_equal Zmod.unsigned) in H. vm_compute in H. discriminate H. Qed.

Lemma df_unsigned_app2 : forall (c : bits 2) (h : bits 30),
  Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) c) h) =
  Z.lor (Zmod.unsigned c) (Z.shiftl (Zmod.unsigned h) 2).
Proof.
  intros c h. rewrite !bits.unsigned_app by lia.
  rewrite Zmod.unsigned_0, Z.shiftl_0_r, Z.lor_0_l. reflexivity.
Qed.

Lemma df_firstn2_app : forall (c : bits 2) (h : bits 30),
  @Zmod.firstn 2 32 (Zmod.app (Zmod.app (Zmod.zero : bits 0) c) h) = c.
Proof.
  intros c h. apply Zmod.unsigned_inj.
  rewrite bits.unsigned_firstn.
  change (Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) c) h) mod 2 ^ 2 = Zmod.unsigned c).
  rewrite df_unsigned_app2.
  pose proof (bits.unsigned_range c ltac:(lia)) as Hc.
  apply Z.bits_inj'; intros i Hi.
  rewrite Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i 2) as [Hlt | Hge]; cbn [andb].
  - rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r (Zmod.unsigned h)) by lia.
    apply orb_false_r.
  - symmetry. apply (df_testbit_high _ 2); lia.
Qed.

Lemma df_unsigned_parcels_app : forall lo hi : bits CompInstSz,
  Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) lo) hi) =
  Z.lor (Zmod.unsigned lo) (Z.shiftl (Zmod.unsigned hi) CompInstSz).
Proof.
  intros lo hi. assert (HC : CompInstSz = 16) by reflexivity.
  rewrite !bits.unsigned_app by lia.
  rewrite Zmod.unsigned_0, Z.shiftl_0_r, Z.lor_0_l. reflexivity.
Qed.

(* Reading back the tag of a tagged union that was packed with tag [t] and then
 * resized (the round trip performed by nested [TaggedUnion] reads). *)
Lemma df_union_tag_rt : forall (n W K M t : Z) (d : bits W),
  0 <= n -> 0 <= W -> n <= K -> n <= M ->
  Zmod.eqb (@Zmod.firstn n K (Zmod.of_Z (2 ^ K) (Zmod.unsigned (Zmod.of_Z (2 ^ M)
              (Zmod.unsigned (@Zmod.app n W (Zmod.of_Z (2 ^ n) t) d))))))
           (Zmod.of_Z (2 ^ n) t) = true.
Proof.
  intros n W K M t d Hn HW HK HM.
  apply Zmod.eqb_eq; apply Zmod.unsigned_inj.
  rewrite bits.unsigned_firstn, !Zmod.unsigned_of_Z.
  rewrite bits.unsigned_app by assumption.
  rewrite Zmod.unsigned_of_Z.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i n) as [Hin | Hin]; cbn [andb]; [| reflexivity].
  rewrite (proj2 (Z.ltb_lt i K)) by lia.
  rewrite (proj2 (Z.ltb_lt i M)) by lia.
  cbn [andb].
  rewrite Z.lor_spec, Z.shiftl_spec_low by lia.
  rewrite Z.testbit_mod_pow2 by lia.
  rewrite (proj2 (Z.ltb_lt i n)) by lia.
  cbn [andb]. apply orb_false_r.
Qed.

Lemma df_bool_cf : forall a b c d : bool,
  orb (orb a b) c = true -> orb (orb (orb b a) c) d = true.
Proof. intros [] [] [] []; cbn; intros H; first [reflexivity | discriminate H]. Qed.

(* ===========================================================================
 * B. ALU STAGE UNDER A VALID EXCEPTION
 * =========================================================================== *)

Lemma df_Alu_exc : forall ro : type AluOut,
  ro.(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true ->
  let aluOp : type AluOpUnion := (evalLetExpr (@Alu type ro)).(Snd).(Snd).(Snd).(Fst) in
  let nonSeqOp : type NonSequentialUnion := evalExpr ((Var type AluOpUnion aluOp) `! "NonSequential") in
  evalExpr ((Var type AluOpUnion aluOp) `? "Sequential") = false /\
  evalExpr ((Var type AluOpUnion aluOp) `? "NonSequential") = true /\
  evalExpr ((Var type NonSequentialUnion nonSeqOp) `? "Exception") = true.
Proof.
  intros ro Hexc.
  destruct ro as [isComp [dstIdx [dstValue [[excD [excV []]] [dm [md [cf [sc []]]]]]]]].
  cbn [Fst Snd] in Hexc. subst excV.
  cbv zeta.
  split; [reflexivity | split; [reflexivity |]].
  unfold Alu.
  cbn [evalLetExpr evalExpr readDiffTuple mapDiffTuple Fst Snd finNum fold_left map
       evalOrBinary evalBinary KindCustomInd getDefault orb evalToBit evalFromBit
       nth_pf snd AluOpUnionType NonSequentialUnion].
  match goal with
  | |- Zmod.eqb (@Zmod.firstn ?n ?K (Zmod.of_Z _ (Zmod.unsigned (Zmod.of_Z (2 ^ ?M)
          (Zmod.unsigned (@Zmod.app _ ?W (Zmod.of_Z _ ?t) ?d)))))) _ = true =>
      apply (df_union_tag_rt n W K M t d)
  end;
  apply Z.leb_le; vm_compute; reflexivity.
Qed.

(* ===========================================================================
 * 2. PRE-DECODE
 * =========================================================================== *)

Lemma df_isCompressed_eval : forall x : type Inst,
  evalExpr (@isCompressed type x) = negb (Zmod.eqb (@Zmod.firstn 2 32 x) (Zmod.of_Z (2 ^ 2) (-1))).
Proof. intros x. reflexivity. Qed.

Lemma df_isParcelCompressed_eval : forall p : type (Bit CompInstSz),
  evalExpr (@isParcelCompressed type p) =
  negb (Zmod.eqb (@Zmod.firstn 2 CompInstSz p) (Zmod.of_Z (2 ^ 2) (-1))).
Proof. intros p. reflexivity. Qed.

Lemma df_unsigned_concat_parcels : forall lo hi : type (Bit CompInstSz),
  Zmod.unsigned (evalExpr ({< #hi, #lo >} : Expr type Inst)) =
  Z.lor (Zmod.unsigned lo) (Z.shiftl (Zmod.unsigned hi) CompInstSz).
Proof.
  intros lo hi.
  change (Zmod.unsigned (Zmod.app (Zmod.app (Zmod.zero : bits 0) lo) hi) =
          Z.lor (Zmod.unsigned lo) (Z.shiftl (Zmod.unsigned hi) CompInstSz)).
  apply df_unsigned_parcels_app.
Qed.

Lemma df_firstn_concat_parcels : forall (lo hi : type (Bit CompInstSz)) (k : Z),
  0 <= k <= 16 ->
  @Zmod.firstn k 32 (evalExpr ({< #hi, #lo >} : Expr type Inst)) = @Zmod.firstn k CompInstSz lo.
Proof.
  intros lo hi k Hk.
  assert (HC : CompInstSz = 16) by reflexivity.
  apply Zmod.unsigned_inj.
  rewrite !bits.unsigned_firstn, df_unsigned_concat_parcels.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i k); cbn [andb]; [| reflexivity].
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  rewrite (Z.testbit_neg_r (Zmod.unsigned hi)) by lia.
  apply orb_false_r.
Qed.

Lemma df_quad_firstn2 : forall raw : type Inst,
  evalExpr (#raw`[1:0]) = @Zmod.firstn 2 32 raw.
Proof.
  intros raw. cbn [evalExpr ConstExtract].
  rewrite df_lastn_same by reflexivity.
  rewrite df_firstn_firstn by lia.
  reflexivity.
Qed.

Lemma df_preDecode_eval : forall raw : type Inst,
  evalLetExpr (@preDecode type raw) =
  (if Zmod.eqb (evalExpr (#raw`[1:0])) (Zmod.of_Z (2 ^ 2) 0) then evalLetExpr (@expandQuadrant0 type raw)
   else if Zmod.eqb (evalExpr (#raw`[1:0])) (Zmod.of_Z (2 ^ 2) 1) then evalLetExpr (@expandQuadrant1 type raw)
   else if Zmod.eqb (evalExpr (#raw`[1:0])) (Zmod.of_Z (2 ^ 2) 2) then evalLetExpr (@expandQuadrant2 type raw)
   else raw).
Proof.
  intros raw.
  unfold preDecode.
  cbn [evalLetExpr evalExpr caseDefault map fst snd fold_left evalOrBinary evalBinary KindCustomInd isEq
       getDefault orb Inst].
  pose proof df_bits2_neq01 as N01; pose proof df_bits2_neq02 as N02; pose proof df_bits2_neq12 as N12.
  (* name the quadrant selector; its copies agree up to conversion *)
  match goal with |- context [Zmod.eqb ?q (Zmod.of_Z (2 ^ 2) 0)] => set (Q := q) end.
  repeat match goal with
         | |- context [Zmod.eqb ?q (Zmod.of_Z (2 ^ 2) _)] =>
             tryif constr_eq q Q then fail else change q with Q
         end.
  clearbody Q.
  destruct (Zmod.eqb_spec Q (Zmod.of_Z (2 ^ 2) 0)) as [H0 | H0];
  destruct (Zmod.eqb_spec Q (Zmod.of_Z (2 ^ 2) 1)) as [H1 | H1];
  destruct (Zmod.eqb_spec Q (Zmod.of_Z (2 ^ 2) 2)) as [H2 | H2];
  cbn [orb];
  first [ reflexivity
        | exfalso; congruence
        | rewrite ?df_or_zero_l, ?df_or_zero_r; reflexivity
        | apply Zmod.unsigned_inj; rewrite ?bits.unsigned_or, ?Zmod.unsigned_0, ?Z.lor_0_l, ?Z.lor_0_r;
          reflexivity ].
Qed.

Lemma df_expandQuadrant0_shape : forall raw : type Inst,
  exists h : bits 30,
    evalLetExpr (@expandQuadrant0 type raw) = Zmod.app (Zmod.app (Zmod.zero : bits 0) (Zmod.zero : bits 2)) h.
Proof. intros raw. eexists. unfold expandQuadrant0. cbn [evalLetExpr evalExpr]. reflexivity. Qed.

Lemma df_expandQuadrant1_shape : forall raw : type Inst,
  exists h : bits 30,
    evalLetExpr (@expandQuadrant1 type raw) = Zmod.app (Zmod.app (Zmod.zero : bits 0) (Zmod.of_Z (2 ^ 2) 1)) h.
Proof. intros raw. eexists. unfold expandQuadrant1. cbn [evalLetExpr evalExpr]. reflexivity. Qed.

Lemma df_expandQuadrant2_shape : forall raw : type Inst,
  exists h : bits 30,
    evalLetExpr (@expandQuadrant2 type raw) = Zmod.app (Zmod.app (Zmod.zero : bits 0) (Zmod.of_Z (2 ^ 2) 2)) h.
Proof. intros raw. eexists. unfold expandQuadrant2. cbn [evalLetExpr evalExpr]. reflexivity. Qed.

Lemma df_expandQuadrant0_low : forall raw : type Inst,
  @Zmod.firstn 2 32 (evalLetExpr (@expandQuadrant0 type raw)) = Zmod.zero.
Proof. intros raw. destruct (df_expandQuadrant0_shape raw) as [h ->]. apply df_firstn2_app. Qed.

Lemma df_expandQuadrant1_low : forall raw : type Inst,
  @Zmod.firstn 2 32 (evalLetExpr (@expandQuadrant1 type raw)) = Zmod.of_Z (2 ^ 2) 1.
Proof. intros raw. destruct (df_expandQuadrant1_shape raw) as [h ->]. apply df_firstn2_app. Qed.

Lemma df_expandQuadrant2_low : forall raw : type Inst,
  @Zmod.firstn 2 32 (evalLetExpr (@expandQuadrant2 type raw)) = Zmod.of_Z (2 ^ 2) 2.
Proof. intros raw. destruct (df_expandQuadrant2_shape raw) as [h ->]. apply df_firstn2_app. Qed.

Lemma df_preDecode_firstn2 : forall raw : type Inst,
  @Zmod.firstn 2 32 (evalLetExpr (@preDecode type raw)) = @Zmod.firstn 2 32 raw.
Proof.
  intros raw.
  rewrite df_preDecode_eval, df_quad_firstn2.
  destruct (Zmod.eqb_spec (@Zmod.firstn 2 32 raw) (Zmod.of_Z (2 ^ 2) 0)) as [H0 | H0]; cbv beta iota;
    [rewrite df_expandQuadrant0_low, H0; first [reflexivity | apply Zmod.unsigned_inj; reflexivity] |].
  destruct (Zmod.eqb_spec (@Zmod.firstn 2 32 raw) (Zmod.of_Z (2 ^ 2) 1)) as [H1 | H1]; cbv beta iota;
    [rewrite df_expandQuadrant1_low, H1; reflexivity |].
  destruct (Zmod.eqb_spec (@Zmod.firstn 2 32 raw) (Zmod.of_Z (2 ^ 2) 2)) as [H2 | H2]; cbv beta iota;
    [rewrite df_expandQuadrant2_low, H2; reflexivity |].
  reflexivity.
Qed.

(* The quadrant expansions only read bits [15:0] of the instruction *)
Lemma df_expandQuadrant0_local : forall x y : type Inst,
  (forall k, 0 <= k <= 16 -> @Zmod.firstn k 32 x = @Zmod.firstn k 32 y) ->
  evalLetExpr (@expandQuadrant0 type x) = evalLetExpr (@expandQuadrant0 type y).
Proof.
  intros x y Hk. unfold expandQuadrant0.
  df_cbn_quad.
  rewrite !Hk by lia. reflexivity.
Qed.

Lemma df_expandQuadrant1_local : forall x y : type Inst,
  (forall k, 0 <= k <= 16 -> @Zmod.firstn k 32 x = @Zmod.firstn k 32 y) ->
  evalLetExpr (@expandQuadrant1 type x) = evalLetExpr (@expandQuadrant1 type y).
Proof.
  intros x y Hk. unfold expandQuadrant1.
  df_cbn_quad.
  rewrite !Hk by lia. reflexivity.
Qed.

Lemma df_expandQuadrant2_local : forall x y : type Inst,
  (forall k, 0 <= k <= 16 -> @Zmod.firstn k 32 x = @Zmod.firstn k 32 y) ->
  evalLetExpr (@expandQuadrant2 type x) = evalLetExpr (@expandQuadrant2 type y).
Proof.
  intros x y Hk. unfold expandQuadrant2.
  df_cbn_quad.
  rewrite !Hk by lia. reflexivity.
Qed.

Lemma df_preDecode_local : forall x y : type Inst,
  (forall k, 0 <= k <= 16 -> @Zmod.firstn k 32 x = @Zmod.firstn k 32 y) ->
  evalExpr (@isCompressed type x) = true ->
  evalLetExpr (@preDecode type x) = evalLetExpr (@preDecode type y).
Proof.
  intros x y Hk Hc.
  rewrite !df_preDecode_eval, !df_quad_firstn2.
  rewrite (Hk 2) by lia.
  rewrite (df_expandQuadrant0_local x y Hk), (df_expandQuadrant1_local x y Hk),
          (df_expandQuadrant2_local x y Hk).
  rewrite df_isCompressed_eval, (Hk 2) in Hc by lia.
  destruct (Zmod.eqb_spec (@Zmod.firstn 2 32 y) (Zmod.of_Z (2 ^ 2) 0)) as [E0 | E0]; [reflexivity |].
  destruct (Zmod.eqb_spec (@Zmod.firstn 2 32 y) (Zmod.of_Z (2 ^ 2) 1)) as [E1 | E1]; [reflexivity |].
  destruct (Zmod.eqb_spec (@Zmod.firstn 2 32 y) (Zmod.of_Z (2 ^ 2) 2)) as [E2 | E2]; [reflexivity |].
  exfalso.
  destruct (df_bits2_cases (@Zmod.firstn 2 32 y)) as [E | [E | [E | E]]]; try contradiction.
  rewrite E in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ===========================================================================
 * 3. MAIN PRE-DECODE THEOREMS
 * =========================================================================== *)

(* Deliverable 1 *)
Theorem preDecode_zero :
  evalLetExpr (@preDecode type (Zmod.zero : type Inst)) = (Zmod.zero : type Inst).
Proof. apply Zmod.unsigned_inj. vm_compute. reflexivity. Qed.

(* Deliverable 3 *)
Theorem isCompressed_preDecode : forall raw : type Inst,
  evalExpr (@isCompressed type (evalLetExpr (@preDecode type raw))) = evalExpr (@isCompressed type raw).
Proof. intros raw. rewrite !df_isCompressed_eval, df_preDecode_firstn2. reflexivity. Qed.

Theorem isCompressed_concat_parcels : forall lo hi : type (Bit CompInstSz),
  evalExpr (@isCompressed type (evalExpr ({< #hi, #lo >} : Expr type Inst))) =
  evalExpr (@isParcelCompressed type lo).
Proof.
  intros lo hi.
  rewrite df_isCompressed_eval, df_isParcelCompressed_eval, df_firstn_concat_parcels by lia.
  reflexivity.
Qed.

Theorem isCompressed_preDecode_concat : forall lo hi : type (Bit CompInstSz),
  evalExpr (@isCompressed type (evalLetExpr (@preDecode type (evalExpr ({< #hi, #lo >} : Expr type Inst))))) =
  evalExpr (@isParcelCompressed type lo).
Proof. intros lo hi. rewrite isCompressed_preDecode. apply isCompressed_concat_parcels. Qed.

(* Deliverable 2 *)
Theorem preDecode_concat_hi_irrelevant : forall lo hi hi' : type (Bit CompInstSz),
  evalExpr (@isParcelCompressed type lo) = true ->
  evalLetExpr (@preDecode type (evalExpr ({< #hi, #lo >} : Expr type Inst))) =
  evalLetExpr (@preDecode type (evalExpr ({< #hi', #lo >} : Expr type Inst))).
Proof.
  intros lo hi hi' Hc.
  apply df_preDecode_local.
  - intros k Hk. rewrite !df_firstn_concat_parcels by exact Hk. reflexivity.
  - rewrite isCompressed_concat_parcels. exact Hc.
Qed.

(* ===========================================================================
 * 4. BRANCH-PREDICTOR FLAGS
 * =========================================================================== *)

Lemma preDecodeBranch_call_return : forall inst : type Inst,
  let pb : type PreBranchInfo := evalLetExpr (@preDecodeBranch type inst) in
  orb (evalExpr (##pb`"isCall")) (evalExpr (##pb`"isReturn")) = true ->
  orb (orb (evalExpr (##pb`"isCjal")) (evalExpr (##pb`"isBranch"))) (evalExpr (##pb`"isCjalr")) = true.
Proof.
  intros inst. cbv zeta. unfold preDecodeBranch.
  cbn [evalLetExpr evalExpr readDiffTuple mapDiffTuple Fst Snd finNum fold_left map fst snd
       evalOrBinary evalAndBinary evalBinary evalNot KindCustomInd getDefault InvDefault isZero
       orb andb negb].
  repeat match goal with
         | |- context [@isEq ?k ?a ?b] => generalize (@isEq k a b); intro
         end.
  repeat match goal with b : bool |- _ => destruct b end;
  intros H; first [reflexivity | discriminate H].
Qed.

(* The impl's needsPred condition (ImplFetch) implies one of the three branch flags *)
Corollary preDecodeBranch_needsPred : forall inst : type Inst,
  let pb : type PreBranchInfo := evalLetExpr (@preDecodeBranch type inst) in
  evalExpr (Or [##pb`"isCjal"; ##pb`"isBranch"; ##pb`"isCjalr"; ##pb`"isCall"; ##pb`"isReturn"]) = true ->
  orb (orb (evalExpr (##pb`"isCjal")) (evalExpr (##pb`"isBranch"))) (evalExpr (##pb`"isCjalr")) = true.
Proof.
  intros inst pb Hn.
  pose proof (preDecodeBranch_call_return inst) as Hcr.
  change (orb (evalExpr (##pb`"isCall")) (evalExpr (##pb`"isReturn")) = true ->
          orb (orb (evalExpr (##pb`"isCjal")) (evalExpr (##pb`"isBranch"))) (evalExpr (##pb`"isCjalr"))
          = true) in Hcr.
  change (orb (orb (orb (orb (evalExpr (##pb`"isCjal")) (evalExpr (##pb`"isBranch")))
                         (evalExpr (##pb`"isCjalr")))
                    (evalExpr (##pb`"isCall")))
               (evalExpr (##pb`"isReturn")) = true) in Hn.
  revert Hn Hcr.
  generalize (evalExpr (##pb`"isCjal")) (evalExpr (##pb`"isBranch")) (evalExpr (##pb`"isCjalr"))
             (evalExpr (##pb`"isCall")) (evalExpr (##pb`"isReturn")).
  intros [] [] [] [] []; cbn; intros H1 H2;
    first [reflexivity | discriminate H1 | apply H2; reflexivity].
Qed.

(* ===========================================================================
 * 5. ALU CLASSIFICATION THEOREMS
 * =========================================================================== *)

Lemma df_evalLetExpr_LetEx : forall (k k' : Kind) (s : string) (le : LetExpr type k')
                                    (cont : type k' -> LetExpr type k),
  evalLetExpr (LetEx s le cont) = evalLetExpr (cont (evalLetExpr le)).
Proof. intros k k' s le cont. reflexivity. Qed.

Lemma df_evalLetExpr_RetE_Var : forall (k : Kind) (x : type k),
  evalLetExpr (RetE (Var type k x)) = x.
Proof. intros k x. reflexivity. Qed.

(* Stepping through the three bindings keeps the kernel from comparing the two
 * evaluated ALU terms (a direct conversion check does not finish). *)
Lemma df_wrappedAlu_unfold : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  evalLetExpr (@wrappedAlu type pcc pkg) =
  evalLetExpr (@Alu type (evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type pkg))))).
Proof.
  intros pcc pkg. unfold wrappedAlu.
  rewrite df_evalLetExpr_LetEx. cbv beta.
  rewrite df_evalLetExpr_LetEx. cbv beta.
  rewrite df_evalLetExpr_LetEx. cbv beta.
  rewrite df_evalLetExpr_RetE_Var. reflexivity.
Qed.

(* Any ControlFlow instruction group gives a NonSequential ALU op, for any operands *)
Theorem wrappedAlu_cf_nonSeq : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  let grp : type InstGroup := evalExpr (##pkg`"instGroup") in
  orb (orb (orb (evalExpr (##grp`"Branch")) (evalExpr (##grp`"Cjal"))) (evalExpr (##grp`"Cjalr")))
      (evalExpr (##grp`"Mret")) = true ->
  let aluOut : type AluOutUnion := evalLetExpr (@wrappedAlu type pcc pkg) in
  evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = false /\
  evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "NonSequential") = true.
Proof.
  intros pcc pkg grp Hcf.
  pose proof (df_routing_cfValid pcc pkg) as E. cbv zeta in E.
  assert (Hr : (evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type pkg)))).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).(Snd).(Fst) = true)
    by (rewrite E; exact Hcf).
  pose proof (df_Alu_cf _ Hr) as Ha.
  cbv zeta. rewrite df_wrappedAlu_unfold. exact Ha.
Qed.

(* Deliverable 4: if the predictor's pre-decode of the fetched instruction flags
 * Cjal/Branch/Cjalr, the ALU op of that instruction is NonSequential, for any pcc and
 * any register values (pkg only has to carry the decoder's instGroup; for the
 * register-read result of [wrappedDecode fo] this hypothesis holds by reflexivity). *)
Theorem preDecodeBranch_nonSeq :
  forall (pcc : type FullECapWithTag) (fo : type FetchOut) (expInst : type Inst) (pkg : type AluInInstGroup),
  evalExpr (##fo`"inst") = expInst ->
  let rri : type RegReadIn := evalLetExpr (@wrappedDecode type fo) in
  let dout : type DecodeOut := evalExpr (##rri`"decodeOut") in
  evalExpr (##pkg`"instGroup") = evalExpr (##dout`"instGroup") ->
  let pb : type PreBranchInfo := evalLetExpr (@preDecodeBranch type expInst) in
  orb (orb (evalExpr (##pb`"isCjal")) (evalExpr (##pb`"isBranch"))) (evalExpr (##pb`"isCjalr")) = true ->
  let aluOut : type AluOutUnion := evalLetExpr (@wrappedAlu type pcc pkg) in
  evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "Sequential") = false /\
  evalExpr ((Var type AluOpUnion (aluOut.(Snd).(Snd).(Snd).(Fst))) `? "NonSequential") = true.
Proof.
  intros pcc fo expInst pkg Hinst. subst expInst.
  cbv zeta. intros Hgrp Hpb.
  pose proof (wrappedAlu_cf_nonSeq pcc pkg) as T. cbv zeta in T. apply T. clear T.
  rewrite Hgrp.
  pose proof (df_decode_flags fo) as Hd. cbv zeta in Hd. destruct Hd as [E1 [E2 E3]].
  first [rewrite E1, E2, E3 | idtac].
  apply df_bool_cf. exact Hpb.
Qed.

(* Deliverable 5: a fetch fault forces a NonSequential/Exception ALU op, for any operands *)
Theorem wrappedAlu_fetchExc_nonSeq : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  let fexc : type FetchException := evalExpr (##pkg`"fetchExc") in
  evalExpr (Or [##fexc`"tag"; ##fexc`"seal"; ##fexc`"perm"; ##fexc`"bounds"]) = true ->
  let aluOut : type AluOutUnion := evalLetExpr (@wrappedAlu type pcc pkg) in
  let aluOp : type AluOpUnion := aluOut.(Snd).(Snd).(Snd).(Fst) in
  let nonSeqOp : type NonSequentialUnion := evalExpr ((Var type AluOpUnion aluOp) `! "NonSequential") in
  evalExpr ((Var type AluOpUnion aluOp) `? "Sequential") = false /\
  evalExpr ((Var type AluOpUnion aluOp) `? "NonSequential") = true /\
  evalExpr ((Var type NonSequentialUnion nonSeqOp) `? "Exception") = true.
Proof.
  intros pcc pkg fexc Hf.
  pose proof (df_routing_excValid pcc pkg Hf) as Hr.
  pose proof (df_Alu_exc (evalLetExpr (@AluRouting type pcc (evalLetExpr (@constructAluIn type pkg)))) Hr) as Ha.
  cbv zeta in Ha |- *.
  rewrite df_wrappedAlu_unfold. exact Ha.
Qed.

(* Deliverable 6, traced through the decoder: aluOut.isComp is the decoder's
 * instGroup.isCompressed whenever the ALU input carries the decoded instruction. *)
Corollary wrappedAlu_isComp_decode :
  forall (pcc : type FullECapWithTag) (fo : type FetchOut) (pkg : type AluInInstGroup),
  let rri : type RegReadIn := evalLetExpr (@wrappedDecode type fo) in
  let dout : type DecodeOut := evalExpr (##rri`"decodeOut") in
  let grp : type InstGroup := evalExpr (##dout`"instGroup") in
  evalExpr (##pkg`"inst") = evalExpr (##rri`"inst") ->
  let aluOut : type AluOutUnion := evalLetExpr (@wrappedAlu type pcc pkg) in
  evalExpr (##aluOut`"isComp") = evalExpr (##grp`"isCompressed").
Proof.
  intros pcc fo pkg. cbv zeta. intros Hinst.
  pose proof (wrappedAlu_isComp pcc pkg) as E1. cbv zeta in E1. rewrite E1. clear E1.
  rewrite Hinst.
  pose proof (decode_isCompressed fo) as E. cbv zeta in E. destruct E as [E2 E3].
  rewrite E3, E2. reflexivity.
Qed.
