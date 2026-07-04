(*
 * Copyright 2026 Google LLC (Cherified Team)
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

From Stdlib Require Import List String Ascii ZArith Zmod.
From Guru Require Import Library Syntax Semantics Notations.
From Cheriot Require Import SpecDefines AluLatest.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Ltac z3_simplify :=
  cbn -[
    (* ==========================================
       Arrays and Loops (Syntax.v)
       ========================================== *)
    countLeadingZerosArray countTrailingZerosArray
    countLeadingZerosLoop countTrailingZerosLoop countOnesArray
    mkBoolArray

    (* ==========================================
       ZArith (BinIntDef.v + ZArith)
       ========================================== *)
    (* Core operations *)
    Z.add Z.sub Z.mul Z.div Z.modulo Z.quot Z.rem Z.pow Z.opp Z.succ Z.pred
    Z.square

    (* Comparisons *)
    Z.geb Z.leb Z.eqb Z.gtb Z.ltb
    Z.ge Z.le Z.gt Z.lt Z.eq Z.compare
    Z.max Z.min

    (* Bitwise *)
    Z.land Z.lor Z.lxor Z.ldiff Z.shiftl Z.shiftr Z.testbit
    Z.setbit Z.clearbit Z.lnot

    (* Misc / Types *)
    Z.abs Z.sgn Z.log2 Z.log2_up Z.even Z.odd Z.to_nat Z.of_nat
    Z.to_N Z.of_N Z.gcd Z.ggcd Z.sqrt Z.quot2 Z.iter

    (* ==========================================
       Zmod (ZmodDef.v)
       ========================================== *)
    (* Core arithmetic *)
    Zmod.add Zmod.sub Zmod.mul Zmod.udiv Zmod.umod Zmod.squot Zmod.srem
    Zmod.opp Zmod.inv Zmod.mdiv Zmod.pow Zmod.abs

    (* Bitwise *)
    Zmod.and Zmod.or Zmod.xor Zmod.not Zmod.ndn

    (* Shifts and slicing *)
    Zmod.slu Zmod.sru Zmod.srs
    Zmod.app Zmod.firstn Zmod.skipn Zmod.slice

    (* Equality and Constants *)
    Zmod.eqb Zmod.zero Zmod.one

    (* Conversions and Extracted states *)
    Zmod.to_Z Zmod.of_Z Zmod.of_small_Z Zmod.signed
    Zmod.elements Zmod.positives Zmod.negatives Zmod.invertibles
  ].

Theorem BoundsMonotonicBool cap addr base length isRoundDown:
  let ecap : type ECap := evalLetExpr (DecodeCap cap addr) in
  let bounds : type BoundsRes := evalLetExpr (Bounds base length isRoundDown) in
  orb (negb (andb (Z.geb (Zmod.to_Z base) (Zmod.to_Z (ecap@%"base")))
                  (Z.leb (Zmod.to_Z (base + length)) (Zmod.to_Z (ecap@%"top")))))
      (andb (Z.geb (Zmod.to_Z (bounds@%"base")) (Zmod.to_Z (ecap@%"base")))
            (Z.leb (Zmod.to_Z (bounds@%"top")) (Zmod.to_Z (ecap@%"top")))) = true.
Proof.
  admit.
Admitted.

Theorem BoundsMonotonic cap addr base length isRoundDown:
  let ecap : type ECap := evalLetExpr (DecodeCap cap addr) in
  let bounds : type BoundsRes := evalLetExpr (Bounds base length isRoundDown) in
  (Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (base + length) <= Zmod.to_Z (ecap@%"top"))%Z ->
  (Zmod.to_Z (bounds@%"base") >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (bounds@%"top") <= Zmod.to_Z (ecap@%"top"))%Z.
Proof.
  admit.
Admitted.
