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

Theorem BoundsMonotonic cap addr base length isRoundDown:
  let ecap : type ECap := evalLetExpr (DecodeCap cap addr) in
  let bounds : type BoundsRes := evalLetExpr (Bounds base length isRoundDown) in
  (Zmod.to_Z base >= Zmod.to_Z (ecap@%"base") /\ Zmod.to_Z (base + length) <= Zmod.to_Z (ecap@%"top"))%Z ->
  (Zmod.to_Z (bounds@%"base") >= Zmod.to_Z base /\ Zmod.to_Z (bounds@%"top") <= Zmod.to_Z (base + length))%Z.
Proof.
  admit.
Admitted.
