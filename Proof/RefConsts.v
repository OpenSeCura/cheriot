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

From Stdlib Require Import ZArith Lia.
From Cheriot Require Import SpecDefines.

Local Open Scope Z_scope.

(* The memory geometry: address, line, capability-slot and access sizes.
 *
 * As in BoundsMonotonic.v, only the `invariant_*` theorems unfold the constants of SpecDefines.
 * Every other fact about these constants, here and in the files that import this one, is derived
 * from them, so a configuration change only has to re-establish these theorems. (Besides them, only
 * RefSnoopMiss.v's two mask checks `checkD_ok` and `checkT_ok` compute with the configured sizes; they
 * are stated over the named constants and rerun for any configuration.) *)

(* ========================================================================= *)
(* PRIMARY INVARIANTS                                                        *)
(* ========================================================================= *)

(* An address is a capability-slot index followed by a byte offset in the slot *)
Theorem invariant_TagAddrWidth : TagAddrWidth = AddrSz - LgNumBytesFullCapSz.
Proof. reflexivity. Qed.

(* A line holds 2^LgNumLineTags capability slots *)
Theorem invariant_LgNumLineTags : LgNumLineTags = LgLineBytes - LgNumBytesFullCapSz.
Proof. reflexivity. Qed.

Theorem invariant_LineBytes : Z.of_nat LineBytes = 2 ^ LgLineBytes.
Proof. reflexivity. Qed.

Theorem invariant_NumLineTags : Z.of_nat NumLineTags = 2 ^ LgNumLineTags.
Proof. reflexivity. Qed.

Theorem invariant_NumBytesFullCapSz : NumBytesFullCapSz = 2 ^ LgNumBytesFullCapSz.
Proof. reflexivity. Qed.

(* A capability slot fits in a line, a line in the address space *)
Theorem invariant_geometry : 0 <= LgNumBytesFullCapSz <= LgLineBytes /\ LgLineBytes < AddrSz.
Proof. unfold LgNumBytesFullCapSz, LgLineBytes, AddrSz; lia. Qed.

(* The size field of an access codes 2^0 .. 2^LgNumBytesFullCapSz bytes: no access is bigger than a
 * capability slot *)
Theorem invariant_sizes : 0 <= LgLgNumBytesFullCapSz /\ 2 ^ LgLgNumBytesFullCapSz = LgNumBytesFullCapSz + 1.
Proof. unfold LgLgNumBytesFullCapSz, LgNumBytesFullCapSz; split; [lia | reflexivity]. Qed.

(* ========================================================================= *)
(* DERIVED FACTS (from the invariants only)                                  *)
(* ========================================================================= *)

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn; apply Z.pow_pos_nonneg; lia. Qed.

Lemma LgNumBytesFullCapSz_nonneg : 0 <= LgNumBytesFullCapSz.
Proof. pose proof invariant_geometry; lia. Qed.

Lemma LgLineBytes_nonneg : 0 <= LgLineBytes.
Proof. pose proof invariant_geometry; lia. Qed.

Lemma LgLineBytes_lt_AddrSz : LgLineBytes < AddrSz.
Proof. pose proof invariant_geometry; lia. Qed.

Lemma LgNumLineTags_nonneg : 0 <= LgNumLineTags.
Proof. rewrite invariant_LgNumLineTags; pose proof invariant_geometry; lia. Qed.

Lemma TagAddrWidth_pos : 0 < TagAddrWidth.
Proof. rewrite invariant_TagAddrWidth; pose proof invariant_geometry; lia. Qed.

Lemma LgLgNumBytesFullCapSz_nonneg : 0 <= LgLgNumBytesFullCapSz.
Proof. exact (proj1 invariant_sizes). Qed.

(* The size field is narrower than the slot offset *)
Lemma LgLgNumBytesFullCapSz_le : LgLgNumBytesFullCapSz <= LgNumBytesFullCapSz.
Proof.
  destruct invariant_sizes as [H0 H1].
  pose proof (Z.pow_gt_lin_r 2 LgLgNumBytesFullCapSz ltac:(lia) H0); lia.
Qed.

(* The code of a full capability fits in the size field *)
Lemma LgNumBytesFullCapSz_lt_sizes : LgNumBytesFullCapSz < 2 ^ LgLgNumBytesFullCapSz.
Proof. rewrite (proj2 invariant_sizes); lia. Qed.

Lemma capBytes_pos : 0 < 2 ^ LgNumBytesFullCapSz.
Proof. apply pow2_pos, LgNumBytesFullCapSz_nonneg. Qed.

Lemma lineBytes_pos : 0 < 2 ^ LgLineBytes.
Proof. apply pow2_pos, LgLineBytes_nonneg. Qed.

Lemma lineTags_pos : 0 < 2 ^ LgNumLineTags.
Proof. apply pow2_pos, LgNumLineTags_nonneg. Qed.

Lemma lineCount_pos : 0 < 2 ^ (AddrSz - LgLineBytes).
Proof. apply pow2_pos; pose proof LgLineBytes_lt_AddrSz; lia. Qed.

Lemma addrBytes_pos : 0 < 2 ^ AddrSz.
Proof. apply pow2_pos; pose proof LgLineBytes_lt_AddrSz; pose proof LgLineBytes_nonneg; lia. Qed.

Lemma slotCount_gt1 : 1 < 2 ^ TagAddrWidth.
Proof. apply Z.pow_gt_1; [lia | exact TagAddrWidth_pos]. Qed.

(* A line is 2^LgNumLineTags capability slots *)
Lemma lineBytes_split : 2 ^ LgLineBytes = 2 ^ LgNumLineTags * 2 ^ LgNumBytesFullCapSz.
Proof.
  pose proof LgNumLineTags_nonneg; pose proof LgNumBytesFullCapSz_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)); pose proof invariant_LgNumLineTags; lia.
Qed.

(* The address space is 2^TagAddrWidth capability slots *)
Lemma addrBytes_split : 2 ^ AddrSz = 2 ^ TagAddrWidth * 2 ^ LgNumBytesFullCapSz.
Proof.
  pose proof TagAddrWidth_pos; pose proof LgNumBytesFullCapSz_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)); pose proof invariant_TagAddrWidth; lia.
Qed.

(* The address space is 2^(AddrSz - LgLineBytes) lines *)
Lemma addrBytes_lines : 2 ^ AddrSz = 2 ^ (AddrSz - LgLineBytes) * 2 ^ LgLineBytes.
Proof.
  pose proof LgLineBytes_lt_AddrSz; pose proof LgLineBytes_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)); lia.
Qed.

(* ... of 2^LgNumLineTags capability slots each *)
Lemma slotCount_lines : 2 ^ TagAddrWidth = 2 ^ (AddrSz - LgLineBytes) * 2 ^ LgNumLineTags.
Proof.
  pose proof LgLineBytes_lt_AddrSz; pose proof LgNumLineTags_nonneg.
  rewrite <- Z.pow_add_r by lia; apply (f_equal (Z.pow 2)).
  pose proof invariant_TagAddrWidth; pose proof invariant_LgNumLineTags; lia.
Qed.

Lemma capBytes_le_lineBytes : 2 ^ LgNumBytesFullCapSz <= 2 ^ LgLineBytes.
Proof. pose proof invariant_geometry; apply Z.pow_le_mono_r; lia. Qed.

Lemma lineBytes_lt_addrBytes : 2 ^ LgLineBytes < 2 ^ AddrSz.
Proof. pose proof invariant_geometry; apply Z.pow_lt_mono_r; lia. Qed.

Lemma lineBytes_succ : 2 ^ (LgLineBytes + 1) = 2 * 2 ^ LgLineBytes.
Proof. rewrite Z.pow_add_r by (pose proof LgLineBytes_nonneg; lia); lia. Qed.

Lemma capBytes_succ : 2 ^ (LgNumBytesFullCapSz + 1) = 2 * 2 ^ LgNumBytesFullCapSz.
Proof. rewrite Z.pow_add_r by (pose proof LgNumBytesFullCapSz_nonneg; lia); lia. Qed.

(* An access of size code `sz` covers 1 .. 2^LgNumBytesFullCapSz bytes *)
Lemma size_pow_bound : forall sz, 0 <= sz < 2 ^ LgLgNumBytesFullCapSz -> 1 <= 2 ^ sz <= 2 ^ LgNumBytesFullCapSz.
Proof.
  intros sz Hs; rewrite (proj2 invariant_sizes) in Hs; split.
  - apply (Z.pow_le_mono_r 2 0 sz); lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

(* The line and slot counts as naturals *)
Lemma lineBytes_nat : LineBytes = Z.to_nat (2 ^ LgLineBytes).
Proof. rewrite <- invariant_LineBytes, Nat2Z.id; reflexivity. Qed.

Lemma numLineTags_nat : NumLineTags = Z.to_nat (2 ^ LgNumLineTags).
Proof. rewrite <- invariant_NumLineTags, Nat2Z.id; reflexivity. Qed.
