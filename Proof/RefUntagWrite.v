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

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics HelperLemmas.
From Cheriot Require Import SpecDefines SpecDevice.
From Cheriot.Proof Require Import RefConsts StateRel SimDevices RefRel RefFetch RefCoreRel RefBits RefSpecRead
  RefWriteRqPorts RefSnoopMiss.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* Milestone 4, the revoker's untagging write (byte level): writing back the capability just read,
 * with its tag cleared, changes no data byte of memory.
 * 1. The packet: read and write are inverse on the data bytes (`untag_pkt`, through Guru's
 *    `evalFromBit_evalToBit`/`evalToBit_evalFromBit`).
 * 2. The line: the packet's bytes go back where they were read (`rtData_ok`, a computation over
 *    the capability slots of a line, in the style of the mask checks of RefConsts.v). *)

(* --- 1. Splitting a bit vector and joining the halves --- *)

Lemma app_firstn_lastn :
  forall lsb msb (x : bits (lsb + msb)), 0 <= lsb -> 0 <= msb ->
    Zmod.app (Zmod.firstn lsb x) (Zmod_lastn msb x) = x.
Proof.
  intros lsb msb x Hl Hm.
  apply Zmod.to_Z_inj.
  rewrite bits.unsigned_app by lia.
  rewrite bits.unsigned_firstn.
  unfold Zmod_lastn; rewrite Zmod.to_Z_of_Z.
  replace (lsb + msb - msb) with lsb by lia.
  pose proof (Zmod.to_Z_range x) as Hx.
  set (v := Zmod.to_Z x) in *.
  apply Z.bits_inj'; intros i Hi.
  rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i lsb) as [Hlt | Hge].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftl_spec_low by lia.
    apply orb_false_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.shiftl_spec_high by lia; cbn [orb].
    destruct (Z.lt_ge_cases (i - lsb) msb) as [Hlt2 | Hge2].
    + rewrite Z.mod_pow2_bits_low by lia.
      rewrite Z.shiftr_spec by lia.
      f_equal; lia.
    + rewrite Z.mod_pow2_bits_high by lia.
      symmetry.
      assert (Hv : v = v mod 2 ^ (lsb + msb)) by (symmetry; apply Z.mod_small; lia).
      rewrite Hv, Z.mod_pow2_bits_high by lia; reflexivity.
Qed.

Lemma app_zero_l : forall m (x : bits m), 0 <= m -> @Zmod.app 0 m Zmod.zero x = x.
Proof.
  intros m x Hm; apply Zmod.to_Z_inj.
  rewrite bits.unsigned_app by lia.
  rewrite Zmod.to_Z_0, Z.shiftl_0_r, Z.lor_0_l; reflexivity.
Qed.

(* --- 2. The line: the packet's bytes go back where they were read --- *)

Local Open Scope string_scope.

(* The data bytes of a line after writing back, at slot offset `o`, the capability bytes read there *)
Definition rtData (o : bits LgLineBytes) (d : type (Array LineBytes (Bit 8))) : list (type (Bit 8)) :=
  (maskUpdateSameTuple
     (evalLetExpr (ArrayRotl (Var type (Array LineBytes (Bit 8))
                                (evalExpr (embedCapBytes LineBytes
                                             (Var type (Array (Z.to_nat NumBytesFullCapSz) (Bit 8))
                                                (evalExpr (slice (Var type (Array LineBytes (Bit 8)) d)
                                                             (Var type (Bit LgLineBytes) o)
                                                             (Z.to_nat NumBytesFullCapSz)))))))
                             (Var type (Bit LgLineBytes) o)))
     d
     (evalLetExpr (dataMaskO type (Const type Bool false) (Var type (Bit LgLineBytes) o)
                     (Var type (Bit LgLgNumBytesFullCapSz) capSz)))).(tupleElems).

Lemma list_map_nth_seq :
  forall {A : Type} (l : list A) (z : A), l = map (fun i => nth i l z) (seq 0 (length l)).
Proof.
  intros A l z; apply nth_ext with (d := z) (d' := z).
  - rewrite length_map, length_seq; reflexivity.
  - intros n Hn; symmetry.
    rewrite (nth_indep _ z (nth 0 l z)) by (rewrite length_map, length_seq; exact Hn).
    rewrite map_nth with (d := 0%nat), seq_nth by exact Hn; reflexivity.
Qed.

Lemma rtData_slot :
  forall k (d : type (Array LineBytes (Bit 8))), (k < NumLineTags)%nat ->
    rtData (Zmod.of_Z _ (Z.of_nat k * 2 ^ LgNumBytesFullCapSz)) d = d.(tupleElems).
Proof.
  intros k [l Hl] Hk; cbn [tupleElems].
  assert (Hlen : length l = LineBytes) by (apply Nat.eqb_eq, Is_true_eq_true; exact Hl).
  assert (Hl' : Is_true (length (map (fun i => nth i l Zmod.zero) (seq 0 LineBytes)) =? LineBytes)%nat)
    by (rewrite length_map, length_seq, Nat.eqb_refl; exact I).
  assert (Ed : @Build_SameTuple _ LineBytes l Hl = @Build_SameTuple _ LineBytes _ Hl').
  { apply SameTuple_ext; cbn [tupleElems]; rewrite <- Hlen; apply list_map_nth_seq. }
  rewrite Ed; clear Ed Hl.
  transitivity (map (fun i => nth i l Zmod.zero) (seq 0 LineBytes));
    [| rewrite <- Hlen; symmetry; apply list_map_nth_seq].
  assert (Hin : In k (seq 0 NumLineTags)) by (apply in_seq; lia).
  clear Hk Hlen; revert Hl' Hin.
  cbv [NumLineTags]; cbn [seq In].
  intros Hp Hin.
  repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity |]).
  destruct Hin.
Qed.

(* --- 3. The packet: the bytes written back are the bytes read --- *)

Lemma untag_pkt :
  forall (a : type Addr) (pkt : type CapPacket),
    evalExpr (TruncLsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr a)) = Zmod.zero ->
    (disassembleW a (untagCap (evalLetExpr (memAssembleCapRead (Var type Addr a)
                                              (Var type (Bit LgLgNumBytesFullCapSz) capSz)
                                              (Var type CapPacket pkt)))) capSz).(Fst) = pkt.(Fst).
Proof.
  intros a pkt Ha.
  unfold disassembleW, memDisassembleCapWrite, memAssembleCapRead, untagCap; cbn [evalLetExpr].
  cbn -[evalToBit evalFromBit Zmod.app Zmod.firstn Zmod_lastn isEq].
  change (Zmod.firstn LgNumBytesFullCapSz a) with (evalExpr (TruncLsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr a))).
  rewrite Ha.
  match goal with |- context [if ?c then _ else _] => replace c with true by (vm_compute; reflexivity) end.
  cbv beta iota.
  rewrite evalToBit_evalFromBit by (vm_compute; reflexivity).
  rewrite app_zero_l by (cbv; congruence).
  match goal with |- evalFromBit ?w = _ =>
    assert (Ew : w = @evalToBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) (Fst pkt))
      by exact (app_firstn_lastn AddrSz CapSz _ ltac:(cbv; congruence) ltac:(cbv; congruence));
    rewrite Ew end.
  exact (@evalFromBit_evalToBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) (Fst pkt) ltac:(vm_compute; reflexivity)).
Qed.

(* --- 4. The whole line, then the whole memory --- *)

Lemma scanFull_aligned :
  forall sa, evalExpr (TruncLsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr (scanFull sa))) = Zmod.zero.
Proof.
  intros sa; apply Zmod.to_Z_inj.
  rewrite to_Z_TruncLsb, to_Z_Var, to_Z_scanFull, Zmod.to_Z_0.
  apply Z.mod_mul; pose proof capBytes_pos; lia.
Qed.

(* The line offset of slot `sa`: slot `sa mod 2^LgNumLineTags` of its line *)
Lemma offset_scanFull :
  forall sa, evalExpr (memLineOffset (Var type Addr (scanFull sa))) =
             Zmod.of_Z _ (Z.of_nat (Z.to_nat (Zmod.to_Z sa mod 2 ^ LgNumLineTags)) * 2 ^ LgNumBytesFullCapSz).
Proof.
  intros sa; apply Zmod.to_Z_inj.
  rewrite to_Z_offset, to_Z_scanFull, Zmod.to_Z_of_Z.
  pose proof capBytes_pos; pose proof lineTags_pos.
  pose proof (Z.mod_pos_bound (Zmod.to_Z sa) _ lineTags_pos).
  rewrite Z2Nat.id by lia.
  rewrite lineBytes_split, Z.mul_mod_distr_r by lia.
  symmetry; apply Z.mod_small; nia.
Qed.

(* The data bytes of a line write: the packet's bytes rotated to the line offset *)
Lemma buildW_data :
  forall b addr pkt size,
    (buildW b addr pkt size).(Snd).(Fst) =
    evalLetExpr (ArrayRotl (Var type (Array LineBytes (Bit 8))
                              (evalExpr (embedCapBytes LineBytes
                                           (Var type (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) pkt.(Fst)))))
                           (Var type (Bit LgLineBytes) (evalExpr (memLineOffset (Var type Addr addr))))).
Proof. intros b addr pkt size; reflexivity. Qed.

Lemma untag_line_data :
  forall rp sa,
    (applyLineWriteRq (lineOf false (scanFull sa))
       (buildW false (scanFull sa)
          (disassembleW (scanFull sa)
             (untagCap (evalLetExpr (memAssembleCapRead (Var type Addr (scanFull sa))
                                       (Var type (Bit LgLgNumBytesFullCapSz) capSz)
                                       (Var type CapPacket (specPkt (scanFull sa) rp))))) capSz) capSz) rp).(Fst) =
    rp.(Fst).
Proof.
  intros rp sa.
  set (a := scanFull sa).
  set (pkt' := disassembleW a _ capSz).
  unfold applyLineWriteRq; cbv zeta.
  rewrite buildW_addr, Zmod.eqb_refl; cbn [Fst Snd].
  apply SameTuple_ext.
  rewrite buildW_dataMask.
  set (o := evalExpr (memLineOffset (Var type Addr a))).
  rewrite buildW_data; fold o.
  assert (Ep : pkt'.(Fst) = (specPkt a rp).(Fst)) by exact (untag_pkt a _ (scanFull_aligned sa)).
  rewrite Ep.
  assert (Es : (specPkt a rp).(Fst) =
               evalExpr (slice (Var type (Array LineBytes (Bit 8)) rp.(Fst)) (Var type (Bit LgLineBytes) o)
                           (Z.to_nat NumBytesFullCapSz)))
    by reflexivity.
  rewrite Es.
  assert (Eo : o = Zmod.of_Z _ (Z.of_nat (Z.to_nat (Zmod.to_Z sa mod 2 ^ LgNumLineTags)) * 2 ^ LgNumBytesFullCapSz))
    by exact (offset_scanFull sa).
  clearbody o; subst o.
  pose proof (winTagIdx_lt (scanFull sa)) as Hlt; rewrite winTagIdx_scanFull in Hlt.
  exact (rtData_slot _ rp.(Fst) Hlt).
Qed.

Section Memory.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation memValAtA := (memValAt pre post revBase revPfB revPfA initLine).
  Local Abbreviation revBitOfA := (revBitOf config pre post revBase revPfB revPfA initLine).

  (* The spec memory after the revoker's untagging write of slot `sa` *)
  Definition untagWrite (m : TS (specMemTree specRegions)) (sa : bits TagAddrWidth) : TS (specMemTree specRegions) :=
    specWriteLine specRegions (lineOf false (scanFull sa))
      (buildW false (scanFull sa) (disassembleW (scanFull sa) (untagCap (memValAtA m (scanFull sa) capSz)) capSz) capSz) m.

  Lemma lineContent_untag :
    forall m sa L,
      lineKind specRegions (lineOf false (scanFull sa)) = Some true -> lineUnique specRegions (lineOf false (scanFull sa)) ->
      (lineContent initLine specRegions (untagWrite m sa) L).(Fst) = (lineContent initLine specRegions m L).(Fst).
  Proof.
    intros m sa L Hk Hu; unfold untagWrite.
    rewrite (lineContent_specWrite initLine specRegions _ _ m L (buildW_addr _ _ _ _) Hk Hu).
    destruct (Zmod.eqb (lineOf false (scanFull sa)) L) eqn:E.
    - apply Zmod.eqb_eq in E; subst L.
      exact (untag_line_data _ sa).
    - rewrite applyLineWriteRq_other; [reflexivity | rewrite buildW_addr; exact E].
  Qed.

  (* A read's address field depends on the data bytes only *)
  Lemma memValAt_addr_ext :
    forall m m' a sz,
      (forall L, (lineContent initLine specRegions m' L).(Fst) = (lineContent initLine specRegions m L).(Fst)) ->
      (memValAtA m' a sz).(Snd).(Snd).(Fst) = (memValAtA m a sz).(Snd).(Snd).(Fst).
  Proof.
    intros m m' a sz H; unfold memValAt.
    specialize (H (lineOf false a)).
    destruct (lineContent initLine specRegions m' (lineOf false a)) as [d1 [t1 []]].
    destruct (lineContent initLine specRegions m (lineOf false a)) as [d2 [t2 []]].
    cbn [Fst] in H; subst d2; reflexivity.
  Qed.

  Lemma revBitOf_dataExt :
    forall m m' b,
      (forall L, (lineContent initLine specRegions m' L).(Fst) = (lineContent initLine specRegions m L).(Fst)) ->
      revBitOfA m' b = revBitOfA m b.
  Proof.
    intros m m' b H; unfold revBitOf; cbv zeta.
    pose proof (memValAt_addr_ext m m' (revByteAddrOf config b) byteSz H) as E.
    destruct (memValAtA m' (revByteAddrOf config b) byteSz) as [t1 [c1 [a1 []]]].
    destruct (memValAtA m (revByteAddrOf config b) byteSz) as [t2 [c2 [a2 []]]].
    cbn [Fst Snd] in E; subst a2; reflexivity.
  Qed.

  Lemma revBitOf_untag :
    forall m sa b,
      lineKind specRegions (lineOf false (scanFull sa)) = Some true -> lineUnique specRegions (lineOf false (scanFull sa)) ->
      revBitOfA (untagWrite m sa) b = revBitOfA m b.
  Proof. intros m sa b Hk Hu; apply revBitOf_dataExt; intros L; exact (lineContent_untag m sa L Hk Hu). Qed.
End Memory.
