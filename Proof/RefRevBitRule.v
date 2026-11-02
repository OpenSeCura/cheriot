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
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices RefRel RefRegion RefGhost RefFetch RefMemRel RefCoreRel.
From Cheriot.Proof Require Import RefPeriph RefReadRpPorts.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Local Abbreviation TS t := (TreeState ElemState t).

(* The software rule on revocation bits (`RevBitRuleStep`, approved by the user) and the variant of
 * `StepOK` for the impl rules that need it (the store commits). The rule speaks about the impl
 * memory: the line contents its accepted writes give (`implLineContent`). *)

Section RevBitRule.
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

  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation ITree :=
    (ImplTree pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
              mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation STree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation envI :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwcs).
  Local Abbreviation envS := (specEnv pcAddrInit specRegions initLine fwcs).
  Local Abbreviation specActs := (@spec pcAddrInit config specRegions clintS revSpec plicS type).
  Local Abbreviation REL :=
    (RefRel pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwcs).
  Local Abbreviation iRegionsA := (iRegions pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA).
  Local Abbreviation IMem := (TS (implRegionsTree implRegions)).

  (* A single-line read of `size` bytes at `addr` from the impl memory (as `memValAt` on the spec) *)
  Definition implMemValAt (mi : IMem) (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz))
    : type FullCapWithTag :=
    evalLetExpr (memAssembleCapRead (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)
                   (Var type CapPacket (specPkt addr (implLineContent initLine implRegions mi (lineOf false addr))))).

  (* The rev bit of base `b` in the impl memory (as `revBitOf` on the spec) *)
  Definition implRevBitOf (mi : IMem) (b : type (Bit (AddrSz + 1))) : bool :=
    let lookup := evalLetExpr (@computeRevBitAddr config type b) in
    let v := implMemValAt mi (revByteAddrOf config b) byteSz in
    evalExpr (extractRevBit lookup (TruncLsb (AddrSz - 8) 8 (##v`"addr"))).

  (* The rule: a step that turns rev bit `b` from 1 to 0 happens only when the memory before the
   * step holds no tagged capability with base `b` that needs a revocation check *)
  Definition RevBitRuleStep (s s' : TS ITree) : Prop :=
    forall b, implRevBitOf (iRegionsA s) b = true -> implRevBitOf (iRegionsA s') b = false ->
      forall sa : bits TagAddrWidth,
        capNeedsCheck config (implMemValAt (iRegionsA s) (scanFull sa) capSz) = true ->
        capBase (implMemValAt (iRegionsA s) (scanFull sa) capSz) <> b.

  (* `StepOK` for impl steps that obey the rule *)
  Definition StepOKR (act : Action type ITree (Bit 0)) : Prop :=
    forall (s1 s1' : TS ITree) (s2 : TS STree),
      SemAction envI act s1 s1' Zmod.zero ->
      RevBitRuleStep s1 s1' ->
      REL s1 s2 ->
      exists s2', SemActions envS specActs s2 s2' /\ REL s1' s2'.

  Local Abbreviation STEPOK := (StepOK pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                  mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
                                  clintS clint plicS plic initLine fwcs).

  Lemma StepOKR_of : forall act, STEPOK act -> StepOKR act.
  Proof. intros act H s1 s1' s2 Hs _ Hr; exact (H s1 s1' s2 Hs Hr). Qed.
End RevBitRule.
