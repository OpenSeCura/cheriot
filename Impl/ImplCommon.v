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

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Hardware Pipeline Parameters & Data Types
 * =========================================================================== *)

Definition EpochSz : Z := 1.
Definition Epoch   : Kind := Bit EpochSz.

Definition FetchBufEntry := STRUCT_TYPE {
  "pcAddr"   :: Addr ;
  "predPc"   :: Addr ;
  "epoch"    :: Epoch ;
  "fetchExc" :: FetchException
}.

Definition DecodeToAluEntry := STRUCT_TYPE {
  "aluIn"  :: AluInInstGroup ;
  "predPc" :: Addr ;
  "epoch"  :: Epoch
}.

(* ===========================================================================
 * Special Register Wait-Bit & Stall Lists
 * =========================================================================== *)

Definition inStringList (s : string) (ls : list string) : bool :=
  existsb (String.eqb s) ls.

Definition stallUntilEmptyScrNames : list string :=
  [ "MePrevPcc" ].

Definition stallUntilEmptyCsrNames : list string :=
  [ "minstret" ; "minstreth" ; "mshwm" ].

Definition neverWaitCsrNames : list string :=
  [ "mcycle" ; "mcycleh" ].

Definition noWaitScrNames : list string :=
  stallUntilEmptyScrNames.

Definition noWaitCsrNames : list string :=
  neverWaitCsrNames ++ stallUntilEmptyCsrNames.

Definition waitScrEntries : list (ScrEntry * Z) :=
  filter (fun '(e, _) => negb (inStringList e.(scrName) noWaitScrNames))
         (enumerate (ScrTable 0)).

Definition waitCsrEntries : list (CsrEntry * Z) :=
  filter (fun '(e, _) => negb (inStringList e.(csrName) noWaitCsrNames))
         (enumerate PhysicalCsrTable).

Definition stallUntilEmptyScrIndices : list Z :=
  Eval cbn in (map snd (filter (fun '(e, _) => inStringList e.(scrName) stallUntilEmptyScrNames)
                               (enumerate (ScrTable 0)))).

Definition stallUntilEmptyCsrIndices : list Z :=
  Eval cbn in (map snd (filter (fun '(e, _) => inStringList e.(csrName) stallUntilEmptyCsrNames)
                               (enumerate PhysicalCsrTable))).

Definition isStallUntilEmptyScr (ty : Kind -> Type) (idx : Expr ty (Bit ScrIdxSz)) : Expr ty Bool :=
  Or (map (fun i => Eq idx $i) stallUntilEmptyScrIndices).

Definition isStallUntilEmptyCsr (ty : Kind -> Type) (idx : Expr ty (Bit CsrIdxSz)) : Expr ty Bool :=
  Or (map (fun i => Eq idx $i) stallUntilEmptyCsrIndices).

Section IndexedWaitBitHelpers.
  Variable ty : Kind -> Type.

  Fixpoint readIndexedWaitBitHelper (acc : list (Expr ty Bool)) {sz : Z} {t : Tree DomainElem}
    (indexedPaths : list (Z * RegOfKind (t:=t) Bool))
    (idx : Expr ty (Bit sz)) : Action ty t Bool :=
    match indexedPaths with
    | [] => Return (Or acc)
    | (regIdx, rk) :: rest =>
        ReadReg "" rk.(rk_path) (fun val_ty =>
          let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
          let casted_ty := eq_rect (regKind (getRegFromPath rk.(rk_path))) (fun K => ty K) val_ty _ pf_eq in
          let iteVal := ITE0 (Eq idx $regIdx) (Var _ _ casted_ty) in
          readIndexedWaitBitHelper (iteVal :: acc) rest idx
        )
    end.

  Definition readIndexedWaitBit {sz : Z} {t : Tree DomainElem} :=
    @readIndexedWaitBitHelper (@nil (Expr ty Bool)) sz t.

  Fixpoint writeIndexedWaitBit {sz : Z} {t : Tree DomainElem}
    (indexedPaths : list (Z * RegOfKind (t:=t) Bool))
    (idx : Expr ty (Bit sz))
    (newVal : Expr ty Bool) : Action ty t (Bit 0) :=
    match indexedPaths with
    | [] => Retv
    | (regIdx, rk) :: rest =>
        let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
        let castedVal := eq_rect Bool (fun K => Expr ty K) newVal _ (eq_sym pf_eq) in
        IfElse EmptyString (Eq idx $regIdx)
          (WriteReg rk.(rk_path) castedVal Retv)
          Retv
          (fun _ => writeIndexedWaitBit rest idx newVal)
    end.
End IndexedWaitBitHelpers.

(* ===========================================================================
 * Hardware Pipeline State Trees & Register Accessors
 * =========================================================================== *)

Section ImplCommon.
  Variable dom : string.
  Variable pcAddrInit : Z.

  (* 1. Scoreboard (waitBits) *)
  Definition gprWaitLeaves : list (Tree DomainElem) :=
    map (fun '(_, idx) =>
      Leaf ("waitBit_" ++ hex_string_of_Z idx)%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (enumerate (repeat tt (Z.to_nat NumRegs))).

  Definition scrWaitLeaves : list (Tree DomainElem) :=
    map (fun '(e, _) =>
      Leaf ("waitBit_" ++ e.(scrName))%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) waitScrEntries.

  Definition csrWaitLeaves : list (Tree DomainElem) :=
    map (fun '(e, _) =>
      Leaf ("waitBit_" ++ e.(csrName))%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) waitCsrEntries.

  Definition waitBitsTree : Tree DomainElem :=
    Node "waitBits" [
      Node "gprs" gprWaitLeaves ;
      Node "scrs" scrWaitLeaves ;
      Node "csrs" csrWaitLeaves
    ].

  Definition np_waitGprs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree "waitBits.gprs").
  Definition np_waitScrs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree "waitBits.scrs").
  Definition np_waitCsrs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree "waitBits.csrs").

  Definition gprWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (map (embedRegOfKind np_waitGprs)
                     (getTreeRegsOfKind Bool (getNode np_waitGprs))).

  Definition scrWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (map (embedRegOfKind np_waitScrs)
                     (getTreeRegsOfKind Bool (getNode np_waitScrs))).

  Definition csrWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (map (embedRegOfKind np_waitCsrs)
                     (getTreeRegsOfKind Bool (getNode np_waitCsrs))).

  Definition scrWaitIndexedPaths : list (Z * RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (combine (map snd waitScrEntries) scrWaitPathsWithKind).

  Definition csrWaitIndexedPaths : list (Z * RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbn in (combine (map snd waitCsrEntries) csrWaitPathsWithKind).

  Definition readGprWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal))
    : Action ty waitBitsTree Bool :=
    readRegsList gprWaitPathsWithKind idx.

  Definition writeGprWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit RegIdxSzReal)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList gprWaitPathsWithKind idx val.

  Definition readScrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit ScrIdxSz))
    : Action ty waitBitsTree Bool :=
    readIndexedWaitBit scrWaitIndexedPaths idx.

  Definition writeScrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit ScrIdxSz)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeIndexedWaitBit scrWaitIndexedPaths idx val.

  Definition readCsrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit CsrIdxSz))
    : Action ty waitBitsTree Bool :=
    readIndexedWaitBit csrWaitIndexedPaths idx.

  Definition writeCsrWaitBit (ty : Kind -> Type) (idx : Expr ty (Bit CsrIdxSz)) (val : Expr ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeIndexedWaitBit csrWaitIndexedPaths idx val.

  Definition setDstWaitBits (ty : Kind -> Type)
    (writesGpr : Expr ty Bool) (gprIdx : Expr ty (Bit RegIdxSzReal))
    (wInfo : ty WaitSpecialInfo)
    (val : Expr ty Bool) : Action ty waitBitsTree (Bit 0) :=
    If writesGpr Then (
      writeGprWaitBit gprIdx val
    ) ;
    If (##wInfo`"writesScr") Then (
      writeScrWaitBit (##wInfo`"readWriteScrIdx") val
    ) ;
    If (##wInfo`"writesCsr") Then (
      writeCsrWaitBit (##wInfo`"writeCsrIdx") val
    ) ;
    Retv.

  (* 2. Core Tree *)
  Definition coreTree (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem) : Tree DomainElem :=
    Node "core" [
      rfTree dom pcAddrInit ;
      waitBitsTree ;
      Node "bp"       [ bpTree ] ;
      Leaf "currEpoch" (dom, EReg (Build_Reg Epoch (Some Zmod.zero) false)) ;
      Node "mem"      [ memTree ] ;
      Node "fetch"    [ fetchTree ] ;
      Node "decode"   [ decodeTree ] ;
      Node "deferred" [ deferredTree ]
    ].

  Definition pCurrEpoch (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem)
    : RegPath (coreTree bpTree memTree fetchTree decodeTree deferredTree) :=
    Eval cbn in (getChildRegPathTree (coreTree bpTree memTree fetchTree decodeTree deferredTree) "currEpoch").

  Definition readCurrEpoch (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem) (ty : Kind -> Type)
    : Action ty (coreTree bpTree memTree fetchTree decodeTree deferredTree) Epoch :=
    ReadReg "currEpoch" (pCurrEpoch bpTree memTree fetchTree decodeTree deferredTree) (fun v => Return #v).

  Definition writeCurrEpoch (bpTree memTree fetchTree decodeTree deferredTree : Tree DomainElem) (ty : Kind -> Type)
    (val : Expr ty Epoch) : Action ty (coreTree bpTree memTree fetchTree decodeTree deferredTree) (Bit 0) :=
    WriteReg (pCurrEpoch bpTree memTree fetchTree decodeTree deferredTree) val Retv.

End ImplCommon.
