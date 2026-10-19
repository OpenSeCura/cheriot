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
From Cheriot Require Import SpecDefines FunctionalUnits ShiftFifo.

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

Definition NumFetchParcels : nat  := Eval compute in Z.to_nat (FullCapSz / CompInstSz).
Definition LgFetchParcels  : Z    := Eval compute in Z.log2_up (FullCapSz / CompInstSz).
Definition FetchPacket     : Kind := Array NumFetchParcels (Bit CompInstSz).

Definition PreBranchInfo := STRUCT_TYPE {
  "isCjal"   :: Bool ;
  "isBranch" :: Bool ;
  "isCjalr"  :: Bool ;
  "isCall"   :: Bool ;
  "isReturn" :: Bool
}.

Definition FetchBufEntry := STRUCT_TYPE {
  "pcAddr"     :: Addr ;
  "predPc"     :: Addr ;
  "exitParcel" :: Bit LgFetchParcels ;
  "execEpoch"  :: Epoch ;
  "predEpoch"  :: Epoch ;
  "fetchExc"   :: FetchException
}.

Definition AssembledInst := STRUCT_TYPE {
  "fetchOut"  :: FetchOut ;
  "predPc"    :: Addr ;
  "execEpoch" :: Epoch
}.

Definition DecodeToAluEntry := STRUCT_TYPE {
  "aluIn"     :: AluInInstGroup ;
  "predPc"    :: Addr ;
  "execEpoch" :: Epoch
}.

(* ===========================================================================
 * Pipeline Stage Interfaces
 * =========================================================================== *)

Record FetchIfc {ty : Kind -> Type} := {
  fetchTree           : Tree DomainElem ;
  fetch_instFirst     : Action ty fetchTree (Option AssembledInst) ;
  fetch_instDeq       : Action ty fetchTree (Bit 0) ;
  fetch_clearStraddle : Action ty fetchTree (Bit 0) ;
  fetch_writeFetchPc  : ty Addr -> Action ty fetchTree (Bit 0)
}.

Record DecodeIfc {ty : Kind -> Type} := {
  decodeTree   : Tree DomainElem ;
  decode_first : Action ty decodeTree (Option DecodeToAluEntry) ;
  decode_deq   : Action ty decodeTree (Bit 0)
}.

Record ExecuteIfc {ty : Kind -> Type} := {
  executeTree             : Tree DomainElem ;
  execute_readExecEpoch   : Action ty executeTree Epoch ;
  execute_readFenceIPend  : Action ty executeTree Bool ;
  execute_clearFenceIPend : Action ty executeTree (Bit 0)
}.

Record DeferredIfc {ty : Kind -> Type} := {
  deferredTree     : Tree DomainElem ;
  deferred_isEmpty : Action ty deferredTree Bool ;
  deferred_isFull  : Action ty deferredTree Bool ;
  deferred_enq     : ty DeferredReq -> Action ty deferredTree (Bit 0)
}.

(* ===========================================================================
 * Special Register Wait-Bit & Stall Lists
 * =========================================================================== *)

Definition inStringList (s : string) (ls : list string) : bool :=
  existsb (String.eqb s) ls.

Definition stallUntilEmptyScrNames : list string :=
  [ "MePrevPcc" ].

Definition stallUntilEmptyCsrNames : list string :=
  [ "minstret" ; "minstreth" ; "mshwm" ; "mip" ].

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
                               (enumerate CsrTable))).

Definition isStallUntilEmptyScr (ty : Kind -> Type) (idx : ty (Bit ScrIdxSz)) : Expr ty Bool :=
  Or (map (fun i => Eq #idx $i) stallUntilEmptyScrIndices).

Definition isStallUntilEmptyCsr (ty : Kind -> Type) (idx : ty (Bit CsrIdxSz)) : Expr ty Bool :=
  Or (map (fun i => Eq #idx $i) stallUntilEmptyCsrIndices).

Section IndexedWaitBitHelpers.
  Variable ty : Kind -> Type.

  Fixpoint readIndexedWaitBitHelper (acc : list (Expr ty Bool)) {sz : Z} {t : Tree DomainElem}
    (indexedPaths : list (Z * RegOfKind (t:=t) Bool))
    (idx : ty (Bit sz)) : Action ty t Bool :=
    match indexedPaths with
    | [] => Return (Or acc)
    | (regIdx, rk) :: rest =>
        ReadReg "" rk.(rk_path) (fun val_ty =>
          let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
          let casted_ty := eq_rect (regKind (getRegFromPath rk.(rk_path))) (fun K => ty K) val_ty _ pf_eq in
          let iteVal := ITE0 (Eq #idx $regIdx) (Var _ _ casted_ty) in
          readIndexedWaitBitHelper (iteVal :: acc) rest idx
        )
    end.

  Definition readIndexedWaitBit {sz : Z} {t : Tree DomainElem} :=
    @readIndexedWaitBitHelper (@nil (Expr ty Bool)) sz t.

  Fixpoint writeIndexedWaitBit {sz : Z} {t : Tree DomainElem}
    (indexedPaths : list (Z * RegOfKind (t:=t) Bool))
    (idx : ty (Bit sz))
    (newVal : ty Bool) : Action ty t (Bit 0) :=
    match indexedPaths with
    | [] => Retv
    | (regIdx, rk) :: rest =>
        let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
        let castedVal := eq_rect Bool (fun K => Expr ty K) #newVal _ (eq_sym pf_eq) in
        IfElse EmptyString (Eq #idx $regIdx)
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
    Node "" [
      Node "gprs" gprWaitLeaves ;
      Node "scrs" scrWaitLeaves ;
      Node "csrs" csrWaitLeaves
    ].

  Definition np_waitGprs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree ".gprs").
  Definition np_waitScrs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree ".scrs").
  Definition np_waitCsrs : NodePath waitBitsTree := Eval cbn in (getNodePath waitBitsTree ".csrs").

  Definition gprWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbv in (map (embedRegOfKind np_waitGprs)
                     (getTreeRegsOfKind Bool (getNode np_waitGprs))).

  Definition scrWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbv in (map (embedRegOfKind np_waitScrs)
                     (getTreeRegsOfKind Bool (getNode np_waitScrs))).

  Definition csrWaitPathsWithKind : list (RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbv in (map (embedRegOfKind np_waitCsrs)
                     (getTreeRegsOfKind Bool (getNode np_waitCsrs))).

  Definition scrWaitIndexedPaths : list (Z * RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbv in (combine (map snd waitScrEntries) scrWaitPathsWithKind).

  Definition csrWaitIndexedPaths : list (Z * RegOfKind (t:=waitBitsTree) Bool) :=
    Eval cbv in (combine (map snd waitCsrEntries) csrWaitPathsWithKind).

  Definition readGprWaitBit (ty : Kind -> Type) (idx : ty (Bit RegIdxSzReal))
    : Action ty waitBitsTree Bool :=
    readRegsList gprWaitPathsWithKind #idx.

  Definition writeGprWaitBit (ty : Kind -> Type) (idx : ty (Bit RegIdxSzReal)) (val : ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeRegsList gprWaitPathsWithKind #idx #val.

  Definition readScrWaitBit (ty : Kind -> Type) (idx : ty (Bit ScrIdxSz))
    : Action ty waitBitsTree Bool :=
    readIndexedWaitBit scrWaitIndexedPaths idx.

  Definition writeScrWaitBit (ty : Kind -> Type) (idx : ty (Bit ScrIdxSz)) (val : ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeIndexedWaitBit scrWaitIndexedPaths idx val.

  Definition readCsrWaitBit (ty : Kind -> Type) (idx : ty (Bit CsrIdxSz))
    : Action ty waitBitsTree Bool :=
    readIndexedWaitBit csrWaitIndexedPaths idx.

  Definition writeCsrWaitBit (ty : Kind -> Type) (idx : ty (Bit CsrIdxSz)) (val : ty Bool)
    : Action ty waitBitsTree (Bit 0) :=
    writeIndexedWaitBit csrWaitIndexedPaths idx val.

  Definition setDstWaitBits (ty : Kind -> Type)
    (writesGpr : ty Bool) (gprIdx : ty (Bit RegIdxSzReal))
    (writesScr : ty Bool) (scrIdx : ty (Bit ScrIdxSz))
    (writesCsr : ty Bool) (csrIdx : ty (Bit CsrIdxSz))
    (val : ty Bool) : Action ty waitBitsTree (Bit 0) :=
    If #writesGpr Then (
      writeGprWaitBit gprIdx val
    ) ;
    If #writesScr Then (
      writeScrWaitBit scrIdx val
    ) ;
    If #writesCsr Then (
      writeCsrWaitBit csrIdx val
    ) ;
    Retv.

  (* 2. Core Tree *)
  Definition coreTree (rfTree bpTree memTree fetchTree decodeTree executeTree deferredTree : Tree DomainElem) : Tree DomainElem :=
    Node "core" [
      Node "rf"       [ rfTree ] ;
      Node "waitBits" [ waitBitsTree ] ;
      Node "bp"       [ bpTree ] ;
      Node "mem"      [ memTree ] ;
      Node "fetch"    [ fetchTree ] ;
      Node "decode"   [ decodeTree ] ;
      Node "execute"  [ executeTree ] ;
      Node "deferred" [ deferredTree ]
    ].

End ImplCommon.
