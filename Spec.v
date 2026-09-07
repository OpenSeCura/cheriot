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

From Stdlib Require Import String List ZArith Zmod Psatz Bool.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchMemory SpecDevice Clint SpecRevoker Plic Uart.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * System Tree Definition
 * =========================================================================== *)

Definition specSysTree (regions : list MemRegion) : Tree Elem :=
  Node "sys" [
    specCoreTree regions
  ].

Section Spec.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : ClintInstance regions.
  Variable rev : RevokerInstance regions.
  Variable uart : UartInstance regions.
  Variable plic : PlicInstance (S (length (collectIrqActions regions))) regions.
  Local Notation sysTree := (specSysTree regions).

  Section Ty.
    Variable ty : Kind -> Type.

  Definition np_core : NodePath sysTree :=
    getNodePath sysTree "sys.core".

  Definition np_rf : NodePath sysTree :=
    getNodePath sysTree "sys.core.rf".

  Definition np_mem : NodePath sysTree :=
    getNodePath sysTree "sys.core.mem".

(* ===========================================================================
 * Peripheral Background Rules & Interrupt Polling
 * =========================================================================== *)

  Definition specTickCycle : Action ty sysTree (Bit 0) :=
    liftAction np_rf incrementMcycle.

  Definition specTickTimer : Action ty sysTree (Bit 0) :=
    liftAction np_mem (clintTickAction clint ty).

  (* Autonomous background revoker step *)
  Definition specRevokerStep : Action ty sysTree (Bit 0) :=
    liftAction np_mem (SpecRevoker.specRevokerStep rev config ty).

  (* Autonomous background UART steps *)
  Definition specUartTxStep : Action ty sysTree (Bit 0) :=
    liftAction np_mem (uartTxStepAction uart ty).

  Definition specUartRxStep : Action ty sysTree (Bit 0) :=
    liftAction np_mem (uartRxStepAction uart ty).

  (* Autonomous background PLIC steps *)
  Definition specPlicPendingsStep : Action ty sysTree (Bit 0) :=
    liftAction np_mem (plicPendingsStep plic ty eq_refl).

  Definition specPlicClaimStep : Action ty sysTree (Bit 0) :=
    liftAction np_mem (plicClaimStep plic ty).

  Definition updateMipBit (bitIdx : Expr ty (Bit LgXlen)) (bitVal : Expr ty Bool) : Action ty sysTree (Bit 0) :=
    liftAction np_rf (
      LetA currMip : Bit Xlen <- readRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz)) ;
      Let currArr : Array (Z.to_nat Xlen) Bool <- FromBit (Array (Z.to_nat Xlen) Bool) #currMip ;
      Let updArr  : Array (Z.to_nat Xlen) Bool <- UpdateArray #currArr bitIdx bitVal ;
      Act (writeRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz)) (ToBit #updArr)) ;
      Retv
    ).

  (* Rule: Reads PLIC MEIP and updates mip.meip *)
  Definition specExternalInterruptRule : Action ty sysTree (Bit 0) :=
    LetA meipVal : Bool <- liftAction np_mem (plicMeipSystem plic ty) ;
    updateMipBit $MEIP_Bit #meipVal.

  (* Rule: Reads mtimecmp CSR and mtime MMIO register to update mip.mtip *)
  Definition specTimerInterruptRule : Action ty sysTree (Bit 0) :=
    LetA lo : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mtimecmp") : Expr _ (Bit CsrIdxSz))) ;
    LetA hi : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mtimecmph") : Expr _ (Bit CsrIdxSz))) ;
    Let mtimecmpDXlen : Bit DXlen <- {< #hi, #lo >} ;
    LetA mtimeDXlen   : Bit DXlen <- liftAction np_mem (readClintMtimeAction clint ty) ;
    Let mtipVal       : Bool      <- Sge #mtimeDXlen #mtimecmpDXlen ;
    updateMipBit $MTIP_Bit #mtipVal.

(* ===========================================================================
 * Atomic Core Pipeline Step (specStep)
 * =========================================================================== *)

  Definition specStep : Action ty sysTree (Bit 0) :=
    (* 1. Fetch *)
    LetA fetchOut : FetchOut <- liftAction np_core (specFetch regions ty) ;

    (* 2. Decode *)
    LetL regReadIn : RegReadIn <- wrappedDecode fetchOut ;

    (* 3. Register Read (GPRs, SCRs, CSRs, mstatus) *)
    LetA aluInInstGroup : AluInInstGroup <- liftAction np_rf (regRead regReadIn) ;

    (* 4. Alu Control, Routing, and Execution *)
    Let  instGroup : InstGroup <- ##aluInInstGroup`"instGroup" ;
    LetL aluCtrl   : AluControl <- decodeInstGroup instGroup ;
    Let  aluIn     : AluIn <- STRUCT {
      "cs2Idx"              ::= ##aluInInstGroup`"cs2Idx" ;
      "writesCd"            ::= ##aluInInstGroup`"writesCd" ;
      "inst"                ::= ##aluInInstGroup`"inst" ;
      "decodeExc"           ::= ##aluInInstGroup`"decodeExc" ;
      "fetchExc"            ::= ##aluInInstGroup`"fetchExc" ;
      "pcc"                 ::= ##aluInInstGroup`"pcc" ;
      "cs1"                 ::= ##aluInInstGroup`"cs1" ;
      "cs2"                 ::= ##aluInInstGroup`"cs2" ;
      "currInterruptStatus" ::= ##aluInInstGroup`"currInterruptStatus" ;
      "aluControl"          ::= #aluCtrl
    } ;
    LetL routingOut : AluOut      <- AluRouting aluIn ;
    LetL aluOut     : AluOutUnion <- Alu routingOut ;

    (* 5. Commit Non-Deferred (GPRs, SCRs, CSRs, PCC, Traps) *)
    LetA execOut : ExecuteOut <- liftAction np_rf (executeNonDeferred aluOut) ;

    (* 6. Commit Deferred (Memory Loads, Stores, Fences) *)
    Let  reqOpt  : Option DeferredReq <- ##execOut`"deferredReq" ;
    Act (liftAction np_core (specExecuteDeferred config regions reqOpt)) ;
    Retv.

  End Ty.

(* ===========================================================================
 * Top-Level Specification Module (spec)
 * =========================================================================== *)

  Definition spec : Mod sysTree :=
    fun ty => [
      specStep ty ;
      specTickCycle ty ;
      specTickTimer ty ;
      specRevokerStep ty ;
      specUartTxStep ty ;
      specUartRxStep ty ;
      specPlicPendingsStep ty ;
      specPlicClaimStep ty ;
      specExternalInterruptRule ty ;
      specTimerInterruptRule ty
    ].

End Spec.
