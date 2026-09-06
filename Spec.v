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

Definition specSysTree (regions : list MemRegion) : Tree Elem :=
  Node "sys" [
    specCoreTree regions ;
    interruptsTree
  ].

Section Spec.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : ClintInstance regions.
  Variable rev : RevokerInstance regions.
  Variable uart : UartInstance regions.
  Variable numSources : nat.
  Variable plic : PlicInstance numSources regions.
  Variable pfPlicCount : length (collectIrqActions regions) = numSources.
  Variable ty : Kind -> Type.

  Local Notation sysTree := (specSysTree regions).

  Definition np_core : NodePath sysTree :=
    getNodePath sysTree "sys.core".

  Definition np_rf : NodePath sysTree :=
    getNodePath sysTree "sys.core.rf".

  Definition np_mem : NodePath sysTree :=
    getNodePath sysTree "sys.core.mem".

  Definition np_intr : NodePath sysTree :=
    getNodePath sysTree "sys.interrupts".

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

  (* Autonomous background PLIC step *)
  Definition specPlicStep : Action ty sysTree (Bit 0) :=
    liftAction np_mem (plicSampleAndStep plic ty pfPlicCount).

  (* Rule: Reads PLIC MEIP and updates mip.meip *)
  Definition specExternalInterruptRule : Action ty sysTree (Bit 0) :=
    LetA meipVal : Bool <- liftAction np_mem (plicMeipSystem plic ty) ;
    LetA currMip : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz))) ;
    Let currArr : Array (Z.to_nat Xlen) Bool <- FromBit (Array (Z.to_nat Xlen) Bool) #currMip ;
    Let idxMeip : Bit LgXlen <- $MEIP_Bit ;
    Let updArr  : Array (Z.to_nat Xlen) Bool <- UpdateArray #currArr #idxMeip #meipVal ;
    Act (liftAction np_rf (writeRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz)) (ToBit #updArr))) ;
    Retv.

  (* Rule: Reads mtimecmp CSR and mtime MMIO register to update mip.mtip *)
  Definition specTimerInterruptRule : Action ty sysTree (Bit 0) :=
    LetA lo : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mtimecmp") : Expr _ (Bit CsrIdxSz))) ;
    LetA hi : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mtimecmph") : Expr _ (Bit CsrIdxSz))) ;
    Let mtimecmpDXlen : Bit DXlen <- {< #hi, #lo >} ;
    LetA mtimeDXlen   : Bit DXlen <- liftAction np_mem (readClintMtimeAction clint ty) ;
    Let mtipVal       : Bool      <- Sge #mtimeDXlen #mtimecmpDXlen ;
    LetA currMip : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz))) ;
    Let currArr : Array (Z.to_nat Xlen) Bool <- FromBit (Array (Z.to_nat Xlen) Bool) #currMip ;
    Let idxMtip : Bit LgXlen <- $MTIP_Bit ;
    Let updArr  : Array (Z.to_nat Xlen) Bool <- UpdateArray #currArr #idxMtip #mtipVal ;
    Act (liftAction np_rf (writeRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz)) (ToBit #updArr))) ;
    Retv.

  Definition specReceiveInterrupts : Action ty sysTree (Bit 0) :=
    LetA meip    : Bool                       <- liftAction np_intr (Get meip <- "interrupts.meip_in" in interruptsTree ; Return #meip) ;
    LetA msip    : Bool                       <- liftAction np_intr (Get msip <- "interrupts.msip_in" in interruptsTree ; Return #msip) ;
    LetA currMip : Bit Xlen                   <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz))) ;
    Let  currArr : Array (Z.to_nat Xlen) Bool <- FromBit (Array (Z.to_nat Xlen) Bool) #currMip ;
    Let  idxMeip : Bit LgXlen                 <- $MEIP_Bit ;
    Let  idxMsip : Bit LgXlen                 <- $MSIP_Bit ;
    Let  arr1    : Array (Z.to_nat Xlen) Bool <- UpdateArray #currArr #idxMeip (Or [ #meip ; ReadArray #currArr #idxMeip ]) ;
    Let  arr2    : Array (Z.to_nat Xlen) Bool <- UpdateArray #arr1    #idxMsip (Or [ #msip ; ReadArray #arr1    #idxMsip ]) ;
    Act (liftAction np_rf (writeRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz)) (ToBit #arr2))) ;
    Retv.

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

End Spec.
