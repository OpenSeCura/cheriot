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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchMemory SpecDevice Clint SpecRevoker Plic SifiveUartController.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * System Tree Definition
 * =========================================================================== *)

Section SpecDom.
  Variable core : string.
  Variable peripheral : string.
  Variable pcAddrInit : Z.

  Definition specSysTree (regions : list MemRegion) : Tree DomainElem :=
    Node "sys" [
      specCoreTree core pcAddrInit regions
    ].

  Section Spec.
    Variable config : RevConfig.
    Variable regions : list MemRegion.
    Variable clint : @ClintInstance core regions.
    Variable rev : @RevokerInstance core regions.
    Variable uart : @SifiveUartInstance peripheral regions.
    Variable plic : @PlicInstance core (S (length (collectIrqActions regions))) regions.
    Local Notation sysTree := (specSysTree regions).
    Local Notation gprPathsWithKind := (gprPathsWithKind core pcAddrInit).
    Local Notation scrPathsWithKind := (scrPathsWithKind core pcAddrInit).
    Local Notation csrPathsWithKind := (csrPathsWithKind core pcAddrInit).
    Local Notation incrementMcycle := (incrementMcycle core pcAddrInit).
    Local Notation incrementMinstret := (incrementMinstret core pcAddrInit).
    Local Notation specFetch := (specFetch core pcAddrInit).
    Local Notation specExecuteDeferred := (specExecuteDeferred core pcAddrInit).
    Local Notation regRead := (regRead core pcAddrInit).
    Local Notation executeNonDeferred := (executeNonDeferred core pcAddrInit).
    Local Notation rfTree := (rfTree core pcAddrInit).

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
      Definition specUartIpStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (sifiveUartIpStepAction uart ty).

      Definition specUartIrqStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (sifiveUartIrqStepAction uart ty).

      Definition specUartDivStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (sifiveUartDivStepAction uart ty).

      Definition specUartTxStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (sifiveUartTxStepAction uart ty).

      Definition specUartRxStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (sifiveUartRxStepAction uart ty).

      (* Autonomous background PLIC steps *)
      Definition specPlicPendingsSteps : list (Action ty sysTree (Bit 0)) :=
        map (fun act => liftAction np_mem act) (plicPendingsSteps plic ty eq_refl).

      Definition specPlicClaimStep : Action ty sysTree (Bit 0) :=
        liftAction np_mem (plicClaimStep plic ty).

      (* Rule: Reads mtimecmp CSR and mtime MMIO register to raise the mtip interrupt source.
         Sticky: only a write to mtimecmp/mtimecmph clears it. *)
      Definition specTimerInterruptRule : Action ty sysTree (Bit 0) :=
        LetA lo : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrPhysicalIdx "mtimecmp") : Expr _ (Bit CsrIdxSz))) ;
        LetA hi : Bit Xlen <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrPhysicalIdx "mtimecmph") : Expr _ (Bit CsrIdxSz))) ;
        Let mtimecmpDXlen : Bit DXlen <- {< #hi, #lo >} ;
        LetA mtimeDXlen   : Bit DXlen <- liftAction np_mem (readClintMtimeAction clint ty) ;
        Let mtipVal       : Bool      <- Uge #mtimeDXlen #mtimecmpDXlen ;
        If #mtipVal Then (liftAction np_rf (RegWrite "rf.mtip" in rfTree <- Const ty Bool true ; Retv)) ;
        Retv.

      (* ===========================================================================
       * Atomic Core Pipeline Step (specStep)
       * =========================================================================== *)

      Definition specStep : Action ty sysTree (Bit 0) :=
        (* MEIP is a pure function of PLIC state; sample it here, where both domains are reachable. *)
        LetA meip : Bool <- liftAction np_mem (plicMeipSystem plic ty) ;

        (* 1. Fetch *)
        LetA fetchOut : FetchOut <- liftAction np_core (specFetch regions ty) ;

        (* 2. Decode *)
        LetL regReadIn : RegReadIn <- wrappedDecode fetchOut ;

        (* 3. Register Read (GPRs, SCRs, CSRs, mstatus) *)
        LetA aluInInstGroup : AluInInstGroup <- liftAction np_rf (regRead #meip regReadIn) ;

        (* 4. Alu Control, Routing, and Execution *)
        Let  instGroup : InstGroup <- ##aluInInstGroup`"instGroup" ;
        (* BAD: LetL aluCtrl   : AluControl <- decodeInstGroup instGroup ; *)
        Let aluCtrl : AluControl <- Const ty AluControl (getDefault AluControl) ;
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
        (* BAD: LetL routingOut : AluOut      <- AluRouting aluIn ; *)
        Let routingOut : AluOut <- Const ty AluOut (getDefault AluOut) ;
        LetL aluOut     : AluOutUnion <- Alu routingOut ;

        (* 5. Commit Non-Deferred (GPRs, SCRs, CSRs, PCC, Traps) *)
        LetA execOut : ExecuteOut <- liftAction np_rf (executeNonDeferred #meip aluOut) ;

        (* 6. Commit Deferred (Memory Loads, Stores, Fences) *)
        Let  reqOpt  : Option DeferredReq <- ##execOut`"deferredReq" ;
        Act (liftAction np_core (specExecuteDeferred config regions reqOpt)) ;
        Retv.

    End Ty.

    (* ===========================================================================
     * Top-Level Specification Module (spec)
     * =========================================================================== *)

    Definition spec : Mod sysTree :=
      fun ty => ([
        (core, specStep ty) ;
        (core, specTickCycle ty) ;
        (core, specTickTimer ty) ;
        (core, specRevokerStep ty) ;
        (peripheral, specUartIpStep ty) ;
        (peripheral, specUartIrqStep ty) ;
        (peripheral, specUartDivStep ty) ;
        (peripheral, specUartTxStep ty) ;
        (peripheral, specUartRxStep ty) ;
        (core, specPlicClaimStep ty) ;
        (core, specTimerInterruptRule ty)
      ] ++ map (fun a => (core, a)) (specPlicPendingsSteps ty))%list.

  End Spec.

End SpecDom.
