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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchMemory.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section Spec.
  Variable config : MemConfig.
  Variable ty : Kind -> Type.

  Local Notation tree := (specSysTree config).

  Definition np_core : NodePath tree :=
    getNodePath tree "sys.core".

  Definition np_rf : NodePath tree :=
    getNodePath tree "sys.core.rf".

  Definition np_mem : NodePath tree :=
    getNodePath tree "sys.core.mem".

  Definition np_intr : NodePath tree :=
    getNodePath tree "sys.interrupts".

  Definition specTickCycle : Action ty tree (Bit 0) :=
    liftAction np_rf (incrementDXlenCsr "mcycle" "mcycleh").

  Definition specTickTimer : Action ty tree (Bit 0) :=
    liftAction np_rf (incrementDXlenCsr "mtime" "mtimeh").

  Definition specReceiveInterrupts : Action ty tree (Bit 0) :=
    LetA meip    : Bool                       <- liftAction np_intr (Get meip <- "interrupts.meip_in" in interruptsTree ; Return #meip) ;
    LetA mtip    : Bool                       <- liftAction np_intr (Get mtip <- "interrupts.mtip_in" in interruptsTree ; Return #mtip) ;
    LetA msip    : Bool                       <- liftAction np_intr (Get msip <- "interrupts.msip_in" in interruptsTree ; Return #msip) ;
    LetA currMip : Bit Xlen                   <- liftAction np_rf (readRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz))) ;
    Let  currArr : Array (Z.to_nat Xlen) Bool <- FromBit (Array (Z.to_nat Xlen) Bool) #currMip ;
    Let  idxMeip : Bit LgXlen                 <- $MEIP_Bit ;
    Let  idxMtip : Bit LgXlen                 <- $MTIP_Bit ;
    Let  idxMsip : Bit LgXlen                 <- $MSIP_Bit ;
    Let  arr1    : Array (Z.to_nat Xlen) Bool <- UpdateArray #currArr #idxMeip (Or [ #meip ; ReadArray #currArr #idxMeip ]) ;
    Let  arr2    : Array (Z.to_nat Xlen) Bool <- UpdateArray #arr1    #idxMtip (Or [ #mtip ; ReadArray #arr1    #idxMtip ]) ;
    Let  arr3    : Array (Z.to_nat Xlen) Bool <- UpdateArray #arr2    #idxMsip (Or [ #msip ; ReadArray #arr2    #idxMsip ]) ;
    Act (liftAction np_rf (writeRegsList csrPathsWithKind ($(getCsrIdx "mip") : Expr _ (Bit CsrIdxSz)) (ToBit #arr3))) ;
    Retv.

  Definition specStep : Action ty tree (Bit 0) :=
    (* 1. Fetch *)
    LetA fetchOut : FetchOut <- liftAction np_core (specFetch config ty) ;

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
    Act (liftAction np_core (specExecuteDeferred config reqOpt)) ;
    Retv.

End Spec.
