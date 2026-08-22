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

  Local Notation memTree := (specMemTree config).
  Local Notation tree := (specTree config).

  Definition np_rf : NodePath tree :=
    getNodePath tree "core.rf".

  Definition np_mem : NodePath tree :=
    getNodePath tree "core.mem".

  Definition specStep : Action ty tree (Bit 0) :=
    (* 1. Fetch *)
    LetA fetchOut : FetchOut <- specFetch config ty ;

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
    Act (specExecuteDeferred config reqOpt) ;
    Retv.

End Spec.
