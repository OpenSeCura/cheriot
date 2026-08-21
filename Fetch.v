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

From Stdlib Require Import String List ZArith.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Memory Alu Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section FetchStages.
  Variable fetchCapacity deferredCapacity : nat.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation tree := (coreTree memTree fetchCapacity deferredCapacity).
  Local Notation capacity := fetchCapacity.

  Definition np_rf : NodePath tree :=
    getNodePath tree "core.rf".

  Definition np_mem : NodePath tree :=
    embedNodeIntoPath (getNodePath tree "core.mem") singletonChildPath.

  Definition np_fetchFifo : NodePath tree :=
    getNodePath tree "core.fetch.fetchBuf.fifo".

  (* =========================================================================
   * STAGE 1: fetchRq
   *
   * - Preconditions: fetchBuf is not full (!isFull) AND
   *                  instruction memory can accept a request (mem_canReadInstRq).
   * - Action:        Read architectural PCC from Register File (GPR 0).
   *                  Issue mem_readInstRq pcc.addr to instruction memory.
   *                  Enqueue pcc into fetchBuf.
   * ========================================================================= *)
  Definition fetchRq : Action ty tree (Bit 0) :=
    LetA fetchBuf_isFull : Bool <- liftAction np_fetchFifo (@isFull capacity FullECapWithTag ty) ;
    LetA canReadInstRq   : Bool <- liftAction np_mem ((memIfc ty).(mem_canReadInstRq)) ;

    Let canFetch : Bool <- And [ Not #fetchBuf_isFull ; #canReadInstRq ] ;

    (* This condition is always true in a spec *)
    If #canFetch Then (
      LetA pcc : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
      Act (liftAction np_mem ((memIfc ty).(mem_readInstRq) ##pcc`"addr")) ;
      liftAction np_fetchFifo (@enq capacity FullECapWithTag ty pcc)
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: fetchRp
   *
   * - Preconditions: fetchBuf has pending request (!isEmpty) AND
   *                  instruction response is valid (isInstRpValid).
   * - Action:        Dequeue pcc from fetchBuf.
   *                  Read raw instruction bytes from mem_getInstRp.
   *                  Evaluate CHERIoT Fetch Exceptions on PCC and instruction length.
   *                  Return Option FetchOut { pcc, inst, fetchExc }.
   * ========================================================================= *)
  Definition fetchRp : Action ty tree (Option FetchOut) :=
    LetA inputHead     : Option FullECapWithTag <- liftAction np_fetchFifo (@first capacity FullECapWithTag ty) ;
    LetA isInstRpValid : Bool                   <- liftAction np_mem ((memIfc ty).(mem_isInstRpValid)) ;

    Let isReady : Bool <- And [ ##inputHead `? "Some" ; #isInstRpValid ] ;

    LetIf res : Option FetchOut <-
      (* This condition is always true in a spec *)
      If #isReady Then (
        Let  pcc         : FullECapWithTag <- ##inputHead `! "Some" ;
        LetA rawInst     : Inst            <- liftAction np_mem ((memIfc ty).(mem_getInstRp)) ;
        Act (liftAction np_fetchFifo (@deq capacity FullECapWithTag ty)) ;

        (* Fetch Exception Checks *)
        Let isComp    : Bool <- isCompressed rawInst ;
        Let instBytes : Addr <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
        Let tagExc    : Bool <- Not ##pcc`"tag" ;
        Let sealExc   : Bool <- isNotZero (##pcc`"ecap"`"oType") ;
        Let permExc   : Bool <- Not (##pcc`"ecap"`"perms"`"EX") ;
        Let boundsExc : Bool <- Or [
          Slt (ZeroExtendTo (AddrSz + 2) ##pcc`"addr") (ZeroExtendTo (AddrSz + 2) ##pcc`"ecap"`"base") ;
          Sgt (ZeroExtendTo (AddrSz + 2) (Add [ ##pcc`"addr" ; #instBytes ])) (##pcc`"ecap"`"top")
        ] ;

        Let fetchOut : FetchOut <- STRUCT {
          "pcc"         ::= #pcc ;
          "inst"        ::= #rawInst ;
          "fetchExc"    ::= STRUCT {
            "tag"    ::= #tagExc ;
            "seal"   ::= #sealExc ;
            "perm"   ::= #permExc ;
            "bounds" ::= #boundsExc
          }
        } ;
        Return (mkSome #fetchOut)
      ) Else (
        Return (mkNone ty)
      ) ;
    Return #res.
End FetchStages.
