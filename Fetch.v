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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits SpecMemory Alu Fifo.

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
   *                  instruction memory can accept a request (mem_canReadInstRq) AND
   *                  (!waitForFenceIAck OR isFenceIAck).
   * - Action:        Read architectural PCC from Register File (GPR 0).
   *                  Issue mem_readInstRq pcc.addr to instruction memory.
   *                  Enqueue PendingFetch { pcc, isFenceIAck } into fetchBuf.
   * ========================================================================= *)
  Definition fetchRq : Action ty tree (Bit 0) :=
    LetA fetchBuf_isFull : Bool <- liftAction np_fetchFifo (@isFull capacity PendingFetch ty) ;
    LetA canReadInstRq   : Bool <- liftAction np_mem ((memIfc ty).(mem_canReadInstRq)) ;
    LetA isFenceIAck     : Bool <- liftAction np_mem ((memIfc ty).(mem_fenceI_ack)) ;
    LetA waitForAck      : Bool <- liftAction np_rf (
      RegRead waitVal <- "rf.waitForFenceIAck" in rfTree ;
      Return #waitVal
    ) ;

    Let canFetch : Bool <- And [ Not #fetchBuf_isFull ; #canReadInstRq ; Or [ Not #waitForAck ; #isFenceIAck ] ] ;

    (* This condition is always true in a spec *)
    If #canFetch Then (
      LetA pcc : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
      Act (liftAction np_mem ((memIfc ty).(mem_readInstRq) ##pcc`"addr")) ;
      Let pending : PendingFetch <- STRUCT {
        "pcc"         ::= #pcc ;
        "isFenceIAck" ::= #isFenceIAck
      } ;
      liftAction np_fetchFifo (@enq capacity PendingFetch ty pending)
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: fetchRp
   *
   * - Preconditions: fetchBuf has pending request (!isEmpty) AND
   *                  instruction response is valid (isInstRpValid).
   * - Action:        Dequeue PendingFetch from fetchBuf.
   *                  Read raw instruction bytes from mem_getInstRp.
   *                  Evaluate CHERIoT Fetch Exceptions on PCC and instruction length.
   *                  Return Option FetchOut { pcc, inst, fetchExc, isFenceIAck }.
   * ========================================================================= *)
  Definition fetchRp : Action ty tree (Option FetchOut) :=
    LetA inputHead     : Option PendingFetch <- liftAction np_fetchFifo (@first capacity PendingFetch ty) ;
    LetA isInstRpValid : Bool                <- liftAction np_mem ((memIfc ty).(mem_isInstRpValid)) ;

    Let isReady : Bool <- And [ ##inputHead `? "Some" ; #isInstRpValid ] ;

    LetIf res : Option FetchOut <-
      (* This condition is always true in a spec *)
      If #isReady Then (
        Let  pf          : PendingFetch    <- ##inputHead `! "Some" ;
        Let  pcc         : FullECapWithTag <- ##pf`"pcc" ;
        Let  isFenceIAck : Bool            <- ##pf`"isFenceIAck" ;
        LetA rawInst     : Inst            <- liftAction np_mem ((memIfc ty).(mem_getInstRp)) ;
        Act (liftAction np_fetchFifo (@deq capacity PendingFetch ty)) ;

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
          } ;
          "isFenceIAck" ::= #isFenceIAck
        } ;
        Return (mkSome #fetchOut)
      ) Else (
        Return (mkNone ty)
      ) ;
    Return #res.
End FetchStages.
