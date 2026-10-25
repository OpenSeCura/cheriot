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

(*
 * Generic Staged Hardware Controllers (`ImplStaged.v`).
 *
 * Completely independent of any specific arithmetic operation (such as Multiply or Divide).
 *
 * Given any computation decomposed into `n` stages:
 *   `f(x) = finishFn (stepFn^n (initFn x))`
 * where:
 *   - `initFn   : forall ty, ty InpK -> LetExpr ty StateK`   (`f_1`)
 *   - `stepFn   : forall ty, ty StateK -> LetExpr ty StateK` (`f_m`)
 *   - `finishFn : forall ty, ty StateK -> LetExpr ty OutK`   (`f_n`)
 *
 * This module provides the generic Iterative (`stagedIterTree`) and
 * Pipelined (`stagedPipeTree`) hardware controllers.
 * See `Proof/ImplStagedProof.v` for `StageValAt` and the step-by-step
 * inductive verification theorems.
 *)

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Composition.
From Cheriot Require Export ShiftFifo.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. GENERIC ITERATIVE HARDWARE CONTROLLER (SINGLE ACCUMULATOR, NO OUTPUT FIFO)
 * =========================================================================== *)

Definition iterStepsSz (num_stages : nat) : Z :=
  Z.max 1 (Z.log2_up (Z.of_nat num_stages + 1)).

Definition IterWorkState (num_stages : nat) (StateK : Kind) : Kind :=
  STRUCT_TYPE {
    "busy"     :: Bool ;
    "stepsRem" :: Bit (iterStepsSz num_stages) ;
    "state"    :: StateK
  }.

Section GenericIterativeHardware.
  Variable dom : string.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Local Abbreviation stepsSz := (iterStepsSz num_stages).
  Variable numStepsFn : forall ty, ty InpK -> LetExpr ty (Bit stepsSz).
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.

  Local Abbreviation WorkK := (IterWorkState num_stages StateK).

  (* Hardware state is JUST the single `work` register (`busy`, `stepsRem`, `state`). *)
  Definition stagedIterTree : Tree DomainElem :=
    Leaf "work" (dom, EReg (Build_Reg WorkK (Some (getDefault WorkK)) false)).

  Definition stagedWorkRegPath : RegPath stagedIterTree :=
    @Build_RegPath stagedIterTree tt I.

  Definition stagedIterCanEnq (ty : Kind -> Type) :
    Action ty stagedIterTree Bool :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      Return (Not (##w`"busy"))).

  Definition stagedIterEnq (ty : Kind -> Type) (inp : ty InpK) :
    Action ty stagedIterTree (Bit 0) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      If (Not (##w`"busy")) Then (
        LetL st0         : StateK      <- initFn ty inp ;
        LetL targetSteps : Bit stepsSz <- numStepsFn ty inp ;
        Let nextW : WorkK <- STRUCT {
          "busy"     ::= Const ty Bool true ;
          "stepsRem" ::= #targetSteps ;
          "state"    ::= #st0
        } ;
        WriteReg stagedWorkRegPath #nextW Retv
      ) Else (
        Retv
      ) ;
      Retv).

  Definition stagedIterStep (ty : Kind -> Type) :
    Action ty stagedIterTree (Bit 0) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      If (And [ ##w`"busy" ; isNotZero (##w`"stepsRem") ]) Then (
        Let curSt   : StateK <- ##w`"state" ;
        LetL nextSt : StateK <- stepFn ty curSt ;
        Let nextW : WorkK <- STRUCT {
          "busy"     ::= Const ty Bool true ;
          "stepsRem" ::= Sub (##w`"stepsRem") $1 ;
          "state"    ::= #nextSt
        } ;
        WriteReg stagedWorkRegPath #nextW Retv
      ) Else (
        Retv
      ) ;
      Retv).

  (* Reads directly from the accumulator when `busy && isZero stepsRem` *)
  Definition stagedIterFirst (ty : Kind -> Type) :
    Action ty stagedIterTree (Option OutK) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      Let lastSt  : StateK <- ##w`"state" ;
      LetL outVal : OutK   <- finishFn ty lastSt ;
      Return (ITE (And [ ##w`"busy" ; isZero (##w`"stepsRem") ])
                  (mkSome #outVal)
                  (mkNone ty))).

  (* Dequeues by clearing `busy <- false` *)
  Definition stagedIterDeq (ty : Kind -> Type) :
    Action ty stagedIterTree (Bit 0) :=
    ReadReg "work" stagedWorkRegPath (fun w : ty WorkK =>
      If (And [ ##w`"busy" ; isZero (##w`"stepsRem") ]) Then (
        Let nextW : WorkK <- (##w `{ "busy" <- Const ty Bool false }) ;
        WriteReg stagedWorkRegPath #nextW Retv
      ) Else (
        Retv
      ) ;
      Retv).

  Definition stagedIterMod : Mod stagedIterTree :=
    fun ty => [ (dom, stagedIterStep ty) ].

End GenericIterativeHardware.

(* ===========================================================================
 * 2. GENERIC PIPELINED HARDWARE CONTROLLER (NO EXTRA OUTPUT FIFO, NO FINISH RULE)
 * =========================================================================== *)

Section GenericPipelinedHardware.
  Variable dom : string.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.

  Fixpoint stagedStagesTail (n : nat) : list (Tree DomainElem) :=
    match n with
    | 0%nat => []
    | S m =>
        [ Node ("stages_" ++ hex_string_of_Z (Z.of_nat m))
               (fifoTree dom 1 StateK :: stagedStagesTail m) ]
    end.

  Definition stagedStagesTree (n : nat) : Tree DomainElem :=
    Node ("stages_" ++ hex_string_of_Z (Z.of_nat n))
         (fifoTree dom 1 StateK :: stagedStagesTail n).

  (* The pipeline tree is simply the chain of stage FIFOs `stagedStagesTree num_stages`
   * (no extra output FIFO and no extra latency cycle). *)
  Definition stagedPipeTree : Tree DomainElem :=
    stagedStagesTree num_stages.

  Fixpoint stagedLiftLastStage {ty : Kind -> Type} {k : Kind}
    (n : nat)
    (a : Action ty (fifoTree dom 1 StateK) k) :
    Action ty (stagedStagesTree n) k :=
    match n with
    | 0%nat => liftAction child0Path a
    | S m   => liftAction child1Path (stagedLiftLastStage m a)
    end.

  Definition stagedPipeCanEnq (ty : Kind -> Type) :
    Action ty stagedPipeTree Bool :=
    LetA full0 : Bool <- liftAction child0Path (@isFull dom 1 StateK ty) ;
    Return (Not #full0).

  Definition stagedPipeEnq (ty : Kind -> Type) (inp : ty InpK) :
    Action ty stagedPipeTree (Bit 0) :=
    LetL st0 : StateK <- initFn ty inp ;
    liftAction child0Path (@enq dom 1 StateK ty st0).

  Definition stagedPipeStepAdjacent (ty : Kind -> Type) (m : nat) :
    Action ty (stagedStagesTree (S m)) (Bit 0) :=
    LetA optIn : Option StateK <- liftAction child0Path (@first dom 1 StateK ty) ;
    LetA nextFull : Bool <-
      liftAction child1Path (liftAction child0Path (@isFull dom 1 StateK ty)) ;
    If (And [ #optIn`"valid" ; Not #nextFull ]) Then (
      Let curSt   : StateK <- #optIn`"data" ;
      LetL nextSt : StateK <- stepFn ty curSt ;
      LetA _ : Bit 0 <-
        liftAction child1Path (liftAction child0Path (@enq dom 1 StateK ty nextSt)) ;
      LetA _ : Bit 0 <- liftAction child0Path (@deq dom 1 StateK ty) ;
      Retv
    ) Else (
      Retv
    ) ;
    Retv.

  Fixpoint stagedPipeStageRulesChain (ty : Kind -> Type) (n : nat) :
    list (Action ty (stagedStagesTree n) (Bit 0)) :=
    match n with
    | 0%nat => []
    | S m =>
        stagedPipeStepAdjacent ty m ::
        map (fun r => liftAction child1Path r)
            (stagedPipeStageRulesChain ty m)
    end.

  Definition stagedPipeAllStageRules (ty : Kind -> Type) :
    list (Action ty stagedPipeTree (Bit 0)) :=
    stagedPipeStageRulesChain ty num_stages.

  Definition stagedPipeMod : Mod stagedPipeTree :=
    fun ty => map (fun r => (dom, r)) (stagedPipeAllStageRules ty).

  (* Reads directly from the final pipeline stage `stages_0` and applies `finishFn`
   * combinationally with zero extra latency. *)
  Definition stagedPipeFirst (ty : Kind -> Type) :
    Action ty stagedPipeTree (Option OutK) :=
    LetA optLast : Option StateK <-
      stagedLiftLastStage num_stages (@first dom 1 StateK ty) ;
    Let lastSt  : StateK <- #optLast`"data" ;
    LetL outVal : OutK   <- finishFn ty lastSt ;
    Return (ITE (#optLast`"valid")
                (mkSome #outVal)
                (mkNone ty)).

  (* Dequeues directly from the final pipeline stage `stages_0`. *)
  Definition stagedPipeDeq (ty : Kind -> Type) :
    Action ty stagedPipeTree (Bit 0) :=
    stagedLiftLastStage num_stages (@deq dom 1 StateK ty).

End GenericPipelinedHardware.
