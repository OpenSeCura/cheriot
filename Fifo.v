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
Require Import Guru.Library Guru.Syntax Guru.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Fifo.
  Variable capacity: nat.
  Variable k: Kind.

  Local Open Scope string.
  Local Open Scope guru_scope.

  Definition fifoTree : Tree Elem :=
    Node ""
      [ Leaf "elems" (EReg (Build_Reg (Array capacity k) None));
        Leaf "size" (EReg (Build_Reg (Bit (Z.log2_up (Z.of_nat capacity))) (Some (Default _))));
        Leaf "deq_idx" (EReg (Build_Reg (Bit (Z.log2_up (Z.of_nat capacity))) (Some (Default _))))].

  Section Ty.
    Variable ty: Kind -> Type.

    Definition ModuloAdd (a b: ty (Bit (Z.log2_up (Z.of_nat capacity)))) :
      LetExpr ty (Bit (Z.log2_up (Z.of_nat capacity))) :=
      if Z.eqb (Z.pow 2 (Z.log2_up (Z.of_nat capacity))) (Z.of_nat capacity)
      then RetE (Add [#a; #b])
      else (
          LetE extendedSum <- Add [ZeroExtend 1 #a; ZeroExtend 1 #b];
          RetE (TruncLsb 1 _ (Sub #extendedSum
                                (ITE (Slt #extendedSum $(Z.of_nat capacity)) $0 $(Z.of_nat capacity))))).

    Definition isFullAction : Action ty fifoTree Bool :=
      ( RegRead sz <- ".size" in fifoTree;
        Return (Eq #sz $(Z.of_nat capacity)) ).

    Definition isEmptyAction : Action ty fifoTree Bool :=
      ( RegRead sz <- ".size" in fifoTree;
        Return (Eq #sz $0) ).

    Definition enqAction (val: ty k) : Action ty fifoTree (Bit 0) :=
      ( LetA isFull <- isFullAction;
        If (Not #isFull)
        Then (
          RegRead elems <- ".elems" in fifoTree;
          RegRead size <- ".size" in fifoTree;
          RegRead deq_idx <- ".deq_idx" in fifoTree;
          LetL enq_idx <- ModuloAdd deq_idx size;
          RegWrite ".elems" in fifoTree <- (#elems @[ #enq_idx <- #val ]);
          RegWrite ".size" in fifoTree <- Add [#size; $1];
          Retv
        );
        Retv ).

    Definition deqAction : Action ty fifoTree (Bit 0) :=
      ( RegRead size <- ".size" in fifoTree;
        Let isEmpty <- Eq #size $0;
        If (Not #isEmpty)
        Then (
          RegRead deq_idx <- ".deq_idx" in fifoTree;
          Let one <- $1;
          LetL new_deq_idx <- ModuloAdd deq_idx one;
          RegWrite ".deq_idx" in fifoTree <- #new_deq_idx;
          RegWrite ".size" in fifoTree <- Sub #size $1;
          Retv
        );
        Retv ).

    Definition firstAction : Action ty fifoTree (Option k) :=
      ( RegRead elems <- ".elems" in fifoTree;
        RegRead size <- ".size" in fifoTree;
        RegRead deq_idx <- ".deq_idx" in fifoTree;
        Let isEmpty <- Eq #size $0;
        Return (ITE #isEmpty (mkNone ty) (mkSome (#elems @[ #deq_idx ]))) ).
  End Ty.
End Fifo.
