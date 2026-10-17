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
From Guru Require Import Primitives Library Syntax Combinators Notations Composition.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section ShiftFifo.
  Variable dom: string.
  Variable capacity: nat.
  Variable k: Kind.

  Local Open Scope guru_scope.

(* ===========================================================================
 * Shifting FIFO State Tree Definition
 * =========================================================================== *)

  Definition elemLeaves : list (Tree DomainElem) :=
    map (fun idx =>
      Leaf ("elem_" ++ hex_string_of_Z (Z.of_nat idx))%string
           (dom, EReg (Build_Reg k None false))
    ) (seq 0 capacity).

  Definition fifoTree : Tree DomainElem :=
    Node "fifo"
      [ Node "elems" elemLeaves;
        Leaf "size" (dom, EReg (Build_Reg (Bit (Z.log2_up (Z.of_nat (capacity + 1)))) (Some (getDefault _)) false)) ].

  Definition elemPathsWithKind : list (RegOfKind (t:=fifoTree) k) :=
    map (embedRegOfKind (getNodePath fifoTree "fifo.elems"))
        (getTreeRegsOfKind k (getNode (getNodePath fifoTree "fifo.elems"))).

  Section Ty.
    Variable ty: Kind -> Type.

(* ===========================================================================
 * Shifting FIFO Queue Operations
 * =========================================================================== *)

    Definition readElemReg (rk : RegOfKind (t:=fifoTree) k) : Action ty fifoTree k :=
      ReadReg "" rk.(rk_path) (fun val_ty =>
        let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
        let casted_ty := eq_rect (regKind (getRegFromPath rk.(rk_path))) (fun K => ty K) val_ty _ pf_eq in
        Return (Var _ _ casted_ty)).

    Definition writeElemReg (rk : RegOfKind (t:=fifoTree) k) (newVal : Expr ty k) : Action ty fifoTree (Bit 0) :=
      let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
      let castedVal := eq_rect k (fun K => Expr ty K) newVal _ (eq_sym pf_eq) in
      WriteReg rk.(rk_path) castedVal Retv.

    Fixpoint shiftElems (ps : list (RegOfKind (t:=fifoTree) k)) : Action ty fifoTree (Bit 0) :=
      match ps with
      | [] => Retv
      | [_] => Retv
      | rkCurr :: ((rkNext :: _) as rest) =>
          LetA nextVal : k <- readElemReg rkNext;
          Act (writeElemReg rkCurr #nextVal);
          shiftElems rest
      end.

    Definition isFull : Action ty fifoTree Bool :=
      ( RegRead sz <- "fifo.size" in fifoTree;
        Return (Eq #sz $(Z.of_nat capacity)) ).

    Definition isEmpty : Action ty fifoTree Bool :=
      ( RegRead sz <- "fifo.size" in fifoTree;
        Return (isZero #sz) ).

    Definition enq (val: ty k) : Action ty fifoTree (Bit 0) :=
      ( LetA isFull <- isFull;
        If (Not #isFull)
        Then (
          RegRead size <- "fifo.size" in fifoTree;
          RegWrite "fifo.size" in fifoTree <- Add [#size; $1];
          writeRegsList elemPathsWithKind #size #val
        );
        Retv ).

    Definition deq : Action ty fifoTree (Bit 0) :=
      ( RegRead size <- "fifo.size" in fifoTree;
        Let isEmpty <- isZero #size;
        If (Not #isEmpty)
        Then (
          RegWrite "fifo.size" in fifoTree <- Sub #size $1;
          shiftElems elemPathsWithKind
        );
        Retv ).

    Definition first : Action ty fifoTree (Option k) :=
      ( RegRead size <- "fifo.size" in fifoTree;
        Let valid <- isNotZero #size;
        LetA elem : k <-
          match elemPathsWithKind with
          | [] => Return ConstDef
          | rk0 :: _ => readElemReg rk0
          end;
        @Return ty fifoTree (Option k) (STRUCT {
          "data"  ::= #elem ;
          "valid" ::= #valid
        }) ).

    Definition clear : Action ty fifoTree (Bit 0) :=
      ( RegWrite "fifo.size" in fifoTree <- $0;
        Retv ).
  End Ty.
End ShiftFifo.
