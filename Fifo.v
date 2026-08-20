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

From Stdlib Require Import String List ZArith Lia.
From Guru Require Import Library Syntax Notations.

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
    Node "fifo"
      [ Leaf "elems" (EReg (Build_Reg (Array capacity k) None));
        Leaf "size" (EReg (Build_Reg (Bit (Z.log2_up (Z.of_nat (capacity + 1)))) (Some (getDefault _))));
        Leaf "deq_idx" (EReg (Build_Reg (Bit (Z.log2_up (Z.of_nat capacity))) (Some (getDefault _))))].

  Section Ty.
    Variable ty: Kind -> Type.

    Local Lemma sub_add_comm : forall a b, (a = b + (a - b))%Z.
    Proof. intros; lia. Qed.

    Local Lemma add_sub_comm : forall a b, (b + (a - b) = a)%Z.
    Proof. intros; lia. Qed.

    Definition ModuloAdd (ptr: ty (Bit (Z.log2_up (Z.of_nat capacity))))
                         (sz: ty (Bit (Z.log2_up (Z.of_nat (capacity + 1))))) :
      LetExpr ty (Bit (Z.log2_up (Z.of_nat capacity))) :=
      if Z.eqb (Z.pow 2 (Z.log2_up (Z.of_nat capacity))) (Z.of_nat capacity)
      then RetE (Add [#ptr; TruncLsb _ _ (castBits (sub_add_comm _ _) #sz)])
      else (
          LetE extendedSum <- Add [castBits (add_sub_comm _ _) (ZeroExtend _ #ptr); #sz];
          RetE (TruncLsb _ _
                  (castBits (sub_add_comm _ _)
                     (Sub #extendedSum
                        (ITE (Slt #extendedSum $(Z.of_nat capacity)) $0 $(Z.of_nat capacity)))))).

    Definition isFull : Action ty fifoTree Bool :=
      ( RegRead sz <- "fifo.size" in fifoTree;
        Return (Eq #sz $(Z.of_nat capacity)) ).

    Definition isEmpty : Action ty fifoTree Bool :=
      ( RegRead sz <- "fifo.size" in fifoTree;
        Return (Eq #sz $0) ).

    Definition enq (val: ty k) : Action ty fifoTree (Bit 0) :=
      ( LetA isFull <- isFull;
        If (Not #isFull)
        Then (
          RegRead elems <- "fifo.elems" in fifoTree;
          RegRead size <- "fifo.size" in fifoTree;
          RegRead deq_idx <- "fifo.deq_idx" in fifoTree;
          LetL enq_idx <- ModuloAdd deq_idx size;
          RegWrite "fifo.elems" in fifoTree <- (#elems @[ #enq_idx <- #val ]);
          RegWrite "fifo.size" in fifoTree <- Add [#size; $1];
          Retv
        );
        Retv ).

    Definition deq : Action ty fifoTree (Bit 0) :=
      ( RegRead size <- "fifo.size" in fifoTree;
        Let isEmpty <- isZero #size;
        If (Not #isEmpty)
        Then (
          RegRead deq_idx <- "fifo.deq_idx" in fifoTree;
          Let one <- $1;
          LetL new_deq_idx <- ModuloAdd deq_idx one;
          RegWrite "fifo.deq_idx" in fifoTree <- #new_deq_idx;
          RegWrite "fifo.size" in fifoTree <- Sub #size $1;
          Retv
        );
        Retv ).

    Definition first : Action ty fifoTree (Option k) :=
      ( RegRead elems <- "fifo.elems" in fifoTree;
        RegRead size <- "fifo.size" in fifoTree;
        RegRead deq_idx <- "fifo.deq_idx" in fifoTree;
        Let isEmpty <- Eq #size $0;
        Return (ITE #isEmpty (mkNone ty) (mkSome (#elems @[ #deq_idx ]))) ).
  End Ty.
End Fifo.
