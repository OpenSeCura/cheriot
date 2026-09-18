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

(* ===========================================================================
 * DEFERRED MULDIV FUNCTIONAL UNIT SPECIFICATION (SpecMulDiv.v)
 * ===========================================================================
 * 1. INSTRUCTION GROUPS
 * ---------------------------------------------------------------------------
 * Mul
 * * MUL cd, cs1, cs2
 * * MULH cd, cs1, cs2
 * * MULHSU cd, cs1, cs2
 * * MULHU cd, cs1, cs2
 *     Functional Units:
 *       a) Multiply (64-bit signed/unsigned product, upper/lower 32-bit select)
 *
 * Div
 * * DIV cd, cs1, cs2
 * * DIVU cd, cs1, cs2
 * * REM cd, cs1, cs2
 * * REMU cd, cs1, cs2
 *     Functional Units:
 *       a) Divide (32-bit signed/unsigned quotient and remainder with div-by-zero/overflow handling)
 *
 * ---------------------------------------------------------------------------
 * 2. FUNCTIONAL UNIT/RESOURCE MAPPING
 * ---------------------------------------------------------------------------
 * Multiply:
 *   - High      : Mul (when MULH/MULHSU/MULHU)
 *   - Op1Signed : Mul (when MULH/MULHSU)
 *   - Op2Signed : Mul (when MULH)
 *   op1: op1 (Mul)
 *   op2: mulOp.op2 (Mul)
 *
 * Divide:
 *   - Unsigned : Div (when DIVU/REMU)
 *   - Rem      : Div (when REM/REMU)
 *   op1: op1 (Div)
 *   op2: divOp.op2 (Div)
 *
 * MulDiv: Multiply (Mul), Divide (Div)
 * =========================================================================== *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Section SpecMulDiv.
  Variable ty : Kind -> Type.

  Definition Multiply (isHigh op1Signed op2Signed : ty Bool) (op1 op2 : ty Addr) : LetExpr ty Addr :=
    LetE extOp1 : Bit DXlen <- ITE #op1Signed (SignExtend Xlen #op1) (ZeroExtend Xlen #op1) ;
    LetE extOp2 : Bit DXlen <- ITE #op2Signed (SignExtend Xlen #op2) (ZeroExtend Xlen #op2) ;
    LetE prod64 : Bit DXlen <- Mul [ #extOp1 ; #extOp2 ] ;
    RetE (ITE #isHigh (TruncMsb Xlen Xlen #prod64) (TruncLsb Xlen Xlen #prod64)).

  Definition Divide (isUnsigned isRem : ty Bool) (op1 op2 : ty Addr) : LetExpr ty Addr :=
    LetE op1Neg       : Bool <- Not (msbIsZero #op1) ;
    LetE op2Neg       : Bool <- Not (msbIsZero #op2) ;
    LetE mag1         : Addr <- ITE (And [ Not #isUnsigned ; #op1Neg ]) (Neg #op1) #op1 ;
    LetE mag2         : Addr <- ITE (And [ Not #isUnsigned ; #op2Neg ]) (Neg #op2) #op2 ;
    LetE uQuot        : Addr <- Div #mag1 #mag2 ;
    LetE uRem         : Addr <- Rem #mag1 #mag2 ;
    LetE quotNeg      : Bool <- And [ Not #isUnsigned ; Xor [ #op1Neg ; #op2Neg ] ] ;
    LetE remNeg       : Bool <- And [ Not #isUnsigned ; #op1Neg ] ;
    LetE sQuot        : Addr <- ITE #quotNeg (Neg #uQuot) #uQuot ;
    LetE sRem         : Addr <- ITE #remNeg (Neg #uRem) #uRem ;
    LetE divByZeroVal : Addr <- ITE #isRem #op1 (Const ty (Bit Xlen) (InvDefault (Bit Xlen))) ;
    LetE divNormalVal : Addr <- ITE #isRem #sRem #sQuot ;
    RetE (ITE (isZero #op2) #divByZeroVal #divNormalVal).

  Definition MulDiv (op1 : ty Addr) (mulDivOp : ty MulDivUnion) : LetExpr ty Addr :=
    LetIfE res : Addr <-
      IfE (#mulDivOp `? "Mul")
      ThenE (
        LetE mulOp     : MulOp <- #mulDivOp `! "Mul" ;
        LetE isHigh    : Bool  <- ##mulOp`"isHigh" ;
        LetE op1Signed : Bool  <- ##mulOp`"op1Signed" ;
        LetE op2Signed : Bool  <- ##mulOp`"op2Signed" ;
        LetE op2       : Addr  <- ##mulOp`"op2" ;
        Multiply isHigh op1Signed op2Signed op1 op2
      )
      ElseE (
        LetE divOp      : DivOp <- #mulDivOp `! "Div" ;
        LetE isUnsigned : Bool  <- ##divOp`"isUnsigned" ;
        LetE isRem      : Bool  <- ##divOp`"isRem" ;
        LetE op2        : Addr  <- ##divOp`"op2" ;
        Divide isUnsigned isRem op1 op2
      ) ;
    RetE #res.
End SpecMulDiv.
