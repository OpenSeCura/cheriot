(*
 * Copyright (c) 2026 Peak AI / Google LLC
 *
 * Fully Parameterized Multiplier & Divider Subsystem (`ImplMulDiv.v`).
 *
 * Architectural Parameters:
 *   1. `input_width : nat` (`D = Z.of_nat input_width`) — operand width in bits.
 *   2. `mul_stages  : nat` (`mul_bits_per_stage = input_width / mul_stages`) —
 *      number of stages (if pipelined) or iterations (if iterative) for Multiply.
 *   3. `div_stages  : nat` (`div_bits_per_stage = input_width / div_stages`) —
 *      number of iterations for Divide (divider is always iterative).
 *   4. `mode : MulDivMode` — selects one of three hardware realizations:
 *      - `PipelinedMul_IterDiv`:
 *          Pipelined `mul_stages`-stage multiplier + separate `div_stages`-iteration divider.
 *      - `IterMul_SeparateIterDiv`:
 *          Iterative `mul_stages`-iteration multiplier + separate `div_stages`-iteration divider.
 *      - `IterMul_SharedIterDiv`:
 *          Iterative multiplier and divider sharing a single `(D + D)`-bit accumulator
 *          (`acc`), a single `D`-bit left-shift operand register (`shiftOp`), and a
 *          single `(D + D)`-bit operand register (`extOp2`).
 *
 * Key Design Properties:
 *   - Stage-Index-Independent Transition Functions (Option B):
 *     `mulBitStep` and `divBitStep` shift `shiftOp` (`op1` / `mag1`) left by 1 bit
 *     at every bit-step and always inspect the MSB (`bit D - 1`). Consequently,
 *     `mulStageStep` and `divStageStep` do not depend on the stage/iteration index
 *     and are shared verbatim across pipelined and iterative modes.
 *   - Zero preserved `op1`/`op2` in `DivStageState`:
 *     By setting `quotNeg = !isUnsigned && !isZero(op2) && (op1Neg ^ op2Neg)` and
 *     `remNeg = !isUnsigned && op1Neg` in `divInitStage`, the restoring divider
 *     naturally yields `uQuot = -1` and `sRem = op1` when `op2 == 0`.
 *   - Generic `N`-Step Controllers (`PipelinedEngine` and `IterativeEngine`):
 *     Parameterized over arbitrary `(InpK, StateK, OutK, initFn, stepFn, finishFn)`.
 *)

From Stdlib Require Import String List ZArith Lia Bool Zmod.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines FunctionalUnits Fifo SpecMulDiv.
From Cheriot Require Export ImplStaged.

Set Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. ARCHITECTURAL MODES & PARAMETERIZED STRUCT TYPES
 * =========================================================================== *)

Inductive MulDivMode : Type :=
| PipelinedMul_IterDiv
| IterMul_SeparateIterDiv
| IterMul_SharedIterDiv.

Definition dataLen (input_width : nat) : Z :=
  Z.of_nat input_width.

Section ParameterizedTypes.
  Variable d : Z.

  (* --- 1A. Multiply Types (Approach 3: Unsigned Core + High-Half Correction) --- *)

  Definition MulInput : Kind :=
    STRUCT_TYPE {
      "isHigh"    :: Bool ;
      "op1Signed" :: Bool ;
      "op2Signed" :: Bool ;
      "op1"       :: Bit d ;
      "op2"       :: Bit d
    }.

  Definition MulCoreState : Kind :=
    STRUCT_TYPE {
      "shiftOp" :: Bit d ;
      "mulAcc"  :: Bit (d + d)
    }.

  Definition MulStageState : Kind :=
    STRUCT_TYPE {
      "isHigh"  :: Bool ;
      "hiCorr"  :: Bit d ;
      "shiftOp" :: Bit d ;
      "extOp2"  :: Bit (d + d) ;
      "mulAcc"  :: Bit (d + d)
    }.

  Definition MulOutput : Kind :=
    STRUCT_TYPE {
      "mulProd" :: Bit (d + d) ;
      "res"     :: Bit d
    }.

  (* --- 1B. Divide Types (Magnitude + Unsigned Iterator) --- *)

  Definition DivSpecOut : Kind :=
    STRUCT_TYPE {
      "quot" :: Bit d ;
      "rem"  :: Bit d
    }.

  Definition DivInput : Kind :=
    STRUCT_TYPE {
      "isUnsigned" :: Bool ;
      "isRem"      :: Bool ;
      "op1"        :: Bit d ;
      "op2"        :: Bit d
    }.

  Definition DivCoreState : Kind :=
    STRUCT_TYPE {
      "shiftOp" :: Bit d ;
      "rem"     :: Bit d ;
      "quot"    :: Bit d
    }.

  Definition DivStageState : Kind :=
    STRUCT_TYPE {
      "isRem"   :: Bool ;
      "quotNeg" :: Bool ;
      "remNeg"  :: Bool ;
      "shiftOp" :: Bit d ;
      "mag2"    :: Bit d ;
      "rem"     :: Bit d ;
      "quot"    :: Bit d
    }.

  Definition DivOutput : Kind :=
    STRUCT_TYPE {
      "uQuot" :: Bit d ;
      "uRem"  :: Bit d ;
      "quot"  :: Bit d ;
      "rem"   :: Bit d ;
      "res"   :: Bit d
    }.

  (* --- 1C. Shared-Accumulator Iterative Mul/Div Types --- *)

  Definition SharedInput : Kind :=
    STRUCT_TYPE {
      "isMul"      :: Bool ;
      "isHigh"     :: Bool ;
      "op1Signed"  :: Bool ;
      "op2Signed"  :: Bool ;
      "isUnsigned" :: Bool ;
      "isRem"      :: Bool ;
      "op1"        :: Bit d ;
      "op2"        :: Bit d
    }.

  (* Shares `shiftOp : Bit d`, `extOp2 : Bit (d + d)`, and `acc : Bit (d + d)`
   * between Multiply (`acc = mulAcc`) and Divide (`acc = {rem, quot}`). *)
  Definition SharedStageState : Kind :=
    STRUCT_TYPE {
      "isMul"       :: Bool ;
      "isHighOrRem" :: Bool ;
      "quotNeg"     :: Bool ;
      "remNeg"      :: Bool ;
      "hiCorr"      :: Bit d ;
      "shiftOp"     :: Bit d ;
      "extOp2"      :: Bit (d + d) ;
      "acc"         :: Bit (d + d)
    }.

  Definition SharedOutput : Kind :=
    STRUCT_TYPE {
      "res" :: Bit d
    }.

  (* --- 1D. Generic Shadow-Annotated Element Wrapper (for Verification) --- *)

  Definition AnnotElem (InpK StateK : Kind) : Kind :=
    STRUCT_TYPE {
      "inp"   :: InpK ;
      "state" :: StateK
    }.

End ParameterizedTypes.

(* ===========================================================================
 * 2. PURE SPECIFICATIONS (ARBITRARY WIDTH `d`: `SpecMul` AND `SpecDiv`)
 * =========================================================================== *)

Section PureSpecifications.
  Variable d : Z.
  Variable ty : Kind -> Type.

  (* Arbitrary-width `d` x `d` -> `2*d` signed/unsigned multiplication spec *)
  Definition SpecMul
    (op1Signed op2Signed : ty Bool) (op1 op2 : ty (Bit d)) : LetExpr ty (Bit (d + d)) :=
    LetE extOp1 : Bit (d + d) <- ITE #op1Signed (SignExtend d #op1) (ZeroExtend d #op1) ;
    LetE extOp2 : Bit (d + d) <- ITE #op2Signed (SignExtend d #op2) (ZeroExtend d #op2) ;
    RetE (Mul [ #extOp1 ; #extOp2 ]).

  Definition PureMultiplyFull := SpecMul.

  Definition PureMultiply
    (isHigh op1Signed op2Signed : ty Bool) (op1 op2 : ty (Bit d)) : LetExpr ty (Bit d) :=
    LETE prod : Bit (d + d) <- SpecMul op1Signed op2Signed op1 op2 ;
    RetE (ITE #isHigh (TruncMsb d d #prod) (TruncLsb d d #prod)).

  Definition PureMulOut (inp : ty (MulInput d)) : LetExpr ty (MulOutput d) :=
    LetE isHigh    : Bool  <- ##inp`"isHigh" ;
    LetE op1Signed : Bool  <- ##inp`"op1Signed" ;
    LetE op2Signed : Bool  <- ##inp`"op2Signed" ;
    LetE op1       : Bit d <- ##inp`"op1" ;
    LetE op2       : Bit d <- ##inp`"op2" ;
    LETE mulProd   : Bit (d + d) <- SpecMul op1Signed op2Signed op1 op2 ;
    LETE res       : Bit d       <- PureMultiply isHigh op1Signed op2Signed op1 op2 ;
    @RetE ty (MulOutput d) (STRUCT {
      "mulProd" ::= #mulProd ;
      "res"     ::= #res
    }).

  (* Arbitrary-width `d` signed/unsigned division & remainder spec *)
  Definition SpecDiv
    (isSignedDividend isSignedDivisor : ty Bool)
    (dividend divisor : ty (Bit d)) : LetExpr ty (DivSpecOut d) :=
    LetE neg1    : Bool  <- And [ #isSignedDividend ; Not (msbIsZero #dividend) ] ;
    LetE neg2    : Bool  <- And [ #isSignedDivisor  ; Not (msbIsZero #divisor) ] ;
    LetE mag1    : Bit d <- ITE #neg1 (Neg #dividend) #dividend ;
    LetE mag2    : Bit d <- ITE #neg2 (Neg #divisor)  #divisor ;
    LetE uQuot   : Bit d <- Div #mag1 #mag2 ;
    LetE uRem    : Bit d <- Rem #mag1 #mag2 ;
    LetE quotNeg : Bool  <- And [ Not (isZero #divisor) ; Xor [ #neg1 ; #neg2 ] ] ;
    LetE remNeg  : Bool  <- #neg1 ;
    LetE sQuot   : Bit d <- ITE #quotNeg (Neg #uQuot) #uQuot ;
    LetE sRem    : Bit d <- ITE #remNeg  (Neg #uRem)  #uRem ;
    @RetE ty (DivSpecOut d) (STRUCT {
      "quot" ::= #sQuot ;
      "rem"  ::= #sRem
    }).

  Definition PureDivide
    (isUnsigned isRem : ty Bool) (op1 op2 : ty (Bit d)) : LetExpr ty (Bit d) :=
    LetE op1Neg       : Bool  <- Not (msbIsZero #op1) ;
    LetE op2Neg       : Bool  <- Not (msbIsZero #op2) ;
    LetE mag1         : Bit d <- ITE (And [ Not #isUnsigned ; #op1Neg ]) (Neg #op1) #op1 ;
    LetE mag2         : Bit d <- ITE (And [ Not #isUnsigned ; #op2Neg ]) (Neg #op2) #op2 ;
    LetE uQuot        : Bit d <- Div #mag1 #mag2 ;
    LetE uRem         : Bit d <- Rem #mag1 #mag2 ;
    LetE quotNeg      : Bool  <- And [ Not #isUnsigned ; Xor [ #op1Neg ; #op2Neg ] ] ;
    LetE remNeg       : Bool  <- And [ Not #isUnsigned ; #op1Neg ] ;
    LetE sQuot        : Bit d <- ITE #quotNeg (Neg #uQuot) #uQuot ;
    LetE sRem         : Bit d <- ITE #remNeg (Neg #uRem) #uRem ;
    LetE allOnes      : Bit d <- Const ty (Bit d) (InvDefault (Bit d)) ;
    LetE divByZeroVal : Bit d <- ITE #isRem #op1 #allOnes ;
    LetE divNormalVal : Bit d <- ITE #isRem #sRem #sQuot ;
    RetE (ITE (isZero #op2) #divByZeroVal #divNormalVal).

  Definition PureDivOut (inp : ty (DivInput d)) : LetExpr ty (DivOutput d) :=
    LetE isUnsigned : Bool         <- ##inp`"isUnsigned" ;
    LetE isRem      : Bool         <- ##inp`"isRem" ;
    LetE op1        : Bit d        <- ##inp`"op1" ;
    LetE op2        : Bit d        <- ##inp`"op2" ;
    LetE isSigned   : Bool         <- Not #isUnsigned ;
    LETE specD      : DivSpecOut d <- SpecDiv isSigned isSigned op1 op2 ;
    LetE op1Neg     : Bool         <- Not (msbIsZero #op1) ;
    LetE op2Neg     : Bool         <- Not (msbIsZero #op2) ;
    LetE mag1       : Bit d        <- ITE (And [ Not #isUnsigned ; #op1Neg ]) (Neg #op1) #op1 ;
    LetE mag2       : Bit d        <- ITE (And [ Not #isUnsigned ; #op2Neg ]) (Neg #op2) #op2 ;
    LetE uQuot      : Bit d        <- Div #mag1 #mag2 ;
    LetE uRem       : Bit d        <- Rem #mag1 #mag2 ;
    LETE res        : Bit d        <- PureDivide isUnsigned isRem op1 op2 ;
    @RetE ty (DivOutput d) (STRUCT {
      "uQuot" ::= #uQuot ;
      "uRem"  ::= #uRem ;
      "quot"  ::= ##specD`"quot" ;
      "rem"   ::= ##specD`"rem" ;
      "res"   ::= #res
    }).

  Definition PureSharedOut (inp : ty (SharedInput d)) : LetExpr ty (SharedOutput d) :=
    LetE isMul      : Bool         <- ##inp`"isMul" ;
    LetE isHigh     : Bool         <- ##inp`"isHigh" ;
    LetE op1Signed  : Bool         <- ##inp`"op1Signed" ;
    LetE op2Signed  : Bool         <- ##inp`"op2Signed" ;
    LetE isUnsigned : Bool         <- ##inp`"isUnsigned" ;
    LetE isRem      : Bool         <- ##inp`"isRem" ;
    LetE op1        : Bit d        <- ##inp`"op1" ;
    LetE op2        : Bit d        <- ##inp`"op2" ;
    LETE mulRes     : Bit d <- PureMultiply isHigh op1Signed op2Signed op1 op2 ;
    LETE divRes     : Bit d <- PureDivide isUnsigned isRem op1 op2 ;
    LetE res        : Bit d <- ITE #isMul #mulRes #divRes ;
    @RetE ty (SharedOutput d) (STRUCT {
      "res" ::= #res
    }).

End PureSpecifications.

(* ===========================================================================
 * 3. STAGE-INDEX-INDEPENDENT COMBINATIONAL STEP FUNCTIONS (OPTION B)
 *    - Multiply uses Approach 3: Pure unsigned core + High-half subtraction
 *    - Divide uses Magnitude + Unsigned restoring iterator
 * =========================================================================== *)

Section StageIndependentCombinational.
  Variable input_width : nat.
  Local Notation d := (dataLen input_width).

  Variable ty : Kind -> Type.

  (* --- 3A. Multiply Combinational Functions (Approach 3) --- *)

  Definition mulBitStep
    (shiftOp : ty (Bit d)) (extOp2 : ty (Bit (d + d))) (mulAcc : ty (Bit (d + d)))
    : LetExpr ty (MulCoreState d) :=
    LetE msbIdx    : Bit d       <- Const ty (Bit d) (bits.of_Z d (d - 1)) ;
    LetE mulBit_d  : Bit d       <- And [ Srl #shiftOp #msbIdx ; $1 ] ;
    LetE mulBit    : Bool        <- isNotZero #mulBit_d ;
    LetE nextShift : Bit d       <- Sll #shiftOp (Const ty (Bit 1) (bits.of_Z 1 1)) ;
    LetE accShift  : Bit (d + d) <- Sll #mulAcc (Const ty (Bit 1) (bits.of_Z 1 1)) ;
    LetE nextAcc   : Bit (d + d) <- ITE #mulBit (Add [ #accShift ; #extOp2 ]) #accShift ;
    @RetE ty (MulCoreState d) (STRUCT {
      "shiftOp" ::= #nextShift ;
      "mulAcc"  ::= #nextAcc
    }).

  Fixpoint mulMultiStep (count : nat)
    (shiftOp : ty (Bit d)) (extOp2 : ty (Bit (d + d))) (mulAcc : ty (Bit (d + d)))
    : LetExpr ty (MulCoreState d) :=
    match count with
    | 0%nat =>
        @RetE ty (MulCoreState d) (STRUCT {
          "shiftOp" ::= #shiftOp ;
          "mulAcc"  ::= #mulAcc
        })
    | S remCount =>
        LETE stepOut : MulCoreState d <- mulBitStep shiftOp extOp2 mulAcc ;
        LetE nShift  : Bit d          <- ##stepOut`"shiftOp" ;
        LetE nAcc    : Bit (d + d)    <- ##stepOut`"mulAcc" ;
        mulMultiStep remCount nShift extOp2 nAcc
    end.

  (* Approach 3 Init:
   * - `extOp2` is pure unsigned `ZeroExtend d #op2`
   * - `mulAcc` starts at `$0`
   * - `hiCorr = (neg1 ? op2 : 0) + (neg2 ? op1 : 0)` is saved to adjust upper `d` bits at finish *)
  Definition mulInitStage (inp : ty (MulInput d)) : LetExpr ty (MulStageState d) :=
    LetE isHigh    : Bool        <- ##inp`"isHigh" ;
    LetE op1Signed : Bool        <- ##inp`"op1Signed" ;
    LetE op2Signed : Bool        <- ##inp`"op2Signed" ;
    LetE op1       : Bit d       <- ##inp`"op1" ;
    LetE op2       : Bit d       <- ##inp`"op2" ;
    LetE neg1      : Bool        <- And [ #op1Signed ; Not (msbIsZero #op1) ] ;
    LetE neg2      : Bool        <- And [ #op2Signed ; Not (msbIsZero #op2) ] ;
    LetE subOp2    : Bit d       <- ITE #neg1 #op2 $0 ;
    LetE subOp1    : Bit d       <- ITE #neg2 #op1 $0 ;
    LetE hiCorr    : Bit d       <- Add [ #subOp2 ; #subOp1 ] ;
    LetE extOp2    : Bit (d + d) <- ZeroExtend d #op2 ;
    LetE zero2D    : Bit (d + d) <- $0 ;
    @RetE ty (MulStageState d) (STRUCT {
      "isHigh"  ::= #isHigh ;
      "hiCorr"  ::= #hiCorr ;
      "shiftOp" ::= #op1 ;
      "extOp2"  ::= #extOp2 ;
      "mulAcc"  ::= #zero2D
    }).

  Definition mulStageStep (mul_bits_per_stage : nat) (st : ty (MulStageState d))
    : LetExpr ty (MulStageState d) :=
    LetE shiftOp : Bit d          <- ##st`"shiftOp" ;
    LetE extOp2  : Bit (d + d)    <- ##st`"extOp2" ;
    LetE mulAcc  : Bit (d + d)    <- ##st`"mulAcc" ;
    LETE coreOut : MulCoreState d <- mulMultiStep mul_bits_per_stage shiftOp extOp2 mulAcc ;
    LetE nShift  : Bit d          <- ##coreOut`"shiftOp" ;
    LetE nAcc    : Bit (d + d)    <- ##coreOut`"mulAcc" ;
    @RetE ty (MulStageState d)
      ((##st `{ "shiftOp" <- #nShift }) `{ "mulAcc" <- #nAcc }).

  (* Approach 3 Finish:
   * - `uProd = st @% "mulAcc"` is the unsigned product `op1 * op2`
   * - `sHi = uProd[2d-1 : d] - hiCorr`
   * - `mulProd = Concat sHi uProd[d-1 : 0]` equals `SpecMul d`! *)
  Definition mulFinishStage (st : ty (MulStageState d)) : LetExpr ty (MulOutput d) :=
    LetE isHigh  : Bool        <- ##st`"isHigh" ;
    LetE hiCorr  : Bit d       <- ##st`"hiCorr" ;
    LetE uProd   : Bit (d + d) <- ##st`"mulAcc" ;
    LetE uHi     : Bit d       <- TruncMsb d d #uProd ;
    LetE uLo     : Bit d       <- TruncLsb d d #uProd ;
    LetE sHi     : Bit d       <- Sub #uHi #hiCorr ;
    LetE mulProd : Bit (d + d) <- Concat #sHi #uLo ;
    LetE mulRes  : Bit d       <- ITE #isHigh #sHi #uLo ;
    @RetE ty (MulOutput d) (STRUCT {
      "mulProd" ::= #mulProd ;
      "res"     ::= #mulRes
    }).

  (* --- 3B. Divide Combinational Functions (`divInitStage`, `divStageStep`, `divFinishStage`) --- *)

  Definition divBitStep
    (shiftOp mag2 rem quot : ty (Bit d))
    : LetExpr ty (DivCoreState d) :=
    LetE msbIdx    : Bit d       <- Const ty (Bit d) (bits.of_Z d (d - 1)) ;
    LetE bit_d     : Bit d       <- And [ Srl #shiftOp #msbIdx ; $1 ] ;
    LetE nextShift : Bit d       <- Sll #shiftOp (Const ty (Bit 1) (bits.of_Z 1 1)) ;
    LetE remShift  : Bit (d + 1) <-
      Or [ Sll (ZeroExtend 1 #rem) (Const ty (Bit 1) (bits.of_Z 1 1)) ;
           ZeroExtend 1 #bit_d ] ;
    LetE mag2Ext   : Bit (d + 1) <- ZeroExtend 1 #mag2 ;
    LetE ge        : Bool        <- Uge #remShift #mag2Ext ;
    LetE remSub    : Bit (d + 1) <- ITE #ge (Sub #remShift #mag2Ext) #remShift ;
    LetE nextRem   : Bit d       <- TruncLsb 1 d #remSub ;
    LetE quotShift : Bit d       <- Sll #quot (Const ty (Bit 1) (bits.of_Z 1 1)) ;
    LetE nextQuot  : Bit d       <- ITE #ge (Or [ #quotShift ; $1 ]) #quotShift ;
    @RetE ty (DivCoreState d) (STRUCT {
      "shiftOp" ::= #nextShift ;
      "rem"     ::= #nextRem ;
      "quot"    ::= #nextQuot
    }).

  Fixpoint divMultiStep (count : nat)
    (shiftOp mag2 rem quot : ty (Bit d))
    : LetExpr ty (DivCoreState d) :=
    match count with
    | 0%nat =>
        @RetE ty (DivCoreState d) (STRUCT {
          "shiftOp" ::= #shiftOp ;
          "rem"     ::= #rem ;
          "quot"    ::= #quot
        })
    | S remCount =>
        LETE stepOut : DivCoreState d <- divBitStep shiftOp mag2 rem quot ;
        LetE nShift  : Bit d          <- ##stepOut`"shiftOp" ;
        LetE nRem    : Bit d          <- ##stepOut`"rem" ;
        LetE nQuot   : Bit d          <- ##stepOut`"quot" ;
        divMultiStep remCount nShift mag2 nRem nQuot
    end.

  Definition divInitStage (inp : ty (DivInput d)) : LetExpr ty (DivStageState d) :=
    LetE isUnsigned : Bool  <- ##inp`"isUnsigned" ;
    LetE isRem      : Bool  <- ##inp`"isRem" ;
    LetE op1        : Bit d <- ##inp`"op1" ;
    LetE op2        : Bit d <- ##inp`"op2" ;
    LetE op1Neg     : Bool  <- Not (msbIsZero #op1) ;
    LetE op2Neg     : Bool  <- Not (msbIsZero #op2) ;
    LetE mag1       : Bit d <- ITE (And [ Not #isUnsigned ; #op1Neg ]) (Neg #op1) #op1 ;
    LetE mag2       : Bit d <- ITE (And [ Not #isUnsigned ; #op2Neg ]) (Neg #op2) #op2 ;
    LetE quotNeg    : Bool  <- And [ Not #isUnsigned ; Not (isZero #op2) ; Xor [ #op1Neg ; #op2Neg ] ] ;
    LetE remNeg     : Bool  <- And [ Not #isUnsigned ; #op1Neg ] ;
    LetE zeroD      : Bit d <- $0 ;
    @RetE ty (DivStageState d) (STRUCT {
      "isRem"   ::= #isRem ;
      "quotNeg" ::= #quotNeg ;
      "remNeg"  ::= #remNeg ;
      "shiftOp" ::= #mag1 ;
      "mag2"    ::= #mag2 ;
      "rem"     ::= #zeroD ;
      "quot"    ::= #zeroD
    }).

  Definition divStageStep (div_bits_per_stage : nat) (st : ty (DivStageState d))
    : LetExpr ty (DivStageState d) :=
    LetE shiftOp : Bit d          <- ##st`"shiftOp" ;
    LetE mag2    : Bit d          <- ##st`"mag2" ;
    LetE rem     : Bit d          <- ##st`"rem" ;
    LetE quot    : Bit d          <- ##st`"quot" ;
    LETE coreOut : DivCoreState d <- divMultiStep div_bits_per_stage shiftOp mag2 rem quot ;
    LetE nShift  : Bit d          <- ##coreOut`"shiftOp" ;
    LetE nRem    : Bit d          <- ##coreOut`"rem" ;
    LetE nQuot   : Bit d          <- ##coreOut`"quot" ;
    @RetE ty (DivStageState d)
      (((##st `{ "shiftOp" <- #nShift })
              `{ "rem"     <- #nRem })
              `{ "quot"    <- #nQuot }).

  Definition divFinishStage (st : ty (DivStageState d)) : LetExpr ty (DivOutput d) :=
    LetE isRem   : Bool  <- ##st`"isRem" ;
    LetE quotNeg : Bool  <- ##st`"quotNeg" ;
    LetE remNeg  : Bool  <- ##st`"remNeg" ;
    LetE uRem    : Bit d <- ##st`"rem" ;
    LetE uQuot   : Bit d <- ##st`"quot" ;
    LetE sQuot   : Bit d <- ITE #quotNeg (Neg #uQuot) #uQuot ;
    LetE sRem    : Bit d <- ITE #remNeg (Neg #uRem) #uRem ;
    LetE divRes  : Bit d <- ITE #isRem #sRem #sQuot ;
    @RetE ty (DivOutput d) (STRUCT {
      "uQuot" ::= #uQuot ;
      "uRem"  ::= #uRem ;
      "quot"  ::= #sQuot ;
      "rem"   ::= #sRem ;
      "res"   ::= #divRes
    }).

  (* --- 3C. Shared-Accumulator Combinational Functions (`sharedInitStage`, `sharedStageStep`, `sharedFinishStage`) --- *)

  Definition sharedInitStage (inp : ty (SharedInput d)) : LetExpr ty (SharedStageState d) :=
    LetE isMul      : Bool        <- ##inp`"isMul" ;
    LetE isHigh     : Bool        <- ##inp`"isHigh" ;
    LetE op1Signed  : Bool        <- ##inp`"op1Signed" ;
    LetE op2Signed  : Bool        <- ##inp`"op2Signed" ;
    LetE isUnsigned : Bool        <- ##inp`"isUnsigned" ;
    LetE isRem      : Bool        <- ##inp`"isRem" ;
    LetE op1        : Bit d       <- ##inp`"op1" ;
    LetE op2        : Bit d       <- ##inp`"op2" ;
    LetE op1Neg     : Bool        <- Not (msbIsZero #op1) ;
    LetE op2Neg     : Bool        <- Not (msbIsZero #op2) ;
    (* Mul init values (Approach 3: unsigned core + hiCorr) *)
    LetE mulNeg1    : Bool        <- And [ #op1Signed ; #op1Neg ] ;
    LetE mulNeg2    : Bool        <- And [ #op2Signed ; #op2Neg ] ;
    LetE subOp2     : Bit d       <- ITE #mulNeg1 #op2 $0 ;
    LetE subOp1     : Bit d       <- ITE #mulNeg2 #op1 $0 ;
    LetE hiCorr     : Bit d       <- Add [ #subOp2 ; #subOp1 ] ;
    (* Div init values (Magnitude + unsigned iterator) *)
    LetE mag1       : Bit d       <- ITE (And [ Not #isUnsigned ; #op1Neg ]) (Neg #op1) #op1 ;
    LetE mag2       : Bit d       <- ITE (And [ Not #isUnsigned ; #op2Neg ]) (Neg #op2) #op2 ;
    LetE quotNeg    : Bool        <- And [ Not #isUnsigned ; Not (isZero #op2) ; Xor [ #op1Neg ; #op2Neg ] ] ;
    LetE remNeg     : Bool        <- And [ Not #isUnsigned ; #op1Neg ] ;
    (* Shared registers muxed once on entry: notice initAcc is $0 for BOTH Mul and Div! *)
    LetE isHighOrRem : Bool        <- ITE #isMul #isHigh #isRem ;
    LetE initShiftOp : Bit d       <- ITE #isMul #op1 #mag1 ;
    LetE initExtOp2  : Bit (d + d) <- ZeroExtend d (ITE #isMul #op2 #mag2) ;
    LetE zero2D      : Bit (d + d) <- $0 ;
    @RetE ty (SharedStageState d) (STRUCT {
      "isMul"       ::= #isMul ;
      "isHighOrRem" ::= #isHighOrRem ;
      "quotNeg"     ::= #quotNeg ;
      "remNeg"      ::= #remNeg ;
      "hiCorr"      ::= #hiCorr ;
      "shiftOp"     ::= #initShiftOp ;
      "extOp2"      ::= #initExtOp2 ;
      "acc"         ::= #zero2D
    }).

  Definition sharedStageStep (mul_bits_per_stage div_bits_per_stage : nat)
    (st : ty (SharedStageState d)) : LetExpr ty (SharedStageState d) :=
    LetE isMul   : Bool          <- ##st`"isMul" ;
    LetE shiftOp : Bit d         <- ##st`"shiftOp" ;
    LetE extOp2  : Bit (d + d)   <- ##st`"extOp2" ;
    LetE acc     : Bit (d + d)   <- ##st`"acc" ;
    (* Multiply path uses `acc` as `mulAcc` *)
    LETE mulCore : MulCoreState d <- mulMultiStep mul_bits_per_stage shiftOp extOp2 acc ;
    (* Divide path unpacks `acc = {rem, quot}` and `mag2 = TruncLsb d d extOp2` *)
    LetE rem     : Bit d         <- TruncMsb d d #acc ;
    LetE quot    : Bit d         <- TruncLsb d d #acc ;
    LetE mag2    : Bit d         <- TruncLsb d d #extOp2 ;
    LETE divCore : DivCoreState d <- divMultiStep div_bits_per_stage shiftOp mag2 rem quot ;
    LetE divAcc  : Bit (d + d)   <- Concat (##divCore`"rem") (##divCore`"quot") ;
    LetE nShift  : Bit d         <- ITE #isMul (##mulCore`"shiftOp") (##divCore`"shiftOp") ;
    LetE nAcc    : Bit (d + d)   <- ITE #isMul (##mulCore`"mulAcc")  #divAcc ;
    @RetE ty (SharedStageState d)
      ((##st `{ "shiftOp" <- #nShift }) `{ "acc" <- #nAcc }).

  Definition sharedFinishStage (st : ty (SharedStageState d)) : LetExpr ty (SharedOutput d) :=
    LetE isMul       : Bool        <- ##st`"isMul" ;
    LetE isHighOrRem : Bool        <- ##st`"isHighOrRem" ;
    LetE quotNeg     : Bool        <- ##st`"quotNeg" ;
    LetE remNeg      : Bool        <- ##st`"remNeg" ;
    LetE hiCorr      : Bit d       <- ##st`"hiCorr" ;
    LetE acc         : Bit (d + d) <- ##st`"acc" ;
    LetE accHi       : Bit d       <- TruncMsb d d #acc ;
    LetE accLo       : Bit d       <- TruncLsb d d #acc ;
    (* Approach 3 Mul finish *)
    LetE sHi         : Bit d       <- Sub #accHi #hiCorr ;
    LetE mulProd     : Bit (d + d) <- Concat #sHi #accLo ;
    LetE mulRes      : Bit d       <- ITE #isHighOrRem #sHi #accLo ;
    (* Magnitude Div finish *)
    LetE sQuot       : Bit d       <- ITE #quotNeg (Neg #accLo) #accLo ;
    LetE sRem        : Bit d       <- ITE #remNeg (Neg #accHi) #accHi ;
    LetE divRes      : Bit d       <- ITE #isHighOrRem #sRem #sQuot ;
    LetE res         : Bit d       <- ITE #isMul #mulRes #divRes ;
    @RetE ty (SharedOutput d) (STRUCT {
      "res" ::= #res
    }).

End StageIndependentCombinational.

(* ===========================================================================
 * 4. CONCRETE INSTANTIATIONS OF THE 3 MODES VIA `ImplStaged.v`
 *    - Mode 1 (`PipelinedMul_IterDiv`):
 *        Pipelined Multiplier (`mul_stages`) + Iterative Divider (`div_stages`)
 *    - Mode 2 (`IterMul_SeparateIterDiv`):
 *        Iterative Multiplier (`mul_stages`) + Separate Iterative Divider (`div_stages`)
 *    - Mode 3 (`IterMul_SharedIterDiv`):
 *        Shared-Accumulator Iterative Multiplier/Divider (`mul_stages` / `div_stages`)
 * =========================================================================== *)

Definition MulDivFifoCapacity : nat := 1%nat.

Notation liftHeadAction := stagedLiftHead (only parsing).
Notation liftTailAction := stagedLiftTail (only parsing).

Section ConcreteMulDivEngines.
  Variable dom : string.
  Variable input_width mul_stages div_stages : nat.

  Local Notation d := (dataLen input_width).
  Local Notation mul_bps := (input_width / mul_stages)%nat.
  Local Notation div_bps := (input_width / div_stages)%nat.

  (* --- 4A. Pipelined Multiplier Instance (`stagedPipeTree`) --- *)

  Definition unannotMulPipeTree : Tree DomainElem :=
    stagedPipeTree dom (MulStageState d) mul_stages.

  Definition unannotMulPipeCanEnq (ty : Kind -> Type) :=
    stagedPipeCanEnq dom (MulStageState d) mul_stages ty.

  Definition unannotMulPipeEnq (ty : Kind -> Type) (inp : ty (MulInput d)) :=
    @stagedPipeEnq dom (MulInput d) (MulStageState d) mul_stages (@mulInitStage input_width) ty inp.

  Definition unannotMulPipeRules (ty : Kind -> Type) :=
    stagedPipeAllStageRules dom (MulStageState d) mul_stages
      (fun ty' st => @mulStageStep input_width ty' mul_bps st) ty.

  Definition unannotMulPipeFirst (ty : Kind -> Type) :=
    stagedPipeFirst dom (MulStageState d) (MulOutput d) mul_stages
      (@mulFinishStage input_width) ty.

  Definition unannotMulPipeDeq (ty : Kind -> Type) :=
    stagedPipeDeq dom (MulStageState d) mul_stages ty.

  (* --- 4B. Iterative Multiplier Instance (`stagedIterTree`) --- *)

  Definition unannotMulIterTree : Tree DomainElem :=
    stagedIterTree dom (MulStageState d) mul_stages.

  Definition mulStepsConst (ty : Kind -> Type) (_ : ty (MulInput d)) : Expr ty (Bit (iterStepsSz mul_stages)) :=
    Const ty (Bit (iterStepsSz mul_stages)) (bits.of_Z (iterStepsSz mul_stages) (Z.of_nat mul_stages)).

  Definition unannotMulIterCanEnq (ty : Kind -> Type) :=
    stagedIterCanEnq dom (MulStageState d) mul_stages ty.

  Definition unannotMulIterEnq (ty : Kind -> Type) (inp : ty (MulInput d)) :=
    @stagedIterEnq dom (MulInput d) (MulStageState d) mul_stages mulStepsConst (@mulInitStage input_width) ty inp.

  Definition unannotMulIterStepRule (ty : Kind -> Type) :=
    stagedIterStep dom (MulStageState d) mul_stages
      (fun ty' st => @mulStageStep input_width ty' mul_bps st) ty.

  Definition unannotMulIterRules (ty : Kind -> Type) :=
    [ unannotMulIterStepRule ty ].

  Definition unannotMulIterFirst (ty : Kind -> Type) :=
    stagedIterFirst dom (MulStageState d) (MulOutput d) mul_stages
      (@mulFinishStage input_width) ty.

  Definition unannotMulIterDeq (ty : Kind -> Type) :=
    stagedIterDeq dom (MulStageState d) mul_stages ty.

  (* --- 4C. Iterative Divider Instance (`stagedIterTree`) --- *)

  Definition unannotDivIterTree : Tree DomainElem :=
    stagedIterTree dom (DivStageState d) div_stages.

  Definition divStepsConst (ty : Kind -> Type) (_ : ty (DivInput d)) : Expr ty (Bit (iterStepsSz div_stages)) :=
    Const ty (Bit (iterStepsSz div_stages)) (bits.of_Z (iterStepsSz div_stages) (Z.of_nat div_stages)).

  Definition unannotDivIterCanEnq (ty : Kind -> Type) :=
    stagedIterCanEnq dom (DivStageState d) div_stages ty.

  Definition unannotDivIterEnq (ty : Kind -> Type) (inp : ty (DivInput d)) :=
    @stagedIterEnq dom (DivInput d) (DivStageState d) div_stages divStepsConst (@divInitStage input_width) ty inp.

  Definition unannotDivIterStepRule (ty : Kind -> Type) :=
    stagedIterStep dom (DivStageState d) div_stages
      (fun ty' st => @divStageStep input_width ty' div_bps st) ty.

  Definition unannotDivIterRules (ty : Kind -> Type) :=
    [ unannotDivIterStepRule ty ].

  Definition unannotDivIterFirst (ty : Kind -> Type) :=
    stagedIterFirst dom (DivStageState d) (DivOutput d) div_stages
      (@divFinishStage input_width) ty.

  Definition unannotDivIterDeq (ty : Kind -> Type) :=
    stagedIterDeq dom (DivStageState d) div_stages ty.

  (* --- 4D. Shared-Accumulator Iterative Mul/Div Instance (`stagedIterTree`) --- *)

  Local Notation shared_max_stages := (Nat.max mul_stages div_stages).

  Definition unannotSharedIterTree : Tree DomainElem :=
    stagedIterTree dom (SharedStageState d) shared_max_stages.

  Definition sharedStepsFn (ty : Kind -> Type) (inp : ty (SharedInput d)) : Expr ty (Bit (iterStepsSz shared_max_stages)) :=
    let sz := iterStepsSz shared_max_stages in
    ITE (##inp`"isMul")
        (Const ty (Bit sz) (bits.of_Z sz (Z.of_nat mul_stages)))
        (Const ty (Bit sz) (bits.of_Z sz (Z.of_nat div_stages))).

  Definition unannotSharedIterCanEnq (ty : Kind -> Type) :=
    stagedIterCanEnq dom (SharedStageState d) shared_max_stages ty.

  Definition unannotSharedIterEnq (ty : Kind -> Type) (inp : ty (SharedInput d)) :=
    @stagedIterEnq dom (SharedInput d) (SharedStageState d) shared_max_stages
      sharedStepsFn (@sharedInitStage input_width) ty inp.

  Definition unannotSharedIterStepRule (ty : Kind -> Type) :=
    stagedIterStep dom (SharedStageState d) shared_max_stages
      (fun ty' st => @sharedStageStep input_width ty' mul_bps div_bps st) ty.

  Definition unannotSharedIterRules (ty : Kind -> Type) :=
    [ unannotSharedIterStepRule ty ].

  Definition unannotSharedIterFirst (ty : Kind -> Type) :=
    stagedIterFirst dom (SharedStageState d) (SharedOutput d) shared_max_stages
      (@sharedFinishStage input_width) ty.

  Definition unannotSharedIterDeq (ty : Kind -> Type) :=
    stagedIterDeq dom (SharedStageState d) shared_max_stages ty.

  (* --- 5E. RegPath-Parameterized Iterative Mul and Div Units (Shared or Separate `acc`) --- *)

  Definition readRegOfKind {ty : Kind -> Type} {t : Tree DomainElem} {k : Kind}
    (r : @RegOfKind t k) : Action ty t k :=
    ReadReg "" r.(rk_path)
      (fun v => Return (eq_rect _ (fun K => Expr ty K) (Var ty _ v) k (Kind_eqb_eq _ _ r.(rk_pf)))).

  Definition writeRegOfKind {ty : Kind -> Type} {t : Tree DomainElem} {k : Kind}
    (r : @RegOfKind t k) (v : Expr ty k) : Action ty t (Bit 0) :=
    WriteReg r.(rk_path)
      (eq_rect k (fun K => Expr ty K) v _ (eq_sym (Kind_eqb_eq _ _ r.(rk_pf))))
      Retv.

  Section RegPathIterativeUnits.
    Variable tree : Tree DomainElem.
    Variable max_stages : nat.
    Local Notation cntSz := (iterStepsSz max_stages).

    (* Passed-in shared/separate datapath `RegOfKind` (`RegPath` + kind witness) *)
    Variable accPath     : @RegOfKind tree (Bit (d + d)).
    Variable shiftOpPath : @RegOfKind tree (Bit d).
    Variable op2Path     : @RegOfKind tree (Bit d).
    Variable stepCntPath : @RegOfKind tree (Bit cntSz).

    (* `IterMul` dedicated control & Approach 3 high-half correction `RegPath`s *)
    Variable mulValidPath : @RegOfKind tree Bool.
    Variable mulDonePath  : @RegOfKind tree Bool.
    Variable hiCorrPath   : @RegOfKind tree (Bit d).

    (* `IterDiv` dedicated control & sign-restoration `RegPath`s *)
    Variable divValidPath : @RegOfKind tree Bool.
    Variable divDonePath  : @RegOfKind tree Bool.
    Variable quotNegPath  : @RegOfKind tree Bool.
    Variable remNegPath   : @RegOfKind tree Bool.

    (* `IterMul` Actions over passed-in `RegPath`s *)
    Definition regPathIterMulCanEnq (ty : Kind -> Type) : Action ty tree Bool :=
      LetA mVal : Bool <- readRegOfKind mulValidPath ;
      LetA dVal : Bool <- readRegOfKind divValidPath ;
      Return (And [ Not #mVal ; Not #dVal ]).

    Definition regPathIterMulEnq (ty : Kind -> Type)
      (op1Signed op2Signed : ty Bool) (op1 op2 : ty (Bit d)) : Action ty tree (Bit 0) :=
      Let neg1   : Bool        <- And [ #op1Signed ; Not (msbIsZero #op1) ] ;
      Let neg2   : Bool        <- And [ #op2Signed ; Not (msbIsZero #op2) ] ;
      Let subOp2 : Bit d       <- ITE #neg1 #op2 $0 ;
      Let subOp1 : Bit d       <- ITE #neg2 #op1 $0 ;
      Let hiCorr : Bit d       <- Add [ #subOp2 ; #subOp1 ] ;
      Let zero2D : Bit (d + d) <- $0 ;
      LetA _ : Bit 0 <- writeRegOfKind mulValidPath (Const ty Bool true) ;
      LetA _ : Bit 0 <- writeRegOfKind mulDonePath  (Const ty Bool false) ;
      LetA _ : Bit 0 <- writeRegOfKind stepCntPath  (Const ty (Bit cntSz) (bits.of_Z cntSz (Z.of_nat mul_stages))) ;
      LetA _ : Bit 0 <- writeRegOfKind shiftOpPath  #op1 ;
      LetA _ : Bit 0 <- writeRegOfKind op2Path      #op2 ;
      LetA _ : Bit 0 <- writeRegOfKind hiCorrPath   #hiCorr ;
      LetA _ : Bit 0 <- writeRegOfKind accPath      #zero2D ;
      Retv.

    Definition regPathIterMulStep (ty : Kind -> Type) : Action ty tree (Bit 0) :=
      LetA mVal : Bool      <- readRegOfKind mulValidPath ;
      LetA mDon : Bool      <- readRegOfKind mulDonePath ;
      LetA cnt  : Bit cntSz <- readRegOfKind stepCntPath ;
      If (And [ #mVal ; Not #mDon ]) Then (
        LetA shiftOp : Bit d       <- readRegOfKind shiftOpPath ;
        LetA op2     : Bit d       <- readRegOfKind op2Path ;
        LetA acc     : Bit (d + d) <- readRegOfKind accPath ;
        Let  extOp2  : Bit (d + d) <- ZeroExtend d #op2 ;
        LetL coreOut : MulCoreState d <- @mulMultiStep input_width ty mul_bps shiftOp extOp2 acc ;
        LetA _ : Bit 0 <- writeRegOfKind shiftOpPath (##coreOut`"shiftOp") ;
        LetA _ : Bit 0 <- writeRegOfKind accPath     (##coreOut`"mulAcc") ;
        Let nextCnt : Bit cntSz <- Sub #cnt (Const ty (Bit cntSz) (bits.of_Z cntSz 1)) ;
        LetA _ : Bit 0 <- writeRegOfKind stepCntPath #nextCnt ;
        If (isZero #nextCnt) Then (
          LetA _ : Bit 0 <- writeRegOfKind mulDonePath (Const ty Bool true) ;
          Retv
        ) Else (
          Retv
        ) ;
        Retv
      ) Else (
        Retv
      ) ;
      Retv.

    Definition regPathIterMulFirst (ty : Kind -> Type) : Action ty tree (Option (Bit (d + d))) :=
      LetA mVal : Bool <- readRegOfKind mulValidPath ;
      LetA mDon : Bool <- readRegOfKind mulDonePath ;
      LetIf resOpt : Option (Bit (d + d)) <-
        If (And [ #mVal ; #mDon ]) Then (
          LetA uProd  : Bit (d + d) <- readRegOfKind accPath ;
          LetA hiCorr : Bit d       <- readRegOfKind hiCorrPath ;
          Let  uHi    : Bit d       <- TruncMsb d d #uProd ;
          Let  uLo    : Bit d       <- TruncLsb d d #uProd ;
          Let  sHi    : Bit d       <- Sub #uHi #hiCorr ;
          Let  sProd  : Bit (d + d) <- Concat #sHi #uLo ;
          Return (mkSome #sProd)
        ) Else (
          Return (mkNone ty)
        ) ;
      Return #resOpt.

    Definition regPathIterMulDeq (ty : Kind -> Type) : Action ty tree (Bit 0) :=
      LetA _ : Bit 0 <- writeRegOfKind mulValidPath (Const ty Bool false) ;
      LetA _ : Bit 0 <- writeRegOfKind mulDonePath  (Const ty Bool false) ;
      Retv.

    (* `IterDiv` Actions over passed-in `RegPath`s *)
    Definition regPathIterDivCanEnq (ty : Kind -> Type) : Action ty tree Bool :=
      LetA mVal : Bool <- readRegOfKind mulValidPath ;
      LetA dVal : Bool <- readRegOfKind divValidPath ;
      Return (And [ Not #mVal ; Not #dVal ]).

    Definition regPathIterDivEnq (ty : Kind -> Type)
      (isSignedDividend isSignedDivisor : ty Bool)
      (dividend divisor : ty (Bit d)) : Action ty tree (Bit 0) :=
      Let neg1    : Bool        <- And [ #isSignedDividend ; Not (msbIsZero #dividend) ] ;
      Let neg2    : Bool        <- And [ #isSignedDivisor  ; Not (msbIsZero #divisor) ] ;
      Let mag1    : Bit d       <- ITE #neg1 (Neg #dividend) #dividend ;
      Let mag2    : Bit d       <- ITE #neg2 (Neg #divisor)  #divisor ;
      Let quotNeg : Bool        <- And [ Not (isZero #divisor) ; Xor [ #neg1 ; #neg2 ] ] ;
      Let remNeg  : Bool        <- #neg1 ;
      Let zero2D  : Bit (d + d) <- $0 ;
      LetA _ : Bit 0 <- writeRegOfKind divValidPath (Const ty Bool true) ;
      LetA _ : Bit 0 <- writeRegOfKind divDonePath  (Const ty Bool false) ;
      LetA _ : Bit 0 <- writeRegOfKind stepCntPath  (Const ty (Bit cntSz) (bits.of_Z cntSz (Z.of_nat div_stages))) ;
      LetA _ : Bit 0 <- writeRegOfKind shiftOpPath  #mag1 ;
      LetA _ : Bit 0 <- writeRegOfKind op2Path      #mag2 ;
      LetA _ : Bit 0 <- writeRegOfKind quotNegPath  #quotNeg ;
      LetA _ : Bit 0 <- writeRegOfKind remNegPath   #remNeg ;
      LetA _ : Bit 0 <- writeRegOfKind accPath      #zero2D ;
      Retv.

    Definition regPathIterDivStep (ty : Kind -> Type) : Action ty tree (Bit 0) :=
      LetA dVal : Bool      <- readRegOfKind divValidPath ;
      LetA dDon : Bool      <- readRegOfKind divDonePath ;
      LetA cnt  : Bit cntSz <- readRegOfKind stepCntPath ;
      If (And [ #dVal ; Not #dDon ]) Then (
        LetA shiftOp : Bit d       <- readRegOfKind shiftOpPath ;
        LetA mag2    : Bit d       <- readRegOfKind op2Path ;
        LetA acc     : Bit (d + d) <- readRegOfKind accPath ;
        Let  rem     : Bit d       <- TruncMsb d d #acc ;
        Let  quot    : Bit d       <- TruncLsb d d #acc ;
        LetL coreOut : DivCoreState d <- @divMultiStep input_width ty div_bps shiftOp mag2 rem quot ;
        Let  nextAcc : Bit (d + d) <- Concat (##coreOut`"rem") (##coreOut`"quot") ;
        LetA _ : Bit 0 <- writeRegOfKind shiftOpPath (##coreOut`"shiftOp") ;
        LetA _ : Bit 0 <- writeRegOfKind accPath     #nextAcc ;
        Let nextCnt : Bit cntSz <- Sub #cnt (Const ty (Bit cntSz) (bits.of_Z cntSz 1)) ;
        LetA _ : Bit 0 <- writeRegOfKind stepCntPath #nextCnt ;
        If (isZero #nextCnt) Then (
          LetA _ : Bit 0 <- writeRegOfKind divDonePath (Const ty Bool true) ;
          Retv
        ) Else (
          Retv
        ) ;
        Retv
      ) Else (
        Retv
      ) ;
      Retv.

    Definition regPathIterDivFirst (ty : Kind -> Type) : Action ty tree (Option (DivSpecOut d)) :=
      LetA dVal : Bool <- readRegOfKind divValidPath ;
      LetA dDon : Bool <- readRegOfKind divDonePath ;
      LetIf resOpt : Option (DivSpecOut d) <-
        If (And [ #dVal ; #dDon ]) Then (
          LetA acc     : Bit (d + d) <- readRegOfKind accPath ;
          LetA quotNeg : Bool        <- readRegOfKind quotNegPath ;
          LetA remNeg  : Bool        <- readRegOfKind remNegPath ;
          Let  uRem    : Bit d       <- TruncMsb d d #acc ;
          Let  uQuot   : Bit d       <- TruncLsb d d #acc ;
          Let  sQuot   : Bit d       <- ITE #quotNeg (Neg #uQuot) #uQuot ;
          Let  sRem    : Bit d       <- ITE #remNeg  (Neg #uRem)  #uRem ;
          Let  out     : DivSpecOut d <- STRUCT {
            "quot" ::= #sQuot ;
            "rem"  ::= #sRem
          } ;
          Return (mkSome #out)
        ) Else (
          Return (mkNone ty)
        ) ;
      Return #resOpt.

    Definition regPathIterDivDeq (ty : Kind -> Type) : Action ty tree (Bit 0) :=
      LetA _ : Bit 0 <- writeRegOfKind divValidPath (Const ty Bool false) ;
      LetA _ : Bit 0 <- writeRegOfKind divDonePath  (Const ty Bool false) ;
      Retv.

  End RegPathIterativeUnits.

End ConcreteMulDivEngines.

(* ===========================================================================
 * 6. MODE-PARAMETERIZED SUBSYSTEM FOR `Impl.v` (`mode : MulDivMode`)
 * =========================================================================== *)

Definition RegIdx : Kind := Bit RegIdxSz.

Section ModeParameterizedSubsystem.
  Variable dom : string.
  Variable input_width mul_stages div_stages : nat.

  Local Notation d := (dataLen input_width).

  Local Lemma xlen_to_d_cast : (Xlen = d + (Xlen - d))%Z.
  Proof. lia. Qed.

  Definition addrToBitD (ty : Kind -> Type) (e : Expr ty Addr) : Expr ty (Bit d) :=
    TruncLsb (Xlen - d) d (castBits xlen_to_d_cast e).

  Definition decodeMulInput (ty : Kind -> Type)
    (op1 : ty (Bit d)) (mulOp : ty MulOp) : LetExpr ty (MulInput d) :=
    LetE isHigh    : Bool  <- ##mulOp`"isHigh" ;
    LetE op1Signed : Bool  <- ##mulOp`"op1Signed" ;
    LetE op2Signed : Bool  <- ##mulOp`"op2Signed" ;
    LetE op2       : Bit d <- addrToBitD (##mulOp`"op2") ;
    @RetE ty (MulInput d) (STRUCT {
      "isHigh"    ::= #isHigh ;
      "op1Signed" ::= #op1Signed ;
      "op2Signed" ::= #op2Signed ;
      "op1"       ::= #op1 ;
      "op2"       ::= #op2
    }).

  Definition decodeDivInput (ty : Kind -> Type)
    (op1 : ty (Bit d)) (divOp : ty DivOp) : LetExpr ty (DivInput d) :=
    LetE isUnsigned : Bool  <- ##divOp`"isUnsigned" ;
    LetE isRem      : Bool  <- ##divOp`"isRem" ;
    LetE op2        : Bit d <- addrToBitD (##divOp`"op2") ;
    @RetE ty (DivInput d) (STRUCT {
      "isUnsigned" ::= #isUnsigned ;
      "isRem"      ::= #isRem ;
      "op1"        ::= #op1 ;
      "op2"        ::= #op2
    }).

  Definition decodeSharedInput (ty : Kind -> Type)
    (op1 : ty (Bit d)) (mulDivOp : ty MulDivUnion) : LetExpr ty (SharedInput d) :=
    LetE isMul      : Bool  <- #mulDivOp `? "Mul" ;
    LetE mulOp      : MulOp <- #mulDivOp `! "Mul" ;
    LetE divOp      : DivOp <- #mulDivOp `! "Div" ;
    LetE isHigh     : Bool  <- ##mulOp`"isHigh" ;
    LetE op1Signed  : Bool  <- ##mulOp`"op1Signed" ;
    LetE op2Signed  : Bool  <- ##mulOp`"op2Signed" ;
    LetE isUnsigned : Bool  <- ##divOp`"isUnsigned" ;
    LetE isRem      : Bool  <- ##divOp`"isRem" ;
    LetE rawOp2     : Addr  <- ITE #isMul (##mulOp`"op2") (##divOp`"op2") ;
    LetE op2        : Bit d <- addrToBitD #rawOp2 ;
    @RetE ty (SharedInput d) (STRUCT {
      "isMul"      ::= #isMul ;
      "isHigh"     ::= #isHigh ;
      "op1Signed"  ::= #op1Signed ;
      "op2Signed"  ::= #op2Signed ;
      "isUnsigned" ::= #isUnsigned ;
      "isRem"      ::= #isRem ;
      "op1"        ::= #op1 ;
      "op2"        ::= #op2
    }).

  Definition modeMulDivTree (mode : MulDivMode) : Tree DomainElem :=
    match mode with
    | PipelinedMul_IterDiv =>
        Node "mulDiv" [
          unannotMulPipeTree dom input_width mul_stages ;
          fifoTree dom MulDivFifoCapacity RegIdx ;
          unannotDivIterTree dom input_width div_stages ;
          fifoTree dom MulDivFifoCapacity RegIdx
        ]
    | IterMul_SeparateIterDiv =>
        Node "mulDiv" [
          unannotMulIterTree dom input_width mul_stages ;
          fifoTree dom MulDivFifoCapacity RegIdx ;
          unannotDivIterTree dom input_width div_stages ;
          fifoTree dom MulDivFifoCapacity RegIdx
        ]
    | IterMul_SharedIterDiv =>
        Node "mulDiv" [
          unannotSharedIterTree dom input_width mul_stages div_stages ;
          fifoTree dom MulDivFifoCapacity RegIdx
        ]
    end.

  Definition modeCanEnq (mode : MulDivMode) (ty : Kind -> Type) (isMul : ty Bool) :
    Action ty (modeMulDivTree mode) Bool :=
    match mode as m return Action ty (modeMulDivTree m) Bool with
    | PipelinedMul_IterDiv =>
        LetIf res : Bool <-
          If #isMul Then (
            LetA c1 : Bool <- liftHeadAction (unannotMulPipeCanEnq dom input_width mul_stages ty) ;
            LetA f2 : Bool <- liftTailAction (liftHeadAction (isFull dom MulDivFifoCapacity RegIdx ty)) ;
            Return (And [ #c1 ; Not #f2 ])
          ) Else (
            LetA c1 : Bool <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterCanEnq dom input_width div_stages ty))) ;
            LetA f2 : Bool <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (isFull dom MulDivFifoCapacity RegIdx ty)))) ;
            Return (And [ #c1 ; Not #f2 ])
          ) ;
        Return #res
    | IterMul_SeparateIterDiv =>
        LetIf res : Bool <-
          If #isMul Then (
            LetA c1 : Bool <- liftHeadAction (unannotMulIterCanEnq dom input_width mul_stages ty) ;
            LetA f2 : Bool <- liftTailAction (liftHeadAction (isFull dom MulDivFifoCapacity RegIdx ty)) ;
            Return (And [ #c1 ; Not #f2 ])
          ) Else (
            LetA c1 : Bool <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterCanEnq dom input_width div_stages ty))) ;
            LetA f2 : Bool <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (isFull dom MulDivFifoCapacity RegIdx ty)))) ;
            Return (And [ #c1 ; Not #f2 ])
          ) ;
        Return #res
    | IterMul_SharedIterDiv =>
        LetA c1 : Bool <- liftHeadAction (unannotSharedIterCanEnq dom input_width mul_stages div_stages ty) ;
        LetA f2 : Bool <- liftTailAction (liftHeadAction (isFull dom MulDivFifoCapacity RegIdx ty)) ;
        Return (And [ #c1 ; Not #f2 ])
    end.

  Definition modeEnqReq (mode : MulDivMode) (ty : Kind -> Type)
    (dst : ty RegIdx) (op1 : ty (Bit d)) (mulDivOp : ty MulDivUnion) :
    Action ty (modeMulDivTree mode) (Bit 0) :=
    match mode as m return Action ty (modeMulDivTree m) (Bit 0) with
    | PipelinedMul_IterDiv =>
        If (#mulDivOp `? "Mul") Then (
          Let mulOp  : MulOp      <- #mulDivOp `! "Mul" ;
          LetL mInp  : MulInput d <- decodeMulInput op1 mulOp ;
          LetA _ : Bit 0 <- liftHeadAction (unannotMulPipeEnq dom mul_stages mInp) ;
          LetA _ : Bit 0 <- liftTailAction (liftHeadAction (enq dom MulDivFifoCapacity dst)) ;
          Retv
        ) Else (
          Let divOp  : DivOp      <- #mulDivOp `! "Div" ;
          LetL dInp  : DivInput d <- decodeDivInput op1 divOp ;
          LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterEnq dom div_stages dInp))) ;
          LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (enq dom MulDivFifoCapacity dst)))) ;
          Retv
        ) ;
        Retv
    | IterMul_SeparateIterDiv =>
        If (#mulDivOp `? "Mul") Then (
          Let mulOp  : MulOp      <- #mulDivOp `! "Mul" ;
          LetL mInp  : MulInput d <- decodeMulInput op1 mulOp ;
          LetA _ : Bit 0 <- liftHeadAction (unannotMulIterEnq dom mul_stages mInp) ;
          LetA _ : Bit 0 <- liftTailAction (liftHeadAction (enq dom MulDivFifoCapacity dst)) ;
          Retv
        ) Else (
          Let divOp  : DivOp      <- #mulDivOp `! "Div" ;
          LetL dInp  : DivInput d <- decodeDivInput op1 divOp ;
          LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterEnq dom div_stages dInp))) ;
          LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (enq dom MulDivFifoCapacity dst)))) ;
          Retv
        ) ;
        Retv
    | IterMul_SharedIterDiv =>
        LetL sInp : SharedInput d <- decodeSharedInput op1 mulDivOp ;
        LetA _ : Bit 0 <- liftHeadAction (unannotSharedIterEnq dom mul_stages div_stages sInp) ;
        LetA _ : Bit 0 <- liftTailAction (liftHeadAction (enq dom MulDivFifoCapacity dst)) ;
        Retv
    end.

  Definition modeAllStageRules (mode : MulDivMode) (ty : Kind -> Type) :
    list (Action ty (modeMulDivTree mode) (Bit 0)) :=
    match mode as m return list (Action ty (modeMulDivTree m) (Bit 0)) with
    | PipelinedMul_IterDiv =>
        map (fun r => liftHeadAction r) (unannotMulPipeRules dom input_width mul_stages ty) ++
        map (fun r => liftTailAction (liftTailAction (liftHeadAction r)))
            (unannotDivIterRules dom input_width div_stages ty)
    | IterMul_SeparateIterDiv =>
        map (fun r => liftHeadAction r) (unannotMulIterRules dom input_width mul_stages ty) ++
        map (fun r => liftTailAction (liftTailAction (liftHeadAction r)))
            (unannotDivIterRules dom input_width div_stages ty)
    | IterMul_SharedIterDiv =>
        map (fun r => liftHeadAction r)
            (unannotSharedIterRules dom input_width mul_stages div_stages ty)
    end.

  Definition MulDivWbResp : Kind :=
    STRUCT_TYPE {
      "dst" :: RegIdx ;
      "res" :: Bit d
    }.

  Definition modePopMulResp (mode : MulDivMode) (ty : Kind -> Type) :
    Action ty (modeMulDivTree mode) (Option MulDivWbResp) :=
    match mode as m return Action ty (modeMulDivTree m) (Option MulDivWbResp) with
    | PipelinedMul_IterDiv =>
        LetA optOut : Option (MulOutput d) <- liftHeadAction (unannotMulPipeFirst dom input_width mul_stages ty) ;
        LetA optDst : Option RegIdx         <- liftTailAction (liftHeadAction (first dom MulDivFifoCapacity RegIdx ty)) ;
        LetIf resOpt : Option MulDivWbResp <-
          If (And [ #optOut `? "Some" ; #optDst `? "Some" ]) Then (
            Let out : MulOutput d <- #optOut `! "Some" ;
            Let dst : RegIdx       <- #optDst `! "Some" ;
            LetA _ : Bit 0 <- liftHeadAction (unannotMulPipeDeq dom input_width mul_stages ty) ;
            LetA _ : Bit 0 <- liftTailAction (liftHeadAction (deq dom MulDivFifoCapacity RegIdx ty)) ;
            Let wb : MulDivWbResp <- STRUCT {
              "dst" ::= #dst ;
              "res" ::= ##out`"res"
            } ;
            Return (mkSome #wb)
          ) Else (
            Return (mkNone ty)
          ) ;
        Return #resOpt
    | IterMul_SeparateIterDiv =>
        LetA optOut : Option (MulOutput d) <- liftHeadAction (unannotMulIterFirst dom input_width mul_stages ty) ;
        LetA optDst : Option RegIdx         <- liftTailAction (liftHeadAction (first dom MulDivFifoCapacity RegIdx ty)) ;
        LetIf resOpt : Option MulDivWbResp <-
          If (And [ #optOut `? "Some" ; #optDst `? "Some" ]) Then (
            Let out : MulOutput d <- #optOut `! "Some" ;
            Let dst : RegIdx       <- #optDst `! "Some" ;
            LetA _ : Bit 0 <- liftHeadAction (unannotMulIterDeq dom input_width mul_stages ty) ;
            LetA _ : Bit 0 <- liftTailAction (liftHeadAction (deq dom MulDivFifoCapacity RegIdx ty)) ;
            Let wb : MulDivWbResp <- STRUCT {
              "dst" ::= #dst ;
              "res" ::= ##out`"res"
            } ;
            Return (mkSome #wb)
          ) Else (
            Return (mkNone ty)
          ) ;
        Return #resOpt
    | IterMul_SharedIterDiv =>
        LetA optOut : Option (SharedOutput d) <- liftHeadAction (unannotSharedIterFirst dom input_width mul_stages div_stages ty) ;
        LetA optDst : Option RegIdx            <- liftTailAction (liftHeadAction (first dom MulDivFifoCapacity RegIdx ty)) ;
        LetIf resOpt : Option MulDivWbResp <-
          If (And [ #optOut `? "Some" ; #optDst `? "Some" ]) Then (
            Let out : SharedOutput d <- #optOut `! "Some" ;
            Let dst : RegIdx          <- #optDst `! "Some" ;
            LetA _ : Bit 0 <- liftHeadAction (unannotSharedIterDeq dom input_width mul_stages div_stages ty) ;
            LetA _ : Bit 0 <- liftTailAction (liftHeadAction (deq dom MulDivFifoCapacity RegIdx ty)) ;
            Let wb : MulDivWbResp <- STRUCT {
              "dst" ::= #dst ;
              "res" ::= ##out`"res"
            } ;
            Return (mkSome #wb)
          ) Else (
            Return (mkNone ty)
          ) ;
        Return #resOpt
    end.

  Definition modePopDivResp (mode : MulDivMode) (ty : Kind -> Type) :
    Action ty (modeMulDivTree mode) (Option MulDivWbResp) :=
    match mode as m return Action ty (modeMulDivTree m) (Option MulDivWbResp) with
    | PipelinedMul_IterDiv =>
        LetA optOut : Option (DivOutput d) <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterFirst dom input_width div_stages ty))) ;
        LetA optDst : Option RegIdx         <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (first dom MulDivFifoCapacity RegIdx ty)))) ;
        LetIf resOpt : Option MulDivWbResp <-
          If (And [ #optOut `? "Some" ; #optDst `? "Some" ]) Then (
            Let out : DivOutput d <- #optOut `! "Some" ;
            Let dst : RegIdx       <- #optDst `! "Some" ;
            LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterDeq dom input_width div_stages ty))) ;
            LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (deq dom MulDivFifoCapacity RegIdx ty)))) ;
            Let wb : MulDivWbResp <- STRUCT {
              "dst" ::= #dst ;
              "res" ::= ##out`"res"
            } ;
            Return (mkSome #wb)
          ) Else (
            Return (mkNone ty)
          ) ;
        Return #resOpt
    | IterMul_SeparateIterDiv =>
        LetA optOut : Option (DivOutput d) <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterFirst dom input_width div_stages ty))) ;
        LetA optDst : Option RegIdx         <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (first dom MulDivFifoCapacity RegIdx ty)))) ;
        LetIf resOpt : Option MulDivWbResp <-
          If (And [ #optOut `? "Some" ; #optDst `? "Some" ]) Then (
            Let out : DivOutput d <- #optOut `! "Some" ;
            Let dst : RegIdx       <- #optDst `! "Some" ;
            LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftHeadAction (unannotDivIterDeq dom input_width div_stages ty))) ;
            LetA _ : Bit 0 <- liftTailAction (liftTailAction (liftTailAction (liftHeadAction (deq dom MulDivFifoCapacity RegIdx ty)))) ;
            Let wb : MulDivWbResp <- STRUCT {
              "dst" ::= #dst ;
              "res" ::= ##out`"res"
            } ;
            Return (mkSome #wb)
          ) Else (
            Return (mkNone ty)
          ) ;
        Return #resOpt
    | IterMul_SharedIterDiv =>
        Return (mkNone ty)
    end.

End ModeParameterizedSubsystem.
