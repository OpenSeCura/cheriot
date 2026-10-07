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

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Two-Level Branch Predictor Interface & Implementation
 * =========================================================================== *)

Definition Plus2OrPlus4Type := [
  ("Plus2"%string, Bit 0) ;
  ("Plus4"%string, Bit 0)
].
Definition Plus2OrPlus4 := TaggedUnion Plus2OrPlus4Type.

Record NoInstPredIfc {ty : Kind -> Type} := {
  noInstTree          : Tree DomainElem ;
  noInst_getPred      : ty Addr -> Action ty noInstTree Addr ;
  noInst_updNoCf      : ty Addr -> Action ty noInstTree (Bit 0) ;
  noInst_updTarget    : ty Addr -> ty Addr -> Action ty noInstTree (Bit 0) ;
  noInst_updInstSize  : ty Addr -> ty Plus2OrPlus4 -> Action ty noInstTree (Bit 0) ;
  noInst_updException : ty Addr -> Action ty noInstTree (Bit 0)
}.

Definition bpTree (noInstTree withInstTree : Tree DomainElem) : Tree DomainElem :=
  Node "bp" [
    Node "noInst"   [ noInstTree ] ;
    Node "withInst" [ withInstTree ]
  ].

Record WithInstPredIfc (noInstTree : Tree DomainElem) {ty : Kind -> Type} := {
  withInstTree     : Tree DomainElem ;
  withInst_getPred : ty Addr -> ty Addr -> ty Inst -> ty DecodeOut -> Action ty (bpTree noInstTree withInstTree) Addr ;
  withInst_updCf   : ty Addr -> ty CfPayload -> Action ty (bpTree noInstTree withInstTree) (Bit 0)
}.

Section ImplBranchPredictor.
  Variable dom : string.

  (* =========================================================================
   * Level 1 (NoInst) Predictor Implementation
   * ========================================================================= *)

  Definition implNoInstTree : Tree DomainElem :=
    Node "noInstImpl" [].

  Section NoInstTy.
    Variable ty : Kind -> Type.

    Definition implNoInst_getPred (pc : ty Addr) : Action ty implNoInstTree Addr :=
      Return (Add [ #pc ; $(InstSz / 8) ]).

    Definition implNoInst_updNoCf (pc : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updTarget (pc target : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updInstSize (pc : ty Addr) (sz : ty Plus2OrPlus4) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updException (pc : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInstIfc : @NoInstPredIfc ty := {|
      noInstTree          := implNoInstTree ;
      noInst_getPred      := implNoInst_getPred ;
      noInst_updNoCf      := implNoInst_updNoCf ;
      noInst_updTarget    := implNoInst_updTarget ;
      noInst_updInstSize  := implNoInst_updInstSize ;
      noInst_updException := implNoInst_updException
    |}.
  End NoInstTy.

  (* =========================================================================
   * Level 2 (WithInst) Predictor Implementation
   * ========================================================================= *)

  Section WithInst.
    Variable noInstIfc : forall ty, @NoInstPredIfc ty.

    Definition implWithInstTree : Tree DomainElem :=
      Node "withInstImpl" [].

    Section WithInstTy.
      Variable ty : Kind -> Type.

      Local Abbreviation noInstTree := (noInstIfc ty).(noInstTree).
      Local Abbreviation tree := (bpTree noInstTree implWithInstTree).

      Local Definition np_noInst : NodePath tree :=
        Eval cbn in (embedNodeIntoPath (getNodePath tree "bp.noInst") singletonChildPath).

      Definition implWithInst_getPred (pc predPc : ty Addr) (inst : ty Inst) (decodeOut : ty DecodeOut) : Action ty tree Addr :=
        Let instGroup    : InstGroup       <- ##decodeOut`"instGroup" ;
        Let decodeExc    : DecodeException <- ##decodeOut`"decodeExc" ;
        Let hasDecodeExc : Bool            <- Or [ ##decodeExc`"illegal" ; ##decodeExc`"asr" ] ;

        Let isComp       : Bool            <- ##instGroup`"isCompressed" ;
        Let instSize     : Plus2OrPlus4    <-
          ITE #isComp
            (UNION (Plus2OrPlus4Type, "Plus2" ::= Const ty (Bit 0) Zmod.zero))
            (UNION (Plus2OrPlus4Type, "Plus4" ::= Const ty (Bit 0) Zmod.zero)) ;
        Let stepBytes    : Addr            <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
        Let seqPc        : Addr            <- Add [ #pc ; #stepBytes ] ;

        Let isJump       : Bool            <- And [ Not #hasDecodeExc ; ##instGroup`"Cjal" ] ;
        Let jOffset      : Addr            <- getJImm inst ;
        Let jumpTarget   : Addr            <- Add [ #pc ; #jOffset ] ;

        Let isBranch     : Bool            <- And [ Not #hasDecodeExc ; ##instGroup`"Branch" ] ;
        Let bOffset      : Addr            <- getBImm inst ;
        Let isPredTaken  : Bool            <- FromBit Bool (TruncMsb 1 (AddrSz - 1) #bOffset) ;
        Let branchTarget : Addr            <- Add [ #pc ; #bOffset ] ;

        Let isOtherCf    : Bool            <- Or [ #hasDecodeExc ;
                                                   ##instGroup`"Cjalr" ;
                                                   ##instGroup`"ECall" ;
                                                   ##instGroup`"EBreak" ;
                                                   ##instGroup`"Mret" ] ;
        Let isNotCf      : Bool            <- Not (Or [ #isJump ; #isBranch ; #isOtherCf ]) ;

        Let l2PredPc     : Addr            <- Or [
          ITE0 #isJump      #jumpTarget ;
          ITE0 #isBranch    (ITE #isPredTaken #branchTarget #seqPc) ;
          ITE0 #isOtherCf   #predPc ;
          ITE0 #isNotCf     #seqPc
        ] ;

        If (And [ Or [ #isJump ; #isBranch ] ; Not (Eq #predPc #l2PredPc) ]) Then (
          liftAction np_noInst ((noInstIfc ty).(noInst_updTarget) pc l2PredPc)
        ) ;

        If (And [ #isNotCf ; Not (Eq #predPc #seqPc) ]) Then (
          liftAction np_noInst ((noInstIfc ty).(noInst_updNoCf) pc)
        ) ;

        If (And [ Or [ #isNotCf ; And [ #isBranch ; Not #isPredTaken ] ] ;
                  Not (Eq #predPc #seqPc) ]) Then (
          liftAction np_noInst ((noInstIfc ty).(noInst_updInstSize) pc instSize)
        ) ;

        Return #l2PredPc.

      Definition implWithInst_updCf (pc : ty Addr) (cf : ty CfPayload) : Action ty tree (Bit 0) :=
        Let cfOp       : CfOp                  <- ##cf`"CfOp" ;
        Let target     : Addr                  <- ##cf`"NewPcc"`"addr" ;
        Let isAddrECap : Bool                  <- #cfOp `? "ControlFlowAddrECap" ;
        Let addrECapOp : ControlFlowAddrECapOp <- #cfOp `! "ControlFlowAddrECap" ;
        Let isMretTrap : Bool                  <- #addrECapOp `? "MretTrap" ;
        Let mretTrapOp : MretTrapOp            <- #addrECapOp `! "MretTrap" ;
        Let isTrap     : Bool                  <- And [ #isAddrECap ; #isMretTrap ; #mretTrapOp `? "Trap" ] ;
        If #isTrap Then (
          liftAction np_noInst ((noInstIfc ty).(noInst_updException) pc)
        ) Else (
          liftAction np_noInst ((noInstIfc ty).(noInst_updTarget) pc target)
        ) ;
        Retv.

      Definition implWithInstIfc : @WithInstPredIfc noInstTree ty := {|
        withInstTree     := implWithInstTree ;
        withInst_getPred := implWithInst_getPred ;
        withInst_updCf   := implWithInst_updCf
      |}.

    End WithInstTy.
  End WithInst.

  Definition implBpTree : Tree DomainElem :=
    bpTree implNoInstTree implWithInstTree.

End ImplBranchPredictor.
