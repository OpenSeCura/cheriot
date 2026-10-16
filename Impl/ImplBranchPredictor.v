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
From Cheriot Require Import SpecDefines ImplCommon.

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

Definition NoInstPredOut := STRUCT_TYPE {
  "exitParcel" :: Bit LgFetchParcels ;
  "predPc"     :: Addr
}.

Section PreDecodeBranch.
  Variable ty : Kind -> Type.

  Definition preDecodeBranch (inst : ty Inst) (hasFault : ty Bool) : LetExpr ty PreBranchInfo :=
    LetE isComp   : Bool  <- isCompressed inst ;
    LetE opcode   : Bit 5 <- #inst`[6:2] ;
    LetE funct3   : Bit 3 <- #inst`[14:12] ;
    LetE isCjal   : Bool  <- Eq #opcode $(Z.shiftr 0x6f 2) ;
    LetE isBranch : Bool  <- And [ Eq #opcode $(Z.shiftr 0x63 2) ; Not (Eq (#funct3`[2:1]) $1) ] ;
    LetE isCjalr  : Bool  <- And [ Eq #opcode $(Z.shiftr 0x67 2) ; isZero #funct3 ] ;
    LetE isSystem : Bool  <- Eq #opcode $(Z.shiftr 0x73 2) ;
    @RetE ty PreBranchInfo (STRUCT {
      "isCompressed" ::= #isComp ;
      "isCjal"       ::= And [ Not #hasFault ; #isCjal ] ;
      "isBranch"     ::= And [ Not #hasFault ; #isBranch ] ;
      "isOtherCf"    ::= Or [ #hasFault ; #isCjalr ; #isSystem ]
    }).
End PreDecodeBranch.

Record NoInstPredIfc {ty : Kind -> Type} := {
  noInstTree              : Tree DomainElem ;
  noInst_getPred          : ty Addr -> Action ty noInstTree NoInstPredOut ;
  noInst_updNoCf          : ty Addr -> Action ty noInstTree (Bit 0) ;
  noInst_updStraddle      : ty Addr -> Action ty noInstTree (Bit 0) ;
  noInst_updTargetByFetch : ty Addr -> ty Addr -> ty PreBranchInfo -> Action ty noInstTree (Bit 0) ;
  noInst_updCfByExecute   : ty Addr -> ty CfPayload -> ty PreBranchInfo -> Action ty noInstTree (Bit 0) ;
  noInst_updInstSize      : ty Addr -> ty Bool -> Action ty noInstTree (Bit 0) ;
  noInst_updException     : ty Addr -> Action ty noInstTree (Bit 0)
}.

Definition bpTree (noInstTree withInstTree : Tree DomainElem) : Tree DomainElem :=
  Node "" [
    Node "noInst"   [ noInstTree ] ;
    Node "withInst" [ withInstTree ]
  ].

Record WithInstPredIfc (noInstTree : Tree DomainElem) {ty : Kind -> Type} := {
  withInstTree          : Tree DomainElem ;
  withInst_getPred      : ty Addr -> ty Addr -> ty Inst -> ty PreBranchInfo -> Action ty (bpTree noInstTree withInstTree) Addr ;
  withInst_updCf        : ty Addr -> ty CfPayload -> ty PreBranchInfo -> Action ty (bpTree noInstTree withInstTree) (Bit 0) ;
  withInst_updException : ty Addr -> Action ty (bpTree noInstTree withInstTree) (Bit 0)
}.

Section ImplBranchPredictor.
  Variable dom : string.

  (* =========================================================================
   * Level 1 (NoInst) Predictor Implementation
   * ========================================================================= *)

  Definition implNoInstTree : Tree DomainElem :=
    Node "" [].

  Section NoInstTy.
    Variable ty : Kind -> Type.

    Definition implNoInst_getPred (pc : ty Addr) : Action ty implNoInstTree NoInstPredOut :=
      Let alignedPc  : Addr               <- {< TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #pc,
                                                Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let nextPktPc  : Addr               <- Add [ #alignedPc ; $NumBytesFullCapSz ] ;
      Let exitParcel : Bit LgFetchParcels <- Const ty (Bit LgFetchParcels) (InvDefault _) ;
      @Return ty _ NoInstPredOut (STRUCT {
        "exitParcel" ::= #exitParcel ;
        "predPc"     ::= #nextPktPc
      }).

    Definition implNoInst_updNoCf (pc : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updStraddle (pc : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updTargetByFetch (pc target : ty Addr) (pb : ty PreBranchInfo) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updCfByExecute (pc : ty Addr) (cf : ty CfPayload) (pb : ty PreBranchInfo) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updInstSize (pc : ty Addr) (sz : ty Bool) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updException (pc : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInstIfc : @NoInstPredIfc ty := {|
      noInstTree              := implNoInstTree ;
      noInst_getPred          := implNoInst_getPred ;
      noInst_updNoCf          := implNoInst_updNoCf ;
      noInst_updStraddle      := implNoInst_updStraddle ;
      noInst_updTargetByFetch := implNoInst_updTargetByFetch ;
      noInst_updCfByExecute   := implNoInst_updCfByExecute ;
      noInst_updInstSize      := implNoInst_updInstSize ;
      noInst_updException     := implNoInst_updException
    |}.
  End NoInstTy.

  (* =========================================================================
   * Level 2 (WithInst) Predictor Implementation
   * ========================================================================= *)

  Section WithInst.
    Variable noInstIfc : forall ty, @NoInstPredIfc ty.

    Definition implWithInstTree : Tree DomainElem :=
      Node "" [].

    Section WithInstTy.
      Variable ty : Kind -> Type.

      Local Abbreviation noInstTree := (noInstIfc ty).(noInstTree).
      Local Abbreviation tree := (bpTree noInstTree implWithInstTree).

      Local Definition np_noInst : NodePath tree :=
        Eval cbn in (embedNodeIntoPath (getNodePath tree ".noInst") singletonChildPath).

      Definition implWithInst_getPred
        (pc predPc : ty Addr)
        (inst : ty Inst)
        (pb : ty PreBranchInfo)
        : Action ty tree Addr :=
        Let isComp       : Bool         <- ##pb`"isCompressed" ;
        Let isCjal       : Bool         <- ##pb`"isCjal" ;
        Let isBranch     : Bool         <- ##pb`"isBranch" ;
        Let isOtherCf    : Bool         <- ##pb`"isOtherCf" ;
        Let isNotCf      : Bool         <- Not (Or [ #isCjal ; #isBranch ; #isOtherCf ]) ;

        Let stepBytes    : Addr         <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
        Let seqPc        : Addr         <- Add [ #pc ; #stepBytes ] ;

        Let jOffset      : Addr         <- getJImm inst ;
        Let jumpTarget   : Addr         <- Add [ #pc ; #jOffset ] ;

        Let bOffset      : Addr         <- getBImm inst ;
        Let isPredTaken  : Bool         <- FromBit Bool (TruncMsb 1 (AddrSz - 1) #bOffset) ;
        Let branchTarget : Addr         <- Add [ #pc ; #bOffset ] ;
        Let isTakenBranch : Bool <- And [ #isBranch ; #isPredTaken ] ;
        Let l2PredPc      : Addr <- caseDefault [
                                        (#isCjal,        #jumpTarget) ;
                                        (#isTakenBranch, #branchTarget) ;
                                        (#isOtherCf,     #predPc)
                                      ] #seqPc ;

        If (And [ Or [ #isCjal ; #isBranch ] ; Not (Eq #predPc #l2PredPc) ]) Then (
          liftAction np_noInst ((noInstIfc ty).(noInst_updTargetByFetch) pc l2PredPc pb)
        ) ;

        If (And [ #isNotCf ; Not (Eq #predPc #seqPc) ]) Then (
          liftAction np_noInst ((noInstIfc ty).(noInst_updNoCf) pc)
        ) ;

        Act (liftAction np_noInst ((noInstIfc ty).(noInst_updInstSize) pc isComp)) ;

        Return #l2PredPc.

      Definition implWithInst_updCf (pc : ty Addr) (cf : ty CfPayload) (pb : ty PreBranchInfo) : Action ty tree (Bit 0) :=
        liftAction np_noInst ((noInstIfc ty).(noInst_updCfByExecute) pc cf pb).

      Definition implWithInst_updException (pc : ty Addr) : Action ty tree (Bit 0) :=
        liftAction np_noInst ((noInstIfc ty).(noInst_updException) pc).

      Definition implWithInstIfc : @WithInstPredIfc noInstTree ty := {|
        withInstTree          := implWithInstTree ;
        withInst_getPred      := implWithInst_getPred ;
        withInst_updCf        := implWithInst_updCf ;
        withInst_updException := implWithInst_updException
      |}.

    End WithInstTy.
  End WithInst.

  Definition implBpTree : Tree DomainElem :=
    bpTree implNoInstTree implWithInstTree.

End ImplBranchPredictor.
