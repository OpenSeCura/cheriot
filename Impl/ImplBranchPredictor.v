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

  Definition preDecodeBranch (inst : ty Inst) : LetExpr ty PreBranchInfo :=
    LetE opcode   : Bit 5        <- #inst`[6:2] ;
    LetE funct3   : Bit 3        <- #inst`[14:12] ;
    LetE cd       : Bit RegIdxSz <- getCd inst ;
    LetE cs1      : Bit RegIdxSz <- getCs1 inst ;
    LetE isCjal   : Bool         <- Eq #opcode $(Z.shiftr 0x6f 2) ;
    LetE isBranch : Bool         <- And [ Eq #opcode $(Z.shiftr 0x63 2) ; Not (Eq (#funct3`[2:1]) $1) ] ;
    LetE isCjalr  : Bool         <- And [ Eq #opcode $(Z.shiftr 0x67 2) ; isZero #funct3 ] ;
    LetE isCall   : Bool         <- And [ Or [ #isCjal ; #isCjalr ] ; Eq #cd $Cra ] ;
    LetE isReturn : Bool         <- And [ #isCjalr ; isZero #cd ; Eq #cs1 $Cra ] ;
    @RetE ty PreBranchInfo (STRUCT {
      "isCjal"   ::= #isCjal ;
      "isBranch" ::= #isBranch ;
      "isCjalr"  ::= #isCjalr ;
      "isCall"   ::= #isCall ;
      "isReturn" ::= #isReturn
    }).
End PreDecodeBranch.

Record NoInstPredIfc := {
  noInst_BpTree             : Tree Elem ;
  noInst_getPred            : forall {ty : Kind -> Type}, ty Addr -> Action ty noInst_BpTree NoInstPredOut ;
  noInst_updByFetch         : forall {ty : Kind -> Type}, ty Addr -> ty (Bit LgFetchParcels) -> ty Bool ->
                              ty Addr -> ty Bool -> ty PreBranchInfo -> ty Bool ->
                              Action ty noInst_BpTree (Bit 0) ;
  noInst_updTargetByExecute : forall {ty : Kind -> Type}, ty Addr -> ty Addr -> ty PreBranchInfo -> Action ty noInst_BpTree (Bit 0) ;
  noInst_updException       : forall {ty : Kind -> Type}, ty Addr -> Action ty noInst_BpTree (Bit 0)
}.

Definition bpTree (noInstTree withInstTree : Tree Elem) : Tree Elem :=
  Node "" [
    Node "noInst"   [ noInstTree ] ;
    Node "withInst" [ withInstTree ]
  ].

(* The predictor interface the pipeline uses.  withInst_BpTree is the state of the whole predictor;
 * the withInst_noInst_* functions just call the level-1 predictor. *)
Record WithInstPredIfc := {
  withInst_BpTree            : Tree Elem ;
  withInst_noInst_getPred    : forall {ty : Kind -> Type}, ty Addr -> Action ty withInst_BpTree NoInstPredOut ;
  withInst_noInst_updByFetch : forall {ty : Kind -> Type}, ty Addr -> ty (Bit LgFetchParcels) -> ty Bool ->
                               ty Addr -> ty Bool -> ty PreBranchInfo -> ty Bool ->
                               Action ty withInst_BpTree (Bit 0) ;
  withInst_getPred           : forall {ty : Kind -> Type}, ty Addr -> ty Addr -> ty Inst -> ty PreBranchInfo -> Action ty withInst_BpTree Addr ;
  withInst_updCf             : forall {ty : Kind -> Type}, ty Addr -> ty CfPayload -> Action ty withInst_BpTree (Bit 0) ;
  withInst_updException      : forall {ty : Kind -> Type}, ty Addr -> Action ty withInst_BpTree (Bit 0)
}.

Section ImplBranchPredictor.

  (* =========================================================================
   * Level 1 (NoInst) Predictor Implementation
   * ========================================================================= *)

  Definition implNoInstTree : Tree Elem :=
    Node "" [].

  Section NoInstTy.
    Variable ty : Kind -> Type.

    Definition implNoInst_getPred (pc : ty Addr) : Action ty implNoInstTree NoInstPredOut :=
      Let alignedPc  : Addr               <- {< TruncMsb (AddrSz - LgLineBytes) LgLineBytes #pc,
                                                Const ty (Bit LgLineBytes) Zmod.zero >} ;
      Let nextPktPc  : Addr               <- Add [ #alignedPc ; $(Z.of_nat LineBytes) ] ;
      Let exitParcel : Bit LgFetchParcels <- Const ty (Bit LgFetchParcels) (InvDefault _) ;
      @Return ty _ NoInstPredOut (STRUCT {
        "exitParcel" ::= #exitParcel ;
        "predPc"     ::= #nextPktPc
      }).

    Definition implNoInst_updByFetch
      (entryPc : ty Addr)
      (lastParcel : ty (Bit LgFetchParcels))
      (exitMismatch : ty Bool)
      (l2PredPc : ty Addr)
      (predPcMismatch : ty Bool)
      (pb : ty PreBranchInfo)
      (isStraddle : ty Bool)
      : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updTargetByExecute (pc target : ty Addr) (pb : ty PreBranchInfo) : Action ty implNoInstTree (Bit 0) :=
      Retv.

    Definition implNoInst_updException (pc : ty Addr) : Action ty implNoInstTree (Bit 0) :=
      Retv.

  End NoInstTy.

  Definition implNoInstIfc : NoInstPredIfc := {|
    noInst_BpTree             := implNoInstTree ;
    noInst_getPred            := implNoInst_getPred ;
    noInst_updByFetch         := implNoInst_updByFetch ;
    noInst_updTargetByExecute := implNoInst_updTargetByExecute ;
    noInst_updException       := implNoInst_updException
  |}.

  (* =========================================================================
   * Level 2 (WithInst) Predictor Implementation
   * ========================================================================= *)

  Section WithInst.
    Variable noInstIfc : NoInstPredIfc.

    Definition implWithInstTree : Tree Elem :=
      Node "" [].

    Section WithInstTy.
      Variable ty : Kind -> Type.

      Local Abbreviation tree := (bpTree noInstIfc.(noInst_BpTree) implWithInstTree).

      Local Definition np_noInst : NodePath tree :=
        Eval cbv in (embedNodeIntoPath (getNodePath tree ".noInst") singletonChildPath).

      Definition implWithInst_noInst_getPred (pc : ty Addr) : Action ty tree NoInstPredOut :=
        liftAction np_noInst (noInstIfc.(noInst_getPred) pc).

      Definition implWithInst_noInst_updByFetch
        (entryPc : ty Addr)
        (lastParcel : ty (Bit LgFetchParcels))
        (exitMismatch : ty Bool)
        (l2PredPc : ty Addr)
        (predPcMismatch : ty Bool)
        (pb : ty PreBranchInfo)
        (isStraddle : ty Bool)
        : Action ty tree (Bit 0) :=
        liftAction np_noInst
          (noInstIfc.(noInst_updByFetch) entryPc lastParcel exitMismatch l2PredPc predPcMismatch pb isStraddle).

      Definition implWithInst_getPred
        (pc predPc : ty Addr)
        (inst : ty Inst)
        (pb : ty PreBranchInfo)
        : Action ty tree Addr :=
        Let isComp        : Bool <- isCompressed inst ;
        Let isCjal        : Bool <- ##pb`"isCjal" ;
        Let isBranch      : Bool <- ##pb`"isBranch" ;
        Let isCjalr       : Bool <- ##pb`"isCjalr" ;

        Let jOffset       : Addr <- getJImm inst ;
        Let jumpTarget    : Addr <- Add [ #pc ; #jOffset ] ;

        Let bOffset       : Addr <- getBImm inst ;
        Let isPredTaken   : Bool <- FromBit Bool (TruncMsb 1 (AddrSz - 1) #bOffset) ;
        Let branchTarget  : Addr <- Add [ #pc ; #bOffset ] ;
        Let isTakenBranch : Bool <- And [ #isBranch ; #isPredTaken ] ;
        Let l2PredPc      : Addr <- caseDefault [
                                        (#isCjal,        #jumpTarget) ;
                                        (#isTakenBranch, #branchTarget)
                                      ] #predPc ;

        Return #l2PredPc.

      Definition implWithInst_updCf (pc : ty Addr) (cf : ty CfPayload) : Action ty tree (Bit 0) :=
        Let target     : Addr                  <- ##cf`"NewPcc"`"addr" ;
        Let cfOp       : CfOp                  <- ##cf`"CfOp" ;
        Let isAddrOnly : Bool                  <- #cfOp `? "ControlFlowAddrOnly" ;
        Let addrOnlyOp : ControlFlowAddrOnlyOp <- #cfOp `! "ControlFlowAddrOnly" ;
        Let isAddrECap : Bool                  <- #cfOp `? "ControlFlowAddrECap" ;
        Let addrECap   : ControlFlowAddrECap   <- #cfOp `! "ControlFlowAddrECap" ;
        Let addrECapOp : ControlFlowAddrECapOp <- ##addrECap`"op" ;
        Let cjalrOp    : CjalrOp               <- #addrECapOp `! "Cjalr" ;
        Let isCjal     : Bool                  <- And [ #isAddrOnly ; #addrOnlyOp `? "Cjal" ] ;
        Let isBranch   : Bool                  <- And [ #isAddrOnly ; #addrOnlyOp `? "Branch" ] ;
        Let isCjalr    : Bool                  <- And [ #isAddrECap ; #addrECapOp `? "Cjalr" ] ;
        Let isCall     : Bool                  <- Or [ And [ #isCjal ; #addrOnlyOp `! "Cjal" ] ;
                                                       And [ #isCjalr ; ##cjalrOp`"isCall" ] ] ;
        Let isReturn   : Bool                  <- And [ #isCjalr ; ##cjalrOp`"isReturn" ] ;
        Let pb         : PreBranchInfo         <- STRUCT {
          "isCjal"   ::= #isCjal ;
          "isBranch" ::= #isBranch ;
          "isCjalr"  ::= #isCjalr ;
          "isCall"   ::= #isCall ;
          "isReturn" ::= #isReturn
        } ;
        liftAction np_noInst (noInstIfc.(noInst_updTargetByExecute) pc target pb).

      Definition implWithInst_updException (pc : ty Addr) : Action ty tree (Bit 0) :=
        liftAction np_noInst (noInstIfc.(noInst_updException) pc).
    End WithInstTy.

    Definition implWithInstIfc : WithInstPredIfc := {|
      withInst_BpTree            := bpTree noInstIfc.(noInst_BpTree) implWithInstTree ;
      withInst_noInst_getPred    := implWithInst_noInst_getPred ;
      withInst_noInst_updByFetch := implWithInst_noInst_updByFetch ;
      withInst_getPred           := implWithInst_getPred ;
      withInst_updCf             := implWithInst_updCf ;
      withInst_updException      := implWithInst_updException
    |}.
  End WithInst.

End ImplBranchPredictor.
