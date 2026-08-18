(*
 * Copyright 2026 Google LLC (Cherified Team)
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
From Guru Require Import Library Syntax Notations Composition.
From Cheriot Require Import SpecDefines Alu.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.
Local Open Scope string_scope.

(* ===========================================================================
   COMPRESSED PAYLOADS AND UNIONS
   =========================================================================== *)

Definition CfPayloadCompressed := STRUCT_TYPE {
  "NewPcc" :: FullCapWithTag ;
  "CfOp"   :: CfOp
}.

Definition ScrCsrPayloadCompressed := STRUCT_TYPE {
  "SpecialDest"  :: TaggedUnion ScrCsrIdx ;
  "SpecialValue" :: FullCapWithTag
}.

Definition CfScrCsrCompressedType := [
  ("ControlFlow"%string, CfPayloadCompressed) ;
  ("ScrCsr"%string,      ScrCsrPayloadCompressed)
].
Definition CfScrCsrUnionCompressed := TaggedUnion CfScrCsrCompressedType.

Definition NotDeferredUnionCompressedType := [
  ("NormalFenceI"%string, NormalFenceIUnion) ;
  ("CfScrCsr"%string,     CfScrCsrUnionCompressed)
].
Definition NotDeferredUnionCompressed := TaggedUnion NotDeferredUnionCompressedType.

Definition NoExceptionUnionCompressedType := [
  ("Deferred"%string,    DeferredUnion) ;
  ("NotDeferred"%string, NotDeferredUnionCompressed)
].
Definition NoExceptionUnionCompressed := TaggedUnion NoExceptionUnionCompressedType.

Definition AluOpUnionCompressedType := [
  ("Exception"%string,   ExceptionInfo) ;
  ("NoException"%string, NoExceptionUnionCompressed)
].
Definition AluOpUnionCompressed := TaggedUnion AluOpUnionCompressedType.

Definition AluOutUnionCompressed := STRUCT_TYPE {
  "isComp"      :: Bool ;
  "dstIdx"      :: Bit RegIdxSz ;
  "dstValue"    :: FullCapWithTag ;
  "Op"          :: AluOpUnionCompressed ;
  "isFenceIAck" :: Bool
}.

(* ===========================================================================
   REGISTER FILE SUBTREE AND REGPATH DEFINITIONS (COMPRESSED)
   =========================================================================== *)

(* 1. Child Leaf Lists (Compressed) *)

Definition gprLeavesCompressed : list (Tree Elem) :=
  map (fun '(_, idx) =>
    Leaf ("gpr_" ++ hex_string_of_Z idx)%string
         (EReg (Build_Reg FullCapWithTag (Some (getDefault _))))
  ) (enumerate (repeat tt (Z.to_nat NumRegs))).

Definition scrLeavesCompressed : list (Tree Elem) :=
  map (fun '(name, _) =>
    Leaf name (EReg (Build_Reg FullCapWithTag (Some (getDefault _))))
  ) ScrTable.

Definition csrLeavesCompressed : list (Tree Elem) :=
  map (fun '(name, _, _, _) =>
    Leaf name (EReg (Build_Reg (Bit Xlen) (Some (getDefault _))))
  ) CsrTable.

(* 2. Top-Level Register File Tree (Compressed) *)

Definition rfTreeCompressed : Tree Elem :=
  Node "rf" [
    Node "gprs" gprLeavesCompressed ;
    Node "scrs" scrLeavesCompressed ;
    Node "csrs" csrLeavesCompressed ;
    Leaf "waitForFenceIAck" (EReg (Build_Reg Bool (Some false)))
  ].

(* 3. Raw RegPaths into rfTreeCompressed *)

Definition gprPathsCompressed : list (RegPath rfTreeCompressed) :=
  map (embedRegPath (getNodePath rfTreeCompressed "rf.gprs"))
      (getTreeRegPaths (getNode (getNodePath rfTreeCompressed "rf.gprs"))).

Definition scrPathsCompressed : list (RegPath rfTreeCompressed) :=
  map (embedRegPath (getNodePath rfTreeCompressed "rf.scrs"))
      (getTreeRegPaths (getNode (getNodePath rfTreeCompressed "rf.scrs"))).

Definition csrPathsCompressed : list (RegPath rfTreeCompressed) :=
  map (embedRegPath (getNodePath rfTreeCompressed "rf.csrs"))
      (getTreeRegPaths (getNode (getNodePath rfTreeCompressed "rf.csrs"))).

(* 4. Typed RegOfKind Lists for readRegsList / writeRegsList (Compressed) *)

Definition gprPathsWithKindCompressed : list (RegOfKind (t:=rfTreeCompressed) FullCapWithTag) :=
  map (embedRegOfKind (getNodePath rfTreeCompressed "rf.gprs"))
      (getTreeRegsOfKind FullCapWithTag (getNode (getNodePath rfTreeCompressed "rf.gprs"))).

Definition scrPathsWithKindCompressed : list (RegOfKind (t:=rfTreeCompressed) FullCapWithTag) :=
  map (embedRegOfKind (getNodePath rfTreeCompressed "rf.scrs"))
      (getTreeRegsOfKind FullCapWithTag (getNode (getNodePath rfTreeCompressed "rf.scrs"))).

Definition csrPathsWithKindCompressed : list (RegOfKind (t:=rfTreeCompressed) (Bit Xlen)) :=
  map (embedRegOfKind (getNodePath rfTreeCompressed "rf.csrs"))
      (getTreeRegsOfKind (Bit Xlen) (getNode (getNodePath rfTreeCompressed "rf.csrs"))).

(* ===========================================================================
   COMPRESSED ALU OUTPUT TRANSFORMER AND EXECUTION ACTION
   =========================================================================== *)

Section CompressAluOut.
  Variable ty : Kind -> Type.

  Definition compressAluOut (aluOut : ty AluOutUnion) : LetExpr ty AluOutUnionCompressed :=
    LetE dstVal    : FullECapWithTag <- ##aluOut`"dstValue" ;
    LetE dstECap   : ECap            <- ##dstVal`"ecap" ;
    LETE dstCap    : Cap             <- EncodeCap dstECap ;
    LetE dstValC   : FullCapWithTag  <- STRUCT {
      "tag"  ::= ##dstVal`"tag" ;
      "cap"  ::= #dstCap ;
      "addr" ::= ##dstVal`"addr"
    } ;
    LetE aluOp        : AluOpUnion        <- ##aluOut`"Op" ;
    LetE isExc        : Bool              <- #aluOp `? "Exception" ;
    LetE excVal       : ExceptionInfo     <- #aluOp `! "Exception" ;
    LetE noExc        : NoExceptionUnion  <- #aluOp `! "NoException" ;
    LetE isDeferred   : Bool              <- #noExc `? "Deferred" ;
    LetE deferredVal  : DeferredUnion     <- #noExc `! "Deferred" ;
    LetE notDef       : NotDeferredUnion  <- #noExc `! "NotDeferred" ;
    LetE isNormFence  : Bool              <- #notDef `? "NormalFenceI" ;
    LetE normFenceVal : NormalFenceIUnion <- #notDef `! "NormalFenceI" ;
    LetE cfScrCsrVal  : CfScrCsrUnion     <- #notDef `! "CfScrCsr" ;
    LetE isCf         : Bool              <- #cfScrCsrVal `? "ControlFlow" ;
    LetE cfVal        : CfPayload         <- #cfScrCsrVal `! "ControlFlow" ;
    LetE isScrCsr     : Bool              <- #cfScrCsrVal `? "ScrCsr" ;
    LetE scrCsrVal    : ScrCsrPayload     <- #cfScrCsrVal `! "ScrCsr" ;

    LetE newPccVal    : FullECapWithTag   <- #cfVal`"NewPcc" ;
    LetE newPccECap   : ECap              <- #newPccVal`"ecap" ;
    LETE newPccCap    : Cap               <- EncodeCap newPccECap ;
    LetE newPccC      : FullCapWithTag    <- STRUCT {
      "tag"  ::= ##newPccVal`"tag" ;
      "cap"  ::= #newPccCap ;
      "addr" ::= ##newPccVal`"addr"
    } ;
    LetE cfC        : CfPayloadCompressed <- STRUCT {
      "NewPcc" ::= #newPccC ;
      "CfOp"   ::= ##cfVal`"CfOp"
    } ;

    LetE sVal       : FullECapWithTag <- #scrCsrVal`"SpecialValue" ;
    LetE sECap      : ECap            <- #sVal`"ecap" ;
    LETE sCap       : Cap             <- EncodeCap sECap ;
    LetE sValC      : FullCapWithTag  <- STRUCT {
      "tag"  ::= ##sVal`"tag" ;
      "cap"  ::= #sCap ;
      "addr" ::= ##sVal`"addr"
    } ;
    LetE scrCsrC    : ScrCsrPayloadCompressed <- STRUCT {
      "SpecialDest"  ::= ##scrCsrVal`"SpecialDest" ;
      "SpecialValue" ::= #sValC
    } ;

    LetE cfScrCsrC : CfScrCsrUnionCompressed <-
      ITE #isCf
        (UNION (CfScrCsrCompressedType, "ControlFlow" ::= #cfC))
        (UNION (CfScrCsrCompressedType, "ScrCsr" ::= #scrCsrC)) ;

    LetE notDefC : NotDeferredUnionCompressed <-
      ITE #isNormFence
        (UNION (NotDeferredUnionCompressedType, "NormalFenceI" ::= #normFenceVal))
        (UNION (NotDeferredUnionCompressedType, "CfScrCsr" ::= #cfScrCsrC)) ;

    LetE noExcC : NoExceptionUnionCompressed <-
      ITE #isDeferred
        (UNION (NoExceptionUnionCompressedType, "Deferred" ::= #deferredVal))
        (UNION (NoExceptionUnionCompressedType, "NotDeferred" ::= #notDefC)) ;

    LetE aluOpC : AluOpUnionCompressed <-
      ITE #isExc
        (UNION (AluOpUnionCompressedType, "Exception" ::= #excVal))
        (UNION (AluOpUnionCompressedType, "NoException" ::= #noExcC)) ;

    @RetE _ AluOutUnionCompressed (STRUCT {
      "isComp"      ::= ##aluOut`"isComp" ;
      "dstIdx"      ::= ##aluOut`"dstIdx" ;
      "dstValue"    ::= #dstValC ;
      "Op"          ::= #aluOpC ;
      "isFenceIAck" ::= ##aluOut`"isFenceIAck"
    }).
End CompressAluOut.

Section ExecuteNonDeferredCompressed.
  Definition executeNonDeferredCompressed ty (aluOutC : ty AluOutUnionCompressed)
    : Action ty rfTreeCompressed (Option DeferredUnion) :=
    Let  isFenceIAck    : Bool                       <- ##aluOutC`"isFenceIAck" ;

    If #isFenceIAck Then
      (
        RegWrite "rf.waitForFenceIAck" in rfTreeCompressed <- ConstBool false ;
        Retv
      ) ;

    RegRead currWait <- "rf.waitForFenceIAck" in rfTreeCompressed ;

    LetIf res : Option DeferredUnion <-
      If (Not #currWait) Then
        (
          Let  isComp         : Bool                       <- ##aluOutC`"isComp" ;
          Let  dstIdx         : Bit RegIdxSz               <- ##aluOutC`"dstIdx" ;
          Let  dstVal         : FullCapWithTag             <- ##aluOutC`"dstValue" ;
          Let  aluOp          : AluOpUnionCompressed       <- ##aluOutC`"Op" ;
          Let  pcStep         : Addr                       <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;

          LetA currPcc        : FullCapWithTag             <- readRegsList gprPathsWithKindCompressed
                                                                ($0 : Expr ty (Bit RegIdxSzReal)) ;
          Let  seqPcc         : FullCapWithTag             <- #currPcc `{ "addr" <- Add [ ##currPcc`"addr" ; #pcStep ] } ;

          Let  isExc          : Bool                       <- #aluOp `? "Exception" ;
          Let  noExc          : NoExceptionUnionCompressed <- #aluOp `! "NoException" ;
          Let  isDeferred     : Bool                       <- And [ Not #isExc ; #noExc `? "Deferred" ] ;
          Let  deferredVal    : DeferredUnion              <- #noExc `! "Deferred" ;

          If #isExc Then
            (
              Let  excVal     : ExceptionInfo  <- #aluOp `! "Exception" ;
              LetA mtcc       : FullCapWithTag <- readRegsList scrPathsWithKindCompressed
                                                    ($(getScrIdx "Mtcc") : Expr ty (Bit ScrIdxSz)) ;
              LetA mstatus    : Bit Xlen       <- readRegsList csrPathsWithKindCompressed
                                                    ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
              Let  currMIE    : Bool           <- getMstatusMIE #mstatus ;
              Let  mstatus1   : Bit Xlen       <- setMstatusMPIE #mstatus #currMIE ;
              Let  newMstatus : Bit Xlen       <- setMstatusMIE #mstatus1 (ConstBool false) ;

              Act (writeRegsList scrPathsWithKindCompressed ($(getScrIdx "MePcc") : Expr ty (Bit ScrIdxSz)) #currPcc) ;
              Act (writeRegsList csrPathsWithKindCompressed ($(getCsrIdx "mcause") : Expr ty (Bit CsrIdxSz))
                     (encodeMcause ##excVal`"mcause")) ;
              Act (writeRegsList csrPathsWithKindCompressed ($(getCsrIdx "mtval") : Expr ty (Bit CsrIdxSz))
                     (encodeCheriMtval ##excVal`"mtval")) ;
              Act (writeRegsList csrPathsWithKindCompressed ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
              writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #mtcc
            )
          Else
            (
              If (#noExc `? "Deferred") Then
                (
                  writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #seqPcc
                )
              Else
                (
                  Let notDeferredVal : NotDeferredUnionCompressed <- #noExc `! "NotDeferred" ;

                  If (isNotZero #dstIdx) Then
                    (writeRegsList gprPathsWithKindCompressed #dstIdx #dstVal) ;

                  If (##notDeferredVal `? "NormalFenceI") Then
                    (
                      Let normFence : NormalFenceIUnion <- #notDeferredVal `! "NormalFenceI" ;
                      If (##normFence `? "FenceI") Then
                        (
                          RegWrite "rf.waitForFenceIAck" in rfTreeCompressed <- ConstBool true ;
                          Retv
                        ) ;
                      writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #seqPcc
                    )
                  Else
                    (
                      Let cfScrCsr : CfScrCsrUnionCompressed <- #notDeferredVal `! "CfScrCsr" ;
                      If (##cfScrCsr `? "ScrCsr") Then
                        (
                          Let scrCsr : ScrCsrPayloadCompressed <- #cfScrCsr `! "ScrCsr" ;
                          Let sDest  : TaggedUnion ScrCsrIdx   <- ##scrCsr`"SpecialDest" ;
                          Let sVal   : FullCapWithTag          <- ##scrCsr`"SpecialValue" ;

                          If (#sDest `? "Scr") Then
                            (
                              Let scrIdx : Bit ScrIdxSz <- #sDest `! "Scr" ;
                              writeRegsList scrPathsWithKindCompressed #scrIdx #sVal
                            )
                          Else
                            (
                              Let csrIdx : Bit CsrIdxSz <- #sDest `! "Csr" ;
                              writeRegsList csrPathsWithKindCompressed #csrIdx ##sVal`"addr"
                            ) ;
                          writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #seqPcc
                        )
                      Else
                        (
                          Let cf     : CfPayloadCompressed <- #cfScrCsr `! "ControlFlow" ;
                          Let newPcc : FullCapWithTag      <- ##cf`"NewPcc" ;
                          Let cfOp   : CfOp                <- ##cf`"CfOp" ;

                          If (#cfOp `? "ControlFlowAddrOnly") Then
                            (
                              Let addrOnlyOp : ControlFlowAddrOnlyOp <- #cfOp `! "ControlFlowAddrOnly" ;
                              If (##addrOnlyOp `? "Branch") Then
                                (
                                  Let isTaken   : Bool           <- #addrOnlyOp `! "Branch" ;
                                  Let targetPcc : FullCapWithTag <- #currPcc `{ "addr" <- ##newPcc`"addr" } ;
                                  Let nextPcc   : FullCapWithTag <- ITE #isTaken #targetPcc #seqPcc ;
                                  writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc
                                )
                              Else
                                (
                                  Let targetPcc : FullCapWithTag <- #currPcc `{ "addr" <- ##newPcc`"addr" } ;
                                  writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #targetPcc
                                ) ;
                              Retv
                            )
                          Else
                            (
                              Let addrECapOp : ControlFlowAddrECapOp <- #cfOp `! "ControlFlowAddrECap" ;
                              If (##addrECapOp `? "Cjalr") Then
                                (
                                  Let  newMIE     : Bool           <- #addrECapOp `! "Cjalr" ;
                                  LetA mstatus    : Bit Xlen       <- readRegsList csrPathsWithKindCompressed
                                                                        ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
                                  Let  newMstatus : Bit Xlen       <- setMstatusMIE #mstatus #newMIE ;
                                  Act (writeRegsList csrPathsWithKindCompressed
                                         ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
                                  writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #newPcc
                                )
                              Else
                                (
                                  LetA mePcc      : FullCapWithTag <- readRegsList scrPathsWithKindCompressed
                                                                        ($(getScrIdx "MePcc") : Expr ty (Bit ScrIdxSz)) ;
                                  LetA mstatus    : Bit Xlen       <- readRegsList csrPathsWithKindCompressed
                                                                        ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
                                  Let  currMPIE   : Bool           <- getMstatusMPIE #mstatus ;
                                  Let  newMstatus : Bit Xlen       <- setMstatusMIE #mstatus #currMPIE ;
                                  Act (writeRegsList csrPathsWithKindCompressed
                                         ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
                                  writeRegsList gprPathsWithKindCompressed ($0 : Expr ty (Bit RegIdxSzReal)) #mePcc
                                ) ;
                              Retv
                            ) ;
                          Retv
                        ) ;
                      Retv
                    ) ;
                  Retv
                ) ;
              Retv
            ) ;
          Return (ITE0 #isDeferred (mkSome #deferredVal))
        ) ;
    Return #res.
End ExecuteNonDeferredCompressed.

Section LoadWritebackCompressed.
  Variable ty : Kind -> Type.

  Definition loadWritebackCompressed (loadRes : ty LoadResult) : Action ty rfTreeCompressed (Bit 0) :=
    Let  dstIdx     : Bit RegIdxSz              <- ##loadRes`"dstIdx" ;
    Let  memSize    : Bit LgLgNumBytesFullCapSz <- ##loadRes`"memSize" ;
    Let  isUnsigned : Bool                      <- ##loadRes`"isUnsigned" ;
    Let  byteOffset : Bit LgNumBytesFullCapSz   <- ##loadRes`"byteOffset" ;
    Let  rawData    : Bit FullCapSz             <- ##loadRes`"data" ;
    Let  tag        : Bool                      <- ##loadRes`"tag" ;

    Let  isCap      : Bool                                       <- isAllOnes #memSize ;
    Let  memSzBytes : Bit (LgNumBytesFullCapSz + 1)              <- Sll $1 #memSize ;
    Let  bytes      : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <- FromBit _ #rawData ;
    Let  rotBytes   : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <- ArrayRotr 8 #bytes #byteOffset ;

    Let  readBits   : Bit FullCapSz  <- ToBit (ITE #isUnsigned
                                                 (ArrayZeroExtend #memSzBytes #rotBytes)
                                                 (ArraySignExtend #memSzBytes #rotBytes)) ;
    Let  ldAddr     : Addr           <- TruncLsb Xlen Xlen #readBits ;
    Let  ldCap      : Cap            <- FromBit Cap (TruncMsb Xlen Xlen #readBits) ;

    Let  dstValC    : FullCapWithTag <- STRUCT {
                                          "tag"  ::= And [#tag; #isCap] ;
                                          "cap"  ::= ITE0 #isCap #ldCap ;
                                          "addr" ::= #ldAddr
                                        } ;

    If (isNotZero #dstIdx) Then
      (writeRegsList gprPathsWithKindCompressed #dstIdx #dstValC) ;
    Retv.
End LoadWritebackCompressed.
