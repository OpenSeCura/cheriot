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
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Definition DecodeOut := STRUCT_TYPE {
  "instGroup"    :: InstGroup ;
  "cs1Idx"       :: Bit RegIdxSzReal ;
  "cs2Idx"       :: TaggedUnion Cs2Source ;
  "instBits"     :: Inst ;
  "illegalInst"  :: Bool ;
  "asrViolation" :: Bool
}.

Section DecodeUncompressed.
  Variable ty : Kind -> Type.
  Variable inst : ty Inst.
  Variable pcc : ty FullECapWithTag.

  Definition decodeUncompressed : LetExpr ty DecodeOut :=
    LetE isComp    : Bool   <- Not (isAllOnes (#inst`[1:0])) ;
    LetE opcode    : Bit 5  <- #inst`[6:2] ;
    LetE rd        : Bit 5  <- #inst`[11:7] ;
    LetE funct3    : Bit 3  <- #inst`[14:12] ;
    LetE rs1       : Bit 5  <- #inst`[19:15] ;
    LetE rs2       : Bit 5  <- #inst`[24:20] ;
    LetE funct7    : Bit 7  <- #inst`[31:25] ;
    LetE csrAddr   : Bit 12 <- #inst`[31:20] ;
    LetE fm        : Bit 4  <- #inst`[31:28] ;

    LetE cs1Real : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal #rs1 ;
    LetE cs2Real : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal #rs2 ;

    (* CSR & SCR Decoders *)
    LetE csrOpt : Option (Bit CsrIdxSz) <- csrAddrDecoder csrAddr ;
    LetE isValidCsr : Bool <- isValid #csrOpt ;
    LetE csrMappedIdx : Bit CsrIdxSz <- getData #csrOpt ;

    LetE scrOpt : Option (Bit ScrIdxSz) <- scrAddrDecoder rs2 ;
    LetE isValidScr : Bool <- isValid #scrOpt ;
    LetE scrMappedIdx : Bit ScrIdxSz <- getData #scrOpt ;

    (* 5-Bit Major Opcode Decodes (inst[6:2]) *)
    LetE isLui    : Bool <- Eq #opcode $(Z.shiftr 0x37 2) ;
    LetE isAuiPcc : Bool <- Eq #opcode $(Z.shiftr 0x17 2) ;
    LetE isCjal   : Bool <- Eq #opcode $(Z.shiftr 0x6f 2) ;
    LetE isCjalr  : Bool <- And [Eq #opcode $(Z.shiftr 0x67 2); isZero #funct3 ] ;
    LetE isBranch : Bool <- And [ Eq #opcode $(Z.shiftr 0x63 2); Not (Eq (#funct3`[2:1]) $1) ] ;
    LetE isLoad   : Bool <- And [ Eq #opcode $(Z.shiftr 0x03 2); Not (Eq (#funct3`[2:1]) $3) ] ;
    LetE isStore  : Bool <- And [ Eq #opcode $(Z.shiftr 0x23 2); Not (FromBit Bool (#funct3`[2:2])) ] ;
    LetE isOpImm  : Bool <- Eq #opcode $(Z.shiftr 0x13 2) ;
    LetE isOp     : Bool <- Eq #opcode $(Z.shiftr 0x33 2) ;
    LetE isSystem : Bool <- Eq #opcode $(Z.shiftr 0x73 2) ;
    LetE isCheri  : Bool <- Eq #opcode $(Z.shiftr 0x5b 2) ;
    LetE isAuiCgp : Bool <- Eq #opcode $(Z.shiftr 0x7b 2) ;

    LetE isAlu : Bool <- Or [ #isOp; #isOpImm ] ;

    (* ALU Operations *)
    LetE isAdd : Bool <- And [isZero #funct3; Or [And [#isOp; isZero #funct7]; #isOpImm]];
    LetE isSub : Bool <- And [#isOp; isZero #funct3; Eq #funct7 $0x20];
    LetE isAddSub : Bool <- Or [#isAdd; #isSub] ;

    LetE isSlt   : Bool <- And [ Eq (#funct3`[2:1]) $1; Or [And [#isOp; isZero #funct7]; #isOpImm] ] ;

    LetE isShiftLeft : Bool <- And [ #isAlu; Eq #funct3 $1; isZero #funct7 ] ;
    LetE isShiftRight : Bool <- And [ #isAlu; Eq #funct3 $5; Or [ isZero #funct7; Eq #funct7 $0x20 ] ] ;
    LetE isShift : Bool <- Or [ #isShiftLeft; #isShiftRight ] ;
    LetE isShiftArith: Bool <- And [ #isShift; FromBit Bool (#funct7`[5:5]) ] ;

    LetE isLogical: Bool <- And [ Or [ Eq #funct3 $4; Eq #funct3 $6; Eq #funct3 $7 ];
                                  Or [And [#isOp; isZero #funct7]; #isOpImm] ] ;

    (* Unsignedness Bit Analysis *)
    LetE isBranchUnsigned : Bool <- And [ #isBranch; FromBit Bool (#funct3`[1:1]) ] ;
    LetE isSltUnsigned    : Bool <- And [ #isSlt; FromBit Bool (#funct3`[0:0]) ] ;
    LetE isLoadUnsigned   : Bool <- And [ #isLoad; FromBit Bool (#funct3`[2:2]) ] ;
    LetE isUnsignedOp     : Bool <- Or [ #isBranchUnsigned; #isSltUnsigned; #isLoadUnsigned ] ;

    (* PCC Permissions Extraction *)
    LetE pccEcap  : ECap     <- ##pcc`"ecap" ;
    LetE pccPerms : CapPerms  <- ##pccEcap`"perms" ;
    LetE hasAsr   : Bool      <- ##pccPerms`"SR" ;

    (* System Operations & CSR Validation *)
    LetE isCsrOp: Bool <- And [ #isSystem; isNotZero (#funct3`[1:0]) ] ;
    LetE csrAllowRead  : Bool <- Or [ csrAllowReadNoAsrDecoder csrAddr; #hasAsr ] ;
    LetE csrAllowWrite : Bool <- Or [ csrAllowWriteNoAsrDecoder csrAddr; #hasAsr ] ;

    LetE isCsrWriteAlways : Bool <- Or [ Eq #funct3 $1; Eq #funct3 $5 ] ; (* CSRRW / CSRRWI *)
    LetE isCsrBitMod      : Bool <- Or [ Eq #funct3 $2; Eq #funct3 $3; Eq #funct3 $6; Eq #funct3 $7 ] ; (* CSRRS/RC/RSI/RCI *)
    LetE isCsrWrite       : Bool <- Or [ #isCsrWriteAlways; And [ #isCsrBitMod; isNotZero #rs1 ] ] ;

    LetE csrReadPermitted  : Bool <- Or [ isZero #rd; #csrAllowRead ] ;
    LetE csrWritePermitted : Bool <- Or [ Not #isCsrWrite; #csrAllowWrite ] ;
    LetE csrPermitted      : Bool <- And [ #csrReadPermitted; #csrWritePermitted ] ;

    LetE isCsr  : Bool <- And [ #isCsrOp; #isValidCsr ] ;
    LetE isCsrImm: Bool <- And [ #isCsr; FromBit Bool (#funct3`[2:2]) ] ;

    LetE isSysZero: Bool <- And [ #isSystem; isZero #funct3 ] ;
    LetE isMret   : Bool <- And [ #isSysZero; Eq #csrAddr $0x302 ] ;
    LetE isECall  : Bool <- And [ #isSysZero; Or [ isZero #csrAddr; Eq #csrAddr $0x105 ] ] ;
    LetE isEBreak : Bool <- And [ #isSysZero; Eq #csrAddr $1 ] ;

    (* CHERIoT Operations (Opcode 0x5B) *)
    LetE isCheriFunct0      : Bool <- And [ #isCheri; Eq #funct3 $0 ] ;
    LetE isCheriFunct0TwoArg: Bool <- And [ #isCheriFunct0; Eq #funct7 $0x7f ] ;

    LetE isCIncAddrImm : Bool <- And [ #isCheri; Eq #funct3 $1 ] ;
    LetE isCSetBoundsImm: Bool <- And [ #isCheri; Eq #funct3 $2 ] ;

    (* Two-argument instructions (funct7 == 0x7F, opcode in rs2 / inst[24:20]) *)
    LetE isCGetPerm  : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x00 ] ;
    LetE isCGetType  : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x01 ] ;
    LetE isCGetBase  : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x02 ] ;
    LetE isCGetLen   : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x03 ] ;
    LetE isCGetTag   : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x04 ] ;
    LetE isCrrl      : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x08 ] ;
    LetE isCram      : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x09 ] ;
    LetE isCMove     : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x0a ] ;
    LetE isCClearTag : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x0b ] ;
    LetE isCGetAddr  : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x0f ] ;
    LetE isCGetHigh  : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x17 ] ;
    LetE isCGetTop   : Bool <- And [ #isCheriFunct0TwoArg; Eq #rs2 $0x18 ] ;

    (* Three-argument and Special instructions (opcode in funct7) *)
    LetE isScrOp              : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x01 ] ;
    LetE isScr                : Bool <- And [ #isScrOp; #isValidScr ] ;
    LetE isCSetBoundsReg      : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x08 ] ;
    LetE isCSetBoundsExact    : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x09 ] ;
    LetE isCSetBoundsRoundDown: Bool <- And [ #isCheriFunct0; Eq #funct7 $0x0a ] ;
    LetE isSeal               : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x0b ] ;
    LetE isUnseal             : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x0c ] ;
    LetE isCAndPerm           : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x0d ] ;
    LetE isCSetAddr           : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x10 ] ;
    LetE isCIncAddrReg        : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x11 ] ;
    LetE isCSub               : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x14 ] ;
    LetE isCSetHigh           : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x16 ] ;
    LetE isCTestSubset        : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x20 ] ;
    LetE isCSetEqual          : Bool <- And [ #isCheriFunct0; Eq #funct7 $0x21 ] ;

    LetE isCIncAddr  : Bool <- Or [ #isCIncAddrReg; #isCIncAddrImm ] ;
    LetE isCSetBounds: Bool <- Or [ #isCSetBoundsReg; #isCSetBoundsExact; #isCSetBoundsRoundDown; #isCSetBoundsImm ] ;

    LetE isFenceOp: Bool <- Eq #opcode $(Z.shiftr 0x0f 2) ;
    LetE isFenceI      : Bool <- And [ #isFenceOp; Eq #funct3 $1; isZero #rs1; isZero #rd; isZero #csrAddr ] ;
    LetE isFenceNormal : Bool <- And [ #isFenceOp; isZero #funct3; isZero #rs1; isZero #rd; isZero #fm ] ;
    LetE isFenceTSO    : Bool <- And [ #isFenceOp; isZero #funct3; isZero #rs1; isZero #rd; Eq #fm $8 ] ;
    LetE isFence       : Bool <- Or [ #isFenceI; #isFenceNormal; #isFenceTSO ] ;

    LetE isValidInst : Bool <- Or [
      #isBranch; #isCjal; #isAuiPcc; #isAuiCgp; #isCIncAddr; #isCSetAddr; #isCjalr; #isCTestSubset;
      #isCSetBounds; #isSeal; #isUnseal; #isLoad; #isStore; #isAddSub; #isCSub; #isCGetLen;
      #isSlt; #isCSetEqual; #isShift; #isLogical; #isCram; #isCrrl; #isCAndPerm; #isCsr; #isScr;
      #isLui; #isCGetPerm; #isCGetType; #isCGetBase; #isCGetTag; #isCGetAddr; #isCGetHigh;
      #isCGetTop; #isCSetHigh; #isCClearTag; #isCMove; #isMret; #isECall; #isEBreak; #isFence
    ] ;

    LetE isIllegalInst : Bool <- Not #isValidInst ;
    LetE asrViolation  : Bool <- Or [ And [ #isCsr; Not #csrPermitted ]; And [ #isScr; Not #hasAsr ] ] ;

    (* Direct Bit Slicing for Branch / Comparator Controls *)
    LetE isBranchLt : Bool <- And [ #isBranch; FromBit Bool (#funct3`[2:2]) ] ;
    LetE checkLt    : Bool <- Or [ #isBranchLt; #isSlt ] ;

    LetE isBranchEq : Bool <- And [ #isBranch; Not (FromBit Bool (#funct3`[2:2])) ] ;
    LetE checkEq    : Bool <- Or [ #isBranchEq; #isCSetEqual ] ;

    LetE invertRes  : Bool <- And [ #isBranch; FromBit Bool (#funct3`[0:0]) ] ;

    LetE groupVal : InstGroup <- STRUCT {
      "isCompressed"                ::= #isComp ;
      "isImm"                       ::= Or [ #isOpImm; #isLoad; #isStore; #isCIncAddrImm; #isCSetBoundsImm; #isCsrImm ] ;
      "isUnsigned"                  ::= #isUnsignedOp ;
      "Branch"                      ::= #isBranch ;
      "Cjal"                        ::= #isCjal ;
      "AuiPcc"                      ::= #isAuiPcc ;
      "AuiCgp"                      ::= #isAuiCgp ;
      "CIncAddr"                    ::= #isCIncAddr ;
      "CSetAddr"                    ::= #isCSetAddr ;
      "Cjalr"                       ::= #isCjalr ;
      "CTestSubset"                 ::= #isCTestSubset ;
      "CSetBounds"                  ::= #isCSetBounds ;
      "CSetBounds_isExact"          ::= #isCSetBoundsExact ;
      "CSetBounds_isRoundDown"      ::= #isCSetBoundsRoundDown ;
      "Seal"                        ::= #isSeal ;
      "Unseal"                      ::= #isUnseal ;
      "Load"                        ::= #isLoad ;
      "Store"                       ::= #isStore ;
      "AddSub"                      ::= #isAddSub ;
      "CSub"                        ::= #isCSub ;
      "CGetLen"                     ::= #isCGetLen ;
      "Slt"                         ::= #isSlt ;
      "CSetEqual"                   ::= #isCSetEqual ;
      "Shift"                       ::= #isShift ;
      "Shift_isArith"               ::= #isShiftArith ;
      "Shift_isRight"               ::= #isShiftRight ;
      "Logical"                     ::= #isLogical ;
      "Cram"                        ::= #isCram ;
      "Crrl"                        ::= #isCrrl ;
      "CAndPerm"                    ::= #isCAndPerm ;
      "Csr"                         ::= #isCsr ;
      "Scr"                         ::= #isScr ;
      "Lui"                         ::= #isLui ;
      "CGetPerm"                    ::= #isCGetPerm ;
      "CGetType"                    ::= #isCGetType ;
      "CGetBase"                    ::= #isCGetBase ;
      "CGetTag"                     ::= #isCGetTag ;
      "CGetAddr"                    ::= #isCGetAddr ;
      "CGetHigh"                    ::= #isCGetHigh ;
      "CGetTop"                     ::= #isCGetTop ;
      "CSetHigh"                    ::= #isCSetHigh ;
      "CClearTag"                   ::= #isCClearTag ;
      "CMove"                       ::= #isCMove ;
      "ECall"                       ::= #isECall ;
      "EBreak"                      ::= #isEBreak ;
      "Mret"                        ::= #isMret ;
      "Fence"                       ::= #isFence ;
      "ComparatorGeneral_checkLt"   ::= #checkLt ;
      "ComparatorGeneral_checkEq"   ::= #checkEq ;
      "ComparatorGeneral_invertRes" ::= #invertRes
    } ;

    LetE cs2SourceVal : TaggedUnion Cs2Source <-
      ITE #isScr (mkCs2Scr #scrMappedIdx)
          (ITE #isCsr (mkCs2Csr #csrMappedIdx)
               (mkCs2Reg #cs2Real)) ;

    @RetE _ DecodeOut (STRUCT {
      "instGroup"    ::= #groupVal ;
      "cs1Idx"       ::= #cs1Real ;
      "cs2Idx"       ::= #cs2SourceVal ;
      "instBits"     ::= #inst ;
      "illegalInst"  ::= #isIllegalInst ;
      "asrViolation" ::= #asrViolation
    }).
End DecodeUncompressed.

Section DecodeCompressed.
  Variable ty : Kind -> Type.
  Variable inst : ty Inst.
  Variable pcc : ty FullECapWithTag.

  Definition decodeQuadrant0 : LetExpr ty DecodeOut :=
    LetE f3 : Bit 3 <- #inst`[15:13] ;
    LetE cs13 : Bit 3 <- #inst`[9:7] ;
    LetE cd3  : Bit 3 <- #inst`[4:2] ;
    LetE cs15 : Bit 5 <- {< Const _ (Bit 2) (Zmod.of_Z _ 1), #cs13 >} ;
    LetE cd5  : Bit 5 <- {< Const _ (Bit 2) (Zmod.of_Z _ 1), #cd3 >} ;

    LetE addi4spnImm : Bit 12 <- {< Const _ (Bit 2) Zmod.zero, #inst`[10:7], #inst`[12:11], #inst`[5:5], #inst`[6:6], Const _ (Bit 2) Zmod.zero >} ;
    LetE pseudoADDI4SPN : Bit 30 <- {< #addi4spnImm, Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 3) (Zmod.of_Z _ 1), #cd5, Const _ (Bit 5) (Zmod.of_Z _ (Z.shiftr 0x5b 2)) >} ;

    LetE lwOff : Bit 12 <- {< Const _ (Bit 5) Zmod.zero, #inst`[5:5], #inst`[12:10], #inst`[6:6], Const _ (Bit 2) Zmod.zero >} ;
    LetE lcOff : Bit 12 <- {< Const _ (Bit 4) Zmod.zero, #inst`[6:5], #inst`[12:10], Const _ (Bit 3) Zmod.zero >} ;

    LetE pseudoLW : Bit 30 <- {< #lwOff, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 2), #cd5, Const _ (Bit 5) Zmod.zero >} ;
    LetE pseudoLC : Bit 30 <- {< #lcOff, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 3), #cd5, Const _ (Bit 5) Zmod.zero >} ;
    LetE pseudoSW : Bit 30 <- {< #lwOff`[11:5], #cd5, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 2), #lwOff`[4:0], Const _ (Bit 5) (Zmod.of_Z _ 8) >} ;
    LetE pseudoSC : Bit 30 <- {< #lcOff`[11:5], #cd5, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 3), #lcOff`[4:0], Const _ (Bit 5) (Zmod.of_Z _ 8) >} ;

    LetE rawInst : Bit 30 <- Or [ITE0 (Eq #f3 $0) #pseudoADDI4SPN;
                                 ITE0 (Eq #f3 $2) #pseudoLW;
                                 ITE0 (Eq #f3 $3) #pseudoLC;
                                 ITE0 (Eq #f3 $6) #pseudoSW;
                                 ITE0 (Eq #f3 $7) #pseudoSC] ;
    LetE pseudoInst : Bit 32 <- {< #rawInst, Const _ (Bit 2) Zmod.zero >} ;
    decodeUncompressed pseudoInst pcc.

  Definition decodeQuadrant1 : LetExpr ty DecodeOut :=
    LetE f3 : Bit 3 <- #inst`[15:13] ;
    LetE rd5 : Bit 5 <- #inst`[11:7] ;
    LetE cs13 : Bit 3 <- #inst`[9:7] ;
    LetE cs23 : Bit 3 <- #inst`[4:2] ;
    LetE cs15 : Bit 5 <- {< Const _ (Bit 2) (Zmod.of_Z _ 1), #cs13 >} ;
    LetE cs25 : Bit 5 <- {< Const _ (Bit 2) (Zmod.of_Z _ 1), #cs23 >} ;

    LetE imm12 : Bit 12 <- SignExtendTo 12 {< #inst`[12:12], #inst`[6:2] >} ;
    LetE pseudoADDI : Bit 30 <- {< #imm12, #rd5, Const _ (Bit 3) Zmod.zero, #rd5, Const _ (Bit 5) (Zmod.of_Z _ 0x04) >} ;

    LetE cjalImm : Bit 20 <- SignExtendTo 20 {< #inst`[12:12], #inst`[8:8], #inst`[10:9], #inst`[6:6], #inst`[7:7], #inst`[2:2], #inst`[11:11], #inst`[5:3] >} ;
    LetE pseudoCJAL : Bit 30 <- {< #cjalImm`[19:19], #cjalImm`[9:0], #cjalImm`[10:10], #cjalImm`[18:11], Const _ (Bit 5) (Zmod.of_Z _ 1), Const _ (Bit 5) (Zmod.of_Z _ 0x1b) >} ;

    LetE pseudoLI : Bit 30 <- {< #imm12, Const _ (Bit 5) Zmod.zero, Const _ (Bit 3) Zmod.zero, #rd5, Const _ (Bit 5) (Zmod.of_Z _ 0x04) >} ;

    LetE luiImm : Bit 20 <- SignExtendTo 20 {< #inst`[12:12], #inst`[6:2] >} ;
    LetE pseudoLUI : Bit 30 <- {< #luiImm, #rd5, Const _ (Bit 5) (Zmod.of_Z _ 0x0d) >} ;

    LetE addi16spImm : Bit 12 <- SignExtendTo 12 {< #inst`[12:12], #inst`[4:3], #inst`[5:5], #inst`[2:2], #inst`[6:6], Const _ (Bit 4) Zmod.zero >} ;
    LetE pseudoADDI16SP : Bit 30 <- {< #addi16spImm, Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 3) (Zmod.of_Z _ 1), Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 5) (Zmod.of_Z _ (Z.shiftr 0x5b 2)) >} ;

    LetE isAddi16spOp : Bool <- Eq #rd5 $2 ;
    LetE pseudoFunct3_3 : Bit 30 <- ITE #isAddi16spOp #pseudoADDI16SP #pseudoLUI ;

    LetE b12 : Bool <- FromBit Bool (#inst`[12:12]) ;
    LetE subop : Bit 2 <- #inst`[11:10] ;

    LetE rawSRLI : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #inst`[6:2], #cs15, Const _ (Bit 3) (Zmod.of_Z _ 5), #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x04) >} ;
    LetE pseudoSRLI : Bit 30 <- ITE #b12 $0 #rawSRLI ;

    LetE rawSRAI : Bit 30 <- {< Const _ (Bit 7) (Zmod.of_Z _ 0x20), #inst`[6:2], #cs15, Const _ (Bit 3) (Zmod.of_Z _ 5), #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x04) >} ;
    LetE pseudoSRAI : Bit 30 <- ITE #b12 $0 #rawSRAI ;

    LetE pseudoANDI : Bit 30 <- {< #imm12, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 7), #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x04) >} ;

    LetE func2 : Bit 2 <- #inst`[6:5] ;
    LetE pseudoSUB : Bit 30 <- {< Const _ (Bit 7) (Zmod.of_Z _ 0x20), #cs25, #cs15, Const _ (Bit 3) Zmod.zero, #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x0c) >} ;
    LetE pseudoXOR : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #cs25, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 4), #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x0c) >} ;
    LetE pseudoOR  : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #cs25, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 6), #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x0c) >} ;
    LetE pseudoAND : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #cs25, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 7), #cs15, Const _ (Bit 5) (Zmod.of_Z _ 0x0c) >} ;
    LetE rawRegOp : Bit 30 <- Or [ITE0 (Eq #func2 $0) #pseudoSUB; ITE0 (Eq #func2 $1) #pseudoXOR; ITE0 (Eq #func2 $2) #pseudoOR; ITE0 (Eq #func2 $3) #pseudoAND] ;
    LetE pseudoRegOp : Bit 30 <- ITE #b12 $0 #rawRegOp ;

    LetE pseudoFunct3_4 : Bit 30 <- Or [ITE0 (Eq #subop $0) #pseudoSRLI; ITE0 (Eq #subop $1) #pseudoSRAI; ITE0 (Eq #subop $2) #pseudoANDI; ITE0 (Eq #subop $3) #pseudoRegOp] ;

    LetE pseudoCJ : Bit 30 <- {< #cjalImm`[19:19], #cjalImm`[9:0], #cjalImm`[10:10], #cjalImm`[18:11], Const _ (Bit 5) Zmod.zero, Const _ (Bit 5) (Zmod.of_Z _ 0x1b) >} ;

    LetE beqImm : Bit 13 <- SignExtendTo 13 {< #inst`[12:12], #inst`[6:5], #inst`[2:2], #inst`[11:10], #inst`[4:3], Const _ (Bit 1) Zmod.zero >} ;
    LetE beqHi : Bit 7 <- {< #beqImm`[12:12], #beqImm`[10:5] >} ;
    LetE beqLo : Bit 5 <- {< #beqImm`[4:1], #beqImm`[11:11] >} ;
    LetE pseudoBEQZ : Bit 30 <- {< #beqHi, Const _ (Bit 5) Zmod.zero, #cs15, Const _ (Bit 3) Zmod.zero, #beqLo, Const _ (Bit 5) (Zmod.of_Z _ 0x18) >} ;
    LetE pseudoBNEZ : Bit 30 <- {< #beqHi, Const _ (Bit 5) Zmod.zero, #cs15, Const _ (Bit 3) (Zmod.of_Z _ 1), #beqLo, Const _ (Bit 5) (Zmod.of_Z _ 0x18) >} ;

    LetE rawInst : Bit 30 <- Or [ITE0 (Eq #f3 $0) #pseudoADDI;
                                 ITE0 (Eq #f3 $1) #pseudoCJAL;
                                 ITE0 (Eq #f3 $2) #pseudoLI;
                                 ITE0 (Eq #f3 $3) #pseudoFunct3_3;
                                 ITE0 (Eq #f3 $4) #pseudoFunct3_4;
                                 ITE0 (Eq #f3 $5) #pseudoCJ;
                                 ITE0 (Eq #f3 $6) #pseudoBEQZ;
                                 ITE0 (Eq #f3 $7) #pseudoBNEZ] ;
    LetE pseudoInst : Bit 32 <- {< #rawInst, Const _ (Bit 2) (Zmod.of_Z _ 1) >} ;
    decodeUncompressed pseudoInst pcc.

  Definition decodeQuadrant2 : LetExpr ty DecodeOut :=
    LetE f3 : Bit 3 <- #inst`[15:13] ;
    LetE rd5 : Bit 5 <- #inst`[11:7] ;
    LetE rs25 : Bit 5 <- #inst`[6:2] ;
    LetE b12 : Bool <- FromBit Bool (#inst`[12:12]) ;

    LetE rawSLLI : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #rs25, #rd5, Const _ (Bit 3) (Zmod.of_Z _ 1), #rd5, Const _ (Bit 5) (Zmod.of_Z _ 4) >} ;
    LetE pseudoSLLI : Bit 30 <- ITE #b12 $0 #rawSLLI ;

    LetE lwspOff : Bit 12 <- {< Const _ (Bit 4) Zmod.zero, #inst`[3:2], #inst`[12:12], #inst`[6:4], Const _ (Bit 2) Zmod.zero >} ;
    LetE pseudoLWSP : Bit 30 <- {< #lwspOff, Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 3) (Zmod.of_Z _ 2), #rd5, Const _ (Bit 5) Zmod.zero >} ;

    LetE clcspOff : Bit 12 <- {< Const _ (Bit 3) Zmod.zero, #inst`[4:2], #inst`[12:12], #inst`[6:5], Const _ (Bit 3) Zmod.zero >} ;
    LetE pseudoCLCSP : Bit 30 <- {< #clcspOff, Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 3) (Zmod.of_Z _ 3), #rd5, Const _ (Bit 5) Zmod.zero >} ;

    LetE pseudoJR : Bit 30 <- {< Const _ (Bit 12) Zmod.zero, #rd5, Const _ (Bit 3) Zmod.zero, Const _ (Bit 5) Zmod.zero, Const _ (Bit 5) (Zmod.of_Z _ 0x19) >} ;
    LetE pseudoMV : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #rs25, Const _ (Bit 5) Zmod.zero, Const _ (Bit 3) Zmod.zero, #rd5, Const _ (Bit 5) (Zmod.of_Z _ 0x0c) >} ;
    LetE pseudoJALR : Bit 30 <- {< Const _ (Bit 12) Zmod.zero, #rd5, Const _ (Bit 3) Zmod.zero, Const _ (Bit 5) (Zmod.of_Z _ 1), Const _ (Bit 5) (Zmod.of_Z _ 0x19) >} ;
    LetE pseudoEBREAK : Bit 30 <- {< Const _ (Bit 12) (Zmod.of_Z _ 1), Const _ (Bit 5) Zmod.zero, Const _ (Bit 3) Zmod.zero, Const _ (Bit 5) Zmod.zero, Const _ (Bit 5) (Zmod.of_Z _ 0x1c) >} ;
    LetE pseudoADD : Bit 30 <- {< Const _ (Bit 7) Zmod.zero, #rs25, #rd5, Const _ (Bit 3) Zmod.zero, #rd5, Const _ (Bit 5) (Zmod.of_Z _ 0x0c) >} ;
    LetE pseudoB12Zero : Bit 30 <- ITE (isZero #rs25) #pseudoJR #pseudoMV ;
    LetE pseudoB12One  : Bit 30 <- ITE (isNotZero #rd5) (ITE (isZero #rs25) #pseudoJALR #pseudoADD) #pseudoEBREAK ;
    LetE pseudoFunct4Q2 : Bit 30 <- ITE #b12 #pseudoB12One #pseudoB12Zero ;

    LetE swspOff : Bit 12 <- {< Const _ (Bit 4) Zmod.zero, #inst`[8:7], #inst`[12:9], Const _ (Bit 2) Zmod.zero >} ;
    LetE pseudoSWSP : Bit 30 <- {< #swspOff`[11:5], #rs25, Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 3) (Zmod.of_Z _ 2), #swspOff`[4:0], Const _ (Bit 5) (Zmod.of_Z _ 8) >} ;

    LetE cscspOff : Bit 12 <- {< Const _ (Bit 3) Zmod.zero, #inst`[9:7], #inst`[12:10], Const _ (Bit 3) Zmod.zero >} ;
    LetE pseudoCSCSP : Bit 30 <- {< #cscspOff`[11:5], #rs25, Const _ (Bit 5) (Zmod.of_Z _ 2), Const _ (Bit 3) (Zmod.of_Z _ 3), #cscspOff`[4:0], Const _ (Bit 5) (Zmod.of_Z _ 8) >} ;

    LetE rawInst : Bit 30 <- Or [ITE0 (Eq #f3 $0) #pseudoSLLI;
                                 ITE0 (Eq #f3 $2) #pseudoLWSP;
                                 ITE0 (Eq #f3 $3) #pseudoCLCSP;
                                 ITE0 (Eq #f3 $4) #pseudoFunct4Q2;
                                 ITE0 (Eq #f3 $6) #pseudoSWSP;
                                 ITE0 (Eq #f3 $7) #pseudoCSCSP] ;
    LetE pseudoInst : Bit 32 <- {< #rawInst, Const _ (Bit 2) (Zmod.of_Z _ 2) >} ;
    decodeUncompressed pseudoInst pcc.

  Definition decode : LetExpr ty DecodeOut :=
    LetE quad : Bit 2 <- #inst`[1:0] ;
    LETE q0 : DecodeOut <- decodeQuadrant0 ;
    LETE q1 : DecodeOut <- decodeQuadrant1 ;
    LETE q2 : DecodeOut <- decodeQuadrant2 ;
    LETE unc : DecodeOut <- decodeUncompressed inst pcc ;
    LetE res : DecodeOut <- caseDefault [(Eq #quad $0, #q0);
                                         (Eq #quad $1, #q1);
                                         (Eq #quad $2, #q2)] #unc ;
    RetE #res.
End DecodeCompressed.
