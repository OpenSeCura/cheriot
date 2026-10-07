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
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Cheriot Require Import SpecDefines FunctionalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Section Alu.
  Variable ty : Kind -> Type.

(* ===========================================================================
 * ALU Input Routing (AluRouting)
 * =========================================================================== *)

  Definition AluRouting (pcc : ty FullECapWithTag) (aluIn : ty AluIn) : LetExpr ty AluOut :=
    LetE cs2Idx : TaggedUnion Cs2Source <- ##aluIn`"cs2Idx" ;
    LetE inst : Inst <- ##aluIn`"inst" ;
    LetE decodeExc : DecodeException <- ##aluIn`"decodeExc" ;
    LetE fetchExc : FetchException <- ##aluIn`"fetchExc" ;
    LetE cs1 : FullECapWithTag <- ##aluIn`"cs1" ;
    LetE cs2 : FullECapWithTag <- ##aluIn`"cs2" ;
    LetE currInterruptStatus : Bool <- ##aluIn`"currInterruptStatus" ;
    LetE aluControl : AluControl <- ##aluIn`"aluControl" ;

    LetE isComp  : Bool     <- isCompressed inst ;
    LetE pccAddr : Addr <- ##pcc`"addr" ;
    LetE pccTag : Bool <- ##pcc`"tag" ;
    LetE pccECap : ECap <- ##pcc`"ecap" ;
    LetE pccBase : Bit (AddrSz + 1) <- ##pccECap`"base" ;
    LetE pcc_cE : Bit ExpSz <- ##pccECap`"cE" ;
    LetE pccExp : Bit ExpSz <- get_E_from_cE pcc_cE ;

    LetE cs1Addr : Addr <- ##cs1`"addr" ;
    LetE cs1Tag : Bool <- ##cs1`"tag" ;
    LetE cs1ECap : ECap <- ##cs1`"ecap" ;
    LetE cs1Base : Bit (AddrSz + 1) <- ##cs1ECap`"base" ;
    LetE cs1Top : Bit (AddrSz + 2) <- ##cs1ECap`"top" ;
    LetE cs1_cE : Bit ExpSz <- ##cs1ECap`"cE" ;
    LetE cs1Exp : Bit ExpSz <- get_E_from_cE cs1_cE ;
    LetE cs1Perms : CapPerms <- ##cs1ECap`"perms" ;
    LetE cs1OType : Bit CapOTypeSz <- getFullOType cs1ECap ;

    LetE cs2Addr : Addr <- ##cs2`"addr" ;
    LetE cs2Tag : Bool <- ##cs2`"tag" ;
    LetE cs2ECap : ECap <- ##cs2`"ecap" ;
    LetE cs2Base : Bit (AddrSz + 1) <- ##cs2ECap`"base" ;
    LetE cs2Top : Bit (AddrSz + 2) <- ##cs2ECap`"top" ;
    LetE cs2Perms : CapPerms <- ##cs2ECap`"perms" ;

    LetE simm12 : Bit Xlen <- SignExtendTo Xlen (##inst`[31:20]) ;
    LetE store_imm : Bit Xlen <- SignExtendTo Xlen ({< ##inst`[31:25], ##inst`[11:7] >}) ;
    LetE zimm12 : Bit Xlen <- ZeroExtendTo Xlen (##inst`[31:20]) ;
    LetE uimm20 : Bit Xlen <- ({< ##inst`[31:12], Const ty (Bit 12) Zmod.zero >}) ;
    LetE uimm20_11 : Bit Xlen <-
      ({< ##inst`[31:31], ##inst`[31:12], Const ty (Bit 11) Zmod.zero >}) ;
    LetE shamt <- ##inst`[24:20] ;
    LetE zimm5 : Bit 5 <- ##inst`[19:15] ;
    LetE bimm12 : Bit Xlen <- getBImm inst ;
    LetE jimm20 : Bit Xlen <- getJImm inst ;
    LetE scrIdx : Bit ScrAddrSz <- getScr inst ;
    LetE cs1Idx : Bit RegIdxSz <- getCs1 inst ;
    LetE dstIdx : Bit RegIdxSzReal <- TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd inst) ;
    LetE memSize : Bit LgLgNumBytesFullCapSz <- getMemSize inst ;

    LetE BranchOrCjalOrAuiPcc : Bool <- ##aluControl`"BranchOrCjalOrAuiPcc" ;

    LetE AdderBeforeBoundsCheck_base : Addr <-
      ITE (#BranchOrCjalOrAuiPcc) #pccAddr #cs1Addr ;
    LetE AdderBeforeBoundsCheck_offset : Addr <-
      caseDefault (k := Addr) [
          (##aluControl`"Branch", #bimm12) ;
          (##aluControl`"Cjal", #jimm20) ;
          (##aluControl`"AdderBeforeBoundsCheck_offset_uimm20_11", #uimm20_11) ;
          (##aluControl`"AdderBeforeBoundsCheck_offset_cs2Addr", #cs2Addr) ;
          (##aluControl`"Bounds_isImm", #zimm12) ;
          (##aluControl`"Store", #store_imm) ]
        #simm12 ;
    LETE AdderBeforeBoundsCheckOut : Addr <-
      AdderBeforeBoundsCheck AdderBeforeBoundsCheck_base AdderBeforeBoundsCheck_offset ;

    LetE AdderToOutput_base : Bit Xlen <-
      caseDefault (k := Bit Xlen) [
          (##aluControl`"CjalOrCjalr", #pccAddr) ;
          (##aluControl`"CGetLen", TruncLsb 2 AddrSz #cs1Top) ]
        #cs1Addr ;
    LetE AdderToOutput_offset : Bit Xlen <-
      caseDefault (k := Bit Xlen) [
          (##aluControl`"AdderToOutput_offset_const2", $(CompInstSz/8)) ;
          (##aluControl`"AdderToOutput_offset_cs2Addr", #cs2Addr) ;
          (##aluControl`"AdderToOutput_offset_simm12", #simm12) ;
          (##aluControl`"CGetLen", TruncLsb 1 AddrSz #cs1Base) ]
        $(InstSz/8) ;
    LetE AdderToOutput_isSub : Bool <- ##aluControl`"AdderToOutput_isSub" ;
    LETE AdderToOutputOut : Bit Xlen <-
      AdderToOutput AdderToOutput_isSub AdderToOutput_base AdderToOutput_offset ;

    LetE Shifter_data : Bit Xlen <- #cs1Addr ;
    LetE Shifter_shamt : Bit RegIdxSz <-
      ITE (##aluControl`"Shifter_shamt_isCs2AddrNotShamt")
          (TruncLsb (AddrSz - RegIdxSz) RegIdxSz #cs2Addr)
          #shamt ;
    LetE Shifter_isRight : Bool <- ##aluControl`"Shifter_isRight" ;
    LetE Shifter_isArith : Bool <- ##aluControl`"Shifter_isArith" ;
    LETE ShifterOut : Bit Xlen <-
      Shifter Shifter_isRight Shifter_isArith Shifter_data Shifter_shamt ;

    LetE AdderBeforeRepCheck_base : Bit (AddrSz + 1) <-
      ITE (#BranchOrCjalOrAuiPcc) #pccBase #cs1Base ;
    LetE AdderBeforeRepCheck_exp : Bit ExpSz <-
      ITE (#BranchOrCjalOrAuiPcc) #pccExp #cs1Exp ;
    LETE AdderBeforeRepCheckOut : Bit (AddrSz + 2) <-
      AdderBeforeRepCheck AdderBeforeRepCheck_base AdderBeforeRepCheck_exp ;

    LetE ComparatorTopOrRep_addr : Bit (AddrSz + 2) <-
      caseDefault (k := Bit (AddrSz + 2)) [
          (##aluControl`"ComparatorTopOrRep_addr_AdderBeforeBoundsCheck",
           ZeroExtendTo (AddrSz + 2) #AdderBeforeBoundsCheckOut) ;
          (##aluControl`"SealOrSetAddr", ZeroExtendTo (AddrSz + 2) #cs2Addr) ;
          (##aluControl`"Unseal", ZeroExtendTo (AddrSz + 2) #cs1OType) ;
          (##aluControl`"CTestSubset", #cs1Top) ]
        (ZeroExtendTo (AddrSz + 2) #cs1Addr) ;
    LetE ComparatorTopOrRep_topRep : Bit (AddrSz + 2) <-
      caseDefault (k := Bit (AddrSz + 2)) [
          (##aluControl`"ComparatorTopOrRep_topRep_AdderBeforeRepCheck", #AdderBeforeRepCheckOut) ;
          (##aluControl`"SealOrUnsealOrSubset", #cs2Top) ]
        #cs1Top ;
    LetE ComparatorTopOrRep_checkLte : Bool <- ##aluControl`"ComparatorTopOrRep_checkLte" ;
    LETE ComparatorTopOrRepOut : ComparatorOut <-
      ComparatorTopOrRep ComparatorTopOrRep_checkLte ComparatorTopOrRep_addr ComparatorTopOrRep_topRep ;

    LetE ComparatorBase_addr : Bit (AddrSz + 1) <-
      caseDefault (k := Bit (AddrSz + 1)) [
          (##aluControl`"ComparatorBase_addr_AdderBeforeBoundsCheck",
           ZeroExtendTo (AddrSz + 1) #AdderBeforeBoundsCheckOut) ;
          (##aluControl`"SealOrSetAddr", ZeroExtendTo (AddrSz + 1) #cs2Addr) ;
          (##aluControl`"Unseal", ZeroExtendTo (AddrSz + 1) #cs1OType) ;
          (##aluControl`"CTestSubset", #cs1Base) ]
        (ZeroExtendTo (AddrSz + 1) #cs1Addr) ;
    LetE ComparatorBase_base : Bit (AddrSz + 1) <-
      caseDefault (k := Bit (AddrSz + 1)) [
          (#BranchOrCjalOrAuiPcc, #pccBase) ;
          (##aluControl`"SealOrUnsealOrSubset", #cs2Base) ]
        #cs1Base ;
    LETE ComparatorBaseOut : Bool <- ComparatorBase ComparatorBase_addr ComparatorBase_base ;

    LetE AddrBoundsCheck_tag : Bool <-
      ITE (#BranchOrCjalOrAuiPcc) #pccTag #cs1Tag ;
    LetE AddrBoundsCheck_topLt : Bool <- ##ComparatorTopOrRepOut`"lt" ;
    LetE AddrBoundsCheck_baseGe : Bool <- ##ComparatorBaseOut ;
    LETE AddrBoundsCheckOut : Bool <-
      AddrBoundsCheck AddrBoundsCheck_tag AddrBoundsCheck_topLt
                      AddrBoundsCheck_baseGe ;

    LetE SealerUnsealer_isUnseal : Bool <- ##aluControl`"Unseal" ;
    LETE SealerUnsealerOut : TagECap <-
      SealerUnsealer SealerUnsealer_isUnseal AddrBoundsCheckOut cs1Tag cs1ECap cs2 ;

    LetE ComparatorGeneral_op1 : Bit Xlen <- #cs1Addr ;
    LetE ComparatorGeneral_op2 : Bit Xlen <-
      ITE (##aluControl`"ComparatorGeneral_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
    LetE ComparatorGeneral_isUnsigned : Bool <- ##aluControl`"ComparatorGeneral_isUnsigned" ;
    LetE ComparatorGeneral_checkLt    : Bool <- ##aluControl`"ComparatorGeneral_checkLt" ;
    LetE ComparatorGeneral_checkEq    : Bool <- ##aluControl`"ComparatorGeneral_checkEq" ;
    LetE ComparatorGeneral_invertRes  : Bool <- ##aluControl`"ComparatorGeneral_invertRes" ;
    LETE ComparatorGeneralOut : ComparatorGeneralRes <-
      ComparatorGeneral ComparatorGeneral_isUnsigned ComparatorGeneral_checkLt
                        ComparatorGeneral_checkEq ComparatorGeneral_invertRes
                        ComparatorGeneral_op1 ComparatorGeneral_op2 ;

    LETE CjalrUnitOut : CjalrUnitRes <- CjalrUnit cs1 inst currInterruptStatus ;

    LetE Logical_op1 : Bit Xlen <- #cs1Addr ;
    LetE Logical_op2 : Bit Xlen <-
      ITE (##aluControl`"Logical_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
    LetE Logical_opSel : Bit 2 <- ##inst`[13:12] ;
    LETE LogicalOut : Bit Xlen <- Logical Logical_opSel Logical_op1 Logical_op2 ;

    LETE CAndPermOut : TagECap <- CAndPerm cs1Tag cs1ECap cs2Addr ;

    LetE Bounds_reqLimit : Addr <-
      caseDefault (k := Addr) [ (##aluControl`"Bounds_reqLimit_cs2Addr", #cs2Addr) ;
                                     (##aluControl`"Bounds_reqLimit_cs1Addr", #cs1Addr) ]
        #zimm12 ;
    LetE Bounds_isRoundDown : Bool <- ##aluControl`"Bounds_isRoundDown" ;
    LETE BoundsOut : BoundsRes <- Bounds Bounds_isRoundDown cs1Addr Bounds_reqLimit ;

    LetE Bounds_boundsExact : Bool <- ##BoundsOut`"exact" ;
    LetE Bounds_instIsExact : Bool <- ##aluControl`"Bounds_isExact" ;
    LETE BoundsExactOut : Bool <- BoundsExact Bounds_instIsExact AddrBoundsCheckOut Bounds_boundsExact ;

    LetE Saturater_isBase : Bool <- ##aluControl`"Saturater_isBase" ;
    LetE Saturater_isTop : Bool <- ##aluControl`"Saturater_isTop" ;
    LetE Saturater_isLen : Bool <- ##aluControl`"CGetLen" ;
    LETE SaturaterOut : Bit Xlen <-
      Saturater Saturater_isBase Saturater_isTop Saturater_isLen cs1Base cs1Top AdderToOutputOut ;

    LETE CapSubsetOut : Bool <-
      CapSubset AddrBoundsCheck_topLt AddrBoundsCheck_baseGe cs1Tag cs2Tag cs1Perms cs2Perms ;

    LetE CapEq_addrEq : Bool <- ##ComparatorGeneralOut`"eq" ;
    LETE CapEqOut : Bool <- CapEq CapEq_addrEq cs1Tag cs2Tag cs1ECap cs2ECap ;

    LETE ScrSanitizerOut : Bool <- ScrSanitizer cs1Tag cs1Addr inst ;

    LetE isMret : Bool <- ##aluControl`"ControlFlow_isMret" ;
    LetE isCjal : Bool <- ##aluControl`"Cjal" ;
    LetE isCjalr : Bool <- ##aluControl`"ControlFlow_isCjalr" ;
    LetE isBranch : Bool <- ##aluControl`"Branch" ;
    LetE isCond : Bool <- ##ComparatorGeneralOut`"cond" ;

    LetE cjalrTag : Bool <- ##CjalrUnitOut`"tag" ;
    LetE cjalrEcap : ECap <- ##CjalrUnitOut`"ecap" ;
    LetE cjalrIntStatus : Bool <- ##CjalrUnitOut`"interruptStatus" ;
    LETE ControlFlowResOut : ControlFlowRes <-
      ControlFlow isMret isCjal isCjalr isBranch isCond cs2 AdderBeforeBoundsCheckOut
             AddrBoundsCheckOut cjalrTag cjalrEcap cjalrIntStatus pccTag inst currInterruptStatus ;
    LetE ControlFlowOut : Option CfPayload <- ##ControlFlowResOut`"cfOut" ;

    LetE PccEcap_cOType : Bit CapcOTypeSz <- ITE0 (##aluControl`"CjalOrCjalr") (##ControlFlowResOut`"linkCOType") ;
    LETE PccEcapOut : ECap <- PccEcap pccECap PccEcap_cOType ;

    LetE Reg_tag : Bool <-
      Or [ And [ ##aluControl`"Cjal"                  ; #pccTag ] ;
           And [ ##aluControl`"Reg_tag_cs1Tag"         ; #cs1Tag ] ;
           And [ ##aluControl`"Scr"                    ; #cs2Tag ] ;
           And [ ##aluControl`"Reg_tag_AddrBoundsCheck"; #AddrBoundsCheckOut ] ;
           And [ ##aluControl`"CSetBounds"             ; #BoundsExactOut ] ;
           And [ ##aluControl`"CAndPerm"               ; ##CAndPermOut`"tag" ] ;
           And [ ##aluControl`"SealOrUnseal"           ; ##SealerUnsealerOut`"tag" ] ] ;

    LetE capToEncode : ECap <- ITE (##aluControl`"Store") (#cs2ECap) (#cs1ECap) ;
    LETE encodedCap : Cap <- EncodeCap capToEncode ;
    LetE cs2AddrAsCap : Cap <- FromBit Cap #cs2Addr ;
    LETE decodedECap : ECap <- DecodeCap cs2AddrAsCap cs1Addr ;
    LetE Bounds_outECap : ECap <- STRUCT { "R"      ::= ##cs1ECap`"R" ;
                                           "perms"  ::= ##cs1ECap`"perms" ;
                                           "cOType" ::= ##cs1ECap`"cOType" ;
                                           "cE"     ::= ##BoundsOut`"cE" ;
                                           "top"    ::= ##BoundsOut`"top" ;
                                           "base"   ::= ##BoundsOut`"base" };

    LetE Reg_ecap : ECap <-
      caseDefault (k := ECap) [ (##aluControl`"Reg_ecap_PccEcap", #PccEcapOut) ;
                                 (##aluControl`"Reg_ecap_cs1Ecap", ##cs1`"ecap") ;
                                 (##aluControl`"Scr", #cs2ECap) ;
                                 (##aluControl`"Reg_ecap_decodedECap", #decodedECap) ;
                                 (##aluControl`"CAndPerm", ##CAndPermOut`"ecap") ;
                                 (##aluControl`"SealOrUnseal", ##SealerUnsealerOut`"ecap") ;
                                 (##aluControl`"CSetBounds", #Bounds_outECap) ]
        (Const ty ECap (getDefault _)) ;

    LetE Reg_addr : Addr <-
      caseDefault (k := Addr) [
          (##aluControl`"Reg_addr_AdderBeforeBoundsCheck", #AdderBeforeBoundsCheckOut) ;
          (##aluControl`"Reg_addr_ComparatorGeneralLt",
           ZeroExtendTo Xlen (ToBit (##ComparatorGeneralOut`"cond"))) ;
          (##aluControl`"Reg_addr_Shifter", #ShifterOut) ;
          (##aluControl`"Reg_addr_Logical", #LogicalOut) ;
          (##aluControl`"Reg_addr_AdderToOutput", #AdderToOutputOut) ;
          (##aluControl`"Reg_addr_CGetPerm", ZeroExtendTo Xlen (ToBit (##cs1ECap`"perms"))) ;
          (##aluControl`"Reg_addr_CGetType", ZeroExtendTo Xlen #cs1OType) ;
          (##aluControl`"Reg_addr_CGetTag",  ZeroExtendTo Xlen (ToBit #cs1Tag)) ;
          (##aluControl`"Reg_addr_CGetHigh", ZeroExtendTo Xlen (ToBit #encodedCap)) ;
          (##aluControl`"Reg_addr_Saturater", #SaturaterOut) ;
          (##aluControl`"Reg_addr_cs2Addr", #cs2Addr) ;
          (##aluControl`"Reg_addr_cs1Addr", #cs1Addr) ;
          (##aluControl`"Reg_addr_BoundsCram", TruncLsb 1 AddrSz (##BoundsOut`"cram")) ;
          (##aluControl`"Reg_addr_BoundsCrrl", TruncLsb 1 AddrSz (##BoundsOut`"length")) ;
          (##aluControl`"CTestSubset", ZeroExtendTo Xlen (ToBit #CapSubsetOut)) ;
          (##aluControl`"Reg_addr_CapEq", ZeroExtendTo Xlen (ToBit #CapEqOut)) ]
        #uimm20 ;

    LetE ecall : Bool <- ##aluControl`"Exception_isECall" ;
    LetE ebreak : Bool <- ##aluControl`"Exception_isEBreak" ;
    LetE isLoad : Bool <- ##aluControl`"Load" ;
    LetE isStore : Bool <- ##aluControl`"Store" ;

    LETE ExceptionRes : Option ExceptionInfo <-
      ExceptionUnit ecall ebreak isLoad isStore
                    fetchExc decodeExc inst
                    cs1Tag cs1ECap AddrBoundsCheckOut AdderBeforeBoundsCheckOut ;

    LetE isFence : Bool <- ##aluControl`"Fence" ;
    LetE isMulDiv : Bool <- ##aluControl`"Deferred_isMulDiv" ;
    LetE storeTag : Bool <- #cs2Tag ;
    LetE storeData : Addr <- #cs2Addr ;
    LETE DeferredOpRes : Option DeferredUnion <-
      Deferred isLoad isStore isFence isMulDiv cs1Perms cs2Perms inst storeTag encodedCap storeData ;

    LETE isFenceIOut : Bool <- FenceI isFence inst ;

    LetE RegVal : FullECapWithTag <-
      STRUCT { "tag" ::= #Reg_tag; "ecap" ::= #Reg_ecap; "addr" ::= #Reg_addr } ;

    LetE cfPayload : Option CfPayload <- #ControlFlowOut ;
  
    LetE ScrCsr_operand : Addr <-
      ITE (##aluControl`"ScrCsr_operand_isImm") (ZeroExtendTo Xlen #zimm5) #cs1Addr ;
    LetE ScrCsr_isSet : Bool <- ##aluControl`"ScrCsr_isSet" ;
    LetE ScrCsr_isClear : Bool <- ##aluControl`"ScrCsr_isClear" ;
    LetE ScrCsr_isWrite : Bool <- ##aluControl`"ScrCsr_isWrite" ;
    LETE ScrCsrOut : Option ScrCsrPayload <-
      ScrCsr ScrCsr_isSet ScrCsr_isClear ScrCsr_isWrite
             cs2Idx ScrSanitizerOut cs1ECap ScrCsr_operand cs2Addr ;

    @RetE _ AluOut (STRUCT {
      "isComp"      ::= #isComp ;
      "dstIdx"      ::= ITE0 (And [##aluIn`"writesCd"; Not (#ExceptionRes`"valid")]) #dstIdx ;
      "dstValue"    ::= #RegVal ;
      "Exception"   ::= #ExceptionRes ;
      "Deferred"    ::= #DeferredOpRes ;
      "ControlFlow" ::= #cfPayload ;
      "ScrCsr"      ::= #ScrCsrOut ;
      "isFenceI"    ::= #isFenceIOut
    }).

(* ===========================================================================
 * ALU Functional Unit Execution (Alu)
 * =========================================================================== *)

  Definition Alu (routingOut : ty AluOut) : LetExpr ty AluOutUnion :=
    LetE excOpt      : Option ExceptionInfo <- ##routingOut`"Exception" ;
    LetE deferredOpt : Option DeferredUnion <- ##routingOut`"Deferred" ;
    LetE cfOpt       : Option CfPayload <- ##routingOut`"ControlFlow" ;
    LetE scrCsrOpt   : Option ScrCsrPayload <- ##routingOut`"ScrCsr" ;
    LetE isFenceI    : Bool <- ##routingOut`"isFenceI" ;

    LetE isExc : Bool <- #excOpt`"valid" ;
    LetE excVal : ExceptionInfo <- #excOpt`"data" ;

    LetE isDeferred : Bool <- #deferredOpt`"valid" ;
    LetE deferredVal : DeferredUnion <- #deferredOpt`"data" ;

    LetE isCf : Bool <- #cfOpt`"valid" ;
    LetE cfVal : CfPayload <- #cfOpt`"data" ;

    LetE isScrCsr : Bool <- #scrCsrOpt`"valid" ;
    LetE scrCsrVal : ScrCsrPayload <- #scrCsrOpt`"data" ;

    LetE cfScrCsrUnion : CfScrCsrUnion <-
      ITE #isCf
          (UNION (CfScrCsrType, "ControlFlow" ::= #cfVal))
          (UNION (CfScrCsrType, "ScrCsr" ::= #scrCsrVal)) ;

    LetE normalFenceIUnion : NormalFenceIUnion <-
      ITE #isFenceI
          (UNION (NormalFenceIType, "FenceI" ::= Const ty (Bit 0) Zmod.zero))
          (UNION (NormalFenceIType, "Normal" ::= Const ty (Bit 0) Zmod.zero)) ;

    LetE notDeferredUnion : NotDeferredUnion <-
      ITE (Or [ #isCf ; #isScrCsr ])
          (UNION (NotDeferredUnionType, "CfScrCsr" ::= #cfScrCsrUnion))
          (UNION (NotDeferredUnionType, "NormalFenceI" ::= #normalFenceIUnion)) ;

    LetE noExcUnion : NoExceptionUnion <-
      ITE #isDeferred
          (UNION (NoExceptionUnionType, "Deferred" ::= #deferredVal))
          (UNION (NoExceptionUnionType, "NotDeferred" ::= #notDeferredUnion)) ;

    LetE opUnion : AluOpUnion <-
      ITE #isExc
          (UNION (AluOpUnionType, "Exception" ::= #excVal))
          (UNION (AluOpUnionType, "NoException" ::= #noExcUnion)) ;

    @RetE _ AluOutUnion (STRUCT {
      "isComp"      ::= ##routingOut`"isComp" ;
      "dstIdx"      ::= ##routingOut`"dstIdx" ;
      "dstValue"    ::= ##routingOut`"dstValue" ;
      "Op"          ::= #opUnion
    }).

  Definition wrappedAlu (pcc : ty FullECapWithTag) (pkg : ty AluInInstGroup) : LetExpr ty AluOutUnion :=
    LETE aluIn      : AluIn       <- constructAluIn pkg ;
    LETE routingOut : AluOut      <- AluRouting pcc aluIn ;
    LETE aluOut     : AluOutUnion <- Alu routingOut ;
    RetE #aluOut.
End Alu.

Section AluRF.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable ty : Kind -> Type.
  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).
  Local Abbreviation scrPathsWithKind := (scrPathsWithKind dom pcAddrInit).
  Local Abbreviation csrPathsWithKind := (csrPathsWithKind dom pcAddrInit).
  Local Abbreviation incrementMinstret := (incrementMinstret dom pcAddrInit).
  Local Abbreviation incrementMcycle := (incrementMcycle dom pcAddrInit).
  Local Abbreviation updateMshwmOnStore := (updateMshwmOnStore dom pcAddrInit).

  Definition isInterruptPending (meip mtip : ty Bool) : Action ty rfTree InterruptPendingInfo :=
    LetA mstatus     : Bit Xlen <- readRegsList csrPathsWithKind
                                     ($(getCsrPhysicalIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
    LetA mie         : Bit Xlen <- readRegsList csrPathsWithKind
                                     ($(getCsrPhysicalIdx "mie") : Expr ty (Bit CsrIdxSz)) ;
    Let  currMIE     : Bool     <- getMstatusMIE #mstatus ;
    Let  meie        : Bool     <- getMieMEIE #mie ;
    Let  mtie        : Bool     <- getMieMTIE #mie ;
    Let  meipPending : Bool     <- And [ #meip ; #meie ] ;
    Let  mtipPending : Bool     <- And [ #mtip ; #mtie ] ;
    Let  isInterrupt : Bool     <- And [ #currMIE ; Or [ #meipPending ; #mtipPending ] ] ;
    @Return ty rfTree InterruptPendingInfo (STRUCT {
      "isInterrupt" ::= #isInterrupt ;
      "meipPending" ::= #meipPending ;
      "mtipPending" ::= #mtipPending ;
      "currMIE"     ::= #currMIE ;
      "mstatus"     ::= #mstatus
    }).

  Definition executeNonDeferred (currPcc : ty FullECapWithTag) (meip mtip : ty Bool) (aluOut : ty AluOutUnion)
    : Action ty rfTree ExecuteOut :=
    Let  isComp         : Bool                       <- ##aluOut`"isComp" ;
    Let  dstIdx         : Bit RegIdxSzReal           <- ##aluOut`"dstIdx" ;
    Let  dstVal         : FullECapWithTag            <- ##aluOut`"dstValue" ;
    Let  aluOp          : AluOpUnion                 <- ##aluOut`"Op" ;
    Let  pcStep         : Addr                       <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;

    Let  seqPcc         : FullECapWithTag            <- #currPcc `{ "addr" <- Add [ ##currPcc`"addr" ; #pcStep ] } ;

    Let  isExc          : Bool                       <- #aluOp `? "Exception" ;
    Let  noExc          : NoExceptionUnion           <- #aluOp `! "NoException" ;

    LetA intInfo        : InterruptPendingInfo       <- isInterruptPending meip mtip ;
    Let  isInterrupt    : Bool                       <- ##intInfo`"isInterrupt" ;
    Let  meipPending    : Bool                       <- ##intInfo`"meipPending" ;
    Let  mtipPending    : Bool                       <- ##intInfo`"mtipPending" ;
    Let  currMIE        : Bool                       <- ##intInfo`"currMIE" ;
    Let  mstatus        : Bit Xlen                   <- ##intInfo`"mstatus" ;

    (* Cause number, not the bitmask; external outranks timer.  ITE not caseDefault,
       which would OR the two when both are pending. *)
    Let  intCauseNo     : Bit (Xlen - 1)             <- ITE #meipPending $MEIP_Bit (ITE0 #mtipPending $MTIP_Bit) ;
    Let  isTrap         : Bool                       <- Or [ #isInterrupt ; #isExc ] ;

    Let  isDeferred     : Bool                       <- And [ Not #isTrap ; #noExc `? "Deferred" ] ;
    Let  deferredVal    : DeferredUnion              <- #noExc `! "Deferred" ;
    Let  deferredReq    : DeferredReq                <- STRUCT {
      "dstIdx" ::= #dstIdx ;
      "addr"   ::= ##dstVal`"addr" ;
      "op"     ::= #deferredVal
    } ;

    Let  notDeferredVal : NotDeferredUnion           <- #noExc `! "NotDeferred" ;
    Let  normFence      : NormalFenceIUnion          <- #notDeferredVal `! "NormalFenceI" ;
    Let  isFenceI       : Bool                       <- And [ Not #isTrap ;
                                                              ##noExc `? "NotDeferred" ;
                                                              ##notDeferredVal `? "NormalFenceI" ;
                                                              ##normFence `? "FenceI" ] ;
    LetA mtcc           : FullECapWithTag            <- readRegsList scrPathsWithKind ($(getScrIdx "Mtcc") : Expr ty (Bit ScrIdxSz)) ;
    Let  trapCfVal      : CfPayload                  <- STRUCT {
      "NewPcc" ::= #mtcc ;
      "CfOp"   ::= UNION (CfOpType, "ControlFlowAddrECap" ::=
                     UNION (ControlFlowAddrECapOpType, "MretTrap" ::=
                       UNION (MretTrapOpType, "Trap" ::= Const ty (Bit 0) Zmod.zero)))
    } ;
    Let  cfScrCsr       : CfScrCsrUnion              <- #notDeferredVal `! "CfScrCsr" ;
    Let  cfVal          : CfPayload                  <- #cfScrCsr `! "ControlFlow" ;
    Let  isCf           : Bool                       <- And [ Not #isTrap ;
                                                              ##noExc `? "NotDeferred" ;
                                                              ##notDeferredVal `? "CfScrCsr" ;
                                                              ##cfScrCsr `? "ControlFlow" ] ;
    Let  cfOpt          : Option CfPayload           <- Or [ ITE0 #isTrap (mkSome #trapCfVal) ;
                                                             ITE0 #isCf (mkSome #cfVal) ] ;

    LetIf nextPcc : FullECapWithTag <-
      If #isTrap Then
        (
          Let  excVal     : ExceptionInfo   <- #aluOp `! "Exception" ;
          Let  mstatus1   : Bit Xlen        <- setMstatusMPIE #mstatus #currMIE ;
          Let  newMstatus : Bit Xlen        <- setMstatusMIE #mstatus1 (ConstBool false) ;
          Let  newMcause  : Bit Xlen        <- ITE #isInterrupt
                                                  {< Const ty (Bit 1) (bits.of_Z 1 1), #intCauseNo >}
                                                  (encodeMcause ##excVal`"mcause") ;
          Let  newMtval   : Bit Xlen        <- ITE #isInterrupt $0 (encodeCheriMtval ##excVal`"mtval") ;

          Act (writeRegsList scrPathsWithKind ($(getScrIdx "MePcc") : Expr ty (Bit ScrIdxSz)) #currPcc) ;
          Act (writeRegsList csrPathsWithKind ($(getCsrPhysicalIdx "mcause") : Expr ty (Bit CsrIdxSz)) #newMcause) ;
          Act (writeRegsList csrPathsWithKind ($(getCsrPhysicalIdx "mtval") : Expr ty (Bit CsrIdxSz)) #newMtval) ;
          Act (writeRegsList csrPathsWithKind ($(getCsrPhysicalIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
          Return #mtcc
        )
      Else
        (
          Act incrementMinstret ;
          LetIf nextPccNonTrap : FullECapWithTag <-
            If (#noExc `? "Deferred") Then
              (
                Let memFence   : MemFenceUnion   <- #deferredVal `! "MemFence" ;
                Let memPayload : MemPayload      <- #memFence `! "Mem" ;
                Let memOp      : LoadOrStoreKind <- ##memPayload`"memOp" ;
                Let stAddr     : Addr            <- ##dstVal`"addr" ;
                If (And [ #deferredVal `? "MemFence" ;
                          #memFence `? "Mem" ;
                          #memOp `? "Store" ]) Then
                  (
                    updateMshwmOnStore stAddr
                  ) ;
                Return #seqPcc
              )
            Else
              (
                If (isNotZero #dstIdx) Then
                  (writeRegsList gprPathsWithKind #dstIdx #dstVal) ;

                LetIf nextPccNotDef : FullECapWithTag <-
                  If (##notDeferredVal `? "NormalFenceI") Then
                    (
                      Return #seqPcc
                    )
                  Else
                    (
                      Let cfScrCsr : CfScrCsrUnion <- #notDeferredVal `! "CfScrCsr" ;
                      LetIf nextPccCfScrCsr : FullECapWithTag <-
                        If (##cfScrCsr `? "ScrCsr") Then
                          (
                            Let scrCsr : ScrCsrPayload       <- #cfScrCsr `! "ScrCsr" ;
                            Let sDest  : TaggedUnion ScrCsrIdx <- ##scrCsr`"SpecialDest" ;
                            Let sVal   : FullECapWithTag      <- ##scrCsr`"SpecialValue" ;

                            If ##scrCsr`"isWrite" Then (
                              If (#sDest `? "Scr") Then
                                (
                                  Let scrIdx : Bit ScrIdxSz <- #sDest `! "Scr" ;
                                  writeRegsList scrPathsWithKind #scrIdx #sVal
                                )
                              Else
                                (
                                  Let csrIdx : Bit CsrIdxSz <- #sDest `! "Csr" ;
                                  writeRegsList csrPathsWithKind #csrIdx ##sVal`"addr"
                                ) ;
                              Retv
                            ) ;
                            Return #seqPcc
                          )
                        Else
                          (
                            Let cf     : CfPayload           <- #cfScrCsr `! "ControlFlow" ;
                            Let newPcc : FullECapWithTag     <- ##cf`"NewPcc" ;
                            Let cfOp   : CfOp                <- ##cf`"CfOp" ;

                            LetIf nextPccCf : FullECapWithTag <-
                              If (#cfOp `? "ControlFlowAddrOnly") Then
                                (
                                  Let addrOnlyOp : ControlFlowAddrOnlyOp <- #cfOp `! "ControlFlowAddrOnly" ;
                                  LetIf nextPccAO : FullECapWithTag <-
                                    If (##addrOnlyOp `? "Branch") Then
                                      (
                                        Let isTaken   : Bool            <- #addrOnlyOp `! "Branch" ;
                                        Let targetPcc : FullECapWithTag <- #currPcc `{ "addr" <- ##newPcc`"addr" } ;
                                        Let nextPcc   : FullECapWithTag <- ITE #isTaken #targetPcc #seqPcc ;
                                        Return #nextPcc
                                      )
                                    Else
                                      (
                                        Let targetPcc : FullECapWithTag <- #currPcc `{ "addr" <- ##newPcc`"addr" } ;
                                        Return #targetPcc
                                      ) ;
                                  Return #nextPccAO
                                )
                              Else
                                (
                                  Let addrECapOp : ControlFlowAddrECapOp <- #cfOp `! "ControlFlowAddrECap" ;
                                  LetIf nextPccECap : FullECapWithTag <-
                                    If (##addrECapOp `? "Cjalr") Then
                                      (
                                        Let  newMIE     : Bool     <- #addrECapOp `! "Cjalr" ;
                                        Let  newMstatus : Bit Xlen <- setMstatusMIE #mstatus #newMIE ;
                                        Act (writeRegsList csrPathsWithKind
                                               ($(getCsrPhysicalIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
                                        Return #newPcc
                                      )
                                    Else
                                      (
                                        Let  currMPIE   : Bool     <- getMstatusMPIE #mstatus ;
                                        Let  newMstatus : Bit Xlen <- setMstatusMIE #mstatus #currMPIE ;
                                        Act (writeRegsList csrPathsWithKind
                                               ($(getCsrPhysicalIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
                                        Return #newPcc
                                      ) ;
                                  Return #nextPccECap
                                ) ;
                            Return #nextPccCf
                          ) ;
                      Return #nextPccCfScrCsr
                    ) ;
                Return #nextPccNotDef
              ) ;
          (* MePrevPcc is effectively a read-only SCR *)
          Act (writeRegsList scrPathsWithKind ($(getScrIdx "MePrevPcc") : Expr ty (Bit ScrIdxSz)) #currPcc) ;
          Return #nextPccNonTrap
        ) ;
    Act (writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc) ;
    Let execOut : ExecuteOut <- STRUCT {
      "deferredReq" ::= ITE0 #isDeferred (mkSome #deferredReq) ;
      "cf"          ::= #cfOpt ;
      "nextPc"      ::= ##nextPcc`"addr" ;
      "isFenceIRq"  ::= #isFenceI
    } ;
    Return #execOut.

  Definition regRead (meip mtip : ty Bool) (regReadIn : ty RegReadIn) : Action ty rfTree AluInInstGroup :=
    Let  decodeOut  : DecodeOut             <- ##regReadIn`"decodeOut" ;
    Let  fetchExc   : FetchException        <- ##regReadIn`"fetchExc" ;
    Let  cs1Idx     : Bit RegIdxSzReal      <- ##decodeOut`"cs1Idx" ;
    Let  cs2Source  : TaggedUnion Cs2Source <- ##decodeOut`"cs2Idx" ;

    LetA cs1Raw     : FullECapWithTag       <- readRegsList gprPathsWithKind #cs1Idx ;
    Let  cs1        : FullECapWithTag       <- ITE (isNotZero #cs1Idx) #cs1Raw (Const ty FullECapWithTag (getDefault _)) ;

    LetIf cs2 : FullECapWithTag <-
      If (#cs2Source `? "Reg") Then
        (
          Let  cs2Idx : Bit RegIdxSzReal <- #cs2Source `! "Reg" ;
          LetA cs2Raw : FullECapWithTag  <- readRegsList gprPathsWithKind #cs2Idx ;
          Return (ITE (isNotZero #cs2Idx) #cs2Raw (Const ty FullECapWithTag (getDefault _)))
        )
      Else
        (
          Let scrCsr : TaggedUnion ScrCsrIdx <- #cs2Source `! "ScrCsr" ;
          LetIf scrCsrVal : FullECapWithTag <-
            If (#scrCsr `? "Scr") Then
              (
                Let scrIdx : Bit ScrIdxSz <- #scrCsr `! "Scr" ;
                readRegsList scrPathsWithKind #scrIdx
              )
            Else
              (
                Let  csrIdx  : Bit CsrIdxSz    <- #scrCsr `! "Csr" ;
                (* Physical read yields 0 for a virtual CSR: its index is past the register list. *)
                LetA csrPhys : Bit Xlen        <- readRegsList csrPathsWithKind #csrIdx ;
                Let  csrVal  : Bit Xlen        <- Or [ #csrPhys ;
                                                       ITE0 (Eq #csrIdx $(getCsrIdx "mip"))
                                                            (createMip #meip #mtip) ] ;
                Let  csrCap : FullECapWithTag <- STRUCT {
                  "tag"  ::= Const ty Bool false ;
                  "ecap" ::= Const ty ECap (getDefault _) ;
                  "addr" ::= #csrVal
                } ;
                Return #csrCap
              ) ;
          Return #scrCsrVal
        ) ;

    LetA mstatus  : Bit Xlen <- readRegsList csrPathsWithKind ($(getCsrPhysicalIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
    Let  currMIE  : Bool     <- getMstatusMIE #mstatus ;

    @Return ty rfTree AluInInstGroup (STRUCT {
      "cs2Idx"              ::= #cs2Source ;
      "writesCd"            ::= ##decodeOut`"writesCd" ;
      "inst"                ::= ##regReadIn`"inst" ;
      "decodeExc"           ::= ##decodeOut`"decodeExc" ;
      "fetchExc"            ::= #fetchExc ;
      "cs1"                 ::= #cs1 ;
      "cs2"                 ::= #cs2 ;
      "currInterruptStatus" ::= #currMIE ;
      "instGroup"           ::= ##decodeOut`"instGroup"
    }).
End AluRF.
