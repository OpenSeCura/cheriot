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
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines.
From Cheriot Require Export FunctionalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Section Alu.
  Variable ty : Kind -> Type.

  Definition AluRouting (aluIn : ty AluIn) : LetExpr ty AluOut :=
    LetE cs2Idx : TaggedUnion Cs2Source <- ##aluIn`"cs2Idx" ;
    LetE inst : Inst <- ##aluIn`"inst" ;
    LetE decodeExc : DecodeException <- ##aluIn`"decodeExc" ;
    LetE fetchExc : FetchException <- ##aluIn`"fetchExc" ;
    LetE cs1 : FullECapWithTag <- ##aluIn`"cs1" ;
    LetE cs2 : FullECapWithTag <- ##aluIn`"cs2" ;
    LetE currInterruptStatus : Bool <- ##aluIn`"currInterruptStatus" ;
    LetE aluControl : AluControl <- ##aluIn`"aluControl" ;

    LetE isComp  : Bool     <- isCompressed inst ;
    LetE pccAddr : Addr <- ##aluIn`"pcc"`"addr" ;
    LetE pccTag : Bool <- ##aluIn`"pcc"`"tag" ;
    LetE pccBase : Bit (AddrSz + 1) <- ##aluIn`"pcc"`"ecap"`"base" ;
    LetE pcc_cE : Bit ExpSz <- ##aluIn`"pcc"`"ecap"`"cE" ;
    LetE pccExp : Bit ExpSz <- get_E_from_cE pcc_cE ;

    LetE cs1Addr : Addr <- ##cs1`"addr" ;
    LetE cs1Tag : Bool <- ##cs1`"tag" ;
    LetE cs1ECap : ECap <- ##cs1`"ecap" ;
    LetE cs1Base : Bit (AddrSz + 1) <- ##cs1ECap`"base" ;
    LetE cs1Top : Bit (AddrSz + 2) <- ##cs1ECap`"top" ;
    LetE cs1_cE : Bit ExpSz <- ##cs1ECap`"cE" ;
    LetE cs1Exp : Bit ExpSz <- get_E_from_cE cs1_cE ;
    LetE cs1Perms : CapPerms <- ##cs1ECap`"perms" ;
    LetE cs1OType : Bit CapOTypeSz <- ##cs1ECap`"oType" ;

    LetE cs2Addr : Addr <- ##cs2`"addr" ;
    LetE cs2Tag : Bool <- ##cs2`"tag" ;
    LetE cs2ECap : ECap <- ##cs2`"ecap" ;
    LetE cs2Base : Bit (AddrSz + 1) <- ##cs2ECap`"base" ;
    LetE cs2Top : Bit (AddrSz + 2) <- ##cs2ECap`"top" ;
    LetE cs2Perms : CapPerms <- ##cs2ECap`"perms" ;

    LetE simm12 : Bit Xlen <- SignExtendTo Xlen (##inst`[31:20]) ;
    LetE zimm12 : Bit Xlen <- ZeroExtendTo Xlen (##inst`[31:20]) ;
    LetE uimm20 : Bit Xlen <- ({< ##inst`[31:12], Const ty (Bit 12) Zmod.zero >}) ;
    LetE uimm20_11 : Bit Xlen <-
      ({< ##inst`[31:31], ##inst`[31:12], Const ty (Bit 11) Zmod.zero >}) ;
    LetE shamt <- ##inst`[24:20] ;
    LetE zimm5 : Bit 5 <- ##inst`[19:15] ;
    LetE bimm13 : Bit 13 <-
      ({< ##inst`[31:31], ##inst`[7:7], ##inst`[30:25], ##inst`[11:8],
          Const _ (Bit 1) Zmod.zero >}) ;
    LetE bimm12 : Bit Xlen <- SignExtendTo Xlen #bimm13 ;
    LetE jimm21 : Bit 21 <-
      ({< ##inst`[31:31], ##inst`[19:12], ##inst`[20:20], ##inst`[30:21],
          Const _ (Bit 1) Zmod.zero >}) ;
    LetE jimm20 : Bit Xlen <- SignExtendTo Xlen #jimm21 ;
    LetE scrIdx : Bit ScrAddrSz <- getScr inst ;
    LetE cs1Idx : Bit RegIdxSz <- getCs1 inst ;
    LetE dstIdx : Bit RegIdxSz <- getCd inst ;
    LetE memSize : Bit LgLgNumBytesFullCapSz <- getMemSize inst ;

    LetE BranchOrCjalOrAuiPcc : Bool <- ##aluControl`"BranchOrCjalOrAuiPcc" ;
    LetE BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr : Bool <-
      ##aluControl`"BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr" ;

    LetE AdderBeforeBoundsCheck_base : Addr <-
      ITE (#BranchOrCjalOrAuiPcc) #pccAddr #cs1Addr ;
    LetE AdderBeforeBoundsCheck_offset : Addr <-
      caseDefault (k := Addr) [
          (##aluControl`"Branch", #bimm12) ;
          (##aluControl`"Cjal", #jimm20) ;
          (##aluControl`"AdderBeforeBoundsCheck_offset_uimm20_11", #uimm20_11) ;
          (##aluControl`"AdderBeforeBoundsCheck_offset_cs2Addr", #cs2Addr) ;
          (##aluControl`"Bounds_isImm", #zimm12) ]
        #simm12 ;
    LETE AdderBeforeBoundsCheckOut : Addr <-
      AdderBeforeBoundsCheck AdderBeforeBoundsCheck_base AdderBeforeBoundsCheck_offset ;

    LetE AdderToOutput_base : Bit Xlen <-
      caseDefault (k := Bit Xlen) [
          (##aluControl`"AdderToOutput_base_pccAddr", #pccAddr) ;
          (##aluControl`"CGetLen", TruncLsb 2 AddrSz #cs1Top) ]
        #cs1Addr ;
    LetE AdderToOutput_offset : Bit Xlen <-
      caseDefault (k := Bit Xlen) [
          (##aluControl`"AdderToOutput_offset_const2", Const ty (Bit Xlen) (Zmod.of_Z _ (CompInstSz/8))) ;
          (##aluControl`"AdderToOutput_offset_cs2Addr", #cs2Addr) ;
          (##aluControl`"AdderToOutput_offset_simm12", #simm12) ;
          (##aluControl`"CGetLen", TruncLsb 1 AddrSz #cs1Base) ]
        (Const ty (Bit Xlen) (Zmod.of_Z _ (InstSz/8))) ;
    LetE AdderToOutput_isSub : Bool <- ##aluControl`"AdderToOutput_isSub" ;
    LETE AdderToOutputOut : Bit Xlen <-
      AdderToOutput AdderToOutput_base AdderToOutput_offset AdderToOutput_isSub ;

    LetE AddCapBSz_baseExp : Bit ExpSz <-
      ITE (#BranchOrCjalOrAuiPcc) #pccExp #cs1Exp ;
    LETE AddCapBSzOut : Bit ExpSz <- AddCapBSz AddCapBSz_baseExp ;

    LetE Shifter_data : Bit Xlen <-
      ITE (##aluControl`"Shift")
          #cs1Addr (Const ty (Bit Xlen) (Zmod.of_Z _ 1)) ;
    LetE Shifter_shamt : Bit RegIdxSz <-
      caseDefault (k := Bit RegIdxSz) [
          (##aluControl`"Shifter_shamt_cs2Addr", TruncLsb (AddrSz - RegIdxSz) RegIdxSz #cs2Addr) ;
          (#BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr, #AddCapBSzOut) ]
        #shamt ;
    LetE Shifter_isRight : Bool <- ##aluControl`"Shifter_isRight" ;
    LetE Shifter_isArith : Bool <- ##aluControl`"Shifter_isArith" ;
    LETE ShifterOut : Bit Xlen <-
      Shifter Shifter_data Shifter_shamt Shifter_isRight Shifter_isArith ;

    LetE AdderBeforeRepCheck_base : Bit (AddrSz + 1) <-
      ITE (#BranchOrCjalOrAuiPcc) #pccBase #cs1Base ;
    LetE AdderBeforeRepCheck_shifter : Bit (AddrSz + 1) <- ZeroExtendTo (AddrSz + 1) #ShifterOut ;
    LETE AdderBeforeRepCheckOut : Bit (AddrSz + 1) <-
      AdderBeforeRepCheck AdderBeforeRepCheck_base AdderBeforeRepCheck_shifter ;

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
          (#BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr, ZeroExtendTo (AddrSz + 2) #AdderBeforeRepCheckOut) ;
          (##aluControl`"SealOrUnsealOrSubset", #cs2Top) ]
        #cs1Top ;
    LetE ComparatorTopOrRep_checkLte : Bool <- ##aluControl`"ComparatorTopOrRep_checkLte" ;
    LETE ComparatorTopOrRepOut : ComparatorOut <-
      ComparatorTopOrRep ComparatorTopOrRep_addr ComparatorTopOrRep_topRep ComparatorTopOrRep_checkLte ;

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
    LetE ComparatorGeneral_isUnsigned : Bool <- ##aluControl`"isUnsigned" ;
    LetE ComparatorGeneral_checkLt    : Bool <- ##aluControl`"ComparatorGeneral_checkLt" ;
    LetE ComparatorGeneral_checkEq    : Bool <- ##aluControl`"ComparatorGeneral_checkEq" ;
    LetE ComparatorGeneral_invertRes  : Bool <- ##aluControl`"ComparatorGeneral_invertRes" ;
    LETE ComparatorGeneralOut : ComparatorGeneralRes <-
      ComparatorGeneral ComparatorGeneral_op1 ComparatorGeneral_op2
                        ComparatorGeneral_isUnsigned ComparatorGeneral_checkLt
                        ComparatorGeneral_checkEq ComparatorGeneral_invertRes ;

    LETE CjalrUnitOut : CjalrUnitRes <- CjalrUnit cs1 inst currInterruptStatus ;

    LetE Logical_op1 : Bit Xlen <- #cs1Addr ;
    LetE Logical_op2 : Bit Xlen <-
      ITE (##aluControl`"Logical_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
    LetE Logical_opSel : Bit 2 <- ##inst`[13:12] ;
    LETE LogicalOut : Bit Xlen <- Logical Logical_op1 Logical_op2 Logical_opSel ;

    LETE CAndPermOut : TagECap <- CAndPerm cs1Tag cs1ECap cs2Addr ;

    LetE Bounds_reqLimit : Addr <-
      caseDefault (k := Addr) [ (##aluControl`"Bounds_reqLimit_cs2Addr", #cs2Addr) ;
                                     (##aluControl`"Bounds_reqLimit_cs1Addr", #cs1Addr) ]
        #zimm12 ;
    LetE Bounds_isRoundDown : Bool <- ##aluControl`"Bounds_isRoundDown" ;
    LETE BoundsOut : BoundsRes <- Bounds cs1Addr Bounds_reqLimit Bounds_isRoundDown ;

    LetE Bounds_boundsExact : Bool <- ##BoundsOut`"exact" ;
    LetE Bounds_instIsExact : Bool <- ##aluControl`"Bounds_isExact" ;
    LETE BoundsExactOut : Bool <- BoundsExact AddrBoundsCheckOut Bounds_boundsExact Bounds_instIsExact ;

    LetE Saturater_isBase : Bool <- ##aluControl`"CGetBase" ;
    LetE Saturater_isTop : Bool <- ##aluControl`"CGetTop" ;
    LetE Saturater_isLen : Bool <- ##aluControl`"CGetLen" ;
    LETE SaturaterOut : Bit Xlen <-
      Saturater cs1Base cs1Top AdderToOutputOut Saturater_isBase Saturater_isTop Saturater_isLen ;

    LETE CapSubsetOut : Bool <-
      CapSubset AddrBoundsCheck_topLt AddrBoundsCheck_baseGe cs1Tag cs2Tag cs1Perms cs2Perms ;

    LetE CapEq_addrEq : Bool <- ##ComparatorGeneralOut`"eq" ;
    LETE CapEqOut : Bool <- CapEq CapEq_addrEq cs1Tag cs2Tag cs1ECap cs2ECap ;

    LETE ScrSanitizerOut : Bool <- ScrSanitizer cs1Tag cs1Addr inst ;

    LetE isMret : Bool <- ##aluControl`"Mret" ;
    LetE isCjal : Bool <- ##aluControl`"Cjal" ;
    LetE isCjalr : Bool <- ##aluControl`"Cjalr" ;
    LetE isBranch : Bool <- ##aluControl`"Branch" ;
    LetE isCond : Bool <- ##ComparatorGeneralOut`"cond" ;

    LetE cjalrTag : Bool <- ##CjalrUnitOut`"tag" ;
    LetE cjalrEcap : ECap <- ##CjalrUnitOut`"ecap" ;
    LetE cjalrIntStatus : Bool <- ##CjalrUnitOut`"interruptStatus" ;
    LETE ControlFlowOut : Option CfPayload <-
      ControlFlow isMret isCjal isCjalr isBranch isCond cs2 AdderBeforeBoundsCheckOut
             AddrBoundsCheckOut cjalrTag cjalrEcap cjalrIntStatus pccTag ;

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
    LetE Bounds_outECap : ECap <- STRUCT { "R"     ::= ##cs1ECap`"R" ;
                                           "perms" ::= ##cs1ECap`"perms" ;
                                           "oType" ::= ##cs1ECap`"oType" ;
                                           "cE"    ::= ##BoundsOut`"cE" ;
                                           "top"   ::= ##BoundsOut`"top" ;
                                           "base"  ::= ##BoundsOut`"base" };

    LetE Reg_ecap : ECap <-
      caseDefault (k := ECap) [ (##aluControl`"Reg_ecap_pccEcap", ##aluIn`"pcc"`"ecap") ;
                                 (##aluControl`"Reg_ecap_cs1Ecap", ##cs1`"ecap") ;
                                 (##aluControl`"Scr", #cs2ECap) ;
                                 (##aluControl`"CSetHigh", #decodedECap) ;
                                 (##aluControl`"CAndPerm", ##CAndPermOut`"ecap") ;
                                 (##aluControl`"SealOrUnseal", ##SealerUnsealerOut`"ecap") ;
                                 (##aluControl`"CSetBounds", #Bounds_outECap) ]
        (Const ty ECap (getDefault _)) ;

    LetE Reg_addr : Addr <-
      caseDefault (k := Addr) [
          (##aluControl`"Reg_addr_AdderBeforeBoundsCheck", #AdderBeforeBoundsCheckOut) ;
          (##aluControl`"Slt",
           ZeroExtendTo Xlen (ToBit (##ComparatorGeneralOut`"cond"))) ;
          (##aluControl`"Shift", #ShifterOut) ;
          (##aluControl`"Logical", #LogicalOut) ;
          (##aluControl`"Reg_addr_AdderToOutput", #AdderToOutputOut) ;
          (##aluControl`"CGetPerm", ZeroExtendTo Xlen (ToBit (##cs1ECap`"perms"))) ;
          (##aluControl`"CGetType", ZeroExtendTo Xlen #cs1OType) ;
          (##aluControl`"CGetTag",  ZeroExtendTo Xlen (ToBit #cs1Tag)) ;
          (##aluControl`"CGetAddr", #cs1Addr) ;
          (##aluControl`"CGetHigh", ZeroExtendTo Xlen (ToBit #encodedCap)) ;
          (##aluControl`"Reg_addr_Saturater", #SaturaterOut) ;
          (##aluControl`"Reg_addr_cs2Addr", #cs2Addr) ;
          (##aluControl`"Reg_addr_zimm5", ZeroExtendTo Xlen #zimm5) ;
          (##aluControl`"Reg_addr_cs1Addr", #cs1Addr) ;
          (##aluControl`"CAndPerm", #cs1Addr) ;
          (##aluControl`"SealOrUnseal", #cs1Addr) ;
          (##aluControl`"CSetBounds", TruncLsb 1 AddrSz (##BoundsOut`"base")) ;
          (##aluControl`"Cram", TruncLsb 1 AddrSz (##BoundsOut`"cram")) ;
          (##aluControl`"Crrl", TruncLsb 1 AddrSz (##BoundsOut`"length")) ;
          (##aluControl`"CTestSubset", ZeroExtendTo Xlen (ToBit #CapSubsetOut)) ;
          (##aluControl`"CSetEqual", ZeroExtendTo Xlen (ToBit #CapEqOut)) ]
        #uimm20 ;

    LetE ecall : Bool <- ##aluControl`"ECall" ;
    LetE ebreak : Bool <- ##aluControl`"EBreak" ;
    LetE isLoad : Bool <- ##aluControl`"Load" ;
    LetE isStore : Bool <- ##aluControl`"Store" ;

    LETE ExceptionRes : Option ExceptionInfo <-
      ExceptionUnit ecall ebreak isLoad isStore
                    fetchExc decodeExc inst
                    cs1Tag cs1ECap AddrBoundsCheckOut AdderBeforeBoundsCheckOut ;

    LetE isFence : Bool <- ##aluControl`"Fence" ;
    LetE storeTag : Bool <- #cs2Tag ;
    LetE storeData : Addr <- #cs2Addr ;
    LETE DeferredOpRes : Option DeferredUnion <-
      Deferred isLoad isStore isFence cs1Perms inst AdderBeforeBoundsCheckOut storeTag encodedCap storeData ;

    LETE isFenceIOut : Bool <- FenceI inst isFence ;

    LetE RegVal : FullECapWithTag <-
      STRUCT { "tag" ::= #Reg_tag; "ecap" ::= #Reg_ecap; "addr" ::= #Reg_addr } ;

    LetE cfPayload : Option CfPayload <- #ControlFlowOut ;
  
    LETE ScrCsrOut : Option ScrCsrPayload <- ScrCsr cs2Idx ScrSanitizerOut cs1ECap cs1Addr ;

    @RetE _ AluOut (STRUCT {
      "isComp"      ::= #isComp ;
      "dstIdx"      ::= ITE0 (And [##aluIn`"writesCd"; Not (#ExceptionRes `? "Some")]) #dstIdx ;
      "dstValue"    ::= #RegVal ;
      "Exception"   ::= #ExceptionRes ;
      "Deferred"    ::= #DeferredOpRes ;
      "ControlFlow" ::= #cfPayload ;
      "ScrCsr"      ::= #ScrCsrOut ;
      "isFenceI"    ::= #isFenceIOut
    }).

  Definition Alu (routingOut : ty AluOut) : LetExpr ty AluOutUnion :=
    LetE excOpt      : Option ExceptionInfo <- ##routingOut`"Exception" ;
    LetE deferredOpt : Option DeferredUnion <- ##routingOut`"Deferred" ;
    LetE cfOpt       : Option CfPayload <- ##routingOut`"ControlFlow" ;
    LetE scrCsrOpt   : Option ScrCsrPayload <- ##routingOut`"ScrCsr" ;
    LetE isFenceI    : Bool <- ##routingOut`"isFenceI" ;

    LetE isExc : Bool <- #excOpt `? "Some" ;
    LetE excVal : ExceptionInfo <- #excOpt `! "Some" ;

    LetE isDeferred : Bool <- #deferredOpt `? "Some" ;
    LetE deferredVal : DeferredUnion <- #deferredOpt `! "Some" ;

    LetE isCf : Bool <- #cfOpt `? "Some" ;
    LetE cfVal : CfPayload <- #cfOpt `! "Some" ;

    LetE isScrCsr : Bool <- #scrCsrOpt `? "Some" ;
    LetE scrCsrVal : ScrCsrPayload <- #scrCsrOpt `! "Some" ;

    LetE cfScrCsrUnion : CfScrCsrUnion <-
      ITE #isCf
          (UNION (CfScrCsrType, "ControlFlow" ::= #cfVal))
          (UNION (CfScrCsrType, "ScrCsr" ::= #scrCsrVal)) ;

    LetE normalFenceIUnion : NormalFenceIUnion <-
      ITE #isFenceI
          (UNION (NormalFenceIType, "FenceI" ::= ConstDef))
          (UNION (NormalFenceIType, "Normal" ::= ConstDef)) ;

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
End Alu.

Section AluRF.
  Variable ty : Kind -> Type.

  Definition executeNonDeferred (aluOut : ty AluOutUnion)
    : Action ty rfTree ExecuteOut :=
    Let  isComp         : Bool                       <- ##aluOut`"isComp" ;
    Let  dstIdx         : Bit RegIdxSz               <- ##aluOut`"dstIdx" ;
    Let  dstVal         : FullECapWithTag            <- ##aluOut`"dstValue" ;
    Let  aluOp          : AluOpUnion                 <- ##aluOut`"Op" ;
    Let  pcStep         : Addr                       <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;

    LetA currPcc        : FullECapWithTag            <- readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) ;
    Let  seqPcc         : FullECapWithTag            <- #currPcc `{ "addr" <- Add [ ##currPcc`"addr" ; #pcStep ] } ;

    Let  isExc          : Bool                       <- #aluOp `? "Exception" ;
    Let  noExc          : NoExceptionUnion           <- #aluOp `! "NoException" ;

    LetA mstatus        : Bit Xlen                   <- readRegsList csrPathsWithKind
                                                          ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
    LetA mip            : Bit Xlen                   <- readRegsList csrPathsWithKind
                                                          ($(getCsrIdx "mip") : Expr ty (Bit CsrIdxSz)) ;
    Let  currMIE        : Bool                       <- getMstatusMIE #mstatus ;
    Let  isInterrupt    : Bool                       <- And [ #currMIE ; isNotZero #mip ] ;
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
    Let  cfScrCsr       : CfScrCsrUnion              <- #notDeferredVal `! "CfScrCsr" ;
    Let  cfVal          : CfPayload                  <- #cfScrCsr `! "ControlFlow" ;
    Let  isCf           : Bool                       <- And [ Not #isTrap ;
                                                              ##noExc `? "NotDeferred" ;
                                                              ##notDeferredVal `? "CfScrCsr" ;
                                                              ##cfScrCsr `? "ControlFlow" ] ;
    Let  cfOpt          : Option CfPayload           <- ITE0 #isCf (mkSome #cfVal) ;

    If #isTrap Then
      (
        Let  excVal     : ExceptionInfo   <- #aluOp `! "Exception" ;
        LetA mtcc       : FullECapWithTag <- readRegsList scrPathsWithKind ($(getScrIdx "Mtcc") : Expr ty (Bit ScrIdxSz)) ;
        Let  mstatus1   : Bit Xlen        <- setMstatusMPIE #mstatus #currMIE ;
        Let  newMstatus : Bit Xlen        <- setMstatusMIE #mstatus1 (ConstBool false) ;
        Let  newMcause  : Bit Xlen        <- ITE #isInterrupt
                                                {< Const ty (Bit 1) (bits.of_Z 1 1), TruncLsb 1 (Xlen - 1) #mip >}
                                                (encodeMcause ##excVal`"mcause") ;
        Let  newMtval   : Bit Xlen        <- ITE #isInterrupt $0 (encodeCheriMtval ##excVal`"mtval") ;

        Act (writeRegsList scrPathsWithKind ($(getScrIdx "MePcc") : Expr ty (Bit ScrIdxSz)) #currPcc) ;
        Act (writeRegsList csrPathsWithKind ($(getCsrIdx "mcause") : Expr ty (Bit CsrIdxSz)) #newMcause) ;
        Act (writeRegsList csrPathsWithKind ($(getCsrIdx "mtval") : Expr ty (Bit CsrIdxSz)) #newMtval) ;
        Act (writeRegsList csrPathsWithKind ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
        writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #mtcc
      )
    Else
      (
        If (#noExc `? "Deferred") Then
          (
            writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #seqPcc
          )
        Else
          (
            Act incrementMinstret ;
            If (isNotZero #dstIdx) Then
              (writeRegsList gprPathsWithKind #dstIdx #dstVal) ;

            If (##notDeferredVal `? "NormalFenceI") Then
              (
                writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #seqPcc
              )
            Else
              (
                Let cfScrCsr : CfScrCsrUnion <- #notDeferredVal `! "CfScrCsr" ;
                If (##cfScrCsr `? "ScrCsr") Then
                  (
                    Let scrCsr : ScrCsrPayload       <- #cfScrCsr `! "ScrCsr" ;
                    Let sDest  : TaggedUnion ScrCsrIdx <- ##scrCsr`"SpecialDest" ;
                    Let sVal   : FullECapWithTag      <- ##scrCsr`"SpecialValue" ;

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
                    writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #seqPcc
                  )
                Else
                  (
                    Let cf     : CfPayload           <- #cfScrCsr `! "ControlFlow" ;
                    Let newPcc : FullECapWithTag     <- ##cf`"NewPcc" ;
                    Let cfOp   : CfOp                <- ##cf`"CfOp" ;

                    If (#cfOp `? "ControlFlowAddrOnly") Then
                      (
                        Let addrOnlyOp : ControlFlowAddrOnlyOp <- #cfOp `! "ControlFlowAddrOnly" ;
                        If (##addrOnlyOp `? "Branch") Then
                          (
                            Let isTaken   : Bool            <- #addrOnlyOp `! "Branch" ;
                            Let targetPcc : FullECapWithTag <- #currPcc `{ "addr" <- ##newPcc`"addr" } ;
                            Let nextPcc   : FullECapWithTag <- ITE #isTaken #targetPcc #seqPcc ;
                            writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #nextPcc
                          )
                        Else
                          (
                            Let targetPcc : FullECapWithTag <- #currPcc `{ "addr" <- ##newPcc`"addr" } ;
                            writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #targetPcc
                          ) ;
                        Retv
                      )
                    Else
                      (
                        Let addrECapOp : ControlFlowAddrECapOp <- #cfOp `! "ControlFlowAddrECap" ;
                        If (##addrECapOp `? "Cjalr") Then
                          (
                            Let  newMIE     : Bool           <- #addrECapOp `! "Cjalr" ;
                            LetA mstatus    : Bit Xlen       <- readRegsList csrPathsWithKind
                                                                  ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
                            Let  newMstatus : Bit Xlen       <- setMstatusMIE #mstatus #newMIE ;
                            Act (writeRegsList csrPathsWithKind
                                   ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
                            writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #newPcc
                          )
                        Else
                          (
                            LetA mePcc      : FullECapWithTag <- readRegsList scrPathsWithKind ($(getScrIdx "MePcc") : Expr ty (Bit ScrIdxSz)) ;
                            LetA mstatus    : Bit Xlen        <- readRegsList csrPathsWithKind
                                                                  ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
                            Let  currMPIE   : Bool            <- getMstatusMPIE #mstatus ;
                            Let  newMstatus : Bit Xlen        <- setMstatusMIE #mstatus #currMPIE ;
                            Act (writeRegsList csrPathsWithKind
                                   ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) #newMstatus) ;
                            writeRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal)) #mePcc
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
    Let execOut : ExecuteOut <- STRUCT {
      "deferredReq" ::= ITE0 #isDeferred (mkSome #deferredReq) ;
      "cf"          ::= #cfOpt ;
      "isFenceIRq"  ::= #isFenceI
    } ;
    Return #execOut.

  Definition regRead (regReadIn : ty RegReadIn) : Action ty rfTree AluInInstGroup :=
    Let  pcc        : FullECapWithTag       <- ##regReadIn`"pcc" ;
    Let  decodeOut  : DecodeOut             <- ##regReadIn`"decodeOut" ;
    Let  fetchExc   : FetchException        <- ##regReadIn`"fetchExc" ;
    Let  cs1Idx     : Bit RegIdxSzReal      <- ##decodeOut`"cs1Idx" ;
    Let  cs2Source  : TaggedUnion Cs2Source <- ##decodeOut`"cs2Idx" ;

    LetA cs1        : FullECapWithTag       <- readRegsList gprPathsWithKind #cs1Idx ;

    LetIf cs2 : FullECapWithTag <-
      If (#cs2Source `? "Reg") Then
        (
          Let  cs2Idx : Bit RegIdxSzReal <- #cs2Source `! "Reg" ;
          readRegsList gprPathsWithKind #cs2Idx
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
                Let  csrIdx : Bit CsrIdxSz    <- #scrCsr `! "Csr" ;
                LetA csrVal : Bit Xlen        <- readRegsList csrPathsWithKind #csrIdx ;
                Let  csrCap : FullECapWithTag <- STRUCT {
                  "tag"  ::= Const ty Bool false ;
                  "ecap" ::= Const ty ECap (getDefault _) ;
                  "addr" ::= #csrVal
                } ;
                Return #csrCap
              ) ;
          Return #scrCsrVal
        ) ;

    LetA mstatus  : Bit Xlen <- readRegsList csrPathsWithKind ($(getCsrIdx "mstatus") : Expr ty (Bit CsrIdxSz)) ;
    Let  currMIE  : Bool     <- getMstatusMIE #mstatus ;

    @Return ty rfTree AluInInstGroup (STRUCT {
      "cs2Idx"              ::= #cs2Source ;
      "writesCd"            ::= ##decodeOut`"writesCd" ;
      "inst"                ::= ##decodeOut`"instBits" ;
      "decodeExc"           ::= ##decodeOut`"decodeExc" ;
      "fetchExc"            ::= #fetchExc ;
      "pcc"                 ::= #pcc ;
      "cs1"                 ::= #cs1 ;
      "cs2"                 ::= #cs2 ;
      "currInterruptStatus" ::= #currMIE ;
      "instGroup"           ::= ##decodeOut`"instGroup"
    }).
End AluRF.
