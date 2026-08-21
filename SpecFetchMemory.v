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

From Stdlib Require Import String List ZArith Zmod Psatz Bool.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section SpecFetchMemory.
  Variable config : MemConfig.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree config).
  Local Notation tree := (specTree config).
  Local Notation isMemAddr := (isMemAddr config).
  Local Notation isTagsAddr := (isTagsAddr config).
  Local Notation isHeapAddr := (isHeapAddr config).
  Local Notation tagsStartAddr := (tagsStartAddr config).
  Local Notation tagsSize := (tagsSize config).

  Definition np_rf : NodePath tree :=
    getNodePath tree "core.rf".

  Definition np_mem : NodePath tree :=
    getNodePath tree "core.mem".

  Local Notation computeRevBitAddr := (computeRevBitAddr config).

  (* =========================================================================
   * Revocation Bit Helper (Combinational Action on specMemTree)
   * ========================================================================= *)
  Definition readRevBit (base : Expr ty (Bit (AddrSz + 1))) : Action ty memTree Bool :=
    LetL lookup  : RevBitLookup <- computeRevBitAddr base ;
    Let  offset  <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) ##lookup`"revByteAddr" ;
    RegRead memVal <- "mem.mainMem" in memTree ;
    Let  byteVal : Bit 8 <- ReadArray #memVal #offset ;
    Let  revBit  : Bool  <- extractRevBit lookup #byteVal ;
    Return #revBit.

  (* =========================================================================
   * 1. specFetch (Atomic Combinational Fetch)
   * ========================================================================= *)
  Definition specFetch : Action ty tree FetchOut :=
    LetA pcc : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
    Let offset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) ##pcc`"addr" ;
    LetA rawInst : Inst <- liftAction np_mem (
      RegRead memVal <- "mem.mainMem" in memTree ;
      Let instBytes : Array (Z.to_nat (InstSz / 8)) (Bit 8) <- slice #memVal #offset (Z.to_nat (InstSz / 8)) ;
      Return (ToBit #instBytes)
    ) ;

    (* Fetch Exception Checks *)
    Let isComp       : Bool <- isCompressed rawInst ;
    Let instBytesLen : Addr <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
    Let tagExc       : Bool <- Not ##pcc`"tag" ;
    Let sealExc      : Bool <- isNotZero (##pcc`"ecap"`"oType") ;
    Let permExc      : Bool <- Not (##pcc`"ecap"`"perms"`"EX") ;
    Let boundsExc    : Bool <- Or [
      Slt (ZeroExtendTo (AddrSz + 2) ##pcc`"addr") (ZeroExtendTo (AddrSz + 2) ##pcc`"ecap"`"base") ;
      Sgt (ZeroExtendTo (AddrSz + 2) (Add [ ##pcc`"addr" ; #instBytesLen ])) (##pcc`"ecap"`"top")
    ] ;

    Let fetchOut : FetchOut <- STRUCT {
      "pcc"      ::= #pcc ;
      "inst"     ::= #rawInst ;
      "fetchExc" ::= STRUCT {
        "tag"    ::= #tagExc ;
        "seal"   ::= #sealExc ;
        "perm"   ::= #permExc ;
        "bounds" ::= #boundsExc
      }
    } ;
    Return #fetchOut.

  (* =========================================================================
   * 2. specExecuteDeferredReq (Single Deferred Request execution)
   * ========================================================================= *)
  Definition specExecuteDeferredReq (req : ty DeferredReq) : Action ty tree (Bit 0) :=
    Let  dstIdx : Bit RegIdxSz   <- ##req`"dstIdx" ;
    Let  addr   : Addr           <- ##req`"addr" ;
    Let  op     : DeferredUnion  <- ##req`"op" ;

    If (#op `? "Mem") Then (
      Let memPayload : MemPayload        <- #op `! "Mem" ;
      Let memSize    : Bit LgLgNumBytesFullCapSz <- ##memPayload`"memSize" ;
      Let memOp      : LoadOrStoreKind   <- ##memPayload`"memOp" ;
      Let isCap      : Bool              <- Eq #memSize $LgNumBytesFullCapSz ;

      Let offset     <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) #addr ;
      Let tagAddr    : Bit TagAddrWidth  <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #addr ;
      Let tagOffset  <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) #tagAddr ;

      If (#memOp `? "Store") Then (
        Let stCapVal   : FullCapWithTag <- #memOp `! "Store" ;
        Let stTag      : Bool           <- And [ #isCap ; ##stCapVal`"tag" ] ;
        Let rawData    : Bit FullCapSz  <-
          ITE #isCap
              {< ToBit ##stCapVal`"cap", ##stCapVal`"addr" >}
              (ZeroExtendTo FullCapSz ##stCapVal`"addr") ;
        Let num_bytes  : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 #memSize ;

        Act (liftAction np_mem (
          RegRead memVal  <- "mem.mainMem" in memTree ;
          RegRead tagsVal <- "mem.tags"    in memTree ;
          LetL updatedMem : Array config.(mainMemSize) (Bit 8) <-
            updSlice #memVal #offset (FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData) #num_bytes ;
          RegWrite "mem.mainMem" in memTree <- #updatedMem ;
          RegWrite "mem.tags" in memTree <- UpdateArray #tagsVal #tagOffset #stTag ;
          Retv
        )) ;
        Retv
      ) Else (
        (* Load Operation *)
        Let  ldOpVal    : LoadOp <- #memOp `! "Load" ;
        Let  isUnsigned : Bool   <- ##ldOpVal`"isUnsigned" ;
        LetA rawBits    : Bit FullCapSz <-
          liftAction np_mem (
            RegRead memVal <- "mem.mainMem" in memTree ;
            Let dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <- slice #memVal #offset (Z.to_nat NumBytesFullCapSz) ;
            Return (ToBit #dataBytes)
          ) ;
        LetA rawTag : Bool <-
          liftAction np_mem (
            RegRead tagsVal <- "mem.tags" in memTree ;
            Let rawTag : Bool <- ReadArray #tagsVal #tagOffset ;
            Return #rawTag
          ) ;
        Let rawDataLsb : Addr          <- TruncLsb Xlen Xlen #rawBits ;
        Let rawCap     : Cap           <- FromBit Cap (TruncMsb Xlen Xlen #rawBits) ;

        If #isCap Then (
          LetL ldECap : ECap <- DecodeCap rawCap rawDataLsb ;
          LetIf finalTag : Bool <-
            If #rawTag Then (
              LetA revBit : Bool <- liftAction np_mem (readRevBit (##ldECap`"base")) ;
              Return (Not #revBit)
            ) Else (
              Return (ConstBool false)
            ) ;
          Let dstVal : FullECapWithTag <- STRUCT {
            "tag"  ::= #finalTag ;
            "ecap" ::= #ldECap ;
            "addr" ::= #rawDataLsb
          } ;
          If (isNotZero #dstIdx) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #dstVal)
          ) ;
          Retv
        ) Else (
          Let rawBytes   : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
            FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #rawDataLsb ;
          Let memSzBytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 #memSize ;
          Let readBits   : Bit Xlen <- ToBit (
            ITE #isUnsigned
                (ArrayZeroExtend #memSzBytes #rawBytes)
                (ArraySignExtend #memSzBytes #rawBytes)
          ) ;
          Let dstVal : FullECapWithTag <- STRUCT {
            "tag"  ::= Const ty Bool false ;
            "ecap" ::= Const ty ECap (getDefault _) ;
            "addr" ::= #readBits
          } ;
          If (isNotZero #dstIdx) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #dstVal)
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * 3. specExecuteDeferred (Executing Option DeferredReq)
   * ========================================================================= *)
  Definition specExecuteDeferred (reqOpt : ty (Option DeferredReq)) : Action ty tree (Bit 0) :=
    If (##reqOpt `? "Some") Then (
      Let req : DeferredReq <- ##reqOpt `! "Some" ;
      specExecuteDeferredReq req
    ) ;
    Retv.

End SpecFetchMemory.
