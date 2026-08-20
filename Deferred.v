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

From Stdlib Require Import String List ZArith.
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines FunctionalUnits SpecMemory Alu.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section DeferredStages.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation tree := (coreTree memTree).

  Definition np_rf : NodePath tree :=
    getNodePath tree "core.rf".

  Definition np_mem : NodePath tree :=
    embedNodeIntoPath (getNodePath tree "core.mem") singletonChildPath.

    (* =========================================================================
     * STAGE 1: loadRqOrStoreOrFence
     *
     * - Requires: inputBuffer is valid (not empty).
     *
     * - Case 1: Memory Operation ("Mem")
     *     - If Store:
     *         * Action: If integer store (32-bit), rotate left LSB 32 bits
     *                   (when mem_needsRotation is true).
     *                   stTag is simply (isCap && tag).
     *                   Issue mem_writeBytes and mem_writeTag.
     *                   Dequeue inputBuffer (set to None).
     *     - If Load:
     *         * Requires: outputBuffer is NOT full (outputBuffer is None).
     *         * Action:   Issue mem_readBytesRq and mem_readTagRq.
     *                     Enq outputBuffer <- Some (PendingLoad { dstIdx, byteOffset, memSize, isUnsigned }).
     *                     Dequeue inputBuffer (set to None).
     *
     * - Case 2: Fence Operation ("Fence")
     *     - Requires: !isRW OR (all downstream buffers are empty).
     *     - Action:   Dequeue inputBuffer (set to None).
     * ========================================================================= *)
    Definition loadRqOrStoreOrFence : Action ty tree (Bit 0) :=
      RegRead inputBuffer  <- "core.deferred.inputBuf" in tree ;
      RegRead outputBuffer <- "core.deferred.loadBuf"  in tree ;
      RegRead revBuffer    <- "core.deferred.revBuf"   in tree ;

      Let inputBuffer_isValid  : Bool <- #inputBuffer `? "Some" ;
      Let outputBuffer_isFull  : Bool <- #outputBuffer `? "Some" ;
      Let outputBuffer_isEmpty : Bool <- Not #outputBuffer_isFull ;
      Let rev_isEmpty          : Bool <- Not (#revBuffer `? "Some") ;

      If #inputBuffer_isValid Then (
        Let req    : DeferredReq   <- #inputBuffer `! "Some" ;
        Let dstIdx : Bit RegIdxSz  <- ##req`"dstIdx" ;
        Let addr   : Addr          <- ##req`"addr" ;
        Let op     : DeferredUnion <- ##req`"op" ;

        If (##op `? "Mem") Then (
          Let memPayload : MemPayload                <- ##op `! "Mem" ;
          Let memSize    : Bit LgLgNumBytesFullCapSz <- ##memPayload`"memSize" ;
          Let memOp      : LoadOrStoreKind           <- ##memPayload`"memOp" ;
          Let tagAddr    : Bit TagAddrWidth          <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #addr ;
          Let byteOffset : Bit LgNumBytesFullCapSz   <- TruncLsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #addr ;

          If (##memOp `? "Store") Then (
            (* --- STORE ACTION --- *)
            Let stCapVal   : FullCapWithTag <- ##memOp `! "Store" ;
            Let tag        : Bool           <- ##stCapVal`"tag" ;
            Let cap        : Cap            <- ##stCapVal`"cap" ;
            Let data       : Addr           <- ##stCapVal`"addr" ;
            Let isCap      : Bool           <- Eq #memSize $LgNumBytesFullCapSz ;
            Let stBytesInt : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
              FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #data ;
            Let stBytesRot : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
              if (memIfc ty).(mem_needsRotation)
              then ArrayRotl 8 #stBytesInt #byteOffset
              else #stBytesInt ;
            Let stDataCap  : Bit FullCapSz  <- {< ToBit #cap, #data >} ;
            Let stDataInt  : Bit FullCapSz  <- ZeroExtendTo FullCapSz (ToBit #stBytesRot) ;
            Let stData     : Bit FullCapSz  <- ITE #isCap #stDataCap #stDataInt ;
            Let stTag      : Bool           <- And [ #isCap ; #tag ] ;
            Act (liftAction np_mem ((memIfc ty).(mem_writeBytes) #addr #stData #memSize)) ;
            Act (liftAction np_mem ((memIfc ty).(mem_writeTag) #tagAddr #stTag)) ;
            RegWrite "core.deferred.inputBuf" in tree <- mkNone ty ;
            Retv
          ) Else (
            (* --- LOAD ACTION: requires outputBuffer is NOT full --- *)
            If (Not #outputBuffer_isFull) Then (
              Let ldOpVal    : LoadOp <- ##memOp `! "Load" ;
              Let isUnsigned : Bool   <- ##ldOpVal`"isUnsigned" ;
              Act (liftAction np_mem ((memIfc ty).(mem_readBytesRq) #addr)) ;
              Act (liftAction np_mem ((memIfc ty).(mem_readTagRq) #tagAddr)) ;
              Let pending : PendingLoad <- STRUCT {
                "dstIdx"     ::= #dstIdx ;
                "byteOffset" ::= #byteOffset ;
                "memSize"    ::= #memSize ;
                "isUnsigned" ::= #isUnsigned
              } ;
              RegWrite "core.deferred.loadBuf"  in tree <- mkSome #pending ;
              RegWrite "core.deferred.inputBuf" in tree <- mkNone ty ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          (* --- FENCE ACTION: !isRW OR (all downstream buffers empty) --- *)
          Let fenceOp : FenceOp <- ##op `! "Fence" ;
          Let isRW    : Bool    <- ##fenceOp`"RW" ;
          Let canPass : Bool    <- Or [ Not #isRW ; And [ #outputBuffer_isEmpty ; #rev_isEmpty ] ] ;
          If #canPass Then (
            RegWrite "core.deferred.inputBuf" in tree <- mkNone ty ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    (* =========================================================================
     * STAGE 2: loadRpAndWritebackOrRevRq
     *
     * - Requires: inputBuffer is valid (not empty) AND
     *             memory load response is valid (readBytesRp AND readTagRp are Some).
     *
     * - Case 1: Tagged Capability Load (memSize == NumBytesFullCapSz AND rawTag == true)
     *     - Requires: outputBuffer is NOT full (outputBuffer is None).
     *     - Action:   NO rotation. Decode capability (DecodeCap).
     *                 Issue mem_readRevBitRq on ldECap.base.
     *                 Enq outputBuffer <- Some (PendingRev { dstIdx, capVal: { tag: rawTag, ecap: ldECap, addr: ldAddr } }).
     *                 Dequeue inputBuffer (set to None).
     *
     * - Case 2: Untagged Full-Cap OR Sub-Word Load
     *     - Action:   Rotate LSB 32 bits right by byteOffset (when mem_needsRotation is true).
     *                 Sign/Zero extend sub-word data.
     *                 Writeback result directly to Register File.
     *                 Dequeue inputBuffer (set to None).
     * ========================================================================= *)
    Definition loadRpAndWritebackOrRevRq : Action ty tree (Bit 0) :=
      RegRead inputBuffer  <- "core.deferred.loadBuf" in tree ;
      RegRead outputBuffer <- "core.deferred.revBuf"  in tree ;

      Let inputBuffer_isValid  : Bool <- #inputBuffer `? "Some" ;
      Let outputBuffer_isFull  : Bool <- #outputBuffer `? "Some" ;
      Let outputBuffer_isEmpty : Bool <- Not #outputBuffer_isFull ;

      If #inputBuffer_isValid Then (
        LetA rawBytesOpt : Option (Bit FullCapSz) <- liftAction np_mem ((memIfc ty).(mem_readBytesRp)) ;
        LetA tagOpt      : Option Bool            <- liftAction np_mem ((memIfc ty).(mem_readTagRp)) ;
        Let memRp_isValid : Bool                  <- And [ ##rawBytesOpt `? "Some" ; ##tagOpt `? "Some" ] ;

        If #memRp_isValid Then (
          Let pl         : PendingLoad               <- ##inputBuffer `! "Some" ;
          Let rawData    : Bit FullCapSz             <- ##rawBytesOpt `! "Some" ;
          Let rawTag     : Bool                      <- ##tagOpt `! "Some" ;
          Let dstIdx     : Bit RegIdxSz              <- ##pl`"dstIdx" ;
          Let byteOffset : Bit LgNumBytesFullCapSz   <- ##pl`"byteOffset" ;
          Let memSize    : Bit LgLgNumBytesFullCapSz <- ##pl`"memSize" ;
          Let isUnsigned : Bool                      <- ##pl`"isUnsigned" ;

          Let isCap       : Bool <- Eq #memSize $LgNumBytesFullCapSz ;
          Let isTaggedCap : Bool <- And [ #isCap ; #rawTag ] ;

          If #isTaggedCap Then (
            (* --- 1. TAGGED CAPABILITY LOAD: requires outputBuffer is NOT full --- *)
            If (Not #outputBuffer_isFull) Then (
              Let ldAddr  : Addr <- TruncLsb Xlen Xlen #rawData ;
              Let ldCap   : Cap  <- FromBit Cap (TruncMsb Xlen Xlen #rawData) ;
              LetL ldECap : ECap <- DecodeCap ldCap ldAddr ;
              Let  base   : Bit (AddrSz + 1) <- ##ldECap`"base" ;
              Act (liftAction np_mem ((memIfc ty).(mem_readRevBitRq) #base)) ;
              Let capVal  : FullECapWithTag <- STRUCT {
                "tag"  ::= #rawTag ;
                "ecap" ::= #ldECap ;
                "addr" ::= #ldAddr
              } ;
              Let pr : PendingRev <- STRUCT {
                "dstIdx" ::= #dstIdx ;
                "capVal" ::= #capVal
              } ;
              RegWrite "core.deferred.revBuf"  in tree <- mkSome #pr ;
              RegWrite "core.deferred.loadBuf" in tree <- mkNone ty ;
              Retv
            ) ;
            Retv
          ) Else (
            (* --- 2. UNTAGGED FULL-CAP OR SUB-WORD LOAD: ROTATE LSB 32 BITS --- *)
            Let rawDataLsb : Bit Xlen                            <- TruncLsb Xlen Xlen #rawData ;
            Let rawBytes   : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
              FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #rawDataLsb ;
            Let rotBytes   : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
              if (memIfc ty).(mem_needsRotation)
              then ArrayRotr 8 #rawBytes #byteOffset
              else #rawBytes ;
            Let memSzBytes : Bit (LgNumBytesFullCapSz + 1)       <- Sll $1 #memSize ;
            Let readBits   : Bit Xlen <- ToBit (
              ITE #isUnsigned
                  (ArrayZeroExtend #memSzBytes #rotBytes)
                  (ArraySignExtend #memSzBytes #rotBytes)
            ) ;
            Let dstVal : FullECapWithTag <- STRUCT {
              "tag"  ::= Const ty Bool false ;
              "ecap" ::= Const ty ECap (getDefault _) ;
              "addr" ::= #readBits
            } ;
            If (isNotZero #dstIdx) Then (
              liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #dstVal)
            ) ;
            RegWrite "core.deferred.loadBuf" in tree <- mkNone ty ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    (* =========================================================================
     * STAGE 3: revRpAndWriteBack
     *
     * - Requires: inputBuffer is valid (not empty) AND
     *             revocation bit response is valid (readRevBitRp is Some).
     * - Action:   Compute finalTag = capVal.tag and not readRevBitRp.Some.
     *             Writeback capability with finalTag directly to Register File.
     *             Dequeue inputBuffer (set to None).
     * ========================================================================= *)
    Definition revRpAndWriteBack : Action ty tree (Bit 0) :=
      RegRead inputBuffer <- "core.deferred.revBuf" in tree ;

      Let inputBuffer_isValid : Bool <- #inputBuffer `? "Some" ;

      If #inputBuffer_isValid Then (
        LetA revBitOpt : Option Bool <- liftAction np_mem ((memIfc ty).(mem_readRevBitRp)) ;
        Let memRp_isValid : Bool     <- ##revBitOpt `? "Some" ;

        If #memRp_isValid Then (
          Let pr       : PendingRev      <- ##inputBuffer `! "Some" ;
          Let revBit   : Bool            <- ##revBitOpt `! "Some" ;
          Let dstIdx   : Bit RegIdxSz    <- ##pr`"dstIdx" ;
          Let capVal   : FullECapWithTag <- ##pr`"capVal" ;
          Let currTag  : Bool            <- ##capVal`"tag" ;
          Let finalTag : Bool            <- And [ Not #revBit ; #currTag ] ;
          Let finalVal : FullECapWithTag <- #capVal `{ "tag" <- #finalTag } ;
          If (isNotZero #dstIdx) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #finalVal)
          ) ;
          RegWrite "core.deferred.revBuf" in tree <- mkNone ty ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

End DeferredStages.
