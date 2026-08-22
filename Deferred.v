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
From Cheriot Require Import SpecDefines FunctionalUnits Memory Alu Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section DeferredStages.
  Variable fetchCapacity deferredCapacity : nat.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable ty : Kind -> Type.

  Local Notation memTree := (memIfc ty).(memTree).
  Local Notation tree := (coreTree memTree fetchCapacity deferredCapacity).
  Local Notation capacity := deferredCapacity.

  Definition np_rf : NodePath tree :=
    getNodePath tree "core.rf".

  Definition np_mem : NodePath tree :=
    embedNodeIntoPath (getNodePath tree "core.mem") singletonChildPath.

  Definition np_inputFifo : NodePath tree :=
    getNodePath tree "core.deferred.inputBuf.fifo".

  Definition np_loadFifo : NodePath tree :=
    getNodePath tree "core.deferred.loadBuf.fifo".

  Definition np_revFifo : NodePath tree :=
    getNodePath tree "core.deferred.revBuf.fifo".

    (* =========================================================================
     * STAGE 1: loadRqOrStoreOrFence
     *
     * - Requires: inputFifo is valid (not empty).
     *
     * - Case 1: Memory Operation ("Mem")
     *     - If Store:
     *         * Action: If integer store (32-bit), rotate left LSB 32 bits
     *                   (when mem_needsRotation is true).
     *                   stTag is simply (isCap && tag).
     *                   Issue mem_writeBytes and mem_writeTag.
     *                   Dequeue inputFifo.
     *     - If Load:
     *         * Requires: loadFifo is NOT full.
     *         * Action:   Issue mem_readBytesRq and mem_readTagRq.
     *                     Enq loadFifo <- PendingLoad { dstIdx, byteOffset, memSize, isUnsigned }.
     *                     Dequeue inputFifo.
     *
     * - Case 2: Fence Operation ("Fence")
     *     - Requires: !isRW OR (all downstream FIFOs are empty).
     *     - Action:   Dequeue inputFifo.
     * ========================================================================= *)
    Definition loadRqOrStoreOrFence : Action ty tree (Bit 0) :=
      LetA inputHead            : Option DeferredReq <- liftAction np_inputFifo (@first capacity DeferredReq ty) ;
      LetA outputBuffer_isFull  : Bool               <- liftAction np_loadFifo (@isFull capacity PendingLoad ty) ;
      LetA outputBuffer_isEmpty : Bool               <- liftAction np_loadFifo (@isEmpty capacity PendingLoad ty) ;
      LetA rev_isEmpty          : Bool               <- liftAction np_revFifo (@isEmpty capacity PendingRev ty) ;

      Let inputBuffer_isValid   : Bool               <- #inputHead `? "Some" ;

      (* This condition is always true in a spec *)
      If #inputBuffer_isValid Then (
        Let req    : DeferredReq   <- #inputHead `! "Some" ;
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
            (* --- STORE ACTION: requires canStoreMemRq --- *)
            LetA canStore : Bool <- liftAction np_mem ((memIfc ty).(mem_canStoreMemRq)) ;
            (* This condition is always true in a spec *)
            If #canStore Then (
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
              Let stAddr     : Addr           <- ITE #isCap #data (ToBit #stBytesRot) ;
              Let stTag      : Bool           <- And [ #isCap ; #tag ] ;
              Let stVal      : FullCapWithTag <- STRUCT {
                "tag"  ::= #stTag ;
                "cap"  ::= #cap ;
                "addr" ::= #stAddr
              } ;
              Act (liftAction np_mem ((memIfc ty).(mem_writeMem) #addr #stVal #memSize)) ;
              liftAction np_inputFifo (@deq capacity DeferredReq ty)
            ) ;
            Retv
          ) Else (
            (* --- LOAD ACTION: requires canLoadMemRq AND loadFifo is NOT full --- *)
            LetA canLoad : Bool <- liftAction np_mem ((memIfc ty).(mem_canLoadMemRq)) ;
            (* This condition is always true in a spec *)
            If (And [ #canLoad ; Not #outputBuffer_isFull ]) Then (
              Let ldOpVal    : LoadOp <- ##memOp `! "Load" ;
              Let isUnsigned : Bool   <- ##ldOpVal`"isUnsigned" ;
              Act (liftAction np_mem ((memIfc ty).(mem_readMemRq) #addr)) ;
              Let pending : PendingLoad <- STRUCT {
                "dstIdx"     ::= #dstIdx ;
                "byteOffset" ::= #byteOffset ;
                "memSize"    ::= #memSize ;
                "isUnsigned" ::= #isUnsigned
              } ;
              Act (liftAction np_loadFifo (@enq capacity PendingLoad ty pending)) ;
              liftAction np_inputFifo (@deq capacity DeferredReq ty)
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          (* --- FENCE ACTION: canFenceMemRq AND (!fenceNeedsEmpty OR all downstream FIFOs empty) --- *)
          Let fenceOp         : FenceOp <- ##op `! "Fence" ;
          Let fenceNeedsEmpty : Bool    <- Or [ ##fenceOp`"RW" ; ##fenceOp`"RR" ] ;
          LetA canFence       : Bool    <- liftAction np_mem ((memIfc ty).(mem_canFenceMemRq)) ;
          (* This condition is always true in a spec *)
          If (And [ #canFence ; Or [ Not #fenceNeedsEmpty ; And [ #outputBuffer_isEmpty ; #rev_isEmpty ] ] ]) Then (
            Act (liftAction np_mem ((memIfc ty).(mem_fence_req) #fenceOp)) ;
            liftAction np_inputFifo (@deq capacity DeferredReq ty)
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    (* =========================================================================
     * STAGE 2: loadRpAndWritebackOrRevRq
     *
     * - Requires: loadFifo is valid (not empty) AND
     *             memory load response is valid (isMemRpValid).
     *
     * - Case 1: Tagged Capability Load (memSize == NumBytesFullCapSz AND rawTag == true)
     *     - Requires: canReadRevBit AND revFifo is NOT full.
     *     - Action:   NO rotation. Decode capability (DecodeCap).
     *                 Issue mem_readRevBitRq on ldECap.base.
     *                 Enq revFifo <- PendingRev { dstIdx, capVal: { tag: rawTag, ecap: ldECap, addr: rawDataLsb } }.
     *                 Dequeue loadFifo.
     *
     * - Case 2: Untagged Full-Cap OR Sub-Word Load
     *     - Action:   Rotate LSB 32 bits right by byteOffset (when mem_needsRotation is true).
     *                 Sign/Zero extend sub-word data.
     *                 Writeback result directly to Register File.
     *                 Dequeue loadFifo.
     * ========================================================================= *)
    Definition loadRpAndWritebackOrRevRq : Action ty tree (Bit 0) :=
      LetA inputHead           : Option PendingLoad <- liftAction np_loadFifo (@first capacity PendingLoad ty) ;
      LetA outputBuffer_isFull : Bool               <- liftAction np_revFifo (@isFull capacity PendingRev ty) ;

      Let inputBuffer_isValid  : Bool               <- #inputHead `? "Some" ;

      (* This condition is always true in a spec *)
      If #inputBuffer_isValid Then (
        LetA isMemRpValid : Bool <- liftAction np_mem ((memIfc ty).(mem_isMemRpValid)) ;

        (* This condition is always true in a spec *)
        If #isMemRpValid Then (
          Let pl         : PendingLoad               <- #inputHead `! "Some" ;
          Let dstIdx     : Bit RegIdxSz              <- ##pl`"dstIdx" ;
          Let byteOffset : Bit LgNumBytesFullCapSz   <- ##pl`"byteOffset" ;
          Let memSize    : Bit LgLgNumBytesFullCapSz <- ##pl`"memSize" ;
          Let isUnsigned : Bool                      <- ##pl`"isUnsigned" ;

          Let isCap : Bool <- Eq #memSize $LgNumBytesFullCapSz ;

          LetA memVal     : FullCapWithTag <- liftAction np_mem ((memIfc ty).(mem_getMemRp)) ;
          Let rawTag     : Bool           <- ##memVal`"tag" ;
          Let rawCap     : Cap            <- ##memVal`"cap" ;
          Let rawDataLsb : Addr           <- ##memVal`"addr" ;
          Let isTaggedCap : Bool          <- And [ #isCap ; #rawTag ] ;

          If #isTaggedCap Then (
            (* --- 1. TAGGED CAPABILITY LOAD --- *)
            LetA canReadRev : Bool <- liftAction np_mem ((memIfc ty).(mem_canReadRevBitRq)) ;

            (* This condition is always true in a spec *)
            If (And [ #canReadRev ; Not #outputBuffer_isFull ]) Then (
              LetL ldECap : ECap <- DecodeCap rawCap rawDataLsb ;
              Let  base   : Bit (AddrSz + 1) <- ##ldECap`"base" ;
              Act (liftAction np_mem ((memIfc ty).(mem_readRevBitRq) #base)) ;
              Let capVal  : FullECapWithTag <- STRUCT {
                "tag"  ::= #rawTag ;
                "ecap" ::= #ldECap ;
                "addr" ::= #rawDataLsb
              } ;
              Let pr : PendingRev <- STRUCT {
                "dstIdx" ::= #dstIdx ;
                "capVal" ::= #capVal
              } ;
              Act (liftAction np_revFifo (@enq capacity PendingRev ty pr)) ;
              liftAction np_loadFifo (@deq capacity PendingLoad ty)
            ) ;
            Retv
          ) Else (
            (* --- 2. UNTAGGED FULL-CAP OR SUB-WORD LOAD: ROTATE LSB 32 BITS --- *)
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
            liftAction np_loadFifo (@deq capacity PendingLoad ty)
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    (* =========================================================================
     * STAGE 3: revRpAndWriteBack
     *
     * - Requires: revFifo is valid (not empty) AND
     *             revocation bit response is valid (isRevBitRpValid).
     * - Action:   Compute finalTag = capVal.tag and not getRevBitRp.
     *             Writeback capability with finalTag directly to Register File.
     *             Dequeue revFifo.
     * ========================================================================= *)
    Definition revRpAndWriteBack : Action ty tree (Bit 0) :=
      LetA inputHead          : Option PendingRev <- liftAction np_revFifo (@first capacity PendingRev ty) ;
      Let inputBuffer_isValid : Bool              <- #inputHead `? "Some" ;

      (* This condition is always true in a spec *)
      If #inputBuffer_isValid Then (
        LetA isRevRpValid : Bool <- liftAction np_mem ((memIfc ty).(mem_isRevBitRpValid)) ;

        (* This condition is always true in a spec *)
        If #isRevRpValid Then (
          Let  pr       : PendingRev      <- #inputHead `! "Some" ;
          LetA revBit   : Bool            <- liftAction np_mem ((memIfc ty).(mem_getRevBitRp)) ;
          Let  dstIdx   : Bit RegIdxSz    <- ##pr`"dstIdx" ;
          Let  capVal   : FullECapWithTag <- ##pr`"capVal" ;
          Let  currTag  : Bool            <- ##capVal`"tag" ;
          Let  finalTag : Bool            <- And [ Not #revBit ; #currTag ] ;
          Let  dstVal   : FullECapWithTag <- STRUCT {
            "tag"  ::= #finalTag ;
            "ecap" ::= ##capVal`"ecap" ;
            "addr" ::= ##capVal`"addr"
          } ;
          If (isNotZero #dstIdx) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind #dstIdx #dstVal)
          ) ;
          liftAction np_revFifo (@deq capacity PendingRev ty)
        ) ;
        Retv
      ) ;
      Retv.
End DeferredStages.
