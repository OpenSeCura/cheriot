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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Dispatched Action Types for Deferred Execution
 * =========================================================================== *)

Definition StoreCmd := STRUCT_TYPE {
  "addr"    :: Addr ;
  "stVal"   :: FullCapWithTag ;
  "memSize" :: Bit LgLgNumBytesFullCapSz
}.

Definition LoadCmd := STRUCT_TYPE {
  "addr"    :: Addr ;
  "pending" :: PendingLoad
}.

Definition MemActionType := [
  ("Store"%string, StoreCmd) ;
  ("Load"%string,  LoadCmd)
].
Definition MemAction := TaggedUnion MemActionType.

Definition FenceCmd := STRUCT_TYPE {
  "fenceOp"    :: FenceOp ;
  "needsEmpty" :: Bool
}.

Definition DeferredActionType := [
  ("Mem"%string,   MemAction) ;
  ("Fence"%string, FenceCmd)
].
Definition DeferredAction := TaggedUnion DeferredActionType.

Definition RevCmd := STRUCT_TYPE {
  "base"       :: Bit (AddrSz + 1) ;
  "pendingRev" :: PendingRev
}.

Definition WbCmd := STRUCT_TYPE {
  "dstIdx" :: Bit RegIdxSz ;
  "dstVal" :: FullECapWithTag
}.

Definition LoadOutcomeType := [
  ("RevLookup"%string, RevCmd) ;
  ("Writeback"%string, WbCmd)
].
Definition LoadOutcome := TaggedUnion LoadOutcomeType.

(* ===========================================================================
 * Pure Combinational Helpers & Dispatchers
 * =========================================================================== *)

Section CombinationalDeferred.
  Variable ty : Kind -> Type.

  Definition formatStorePayload (stVal : ty FullCapWithTag)
                                (byteOffset : ty (Bit LgNumBytesFullCapSz))
                                (isCap : ty Bool)
                                (needsRotation : bool) : LetExpr ty FullCapWithTag :=
    LetE tag        : Bool           <- ##stVal`"tag" ;
    LetE cap        : Cap            <- ##stVal`"cap" ;
    LetE data       : Data           <- ##stVal`"addr" ;
    LetE stBytesInt : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
      FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #data ;
    LetE stBytesRot : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
      if needsRotation then ArrayRotl 8 #stBytesInt #byteOffset else #stBytesInt ;
    LetE stAddr     : Addr           <- ITE #isCap #data (ToBit #stBytesRot) ;
    LetE stTag      : Bool           <- And [ #isCap ; #tag ] ;
    @RetE _ FullCapWithTag (STRUCT {
      "tag"  ::= #stTag ;
      "cap"  ::= #cap ;
      "addr" ::= #stAddr
    }).

  Definition decodeAndAttenuateCap (rawCap : ty Cap) (rawDataLsb : ty Addr)
                                  (rawTag isLM isLG : ty Bool) : LetExpr ty ECap :=
    LETE ldECapRaw   : ECap     <- DecodeCap rawCap rawDataLsb ;
    LetE isCapSealed : Bool     <- isSealed ldECapRaw ;
    LetE rawPerms    : CapPerms <- ##ldECapRaw`"perms" ;
    LetE newPerms    : CapPerms <- ITE #rawTag (attenuatePerms rawPerms isCapSealed isLM isLG) #rawPerms ;
    @RetE _ ECap (STRUCT {
      "R"     ::= ##ldECapRaw`"R" ;
      "perms" ::= #newPerms ;
      "oType" ::= ##ldECapRaw`"oType" ;
      "cE"    ::= ##ldECapRaw`"cE" ;
      "top"   ::= ##ldECapRaw`"top" ;
      "base"  ::= ##ldECapRaw`"base"
    }).

  Definition needsRevocationCheck (ecap : ty ECap) (rawTag : ty Bool) : LetExpr ty Bool :=
    LetE isSealing : Bool <- isSealingCap ecap ;
    @RetE _ Bool (And [ #rawTag ; Not #isSealing ]).

  Definition decodeSubwordData (rawDataLsb : ty Addr)
                               (byteOffset : ty (Bit LgNumBytesFullCapSz))
                               (memSize : ty (Bit LgLgNumBytesFullCapSz))
                               (isUnsigned : ty Bool)
                               (needsRotation : bool) : LetExpr ty (Bit Xlen) :=
    LetE rawBytes   : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
      FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #rawDataLsb ;
    LetE rotBytes   : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
      if needsRotation then ArrayRotr 8 #rawBytes #byteOffset else #rawBytes ;
    LetE memSzBytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 #memSize ;
    @RetE _ (Bit Xlen) (ToBit (
      ITE #isUnsigned
          (ArrayZeroExtend #memSzBytes #rotBytes)
          (ArraySignExtend #memSzBytes #rotBytes)
    )).

  Definition dispatchDeferredReq (req : ty DeferredReq) (needsRotation : bool) : LetExpr ty DeferredAction :=
    LetE dstIdx     : Bit RegIdxSz             <- ##req`"dstIdx" ;
    LetE addr       : Addr                     <- ##req`"addr" ;
    LetE byteOffset : Bit LgNumBytesFullCapSz  <- TruncLsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #addr ;
    LetE op         : DeferredUnion            <- ##req`"op" ;
    LetIfE action : DeferredAction <-
      IfE (##op `? "Mem") ThenE (
        LetE memPayload : MemPayload                <- ##op `! "Mem" ;
        LetE memSize    : Bit LgLgNumBytesFullCapSz <- ##memPayload`"memSize" ;
        LetE memOp      : LoadOrStoreKind           <- ##memPayload`"memOp" ;
        LetE isCap      : Bool                      <- Eq #memSize $LgNumBytesFullCapSz ;
        LetIfE memAct : MemAction <-
          IfE (##memOp `? "Store") ThenE (
            LetE stCapVal : FullCapWithTag <- ##memOp `! "Store" ;
            LETE stVal    : FullCapWithTag <- formatStorePayload stCapVal byteOffset isCap needsRotation ;
            LetE stCmd    : StoreCmd       <- STRUCT {
              "addr"    ::= #addr ;
              "stVal"   ::= #stVal ;
              "memSize" ::= #memSize
            } ;
            @RetE _ MemAction (UNION (MemActionType, "Store" ::= #stCmd))
          ) ElseE (
            LetE ldOpVal : LoadOp <- ##memOp `! "Load" ;
            LetE pending : PendingLoad <- STRUCT {
              "dstIdx"     ::= #dstIdx ;
              "byteOffset" ::= #byteOffset ;
              "memSize"    ::= #memSize ;
              "isUnsigned" ::= ##ldOpVal`"isUnsigned" ;
              "isLM"       ::= ##ldOpVal`"isLM" ;
              "isLG"       ::= ##ldOpVal`"isLG"
            } ;
            LetE ldCmd : LoadCmd <- STRUCT {
              "addr"    ::= #addr ;
              "pending" ::= #pending
            } ;
            @RetE _ MemAction (UNION (MemActionType, "Load" ::= #ldCmd))
          ) ;
        @RetE _ DeferredAction (UNION (DeferredActionType, "Mem" ::= #memAct))
      ) ElseE (
        LetE fenceVal        : FenceOp  <- ##op `! "Fence" ;
        LetE fenceNeedsEmpty : Bool     <- Or [ ##fenceVal`"RW" ; ##fenceVal`"WW" ] ;
        LetE fenceCmd        : FenceCmd <- STRUCT {
          "fenceOp"    ::= #fenceVal ;
          "needsEmpty" ::= #fenceNeedsEmpty
        } ;
        @RetE _ DeferredAction (UNION (DeferredActionType, "Fence" ::= #fenceCmd))
      ) ;
    @RetE _ DeferredAction #action.

  Definition dispatchLoadResponse (pl : ty PendingLoad) (memVal : ty FullCapWithTag) (needsRotation : bool) : LetExpr ty LoadOutcome :=
    LetE dstIdx     : Bit RegIdxSz              <- ##pl`"dstIdx" ;
    LetE byteOffset : Bit LgNumBytesFullCapSz   <- ##pl`"byteOffset" ;
    LetE memSize    : Bit LgLgNumBytesFullCapSz <- ##pl`"memSize" ;
    LetE isUnsigned : Bool                      <- ##pl`"isUnsigned" ;
    LetE isLM       : Bool                      <- ##pl`"isLM" ;
    LetE isLG       : Bool                      <- ##pl`"isLG" ;
    LetE isCap      : Bool                      <- Eq #memSize $LgNumBytesFullCapSz ;

    LetE rawTag     : Bool                      <- ##memVal`"tag" ;
    LetE rawCap     : Cap                       <- ##memVal`"cap" ;
    LetE rawDataLsb : Addr                      <- ##memVal`"addr" ;

    LetIfE outcome : LoadOutcome <-
      IfE #isCap ThenE (
        LETE ldECap        : ECap <- decodeAndAttenuateCap rawCap rawDataLsb rawTag isLM isLG ;
        LETE needsRevCheck : Bool <- needsRevocationCheck ldECap rawTag ;
        LetIfE outcomeCap : LoadOutcome <-
          IfE #needsRevCheck ThenE (
            LetE capVal : FullECapWithTag <- STRUCT {
              "tag"  ::= #rawTag ;
              "ecap" ::= #ldECap ;
              "addr" ::= #rawDataLsb
            } ;
            LetE pr : PendingRev <- STRUCT {
              "dstIdx" ::= #dstIdx ;
              "capVal" ::= #capVal
            } ;
            LetE revCmd : RevCmd <- STRUCT {
              "base"       ::= ##ldECap`"base" ;
              "pendingRev" ::= #pr
            } ;
            @RetE _ LoadOutcome (UNION (LoadOutcomeType, "RevLookup" ::= #revCmd))
          ) ElseE (
            LetE dstVal : FullECapWithTag <- STRUCT {
              "tag"  ::= #rawTag ;
              "ecap" ::= #ldECap ;
              "addr" ::= #rawDataLsb
            } ;
            LetE wbCmd : WbCmd <- STRUCT {
              "dstIdx" ::= #dstIdx ;
              "dstVal" ::= #dstVal
            } ;
            @RetE _ LoadOutcome (UNION (LoadOutcomeType, "Writeback" ::= #wbCmd))
          ) ;
        @RetE _ LoadOutcome #outcomeCap
      ) ElseE (
        LETE readBits : Bit Xlen <- decodeSubwordData rawDataLsb byteOffset memSize isUnsigned needsRotation ;
        LetE dstVal   : FullECapWithTag <- STRUCT {
          "tag"  ::= Const ty Bool false ;
          "ecap" ::= Const ty ECap (getDefault _) ;
          "addr" ::= #readBits
        } ;
        LetE wbCmd : WbCmd <- STRUCT {
          "dstIdx" ::= #dstIdx ;
          "dstVal" ::= #dstVal
        } ;
        @RetE _ LoadOutcome (UNION (LoadOutcomeType, "Writeback" ::= #wbCmd))
      ) ;
    @RetE _ LoadOutcome #outcome.

  Definition dispatchRevResponse (pr : ty PendingRev) (revBit : ty Bool) : LetExpr ty WbCmd :=
    LetE dstIdx   : Bit RegIdxSz     <- ##pr`"dstIdx" ;
    LetE capVal   : FullECapWithTag  <- ##pr`"capVal" ;
    LetE currTag  : Bool             <- ##capVal`"tag" ;
    LetE finalTag : Bool             <- And [ Not #revBit ; #currTag ] ;
    LetE dstVal   : FullECapWithTag  <- STRUCT {
      "tag"  ::= #finalTag ;
      "ecap" ::= ##capVal`"ecap" ;
      "addr" ::= ##capVal`"addr"
    } ;
    @RetE _ WbCmd (STRUCT {
      "dstIdx" ::= #dstIdx ;
      "dstVal" ::= #dstVal
    }).

End CombinationalDeferred.

(* ===========================================================================
 * Spec Memory Execution Transition Section
 * =========================================================================== *)

Definition specCoreTree (regions : list MemRegion) : Tree Elem :=
  Node "core" [
    rfTree ;
    specMemTree regions
  ].

Section SpecFetchMemory.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).
  Local Notation coreTree := (specCoreTree regions).

  Definition np_rf : NodePath coreTree :=
    getNodePath coreTree "core.rf".

  Definition np_mem : NodePath coreTree :=
    getNodePath coreTree "core.mem".

  Local Notation computeRevBitAddr := (computeRevBitAddr config).

  Local Notation readRevBit := (readRevBit config regions).

  (* =========================================================================
   * 1. specFetch (Atomic Combinational Fetch)
   * ========================================================================= *)
  Definition specFetch : Action ty coreTree FetchOut :=
    LetA pcc : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
    LetA rawFull : FullCapWithTag <- liftAction np_mem (specMemRead regions (##pcc`"addr") $LgNumBytesInstSz) ;
    Let rawInst : Inst <- ##rawFull`"addr" ;

    (* Fetch Exception Checks *)
    Let pccECap      : ECap <- ##pcc`"ecap" ;
    Let isComp       : Bool <- isCompressed rawInst ;
    Let instBytesLen : Addr <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
    Let tagExc       : Bool <- Not ##pcc`"tag" ;
    Let sealExc      : Bool <- isSealed pccECap ;
    Let permExc      : Bool <- Not (##pccECap`"perms"`"EX") ;
    Let boundsExc    : Bool <- Or [
      Slt (ZeroExtendTo (AddrSz + 2) ##pcc`"addr") (ZeroExtendTo (AddrSz + 2) ##pccECap`"base") ;
      Sgt (ZeroExtendTo (AddrSz + 2) (Add [ ##pcc`"addr" ; #instBytesLen ])) (##pccECap`"top")
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
  Definition specExecuteDeferredReq (req : ty DeferredReq) : Action ty coreTree (Bit 0) :=
    LetL action : DeferredAction <- dispatchDeferredReq req false ;

    If (##action `? "Mem") Then (
      Let memAct : MemAction <- ##action `! "Mem" ;

      If (##memAct `? "Store") Then (
        Let st        : StoreCmd                  <- ##memAct `! "Store" ;
        Let addr      : Addr                      <- ##st`"addr" ;
        Let stVal     : FullCapWithTag            <- ##st`"stVal" ;
        Let memSize   : Bit LgLgNumBytesFullCapSz <- ##st`"memSize" ;

        Act (liftAction np_mem (specMemWrite regions #addr #stVal #memSize)) ;
        Act (liftAction np_rf (updateMshwmOnStore #addr)) ;
        Act (liftAction np_rf incrementMinstret) ;
        Retv
      ) Else (
        Let ld        : LoadCmd           <- ##memAct `! "Load" ;
        Let addr      : Addr              <- ##ld`"addr" ;
        Let pending   : PendingLoad       <- ##ld`"pending" ;

        LetA memVal   : FullCapWithTag    <- liftAction np_mem (specMemRead regions #addr (##pending`"memSize")) ;
        LetL outcome  : LoadOutcome       <- dispatchLoadResponse pending memVal false ;

        If (#outcome `? "RevLookup") Then (
          Let  revInfo : RevCmd        <- #outcome `! "RevLookup" ;
          Let  pr      : PendingRev    <- ##revInfo`"pendingRev" ;
          LetA revBit  : Bool          <- liftAction np_mem (readRevBit (##revInfo`"base")) ;
          LetL wbInfo  : WbCmd         <- dispatchRevResponse pr revBit ;
          If (isNotZero (##wbInfo`"dstIdx")) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))
          ) ;
          Act (liftAction np_rf incrementMinstret) ;
          Retv
        ) Else (
          Let wbInfo : WbCmd <- #outcome `! "Writeback" ;
          If (isNotZero (##wbInfo`"dstIdx")) Then (
            liftAction np_rf (writeRegsList gprPathsWithKind (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))
          ) ;
          Act (liftAction np_rf incrementMinstret) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) Else (
      Act (liftAction np_rf incrementMinstret) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * 3. specExecuteDeferred (Executing Option DeferredReq)
   * ========================================================================= *)
  Definition specExecuteDeferred (reqOpt : ty (Option DeferredReq)) : Action ty coreTree (Bit 0) :=
    If (##reqOpt `? "Some") Then (
      Let req : DeferredReq <- ##reqOpt `! "Some" ;
      specExecuteDeferredReq req
    ) ;
    Retv.

End SpecFetchMemory.
