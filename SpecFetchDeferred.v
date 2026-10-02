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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecDevice SpecMulDiv.

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

Definition MemFenceActionType := [
  ("Mem"%string,   MemAction) ;
  ("Fence"%string, FenceOp)
].
Definition MemFenceAction := TaggedUnion MemFenceActionType.

Definition MulDivCmd := STRUCT_TYPE {
  "dstIdx"   :: Bit RegIdxSz ;
  "op1"      :: Addr ;
  "mulDivOp" :: MulDivUnion
}.

Definition DeferredActionType := [
  ("MemFence"%string, MemFenceAction) ;
  ("MulDiv"%string,   MulDivCmd)
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

  Definition decodeAndAttenuateCap (rawCap : ty Cap) (rawDataLsb : ty Addr)
                                  (rawTag isLM isLG : ty Bool) : LetExpr ty ECap :=
    LETE ldECapRaw   : ECap     <- DecodeCap rawCap rawDataLsb ;
    LetE isCapSealed : Bool     <- isSealed ldECapRaw ;
    LetE rawPerms    : CapPerms <- ##ldECapRaw`"perms" ;
    LetE newPerms    : CapPerms <- ITE #rawTag (attenuatePerms rawPerms isCapSealed isLM isLG) #rawPerms ;
    @RetE _ ECap (STRUCT {
      "R"      ::= ##ldECapRaw`"R" ;
      "perms"  ::= #newPerms ;
      "cOType" ::= ##ldECapRaw`"cOType" ;
      "cE"     ::= ##ldECapRaw`"cE" ;
      "top"    ::= ##ldECapRaw`"top" ;
      "base"   ::= ##ldECapRaw`"base"
    }).

  Definition needsRevocationCheck (ecap : ty ECap) (rawTag : ty Bool) : LetExpr ty Bool :=
    LetE isSealing : Bool <- isSealingCap ecap ;
    @RetE _ Bool (And [ #rawTag ; Not #isSealing ]).

  Definition decodeSubwordData (rawDataLsb : ty Addr)
                               (memSize : ty (Bit LgLgNumBytesFullCapSz))
                               (isUnsigned : ty Bool) : LetExpr ty (Bit Xlen) :=
    LetE rawBytes   : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
      FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #rawDataLsb ;
    LetE memSzBytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 #memSize ;
    @RetE _ (Bit Xlen) (ToBit (
      ITE #isUnsigned
          (ArrayZeroExtend #memSzBytes #rawBytes)
          (ArraySignExtend #memSzBytes #rawBytes)
    )).

  Definition dispatchDeferredReq (req : ty DeferredReq) : LetExpr ty DeferredAction :=
    LetE dstIdx     : Bit RegIdxSz    <- ##req`"dstIdx" ;
    LetE addr       : Addr            <- ##req`"addr" ;
    LetE op         : DeferredUnion   <- ##req`"op" ;
    LetIfE action : DeferredAction <-
      IfE (##op `? "MemFence") ThenE (
        LetE memFence   : MemFenceUnion <- ##op `! "MemFence" ;
        LetIfE mfAct : MemFenceAction <-
          IfE (##memFence `? "Mem") ThenE (
            LetE memPayload : MemPayload                <- ##memFence `! "Mem" ;
            LetE memSize    : Bit LgLgNumBytesFullCapSz <- ##memPayload`"memSize" ;
            LetE memOp      : LoadOrStoreKind           <- ##memPayload`"memOp" ;
            LetIfE memAct : MemAction <-
              IfE (##memOp `? "Store") ThenE (
                LetE stCapVal : FullCapWithTag <- ##memOp `! "Store" ;
                LetE stCmd    : StoreCmd       <- STRUCT {
                  "addr"    ::= #addr ;
                  "stVal"   ::= #stCapVal ;
                  "memSize" ::= #memSize
                } ;
                @RetE _ MemAction (UNION (MemActionType, "Store" ::= #stCmd))
              ) ElseE (
                LetE ldOpVal : LoadOp <- ##memOp `! "Load" ;
                LetE pending : PendingLoad <- STRUCT {
                  "dstIdx"     ::= #dstIdx ;
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
            @RetE _ MemFenceAction (UNION (MemFenceActionType, "Mem" ::= #memAct))
          ) ElseE (
            LetE fenceVal : FenceOp <- ##memFence `! "Fence" ;
            @RetE _ MemFenceAction (UNION (MemFenceActionType, "Fence" ::= #fenceVal))
          ) ;
        @RetE _ DeferredAction (UNION (DeferredActionType, "MemFence" ::= #mfAct))
      ) ElseE (
        LetE mulDivOp : MulDivUnion <- ##op `! "MulDiv" ;
        LetE mdCmd    : MulDivCmd   <- STRUCT {
          "dstIdx"   ::= #dstIdx ;
          "op1"      ::= #addr ;
          "mulDivOp" ::= #mulDivOp
        } ;
        @RetE _ DeferredAction (UNION (DeferredActionType, "MulDiv" ::= #mdCmd))
      ) ;
    @RetE _ DeferredAction #action.

  Definition dispatchLoadResponse (pl : ty PendingLoad) (memVal : ty FullCapWithTag) : LetExpr ty LoadOutcome :=
    LetE dstIdx     : Bit RegIdxSz              <- ##pl`"dstIdx" ;
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
        LETE readBits : Bit Xlen <- decodeSubwordData rawDataLsb memSize isUnsigned ;
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

Section SpecCoreTree.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable tohostAddr : Z.

  Definition specCoreTree (regions : list MemRegion) : Tree DomainElem :=
    Node "core" [
      rfTree dom pcAddrInit ;
      specMemTree regions
    ].

  Section SpecFetchDeferred.
    Variable config : RevConfig.
    Variable regions : list MemRegion.
    Variable ty : Kind -> Type.

    Local Notation memTree := (specMemTree regions).
    Local Notation coreTree := (specCoreTree regions).

    Definition np_rf : NodePath coreTree :=
      Eval cbn in (getNodePath coreTree "core.rf").

    Definition np_mem : NodePath coreTree :=
      Eval cbn in (getNodePath coreTree "core.mem").

    Local Notation readRevBit := (readRevBit config regions).

    (* ===========================================================================
     * specFetch (Atomic Combinational Fetch)
     * =========================================================================== *)
    Definition specFetch : Action ty coreTree FetchOut :=
      LetA pcc     : FullECapWithTag            <- liftAction np_rf (readRegsList (gprPathsWithKind dom pcAddrInit) ($0 : Expr ty (Bit RegIdxSzReal))) ;
      Let  pccAddr : Addr                       <- ##pcc`"addr" ;
      Let  instSz  : Bit LgLgNumBytesFullCapSz  <- $LgNumBytesInstSz ;
      LetA rawFull : FullCapWithTag             <- liftAction np_mem (specMemRead regions pccAddr instSz) ;
      Let rawInst : Inst <- ##rawFull`"addr" ;

      (* Fetch Exception Checks *)
      Let pccECap      : ECap <- ##pcc`"ecap" ;
      Let isComp       : Bool <- isCompressed rawInst ;
      Let instBytesLen : Addr <- ITE #isComp $(CompInstSz / 8) $(InstSz / 8) ;
      Let tagExc       : Bool <- Not ##pcc`"tag" ;
      Let sealExc      : Bool <- isSealed pccECap ;
      Let permExc      : Bool <- Not (##pccECap`"perms"`"EX") ;
      Let boundsExc    : Bool <- Or [
        Ult (ZeroExtendTo (AddrSz + 2) ##pcc`"addr") (ZeroExtendTo (AddrSz + 2) ##pccECap`"base") ;
        Ugt (ZeroExtendTo (AddrSz + 2) (Add [ ##pcc`"addr" ; #instBytesLen ])) (##pccECap`"top")
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

    (* ===========================================================================
     * specExecuteDeferredReq (Single Deferred Request Execution)
     * =========================================================================== *)
    Definition specExecuteDeferredReq (req : ty DeferredReq) : Action ty coreTree (Bit 0) :=
      LetL action : DeferredAction <- dispatchDeferredReq req ;

      If (##action `? "MemFence") Then (
        Let mfAct : MemFenceAction <- ##action `! "MemFence" ;

        If (##mfAct `? "Mem") Then (
          Let memAct : MemAction <- ##mfAct `! "Mem" ;

          If (##memAct `? "Store") Then (
            Let st        : StoreCmd                  <- ##memAct `! "Store" ;
            Let addr      : Addr                      <- ##st`"addr" ;
            Let stVal     : FullCapWithTag            <- ##st`"stVal" ;
            Let memSize   : Bit LgLgNumBytesFullCapSz <- ##st`"memSize" ;

            Act (liftAction np_mem (specMemWrite regions addr stVal memSize)) ;
            If (And [ Eq #addr ($ tohostAddr) ; isNotZero (##stVal`"addr") ]) Then (
              Let tohostVal : Addr <- ##stVal`"addr" ;
              If (Eq #tohostVal $1) Then (
                Sys [ DispString ty "TEST PASSED!\n" ; Finish ty ] ; Retv
              ) ;
              If (Not (Eq #tohostVal $1)) Then (
                Sys [ DispString ty "TEST FAILED at test case: " ; DispDecimal #tohostVal ; DispString ty "\n" ; Finish ty ] ; Retv
              ) ;
              Retv
            ) ;
            Retv
          ) Else (
            Let ld        : LoadCmd                   <- ##memAct `! "Load" ;
            Let addr      : Addr                      <- ##ld`"addr" ;
            Let pending   : PendingLoad               <- ##ld`"pending" ;
            Let memSize   : Bit LgLgNumBytesFullCapSz <- ##pending`"memSize" ;

            LetA memVal   : FullCapWithTag    <- liftAction np_mem (specMemRead regions addr memSize) ;
            LetL outcome  : LoadOutcome       <- dispatchLoadResponse pending memVal ;

            If (#outcome `? "RevLookup") Then (
              Let  revInfo : RevCmd           <- #outcome `! "RevLookup" ;
              Let  revBase : Bit (AddrSz + 1) <- ##revInfo`"base" ;
              Let  pr      : PendingRev       <- ##revInfo`"pendingRev" ;
              LetA revBit  : Bool             <- liftAction np_mem (readRevBit revBase) ;
              LetL wbInfo  : WbCmd            <- dispatchRevResponse pr revBit ;
              If (isNotZero (##wbInfo`"dstIdx")) Then (
                liftAction np_rf (writeRegsList (gprPathsWithKind dom pcAddrInit) (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))
              ) ;
              Retv
            ) Else (
              Let wbInfo : WbCmd <- #outcome `! "Writeback" ;
              If (isNotZero (##wbInfo`"dstIdx")) Then (
                liftAction np_rf (writeRegsList (gprPathsWithKind dom pcAddrInit) (##wbInfo`"dstIdx") (##wbInfo`"dstVal"))
              ) ;
              Retv
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          Retv
        ) ;
        Retv
      ) Else (
        Let md       : MulDivCmd   <- ##action `! "MulDiv" ;
        Let op1      : Addr        <- ##md`"op1" ;
        Let mulDivOp : MulDivUnion <- ##md`"mulDivOp" ;
        LetL resAddr : Addr        <- MulDiv op1 mulDivOp ;
        Let wbVal : FullECapWithTag <- STRUCT {
          "tag"  ::= Const ty Bool false ;
          "ecap" ::= Const ty ECap (getDefault _) ;
          "addr" ::= #resAddr
        } ;
        If (isNotZero (##md`"dstIdx")) Then (
          liftAction np_rf (writeRegsList (gprPathsWithKind dom pcAddrInit) (##md`"dstIdx") #wbVal)
        ) ;
        Retv
      ) ;
      Retv.

    (* ===========================================================================
     * specExecuteDeferred (Executing Option DeferredReq)
     * =========================================================================== *)
    Definition specExecuteDeferred (reqOpt : ty (Option DeferredReq)) : Action ty coreTree (Bit 0) :=
      If (##reqOpt`"valid") Then (
        Let req : DeferredReq <- ##reqOpt`"data" ;
        specExecuteDeferredReq req
      ) ;
      Retv.

  End SpecFetchDeferred.

End SpecCoreTree.
