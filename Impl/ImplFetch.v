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
From Cheriot Require Import SpecDefines Decoder FunctionalUnits ImplCommon ImplBranchPredictor ImplDevice ShiftFifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Section FetchStage.
  Variable dom : string.
  Variable pcAddrInit : Z.
  Variable capacity : nat.

  Definition StraddleHalf := STRUCT_TYPE {
    "lowParcel" :: Bit CompInstSz ;
    "fetchExc"  :: FetchException
  }.

  Definition implFetchTree : Tree DomainElem :=
    Node "" [
      Leaf "fetchPc"      (dom, EReg (Build_Reg Addr (Some (Zmod.of_Z _ pcAddrInit)) false)) ;
      Leaf "predEpoch"    (dom, EReg (Build_Reg Epoch (Some Zmod.zero) false)) ;
      Leaf "curParcelOpt" (dom, EReg (Build_Reg (Option (Bit LgFetchParcels)) (Some (getDefault _)) false)) ;
      Leaf "straddleOpt"  (dom, EReg (Build_Reg (Option StraddleHalf) (Some (getDefault _)) false)) ;
      Node "fetchBuf"     [ fifoTree dom capacity FetchBufEntry ] ;
      Node "instBuf"      [ fifoTree dom capacity AssembledInst ]
    ].

  Definition pFetchPc : RegPath implFetchTree :=
    Eval cbn in (getChildRegPathTree implFetchTree "fetchPc").

  Definition readFetchPc (ty : Kind -> Type) : Action ty implFetchTree Addr :=
    ReadReg "fetchPc" pFetchPc (fun v => Return #v).

  Definition writeFetchPc (ty : Kind -> Type) (val : ty Addr) : Action ty implFetchTree (Bit 0) :=
    WriteReg pFetchPc #val Retv.

  Definition pPredEpoch : RegPath implFetchTree :=
    Eval cbn in (getChildRegPathTree implFetchTree "predEpoch").

  Definition readPredEpoch (ty : Kind -> Type) : Action ty implFetchTree Epoch :=
    ReadReg "predEpoch" pPredEpoch (fun v => Return #v).

  Definition writePredEpoch (ty : Kind -> Type) (val : ty Epoch) : Action ty implFetchTree (Bit 0) :=
    WriteReg pPredEpoch #val Retv.

  Definition pCurParcelOpt : RegPath implFetchTree :=
    Eval cbn in (getChildRegPathTree implFetchTree "curParcelOpt").

  Definition readCurParcelOpt (ty : Kind -> Type) : Action ty implFetchTree (Option (Bit LgFetchParcels)) :=
    ReadReg "curParcelOpt" pCurParcelOpt (fun v => Return #v).

  Definition writeCurParcelOpt (ty : Kind -> Type) (val : ty (Option (Bit LgFetchParcels))) : Action ty implFetchTree (Bit 0) :=
    WriteReg pCurParcelOpt #val Retv.

  Definition pStraddleOpt : RegPath implFetchTree :=
    Eval cbn in (getChildRegPathTree implFetchTree "straddleOpt").

  Definition readStraddleOpt (ty : Kind -> Type) : Action ty implFetchTree (Option StraddleHalf) :=
    ReadReg "straddleOpt" pStraddleOpt (fun v => Return #v).

  Definition writeStraddleOpt (ty : Kind -> Type) (val : ty (Option StraddleHalf)) : Action ty implFetchTree (Bit 0) :=
    WriteReg pStraddleOpt #val Retv.

  Definition clearStraddle (ty : Kind -> Type) : Action ty implFetchTree (Bit 0) :=
    WriteReg pStraddleOpt ConstDef Retv.

  Definition np_fetchInstFifo : NodePath implFetchTree :=
    Eval cbn in (getNodePath implFetchTree ".instBuf.fifo").

  Definition fetchInstFirst (ty : Kind -> Type) : Action ty implFetchTree (Option AssembledInst) :=
    liftAction np_fetchInstFifo (@first dom capacity AssembledInst ty).

  Definition fetchInstDeq (ty : Kind -> Type) : Action ty implFetchTree (Bit 0) :=
    liftAction np_fetchInstFifo (@deq dom capacity AssembledInst ty).

  Definition implFetchIfc (ty : Kind -> Type) : @FetchIfc ty := {|
    fetchTree           := implFetchTree ;
    fetch_instFirst     := @fetchInstFirst ty ;
    fetch_instDeq       := @fetchInstDeq ty ;
    fetch_clearStraddle := @clearStraddle ty ;
    fetch_writeFetchPc  := @writeFetchPc ty
  |}.

  Definition alignPacketAddr {ty : Kind -> Type} (addr : ty Addr) : Expr ty Addr :=
    {< TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #addr,
       Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >}.

  Definition getPacketParcel {ty : Kind -> Type} (addr : ty Addr) : Expr ty (Bit LgFetchParcels) :=
    TruncMsb LgFetchParcels (LgNumBytesFullCapSz - LgFetchParcels)
      (TruncLsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #addr).

  Definition getParcelAddr {ty : Kind -> Type} (alignedPc : ty Addr) (p : ty (Bit LgFetchParcels)) : Expr ty Addr :=
    {< TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #alignedPc,
       #p,
       Const ty (Bit (LgNumBytesFullCapSz - LgFetchParcels)) Zmod.zero >}.

  Definition isParcelCompressed {ty : Kind -> Type} (p : ty (Bit CompInstSz)) : Expr ty Bool :=
    Not (isAllOnes (TruncLsb (CompInstSz - 2) 2 #p)).

  Variable noInstIfc : forall ty, @NoInstPredIfc ty.
  Variable withInstIfc : forall ty, @WithInstPredIfc (noInstIfc ty).(noInstTree) ty.
  Variable memIfc : forall ty, @MemIfc ty.
  Variable executeIfc : forall ty, @ExecuteIfc ty.
  Variable decodeTree deferredTree : Tree DomainElem.
  Variable ty : Kind -> Type.

  Local Abbreviation rfTree := (rfTree dom pcAddrInit).
  Local Abbreviation bpTree := (bpTree (noInstIfc ty).(noInstTree) (withInstIfc ty).(withInstTree)).
  Local Abbreviation memTree := (memIfc ty).(memTree).
  Local Abbreviation executeTree := (executeIfc ty).(executeTree).
  Local Abbreviation coreTree := (coreTree dom rfTree bpTree memTree implFetchTree decodeTree executeTree deferredTree).
  Local Abbreviation gprPathsWithKind := (gprPathsWithKind dom pcAddrInit).

  Definition np_rf : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.rf.").

  Definition np_bp : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.bp") singletonChildPath).

  Definition np_noInst : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.bp..noInst") singletonChildPath).

  Definition np_mem : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.mem") singletonChildPath).

  Definition np_fetch : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch.").

  Definition np_fetchFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch..fetchBuf.fifo").

  Definition np_instFifo : NodePath coreTree :=
    Eval cbn in (getNodePath coreTree "core.fetch..instBuf.fifo").

  Definition np_execute : NodePath coreTree :=
    Eval cbv in (embedNodeIntoPath (getNodePath coreTree "core.execute") singletonChildPath).

  (* =========================================================================
   * STAGE 1: fetchRq
   *
   * - Precondition: fetchBuf is not full (!isFull).
   * - Action:       Read fetchPc, execEpoch, predEpoch, and global PCC
   *                 metadata from GPR 0. Perform pre-fetch Tag, Seal,
   *                 EX-perm, and Base-bounds checks. If no fault so far,
   *                 issue aligned packet read mem_readInstRq(alignedPc).
   *                 When pre-fault or request accepted, predict exitParcel
   *                 and predPc via noInst_getPred(fetchPc), enqueue
   *                 FetchBufEntry into fetchBuf, and advance fetchPc to predPc.
   * ========================================================================= *)
  Definition fetchRq : Action ty coreTree (Bit 0) :=
    LetA fetchBuf_isFull : Bool <- liftAction np_fetchFifo (@isFull dom capacity FetchBufEntry ty) ;
    LetA fenceIPending   : Bool <- liftAction np_execute (executeIfc ty).(execute_readFenceIPend) ;
    LetA fenceIWait      : Bool <- liftAction np_mem ((memIfc ty).(mem_readFenceIWait)) ;

    If (And [ Not #fetchBuf_isFull ; Not #fenceIPending ; Not #fenceIWait ]) Then (
      LetA fetchPc   : Addr            <- liftAction np_fetch (@readFetchPc ty) ;
      LetA execEpoch : Epoch           <- liftAction np_execute (executeIfc ty).(execute_readExecEpoch) ;
      LetA predEpoch : Epoch           <- liftAction np_fetch (@readPredEpoch ty) ;
      LetA pcc       : FullECapWithTag <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;

      Let  alignedPc   : Addr <- alignPacketAddr fetchPc ;
      Let  pccECap     : ECap <- ##pcc`"ecap" ;
      Let  tagExc      : Bool <- Not ##pcc`"tag" ;
      Let  sealExc     : Bool <- isSealed pccECap ;
      Let  permExc     : Bool <- Not (##pccECap`"perms"`"EX") ;
      Let  baseBndsExc : Bool <- Ult (ZeroExtendTo (AddrSz + 1) #fetchPc) (##pccECap`"base") ;
      Let  hasPreFault : Bool <- Or [ #tagExc ; #sealExc ; #permExc ; #baseBndsExc ] ;

      Let  preFetchExc : FetchException <- STRUCT {
        "tag"    ::= #tagExc ;
        "seal"   ::= #sealExc ;
        "perm"   ::= #permExc ;
        "bounds" ::= #baseBndsExc
      } ;

      LetIf canEnq : Bool <-
        If #hasPreFault Then (
          Return (ConstBool true)
        ) Else (
          liftAction np_mem ((memIfc ty).(mem_readInstRq) alignedPc)
        ) ;

      If #canEnq Then (
        Let  defaultNoInstOut : NoInstPredOut <- STRUCT {
          "exitParcel" ::= Const ty (Bit LgFetchParcels) (InvDefault _) ;
          "predPc"     ::= #fetchPc
        } ;
        LetIf noInstOut : NoInstPredOut <-
          If (Not #hasPreFault) Then (
            liftAction np_noInst ((noInstIfc ty).(noInst_getPred) fetchPc)
          ) Else (
            Return #defaultNoInstOut
          ) ;
        Let  predPc    : Addr          <- ##noInstOut`"predPc" ;
        Let  entry     : FetchBufEntry <- STRUCT {
          "pcAddr"     ::= #fetchPc ;
          "predPc"     ::= #predPc ;
          "exitParcel" ::= ##noInstOut`"exitParcel" ;
          "execEpoch"  ::= #execEpoch ;
          "predEpoch"  ::= #predEpoch ;
          "fetchExc"   ::= #preFetchExc
        } ;
        Act (liftAction np_fetchFifo (@enq dom capacity FetchBufEntry ty entry)) ;
        liftAction np_fetch (@writeFetchPc ty predPc)
      ) ;
      Retv
    ) ;
    Retv.

  (* =========================================================================
   * STAGE 2: fetchAssemble
   *
   * - Precondition: fetchBuf is non-empty, memory packet response is ready
   *                 (or pre-fault), and instBuf is not full when valid.
   * - Action:       Drop wrong-epoch packets (resetting curParcelOpt). For
   *                 valid packets, step through parcels sequentially until
   *                 either L2 predicts a taken branch or the end of the line
   *                 is reached (including cross-packet straddles), updating
   *                 noInst and redirecting on predEpoch if predPc != l2PredPc.
   * ========================================================================= *)
  Definition fetchAssemble : Action ty coreTree (Bit 0) :=
    LetA fetchHead      : Option FetchBufEntry <- liftAction np_fetchFifo (@first dom capacity FetchBufEntry ty) ;
    LetA instBuf_isFull : Bool                 <- liftAction np_instFifo (@isFull dom capacity AssembledInst ty) ;

    If (##fetchHead`"valid") Then (
      Let entry       : FetchBufEntry      <- ##fetchHead`"data" ;
      Let entryPc     : Addr               <- ##entry`"pcAddr" ;
      Let alignedPc   : Addr               <- alignPacketAddr entryPc ;
      Let startParcel : Bit LgFetchParcels <- getPacketParcel entryPc ;
      Let exitParcel  : Bit LgFetchParcels <- ##entry`"exitParcel" ;
      Let preExc      : FetchException     <- ##entry`"fetchExc" ;
      Let hasPreFault : Bool               <- Or [ ##preExc`"tag" ;
                                                   ##preExc`"seal" ;
                                                   ##preExc`"perm" ;
                                                   ##preExc`"bounds" ] ;

      LetIf pktOpt : Option FetchPacket <-
        If #hasPreFault Then (
          Return (mkSome ConstDef)
        ) Else (
          liftAction np_mem ((memIfc ty).(mem_getInstRp) alignedPc)
        ) ;

      If (##pktOpt`"valid") Then (
        Let  pkt          : FetchPacket                 <- ##pktOpt`"data" ;
        Let  noneParcel   : Option (Bit LgFetchParcels) <- ConstDef ;
        LetA execEpoch    : Epoch                       <- liftAction np_execute (executeIfc ty).(execute_readExecEpoch) ;
        LetA predEpoch    : Epoch                       <- liftAction np_fetch (@readPredEpoch ty) ;

        Let  isEpochMatch : Bool                        <- And [ Eq (##entry`"execEpoch") #execEpoch ;
                                                                 Eq (##entry`"predEpoch") #predEpoch ] ;

        If (Not #isEpochMatch) Then (
          Act (liftAction np_fetchFifo (@deq dom capacity FetchBufEntry ty)) ;
          If (Not #hasPreFault) Then (
            liftAction np_mem ((memIfc ty).(mem_deqInstRp) alignedPc)
          ) ;
          liftAction np_fetch (@writeCurParcelOpt ty noneParcel)
        ) Else (
          If (Not #instBuf_isFull) Then (
            LetA curParcelOpt       : Option (Bit LgFetchParcels) <- liftAction np_fetch (@readCurParcelOpt ty) ;
            LetA straddleOpt        : Option StraddleHalf         <- liftAction np_fetch (@readStraddleOpt ty) ;
            Let  straddle           : StraddleHalf                <- ##straddleOpt`"data" ;
            Let  hasStraddle        : Bool                        <- ##straddleOpt`"valid" ;

            Let  k                  : Bit LgFetchParcels          <- ITE (##curParcelOpt`"valid") (##curParcelOpt`"data") #startParcel ;
            Let  instPcK            : Addr                        <- getParcelAddr alignedPc k ;
            Let  parcelK            : Bit CompInstSz              <- ReadArray #pkt #k ;
            Let  isCompParcel       : Bool                        <- isParcelCompressed parcelK ;
            Let  isLastK            : Bool                        <- isAllOnes #k ;
            Let  initStraddle       : Bool                        <- And [ Not #hasStraddle ; Not #isCompParcel ; #isLastK ] ;

            Let  kPlus1             : Bit LgFetchParcels          <- Add [ #k ; $1 ] ;
            Let  currInstLastParcel : Bit LgFetchParcels          <-
              ITE0 (Not #hasStraddle) (ITE (Or [ #isCompParcel ; #initStraddle ]) #k #kPlus1) ;

            Let  highParcelIdx      : Bit LgFetchParcels          <- ITE0 (Not #hasStraddle) #kPlus1 ;
            Let  highParcel         : Bit CompInstSz              <- ReadArray #pkt #highParcelIdx ;
            Let  lowParcel          : Bit CompInstSz              <- ITE #hasStraddle (##straddle`"lowParcel") #parcelK ;
            Let  rawInst            : Inst                        <- {< #highParcel, #lowParcel >} ;
            LetL expInst            : Inst                        <- preDecode rawInst ;

            Let  instPc             : Addr                        <- ITE #hasStraddle (Sub #alignedPc $2) #instPcK ;
            Let  stepBytes          : Addr                        <-
              ITE (And [ Not #hasStraddle ; #isCompParcel ]) $(CompInstSz / 8) $(InstSz / 8) ;
            Let  seqPc              : Addr                        <- Add [ #instPc ; #stepBytes ] ;

            LetA pcc                : FullECapWithTag             <- liftAction np_rf (readRegsList gprPathsWithKind ($0 : Expr ty (Bit RegIdxSzReal))) ;
            Let  pccECap            : ECap                        <- ##pcc`"ecap" ;
            Let  topExc             : Bool                        <- Ugt (ZeroExtendTo (AddrSz + 2) #seqPc) (##pccECap`"top") ;
            Let  stradExc           : FetchException              <- ##straddle`"fetchExc" ;
            Let  pktExc             : FetchException              <- ITE #hasStraddle #stradExc #preExc ;
            Let  combExc            : FetchException              <- #pktExc `{ "bounds" <- Or [ ##pktExc`"bounds" ; #topExc ] } ;
            Let  hasCombFault       : Bool                        <- Or [ ##combExc`"tag" ;
                                                                          ##combExc`"seal" ;
                                                                          ##combExc`"perm" ;
                                                                          ##combExc`"bounds" ] ;

            LetL pb                 : PreBranchInfo               <- preDecodeBranch expInst ;
            Let  instPred           : Addr                        <- ITE (Eq #currInstLastParcel #exitParcel) (##entry`"predPc") #seqPc ;
            Let  seqNextPktAddr     : Addr                        <- Add [ #alignedPc ; $NumBytesFullCapSz ] ;

            Let  defaultPredPc      : Addr                        <- ITE #initStraddle #seqNextPktAddr #instPred ;

            LetIf l2PredPc : Addr <-
              If (And [ Not #initStraddle ; Not #hasCombFault ]) Then (
                liftAction np_bp ((withInstIfc ty).(withInst_getPred) instPc instPred expInst pb)
              ) Else (
                Return #defaultPredPc
              ) ;

            Let  isEndOfLine        : Bool                        <- Or [ Not (Eq #l2PredPc #seqPc) ; isAllOnes #currInstLastParcel ] ;

            If #isEndOfLine Then (
              Let exitMismatch   : Bool <- Not (Eq #exitParcel #currInstLastParcel) ;
              Let predPcMismatch : Bool <- Not (Eq (##entry`"predPc") #l2PredPc) ;

              Act (liftAction np_fetchFifo (@deq dom capacity FetchBufEntry ty)) ;
              If (Not #hasPreFault) Then (
                liftAction np_mem ((memIfc ty).(mem_deqInstRp) alignedPc)
              ) ;
              Act (liftAction np_fetch (@writeCurParcelOpt ty noneParcel)) ;
              Act (liftAction np_noInst ((noInstIfc ty).(noInst_updByFetch)
                     entryPc currInstLastParcel exitMismatch l2PredPc predPcMismatch pb initStraddle)) ;

              If #predPcMismatch Then (
                Let nextPredEpoch : Epoch <- Add [ #predEpoch ; $1 ] ;
                Act (liftAction np_fetch (@writePredEpoch ty nextPredEpoch)) ;
                liftAction np_fetch (@writeFetchPc ty l2PredPc)
              ) ;
              Retv
            ) Else (
              Let nextK     : Bit LgFetchParcels          <- Add [ #currInstLastParcel ; $1 ] ;
              Let someNextK : Option (Bit LgFetchParcels) <- mkSome #nextK ;
              liftAction np_fetch (@writeCurParcelOpt ty someNextK)
            ) ;

            If #initStraddle Then (
              Let newStraddle : StraddleHalf <- STRUCT {
                "lowParcel" ::= #parcelK ;
                "fetchExc"  ::= #preExc
              } ;
              Let someStraddle : Option StraddleHalf <- mkSome #newStraddle ;
              liftAction np_fetch (@writeStraddleOpt ty someStraddle)
            ) Else (
              Let fetchOut : FetchOut <- STRUCT {
                "hasAsr"   ::= ##pccECap`"perms"`"SR" ;
                "inst"     ::= #expInst ;
                "fetchExc" ::= #combExc
              } ;
              Let asmInst : AssembledInst <- STRUCT {
                "fetchOut"  ::= #fetchOut ;
                "predPc"    ::= #l2PredPc ;
                "execEpoch" ::= #execEpoch
              } ;
              Act (liftAction np_fetch (@clearStraddle ty)) ;
              liftAction np_instFifo (@enq dom capacity AssembledInst ty asmInst)
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End FetchStage.
