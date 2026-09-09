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

From Stdlib Require Import String List ZArith Zmod Bool Psatz Nat Arith.
From Guru Require Import Syntax Notations Semantics Library Composition SimulatorOnly.
From Cheriot Require Import SpecDefines SpecDevice Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * SiFive UART Register Offsets & Memory Footprint
 * =========================================================================== *)

Definition SifiveUartRegNames : list string :=
  [ "txdata" ; "rxdata" ; "txctrl" ; "rxctrl" ; "ie" ; "ip" ; "div" ].

Definition sifiveUartRegIdx (name : string) :=
  forceOption (getStrIndexOption name SifiveUartRegNames).

Definition SifiveUartNumRegs : nat := Eval compute in (length SifiveUartRegNames).
Definition SifiveUartSizeBytes : Z := Eval compute in (Z.of_nat SifiveUartNumRegs * NumBytesXlen)%Z.

Definition SifiveUartRegIdxWidth : Z := Eval compute in (Z.log2_up (Z.of_nat SifiveUartNumRegs)).

Notation sifiveUartRegIdxBit name :=
  ($(Z.of_nat (sifiveUartRegIdx name))).

Definition SIFIVE_UART_TXDATA_OFFSET : Z := 0.   (* 0x00: txdata (w: data, r: full) *)
Definition SIFIVE_UART_RXDATA_OFFSET : Z := 4.   (* 0x04: rxdata (r: data, empty) *)
Definition SIFIVE_UART_TXCTRL_OFFSET : Z := 8.   (* 0x08: txctrl (txen, nstop, txcnt) *)
Definition SIFIVE_UART_RXCTRL_OFFSET : Z := 12.  (* 0x0C: rxctrl (rxen, rxcnt) *)
Definition SIFIVE_UART_IE_OFFSET     : Z := 16.  (* 0x10: ie (txwm, rxwm) *)
Definition SIFIVE_UART_IP_OFFSET     : Z := 20.  (* 0x14: ip (txwm, rxwm) *)
Definition SIFIVE_UART_DIV_OFFSET    : Z := 24.  (* 0x18: div (baud rate divisor) *)

Definition SifiveUartFifoCapacity : nat := 8.

Definition SifiveUartWatermarkWidth : Z :=
  Eval compute in (Z.log2_up (Z.of_nat SifiveUartFifoCapacity)).

Definition SifiveUartFifoCountWidth : Z :=
  Eval compute in (Z.log2_up (Z.of_nat (SifiveUartFifoCapacity + 1))).

(* Helper to read size/count from a fifoTree *)
Definition fifoCount {capacity : nat} {k : Kind} {ty : Kind -> Type} :
  Action ty (fifoTree capacity k) (Bit (Z.log2_up (Z.of_nat (capacity + 1)))) :=
  RegRead sz <- "fifo.size" in (fifoTree capacity k) ;
  Return #sz.

(* ===========================================================================
 * SiFive UART Tree Definition
 * =========================================================================== *)

Definition sifiveUartChildren : list (Tree Elem) :=
  [ Node "tx" [ fifoTree SifiveUartFifoCapacity (Bit 8) ] ;
    Node "rx" [ fifoTree SifiveUartFifoCapacity (Bit 8) ] ;
    Leaf "txctrl_txen"  (EReg (Build_Reg Bool (Some false))) ;
    Leaf "txctrl_nstop" (EReg (Build_Reg Bool (Some false))) ;
    Leaf "txctrl_txcnt" (EReg (Build_Reg (Bit SifiveUartWatermarkWidth) (Some Zmod.zero))) ;
    Leaf "rxctrl_rxen"  (EReg (Build_Reg Bool (Some false))) ;
    Leaf "rxctrl_rxcnt" (EReg (Build_Reg (Bit SifiveUartWatermarkWidth) (Some Zmod.zero))) ;
    Leaf "ie_txwm"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "ie_rxwm"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "ip_txwm"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "ip_rxwm"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "div"          (EReg (Build_Reg (Bit 16) (Some Zmod.zero))) ;
    Leaf "txData"       (ESend (Bit 8)) ;
    Leaf "txRdy"        (ERecv Bool) ;
    Leaf "rxData"       (ERecv (Option (Bit 8))) ;
    Leaf "rxRdy"        (ESend (Bit 0)) ;
    Leaf "divOut"       (ESend (Bit 16))
  ].

Definition sifiveUartTree : Tree Elem :=
  Node "sifive_uart" sifiveUartChildren.

Definition SifiveUartLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

(* ===========================================================================
 * Paths & Embeddings
 * =========================================================================== *)

Definition sifiveUartTxctrlTxenPath  : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "txctrl_txen".
Definition sifiveUartTxctrlNstopPath : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "txctrl_nstop".
Definition sifiveUartTxctrlTxcntPath : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "txctrl_txcnt".

Definition sifiveUartRxctrlRxenPath  : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "rxctrl_rxen".
Definition sifiveUartRxctrlRxcntPath : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "rxctrl_rxcnt".

Definition sifiveUartIeTxwmPath      : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "ie_txwm".
Definition sifiveUartIeRxwmPath      : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "ie_rxwm".

Definition sifiveUartIpTxwmPath      : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "ip_txwm".
Definition sifiveUartIpRxwmPath      : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "ip_rxwm".

Definition sifiveUartDivPath         : RegPath sifiveUartTree := getChildRegPathTree sifiveUartTree "div".

Definition sifiveUartTxDataPath      : SendPath sifiveUartTree := getChildSendPathTree sifiveUartTree "txData".
Definition sifiveUartTxRdyPath       : RecvPath sifiveUartTree := getChildRecvPathTree sifiveUartTree "txRdy".
Definition sifiveUartRxDataPath      : RecvPath sifiveUartTree := getChildRecvPathTree sifiveUartTree "rxData".
Definition sifiveUartRxRdyPath       : SendPath sifiveUartTree := getChildSendPathTree sifiveUartTree "rxRdy".
Definition sifiveUartDivOutPath      : SendPath sifiveUartTree := getChildSendPathTree sifiveUartTree "divOut".

Definition np_tx_fifo : NodePath sifiveUartTree :=
  getNodePath sifiveUartTree "sifive_uart.tx.fifo".

Definition np_rx_fifo : NodePath sifiveUartTree :=
  getNodePath sifiveUartTree "sifive_uart.rx.fifo".

(* Helper to lift an action across equality of tree nodes *)
Definition liftActionEq {ty : Kind -> Type} {t : Tree Elem} {k : Kind}
  (p : NodePath t) {t' : Tree Elem} (H : getNode p = t') (a : Action ty t' k) : Action ty t k :=
  match H in _ = X return Action ty X k -> Action ty t k with
  | eq_refl => liftAction (ty:=ty) p (k:=k)
  end a.
Arguments liftActionEq [ty t k] p [t'] H a.

(* ===========================================================================
 * SiFive UART Internal Operations
 * =========================================================================== *)

Section SifiveUartOperations.
  Variable ty : Kind -> Type.

  (* Read txdata: bit 31 indicates whether TX FIFO is full *)
  Definition readTxData : Action ty sifiveUartTree (Bit Xlen) :=
    LetA txFull : Bool <- liftAction np_tx_fifo (@isFull SifiveUartFifoCapacity (Bit 8) ty) ;
    Return {< ToBit #txFull, Const ty (Bit (Xlen - 1)) Zmod.zero >}.

  (* Read rxdata: dequeues byte from RX FIFO if available, bit 31 indicates empty *)
  Definition readRxData : Action ty sifiveUartTree (Bit Xlen) :=
    LetA rxEmpty : Bool <- liftAction np_rx_fifo (@isEmpty SifiveUartFifoCapacity (Bit 8) ty) ;
    LetIf rxByte : Bit 8 <-
      If (Not #rxEmpty) Then (
        LetA rxHead : Option (Bit 8) <- liftAction np_rx_fifo (@first SifiveUartFifoCapacity (Bit 8) ty) ;
        Act (liftAction np_rx_fifo (@deq SifiveUartFifoCapacity (Bit 8) ty)) ;
        Return (##rxHead `! "Some")
      ) Else (
        Return $0
      ) ;
    Return {< ToBit #rxEmpty, Const ty (Bit (Xlen - 9)) Zmod.zero, #rxByte >}.

  (* Read ip: reads registered interrupt pending flags *)
  Definition readIp : Action ty sifiveUartTree (Bit Xlen) :=
    LetA txwm_ip : Bool <- ReadReg "ip_txwm" sifiveUartIpTxwmPath (fun v => Return #v) ;
    LetA rxwm_ip : Bool <- ReadReg "ip_rxwm" sifiveUartIpRxwmPath (fun v => Return #v) ;
    Return {< Const ty (Bit (Xlen - 2)) Zmod.zero, ToBit #rxwm_ip, ToBit #txwm_ip >}.

  (* Autonomous rule to update ip_txwm and ip_rxwm registers *)
  Definition sifiveUartIpStep : Action ty sifiveUartTree (Bit 0) :=
    LetA txCount : Bit SifiveUartFifoCountWidth <- liftAction np_tx_fifo (@fifoCount SifiveUartFifoCapacity (Bit 8) ty) ;
    LetA rxCount : Bit SifiveUartFifoCountWidth <- liftAction np_rx_fifo (@fifoCount SifiveUartFifoCapacity (Bit 8) ty) ;
    LetA txcnt   : Bit SifiveUartWatermarkWidth <- ReadReg "txctrl_txcnt" sifiveUartTxctrlTxcntPath (fun v => Return #v) ;
    LetA rxcnt   : Bit SifiveUartWatermarkWidth <- ReadReg "rxctrl_rxcnt" sifiveUartRxctrlRxcntPath (fun v => Return #v) ;
    Let txwm_ip  : Bool <- Slt #txCount (ZeroExtendTo SifiveUartFifoCountWidth #txcnt) ;
    Let rxwm_ip  : Bool <- Sgt #rxCount (ZeroExtendTo SifiveUartFifoCountWidth #rxcnt) ;
    Act (WriteReg sifiveUartIpTxwmPath #txwm_ip Retv) ;
    WriteReg sifiveUartIpRxwmPath #rxwm_ip Retv.

  (* SiFive UART Interrupt Output: evaluated for PLIC connection *)
  Definition sifiveUartIrq : Action ty sifiveUartTree Bool :=
    LetA txwm_ip : Bool <- ReadReg "ip_txwm" sifiveUartIpTxwmPath (fun v => Return #v) ;
    LetA rxwm_ip : Bool <- ReadReg "ip_rxwm" sifiveUartIpRxwmPath (fun v => Return #v) ;
    LetA ie_txwm : Bool <- ReadReg "ie_txwm" sifiveUartIeTxwmPath (fun v => Return #v) ;
    LetA ie_rxwm : Bool <- ReadReg "ie_rxwm" sifiveUartIeRxwmPath (fun v => Return #v) ;
    Let tx_irq   : Bool <- And [ #txwm_ip ; #ie_txwm ] ;
    Let rx_irq   : Bool <- And [ #rxwm_ip ; #ie_rxwm ] ;
    Let any_irq  : Bool <- Or [ #tx_irq ; #rx_irq ] ;
    Return #any_irq.

  (* =========================================================================
   * Decoupled Hardware Rules for Streaming PHY Interface & Divisor Export
   * ========================================================================= *)

  (* Autonomous rule to export divisor on divOut *)
  Definition sifiveUartDivStep : Action ty sifiveUartTree (Bit 0) :=
    ReadReg "div" sifiveUartDivPath (fun divVal =>
      Send sifiveUartDivOutPath #divVal Retv
    ).

  (* TX Rule: When enabled and not empty, presents data on txData and dequeues on txRdy *)
  Definition sifiveUartTxStep : Action ty sifiveUartTree (Bit 0) :=
    LetA txen : Bool <- ReadReg "txctrl_txen" sifiveUartTxctrlTxenPath (fun v => Return #v) ;
    If #txen Then (
      LetA txEmpty : Bool <- liftAction np_tx_fifo (@isEmpty SifiveUartFifoCapacity (Bit 8) ty) ;
      If (Not #txEmpty) Then (
        LetA txHead : Option (Bit 8) <- liftAction np_tx_fifo (@first SifiveUartFifoCapacity (Bit 8) ty) ;
        Let hasData : Bool <- ##txHead `? "Some" ;
        If #hasData Then (
          Let txByte : Bit 8 <- ##txHead `! "Some" ;
          Act (Send sifiveUartTxDataPath #txByte Retv) ;
          Recv "txRdy" sifiveUartTxRdyPath (fun txRdy =>
            If #txRdy Then (
              Act (liftAction np_tx_fifo (@deq SifiveUartFifoCapacity (Bit 8) ty)) ;
              Retv
            ) ;
            Retv
          )
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* RX Rule: When rxen enabled and FIFO not full, sends rxRdy and samples rxData *)
  Definition sifiveUartRxStep : Action ty sifiveUartTree (Bit 0) :=
    LetA rxen : Bool <- ReadReg "rxctrl_rxen" sifiveUartRxctrlRxenPath (fun v => Return #v) ;
    If #rxen Then (
      LetA rxFull : Bool <- liftAction np_rx_fifo (@isFull SifiveUartFifoCapacity (Bit 8) ty) ;
      If (Not #rxFull) Then (
        Act (Send sifiveUartRxRdyPath (Const ty (Bit 0) Zmod.zero) Retv) ;
        Retv
      ) ;
      Recv "rxData" sifiveUartRxDataPath (fun rxOpt =>
        Let hasData : Bool <- ##rxOpt `? "Some" ;
        If #hasData Then (
          Let rxByte : Bit 8 <- ##rxOpt `! "Some" ;
          If (Not #rxFull) Then (
            Act (liftAction np_rx_fifo (@enq SifiveUartFifoCapacity (Bit 8) ty rxByte)) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      )
    ) ;
    Retv.

End SifiveUartOperations.

Arguments readTxData {ty}.
Arguments readRxData {ty}.
Arguments readIp {ty}.
Arguments sifiveUartIpStep {ty}.
Arguments sifiveUartIrq {ty}.
Arguments sifiveUartDivStep {ty}.
Arguments sifiveUartTxStep {ty}.
Arguments sifiveUartRxStep {ty}.
Arguments fifoCount {capacity k ty}.

(* ===========================================================================
 * MMIO Line Read & Write Actions
 * =========================================================================== *)

Definition sifiveUartLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty sifiveUartTree (LineReadRp SifiveUartLineConfig) :=
  Let offset <- getMemOffset base SifiveUartSizeBytes addr ;
  Let regIdx : Bit SifiveUartRegIdxWidth <- TruncMsb SifiveUartRegIdxWidth LgNumBytesXlen #offset ;
  Let isTxData : Bool <- Eq #regIdx (sifiveUartRegIdxBit "txdata") ;
  Let isRxData : Bool <- Eq #regIdx (sifiveUartRegIdxBit "rxdata") ;
  Let isTxCtrl : Bool <- Eq #regIdx (sifiveUartRegIdxBit "txctrl") ;
  Let isRxCtrl : Bool <- Eq #regIdx (sifiveUartRegIdxBit "rxctrl") ;
  Let isIe     : Bool <- Eq #regIdx (sifiveUartRegIdxBit "ie") ;
  Let isIp     : Bool <- Eq #regIdx (sifiveUartRegIdxBit "ip") ;
  Let isDiv    : Bool <- Eq #regIdx (sifiveUartRegIdxBit "div") ;
  LetIf txDataWord : Bit Xlen <-
    If #isTxData Then readTxData Else (Return $0) ;
  LetIf rxDataWord : Bit Xlen <-
    If #isRxData Then readRxData Else (Return $0) ;
  LetIf ipWord : Bit Xlen <-
    If #isIp Then readIp Else (Return $0) ;
  ReadReg "txctrl_txen"  sifiveUartTxctrlTxenPath  (fun txen =>
  ReadReg "txctrl_nstop" sifiveUartTxctrlNstopPath (fun nstop =>
  ReadReg "txctrl_txcnt" sifiveUartTxctrlTxcntPath (fun txcnt =>
  ReadReg "rxctrl_rxen"  sifiveUartRxctrlRxenPath  (fun rxen =>
  ReadReg "rxctrl_rxcnt" sifiveUartRxctrlRxcntPath (fun rxcnt =>
  ReadReg "ie_txwm"      sifiveUartIeTxwmPath      (fun ie_txwm =>
  ReadReg "ie_rxwm"      sifiveUartIeRxwmPath      (fun ie_rxwm =>
  ReadReg "div"          sifiveUartDivPath         (fun divVal =>
  Let txctrlWord : Bit Xlen <-
    {< Const ty (Bit (16 - SifiveUartWatermarkWidth)) Zmod.zero,
       #txcnt,
       Const ty (Bit 14) Zmod.zero,
       ToBit #nstop,
       ToBit #txen >} ;
  Let rxctrlWord : Bit Xlen <-
    {< Const ty (Bit (16 - SifiveUartWatermarkWidth)) Zmod.zero,
       #rxcnt,
       Const ty (Bit 15) Zmod.zero,
       ToBit #rxen >} ;
  Let ieWord : Bit Xlen <-
    {< Const ty (Bit (Xlen - 2)) Zmod.zero,
       ToBit #ie_rxwm,
       ToBit #ie_txwm >} ;
  Let divWord : Bit Xlen <-
    {< Const ty (Bit (Xlen - 16)) Zmod.zero,
       #divVal >} ;
  Let readWord : Bit Xlen <-
    Or [ ITE0 #isTxData #txDataWord ;
         ITE0 #isRxData #rxDataWord ;
         ITE0 #isTxCtrl #txctrlWord ;
         ITE0 #isRxCtrl #rxctrlWord ;
         ITE0 #isIe     #ieWord ;
         ITE0 #isIp     #ipWord ;
         ITE0 #isDiv    #divWord ] ;
  Let dataArr : Array (cfgLineBytes SifiveUartLineConfig) (Bit 8) <-
    FromBit (Array (cfgLineBytes SifiveUartLineConfig) (Bit 8)) #readWord ;
  @Return ty sifiveUartTree (LineReadRp SifiveUartLineConfig) (STRUCT {
    "data" ::= #dataArr ;
    "tag"  ::= Const ty (Array (cfgNumLineTags SifiveUartLineConfig) Bool) (getDefault _)
  }))))))))).

Definition sifiveUartLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq SifiveUartLineConfig))
           : Action ty sifiveUartTree (Bit 0) :=
  Let offset <- getMemOffset base SifiveUartSizeBytes (rq`"addr") ;
  Let regIdx : Bit SifiveUartRegIdxWidth <- TruncMsb SifiveUartRegIdxWidth LgNumBytesXlen #offset ;
  Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
  Let writeBits : Array (Z.to_nat Xlen) Bool <-
    FromBit (Array (Z.to_nat Xlen) Bool) #writeWord ;
  Let dataByte : Bit 8 <- TruncLsb (Xlen - 8) 8 #writeWord ;
  If (Eq #regIdx (sifiveUartRegIdxBit "txdata")) Then (
    LetA txFull : Bool <- liftAction np_tx_fifo (@isFull SifiveUartFifoCapacity (Bit 8) ty) ;
    If (Not #txFull) Then (
      liftAction np_tx_fifo (@enq SifiveUartFifoCapacity (Bit 8) ty dataByte)
    ) ;
    Retv
  ) ;
  If (Eq #regIdx (sifiveUartRegIdxBit "txctrl")) Then (
    Act (WriteReg sifiveUartTxctrlTxenPath (##writeBits$[0]) Retv) ;
    Act (WriteReg sifiveUartTxctrlNstopPath (##writeBits$[1]) Retv) ;
    WriteReg sifiveUartTxctrlTxcntPath (TruncLsb (16 - SifiveUartWatermarkWidth) SifiveUartWatermarkWidth (TruncMsb 16 16 #writeWord)) Retv
  ) ;
  If (Eq #regIdx (sifiveUartRegIdxBit "rxctrl")) Then (
    Act (WriteReg sifiveUartRxctrlRxenPath (##writeBits$[0]) Retv) ;
    WriteReg sifiveUartRxctrlRxcntPath (TruncLsb (16 - SifiveUartWatermarkWidth) SifiveUartWatermarkWidth (TruncMsb 16 16 #writeWord)) Retv
  ) ;
  If (Eq #regIdx (sifiveUartRegIdxBit "ie")) Then (
    Act (WriteReg sifiveUartIeTxwmPath (##writeBits$[0]) Retv) ;
    WriteReg sifiveUartIeRxwmPath (##writeBits$[1]) Retv
  ) ;
  If (Eq #regIdx (sifiveUartRegIdxBit "div")) Then (
    WriteReg sifiveUartDivPath (TruncLsb 16 16 #writeWord) Retv
  ) ;
  Retv.

Arguments sifiveUartLineReadAction base ty addr : clear implicits.
Arguments sifiveUartLineWriteAction base ty rq : clear implicits.

(* ===========================================================================
 * MemRegion Constructor
 * =========================================================================== *)

Definition sifiveUartMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + SifiveUartSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes SifiveUartLineConfig)) =? 0)%Z)
           : MemRegion := {|
  regionName        := "sifive_uart" ;
  regionBase        := base ;
  regionSize        := SifiveUartSizeBytes ;
  regionLineCfg     := SifiveUartLineConfig ;
  isReadOnly        := false ;
  regionKind        := @CustomMem "sifive_uart" SifiveUartSizeBytes SifiveUartLineConfig
                                  sifiveUartChildren
                                  (sifiveUartLineReadAction base)
                                  (sifiveUartLineWriteAction base)
                                  (Some (fun ty => sifiveUartIrq (ty:=ty))) ;
  regionInMemory    := pfBound ;
  regionBaseAligned := pfAligned ;
  regionSizeAligned := I
|}.

Arguments sifiveUartMemRegion base pfBound pfAligned : clear implicits.

(* ===========================================================================
 * System Integration Helpers
 * =========================================================================== *)

Record SifiveUartInstance (regions : list MemRegion) := {
  sifiveUartIdx      : nat ;
  sifiveUartBaseAddr : Z ;
  pfBound            : Is_true ((0 <=? sifiveUartBaseAddr) && (sifiveUartBaseAddr + SifiveUartSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  pfAligned          : Is_true (sifiveUartBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes SifiveUartLineConfig)) =? 0)%Z ;
  pfSifiveUart       : nth_error regions sifiveUartIdx = Some (sifiveUartMemRegion sifiveUartBaseAddr pfBound pfAligned)
}.

Definition sifiveUartRegion {regions} (uart : SifiveUartInstance regions) : MemRegion :=
  sifiveUartMemRegion uart.(sifiveUartBaseAddr) uart.(pfBound) uart.(pfAligned).

Section SifiveUartSystem.
  Variable regions : list MemRegion.
  Variable uart : SifiveUartInstance regions.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Definition sifiveUartAction {k : Kind} (act : Action ty sifiveUartTree k) : Action ty memTree k :=
    nthRegionAction uart.(sifiveUartIdx) regions (sifiveUartRegion uart) uart.(pfSifiveUart) act.

  Definition sifiveUartIpStepAction : Action ty memTree (Bit 0) :=
    sifiveUartAction (@sifiveUartIpStep ty).

  Definition sifiveUartDivStepAction : Action ty memTree (Bit 0) :=
    sifiveUartAction (@sifiveUartDivStep ty).

  Definition sifiveUartTxStepAction : Action ty memTree (Bit 0) :=
    sifiveUartAction (@sifiveUartTxStep ty).

  Definition sifiveUartRxStepAction : Action ty memTree (Bit 0) :=
    sifiveUartAction (@sifiveUartRxStep ty).

End SifiveUartSystem.
