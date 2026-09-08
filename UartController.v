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

(* TODO: Fix UART *)

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
 * 16550 UART Register Offsets & Memory Footprint
 * =========================================================================== *)

Definition UartRegNames : list string :=
  [ "rbr_thr_dll" ; "ier_dlm" ; "iir_fcr" ; "lcr" ; "mcr" ; "lsr" ; "msr" ; "scr" ].

Definition uartRegIdx (name : string) :=
  forceOption (getStrIndexOption name UartRegNames).

Definition UartNumRegs : nat := Eval compute in (length UartRegNames).
Definition UartSizeBytes : Z := Eval compute in (Z.of_nat UartNumRegs * NumBytesXlen)%Z.

Definition UartRegIdxWidth : Z := Eval compute in (Z.log2_up (Z.of_nat UartNumRegs)).

Notation uartRegIdxBit name :=
  ($(Z.of_nat (uartRegIdx name))).

Definition UART_RBR_THR_DLL_OFFSET : Z := 0.   (* 0x00: RBR (r), THR (w), DLL (r/w, DLAB=1) *)
Definition UART_IER_DLM_OFFSET     : Z := 4.   (* 0x04: IER (r/w), DLM (r/w, DLAB=1) *)
Definition UART_IIR_FCR_OFFSET     : Z := 8.   (* 0x08: IIR (r), FCR (w) *)
Definition UART_LCR_OFFSET         : Z := 12.  (* 0x0C: Line Control Register (r/w) *)
Definition UART_MCR_OFFSET         : Z := 16.  (* 0x10: Modem Control Register (r/w) *)
Definition UART_LSR_OFFSET         : Z := 20.  (* 0x14: Line Status Register (r) *)
Definition UART_MSR_OFFSET         : Z := 24.  (* 0x18: Modem Status Register (r) *)
Definition UART_SCR_OFFSET         : Z := 28.  (* 0x1C: Scratchpad Register (r/w) *)

Definition UART_IIR_LINE_STATUS  : Z := 6.   (* 0b110: Priority 1 - Receiver Line Status Error *)
Definition UART_IIR_RX_DATA      : Z := 4.   (* 0b100: Priority 2 - Received Data Available *)
Definition UART_IIR_TX_EMPTY     : Z := 2.   (* 0b010: Priority 3 - Transmitter Holding Register Empty *)
Definition UART_IIR_MODEM_STATUS : Z := 0.   (* 0b000: Priority 4 - Modem Status Change *)
Definition UART_IIR_NO_INT       : Z := 1.   (* 0b001: No Interrupt Pending (bit 0 = 1) *)

Definition UartFifoCapacity : nat := 16.

(* ===========================================================================
 * UART Tree Definition
 * =========================================================================== *)

Definition uartChildren : list (Tree Elem) :=
  [ Node "tx" [ fifoTree UartFifoCapacity (Bit 8) ] ;
    Node "rx" [ fifoTree UartFifoCapacity (Bit 8) ] ;
    Leaf "ier_erbfi"   (EReg (Build_Reg Bool (Some false))) ;
    Leaf "ier_etbei"   (EReg (Build_Reg Bool (Some false))) ;
    Leaf "ier_elsi"    (EReg (Build_Reg Bool (Some false))) ;
    Leaf "ier_edssi"   (EReg (Build_Reg Bool (Some false))) ;
    Leaf "fcr_fifo_en" (EReg (Build_Reg Bool (Some false))) ;
    Leaf "lcr_dlab"    (EReg (Build_Reg Bool (Some false))) ;
    Leaf "lcr_cfg"     (EReg (Build_Reg (Bit 7) (Some (bits.of_Z 7 3)))) ;
    Leaf "mcr_dtr"     (EReg (Build_Reg Bool (Some false))) ;
    Leaf "mcr_rts"     (EReg (Build_Reg Bool (Some false))) ;
    Leaf "mcr_out2"    (EReg (Build_Reg Bool (Some false))) ;
    Leaf "mcr_loop"    (EReg (Build_Reg Bool (Some false))) ;
    Leaf "lsr_oe"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "lsr_pe"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "lsr_fe"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "lsr_bi"      (EReg (Build_Reg Bool (Some false))) ;
    Leaf "scr"         (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "dll"         (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "dlm"         (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "txData"      (ESend (Bit 8)) ;
    Leaf "txRdy"       (ERecv Bool) ;
    Leaf "rxData"      (ERecv (Option (Bit 8))) ;
    Leaf "rxRdy"       (ESend (Bit 0))
  ].

Definition uartTree : Tree Elem :=
  Node "uart" uartChildren.

Definition UartLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

(* ===========================================================================
 * Paths & Embeddings
 * =========================================================================== *)

Definition uartIerErbfiPath : RegPath uartTree := getChildRegPathTree uartTree "ier_erbfi".
Definition uartIerEtbeiPath : RegPath uartTree := getChildRegPathTree uartTree "ier_etbei".
Definition uartIerElsiPath  : RegPath uartTree := getChildRegPathTree uartTree "ier_elsi".
Definition uartIerEdssiPath : RegPath uartTree := getChildRegPathTree uartTree "ier_edssi".

Definition uartFcrFifoEnPath: RegPath uartTree := getChildRegPathTree uartTree "fcr_fifo_en".

Definition uartLcrDlabPath  : RegPath uartTree := getChildRegPathTree uartTree "lcr_dlab".
Definition uartLcrCfgPath   : RegPath uartTree := getChildRegPathTree uartTree "lcr_cfg".

Definition uartMcrDtrPath   : RegPath uartTree := getChildRegPathTree uartTree "mcr_dtr".
Definition uartMcrRtsPath   : RegPath uartTree := getChildRegPathTree uartTree "mcr_rts".
Definition uartMcrOut2Path  : RegPath uartTree := getChildRegPathTree uartTree "mcr_out2".
Definition uartMcrLoopPath  : RegPath uartTree := getChildRegPathTree uartTree "mcr_loop".

Definition uartLsrOePath    : RegPath uartTree := getChildRegPathTree uartTree "lsr_oe".
Definition uartLsrPePath    : RegPath uartTree := getChildRegPathTree uartTree "lsr_pe".
Definition uartLsrFePath    : RegPath uartTree := getChildRegPathTree uartTree "lsr_fe".
Definition uartLsrBiPath    : RegPath uartTree := getChildRegPathTree uartTree "lsr_bi".

Definition uartScrPath      : RegPath uartTree := getChildRegPathTree uartTree "scr".
Definition uartDllPath      : RegPath uartTree := getChildRegPathTree uartTree "dll".
Definition uartDlmPath      : RegPath uartTree := getChildRegPathTree uartTree "dlm".

Definition uartTxDataPath   : SendPath uartTree := getChildSendPathTree uartTree "txData".
Definition uartTxRdyPath    : RecvPath uartTree := getChildRecvPathTree uartTree "txRdy".
Definition uartRxDataPath   : RecvPath uartTree := getChildRecvPathTree uartTree "rxData".
Definition uartRxRdyPath    : SendPath uartTree := getChildSendPathTree uartTree "rxRdy".

Definition np_tx_fifo : NodePath uartTree :=
  getNodePath uartTree "uart.tx.fifo".

Definition np_rx_fifo : NodePath uartTree :=
  getNodePath uartTree "uart.rx.fifo".

(* Helper to lift an action across equality of tree nodes *)
Definition liftActionEq {ty : Kind -> Type} {t : Tree Elem} {k : Kind}
  (p : NodePath t) {t' : Tree Elem} (H : getNode p = t') (a : Action ty t' k) : Action ty t k :=
  match H in _ = X return Action ty X k -> Action ty t k with
  | eq_refl => liftAction (ty:=ty) p (k:=k)
  end a.
Arguments liftActionEq [ty t k] p [t'] H a.

(* ===========================================================================
 * UART Internal Operations
 * =========================================================================== *)

Section UartOperations.
  Variable ty : Kind -> Type.

  (* Read RBR: dequeues byte from RX FIFO if available *)
  Definition readRbr : Action ty uartTree (Bit 8) :=
    LetA rxHead : Option (Bit 8) <- liftAction np_rx_fifo (@first UartFifoCapacity (Bit 8) ty) ;
    Let hasData : Bool <- ##rxHead `? "Some" ;
    LetIf rByte : Bit 8 <-
      If #hasData Then (
        Act (liftAction np_rx_fifo (@deq UartFifoCapacity (Bit 8) ty)) ;
        Return (##rxHead `! "Some")
      ) Else (
        Return $0
      ) ;
    Return #rByte.

  (* Write THR: enqueues byte to TX FIFO (or RX FIFO if loopback enabled) *)
  Definition writeThr (dataByte : Expr ty (Bit 8)) : Action ty uartTree (Bit 0) :=
    Let dByte : Bit 8 <- dataByte ;
    LetA isLoopback : Bool <- ReadReg "mcr_loop" uartMcrLoopPath (fun v => Return #v) ;
    If #isLoopback Then (
      LetA rxFull : Bool <- liftAction np_rx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
      If (Not #rxFull) Then (
        liftAction np_rx_fifo (@enq UartFifoCapacity (Bit 8) ty dByte)
      ) ;
      Retv
    ) ;
    If (Not #isLoopback) Then (
      LetA txFull : Bool <- liftAction np_tx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
      If (Not #txFull) Then (
        liftAction np_tx_fifo (@enq UartFifoCapacity (Bit 8) ty dByte)
      ) ;
      Retv
    ) ;
    Retv.

  (* Read IIR: computes highest priority pending interrupt dynamically into a Xlen-bit word *)
  Definition readIir : Action ty uartTree (Bit Xlen) :=
    LetA is_rx_empty : Bool <- liftAction np_rx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA is_tx_empty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA erbfi       : Bool <- ReadReg "ier_erbfi" uartIerErbfiPath (fun v => Return #v) ;
    LetA etbei       : Bool <- ReadReg "ier_etbei" uartIerEtbeiPath (fun v => Return #v) ;
    LetA elsi        : Bool <- ReadReg "ier_elsi" uartIerElsiPath (fun v => Return #v) ;
    LetA edssi       : Bool <- ReadReg "ier_edssi" uartIerEdssiPath (fun v => Return #v) ;
    LetA oe          : Bool <- ReadReg "lsr_oe" uartLsrOePath (fun v => Return #v) ;
    LetA pe          : Bool <- ReadReg "lsr_pe" uartLsrPePath (fun v => Return #v) ;
    LetA fe          : Bool <- ReadReg "lsr_fe" uartLsrFePath (fun v => Return #v) ;
    LetA bi          : Bool <- ReadReg "lsr_bi" uartLsrBiPath (fun v => Return #v) ;
    LetA fifo_en     : Bool <- ReadReg "fcr_fifo_en" uartFcrFifoEnPath (fun v => Return #v) ;
    Let hasLineErr   : Bool <- Or [ #oe ; #pe ; #fe ; #bi ] ;
    Let p1 : Bool <- And [ #hasLineErr ; #elsi ] ;
    Let p2 : Bool <- And [ Not #is_rx_empty ; #erbfi ] ;
    Let p3 : Bool <- And [ #is_tx_empty ; #etbei ] ;
    Let p4 : Bool <- #edssi ;
    Let iir_val : Bit 3 <-
      ITE #p1 $(UART_IIR_LINE_STATUS)
        (ITE #p2 $(UART_IIR_RX_DATA)
          (ITE #p3 $(UART_IIR_TX_EMPTY)
            (ITE #p4 $(UART_IIR_MODEM_STATUS) $(UART_IIR_NO_INT)))) ;
    Let iir_fifo : Bit 2 <- ITE #fifo_en $3 $0 ;
    Return {< Const ty (Bit (Xlen - 8)) Zmod.zero, #iir_fifo, Const ty (Bit 3) Zmod.zero, #iir_val >}.

  (* Read LSR: returns status and clears sticky error bits *)
  Definition readLsr : Action ty uartTree (Bit Xlen) :=
    LetA is_rx_empty : Bool <- liftAction np_rx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA is_tx_empty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA oe          : Bool <- ReadReg "lsr_oe" uartLsrOePath (fun v => Return #v) ;
    LetA pe          : Bool <- ReadReg "lsr_pe" uartLsrPePath (fun v => Return #v) ;
    LetA fe          : Bool <- ReadReg "lsr_fe" uartLsrFePath (fun v => Return #v) ;
    LetA bi          : Bool <- ReadReg "lsr_bi" uartLsrBiPath (fun v => Return #v) ;
    Act (WriteReg uartLsrOePath (ConstBool false) Retv) ;
    Act (WriteReg uartLsrPePath (ConstBool false) Retv) ;
    Act (WriteReg uartLsrFePath (ConstBool false) Retv) ;
    Act (WriteReg uartLsrBiPath (ConstBool false) Retv) ;
    Let anyErr : Bool <- Or [ #oe ; #pe ; #fe ; #bi ] ;
    Let dr : Bool <- Not #is_rx_empty ;
    Let thre : Bool <- #is_tx_empty ;
    Let temt : Bool <- #is_tx_empty ;
    Return {< Const ty (Bit (Xlen - 8)) Zmod.zero,
              ToBit #anyErr, ToBit #temt, ToBit #thre,
              ToBit #bi, ToBit #fe, ToBit #pe, ToBit #oe, ToBit #dr >}.

  (* UART Interrupt Output: evaluated for PLIC connection *)
  Definition uartIrq : Action ty uartTree Bool :=
    LetA is_rx_empty : Bool <- liftAction np_rx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA is_tx_empty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA erbfi       : Bool <- ReadReg "ier_erbfi" uartIerErbfiPath (fun v => Return #v) ;
    LetA etbei       : Bool <- ReadReg "ier_etbei" uartIerEtbeiPath (fun v => Return #v) ;
    LetA elsi        : Bool <- ReadReg "ier_elsi" uartIerElsiPath (fun v => Return #v) ;
    LetA edssi       : Bool <- ReadReg "ier_edssi" uartIerEdssiPath (fun v => Return #v) ;
    LetA oe          : Bool <- ReadReg "lsr_oe" uartLsrOePath (fun v => Return #v) ;
    LetA pe          : Bool <- ReadReg "lsr_pe" uartLsrPePath (fun v => Return #v) ;
    LetA fe          : Bool <- ReadReg "lsr_fe" uartLsrFePath (fun v => Return #v) ;
    LetA bi          : Bool <- ReadReg "lsr_bi" uartLsrBiPath (fun v => Return #v) ;
    LetA out2        : Bool <- ReadReg "mcr_out2" uartMcrOut2Path (fun v => Return #v) ;
    Let hasLineErr   : Bool <- Or [ #oe ; #pe ; #fe ; #bi ] ;
    Let p1 : Bool <- And [ #hasLineErr ; #elsi ] ;
    Let p2 : Bool <- And [ Not #is_rx_empty ; #erbfi ] ;
    Let p3 : Bool <- And [ #is_tx_empty ; #etbei ] ;
    Let p4 : Bool <- #edssi ;
    Let any_irq : Bool <- Or [ #p1 ; #p2 ; #p3 ; #p4 ] ;
    Return (And [ #any_irq ; Or [ #out2 ; ConstBool true ] ]).

  (* =========================================================================
   * 4 Decoupled Hardware Rules for Streaming PHY Interface
   * ========================================================================= *)

  (* TX Rule 1: Always presents data onto txData whenever TX FIFO is not empty *)
  Definition uartTxDataStep : Action ty uartTree (Bit 0) :=
    LetA txEmpty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    If (Not #txEmpty) Then (
      LetA txHead : Option (Bit 8) <- liftAction np_tx_fifo (@first UartFifoCapacity (Bit 8) ty) ;
      Let hasData : Bool <- ##txHead `? "Some" ;
      If #hasData Then (
        Let txByte : Bit 8 <- ##txHead `! "Some" ;
        Act (Send uartTxDataPath #txByte Retv) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  (* TX Rule 2: Samples txRdy; if ready and TX FIFO is not empty, dequeues *)
  Definition uartTxDeqStep : Action ty uartTree (Bit 0) :=
    Recv "txRdy" uartTxRdyPath (fun txRdy =>
      If #txRdy Then (
        LetA txEmpty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
        If (Not #txEmpty) Then (
          liftAction np_tx_fifo (@deq UartFifoCapacity (Bit 8) ty)
        ) ;
        Retv
      ) ;
      Retv
    ).

  (* RX Rule 3: Always sends rxRdy whenever RX FIFO is not full *)
  Definition uartRxRdyStep : Action ty uartTree (Bit 0) :=
    LetA rxFull : Bool <- liftAction np_rx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
    If (Not #rxFull) Then (
      Act (Send uartRxRdyPath (Const ty (Bit 0) Zmod.zero) Retv) ;
      Retv
    ) ;
    Retv.

  (* RX Rule 4: Samples rxData; enqueues if not full, flags overrun error if full *)
  Definition uartRxDataStep : Action ty uartTree (Bit 0) :=
    Recv "rxData" uartRxDataPath (fun rxOpt =>
      Let hasData : Bool <- ##rxOpt `? "Some" ;
      If #hasData Then (
        Let rxByte : Bit 8 <- ##rxOpt `! "Some" ;
        LetA rxFull : Bool <- liftAction np_rx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
        If (Not #rxFull) Then (
          Act (liftAction np_rx_fifo (@enq UartFifoCapacity (Bit 8) ty rxByte)) ;
          Retv
        ) Else (
          Act (WriteReg uartLsrOePath (ConstBool true) Retv) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ).

End UartOperations.

Arguments readRbr {ty}.
Arguments readIir {ty}.
Arguments readLsr {ty}.
Arguments uartIrq {ty}.
Arguments uartTxDataStep {ty}.
Arguments uartTxDeqStep {ty}.
Arguments uartRxRdyStep {ty}.
Arguments uartRxDataStep {ty}.
Arguments writeThr [ty] dataByte.

(* ===========================================================================
 * MMIO Line Read & Write Actions
 * =========================================================================== *)

Definition uartLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty uartTree (LineReadRp UartLineConfig) :=
  Let offset <- getMemOffset base UartSizeBytes addr ;
  Let regIdx : Bit UartRegIdxWidth <- TruncMsb UartRegIdxWidth LgNumBytesXlen #offset ;
  LetA dlab : Bool <- ReadReg "lcr_dlab" uartLcrDlabPath (fun v => Return #v) ;
  Let isRbr : Bool <- And [ Eq #regIdx (uartRegIdxBit "rbr_thr_dll") ; Not #dlab ] ;
  Let isLsr : Bool <- Eq #regIdx (uartRegIdxBit "lsr") ;
  Let isIir : Bool <- Eq #regIdx (uartRegIdxBit "iir_fcr") ;
  LetIf rbrByte : Bit 8 <-
    If #isRbr Then readRbr Else (Return $0) ;
  LetIf lsrWord : Bit Xlen <-
    If #isLsr Then readLsr Else (Return $0) ;
  LetIf iirWord : Bit Xlen <-
    If #isIir Then readIir Else (Return $0) ;
  ReadReg "ier_erbfi" uartIerErbfiPath (fun erbfi =>
  ReadReg "ier_etbei" uartIerEtbeiPath (fun etbei =>
  ReadReg "ier_elsi"  uartIerElsiPath  (fun elsi =>
  ReadReg "ier_edssi" uartIerEdssiPath (fun edssi =>
  ReadReg "lcr_cfg"   uartLcrCfgPath   (fun lcrCfg =>
  ReadReg "mcr_dtr"   uartMcrDtrPath   (fun dtr =>
  ReadReg "mcr_rts"   uartMcrRtsPath   (fun rts =>
  ReadReg "mcr_out2"  uartMcrOut2Path  (fun out2 =>
  ReadReg "mcr_loop"  uartMcrLoopPath  (fun loop =>
  ReadReg "scr"       uartScrPath      (fun scrVal =>
  ReadReg "dll"       uartDllPath      (fun dllVal =>
  ReadReg "dlm"       uartDlmPath      (fun dlmVal =>
  Let ierWord : Bit Xlen <- {< Const ty (Bit (Xlen - 4)) Zmod.zero, ToBit #edssi, ToBit #elsi, ToBit #etbei, ToBit #erbfi >} ;
  Let lcrWord : Bit Xlen <- {< Const ty (Bit (Xlen - 8)) Zmod.zero, ToBit #dlab, #lcrCfg >} ;
  Let mcrWord : Bit Xlen <- {< Const ty (Bit (Xlen - 5)) Zmod.zero, ToBit #loop, ToBit #out2, Const ty (Bit 1) Zmod.zero, ToBit #rts, ToBit #dtr >} ;
  Let msrWord : Bit Xlen <- Const ty (Bit Xlen) (bits.of_Z Xlen 176) ;
  Let readWord : Bit Xlen <-
    Or [ ITE0 #isRbr (ZeroExtendTo Xlen #rbrByte) ;
         ITE0 (And [ Eq #regIdx (uartRegIdxBit "rbr_thr_dll") ; #dlab ]) (ZeroExtendTo Xlen #dllVal) ;
         ITE0 (And [ Eq #regIdx (uartRegIdxBit "ier_dlm") ; Not #dlab ]) #ierWord ;
         ITE0 (And [ Eq #regIdx (uartRegIdxBit "ier_dlm") ; #dlab ]) (ZeroExtendTo Xlen #dlmVal) ;
         ITE0 #isIir #iirWord ;
         ITE0 (Eq #regIdx (uartRegIdxBit "lcr")) #lcrWord ;
         ITE0 (Eq #regIdx (uartRegIdxBit "mcr")) #mcrWord ;
         ITE0 #isLsr #lsrWord ;
         ITE0 (Eq #regIdx (uartRegIdxBit "msr")) #msrWord ;
         ITE0 (Eq #regIdx (uartRegIdxBit "scr")) (ZeroExtendTo Xlen #scrVal) ] ;
  Let dataArr : Array (cfgLineBytes UartLineConfig) (Bit 8) <-
    FromBit (Array (cfgLineBytes UartLineConfig) (Bit 8)) #readWord ;
  @Return ty uartTree (LineReadRp UartLineConfig) (STRUCT {
    "data" ::= #dataArr ;
    "tag"  ::= Const ty (Array (cfgNumLineTags UartLineConfig) Bool) (getDefault _)
  }))))))))))))).

Definition uartLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq UartLineConfig))
           : Action ty uartTree (Bit 0) :=
  Let offset <- getMemOffset base UartSizeBytes (rq`"addr") ;
  Let regIdx : Bit UartRegIdxWidth <- TruncMsb UartRegIdxWidth LgNumBytesXlen #offset ;
  Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
  Let writeBits : Array (Z.to_nat Xlen) Bool <-
    FromBit (Array (Z.to_nat Xlen) Bool) #writeWord ;
  Let dataByte : Bit 8 <- TruncLsb (Xlen - 8) 8 #writeWord ;
  LetA dlab : Bool <- ReadReg "lcr_dlab" uartLcrDlabPath (fun v => Return #v) ;
  If (And [ Eq #regIdx (uartRegIdxBit "rbr_thr_dll") ; #dlab ]) Then (
    WriteReg uartDllPath #dataByte Retv
  ) ;
  If (And [ Eq #regIdx (uartRegIdxBit "rbr_thr_dll") ; Not #dlab ]) Then (
    writeThr #dataByte
  ) ;
  If (And [ Eq #regIdx (uartRegIdxBit "ier_dlm") ; #dlab ]) Then (
    WriteReg uartDlmPath #dataByte Retv
  ) ;
  If (And [ Eq #regIdx (uartRegIdxBit "ier_dlm") ; Not #dlab ]) Then (
    WriteReg uartIerErbfiPath (##writeBits$[0]) (
    WriteReg uartIerEtbeiPath (##writeBits$[1]) (
    WriteReg uartIerElsiPath  (##writeBits$[2]) (
    WriteReg uartIerEdssiPath (##writeBits$[3]) Retv)))
  ) ;
  If (Eq #regIdx (uartRegIdxBit "iir_fcr")) Then (
    Act (WriteReg uartFcrFifoEnPath (##writeBits$[0]) Retv) ;
    If (##writeBits$[1]) Then (
      liftAction np_rx_fifo (@clear UartFifoCapacity (Bit 8) ty)
    ) ;
    If (##writeBits$[2]) Then (
      liftAction np_tx_fifo (@clear UartFifoCapacity (Bit 8) ty)
    ) ;
    Retv
  ) ;
  If (Eq #regIdx (uartRegIdxBit "lcr")) Then (
    WriteReg uartLcrDlabPath (##writeBits$[7]) (
    WriteReg uartLcrCfgPath (TruncLsb (Xlen - 7) 7 #writeWord) Retv)
  ) ;
  If (Eq #regIdx (uartRegIdxBit "mcr")) Then (
    WriteReg uartMcrDtrPath  (##writeBits$[0]) (
    WriteReg uartMcrRtsPath  (##writeBits$[1]) (
    WriteReg uartMcrOut2Path (##writeBits$[3]) (
    WriteReg uartMcrLoopPath (##writeBits$[4]) Retv)))
  ) ;
  If (Eq #regIdx (uartRegIdxBit "scr")) Then (
    WriteReg uartScrPath #dataByte Retv
  ) ;
  Retv.

Arguments uartLineReadAction base ty addr : clear implicits.
Arguments uartLineWriteAction base ty rq : clear implicits.

(* ===========================================================================
 * MemRegion Constructor
 * =========================================================================== *)

Definition uartMemRegion
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + UartSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes UartLineConfig)) =? 0)%Z)
           : MemRegion := {|
  regionName        := "uart" ;
  regionBase        := base ;
  regionSize        := UartSizeBytes ;
  regionLineCfg     := UartLineConfig ;
  isReadOnly        := false ;
  regionKind        := @CustomMem "uart" UartSizeBytes UartLineConfig
                                  uartChildren
                                  (uartLineReadAction base)
                                  (uartLineWriteAction base)
                                  (Some (fun ty => uartIrq (ty:=ty))) ;
  regionInMemory    := pfBound ;
  regionBaseAligned := pfAligned ;
  regionSizeAligned := I
|}.

Arguments uartMemRegion base pfBound pfAligned : clear implicits.

(* ===========================================================================
 * System Integration Helpers
 * =========================================================================== *)

Record UartInstance (regions : list MemRegion) := {
  uartIdx      : nat ;
  uartBaseAddr : Z ;
  pfBound      : Is_true ((0 <=? uartBaseAddr) && (uartBaseAddr + UartSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  pfAligned    : Is_true (uartBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes UartLineConfig)) =? 0)%Z ;
  pfUart       : nth_error regions uartIdx = Some (uartMemRegion uartBaseAddr pfBound pfAligned)
}.

Definition uartRegion {regions} (uart : UartInstance regions) : MemRegion :=
  uartMemRegion uart.(uartBaseAddr) uart.(pfBound) uart.(pfAligned).

Section UartSystem.
  Variable regions : list MemRegion.
  Variable uart : UartInstance regions.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Definition uartAction {k : Kind} (act : Action ty uartTree k) : Action ty memTree k :=
    nthRegionAction uart.(uartIdx) regions (uartRegion uart) uart.(pfUart) act.

  Definition uartTxDataStepAction : Action ty memTree (Bit 0) :=
    uartAction (@uartTxDataStep ty).

  Definition uartTxDeqStepAction : Action ty memTree (Bit 0) :=
    uartAction (@uartTxDeqStep ty).

  Definition uartRxRdyStepAction : Action ty memTree (Bit 0) :=
    uartAction (@uartRxRdyStep ty).

  Definition uartRxDataStepAction : Action ty memTree (Bit 0) :=
    uartAction (@uartRxDataStep ty).

End UartSystem.
