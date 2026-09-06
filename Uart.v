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

(* TODO:
 * fix Uart
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
 * 16550 UART Register Offsets & Memory Footprint
 * =========================================================================== *)

Definition UartRegNames : list string :=
  [ "rbr_thr_dll" ; "ier_dlm" ; "iir_fcr" ; "lcr" ; "mcr" ; "lsr" ; "msr" ; "scr" ].

Definition uartRegIdx (name : string) :=
  forceOption (getStrIndexOption name UartRegNames).

Definition UartNumRegs : nat := Eval compute in (length UartRegNames).
Definition UartSizeBytes : Z := Eval compute in (Z.of_nat UartNumRegs * NumBytesXlen)%Z.

Definition UART_RBR_THR_DLL_OFFSET : Z := 0.   (* 0x00: RBR (r), THR (w), DLL (r/w, DLAB=1) *)
Definition UART_IER_DLM_OFFSET     : Z := 4.   (* 0x04: IER (r/w), DLM (r/w, DLAB=1) *)
Definition UART_IIR_FCR_OFFSET     : Z := 8.   (* 0x08: IIR (r), FCR (w) *)
Definition UART_LCR_OFFSET         : Z := 12.  (* 0x0C: Line Control Register (r/w) *)
Definition UART_MCR_OFFSET         : Z := 16.  (* 0x10: Modem Control Register (r/w) *)
Definition UART_LSR_OFFSET         : Z := 20.  (* 0x14: Line Status Register (r) *)
Definition UART_MSR_OFFSET         : Z := 24.  (* 0x18: Modem Status Register (r) *)
Definition UART_SCR_OFFSET         : Z := 28.  (* 0x1C: Scratchpad Register (r/w) *)

Definition UartFifoCapacity : nat := 16.

(* ===========================================================================
 * UART Tree Definition
 * =========================================================================== *)

Definition uartChildren : list (Tree Elem) :=
  [ Node "tx" [ fifoTree UartFifoCapacity (Bit 8) ] ;
    Node "rx" [ fifoTree UartFifoCapacity (Bit 8) ] ;
    Leaf "ier" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "fcr" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "lcr" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "mcr" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "lsr_err" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "msr" (EReg (Build_Reg (Bit 8) (Some (bits.of_Z 8 176)))) ;
    Leaf "scr" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "dll" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "dlm" (EReg (Build_Reg (Bit 8) (Some Zmod.zero))) ;
    Leaf "tx_byte" (ESend (Bit 8)) ;
    Leaf "rx_byte" (ERecv (Bit 8))
  ].

Definition uartTree : Tree Elem :=
  Node "uart" uartChildren.

Definition UartLineConfig : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

(* ===========================================================================
 * Paths & Embeddings
 * =========================================================================== *)

Definition uartIerPath    : RegPath uartTree := getChildRegPathTree uartTree "ier".
Definition uartFcrPath    : RegPath uartTree := getChildRegPathTree uartTree "fcr".
Definition uartLcrPath    : RegPath uartTree := getChildRegPathTree uartTree "lcr".
Definition uartMcrPath    : RegPath uartTree := getChildRegPathTree uartTree "mcr".
Definition uartLsrErrPath : RegPath uartTree := getChildRegPathTree uartTree "lsr_err".
Definition uartMsrPath    : RegPath uartTree := getChildRegPathTree uartTree "msr".
Definition uartScrPath    : RegPath uartTree := getChildRegPathTree uartTree "scr".
Definition uartDllPath    : RegPath uartTree := getChildRegPathTree uartTree "dll".
Definition uartDlmPath    : RegPath uartTree := getChildRegPathTree uartTree "dlm".
Definition uartTxBytePath : SendPath uartTree := getChildSendPathTree uartTree "tx_byte".
Definition uartRxBytePath : RecvPath uartTree := getChildRecvPathTree uartTree "rx_byte".

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

  (* Check if DLAB (Divisor Latch Access Bit) is set in LCR (bit 7) *)
  Definition isDlabSet (lcrVal : Expr ty (Bit 8)) : Expr ty Bool :=
    isNotZero (And [ lcrVal ; $128 ]).

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
    Let byteVal : Bit 8 <- dataByte ;
    LetA mcr : Bit 8 <- ReadReg "mcr" uartMcrPath (fun v => Return #v) ;
    Let isLoopback : Bool <- isNotZero (And [ #mcr ; $16 ]) ;
    If #isLoopback Then (
      LetA rxFull : Bool <- liftAction np_rx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
      If (Not #rxFull) Then (
        liftAction np_rx_fifo (@enq UartFifoCapacity (Bit 8) ty byteVal)
      ) ;
      Retv
    ) ;
    If (Not #isLoopback) Then (
      LetA txFull : Bool <- liftAction np_tx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
      If (Not #txFull) Then (
        liftAction np_tx_fifo (@enq UartFifoCapacity (Bit 8) ty byteVal)
      ) ;
      Retv
    ) ;
    Retv.

  (* Write FCR: writes configuration and resets FIFOs if requested *)
  Definition writeFcr (dataByte : Expr ty (Bit 8)) : Action ty uartTree (Bit 0) :=
    Act (WriteReg uartFcrPath dataByte Retv) ;
    Let rxReset : Bool <- isNotZero (And [ dataByte ; $2 ]) ;
    If #rxReset Then (
      liftAction np_rx_fifo (@clear UartFifoCapacity (Bit 8) ty)
    ) ;
    Let txReset : Bool <- isNotZero (And [ dataByte ; $4 ]) ;
    If #txReset Then (
      liftAction np_tx_fifo (@clear UartFifoCapacity (Bit 8) ty)
    ) ;
    Retv.

  (* Read IIR: computes highest priority pending interrupt combinatorially *)
  Definition readIir : Action ty uartTree (Bit 8) :=
    LetA is_rx_empty : Bool <- liftAction np_rx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA is_tx_empty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA ier         : Bit 8 <- ReadReg "ier" uartIerPath (fun v => Return #v) ;
    LetA lsr_err     : Bit 8 <- ReadReg "lsr_err" uartLsrErrPath (fun v => Return #v) ;
    LetA fcr         : Bit 8 <- ReadReg "fcr" uartFcrPath (fun v => Return #v) ;
    Let p1 : Bool <- And [ isNotZero (And [ #lsr_err ; $30 ]) ; isNotZero (And [ #ier ; $4 ]) ] ;
    Let p2 : Bool <- And [ Not #is_rx_empty ; isNotZero (And [ #ier ; $1 ]) ] ;
    Let p3 : Bool <- And [ #is_tx_empty ; isNotZero (And [ #ier ; $2 ]) ] ;
    Let p4 : Bool <- isNotZero (And [ #ier ; $8 ]) ;
    Let iir_val : Bit 8 <-
      ITE #p1 $6
        (ITE #p2 $4
          (ITE #p3 $2
            (ITE #p4 $0 $1))) ;
    Let is_fifo_en : Bool <- isNotZero (And [ #fcr ; $1 ]) ;
    Let iir_fifo : Bit 8 <- ITE #is_fifo_en $192 $0 ;
    Return (Or [ #iir_val ; #iir_fifo ]).

  (* Read LSR: returns status and clears sticky error bits *)
  Definition readLsr : Action ty uartTree (Bit 8) :=
    LetA is_rx_empty : Bool <- liftAction np_rx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA is_tx_empty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA lsr_err     : Bit 8 <- ReadReg "lsr_err" uartLsrErrPath (fun v => Return #v) ;
    Act (WriteReg uartLsrErrPath $0 Retv) ;
    Let dr_bit   : Bit 8 <- ITE (Not #is_rx_empty) $1 $0 ;
    Let thre_bit : Bit 8 <- ITE #is_tx_empty $32 $0 ;
    Let temt_bit : Bit 8 <- ITE #is_tx_empty $64 $0 ;
    Return (Or [ #dr_bit ; #lsr_err ; #thre_bit ; #temt_bit ]).

  (* UART Interrupt Output: evaluated for PLIC connection *)
  Definition uartIrq : Action ty uartTree Bool :=
    LetA is_rx_empty : Bool <- liftAction np_rx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA is_tx_empty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    LetA ier         : Bit 8 <- ReadReg "ier" uartIerPath (fun v => Return #v) ;
    LetA lsr_err     : Bit 8 <- ReadReg "lsr_err" uartLsrErrPath (fun v => Return #v) ;
    LetA mcr         : Bit 8 <- ReadReg "mcr" uartMcrPath (fun v => Return #v) ;
    Let p1 : Bool <- And [ isNotZero (And [ #lsr_err ; $30 ]) ; isNotZero (And [ #ier ; $4 ]) ] ;
    Let p2 : Bool <- And [ Not #is_rx_empty ; isNotZero (And [ #ier ; $1 ]) ] ;
    Let p3 : Bool <- And [ #is_tx_empty ; isNotZero (And [ #ier ; $2 ]) ] ;
    Let p4 : Bool <- isNotZero (And [ #ier ; $8 ]) ;
    Let any_irq : Bool <- Or [ #p1 ; #p2 ; #p3 ; #p4 ] ;
    Let out2    : Bool <- isNotZero (And [ #mcr ; $8 ]) ;
    Return (And [ #any_irq ; Or [ #out2 ; ConstBool true ] ]).

  (* External Transmit Step: sends dequeued byte from TX FIFO out on tx_byte channel *)
  Definition uartTxStep : Action ty uartTree (Bit 0) :=
    LetA txEmpty : Bool <- liftAction np_tx_fifo (@isEmpty UartFifoCapacity (Bit 8) ty) ;
    If (Not #txEmpty) Then (
      LetA txHead : Option (Bit 8) <- liftAction np_tx_fifo (@first UartFifoCapacity (Bit 8) ty) ;
      Let hasData : Bool <- ##txHead `? "Some" ;
      If #hasData Then (
        Let txByte : Bit 8 <- ##txHead `! "Some" ;
        Act (Send uartTxBytePath #txByte Retv) ;
        liftAction np_tx_fifo (@deq UartFifoCapacity (Bit 8) ty)
      ) ;
      Retv
    ) ;
    Retv.

  (* External Receive Step: receives byte on rx_byte channel and enqueues into RX FIFO *)
  Definition uartRxStep : Action ty uartTree (Bit 0) :=
    Recv "rx_byte" uartRxBytePath (fun byte =>
      LetA rxFull : Bool <- liftAction np_rx_fifo (@isFull UartFifoCapacity (Bit 8) ty) ;
      If (Not #rxFull) Then (
        Act (liftAction np_rx_fifo (@enq UartFifoCapacity (Bit 8) ty byte)) ;
        Retv
      ) ;
      If #rxFull Then (
        LetA curErr : Bit 8 <- ReadReg "lsr_err" uartLsrErrPath (fun v => Return #v) ;
        Let newErr : Bit 8 <- Or [ #curErr ; $2 ] ;
        WriteReg uartLsrErrPath #newErr Retv
      ) ;
      Retv
    ).

End UartOperations.

Arguments readRbr {ty}.
Arguments readIir {ty}.
Arguments readLsr {ty}.
Arguments uartIrq {ty}.
Arguments uartTxStep {ty}.
Arguments uartRxStep {ty}.
Arguments writeThr [ty] dataByte.
Arguments writeFcr [ty] dataByte.

(* ===========================================================================
 * MMIO Line Read & Write Actions
 * =========================================================================== *)

Definition uartLineReadAction
           (base : Z)
           (ty : Kind -> Type)
           (addr : Expr ty Addr)
           : Action ty uartTree (LineReadRp UartLineConfig) :=
  Let rawOffset : Addr <- Sub addr $(base) ;
  Let offset : Addr <- {< TruncMsb (AddrSz - 2) 2 #rawOffset, Const ty (Bit 2) Zmod.zero >} ;
  LetA lcrVal : Bit 8 <- ReadReg "lcr" uartLcrPath (fun v => Return #v) ;
  Let dlab : Bool <- isDlabSet #lcrVal ;
  Let isRbrThrDll : Bool <- Eq #offset $(UART_RBR_THR_DLL_OFFSET) ;
  Let isIerDlm    : Bool <- Eq #offset $(UART_IER_DLM_OFFSET) ;
  Let isIirFcr    : Bool <- Eq #offset $(UART_IIR_FCR_OFFSET) ;
  Let isLcr       : Bool <- Eq #offset $(UART_LCR_OFFSET) ;
  Let isMcr       : Bool <- Eq #offset $(UART_MCR_OFFSET) ;
  Let isLsr       : Bool <- Eq #offset $(UART_LSR_OFFSET) ;
  Let isMsr       : Bool <- Eq #offset $(UART_MSR_OFFSET) ;
  Let isScr       : Bool <- Eq #offset $(UART_SCR_OFFSET) ;
  LetIf rVal8 : Bit 8 <-
    If #isRbrThrDll Then (
      LetIf rRbrDll : Bit 8 <-
        If #dlab Then (
          ReadReg "dll" uartDllPath (fun v => Return #v)
        ) Else (
          readRbr
        ) ;
      Return #rRbrDll
    ) Else (
      LetIf rValIerDlm : Bit 8 <-
        If #isIerDlm Then (
          LetIf rIerDlm : Bit 8 <-
            If #dlab Then (
              ReadReg "dlm" uartDlmPath (fun v => Return #v)
            ) Else (
              ReadReg "ier" uartIerPath (fun v => Return #v)
            ) ;
          Return #rIerDlm
        ) Else (
          LetIf rValIir : Bit 8 <-
            If #isIirFcr Then (
              readIir
            ) Else (
              LetIf rValLcr : Bit 8 <-
                If #isLcr Then (
                  Return #lcrVal
                ) Else (
                  LetIf rValMcr : Bit 8 <-
                    If #isMcr Then (
                      ReadReg "mcr" uartMcrPath (fun v => Return #v)
                    ) Else (
                      LetIf rValLsr : Bit 8 <-
                        If #isLsr Then (
                          readLsr
                        ) Else (
                          LetIf rValMsr : Bit 8 <-
                            If #isMsr Then (
                              ReadReg "msr" uartMsrPath (fun v => Return #v)
                            ) Else (
                              LetIf rValScr : Bit 8 <-
                                If #isScr Then (
                                  ReadReg "scr" uartScrPath (fun v => Return #v)
                                ) Else (
                                  Return $0
                                ) ;
                              Return #rValScr
                            ) ;
                          Return #rValMsr
                        ) ;
                      Return #rValLsr
                    ) ;
                  Return #rValMcr
                ) ;
              Return #rValLcr
            ) ;
          Return #rValIir
        ) ;
      Return #rValIerDlm
    ) ;
  Let rValXlen : Bit Xlen <- ZeroExtend (Xlen - 8) #rVal8 ;
  Let dataArr : Array (cfgLineBytes UartLineConfig) (Bit 8) <-
    FromBit (Array (cfgLineBytes UartLineConfig) (Bit 8)) #rValXlen ;
  @Return ty uartTree (LineReadRp UartLineConfig) (STRUCT {
    "data" ::= #dataArr ;
    "tag"  ::= Const ty (Array (cfgNumLineTags UartLineConfig) Bool) (getDefault _)
  }).

Definition uartLineWriteAction
           (base : Z)
           (ty : Kind -> Type)
           (rq : Expr ty (LineWriteRq UartLineConfig))
           : Action ty uartTree (Bit 0) :=
  Let rawOffset : Addr <- Sub (rq`"addr") $(base) ;
  Let offset : Addr <- {< TruncMsb (AddrSz - 2) 2 #rawOffset, Const ty (Bit 2) Zmod.zero >} ;
  Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
  Let dataByte  : Bit 8    <- TruncLsb 24 8 #writeWord ;
  LetA lcrVal   : Bit 8    <- ReadReg "lcr" uartLcrPath (fun v => Return #v) ;
  Let dlab : Bool <- isDlabSet #lcrVal ;
  Let isRbrThrDll : Bool <- Eq #offset $(UART_RBR_THR_DLL_OFFSET) ;
  Let isIerDlm    : Bool <- Eq #offset $(UART_IER_DLM_OFFSET) ;
  Let isIirFcr    : Bool <- Eq #offset $(UART_IIR_FCR_OFFSET) ;
  Let isLcr       : Bool <- Eq #offset $(UART_LCR_OFFSET) ;
  Let isMcr       : Bool <- Eq #offset $(UART_MCR_OFFSET) ;
  Let isScr       : Bool <- Eq #offset $(UART_SCR_OFFSET) ;
  If (And [ #isRbrThrDll ; #dlab ]) Then (
    WriteReg uartDllPath #dataByte Retv
  ) ;
  If (And [ #isRbrThrDll ; Not #dlab ]) Then (
    writeThr #dataByte
  ) ;
  If (And [ #isIerDlm ; #dlab ]) Then (
    WriteReg uartDlmPath #dataByte Retv
  ) ;
  If (And [ #isIerDlm ; Not #dlab ]) Then (
    WriteReg uartIerPath #dataByte Retv
  ) ;
  If #isIirFcr Then (
    writeFcr #dataByte
  ) ;
  If #isLcr Then (
    WriteReg uartLcrPath #dataByte Retv
  ) ;
  If #isMcr Then (
    WriteReg uartMcrPath #dataByte Retv
  ) ;
  If #isScr Then (
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

  Definition uartTxStepAction : Action ty memTree (Bit 0) :=
    uartAction (@uartTxStep ty).

  Definition uartRxStepAction : Action ty memTree (Bit 0) :=
    uartAction (@uartRxStep ty).

End UartSystem.
