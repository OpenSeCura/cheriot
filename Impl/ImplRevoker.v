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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition.
From Cheriot Require Import SpecDefines SpecDevice SpecRevoker FunctionalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Split-Phase Hardware Revoker with Store-Address Snooping
 * =========================================================================== *)

Definition RevPhaseList : list (string * Kind) :=
  [ ("Idle",         Bit 0) ;
    ("WaitCapRp",    Bit 0) ;
    ("WaitRevBitRq", Bit 0) ;
    ("WaitRevBitRp", Bit 0) ;
    ("WriteCap",     Bit 0) ].

Definition RevPhase : Kind := TaggedUnion RevPhaseList.

Notation mkRevPhase tag := (UNION (RevPhaseList, tag ::= Const ltac:(getTy) (Bit 0) Zmod.zero)) (only parsing).

Section ImplRevoker.
  Variable dom : string.

  Definition implRevokerExtraChildren : list (Tree DomainElem) :=
    [ Leaf "revPhase"         (dom, EReg (Build_Reg RevPhase (Some (getDefault _)) false)) ;
      Leaf "revScanCap"       (dom, EReg (Build_Reg FullCapWithTag (Some (getDefault _)) false)) ;
      Leaf "revStoreSnoopHit" (dom, EReg (Build_Reg Bool (Some false) false)) ].

  Definition implRevokerTree : Tree DomainElem :=
    Node "revoker" (revokerChildren dom implRevokerExtraChildren).

  Local Definition pBase               : RegPath implRevokerTree := Eval cbn in (revokerBasePath dom implRevokerExtraChildren).
  Local Definition pTop                : RegPath implRevokerTree := Eval cbn in (revokerTopPath dom implRevokerExtraChildren).
  Local Definition pControl            : RegPath implRevokerTree := Eval cbn in (revokerControlPath dom implRevokerExtraChildren).
  Local Definition pEpoch              : RegPath implRevokerTree := Eval cbn in (revokerEpochPath dom implRevokerExtraChildren).
  Local Definition pInterruptStatus    : RegPath implRevokerTree := Eval cbn in (revokerInterruptStatusPath dom implRevokerExtraChildren).
  Local Definition pInterruptRequested : RegPath implRevokerTree := Eval cbn in (revokerInterruptRequestedPath dom implRevokerExtraChildren).
  Local Definition pScanAddr           : RegPath implRevokerTree := Eval cbn in (revokerScanAddrPath dom implRevokerExtraChildren).
  Local Definition pRevPhase           : RegPath implRevokerTree := Eval cbn in (getChildRegPathTree implRevokerTree "revPhase").
  Local Definition pRevScanCap         : RegPath implRevokerTree := Eval cbn in (getChildRegPathTree implRevokerTree "revScanCap").
  Local Definition pRevStoreSnoopHit   : RegPath implRevokerTree := Eval cbn in (getChildRegPathTree implRevokerTree "revStoreSnoopHit").

  Section Ty.
    Variable ty : Kind -> Type.

    (* Snoop CPU Store address against currently active revoker scanAddr *)
    Definition implRevokerSnoopStore
      (addr : ty Addr)
      (memSize : ty (Bit LgLgNumBytesFullCapSz))
      : Action ty implRevokerTree (Bit 0) :=
      ReadReg "scanAddr" pScanAddr (fun scanAddrMsb =>
      Let stAddrMsb      : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz #addr ;
      Let capOffset      : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz #addr ;
      Let numBytesDXlen  : Bit (LgNumBytesFullCapSz + 1) <-
        Sll $1 (ZeroExtend (LgNumBytesFullCapSz + 1 - LgLgNumBytesFullCapSz) #memSize) ;
      Let endOffsetDXlen : Bit (LgNumBytesFullCapSz + 1) <-
        Add [ ZeroExtend 1 #capOffset ; #numBytesDXlen ] ;
      Let crossesDXlen   : Bool <-
        FromBit Bool (TruncMsb 1 LgNumBytesFullCapSz (Sub #endOffsetDXlen $1)) ;
      Let nextStAddrMsb  : Bit TagAddrWidth <- Add [ #stAddrMsb ; $1 ] ;
      Let hitsScanAddr   : Bool <-
        Or [ Eq #stAddrMsb #scanAddrMsb ;
             And [ #crossesDXlen ; Eq #nextStAddrMsb #scanAddrMsb ] ] ;
      If #hitsScanAddr Then (
        WriteReg pRevStoreSnoopHit (ConstBool true) Retv
      ) ;
      Retv).

    (* Split-Phase Autonomous Revoker Steps *)
    Variable revConfig    : RevConfig.
    Variable memTree      : Tree DomainElem.
    Variable revAct       : forall {k : Kind}, Action ty implRevokerTree k -> Action ty memTree k.
    Variable readMemRq      : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool.
    Variable getMemRp       : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree (Option FullCapWithTag).
    Variable deqMemRp       : ty Addr -> Action ty memTree (Bit 0).
    Variable readRevBitRq   : ty (Bit (AddrSz + 1)) -> Action ty memTree Bool.
    Variable getDeqRevBitRp : ty (Bit (AddrSz + 1)) -> Action ty memTree (Option Bool).
    Variable writeMem       : ty Addr -> ty FullCapWithTag -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool.

    Local Definition advanceScanAndReset (nextScanAddrMsb : ty (Bit TagAddrWidth)) : Action ty memTree (Bit 0) :=
      Act (revAct (WriteReg pScanAddr #nextScanAddrMsb Retv)) ;
      revAct (WriteReg pRevPhase (mkRevPhase "Idle") Retv).

    Definition implRevokerIdle : Action ty memTree (Bit 0) :=
      LetA epoch : Bit Xlen <- revAct (ReadReg "epoch" pEpoch (fun v => Return #v)) ;
      Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;
      If #isOddEpoch Then (
        LetA scanAddrMsb : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" pScanAddr (fun v => Return #v)) ;
        LetA topAddrMsb  : Bit TagAddrWidth <- revAct (ReadReg "top" pTop (fun v => Return #v)) ;
        Let scanAddr     : Addr             <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Let isDone       : Bool             <- Uge #scanAddrMsb #topAddrMsb ;
        If (Not #isDone) Then (
          LetA revPhase : RevPhase <- revAct (ReadReg "revPhase" pRevPhase (fun v => Return #v)) ;
          If (##revPhase `? "Idle") Then (
            Let capSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
            LetA rdy  : Bool                      <- readMemRq scanAddr capSz ;
            If #rdy Then (
              Act (revAct (WriteReg pRevStoreSnoopHit (ConstBool false) Retv)) ;
              revAct (WriteReg pRevPhase (mkRevPhase "WaitCapRp") Retv)
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          (* Sweep complete: scanAddrMsb reached topAddrMsb *)
          Act (revAct (WriteReg pRevPhase (mkRevPhase "Idle") Retv)) ;
          Let nextEpoch : Bit Xlen <- Add [ #epoch ; $1 ] ;
          Act (revAct (WriteReg pEpoch #nextEpoch Retv)) ;
          LetA intReq : Bool <- revAct (ReadReg "interruptRequested" pInterruptRequested (fun v => Return #v)) ;
          If #intReq Then (
            Act (revAct (WriteReg pInterruptStatus (ConstBool true) Retv)) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) Else (
        (* Idle state: epoch is even *)
        Act (revAct (WriteReg pRevPhase (mkRevPhase "Idle") Retv)) ;
        Act (revAct (WriteReg pInterruptStatus (ConstBool false) Retv)) ;
        LetA isKicked : Bool <- revAct (ReadReg "control" pControl (fun v => Return #v)) ;
        If #isKicked Then (
          LetA baseAddrMsb : Bit TagAddrWidth <- revAct (ReadReg "base" pBase (fun v => Return #v)) ;
          Act (revAct (WriteReg pScanAddr #baseAddrMsb Retv)) ;
          Let oddEpoch : Bit Xlen <-
            {< TruncMsb (Xlen - 1) 1 #epoch, Const ty (Bit 1) (bits.of_Z 1 1) >} ;
          Act (revAct (WriteReg pEpoch #oddEpoch Retv)) ;
          Act (revAct (WriteReg pControl (ConstBool false) Retv)) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    Definition implRevokerWaitCapRp : Action ty memTree (Bit 0) :=
      LetA revPhase : RevPhase <- revAct (ReadReg "revPhase" pRevPhase (fun v => Return #v)) ;
      If (##revPhase `? "WaitCapRp") Then (
        LetA scanAddrMsb    : Bit TagAddrWidth          <- revAct (ReadReg "scanAddr" pScanAddr (fun v => Return #v)) ;
        Let scanAddr        : Addr                      <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Let nextScanAddrMsb : Bit TagAddrWidth          <- Add [ #scanAddrMsb ; $1 ] ;
        Let capSz           : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
        LetA rpOpt          : Option FullCapWithTag     <- getMemRp scanAddr capSz ;
        If (##rpOpt`"valid") Then (
          Act (deqMemRp scanAddr) ;
          Let ldFullCap   : FullCapWithTag <- ##rpOpt`"data" ;
          Let ldTag       : Bool           <- ##ldFullCap`"tag" ;
          Let ldCap       : Cap            <- ##ldFullCap`"cap" ;
          Let ldAddr      : Addr           <- ##ldFullCap`"addr" ;
          LetA ldECap     : ECap           <- toAction memTree (DecodeCap ldCap ldAddr) ;
          Let shouldCheck : Bool           <- needsRevocationCheck revConfig ldECap ldTag ;
          If #shouldCheck Then (
            Act (revAct (WriteReg pRevScanCap #ldFullCap Retv)) ;
            revAct (WriteReg pRevPhase (mkRevPhase "WaitRevBitRq") Retv)
          ) Else (
            advanceScanAndReset nextScanAddrMsb
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    Definition implRevokerWaitRevBitRq : Action ty memTree (Bit 0) :=
      LetA revPhase : RevPhase <- revAct (ReadReg "revPhase" pRevPhase (fun v => Return #v)) ;
      If (##revPhase `? "WaitRevBitRq") Then (
        LetA savedCap : FullCapWithTag   <- revAct (ReadReg "savedCap" pRevScanCap (fun v => Return #v)) ;
        Let ldCap     : Cap              <- ##savedCap`"cap" ;
        Let ldAddr    : Addr             <- ##savedCap`"addr" ;
        LetA ldECap   : ECap             <- toAction memTree (DecodeCap ldCap ldAddr) ;
        Let ldBase    : Bit (AddrSz + 1) <- ##ldECap`"base" ;
        LetA rdy      : Bool             <- readRevBitRq ldBase ;
        If #rdy Then (
          revAct (WriteReg pRevPhase (mkRevPhase "WaitRevBitRp") Retv)
        ) ;
        Retv
      ) ;
      Retv.

    Definition implRevokerWaitRevBitRp : Action ty memTree (Bit 0) :=
      LetA revPhase : RevPhase <- revAct (ReadReg "revPhase" pRevPhase (fun v => Return #v)) ;
      If (##revPhase `? "WaitRevBitRp") Then (
        LetA scanAddrMsb    : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" pScanAddr (fun v => Return #v)) ;
        Let nextScanAddrMsb : Bit TagAddrWidth <- Add [ #scanAddrMsb ; $1 ] ;
        LetA savedCap       : FullCapWithTag   <- revAct (ReadReg "savedCap" pRevScanCap (fun v => Return #v)) ;
        Let ldCap           : Cap              <- ##savedCap`"cap" ;
        Let ldAddr          : Addr             <- ##savedCap`"addr" ;
        LetA ldECap         : ECap             <- toAction memTree (DecodeCap ldCap ldAddr) ;
        Let ldBase          : Bit (AddrSz + 1) <- ##ldECap`"base" ;
        LetA revOpt         : Option Bool      <- getDeqRevBitRp ldBase ;
        If (##revOpt`"valid") Then (
          Let revBit : Bool <- ##revOpt`"data" ;
          If #revBit Then (
            revAct (WriteReg pRevPhase (mkRevPhase "WriteCap") Retv)
          ) Else (
            advanceScanAndReset nextScanAddrMsb
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    Definition implRevokerWriteCap : Action ty memTree (Bit 0) :=
      LetA revPhase : RevPhase <- revAct (ReadReg "revPhase" pRevPhase (fun v => Return #v)) ;
      If (##revPhase `? "WriteCap") Then (
        LetA scanAddrMsb    : Bit TagAddrWidth          <- revAct (ReadReg "scanAddr" pScanAddr (fun v => Return #v)) ;
        Let scanAddr        : Addr                      <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
        Let nextScanAddrMsb : Bit TagAddrWidth          <- Add [ #scanAddrMsb ; $1 ] ;
        Let capSz           : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
        LetA snoopHit       : Bool                      <- revAct (ReadReg "snoopHit" pRevStoreSnoopHit (fun v => Return #v)) ;
        If #snoopHit Then (
          advanceScanAndReset nextScanAddrMsb
        ) Else (
          LetA savedCap   : FullCapWithTag <- revAct (ReadReg "savedCap" pRevScanCap (fun v => Return #v)) ;
          Let untaggedCap : FullCapWithTag <- STRUCT {
            "tag"  ::= Const ty Bool false ;
            "cap"  ::= ##savedCap`"cap" ;
            "addr" ::= ##savedCap`"addr"
          } ;
          LetA rdy : Bool <- writeMem scanAddr untaggedCap capSz ;
          If #rdy Then (
            advanceScanAndReset nextScanAddrMsb
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv.

    Definition implRevokerStepsFsm : list (Action ty memTree (Bit 0)) :=
      [ implRevokerIdle ;
        (Act implRevokerWaitCapRp ; implRevokerWaitRevBitRq) ;
        implRevokerWaitRevBitRp ;
        implRevokerWriteCap ].

  End Ty.

End ImplRevoker.

Arguments implRevokerSnoopStore dom [ty] addr memSize.
