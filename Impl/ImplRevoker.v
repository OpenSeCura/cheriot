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
From Guru Require Import Syntax Notations Semantics Library Composition.
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

Section ImplRevoker.
  Variable dom : string.
  Variable ty : Kind -> Type.
  Variable memTree : Tree DomainElem.

  Variable pRevPhase         : RegPath memTree.
  Variable pRevScanAddrMsb   : RegPath memTree.
  Variable pRevScanCap       : RegPath memTree.
  Variable pRevStoreSnoopHit : RegPath memTree.

  Hypothesis HPhaseKind   : regKind (getRegFromPath pRevPhase) = Bit 3.
  Hypothesis HScanAddrKind : regKind (getRegFromPath pRevScanAddrMsb) = Bit TagAddrWidth.
  Hypothesis HScanCapKind : regKind (getRegFromPath pRevScanCap) = FullCapWithTag.
  Hypothesis HSnoopKind   : regKind (getRegFromPath pRevStoreSnoopHit) = Bool.

  Local Definition castPhaseOut (v : ty (regKind (getRegFromPath pRevPhase))) : ty (Bit 3) :=
    match HPhaseKind in (_ = K) return ty K with eq_refl => v end.
  Local Definition castPhaseIn (e : Expr ty (Bit 3)) : Expr ty (regKind (getRegFromPath pRevPhase)) :=
    match eq_sym HPhaseKind in (_ = K) return Expr ty K with eq_refl => e end.

  Local Definition castScanAddrOut (v : ty (regKind (getRegFromPath pRevScanAddrMsb))) : ty (Bit TagAddrWidth) :=
    match HScanAddrKind in (_ = K) return ty K with eq_refl => v end.
  Local Definition castScanAddrIn (e : Expr ty (Bit TagAddrWidth)) : Expr ty (regKind (getRegFromPath pRevScanAddrMsb)) :=
    match eq_sym HScanAddrKind in (_ = K) return Expr ty K with eq_refl => e end.

  Local Definition castScanCapOut (v : ty (regKind (getRegFromPath pRevScanCap))) : ty FullCapWithTag :=
    match HScanCapKind in (_ = K) return ty K with eq_refl => v end.
  Local Definition castScanCapIn (e : Expr ty FullCapWithTag) : Expr ty (regKind (getRegFromPath pRevScanCap)) :=
    match eq_sym HScanCapKind in (_ = K) return Expr ty K with eq_refl => e end.

  Local Definition castSnoopOut (v : ty (regKind (getRegFromPath pRevStoreSnoopHit))) : ty Bool :=
    match HSnoopKind in (_ = K) return ty K with eq_refl => v end.
  Local Definition castSnoopIn (e : Expr ty Bool) : Expr ty (regKind (getRegFromPath pRevStoreSnoopHit)) :=
    match eq_sym HSnoopKind in (_ = K) return Expr ty K with eq_refl => e end.

  (* Snoop CPU Store address against currently active revoker scanAddrMsb *)
  Definition implRevokerSnoopStore
    (addr : ty Addr)
    (memSize : ty (Bit LgLgNumBytesFullCapSz))
    : Action ty memTree (Bit 0) :=
    ReadReg "revPhase" pRevPhase (fun revPhaseRaw =>
    let revPhase := castPhaseOut revPhaseRaw in
    ReadReg "scanAddrMsb" pRevScanAddrMsb (fun scanAddrRaw =>
    let scanAddrMsb := castScanAddrOut scanAddrRaw in
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
    If (And [ isNotZero #revPhase ; #hitsScanAddr ]) Then (
      WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool true)) Retv
    ) ;
    Retv)).

  (* Split-Phase Autonomous Revoker Step *)
  Variable revConfig : RevConfig.
  Variable revAct    : forall {k : Kind}, Action ty (Node "revoker" (revokerChildren dom)) k -> Action ty memTree k.
  Variable isCoreFree : Action ty memTree Bool.
  Variable readRq    : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool.
  Variable readRp    : ty Addr -> Action ty memTree (Option FullCapWithTag).
  Variable writeMem  : ty Addr -> ty FullCapWithTag -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool.

  Definition implRevokerPhase0 : Action ty memTree (Bit 0) :=
    LetA epoch : Bit Xlen <- revAct (ReadReg "epoch" (revokerEpochPath dom) (fun v => Return #v)) ;
    Let isOddEpoch : Bool <- FromBit Bool (TruncLsb (Xlen - 1) 1 #epoch) ;
    If #isOddEpoch Then (
      LetA scanAddrMsb : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" (revokerScanAddrPath dom) (fun v => Return #v)) ;
      LetA topAddrMsb  : Bit TagAddrWidth <- revAct (ReadReg "top" (revokerTopPath dom) (fun v => Return #v)) ;
      Let scanAddr     : Addr             <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let isDone       : Bool             <- Uge #scanAddrMsb #topAddrMsb ;
      Let capSz        : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
      If (Not #isDone) Then (
        ReadReg "revPhase" pRevPhase (fun revPhaseRaw =>
        let revPhase := castPhaseOut revPhaseRaw in
        If (Eq #revPhase $0) Then (
          LetA coreFree : Bool <- isCoreFree ;
          If #coreFree Then (
            LetA rdy : Bool <- readRq scanAddr capSz ;
            If #rdy Then (
              Act (WriteReg pRevScanAddrMsb (castScanAddrIn #scanAddrMsb) Retv) ;
              Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
              WriteReg pRevPhase (castPhaseIn $1) Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv)
      ) Else (
        (* Sweep complete: scanAddrMsb reached topAddrMsb *)
        Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
        Act (WriteReg pRevPhase (castPhaseIn $0) Retv) ;
        Let nextEpoch : Bit Xlen <- Add [ #epoch ; $1 ] ;
        Act (revAct (WriteReg (revokerEpochPath dom) #nextEpoch Retv)) ;
        LetA intReq : Bool <- revAct (ReadReg "interruptRequested" (revokerInterruptRequestedPath dom) (fun v => Return #v)) ;
        If #intReq Then (
          Act (revAct (WriteReg (revokerInterruptStatusPath dom) (ConstBool true) Retv)) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) Else (
      (* Idle state: epoch is even *)
      Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
      Act (WriteReg pRevPhase (castPhaseIn $0) Retv) ;
      Act (revAct (WriteReg (revokerInterruptStatusPath dom) (ConstBool false) Retv)) ;
      LetA isKicked : Bool <- revAct (ReadReg "control" (revokerControlPath dom) (fun v => Return #v)) ;
      If #isKicked Then (
        LetA baseAddrMsb : Bit TagAddrWidth <- revAct (ReadReg "base" (revokerBasePath dom) (fun v => Return #v)) ;
        Act (revAct (WriteReg (revokerScanAddrPath dom) #baseAddrMsb Retv)) ;
        Act (WriteReg pRevScanAddrMsb (castScanAddrIn #baseAddrMsb) Retv) ;
        Let oddEpoch : Bit Xlen <-
          {< TruncMsb (Xlen - 1) 1 #epoch, Const ty (Bit 1) (bits.of_Z 1 1) >} ;
        Act (revAct (WriteReg (revokerEpochPath dom) #oddEpoch Retv)) ;
        Act (revAct (WriteReg (revokerControlPath dom) (ConstBool false) Retv)) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

  Definition implRevokerPhase1 : Action ty memTree (Bit 0) :=
    ReadReg "revPhase" pRevPhase (fun revPhaseRaw =>
    let revPhase := castPhaseOut revPhaseRaw in
    If (Eq #revPhase $1) Then (
      LetA scanAddrMsb : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" (revokerScanAddrPath dom) (fun v => Return #v)) ;
      Let scanAddr        : Addr             <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let nextScanAddrMsb : Bit TagAddrWidth <- Add [ #scanAddrMsb ; $1 ] ;
      ReadReg "snoopHit" pRevStoreSnoopHit (fun snoopHitRaw =>
      let snoopHit := castSnoopOut snoopHitRaw in
      LetA rpOpt : Option FullCapWithTag <- readRp scanAddr ;
      If (##rpOpt `? "Some") Then (
        Let ldFullCap : FullCapWithTag <- ##rpOpt `! "Some" ;
        Let ldCap     : Cap            <- ##ldFullCap`"cap" ;
        Let ldAddr    : Addr           <- ##ldFullCap`"addr" ;
        LetA ldECap   : ECap           <- toAction memTree (DecodeCap ldCap ldAddr) ;
        Let isSealing : Bool           <- isSealingCap ldECap ;
        Let shouldCheck : Bool         <- And [ ##ldFullCap`"tag" ; Not #isSealing ; Not #snoopHit ] ;
        If #shouldCheck Then (
          Act (WriteReg pRevScanCap (castScanCapIn #ldFullCap) Retv) ;
          WriteReg pRevPhase (castPhaseIn $2) Retv
        ) Else (
          Act (revAct (WriteReg (revokerScanAddrPath dom) #nextScanAddrMsb Retv)) ;
          Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
          WriteReg pRevPhase (castPhaseIn $0) Retv
        ) ;
        Retv
      ) ;
      Retv)
    ) ;
    Retv).

  Definition implRevokerPhase2 : Action ty memTree (Bit 0) :=
    ReadReg "revPhase" pRevPhase (fun revPhaseRaw =>
    let revPhase := castPhaseOut revPhaseRaw in
    If (Eq #revPhase $2) Then (
      LetA scanAddrMsb    : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" (revokerScanAddrPath dom) (fun v => Return #v)) ;
      Let nextScanAddrMsb : Bit TagAddrWidth <- Add [ #scanAddrMsb ; $1 ] ;
      ReadReg "snoopHit" pRevStoreSnoopHit (fun snoopHitRaw =>
      let snoopHit := castSnoopOut snoopHitRaw in
      If #snoopHit Then (
        Act (revAct (WriteReg (revokerScanAddrPath dom) #nextScanAddrMsb Retv)) ;
        Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
        WriteReg pRevPhase (castPhaseIn $0) Retv
      ) Else (
        ReadReg "savedCap" pRevScanCap (fun savedCapRaw =>
        let savedCap := castScanCapOut savedCapRaw in
        Let ldCap     : Cap              <- ##savedCap`"cap" ;
        Let ldAddr    : Addr             <- ##savedCap`"addr" ;
        LetA ldECap   : ECap             <- toAction memTree (DecodeCap ldCap ldAddr) ;
        Let ldBase    : Bit (AddrSz + 1) <- ##ldECap`"base" ;
        LetL lookup   : RevBitLookup     <- computeRevBitAddr revConfig ldBase ;
        If (##lookup`"isRevokable") Then (
          LetA coreFree : Bool <- isCoreFree ;
          If #coreFree Then (
            Let revByteAddr : Addr <- ##lookup`"revByteAddr" ;
            Let sz0 : Bit LgLgNumBytesFullCapSz <- $0 ;
            LetA rdy : Bool <- readRq revByteAddr sz0 ;
            If #rdy Then (
              WriteReg pRevPhase (castPhaseIn $3) Retv
            ) ;
            Retv
          ) ;
          Retv
        ) Else (
          Act (revAct (WriteReg (revokerScanAddrPath dom) #nextScanAddrMsb Retv)) ;
          Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
          WriteReg pRevPhase (castPhaseIn $0) Retv
        ) ;
        Retv)
      ) ;
      Retv)
    ) ;
    Retv).

  Definition implRevokerPhase3 : Action ty memTree (Bit 0) :=
    ReadReg "revPhase" pRevPhase (fun revPhaseRaw =>
    let revPhase := castPhaseOut revPhaseRaw in
    If (Eq #revPhase $3) Then (
      LetA scanAddrMsb    : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" (revokerScanAddrPath dom) (fun v => Return #v)) ;
      Let nextScanAddrMsb : Bit TagAddrWidth <- Add [ #scanAddrMsb ; $1 ] ;
      ReadReg "snoopHit" pRevStoreSnoopHit (fun snoopHitRaw =>
      let snoopHit := castSnoopOut snoopHitRaw in
      ReadReg "savedCap" pRevScanCap (fun savedCapRaw =>
      let savedCap := castScanCapOut savedCapRaw in
      Let ldCap     : Cap              <- ##savedCap`"cap" ;
      Let ldAddr    : Addr             <- ##savedCap`"addr" ;
      LetA ldECap   : ECap             <- toAction memTree (DecodeCap ldCap ldAddr) ;
      Let ldBase    : Bit (AddrSz + 1) <- ##ldECap`"base" ;
      LetL lookup   : RevBitLookup     <- computeRevBitAddr revConfig ldBase ;
      Let revByteAddr : Addr           <- ##lookup`"revByteAddr" ;
      LetA rpOpt : Option FullCapWithTag <- readRp revByteAddr ;
      If (##rpOpt `? "Some") Then (
        Let revCap  : FullCapWithTag <- ##rpOpt `! "Some" ;
        Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
        Let revBit  : Bool           <- extractRevBit lookup #revByte ;
        If (And [ #revBit ; Not #snoopHit ]) Then (
          WriteReg pRevPhase (castPhaseIn $4) Retv
        ) Else (
          Act (revAct (WriteReg (revokerScanAddrPath dom) #nextScanAddrMsb Retv)) ;
          Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
          WriteReg pRevPhase (castPhaseIn $0) Retv
        ) ;
        Retv
      ) ;
      Retv))
    ) ;
    Retv).

  Definition implRevokerPhase4 : Action ty memTree (Bit 0) :=
    ReadReg "revPhase" pRevPhase (fun revPhaseRaw =>
    let revPhase := castPhaseOut revPhaseRaw in
    If (Eq #revPhase $4) Then (
      LetA scanAddrMsb    : Bit TagAddrWidth <- revAct (ReadReg "scanAddr" (revokerScanAddrPath dom) (fun v => Return #v)) ;
      Let scanAddr        : Addr             <- {< #scanAddrMsb, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >} ;
      Let nextScanAddrMsb : Bit TagAddrWidth <- Add [ #scanAddrMsb ; $1 ] ;
      Let capSz           : Bit LgLgNumBytesFullCapSz <- $LgNumBytesFullCapSz ;
      ReadReg "snoopHit" pRevStoreSnoopHit (fun snoopHitRaw =>
      let snoopHit := castSnoopOut snoopHitRaw in
      If #snoopHit Then (
        Act (revAct (WriteReg (revokerScanAddrPath dom) #nextScanAddrMsb Retv)) ;
        Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
        WriteReg pRevPhase (castPhaseIn $0) Retv
      ) Else (
        ReadReg "savedCap" pRevScanCap (fun savedCapRaw =>
        let savedCap := castScanCapOut savedCapRaw in
        Let untaggedCap : FullCapWithTag <- STRUCT {
          "tag"  ::= Const ty Bool false ;
          "cap"  ::= ##savedCap`"cap" ;
          "addr" ::= ##savedCap`"addr"
        } ;
        LetA rdy : Bool <- writeMem scanAddr untaggedCap capSz ;
        If #rdy Then (
          Act (revAct (WriteReg (revokerScanAddrPath dom) #nextScanAddrMsb Retv)) ;
          Act (WriteReg pRevStoreSnoopHit (castSnoopIn (ConstBool false)) Retv) ;
          WriteReg pRevPhase (castPhaseIn $0) Retv
        ) ;
        Retv)
      ) ;
      Retv)
    ) ;
    Retv).

  Definition implRevokerStepsFsm : list (Action ty memTree (Bit 0)) :=
    [ implRevokerPhase0 ;
      implRevokerPhase1 ;
      implRevokerPhase2 ;
      implRevokerPhase3 ;
      implRevokerPhase4 ].

End ImplRevoker.
