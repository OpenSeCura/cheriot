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
From Cheriot Require Import SpecDefines SpecDevice FunctionalUnits SpecRevoker ImplRevoker.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Split-Phase Implementation Memory Interface (MemIfc)
 * =========================================================================== *)

Record MemIfc {ty : Kind -> Type} := {
  memTree : Tree DomainElem ;

  (* 1. Instruction Memory Channel *)
  mem_readInstRq   : ty Addr -> Action ty memTree Bool ;
  mem_getInstRp    : Action ty memTree (Option Inst) ;

  (* 2. Data Load Channel *)
  mem_readMemRq    : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;
  mem_getMemRp     : Action ty memTree (Option FullCapWithTag) ;

  (* 3. Revocation Bit Memory Channel *)
  mem_readRevBitRq : ty (Bit (AddrSz + 1)) -> Action ty memTree Bool ;
  mem_getRevBitRp  : Action ty memTree (Option Bool) ;

  (* 4. Memory Write Channel *)
  mem_writeMem     : ty Addr -> ty FullCapWithTag -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;

  (* 5. FENCE & FENCE.I Synchronization Channels *)
  mem_fence_req    : ty FenceOp -> Action ty memTree Bool ;
  mem_fenceI_req   : Action ty memTree Bool ;
  mem_fenceI_ack   : Action ty memTree Bool
}.

(* ===========================================================================
 * Split-Phase Line-Level MemRegion Trees
 * =========================================================================== *)

Definition implInternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
  Node r.(regionName) [
    internalMemRegionTree r false ;
    Leaf "rpValid" (r.(regionDom), EReg (Build_Reg Bool (Some false) false))
  ].

Definition implExternalMemRegionChildren (r : MemRegion) : list (Tree DomainElem) :=
  externalMemRegionChildren r.

Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
  externalMemRegionTree r.

Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
  Node r.(regionName) [
    customMemRegionTree r children ;
    Leaf "rpReg" (r.(regionDom), EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg))) (Some (getDefault _)) false))
  ].

Arguments implInternalMemRegionTree r : clear implicits.
Arguments implExternalMemRegionChildren r : clear implicits.
Arguments implExternalMemRegionTree r : clear implicits.
Arguments implCustomMemRegionTree r children : clear implicits.

Definition implMemRegionLineTree (r : MemRegion) : Tree DomainElem :=
  match r.(regionKind) with
  | InternalMem _ _ _ => implInternalMemRegionTree r
  | ExternalMem => implExternalMemRegionTree r
  | CustomMem children _ _ _ => implCustomMemRegionTree r children
  end.

(* ===========================================================================
 * Split-Phase Line-Level Actions for Each Region Kind
 * =========================================================================== *)

Section ImplInternalMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tInt := implInternalMemRegionTree r.
  Local Definition pRpValid : RegPath tInt := Build_RegPath tInt (inr (inl tt)) I.

  Definition internalMemLineReadRq (addr : ty Addr) : Action ty tInt Bool :=
    ReadReg "rpValidVal" pRpValid (fun rpValidVal =>
    Let isReady : Bool <- Not #rpValidVal ;
    If #isReady Then (
      Act (liftAction child0Path (internalMemRegionLineReadRq r false addr)) ;
      WriteReg pRpValid (ConstBool true) Retv
    ) ;
    Return #isReady).

  Definition internalMemLineWriteRq (rq : ty (LineWriteRq r.(regionLineCfg))) : Action ty tInt Bool :=
    Act (liftAction child0Path (internalMemRegionLineWrite r false rq)) ;
    Return (ConstBool true).

  Definition internalMemLineReadRp : Action ty tInt (Option (LineReadRp r.(regionLineCfg))) :=
    ReadReg "rpValidVal" pRpValid (fun rpValidVal =>
    LetIf rpOpt : Option (LineReadRp r.(regionLineCfg)) <-
      If #rpValidVal Then (
        LetA rp : LineReadRp r.(regionLineCfg) <- liftAction child0Path (internalMemRegionLineReadRp r false) ;
        Act (WriteReg pRpValid (ConstBool false) Retv) ;
        Return (mkSome #rp)
      ) Else (
        Return ConstDef
      ) ;
    Return #rpOpt).

End ImplInternalMemRegionActions.

Arguments internalMemLineReadRq r [ty] addr.
Arguments internalMemLineWriteRq r [ty] rq.
Arguments internalMemLineReadRp r {ty}.

Section ImplExternalMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tExt := implExternalMemRegionTree r.

  Definition externalMemLineReadRq (addr : ty Addr) : Action ty tExt Bool :=
    externalMemRegionLineReadRq r addr.

  Definition externalMemLineWriteRq (rq : ty (LineWriteRq r.(regionLineCfg))) : Action ty tExt Bool :=
    externalMemRegionLineWrite r rq.

  Definition externalMemLineReadRp : Action ty tExt (Option (LineReadRp r.(regionLineCfg))) :=
    externalMemRegionLineReadRp r.

End ImplExternalMemRegionActions.

Arguments externalMemLineReadRq r [ty] addr.
Arguments externalMemLineWriteRq r [ty] rq.
Arguments externalMemLineReadRp r {ty}.

Section ImplCustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree DomainElem).
  Variable readAction : forall ty, ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp r.(regionLineCfg)).
  Variable writeAction : forall ty, ty (LineWriteRq r.(regionLineCfg)) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tCust := implCustomMemRegionTree r children.
  Local Definition pRpReg : RegPath tCust := Build_RegPath tCust (inr (inl tt)) I.

  Definition customMemLineReadRq (addr : ty Addr) : Action ty tCust Bool :=
    ReadReg "rpRegVal" pRpReg (fun rpRegVal =>
    Let isReady : Bool <- Not (##rpRegVal `? "Some") ;
    If #isReady Then (
      LetA rp : LineReadRp r.(regionLineCfg) <- liftAction child0Path (readAction addr) ;
      WriteReg pRpReg (mkSome #rp) Retv
    ) ;
    Return #isReady).

  Definition customMemLineWriteRq (rq : ty (LineWriteRq r.(regionLineCfg))) : Action ty tCust Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      LetA _ : Bit 0 <- liftAction child0Path (writeAction rq) ;
      Return (ConstBool true)
    ).

  Definition customMemLineReadRp : Action ty tCust (Option (LineReadRp r.(regionLineCfg))) :=
    ReadReg "rpRegVal" pRpReg (fun rpRegVal =>
    If (##rpRegVal `? "Some") Then (
      WriteReg pRpReg ConstDef Retv
    ) ;
    Return #rpRegVal).

End ImplCustomMemRegionActions.

Arguments customMemLineReadRq r children readAction [ty] addr.
Arguments customMemLineWriteRq r children writeAction [ty] rq.
Arguments customMemLineReadRp r children {ty}.

(* ===========================================================================
 * Unified Line-Level Dispatchers (lineReadRq, lineWriteRq, lineReadRp)
 * =========================================================================== *)

Definition lineReadRq
           (ty : Kind -> Type)
           (r : MemRegion)
           (addr : ty Addr)
           : Action ty (implMemRegionLineTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem _ _ _ => implInternalMemRegionTree r
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem _ _ _ => internalMemLineReadRq r addr
  | ExternalMem => externalMemLineReadRq r addr
  | CustomMem children readAction _ _ => customMemLineReadRq r children readAction addr
  end.

Definition lineWriteRq
           (ty : Kind -> Type)
           (r : MemRegion)
           (rq : ty (LineWriteRq r.(regionLineCfg)))
           : Action ty (implMemRegionLineTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem _ _ _ => implInternalMemRegionTree r
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem _ _ _ => internalMemLineWriteRq r rq
  | ExternalMem => externalMemLineWriteRq r rq
  | CustomMem children _ writeAction _ => customMemLineWriteRq r children writeAction rq
  end.

Definition lineReadRp
           (ty : Kind -> Type)
           (r : MemRegion)
           : Action ty (implMemRegionLineTree r) (Option (LineReadRp r.(regionLineCfg))) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem _ _ _ => implInternalMemRegionTree r
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) (Option (LineReadRp r.(regionLineCfg))) with
  | InternalMem _ _ _ => internalMemLineReadRp r
  | ExternalMem => externalMemLineReadRp r
  | CustomMem children _ _ _ => customMemLineReadRp r children
  end.

Arguments lineReadRq [ty] r addr.
Arguments lineWriteRq [ty] r rq.
Arguments lineReadRp [ty] r.

(* ===========================================================================
 * Per-Region Split-Phase Multi-Byte Read & Write (Sequential Two-Line Actions)
 * =========================================================================== *)

Notation RegionReadState cfg := (STRUCT_TYPE {
  "addr"        :: Addr ;
  "memSize"     :: Bit LgLgNumBytesFullCapSz ;
  "crossesLine" :: Bool ;
  "phase"       :: Bit 2 ;
  "rp1"         :: LineReadRp cfg
}).

Definition implMemRegionTree (r : MemRegion) : Tree DomainElem :=
  Node r.(regionName) [
    Node "line" [ implMemRegionLineTree r ] ;
    Leaf "rdReq"         (r.(regionDom), EReg (Build_Reg (Option (RegionReadState r.(regionLineCfg))) (Some (getDefault _)) false)) ;
    Leaf "wrSecondPhase" (r.(regionDom), EReg (Build_Reg (Option (LineWriteRq r.(regionLineCfg))) (Some (getDefault _)) false))
  ].

Section ImplMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Let tR := implMemRegionTree r.
  Let lBytes := lineBytes r.
  Let nTags := numLineTags r.
  Let lgLineBytesZ := Z.of_nat (lgLineBytes r).

  Let npLine : NodePath tR := embedNodeIntoPath child0Path singletonChildPath.
  Let pRdReq : RegPath tR := Build_RegPath tR (inr (inl tt)) I.
  Let pWrSecondPhase : RegPath tR := Build_RegPath tR (inr (inr (inl tt))) I.

  Let castAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

  Let lineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytesZ) :=
    TruncLsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Let lineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgLineBytesZ)%Z) :=
    TruncMsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Let lineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< lineIndex addr, Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Let nextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< Add [ lineIndex addr ; $1 ], Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Let add1 (addr : Expr ty Addr) : Expr ty (Array lBytes Bool) :=
    FromBit (Array lBytes Bool)
      (Not (Sll (ConstBit (InvDefault _)) (lineOffset addr))).

  Let lgNumDXlenZ : Z := (lgLineBytesZ - LgNumBytesFullCapSz)%Z.

  Let castLineOffsetForTag (offset : Expr ty (Bit lgLineBytesZ))
    : Expr ty (Bit (LgNumBytesFullCapSz + lgNumDXlenZ)%Z) :=
    castBits (eq_sym (add_sub_cancel lgLineBytesZ LgNumBytesFullCapSz)) offset.

  Let tagSlot (addr : Expr ty Addr) : Expr ty (Bit lgNumDXlenZ) :=
    TruncMsb lgNumDXlenZ LgNumBytesFullCapSz (castLineOffsetForTag (lineOffset addr)).

  Let computeCrossesLine (addr : Expr ty Addr) (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Expr ty Bool :=
    let numBytesActive :=
      Sll $1 (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z memSize) in
    let endOffset :=
      Add [ ZeroExtend 1 (lineOffset addr) ; numBytesActive ] in
    FromBit Bool (TruncMsb 1 lgLineBytesZ (Sub endOffset $1)).

  Let extractReadCap
                   (addr : Expr ty Addr)
                   (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
                   (lineDataMerged : Expr ty (Array lBytes (Bit 8)))
                   (tagArr1 : Expr ty (Array nTags Bool))
                   : Expr ty FullCapWithTag :=
    let capOffset := TruncLsb TagAddrWidth LgNumBytesFullCapSz addr in
    let isCapAligned := isZero capOffset in
    let isCap := And [Eq memSize $LgNumBytesFullCapSz ; isCapAligned] in
    let rotData := ArrayRotr lineDataMerged (lineOffset addr) in
    let dataBytes := slice rotData (Const ty (Bit lgLineBytesZ) Zmod.zero) (Z.to_nat NumBytesFullCapSz) in
    let rawData := ToBit dataBytes in
    let rawTag :=
      if hasTags r then
        ReadArray tagArr1 (tagSlot addr)
      else
        ConstBool false in
    STRUCT {
      "tag"  ::= And [ isCap ; rawTag ] ;
      "cap"  ::= FromBit Cap (TruncMsb CapSz AddrSz rawData) ;
      "addr" ::= TruncLsb CapSz AddrSz rawData
    }.

  (* Issue first line read request *)
  Definition implMemRegionReadRq
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR Bool :=
    ReadReg "rdReqVal" pRdReq (fun rdReqVal =>
    Let canIssue : Bool <- Not (##rdReqVal `? "Some") ;
    LetIf accepted : Bool <-
      If #canIssue Then (
        Let crossesLine : Bool <- computeCrossesLine #addr #memSize ;
        Let lAddr1      : Addr <- lineAddr #addr ;
        LetA rdy1       : Bool <- liftAction npLine (lineReadRq r lAddr1) ;
        If #rdy1 Then (
          Let initSt : RegionReadState r.(regionLineCfg) <- STRUCT {
            "addr"        ::= #addr ;
            "memSize"     ::= #memSize ;
            "crossesLine" ::= #crossesLine ;
            "phase"       ::= ($0 : Expr ty (Bit 2)) ;
            "rp1"         ::= (ConstDef : Expr ty (LineReadRp r.(regionLineCfg)))
          } ;
          WriteReg pRdReq (mkSome #initSt) Retv
        ) ;
        Return #rdy1
      ) Else (
        Return (ConstBool false)
      ) ;
    Return #accepted).

  (* Independent intermediate action to step cross-line read/write to the second line *)
  Definition implMemRegionStepSecondLine : Action ty tR (Bit 0) :=
    ReadReg "rdReqVal" pRdReq (fun rdReqVal =>
    Act (
      If (##rdReqVal `? "Some") Then (
        Let st          : RegionReadState r.(regionLineCfg) <- ##rdReqVal `! "Some" ;
        Let addr        : Addr                              <- ##st`"addr" ;
        Let memSize     : Bit LgLgNumBytesFullCapSz         <- ##st`"memSize" ;
        Let crossesLine : Bool                              <- ##st`"crossesLine" ;
        Let phase       : Bit 2                             <- ##st`"phase" ;
        If (And [ Eq #phase $0 ; #crossesLine ]) Then (
          LetA rp1Opt : Option (LineReadRp r.(regionLineCfg)) <- liftAction npLine (@lineReadRp ty r) ;
          If (##rp1Opt `? "Some") Then (
            Let rp1    : LineReadRp r.(regionLineCfg) <- ##rp1Opt `! "Some" ;
            Let lAddr2 : Addr                         <- nextLineAddr #addr ;
            LetA rdy2  : Bool                         <- liftAction npLine (lineReadRq r lAddr2) ;
            If #rdy2 Then (
              Let nextSt : RegionReadState r.(regionLineCfg) <- STRUCT {
                "addr"        ::= #addr ;
                "memSize"     ::= #memSize ;
                "crossesLine" ::= #crossesLine ;
                "phase"       ::= ($2 : Expr ty (Bit 2)) ;
                "rp1"         ::= #rp1
              } ;
              WriteReg pRdReq (mkSome #nextSt) Retv
            ) ;
            Retv
          ) ;
          Retv
        ) ;
        Retv
      ) ;
      Retv
    ) ;
    ReadReg "wrSecondOpt" pWrSecondPhase (fun wrSecondOpt =>
    If (##wrSecondOpt `? "Some") Then (
      Let rq2   : LineWriteRq r.(regionLineCfg) <- ##wrSecondOpt `! "Some" ;
      LetA rdy2 : Bool                          <- liftAction npLine (lineWriteRq r rq2) ;
      If #rdy2 Then (
        WriteReg pWrSecondPhase ConstDef Retv
      ) ;
      Retv
    ) ;
    Retv)).

  (* Advance cross-line read state machine or return completed FullCapWithTag *)
  Definition implMemRegionReadRp : Action ty tR (Option FullCapWithTag) :=
    ReadReg "rdReqVal" pRdReq (fun rdReqVal =>
    LetIf resOpt : Option FullCapWithTag <-
      If (##rdReqVal `? "Some") Then (
        Let st          : RegionReadState r.(regionLineCfg) <- ##rdReqVal `! "Some" ;
        Let addr        : Addr                              <- ##st`"addr" ;
        Let memSize     : Bit LgLgNumBytesFullCapSz         <- ##st`"memSize" ;
        Let crossesLine : Bool                              <- ##st`"crossesLine" ;
        Let phase       : Bit 2                             <- ##st`"phase" ;
        Let savedRp1    : LineReadRp r.(regionLineCfg)      <- ##st`"rp1" ;

        LetIf phaseRes : Option FullCapWithTag <-
          If (Eq #phase $0) Then (
            (* Phase 0: Waiting for first line response rp1 *)
            LetA rp1Opt : Option (LineReadRp r.(regionLineCfg)) <- liftAction npLine (@lineReadRp ty r) ;
            LetIf phase0Res : Option FullCapWithTag <-
              If (##rp1Opt `? "Some") Then (
                Let rp1 : LineReadRp r.(regionLineCfg) <- ##rp1Opt `! "Some" ;
                LetIf crossRes : Option FullCapWithTag <-
                  If #crossesLine Then (
                    Let nextSt : RegionReadState r.(regionLineCfg) <- STRUCT {
                      "addr"        ::= #addr ;
                      "memSize"     ::= #memSize ;
                      "crossesLine" ::= #crossesLine ;
                      "phase"       ::= ($1 : Expr ty (Bit 2)) ;
                      "rp1"         ::= #rp1
                    } ;
                    Act (WriteReg pRdReq (mkSome #nextSt) Retv) ;
                    Return ConstDef
                  ) Else (
                    (* Single-line read complete *)
                    Let res : FullCapWithTag <- extractReadCap #addr #memSize (##rp1`"data") (##rp1`"tag") ;
                    Act (WriteReg pRdReq ConstDef Retv) ;
                    Return (mkSome #res)
                  ) ;
                Return #crossRes
              ) Else (
                Return ConstDef
              ) ;
            Return #phase0Res
          ) Else (
            LetIf phase12Res : Option FullCapWithTag <-
              If (Eq #phase $1) Then (
                (* Phase 1: Issue second line request lAddr2 sequentially *)
                Let lAddr2 : Addr <- nextLineAddr #addr ;
                LetA rdy2  : Bool <- liftAction npLine (lineReadRq r lAddr2) ;
                If #rdy2 Then (
                  Let nextSt : RegionReadState r.(regionLineCfg) <- STRUCT {
                    "addr"        ::= #addr ;
                    "memSize"     ::= #memSize ;
                    "crossesLine" ::= #crossesLine ;
                    "phase"       ::= ($2 : Expr ty (Bit 2)) ;
                    "rp1"         ::= #savedRp1
                  } ;
                  WriteReg pRdReq (mkSome #nextSt) Retv
                ) ;
                Return ConstDef
              ) Else (
                (* Phase 2: Waiting for second line response rp2 *)
                LetA rp2Opt : Option (LineReadRp r.(regionLineCfg)) <- liftAction npLine (@lineReadRp ty r) ;
                LetIf phase2Res : Option FullCapWithTag <-
                  If (##rp2Opt `? "Some") Then (
                    Let rp2 : LineReadRp r.(regionLineCfg) <- ##rp2Opt `! "Some" ;
                    Let lineDataMerged : Array lBytes (Bit 8) <-
                      ArrayBuilder (fun (i : FinType lBytes) =>
                        ITE (ReadArrayConst (add1 #addr) i)
                            (ReadArrayConst (##rp2`"data") i)
                            (ReadArrayConst (##savedRp1`"data") i)) ;
                    Let res : FullCapWithTag <- extractReadCap #addr #memSize #lineDataMerged (##savedRp1`"tag") ;
                    Act (WriteReg pRdReq ConstDef Retv) ;
                    Return (mkSome #res)
                  ) Else (
                    Return ConstDef
                  ) ;
                Return #phase2Res
              ) ;
            Return #phase12Res
          ) ;
        Return #phaseRes
      ) Else (
        Return ConstDef
      ) ;
    Return #resOpt).

  (* Write first line immediately; if crossesLine, latch rq2 for implMemRegionStepSecondLine *)
  Definition implMemRegionWrite
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      Let capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz #addr ;
      Let isCapAligned : Bool <- isZero #capOffset ;
      Let isCap : Bool <- And [Eq #memSize $LgNumBytesFullCapSz ; #isCapAligned] ;
      Let rawData : Bit FullCapSz <-
        ITE #isCap
            {< ToBit (##stVal`"cap"), ##stVal`"addr" >}
            (ZeroExtendTo FullCapSz (##stVal`"addr")) ;
      Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData ;
      Let baseData : Array lBytes (Bit 8) <- embedCapBytes lBytes #capBytes ;
      Let rotData : Array lBytes (Bit 8) <- ArrayRotl #baseData (lineOffset #addr) ;
      Let numBytesActive : Bit (lgLineBytesZ + 1)%Z <-
                             Sll $1
                               (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z #memSize) ;
      Let endOffset : Bit (lgLineBytesZ + 1)%Z <-
        Add [ ZeroExtend 1 (lineOffset #addr) ; #numBytesActive ] ;
      Let crossesLine : Bool <- FromBit Bool (TruncMsb 1 lgLineBytesZ (Sub #endOffset $1)) ;
      Let numBytesActiveDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
                             Sll $1
                               (ZeroExtend (LgNumBytesFullCapSz + 1 - LgLgNumBytesFullCapSz)%Z #memSize) ;
      Let endOffsetDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
        Add [ ZeroExtend 1 #capOffset ; #numBytesActiveDXlen ] ;
      Let crossesDXlen : Bool <- FromBit Bool (TruncMsb 1 LgNumBytesFullCapSz (Sub #endOffsetDXlen $1)) ;
      Let isWrites : Array lBytes Bool <-
        FromBit (Array lBytes Bool)
          (rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (lineOffset #addr)) ;
      ReadReg "wrSecondOpt" pWrSecondPhase (fun wrSecondOpt =>
      Let canWrite : Bool <- Not (##wrSecondOpt `? "Some") ;
      LetIf done : Bool <-
        If #canWrite Then (
          Let mask1 : Array lBytes Bool <-
            ArrayBuilder (fun (i : FinType lBytes) =>
              And [ ReadArrayConst #isWrites i ; Not (ReadArrayConst (add1 #addr) i) ]) ;
          Let tagData1 : Array nTags Bool <-
            if hasTags r then (
              UpdateArray ConstDef (tagSlot #addr) (And [ #isCap ; ##stVal`"tag" ])
            ) else (
              ConstDef
            ) ;
          Let crossWithinLine : Bool <- And [ #crossesDXlen ; Not #crossesLine ] ;
          Let nextTagSlot : Bit lgNumDXlenZ <- Add [ tagSlot #addr ; $1 ] ;
          Let tagMask1 : Array nTags Bool <-
            if hasTags r then (
              UpdateArray
                (UpdateArray ConstDef #nextTagSlot #crossWithinLine)
                (tagSlot #addr)
                (ConstBool true)
            ) else (
              ConstDef
            ) ;
          Let rq1 : LineWriteRq r.(regionLineCfg) <- STRUCT {
            "addr"     ::= lineAddr #addr ;
            "data"     ::= #rotData ;
            "dataMask" ::= #mask1 ;
            "tag"      ::= #tagData1 ;
            "tagMask"  ::= #tagMask1
          } ;
          Let mask2 : Array lBytes Bool <-
            ArrayBuilder (fun (i : FinType lBytes) =>
              And [ ReadArrayConst #isWrites i ; ReadArrayConst (add1 #addr) i ]) ;
          Let tagData2 : Array nTags Bool <- ConstDef ;
          Let tagMask2 : Array nTags Bool <-
            if hasTags r then (
              UpdateArray ConstDef (Const ty (Bit lgNumDXlenZ) Zmod.zero) (ConstBool true)
            ) else (
              ConstDef
            ) ;
          Let rq2 : LineWriteRq r.(regionLineCfg) <- STRUCT {
            "addr"     ::= nextLineAddr #addr ;
            "data"     ::= #rotData ;
            "dataMask" ::= #mask2 ;
            "tag"      ::= #tagData2 ;
            "tagMask"  ::= #tagMask2
          } ;
          LetA rdy1 : Bool <- liftAction npLine (lineWriteRq r rq1) ;
          If (And [ #rdy1 ; #crossesLine ]) Then (
            WriteReg pWrSecondPhase (mkSome #rq2) Retv
          ) ;
          Return #rdy1
        ) Else (
          Return (ConstBool false)
        ) ;
      Return #done)
    ).

End ImplMemRegionActions.

Arguments implMemRegionReadRq r [ty] addr memSize.
Arguments implMemRegionStepSecondLine r {ty}.
Arguments implMemRegionReadRp r {ty}.
Arguments implMemRegionWrite r [ty] addr stVal memSize.

(* ===========================================================================
 * Multi-Region Composite Implementation Router & MemIfc Instance
 * =========================================================================== *)

Fixpoint implRegionsChildren (regions : list MemRegion) : list (Tree DomainElem) :=
  match regions with
  | [] => []
  | r :: rs => [ implMemRegionTree r ; Node "regions" (implRegionsChildren rs) ]
  end.

Definition implRegionsTree (regions : list MemRegion) : Tree DomainElem :=
  Node "regions" (implRegionsChildren regions).

Section ImplRegionsRouter.
  Variable ty : Kind -> Type.

  Fixpoint implRegionsReadRq
           (regions : list MemRegion)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) Bool :=
    match regions return Action ty (implRegionsTree regions) Bool with
    | [] => Return (ConstBool true)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rdy : Bool <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRq r addr memSize)
          ) Else (
            liftAction child1Path (implRegionsReadRq rs addr memSize)
          ) ;
        Return #rdy
    end.

  Fixpoint implRegionsStepSecondLine
           (regions : list MemRegion)
           : Action ty (implRegionsTree regions) (Bit 0) :=
    match regions return Action ty (implRegionsTree regions) (Bit 0) with
    | [] => Retv
    | r :: rs =>
        Act (liftAction child0Path (@implMemRegionStepSecondLine r ty)) ;
        liftAction child1Path (implRegionsStepSecondLine rs)
    end.

  Fixpoint implRegionsReadRp
           (regions : list MemRegion)
           (addr : ty Addr)
           : Action ty (implRegionsTree regions) (Option FullCapWithTag) :=
    match regions return Action ty (implRegionsTree regions) (Option FullCapWithTag) with
    | [] => Return (mkSome ConstDef)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rpOpt : Option FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (@implMemRegionReadRp r ty)
          ) Else (
            liftAction child1Path (implRegionsReadRp rs addr)
          ) ;
        Return #rpOpt
    end.

  Fixpoint implRegionsWrite
           (regions : list MemRegion)
           (addr : ty Addr)
           (stVal : ty FullCapWithTag)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) Bool :=
    match regions return Action ty (implRegionsTree regions) Bool with
    | [] => Return (ConstBool true)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rdy : Bool <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionWrite r addr stVal memSize)
          ) Else (
            liftAction child1Path (implRegionsWrite rs addr stVal memSize)
          ) ;
        Return #rdy
    end.

End ImplRegionsRouter.

Section ImplMemModel.
  Variable dom : string.
  Variable revConfig : RevConfig.
  Variable regions : list MemRegion.

  Definition liftToImplRegion
    (ty : Kind -> Type)
    (r : MemRegion)
    {k : Kind}
    (act : Action ty (memRegionTree r) k)
    : Action ty (implMemRegionTree r) k.
  Proof.
    unfold memRegionTree in act.
    unfold implMemRegionTree, implMemRegionLineTree.
    destruct (r.(regionKind)) as [| | children readAction writeAction irqAction].
    - exact (Return (Const ty k (getDefault k))).
    - exact (Return (Const ty k (getDefault k))).
    - exact (liftAction child0Path (liftAction child0Path (liftAction child0Path act))).
  Defined.

  Arguments liftToImplRegion {ty} r {k} act.

  Fixpoint implNthRegionAction
    (ty : Kind -> Type)
    (idx : nat)
    {struct idx}
    : forall (rs : list MemRegion) (r0 : MemRegion),
      nth_error rs idx = Some r0 ->
      forall k, Action ty (memRegionTree r0) k -> Action ty (implRegionsTree rs) k :=
    match idx with
    | 0%nat =>
        fun rs =>
          match rs return forall r0, nth_error rs 0 = Some r0 ->
                          forall k, Action ty (memRegionTree r0) k -> Action ty (implRegionsTree rs) k with
          | nil => fun r0 pf => False_rect _ (none_neq_some pf)
          | cons r rs' => fun r0 pf k act =>
              let eq_r0_r : r0 = r :=
                match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end with
                | eq_refl => eq_refl
                end in
              liftAction child0Path
                (@liftToImplRegion ty r k
                  (match eq_r0_r in (_ = y) return Action ty (memRegionTree y) k with
                   | eq_refl => act
                   end))
          end
    | S idx' =>
        fun rs =>
          match rs return forall r0, nth_error rs (S idx') = Some r0 ->
                          forall k, Action ty (memRegionTree r0) k -> Action ty (implRegionsTree rs) k with
          | nil => fun r0 pf => False_rect _ (none_neq_some pf)
          | cons r rs' => fun r0 pf k act =>
              liftAction child1Path (@implNthRegionAction ty idx' rs' r0 pf k act)
          end
    end.

  Arguments implNthRegionAction {ty} idx rs r0 pf {k} act.

  Fixpoint implCollectIrqActions
    (rs : list MemRegion)
    : list (forall ty, Action ty (implRegionsTree rs) Bool) :=
    match rs return list (forall ty, Action ty (implRegionsTree rs) Bool) with
    | [] => []
    | r :: rs' =>
        let rest := map (fun act ty => liftAction child1Path (act ty))
                        (implCollectIrqActions rs') in
        match memRegionIrqAction r with
        | Some act =>
            (fun ty => liftAction child0Path (liftToImplRegion r (act ty))) :: rest
        | None => rest
        end
    end.

  Lemma implCollectIrqActions_length (rs : list MemRegion) :
    List.length (implCollectIrqActions rs) = List.length (collectIrqActions rs).
  Proof.
    induction rs as [| r rs' IH]; simpl; auto.
    destruct (memRegionIrqAction r); simpl; repeat rewrite length_map; lia.
  Qed.

  Definition implMemTree : Tree DomainElem :=
    Node "mem" [
      implRegionsTree regions ;
      Leaf "instPending"      (dom, EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
      Leaf "memPending"       (dom, EReg (Build_Reg (Option Addr) (Some (getDefault _)) false)) ;
Leaf "revPending"       (dom, EReg (Build_Reg (Option (Bit (AddrSz + 1))) (Some (getDefault _)) false)) ;
      Leaf "revPhase"         (dom, EReg (Build_Reg (Bit 3) (Some (getDefault _)) false)) ;
      Leaf "revScanAddrMsb"   (dom, EReg (Build_Reg (Bit (AddrSz - LgNumBytesFullCapSz)) (Some (getDefault _)) false)) ;
      Leaf "revScanCap"       (dom, EReg (Build_Reg FullCapWithTag (Some (getDefault _)) false)) ;
      Leaf "revStoreSnoopHit" (dom, EReg (Build_Reg Bool (Some false) false))
    ].

  Section Ty.
    Variable ty : Kind -> Type.

    Definition implMemNthRegionAction
      (idx : nat)
      (r0 : MemRegion)
      (pf : nth_error regions idx = Some r0)
      {k : Kind}
      (act : Action ty (memRegionTree r0) k)
      : Action ty implMemTree k :=
      liftAction child0Path (implNthRegionAction idx regions r0 pf act).

    Arguments implMemNthRegionAction idx r0 pf {k} act.

    Definition implMemCollectIrqActions : list (Action ty implMemTree Bool) :=
      map (fun f => liftAction child0Path (f ty)) (implCollectIrqActions regions).

    Local Definition pInstPending      : RegPath implMemTree := Build_RegPath implMemTree (inr (inl tt)) I.
    Local Definition pMemPending       : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inl tt))) I.
    Local Definition pRevPending       : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inl tt)))) I.
    Local Definition pRevPhase         : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inr (inl tt))))) I.
    Local Definition pRevScanAddrMsb   : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inr (inr (inl tt)))))) I.
    Local Definition pRevScanCap       : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inr (inr (inr (inl tt))))))) I.
    Local Definition pRevStoreSnoopHit : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inr (inr (inr (inr (inl tt)))))))) I.

    Local Definition isNoCorePending : Action ty implMemTree Bool :=
      ReadReg "instP" pInstPending (fun instP =>
      ReadReg "memP"  pMemPending  (fun memP =>
      ReadReg "revP"  pRevPending  (fun revP =>
      Return (And [ Not (##instP `? "Some") ;
                    Not (##memP `? "Some") ;
                    Not (##revP `? "Some") ])))).

    Local Definition isNoReadPending : Action ty implMemTree Bool :=
      LetA coreFree : Bool  <- isNoCorePending ;
      ReadReg "revPh" pRevPhase (fun revPhase =>
      Return (And [ #coreFree ; Eq ##revPhase $0 ])).

    (* 1. Instruction Memory Channel *)
    Definition implReadInstRq (addr : ty Addr) : Action ty implMemTree Bool :=
      LetA canIssue : Bool <- isNoReadPending ;
      LetIf accepted : Bool <-
        If #canIssue Then (
          Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
          LetA rdy   : Bool <- liftAction child0Path (implRegionsReadRq regions addr instSz) ;
          If #rdy Then (
            WriteReg pInstPending (mkSome #addr) Retv
          ) ;
          Return #rdy
        ) Else (
          Return (ConstBool false)
        ) ;
      Return #accepted.

    Definition implGetInstRp : Action ty implMemTree (Option Inst) :=
      ReadReg "instP" pInstPending (fun instP =>
      LetIf res : Option Inst <-
        If (##instP `? "Some") Then (
          Let  addr  : Addr                  <- ##instP `! "Some" ;
          LetA rpOpt : Option FullCapWithTag <- liftAction child0Path (implRegionsReadRp regions addr) ;
          LetIf instOpt : Option Inst <-
            If (##rpOpt `? "Some") Then (
              Let fullVal : FullCapWithTag <- ##rpOpt `! "Some" ;
              Act (WriteReg pInstPending ConstDef Retv) ;
              Return (mkSome (##fullVal`"addr"))
            ) Else (
              Return ConstDef
            ) ;
          Return #instOpt
        ) Else (
          Return ConstDef
        ) ;
      Return #res).

    (* 2. Data Load Channel *)
    Definition implReadMemRq (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
      LetA canIssue : Bool <- isNoReadPending ;
      LetIf accepted : Bool <-
        If #canIssue Then (
          LetA rdy : Bool <- liftAction child0Path (implRegionsReadRq regions addr memSize) ;
          If #rdy Then (
            WriteReg pMemPending (mkSome #addr) Retv
          ) ;
          Return #rdy
        ) Else (
          Return (ConstBool false)
        ) ;
      Return #accepted.

    Definition implGetMemRp : Action ty implMemTree (Option FullCapWithTag) :=
      ReadReg "memP" pMemPending (fun memP =>
      LetIf res : Option FullCapWithTag <-
        If (##memP `? "Some") Then (
          Let  addr  : Addr                  <- ##memP `! "Some" ;
          LetA rpOpt : Option FullCapWithTag <- liftAction child0Path (implRegionsReadRp regions addr) ;
          If (##rpOpt `? "Some") Then (
            WriteReg pMemPending ConstDef Retv
          ) ;
          Return #rpOpt
        ) Else (
          Return ConstDef
        ) ;
      Return #res).

    (* 3. Revocation Bit Memory Channel *)
    Definition implReadRevBitRq (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
      LetA canIssue : Bool <- isNoReadPending ;
      LetIf accepted : Bool <-
        If #canIssue Then (
          LetL lookup : RevBitLookup <- computeRevBitAddr revConfig base ;
          LetIf rdy : Bool <-
            If (##lookup`"isRevokable") Then (
              Let revByteAddr : Addr <- ##lookup`"revByteAddr" ;
              Let sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
              liftAction child0Path (implRegionsReadRq regions revByteAddr sz0)
            ) Else (
              Return (ConstBool true)
            ) ;
          If #rdy Then (
            WriteReg pRevPending (mkSome #base) Retv
          ) ;
          Return #rdy
        ) Else (
          Return (ConstBool false)
        ) ;
      Return #accepted.

    Definition implGetRevBitRp : Action ty implMemTree (Option Bool) :=
      ReadReg "revP" pRevPending (fun revP =>
      LetIf res : Option Bool <-
        If (##revP `? "Some") Then (
          Let  base   : Bit (AddrSz + 1) <- ##revP `! "Some" ;
          LetL lookup : RevBitLookup     <- computeRevBitAddr revConfig base ;
          LetIf revOpt : Option Bool <-
            If (##lookup`"isRevokable") Then (
              Let  revByteAddr : Addr                  <- ##lookup`"revByteAddr" ;
              LetA rpOpt       : Option FullCapWithTag <- liftAction child0Path (implRegionsReadRp regions revByteAddr) ;
              LetIf rOpt : Option Bool <-
                If (##rpOpt `? "Some") Then (
                  Let revCap  : FullCapWithTag <- ##rpOpt `! "Some" ;
                  Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
                  Let revBit  : Bool           <- extractRevBit lookup #revByte ;
                  Act (WriteReg pRevPending ConstDef Retv) ;
                  Return (mkSome #revBit)
                ) Else (
                  Return ConstDef
                ) ;
              Return #rOpt
            ) Else (
              Act (WriteReg pRevPending ConstDef Retv) ;
              Return (mkSome (ConstBool false))
            ) ;
          Return #revOpt
        ) Else (
          Return ConstDef
        ) ;
      Return #res).

    (* 4. Memory Write Channel (with store-address snooping for split-phase revoker) *)
    Definition implWriteMem (addr : ty Addr) (stVal : ty FullCapWithTag)
                            (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
      Act (@implRevokerSnoopStore ty implMemTree pRevPhase pRevScanAddrMsb pRevStoreSnoopHit eq_refl eq_refl eq_refl addr memSize) ;
      liftAction child0Path (implRegionsWrite regions addr stVal memSize).

    (* 5. FENCE & FENCE.I Synchronization Channels *)
    Definition implFenceReq (_ : ty FenceOp) : Action ty implMemTree Bool :=
      Return (ConstBool true).

    Definition implFenceIReq : Action ty implMemTree Bool :=
      Return (ConstBool true).

    Definition implFenceIAck : Action ty implMemTree Bool :=
      Return (ConstBool true).

    Definition implMemStepSecondLine : Action ty implMemTree (Bit 0) :=
      liftAction child0Path (@implRegionsStepSecondLine ty regions).

    (* 6. Split-Phase Autonomous Revoker Steps (5 independent forward-ordered actions) *)
    Definition implRevokerSteps (rev : @RevokerInstance dom regions) : list (Action ty implMemTree (Bit 0)) :=
      @implRevokerStepsFsm
        dom
        ty
        implMemTree
        pRevPhase
        pRevScanAddrMsb
        pRevScanCap
        pRevStoreSnoopHit
        eq_refl
        eq_refl
        eq_refl
        eq_refl
        revConfig
        (fun k a => implMemNthRegionAction rev.(revokerIdx) (@revokerRegion dom regions rev) rev.(pfRevoker) a)
        isNoCorePending
        (fun addr sz => liftAction child0Path (implRegionsReadRq regions addr sz))
        (fun addr => liftAction child0Path (implRegionsReadRp regions addr))
        (fun addr stVal sz => liftAction child0Path (implRegionsWrite regions addr stVal sz)).

    (* 7. Top-level MemIfc Instance *)
    Definition implMemIfc : @MemIfc ty := {|
      memTree          := implMemTree ;
      mem_readInstRq   := implReadInstRq ;
      mem_getInstRp    := implGetInstRp ;
      mem_readMemRq    := implReadMemRq ;
      mem_getMemRp     := implGetMemRp ;
      mem_readRevBitRq := implReadRevBitRq ;
      mem_getRevBitRp  := implGetRevBitRp ;
      mem_writeMem     := implWriteMem ;
      mem_fence_req    := implFenceReq ;
      mem_fenceI_req   := implFenceIReq ;
      mem_fenceI_ack   := implFenceIAck
    |}.

  End Ty.

End ImplMemModel.
