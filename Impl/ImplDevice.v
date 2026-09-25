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
  mem_getInstRp    : ty Addr -> Action ty memTree (Option Inst) ;

  (* 2. Data Load Channel *)
  mem_readMemRq    : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;
  mem_getMemRp     : ty Addr -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree (Option FullCapWithTag) ;

  (* 3. Revocation Bit Memory Channel *)
  mem_readRevBitRq : ty (Bit (AddrSz + 1)) -> Action ty memTree Bool ;
  mem_getRevBitRp  : ty (Bit (AddrSz + 1)) -> Action ty memTree (Option Bool) ;

  (* 4. Memory Write Channel *)
  mem_writeMem     : ty Addr -> ty FullCapWithTag -> ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree Bool ;

  (* 5. FENCE & FENCE.I Synchronization Channels *)
  mem_fence_req    : ty FenceOp -> Action ty memTree Bool ;
  mem_fenceI_req   : Action ty memTree Bool ;
  mem_fenceI_ack   : Action ty memTree Bool
}.

(* ===========================================================================
 * Split-Phase MemRegion Trees
 * =========================================================================== *)

Definition implInternalMemRegionTree (r : MemRegion) (isAccessible : bool) : Tree DomainElem :=
  internalMemRegionTree r isAccessible.

Definition implExternalMemRegionChildren (r : MemRegion) : list (Tree DomainElem) :=
  externalMemRegionChildren r.

Definition implExternalMemRegionTree (r : MemRegion) : Tree DomainElem :=
  externalMemRegionTree r.

Definition implCustomMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
  Node r.(regionName) [
    customMemRegionTree r children ;
    Leaf "rpReg" (r.(regionDom), EReg (Build_Reg (Option (LineReadRp r.(regionLineCfg))) (Some (getDefault _)) false))
  ].

Arguments implInternalMemRegionTree r isAccessible : clear implicits.
Arguments implExternalMemRegionChildren r : clear implicits.
Arguments implExternalMemRegionTree r : clear implicits.
Arguments implCustomMemRegionTree r children : clear implicits.

Definition implMemRegionTree (r : MemRegion) : Tree DomainElem :=
  match r.(regionKind) with
  | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
  | ExternalMem => implExternalMemRegionTree r
  | CustomMem children _ _ _ => implCustomMemRegionTree r children
  end.

(* ===========================================================================
 * Split-Phase Line-Level Actions for Each Region Kind
 * =========================================================================== *)

Section ImplInternalMemRegionActions.
  Variable r : MemRegion.
  Variable isAccessible : bool.
  Variable ty : Kind -> Type.

  Local Definition tInt := implInternalMemRegionTree r isAccessible.

  Definition internalMemLineReadRq (addr : ty Addr) : Action ty tInt Bool :=
    internalMemRegionLineReadRq r isAccessible addr.

  Definition internalMemLineWriteRq (rq : ty (LineWriteRq r.(regionLineCfg))) : Action ty tInt Bool :=
    internalMemRegionLineWrite r isAccessible rq.

  Definition internalMemLineReadRp : Action ty tInt (Option (LineReadRp r.(regionLineCfg))) :=
    internalMemRegionLineReadRp r isAccessible.

End ImplInternalMemRegionActions.

Arguments internalMemLineReadRq r isAccessible [ty] addr.
Arguments internalMemLineWriteRq r isAccessible [ty] rq.
Arguments internalMemLineReadRp r isAccessible {ty}.

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
           : Action ty (implMemRegionTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem isAccessible _ _ => internalMemLineReadRq r isAccessible addr
  | ExternalMem => externalMemLineReadRq r addr
  | CustomMem children readAction _ _ => customMemLineReadRq r children readAction addr
  end.

Definition lineWriteRq
           (ty : Kind -> Type)
           (r : MemRegion)
           (rq : ty (LineWriteRq r.(regionLineCfg)))
           : Action ty (implMemRegionTree r) Bool :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) Bool with
  | InternalMem isAccessible _ _ => internalMemLineWriteRq r isAccessible rq
  | ExternalMem => externalMemLineWriteRq r rq
  | CustomMem children _ writeAction _ => customMemLineWriteRq r children writeAction rq
  end.

Definition lineReadRp
           (ty : Kind -> Type)
           (r : MemRegion)
           : Action ty (implMemRegionTree r) (Option (LineReadRp r.(regionLineCfg))) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => implInternalMemRegionTree r isAccessible
                                              | ExternalMem => implExternalMemRegionTree r
                                              | CustomMem children _ _ _ => implCustomMemRegionTree r children
                                              end) (Option (LineReadRp r.(regionLineCfg))) with
  | InternalMem isAccessible _ _ => internalMemLineReadRp r isAccessible
  | ExternalMem => externalMemLineReadRp r
  | CustomMem children _ _ _ => customMemLineReadRp r children
  end.

Arguments lineReadRq [ty] r addr.
Arguments lineWriteRq [ty] r rq.
Arguments lineReadRp [ty] r.

(* ===========================================================================
 * Per-Region Split-Phase Multi-Byte Read & Write
 * =========================================================================== *)

Section ImplMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Let tR := implMemRegionTree r.
  Let lBytes := lineBytes r.
  Let nTags := numLineTags r.
  Let lgLineBytesZ := Z.of_nat (lgLineBytes r).

  Let castAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

  Let lineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytesZ) :=
    TruncLsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Let lgNumDXlenZ : Z := (lgLineBytesZ - LgNumBytesFullCapSz)%Z.

  Let castLineOffsetForTag (offset : Expr ty (Bit lgLineBytesZ))
    : Expr ty (Bit (LgNumBytesFullCapSz + lgNumDXlenZ)%Z) :=
    castBits (eq_sym (add_sub_cancel lgLineBytesZ LgNumBytesFullCapSz)) offset.

  Let tagSlot (addr : Expr ty Addr) : Expr ty (Bit lgNumDXlenZ) :=
    TruncMsb lgNumDXlenZ LgNumBytesFullCapSz (castLineOffsetForTag (lineOffset addr)).

  Let extractReadCap
                   (addr : Expr ty Addr)
                   (memSize : Expr ty (Bit LgLgNumBytesFullCapSz))
                   (lineData : Expr ty (Array lBytes (Bit 8)))
                   (tagArr : Expr ty (Array nTags Bool))
                   : Expr ty FullCapWithTag :=
    let capOffset := TruncLsb TagAddrWidth LgNumBytesFullCapSz addr in
    let isCapAligned := isZero capOffset in
    let isCap := And [Eq memSize $LgNumBytesFullCapSz ; isCapAligned] in
    let rotData := ArrayRotr lineData (lineOffset addr) in
    let dataBytes := slice rotData (Const ty (Bit lgLineBytesZ) Zmod.zero) (Z.to_nat NumBytesFullCapSz) in
    let rawData := ToBit dataBytes in
    let rawTag :=
      if hasTags r then
        ReadArray tagArr (tagSlot addr)
      else
        ConstBool false in
    STRUCT {
      "tag"  ::= And [ isCap ; rawTag ] ;
      "cap"  ::= FromBit Cap (TruncMsb CapSz AddrSz rawData) ;
      "addr" ::= TruncLsb CapSz AddrSz rawData
    }.

  Definition implMemRegionReadRq
             (addr : ty Addr)
             : Action ty tR Bool :=
    lineReadRq r addr.

  Definition implMemRegionReadRp
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR (Option FullCapWithTag) :=
    LetA rpOpt : Option (LineReadRp r.(regionLineCfg)) <- @lineReadRp ty r ;
    LetIf resOpt : Option FullCapWithTag <-
      If (##rpOpt `? "Some") Then (
        Let rp  : LineReadRp r.(regionLineCfg) <- ##rpOpt `! "Some" ;
        Let res : FullCapWithTag               <- extractReadCap #addr #memSize (##rp`"data") (##rp`"tag") ;
        Return (mkSome #res)
      ) Else (
        Return ConstDef
      ) ;
    Return #resOpt.

  Definition implMemRegionWrite
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR Bool :=
    if r.(isReadOnly) then (
      Return (ConstBool true)
    ) else (
      Let capOffset    : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz #addr ;
      Let isCapAligned : Bool                    <- isZero #capOffset ;
      Let isCap        : Bool                    <- And [Eq #memSize $LgNumBytesFullCapSz ; #isCapAligned] ;
      Let rawData      : Bit FullCapSz <-
        ITE #isCap
            {< ToBit (##stVal`"cap"), ##stVal`"addr" >}
            (ZeroExtendTo FullCapSz (##stVal`"addr")) ;
      Let capBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
        FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData ;
      Let baseData : Array lBytes (Bit 8) <- embedCapBytes lBytes #capBytes ;
      Let rotData  : Array lBytes (Bit 8) <- ArrayRotl #baseData (lineOffset #addr) ;
      Let numBytesActive : Bit (lgLineBytesZ + 1)%Z <-
        Sll $1 (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z #memSize) ;
      Let numBytesActiveDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
        Sll $1 (ZeroExtend (LgNumBytesFullCapSz + 1 - LgLgNumBytesFullCapSz)%Z #memSize) ;
      Let endOffsetDXlen : Bit (LgNumBytesFullCapSz + 1)%Z <-
        Add [ ZeroExtend 1 #capOffset ; #numBytesActiveDXlen ] ;
      Let crossesDXlen : Bool <- FromBit Bool (TruncMsb 1 LgNumBytesFullCapSz (Sub #endOffsetDXlen $1)) ;
      Let isWrites : Array lBytes Bool <-
        FromBit (Array lBytes Bool)
          (rotateLeft (Not (Sll (ConstBit (InvDefault _)) #numBytesActive)) (lineOffset #addr)) ;
      Let tagData : Array nTags Bool <-
        if hasTags r then
          UpdateArray ConstDef (tagSlot #addr) (And [ #isCap ; ##stVal`"tag" ])
        else
          ConstDef ;
      Let nextTagSlot : Bit lgNumDXlenZ <- Add [ tagSlot #addr ; $1 ] ;
      Let tagMask : Array nTags Bool <-
        if hasTags r then
          UpdateArray
            (UpdateArray ConstDef #nextTagSlot #crossesDXlen)
            (tagSlot #addr)
            (ConstBool true)
        else
          ConstDef ;
      Let rq : LineWriteRq r.(regionLineCfg) <- STRUCT {
        "addr"     ::= #addr ;
        "data"     ::= #rotData ;
        "dataMask" ::= #isWrites ;
        "tag"      ::= #tagData ;
        "tagMask"  ::= #tagMask
      } ;
      lineWriteRq r rq
    ).

End ImplMemRegionActions.

Arguments implMemRegionReadRq r [ty] addr.
Arguments implMemRegionReadRp r [ty] addr memSize.
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
           : Action ty (implRegionsTree regions) Bool :=
    match regions return Action ty (implRegionsTree regions) Bool with
    | [] => Return (ConstBool true)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rdy : Bool <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRq r addr)
          ) Else (
            liftAction child1Path (implRegionsReadRq rs addr)
          ) ;
        Return #rdy
    end.

  Fixpoint implRegionsReadRp
           (regions : list MemRegion)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (implRegionsTree regions) (Option FullCapWithTag) :=
    match regions return Action ty (implRegionsTree regions) (Option FullCapWithTag) with
    | [] => Return (mkSome ConstDef)
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf rpOpt : Option FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (implMemRegionReadRp r addr memSize)
          ) Else (
            liftAction child1Path (implRegionsReadRp rs addr memSize)
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
    unfold implMemRegionTree.
    destruct (r.(regionKind)) as [isAccessible initData initTags | | children readAction writeAction irqAction].
    - exact act.
    - exact act.
    - exact (liftAction child0Path act).
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

  Fixpoint implCollectTargetPortActions
    (rs : list MemRegion)
    : list (string * (forall ty, Action ty (implRegionsTree rs) (Bit 0))) :=
    match rs return list (string * (forall ty, Action ty (implRegionsTree rs) (Bit 0))) with
    | [] => []
    | r :: rs' =>
        let cur := map (fun '(d, act) =>
                          (d, fun ty => liftAction child0Path (liftToImplRegion r (act ty))))
                       (memRegionTargetPortActions r) in
        let rest := map (fun '(d, act) =>
                           (d, fun ty => liftAction child1Path (act ty)))
                        (implCollectTargetPortActions rs') in
        (cur ++ rest)%list
    end.

  Definition implMemTree : Tree DomainElem :=
    Node "mem" [
      implRegionsTree regions ;
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

    Definition implMemCollectTargetPortActions : list (string * Action ty implMemTree (Bit 0)) :=
      map (fun '(d, f) => (d, liftAction child0Path (f ty))) (implCollectTargetPortActions regions).

    Local Definition pRevPhase         : RegPath implMemTree := Build_RegPath implMemTree (inr (inl tt)) I.
    Local Definition pRevScanAddrMsb   : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inl tt))) I.
    Local Definition pRevScanCap       : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inl tt)))) I.
    Local Definition pRevStoreSnoopHit : RegPath implMemTree := Build_RegPath implMemTree (inr (inr (inr (inr (inl tt))))) I.

    (* 1. Instruction Memory Channel *)
    Definition implReadInstRq (addr : ty Addr) : Action ty implMemTree Bool :=
      liftAction child0Path (implRegionsReadRq regions addr).

    Definition implGetInstRp (addr : ty Addr) : Action ty implMemTree (Option Inst) :=
      Let instSz : Bit LgLgNumBytesFullCapSz <- $LgNumBytesInstSz ;
      LetA rpOpt : Option FullCapWithTag <- liftAction child0Path (implRegionsReadRp regions addr instSz) ;
      LetIf instOpt : Option Inst <-
        If (##rpOpt `? "Some") Then (
          Let fullVal : FullCapWithTag <- ##rpOpt `! "Some" ;
          Return (mkSome (##fullVal`"addr"))
        ) Else (
          Return ConstDef
        ) ;
      Return #instOpt.

    (* 2. Data Load Channel *)
    Definition implReadMemRq (addr : ty Addr) (_ : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree Bool :=
      liftAction child0Path (implRegionsReadRq regions addr).

    Definition implGetMemRp (addr : ty Addr) (memSize : ty (Bit LgLgNumBytesFullCapSz)) : Action ty implMemTree (Option FullCapWithTag) :=
      liftAction child0Path (implRegionsReadRp regions addr memSize).

    (* 3. Revocation Bit Memory Channel *)
    Definition implReadRevBitRq (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree Bool :=
      LetL lookup : RevBitLookup <- computeRevBitAddr revConfig base ;
      LetIf rdy : Bool <-
        If (##lookup`"isRevokable") Then (
          Let revByteAddr : Addr <- ##lookup`"revByteAddr" ;
          liftAction child0Path (implRegionsReadRq regions revByteAddr)
        ) Else (
          Return (ConstBool true)
        ) ;
      Return #rdy.

    Definition implGetRevBitRp (base : ty (Bit (AddrSz + 1))) : Action ty implMemTree (Option Bool) :=
      LetL lookup : RevBitLookup <- computeRevBitAddr revConfig base ;
      LetIf revOpt : Option Bool <-
        If (##lookup`"isRevokable") Then (
          Let  revByteAddr : Addr                      <- ##lookup`"revByteAddr" ;
          Let  sz0         : Bit LgLgNumBytesFullCapSz <- $0 ;
          LetA rpOpt       : Option FullCapWithTag     <- liftAction child0Path (implRegionsReadRp regions revByteAddr sz0) ;
          LetIf rOpt : Option Bool <-
            If (##rpOpt `? "Some") Then (
              Let revCap  : FullCapWithTag <- ##rpOpt `! "Some" ;
              Let revByte : Bit 8          <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
              Let revBit  : Bool           <- extractRevBit lookup #revByte ;
              Return (mkSome #revBit)
            ) Else (
              Return ConstDef
            ) ;
          Return #rOpt
        ) Else (
          Return (mkSome (ConstBool false))
        ) ;
      Return #revOpt.

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
        (fun addr => liftAction child0Path (implRegionsReadRq regions addr))
        (fun addr sz => liftAction child0Path (implRegionsReadRp regions addr sz))
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
