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
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * MemRegion Definition & Disjointness Checking
 * =========================================================================== *)

Record LineConfig := {
  cfgLgLineBytes : nat ;
  cfgHasTags     : bool ;
  cfgTaggedPf    : if cfgHasTags
                   then Is_true (Z.to_nat LgNumBytesFullCapSz <=? cfgLgLineBytes)%nat
                   else True
}.

Definition TaggedLine (lgLineBytes : nat) (pf : Is_true (Z.to_nat LgNumBytesFullCapSz <=? lgLineBytes)%nat) : LineConfig :=
  {| cfgLgLineBytes := lgLineBytes ; cfgHasTags := true ; cfgTaggedPf := pf |}.

Definition RawLine (lgLineBytes : nat) : LineConfig :=
  {| cfgLgLineBytes := lgLineBytes ; cfgHasTags := false ; cfgTaggedPf := I |}.

Definition cfgLineBytes (cfg : LineConfig) : nat :=
  Nat.pow 2 (cfgLgLineBytes cfg).

Definition cfgNumLineTags (cfg : LineConfig) : nat :=
  if cfgHasTags cfg
  then Nat.pow 2 (cfgLgLineBytes cfg - Z.to_nat LgNumBytesFullCapSz)
  else 0%nat.

Definition cfgNumLines (regionSize : Z) (cfg : LineConfig) : nat :=
  Z.to_nat (regionSize / Z.of_nat (cfgLineBytes cfg)).

Definition cfgTagNumLines (regionSize : Z) (cfg : LineConfig) : nat :=
  if cfgHasTags cfg then cfgNumLines regionSize cfg else 0%nat.

Definition cfgTagTotal (regionSize : Z) (cfg : LineConfig) : nat :=
  (cfgTagNumLines regionSize cfg * cfgNumLineTags cfg)%nat.

Definition defaultTagsInit (regionSize : Z) (cfg : LineConfig)
  : option (option (type (Array (cfgTagTotal regionSize cfg) Bool))) :=
  Some (Some (getDefault _)).

Fixpoint takeChunk {A} (k : nat) (def : A) (ls : list A) : list A :=
  match k with
  | 0%nat => []
  | S k' =>
      match ls with
      | [] => def :: takeChunk k' def []
      | x :: xs => x :: takeChunk k' def xs
      end
  end.

Lemma takeChunk_length {A} (k : nat) (def : A) (ls : list A) :
  List.length (takeChunk k def ls) = k.
Proof.
  revert ls; induction k as [| k' IH]; intros ls; simpl; auto.
  destruct ls; simpl; f_equal; apply IH.
Qed.

Definition bytesToMemInit (regionSize : Z) (bytes : list (bits 8))
  : option (option (type (Array (Z.to_nat regionSize) (Bit 8)))) :=
  let sz := Z.to_nat regionSize in
  Some (Some (Build_SameTuple (tupleElems := takeChunk sz Zmod.zero bytes)
                              (transparent_Is_true _ (Is_true_Nat_eq_implies (takeChunk_length sz Zmod.zero bytes))))).

Fixpoint strideStep {A} (stride : nat) (def : A) (n : nat) (ls : list A) : list A :=
  match n with
  | 0%nat => []
  | S n' =>
      match ls with
      | [] => def :: strideStep stride def n' []
      | x :: _ => x :: strideStep stride def n' (skipn stride ls)
      end
  end.

Lemma strideStep_length {A} (stride : nat) (def : A) (n : nat) (ls : list A) :
  List.length (strideStep stride def n ls) = n.
Proof.
  revert ls; induction n as [| n' IH]; intros ls; simpl; auto.
  destruct ls; simpl; f_equal; apply IH.
Qed.

Definition buildStrideTuple {A} (stride : nat) (def : A) (n b : nat) (ls : list A)
  : SameTuple A n :=
  Build_SameTuple (tupleElems := strideStep stride def n (skipn b ls))
                  (transparent_Is_true _ (Is_true_Nat_eq_implies (strideStep_length stride def n (skipn b ls)))).

Notation LineReadRp cfg := (STRUCT_TYPE {
  "data" :: Array (cfgLineBytes cfg) (Bit 8) ;
  "tag"  :: Array (cfgNumLineTags cfg) Bool
}).

Notation LineWriteRq cfg := (STRUCT_TYPE {
  "addr"     :: Addr ;
  "data"     :: Array (cfgLineBytes cfg) (Bit 8) ;
  "dataMask" :: Array (cfgLineBytes cfg) Bool ;
  "tag"      :: Array (cfgNumLineTags cfg) Bool ;
  "tagMask"  :: Array (cfgNumLineTags cfg) Bool
}).

Inductive RegionKind (regionName : string) (regionSize : Z) (cfg : LineConfig) :=
| InternalMem (isAccessible : bool)
              (initData : option (option (type (Array (Z.to_nat regionSize) (Bit 8)))))
              (initTags : option (option (type (Array (cfgTagTotal regionSize cfg) Bool))))
| ExternalMem
| CustomMem (children : list (Tree DomainElem))
            (readAction : forall ty, ty Addr ->
                          Action ty (Node regionName children) (LineReadRp cfg))
            (writeAction : forall ty, ty (LineWriteRq cfg) ->
                           Action ty (Node regionName children) (Bit 0))
            (irqAction : option (forall ty, Action ty (Node regionName children) Bool)).

Arguments InternalMem {regionName regionSize cfg} isAccessible initData initTags.
Arguments ExternalMem {regionName regionSize cfg}.
Arguments CustomMem {regionName regionSize cfg} children readAction writeAction irqAction.

Record MemRegion := {
  regionName        : string ;
  regionDom         : string ;
  regionBase        : Z ;
  regionSize        : Z ;
  regionLineCfg     : LineConfig ;
  isReadOnly        : bool ;
  regionKind        : RegionKind regionName regionSize regionLineCfg ;
  regionInMemory    : Is_true ((0 <=? regionBase) && (regionBase + regionSize <=? Z.shiftl 1 AddrSz))%Z ;
  regionBaseAligned : Is_true (regionBase mod (2 ^ Z.of_nat (cfgLgLineBytes regionLineCfg)) =? 0)%Z ;
  regionSizeAligned : Is_true (regionSize mod (2 ^ Z.of_nat (cfgLgLineBytes regionLineCfg)) =? 0)%Z
}.

Definition hasTags (r : MemRegion) : bool :=
  cfgHasTags r.(regionLineCfg).

Definition lgLineBytes (r : MemRegion) : nat :=
  cfgLgLineBytes r.(regionLineCfg).

Definition lineBytes (r : MemRegion) : nat :=
  cfgLineBytes r.(regionLineCfg).

Definition numLineTags (r : MemRegion) : nat :=
  cfgNumLineTags r.(regionLineCfg).

Definition disjointBool (r1 r2 : MemRegion) : bool :=
  (r1.(regionBase) + r1.(regionSize) <=? r2.(regionBase))%Z ||
  (r2.(regionBase) + r2.(regionSize) <=? r1.(regionBase))%Z.

Fixpoint pairwiseDisjoint (l : list MemRegion) : bool :=
  match l with
  | [] => true
  | r :: rs => forallb (disjointBool r) rs && pairwiseDisjoint rs
  end.

Definition isRegionAddr {ty : Kind -> Type} (r : MemRegion) (addr : Expr ty Addr) : Expr ty Bool :=
  And [ Uge addr $(r.(regionBase)) ; Ult addr $(r.(regionBase) + r.(regionSize)) ].

Definition regionNumLines (r : MemRegion) : nat :=
  cfgNumLines r.(regionSize) r.(regionLineCfg).

Definition regionTagSize (r : MemRegion) : nat :=
  cfgTagNumLines r.(regionSize) r.(regionLineCfg).

(* ===========================================================================
 * Payload Utilities
 * =========================================================================== *)

Definition embedCapBytes {ty : Kind -> Type} (numBytes : nat)
  (capBytes : Expr ty (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)))
  : Expr ty (Array numBytes (Bit 8)) :=
  ArrayBuilder (fun (i : FinType numBytes) =>
    readNatToFinType (Const ty (Bit 8) Zmod.zero)
                     (ReadArrayConst capBytes)
                     (finNum i)).

Lemma add_sub_cancel (a l : Z) : (l + (a - l))%Z = a.
Proof. lia. Qed.

(* ===========================================================================
 * Banked Internal Memory Helpers & Converting a MemRegion into a Tree
 * =========================================================================== *)

Definition extractBankDataInit (r : MemRegion) (b : nat)
  : option (option (type (Array (regionNumLines r) (Bit 8)))) :=
  match r.(regionKind) with
  | InternalMem _ (Some (Some tup)) _ =>
      Some (Some (buildStrideTuple (lineBytes r) Zmod.zero (regionNumLines r) b tup.(tupleElems)))
  | InternalMem _ (Some None) _ => Some None
  | _ => None
  end.

Definition extractBankTagInit (r : MemRegion) (b : nat)
  : option (option (type (Array (regionNumLines r) Bool))) :=
  match r.(regionKind) with
  | InternalMem _ _ (Some (Some tup)) =>
      if hasTags r
      then Some (Some (buildStrideTuple (numLineTags r) false (regionNumLines r) b tup.(tupleElems)))
      else None
  | InternalMem _ _ (Some None) => Some None
  | _ => None
  end.

Definition memBankLeaf (r : MemRegion) (b : nat) : Tree DomainElem :=
  Leaf "memBank" (r.(regionDom), EMem (@Build_Mem (regionNumLines r) (Bit 8) 1%nat (extractBankDataInit r b))).

Definition tagBankLeaf (r : MemRegion) (b : nat) : Tree DomainElem :=
  Leaf "tagBank" (r.(regionDom), EMem (@Build_Mem (regionNumLines r) Bool 1%nat (extractBankTagInit r b))).

Fixpoint leaf_list_path_seq {A} (f : nat -> Tree A) (default_path : forall k, LeafPath (f k))
  (start n : nat) (p : FinType n) :
  (fix loop (ls : list (Tree A)) : Type :=
     match ls with
     | nil => Empty_set
     | x :: xs => (LeafPath x + loop xs)%type
     end) (map f (seq start n)) :=
  match n return forall (p : FinType n),
    (fix loop (ls : list (Tree A)) : Type :=
       match ls with
       | nil => Empty_set
       | x :: xs => (LeafPath x + loop xs)%type
       end) (map f (seq start n)) with
  | O => fun p => match (Nat_ltb_0 p.(finLt)) with end
  | S m => fun p =>
      match p.(finNum) as inum return forall pf : Is_true (inum <? S m)%nat,
        (fix loop (ls : list (Tree A)) : Type :=
           match ls with
           | nil => Empty_set
           | x :: xs => (LeafPath x + loop xs)%type
           end) (map f (seq start (S m))) with
      | O => fun _ => inl (default_path start)
      | S k => fun pf => inr (@leaf_list_path_seq A f default_path (S start) m (Build_FinType k pf))
      end p.(finLt)
  end p.

Arguments leaf_list_path_seq [A] f default_path start [n] p.

Lemma getLeaf_seq {A} (nodeName : string) (f : nat -> Tree A) (default_path : forall k, LeafPath (f k))
  (start n : nat) (i : FinType n) :
  @getLeaf A (Node nodeName (map f (seq start n))) (leaf_list_path_seq f default_path start i) =
  @getLeaf A (f (start + i.(finNum))%nat) (default_path (start + i.(finNum))%nat).
Proof.
  revert start.
  induction n; intros start.
  - destruct i as [inum ilt].
    destruct (Nat_ltb_0 ilt).
  - destruct i as [inum ilt].
    simpl.
    destruct inum.
    + rewrite Nat.add_0_r. reflexivity.
    + simpl.
      pose proof (IHn (Build_FinType inum ilt) (S start)) as H.
      simpl in H.
      rewrite H.
      rewrite Nat.add_succ_r.
      reflexivity.
Qed.

Definition internalMemTargetPortChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "lineReadRq" (r.(regionDom), ERecv (Option Addr)) ;
    Leaf "lineReadRp" (r.(regionDom), ESend (LineReadRp r.(regionLineCfg))) ;
    Leaf "lineWriteRq" (r.(regionDom), ERecv (Option (LineWriteRq r.(regionLineCfg))))
  ].

Definition internalMemRegionChildren
           (r : MemRegion)
           (isAccessible : bool)
           : list (Tree DomainElem) :=
  ([ Node "memBanks" (map (memBankLeaf r) (seq 0 (lineBytes r))) ;
     Node "tagBanks" (map (tagBankLeaf r) (seq 0 (numLineTags r)))
   ] ++ if isAccessible then internalMemTargetPortChildren r else [])%list.

Definition externalMemRegionChildren (r : MemRegion) : list (Tree DomainElem) :=
  [ Leaf "lineReadRq" (r.(regionDom), ESend Addr) ;
    Leaf "lineReadRp" (r.(regionDom), ERecv (LineReadRp r.(regionLineCfg))) ;
    Leaf "lineWriteRq" (r.(regionDom), ESend (LineWriteRq r.(regionLineCfg)))
  ].

Arguments internalMemRegionChildren r isAccessible : clear implicits.
Arguments externalMemRegionChildren r : clear implicits.

Definition internalMemRegionTree
           (r : MemRegion)
           (isAccessible : bool)
           : Tree DomainElem :=
  Node r.(regionName) (internalMemRegionChildren r isAccessible).

Definition externalMemRegionTree (r : MemRegion) : Tree DomainElem :=
  Node r.(regionName) (externalMemRegionChildren r).

Definition customMemRegionTree (r : MemRegion) (children : list (Tree DomainElem)) : Tree DomainElem :=
  Node r.(regionName) children.

Arguments internalMemRegionTree r isAccessible : clear implicits.
Arguments externalMemRegionTree r : clear implicits.
Arguments customMemRegionTree r children : clear implicits.

Definition memRegionTree (r : MemRegion) : Tree DomainElem :=
  match r.(regionKind) with
  | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
  | ExternalMem => externalMemRegionTree r
  | CustomMem children _ _ _ => customMemRegionTree r children
  end.

(* ===========================================================================
 * Line-Level Actions for Each Region Kind
 * =========================================================================== *)

Section InternalMemRegionActions.
  Variable r : MemRegion.
  Variable isAccessible : bool.
  Variable ty : Kind -> Type.

  Let tInt := internalMemRegionTree r isAccessible.
  Let numLines := regionNumLines r.
  Let lBytes := lineBytes r.
  Let nTags := numLineTags r.
  Let lgLineBytesZ := Z.of_nat (lgLineBytes r).
  Let port0 : FinType 1%nat := @Build_FinType 1%nat 0%nat I.

  Local Definition leaf_list_path_mem (n : nat) (p : FinType n) :=
    leaf_list_path_seq (memBankLeaf r) (fun _ => tt) 0 p.

  Local Definition leaf_list_path_tag (n : nat) (p : FinType n) :=
    leaf_list_path_seq (tagBankLeaf r) (fun _ => tt) 0 p.

  Local Lemma leaf_list_path_mem_is_mem n (i : FinType n) :
    Is_true (isMemElem (@getLeafElem (Node "memBanks" (map (memBankLeaf r) (seq 0 n))) (leaf_list_path_mem i))).
  Proof.
    unfold leaf_list_path_mem, getLeafElem.
    rewrite getLeaf_seq.
    simpl.
    exact I.
  Qed.

  Local Lemma leaf_list_path_tag_is_mem n (i : FinType n) :
    Is_true (isMemElem (@getLeafElem (Node "tagBanks" (map (tagBankLeaf r) (seq 0 n))) (leaf_list_path_tag i))).
  Proof.
    unfold leaf_list_path_tag, getLeafElem.
    rewrite getLeaf_seq.
    simpl.
    exact I.
  Qed.

  Local Definition memBankPath (i : FinType lBytes) : MemPath tInt.
  Proof.
    refine (Build_MemPath tInt (inl (leaf_list_path_mem i)) _).
    exact (leaf_list_path_mem_is_mem i).
  Defined.

  Local Definition tagBankPath (i : FinType nTags) : MemPath tInt.
  Proof.
    refine (Build_MemPath tInt (inr (inl (leaf_list_path_tag i))) _).
    exact (leaf_list_path_tag_is_mem i).
  Defined.

  Local Lemma memBankEq n (i : FinType n) :
    @getMemFromPathUnsafe (Node "memBanks" (map (memBankLeaf r) (seq 0 n))) (leaf_list_path_mem i) =
    {| memSize := numLines; memKind := Bit 8; memPort := 1; memInit := extractBankDataInit r (0 + i.(finNum)) |}.
  Proof.
    unfold leaf_list_path_mem, getMemFromPathUnsafe, getLeafElem.
    rewrite getLeaf_seq.
    reflexivity.
  Qed.

  Local Lemma tagBankEq n (i : FinType n) :
    @getMemFromPathUnsafe (Node "tagBanks" (map (tagBankLeaf r) (seq 0 n))) (leaf_list_path_tag i) =
    {| memSize := numLines; memKind := Bool; memPort := 1; memInit := extractBankTagInit r (0 + i.(finNum)) |}.
  Proof.
    unfold leaf_list_path_tag, getMemFromPathUnsafe, getLeafElem.
    rewrite getLeaf_seq.
    reflexivity.
  Qed.

  Local Definition memPortCast (i : FinType lBytes) (p : FinType 1%nat) : FinType (memPort (getMemFromPath (memBankPath i))) :=
    match eq_sym (f_equal memPort (memBankEq i)) in _ = Y return FinType Y with
    | eq_refl => p
    end.

  Local Definition tagPortCast (i : FinType nTags) (p : FinType 1%nat) : FinType (memPort (getMemFromPath (tagBankPath i))) :=
    match eq_sym (f_equal memPort (tagBankEq i)) in _ = Y return FinType Y with
    | eq_refl => p
    end.

  Local Definition memSizeCast (i : FinType lBytes) (e : Expr ty (Bit (Z.log2_up (Z.of_nat numLines)))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (memBankPath i)))))) :=
    match eq_sym (f_equal memSize (memBankEq i)) in _ = Y return Expr ty (Bit (Z.log2_up (Z.of_nat Y))) with
    | eq_refl => e
    end.

  Local Definition tagSizeCast (i : FinType nTags) (e : Expr ty (Bit (Z.log2_up (Z.of_nat numLines)))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (tagBankPath i)))))) :=
    match eq_sym (f_equal memSize (tagBankEq i)) in _ = Y return Expr ty (Bit (Z.log2_up (Z.of_nat Y))) with
    | eq_refl => e
    end.

  Local Definition memKindCast (i : FinType lBytes) (e : Expr ty (Bit 8)) :
    Expr ty (memKind (getMemFromPath (memBankPath i))) :=
    match eq_sym (f_equal memKind (memBankEq i)) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Definition memKindCastInv (i : FinType lBytes) (e : Expr ty (memKind (getMemFromPath (memBankPath i)))) :
    Expr ty (Bit 8) :=
    match f_equal memKind (memBankEq i) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Definition tagKindCast (i : FinType nTags) (e : Expr ty Bool) :
    Expr ty (memKind (getMemFromPath (tagBankPath i))) :=
    match eq_sym (f_equal memKind (tagBankEq i)) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Definition tagKindCastInv (i : FinType nTags) (e : Expr ty (memKind (getMemFromPath (tagBankPath i)))) :
    Expr ty Bool :=
    match f_equal memKind (tagBankEq i) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Let castAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

  Let lineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgLineBytesZ)%Z) :=
    TruncMsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Let getLineOffsetIdx (addr : Expr ty Addr) : Expr ty (Bit (Z.log2_up (Z.of_nat numLines))) :=
    getMemOffset (Z.shiftr r.(regionBase) lgLineBytesZ) (Z.of_nat numLines) (lineIndex addr).

  Definition internalMemRegionLineRead (addr : ty Addr)
             : Action ty tInt (LineReadRp r.(regionLineCfg)) :=
    Let lineIdx : Bit (Z.log2_up (Z.of_nat numLines)) <- getLineOffsetIdx #addr ;
    Act (fold_right (fun memIdx acc =>
                       ReadRqMem (memBankPath memIdx) (memSizeCast memIdx #lineIdx) (memPortCast memIdx port0) acc)
                    Retv (genFinType lBytes)) ;
    Act (if hasTags r then (
           fold_right (fun tagIdx acc =>
                         ReadRqMem (tagBankPath tagIdx) (tagSizeCast tagIdx #lineIdx) (tagPortCast tagIdx port0) acc)
                      Retv (genFinType nTags)
         ) else (
           Retv
         )) ;
    LetA dataBytes : Array lBytes (Bit 8) <-
      fold_right (fun memIdx acc =>
                    ReadRpMem "readByteRp" (memBankPath memIdx) (memPortCast memIdx port0)
                      (fun val =>
                         LetA rest : Array lBytes (Bit 8) <- acc ;
                         Return (UpdateArrayConst #rest memIdx (memKindCastInv #val))))
                 (Return ConstDef) (genFinType lBytes) ;
    LetA tagArr : Array nTags Bool <-
      if hasTags r then (
        fold_right (fun tagIdx acc =>
                      ReadRpMem "readTagRp" (tagBankPath tagIdx) (tagPortCast tagIdx port0)
                        (fun val =>
                           LetA rest : Array nTags Bool <- acc ;
                           Return (UpdateArrayConst #rest tagIdx (tagKindCastInv #val))))
                   (Return ConstDef) (genFinType nTags)
      ) else (
        Return ConstDef
      ) ;
    @Return ty tInt (LineReadRp r.(regionLineCfg)) (STRUCT {
      "data" ::= #dataBytes ;
      "tag"  ::= #tagArr
    }).

  Definition internalMemRegionLineWrite
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tInt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Let lineIdx : Bit (Z.log2_up (Z.of_nat numLines)) <- getLineOffsetIdx (##rq`"addr") ;
      Act (fold_right (fun memIdx acc =>
                         If (ReadArrayConst (##rq`"dataMask") memIdx) Then (
                           WriteMem (memBankPath memIdx) (memSizeCast memIdx #lineIdx)
                             (memKindCast memIdx (ReadArrayConst (##rq`"data") memIdx)) Retv
                         ) ;
                         acc)
                      Retv (genFinType lBytes)) ;
      if hasTags r then (
        fold_right (fun tagIdx acc =>
                      If (ReadArrayConst (##rq`"tagMask") tagIdx) Then (
                        WriteMem (tagBankPath tagIdx) (tagSizeCast tagIdx #lineIdx)
                          (tagKindCast tagIdx (ReadArrayConst (##rq`"tag") tagIdx)) Retv
                      ) ;
                      acc)
                   Retv (genFinType nTags)
      ) else (
        Retv
      )
    ).

End InternalMemRegionActions.

Arguments internalMemRegionLineRead r isAccessible [ty] addr.
Arguments internalMemRegionLineWrite r isAccessible [ty] rq.

Section InternalMemTargetPortActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tIntTargetPort := internalMemRegionTree r true.
  Local Definition pTargetPortLineReadRq : RecvPath tIntTargetPort := getChildRecvPathTree tIntTargetPort "lineReadRq".
  Local Definition pTargetPortLineReadRp : SendPath tIntTargetPort := getChildSendPathTree tIntTargetPort "lineReadRp".
  Local Definition pTargetPortLineWriteRq : RecvPath tIntTargetPort := getChildRecvPathTree tIntTargetPort "lineWriteRq".

  Definition internalMemRegionTargetPortRead : Action ty tIntTargetPort (Bit 0) :=
    Recv "rqOpt" pTargetPortLineReadRq (fun rqOpt =>
    If (##rqOpt `? "Some") Then (
      Let addr : Addr <- ##rqOpt `! "Some" ;
      LetA rp : LineReadRp r.(regionLineCfg) <-
        internalMemRegionLineRead r true addr ;
      Send pTargetPortLineReadRp #rp Retv
    ) ;
    Retv).

  Definition internalMemRegionTargetPortWrite : Action ty tIntTargetPort (Bit 0) :=
    Recv "rqOpt" pTargetPortLineWriteRq (fun rqOpt =>
    If (##rqOpt `? "Some") Then (
      Let rq : LineWriteRq r.(regionLineCfg) <- ##rqOpt `! "Some" ;
      internalMemRegionLineWrite r true rq
    ) ;
    Retv).

End InternalMemTargetPortActions.

Arguments internalMemRegionTargetPortRead r {ty}.
Arguments internalMemRegionTargetPortWrite r {ty}.

Section ExternalMemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tExt := externalMemRegionTree r.
  Local Definition pLineReadRq : SendPath tExt := getChildSendPathTree tExt "lineReadRq".
  Local Definition pLineReadRp : RecvPath tExt := getChildRecvPathTree tExt "lineReadRp".
  Local Definition pLineWriteRq : SendPath tExt := getChildSendPathTree tExt "lineWriteRq".

  Definition externalMemRegionLineRead (addr : ty Addr)
             : Action ty tExt (LineReadRp r.(regionLineCfg)) :=
    Send pLineReadRq #addr (
    Recv "rp" pLineReadRp (fun rp =>
    Return #rp)).

  Definition externalMemRegionLineWrite
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tExt (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      Send pLineWriteRq #rq Retv
    ).

End ExternalMemRegionActions.

Arguments externalMemRegionLineRead r [ty] addr.
Arguments externalMemRegionLineWrite r [ty] rq.

Section CustomMemRegionActions.
  Variable r : MemRegion.
  Variable children : list (Tree DomainElem).
  Variable readAction : forall ty, ty Addr ->
                        Action ty (Node r.(regionName) children)
                               (LineReadRp r.(regionLineCfg)).
  Variable writeAction : forall ty, ty (LineWriteRq r.(regionLineCfg)) ->
                         Action ty (Node r.(regionName) children) (Bit 0).
  Variable ty : Kind -> Type.

  Local Definition tCust := customMemRegionTree r children.

  Definition customMemRegionLineRead (addr : ty Addr)
             : Action ty tCust (LineReadRp r.(regionLineCfg)) :=
    readAction addr.

  Definition customMemRegionLineWrite
             (rq : ty (LineWriteRq r.(regionLineCfg)))
             : Action ty tCust (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
    ) else (
      writeAction rq
    ).

End CustomMemRegionActions.

Arguments customMemRegionLineRead r children readAction [ty] addr.
Arguments customMemRegionLineWrite r children writeAction [ty] rq.

Definition memRegionLineRead
           {ty : Kind -> Type}
           (r : MemRegion)
           (addr : ty Addr)
           : Action ty (memRegionTree r) (LineReadRp r.(regionLineCfg)) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                              | ExternalMem => externalMemRegionTree r
                                              | CustomMem children _ _ _ => customMemRegionTree r children
                                              end) (LineReadRp r.(regionLineCfg)) with
  | InternalMem isAccessible _ _ => internalMemRegionLineRead r isAccessible addr
  | ExternalMem => externalMemRegionLineRead r addr
  | CustomMem children readAct writeAct _ => customMemRegionLineRead r children readAct addr
  end.

Definition memRegionLineWrite
           {ty : Kind -> Type}
           (r : MemRegion)
           (rq : ty (LineWriteRq r.(regionLineCfg)))
           : Action ty (memRegionTree r) (Bit 0) :=
  match r.(regionKind) as k return Action ty (match k with
                                              | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                              | ExternalMem => externalMemRegionTree r
                                              | CustomMem children _ _ _ => customMemRegionTree r children
                                              end) (Bit 0) with
  | InternalMem isAccessible _ _ => internalMemRegionLineWrite r isAccessible rq
  | ExternalMem => externalMemRegionLineWrite r rq
  | CustomMem children readAct writeAct _ => customMemRegionLineWrite r children writeAct rq
  end.

Arguments memRegionLineRead [ty] r addr.
Arguments memRegionLineWrite [ty] r rq.

(* ===========================================================================
 * Universal CHERI Capability Multi-Byte Read & Write for a MemRegion
 * =========================================================================== *)

Section MemRegionActions.
  Variable r : MemRegion.
  Variable ty : Kind -> Type.

  Local Definition tR := memRegionTree r.
  Local Definition lBytes := lineBytes r.
  Local Definition nTags := numLineTags r.
  Local Definition lgLineBytesZ := Z.of_nat (lgLineBytes r).

  Local Definition castAddr (addr : Expr ty Addr) : Expr ty (Bit ((lgLineBytesZ + (AddrSz - lgLineBytesZ))%Z)) :=
    castBits (eq_sym (add_sub_cancel AddrSz lgLineBytesZ)) addr.

  Local Definition lineOffset (addr : Expr ty Addr) : Expr ty (Bit lgLineBytesZ) :=
    TruncLsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Local Definition lineIndex (addr : Expr ty Addr) : Expr ty (Bit (AddrSz - lgLineBytesZ)%Z) :=
    TruncMsb (AddrSz - lgLineBytesZ)%Z lgLineBytesZ (castAddr addr).

  Local Definition lineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< lineIndex addr, Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Local Definition nextLineAddr (addr : Expr ty Addr) : Expr ty Addr :=
    castBits (add_sub_cancel AddrSz lgLineBytesZ) {< Add [ lineIndex addr ; $1 ], Const ty (Bit lgLineBytesZ) Zmod.zero >}.

  Local Definition add1 (addr : Expr ty Addr) : Expr ty (Array lBytes Bool) :=
    FromBit (Array lBytes Bool)
      (Not (Sll (ConstBit (InvDefault _)) (lineOffset addr))).

  Local Definition lgNumDXlenZ : Z := (lgLineBytesZ - LgNumBytesFullCapSz)%Z.

  Local Definition castLineOffsetForTag (offset : Expr ty (Bit lgLineBytesZ))
    : Expr ty (Bit (LgNumBytesFullCapSz + lgNumDXlenZ)%Z) :=
    castBits (eq_sym (add_sub_cancel lgLineBytesZ LgNumBytesFullCapSz)) offset.

  Local Definition tagSlot (addr : Expr ty Addr) : Expr ty (Bit lgNumDXlenZ) :=
    TruncMsb lgNumDXlenZ LgNumBytesFullCapSz (castLineOffsetForTag (lineOffset addr)).

  Definition memRegionRead
             (addr : ty Addr)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR FullCapWithTag :=
    Let capOffset : Bit LgNumBytesFullCapSz <- TruncLsb TagAddrWidth LgNumBytesFullCapSz #addr ;
    Let isCapAligned : Bool <- isZero #capOffset ;
    Let isCap : Bool <- And [Eq #memSize $LgNumBytesFullCapSz ; #isCapAligned] ;
    Let numBytesActive : Bit (lgLineBytesZ + 1)%Z <-
                           Sll $1
                             (ZeroExtend (lgLineBytesZ + 1 - LgLgNumBytesFullCapSz)%Z #memSize) ;
    Let endOffset : Bit (lgLineBytesZ + 1)%Z <-
      Add [ ZeroExtend 1 (lineOffset #addr) ; #numBytesActive ] ;
    Let crossesLine : Bool <- FromBit Bool (TruncMsb 1 lgLineBytesZ (Sub #endOffset $1)) ;
    Let lAddr1 : Addr <- lineAddr #addr ;
    LetA rp1 : LineReadRp r.(regionLineCfg) <- memRegionLineRead r lAddr1 ;
    LetIf lineDataMerged : Array lBytes (Bit 8) <-
      If #crossesLine Then (
        Let lAddr2 : Addr <- nextLineAddr #addr ;
        LetA rp2 : LineReadRp r.(regionLineCfg) <- memRegionLineRead r lAddr2 ;
        Return (ArrayBuilder (fun (i : FinType lBytes) =>
          ITE (ReadArrayConst (add1 #addr) i)
              (ReadArrayConst (##rp2`"data") i)
              (ReadArrayConst (##rp1`"data") i)))
      ) Else (
        Return (##rp1`"data")
      ) ;
    Let rotData : Array lBytes (Bit 8) <- ArrayRotr #lineDataMerged (lineOffset #addr) ;
    Let dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
      slice #rotData (Const ty (Bit lgLineBytesZ) Zmod.zero) (Z.to_nat NumBytesFullCapSz) ;
    Let rawData : Bit FullCapSz <- ToBit #dataBytes ;
    LetA rawTag : Bool <-
      if hasTags r then (
        Return (ReadArray (##rp1`"tag") (tagSlot #addr))
      ) else (
        Return (ConstBool false)
      ) ;
    Let res : FullCapWithTag <- STRUCT {
      "tag"  ::= And [ #isCap ; #rawTag ] ;
      "cap"  ::= FromBit Cap (TruncMsb CapSz AddrSz #rawData) ;
      "addr" ::= TruncLsb CapSz AddrSz #rawData
    } ;
    Return #res.

  Definition memRegionWrite
             (addr : ty Addr)
             (stVal : ty FullCapWithTag)
             (memSize : ty (Bit LgLgNumBytesFullCapSz))
             : Action ty tR (Bit 0) :=
    if r.(isReadOnly) then (
      Retv
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
      Act (memRegionLineWrite r rq1) ;
      If #crossesLine Then (
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
        Act (memRegionLineWrite r rq2) ;
        Retv
      ) ;
      Retv
    ).

End MemRegionActions.

Arguments memRegionRead r [ty] addr memSize.
Arguments memRegionWrite r [ty] addr stVal memSize.

(* ===========================================================================
 * Composite Memory Tree & System Routing
 * =========================================================================== *)

Fixpoint specMemChildren (regions : list MemRegion) : list (Tree DomainElem) :=
  match regions with
  | [] => []
  | r :: rs => [ memRegionTree r ; Node "mem" (specMemChildren rs) ]
  end.

Definition specMemTree (regions : list MemRegion) : Tree DomainElem :=
  Node "mem" (specMemChildren regions).

Definition child0Path {A : Type} {name : string} {c0 : Tree A} {cs : list (Tree A)}
  : NodePath (Node name (c0 :: cs)) :=
  inr (inl (inl tt)).

Definition child1Path {A : Type} {name : string} {c0 c1 : Tree A} {cs : list (Tree A)}
  : NodePath (Node name (c0 :: c1 :: cs)) :=
  inr (inr (inl (inl tt))).

Arguments child0Path {A name c0 cs}.
Arguments child1Path {A name c0 c1 cs}.

Definition none_neq_some {A} {x : A} (pf : None = Some x) : False :=
  match pf in (_ = y) return match y with Some _ => False | None => True end with
  | eq_refl => I
  end.

Section NthRegionAction.
  Variable ty : Kind -> Type.

  Fixpoint nthRegionAction
             (idx : nat)
             {struct idx}
             : forall (regions : list MemRegion) (r0 : MemRegion),
               nth_error regions idx = Some r0 ->
               forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k :=
    match idx with
    | 0%nat =>
        fun regions =>
          match regions return forall r0, nth_error regions 0 = Some r0 ->
                                forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k with
          | nil => fun r0 pf => False_rect _ (none_neq_some pf)
          | cons r rs => fun r0 pf k act =>
              let eq_r0_r : r0 = r :=
                match pf in (_ = o) return match o with Some r0' => r0' = r | None => False end with
                | eq_refl => eq_refl
                end in
              liftAction child0Path
                (match eq_r0_r in (_ = y) return Action ty (memRegionTree y) k with
                 | eq_refl => act
                 end)
          end
    | S idx' =>
        fun regions =>
          match regions return forall r0, nth_error regions (S idx') = Some r0 ->
                                forall k, Action ty (memRegionTree r0) k -> Action ty (specMemTree regions) k with
          | nil => fun r0 pf => False_rect _ (none_neq_some pf)
          | cons r rs => fun r0 pf k act =>
              liftAction child1Path (@nthRegionAction idx' rs r0 pf k act)
          end
    end.

End NthRegionAction.

Arguments nthRegionAction {ty} idx regions r0 pf {k} act.

Section SpecMemRouter.
  Variable ty : Kind -> Type.

  Fixpoint specMemRead
           (regions : list MemRegion)
           (addr : ty Addr)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (specMemTree regions) FullCapWithTag :=
    match regions return Action ty (specMemTree regions) FullCapWithTag with
    | [] => Return ConstDef
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        LetIf devVal : FullCapWithTag <-
          If #isMatch Then (
            liftAction child0Path (memRegionRead r addr memSize)
          ) Else (
            Return ConstDef
          ) ;
        LetA restVal : FullCapWithTag <-
          liftAction child1Path (specMemRead rs addr memSize) ;
        Return (Or [ #devVal ; #restVal ])
    end.

  Fixpoint specMemWrite
           (regions : list MemRegion)
           (addr : ty Addr)
           (stVal : ty FullCapWithTag)
           (memSize : ty (Bit LgLgNumBytesFullCapSz))
           : Action ty (specMemTree regions) (Bit 0) :=
    match regions return Action ty (specMemTree regions) (Bit 0) with
    | [] => Retv
    | r :: rs =>
        Let isMatch : Bool <- isRegionAddr r #addr ;
        If #isMatch Then (
          liftAction child0Path (memRegionWrite r addr stVal memSize)
        ) ;
        liftAction child1Path (specMemWrite rs addr stVal memSize)
    end.

End SpecMemRouter.

Section RevBitHelper.
  Variable ty : Kind -> Type.
  Variable config : RevConfig.
  Variable regions : list MemRegion.

  Definition readRevBit (base : ty (Bit (AddrSz + 1))) : Action ty (specMemTree regions) Bool :=
    LetL lookup      : RevBitLookup               <- computeRevBitAddr config base ;
    Let  revByteAddr : Addr                       <- ##lookup`"revByteAddr" ;
    Let  sz0         : Bit LgLgNumBytesFullCapSz  <- $0 ;
    LetA revCap      : FullCapWithTag             <- specMemRead regions revByteAddr sz0 ;
    Let  revByte     : Bit 8                      <- TruncLsb (AddrSz - 8) 8 (##revCap`"addr") ;
    Let  revBit      : Bool                       <- extractRevBit lookup #revByte ;
    Return #revBit.
End RevBitHelper.

Definition memRegionIrqAction
           (r : MemRegion)
           : option (forall ty, Action ty (memRegionTree r) Bool) :=
  match r.(regionKind) as k return option (forall ty, Action ty (match k with
                                                                | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                                                | ExternalMem => externalMemRegionTree r
                                                                | CustomMem children _ _ _ => customMemRegionTree r children
                                                                end) Bool) with
  | CustomMem children _ _ (Some act) => Some act
  | _ => None
  end.

Section IrqCollector.
  Fixpoint collectIrqActions
           (regions : list MemRegion)
           : list (forall ty, Action ty (specMemTree regions) Bool) :=
    match regions return list (forall ty, Action ty (specMemTree regions) Bool) with
    | [] => []
    | r :: rs =>
        let rest := map (fun act ty => liftAction child1Path (act ty))
                        (collectIrqActions rs) in
        match memRegionIrqAction r with
        | Some act =>
            (fun ty => liftAction child0Path (act ty)) :: rest
        | None => rest
        end
    end.
End IrqCollector.

Definition memRegionTargetPortActions
           (r : MemRegion)
           : list (string * (forall ty, Action ty (memRegionTree r) (Bit 0))) :=
  match r.(regionKind) as k return list (string * (forall ty, Action ty (match k with
                                                                         | InternalMem isAccessible _ _ => internalMemRegionTree r isAccessible
                                                                         | ExternalMem => externalMemRegionTree r
                                                                         | CustomMem children _ _ _ => customMemRegionTree r children
                                                                         end) (Bit 0))) with
  | InternalMem true _ _ =>
      [ (r.(regionDom), fun ty => @internalMemRegionTargetPortRead r ty) ;
        (r.(regionDom), fun ty => @internalMemRegionTargetPortWrite r ty) ]
  | _ => []
  end.

Section TargetPortCollector.
  Fixpoint collectTargetPortActions
           (regions : list MemRegion)
           : list (string * (forall ty, Action ty (specMemTree regions) (Bit 0))) :=
    match regions return list (string * (forall ty, Action ty (specMemTree regions) (Bit 0))) with
    | [] => []
    | r :: rs =>
        let curr := map (fun '(dom, act) => (dom, fun ty => liftAction child0Path (act ty)))
                        (memRegionTargetPortActions r) in
        let rest := map (fun '(dom, act) => (dom, fun ty => liftAction child1Path (act ty)))
                        (collectTargetPortActions rs) in
        (curr ++ rest)%list
    end.
End TargetPortCollector.
