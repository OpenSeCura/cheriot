From Stdlib Require Import String List ZArith Zmod Bool.
Require Import Guru.Library Guru.Syntax Guru.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section BankedMem.
  Local Open Scope Z.
  (* Num8Banks and NumBanks used in Array and repeat; EachSize used in Array; rest should be Z *)
  Variable LgNum8Banks: Z. (* Lg of Number of 64-bit sized banks *)
  Variable LgEachSize: Z. (* Lg of Size of each bank *)
  Variable LgEachSizeGe0: LgEachSize >= 0.
  Variable port: FinType 2%nat.

  Local Definition LgNumBanks := 3 + LgNum8Banks. (* Lg of Number of 8-bit sized banks *)
  Local Definition Num8Banks := Z.to_nat (Z.shiftl 1 LgNum8Banks).
  Local Definition NumBanks := Z.to_nat (Z.shiftl 1 LgNumBanks).
  Local Definition EachSize := Z.to_nat (Z.shiftl 1 LgEachSize).
  Local Definition MemAddrSz := LgNumBanks + LgEachSize.

  Definition bankedMemIfc : Tree ModElem :=
    Node "" [
      Node "memBanks" (repeat (Leaf "memBank" (EMem (@Build_Mem EachSize (Bit 8) 2%nat None))) NumBanks);
      Node "tagBanks" (repeat (Leaf "tagBank" (EMem (@Build_Mem EachSize Bool 2%nat None))) Num8Banks);
      Leaf "initTagReg" (EReg (Build_Reg (Bit (LgEachSize + 1)) (Some (Default _))))
    ].

  Definition cl := bankedMemIfc.

  Definition leaf_list_path_mem (n: nat) (p: FinType n) :=
    leaf_list_path_repeat (Leaf "memBank" (EMem (@Build_Mem EachSize (Bit 8) 2%nat None))) tt p.

  Definition leaf_list_path_tag (n: nat) (p: FinType n) :=
    leaf_list_path_repeat (Leaf "tagBank" (EMem (@Build_Mem EachSize Bool 2%nat None))) tt p.

  Lemma leaf_list_path_mem_is_mem n (i: FinType n) :
    Is_true (isMemElem (@getLeaf ModElem (Node "memBanks" (repeat (Leaf "memBank" (EMem (@Build_Mem EachSize (Bit 8) 2%nat None))) n)) (leaf_list_path_mem i))).
  Proof.
    unfold leaf_list_path_mem.
    rewrite getLeaf_repeat.
    simpl.
    exact I.
  Qed.

  Lemma leaf_list_path_tag_is_mem n (i: FinType n) :
    Is_true (isMemElem (@getLeaf ModElem (Node "tagBanks" (repeat (Leaf "tagBank" (EMem (@Build_Mem EachSize Bool 2%nat None))) n)) (leaf_list_path_tag i))).
  Proof.
    unfold leaf_list_path_tag.
    rewrite getLeaf_repeat.
    simpl.
    exact I.
  Qed.

  Definition initTagRegPath : RegPath bankedMemIfc := getRegPathTree cl ".initTagReg".

  Definition memBankPath (i: FinType NumBanks) : MemPath bankedMemIfc.
  Proof.
    refine (Build_MemPath bankedMemIfc (inl (leaf_list_path_mem i)) _).
    exact (leaf_list_path_mem_is_mem i).
  Defined.

  Definition tagBankPath (i: FinType Num8Banks) : MemPath bankedMemIfc.
  Proof.
    refine (Build_MemPath bankedMemIfc (inr (inl (leaf_list_path_tag i))) _).
    exact (leaf_list_path_tag_is_mem i).
  Defined.

  Lemma memBankEq n (i: FinType n) :
    @getMemFromPathUnsafe (Node "memBanks" (repeat (Leaf "memBank" (EMem (@Build_Mem EachSize (Bit 8) 2%nat None))) n)) (leaf_list_path_mem i) =
    {| memSize := EachSize; memKind := Bit 8; memPort := 2; memInit := None |}.
  Proof.
    unfold leaf_list_path_mem, getMemFromPathUnsafe.
    rewrite getLeaf_repeat.
    reflexivity.
  Qed.

  Lemma tagBankEq n (i: FinType n) :
    @getMemFromPathUnsafe (Node "tagBanks" (repeat (Leaf "tagBank" (EMem (@Build_Mem EachSize Bool 2%nat None))) n)) (leaf_list_path_tag i) =
    {| memSize := EachSize; memKind := Bool; memPort := 2; memInit := None |}.
  Proof.
    unfold leaf_list_path_tag, getMemFromPathUnsafe.
    rewrite getLeaf_repeat.
    reflexivity.
  Qed.

  Definition memPortCast (i: FinType NumBanks) (p: FinType 2%nat) : FinType (memPort (getMemFromPath (memBankPath i))) :=
    match eq_sym (f_equal memPort (memBankEq i)) in _ = Y return FinType Y with
    | eq_refl => p
    end.

  Definition tagPortCast (i: FinType Num8Banks) (p: FinType 2%nat) : FinType (memPort (getMemFromPath (tagBankPath i))) :=
    match eq_sym (f_equal memPort (tagBankEq i)) in _ = Y return FinType Y with
    | eq_refl => p
    end.

  Definition memSizeCast (i: FinType NumBanks) {ty} (e: Expr ty (Bit (Z.log2_up (Z.of_nat EachSize)))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (memBankPath i)))))) :=
    match eq_sym (f_equal memSize (memBankEq i)) in _ = Y return Expr ty (Bit (Z.log2_up (Z.of_nat Y))) with
    | eq_refl => e
    end.

  Definition tagSizeCast (i: FinType Num8Banks) {ty} (e: Expr ty (Bit (Z.log2_up (Z.of_nat EachSize)))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (tagBankPath i)))))) :=
    match eq_sym (f_equal memSize (tagBankEq i)) in _ = Y return Expr ty (Bit (Z.log2_up (Z.of_nat Y))) with
    | eq_refl => e
    end.

  Definition memKindCast (i: FinType NumBanks) {ty} (e: Expr ty (Bit 8)) :
    Expr ty (memKind (getMemFromPath (memBankPath i))) :=
    match eq_sym (f_equal memKind (memBankEq i)) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Definition memKindCastInv (i: FinType NumBanks) {ty} (e: Expr ty (memKind (getMemFromPath (memBankPath i)))) :
    Expr ty (Bit 8) :=
    match f_equal memKind (memBankEq i) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Definition tagKindCast (i: FinType Num8Banks) {ty} (e: Expr ty Bool) :
    Expr ty (memKind (getMemFromPath (tagBankPath i))) :=
    match eq_sym (f_equal memKind (tagBankEq i)) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Definition tagKindCastInv (i: FinType Num8Banks) {ty} (e: Expr ty (memKind (getMemFromPath (tagBankPath i)))) :
    Expr ty Bool :=
    match f_equal memKind (tagBankEq i) in _ = Y return Expr ty Y with
    | eq_refl => e
    end.

  Local Lemma LgEachSizeRoundTrip: LgEachSize = Z.log2_up (Z.of_nat EachSize).
  Proof.
    unfold EachSize.
    rewrite Z2Nat.id; rewrite Z.shiftl_1_l.
    - rewrite Z.log2_up_pow2 by Lia.lia.
      auto.
    - rewrite <- Z.pow_nonneg by Lia.lia.
      Lia.lia.
  Qed.

  Section Ty.
    Variable ty: Kind -> Type.
    Variable addr: Expr ty (Bit MemAddrSz).
    Variable memSz: Expr ty (Bit LgNumBanks).
    Variable writeVals: Expr ty (Array NumBanks (Bit 8)).
    Variable isCap: Expr ty Bool.
    Variable tagVal: Expr ty Bool.

    Local Open Scope guru.

    Local Definition shamt := TruncLsb LgEachSize LgNumBanks addr.
    Local Definition lineIdx := TruncMsb LgEachSize LgNumBanks addr.

    Local Definition add1: Expr ty (Array NumBanks Bool) :=
      FromBit (Array NumBanks Bool) (Not (Sll (ConstBit (InvDefault _)) shamt)).

    Local Definition castLineIdx (memIdx: FinType NumBanks):
      Expr ty (Bit (Z.log2_up (Z.of_nat EachSize))) :=
      (Add [castBits LgEachSizeRoundTrip lineIdx;
            ITE0 (ReadArrayConst add1 memIdx)
              (ConstT (Bit (Z.log2_up (Z.of_nat EachSize))) (Zmod.of_Z _ 1))]).

    Local Definition isWrites: Expr ty (Array NumBanks Bool) :=
      FromBit (Array NumBanks Bool)
        (rotateLeft (Not (Sll (ConstBit (InvDefault _)) memSz)) shamt).

    Local Definition rotWriteVals: Expr ty (Array NumBanks (Bit 8)) :=
      ArrayRotl 8 writeVals shamt.

    Local Definition doLoadRpNoRot : Action ty cl (Array NumBanks (Bit 8)) :=
      fold_right (fun memIdx acc =>
                    ReadRpMem "readMemRp" (memBankPath memIdx) (memPortCast memIdx port)
                      (fun val =>
                         (LetA rest: Array NumBanks (Bit 8) <- acc;
                          Return (UpdateArrayConst #rest memIdx (memKindCastInv #val)))))
        (Return ConstDef) (genFinType NumBanks).

    Local Definition shamtTag := TruncMsb LgNum8Banks 3 shamt.

    Local Definition castLineIdxTag (tagIdx: FinType Num8Banks):
      Expr ty (Bit (Z.log2_up (Z.of_nat EachSize))) :=
      castBits LgEachSizeRoundTrip lineIdx.

    Local Definition tagBankCap: Expr ty (Array Num8Banks Bool) :=
      FromBit (Array Num8Banks Bool)
        (Sll (ITE0 isCap (ConstT (Bit (NatZ_mul Num8Banks 1)) Zmod.one)) shamtTag).

    Local Definition tagBank: Expr ty (Array Num8Banks Bool) :=
      FromBit (Array Num8Banks Bool)
        (Sll (ConstT (Bit (NatZ_mul Num8Banks 1)) Zmod.one) shamtTag).

    Definition doLoadRq : Action ty cl (Bit 0) :=
      fold_right (fun memIdx acc =>
                    ReadRqMem (memBankPath memIdx) (memSizeCast memIdx (castLineIdx memIdx)) (memPortCast memIdx port) acc)
        (Return ConstDef) (genFinType NumBanks).

    Definition doWrite : Action ty cl (Bit 0) :=
      fold_right (fun memIdx acc =>
                    If (ReadArrayConst isWrites memIdx) Then (
                        WriteMem (memBankPath memIdx) (memSizeCast memIdx (castLineIdx memIdx))
                          (memKindCast memIdx (ReadArrayConst rotWriteVals memIdx))
                          (Return (ConstDefK (Bit 0))));
                  acc)
        (Return ConstDef) (genFinType NumBanks).

    Definition doLoadRp : Action ty cl (Array NumBanks (Bit 8)) :=
      (LetA noRotLoadRp : Array NumBanks (Bit 8) <- doLoadRpNoRot;
       Return (ArrayRotr 8 #noRotLoadRp shamt)).

    Definition doLoadRqTag : Action ty cl (Bit 0) :=
      fold_right (fun tagIdx acc =>
                    ReadRqMem (tagBankPath tagIdx) (tagSizeCast tagIdx (castLineIdxTag tagIdx)) (tagPortCast tagIdx port) acc)
        (Return ConstDef) (genFinType Num8Banks).

    Definition doWriteTag : Action ty cl (Bit 0) :=
      fold_right (fun tagIdx acc =>
                    (If (ReadArrayConst tagBankCap tagIdx) Then (
                         WriteMem (tagBankPath tagIdx) (tagSizeCast tagIdx (castLineIdxTag tagIdx))
                           (tagKindCast tagIdx tagVal)
                           (Return (ConstDefK (Bit 0))));
                     acc))
        (Return ConstDef) (genFinType Num8Banks).

    Definition doLoadRpTag : Action ty cl Bool :=
      fold_right
        (fun tagIdx acc =>
           ReadRpMem "readTagRp" (tagBankPath tagIdx) (tagPortCast tagIdx port)
             (fun val =>
                (LetA rest : Bool <- acc;
                 Return
                   (Or [And [ReadArrayConst tagBank tagIdx; tagKindCastInv #val]; #rest]))))
        (Return ConstDef) (genFinType Num8Banks).

    Definition initTags : Action ty cl (Bit 0) :=
      (ReadReg "initTagRegVal" initTagRegPath
         (fun initTagRegVal =>
            (Let isDone : Bool <- FromBit Bool (TruncMsb 1 LgEachSize #initTagRegVal);
             Let lineIdx : Bit LgEachSize <- TruncLsb 1 LgEachSize #initTagRegVal;
             LetIf dummy <- If (Not #isDone) Then (
                 fold_right (fun tagIdx acc =>
                               WriteMem (tagBankPath tagIdx)
                                 (tagSizeCast tagIdx (castBits LgEachSizeRoundTrip #lineIdx))
                                 (tagKindCast tagIdx ConstDef) acc)
                   (WriteReg initTagRegPath
                      (Add [#initTagRegVal; $1]) (Return ConstDef))
                   (genFinType Num8Banks));
             Return #dummy))).
  End Ty.
End BankedMem.
