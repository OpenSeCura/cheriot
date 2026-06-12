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

From Stdlib Require Import String List ZArith Zmod Bool.
Require Import Guru.Syntax Guru.Notations Guru.Semantics Guru.Library Guru.Composition.
Require Import Cheriot.Alu Cheriot.Binary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Spec.
  Variable MemWidth: nat.
  Definition LgBytesFullCapSz := Eval compute in Z.to_nat LgNumBytesFullCapSz.
  Variable MemWidthGeLgBytesFullCapSz: MemWidth >= LgBytesFullCapSz.
  Definition MemByteSz := Nat.pow 2 MemWidth.
  Definition MemFullCapSz := Nat.pow 2 (MemWidth - LgBytesFullCapSz).
  Definition binaryLength := Eval compute in (length binary).
  Definition specInst: type (Array binaryLength (Bit 8)) := Build_SameTuple (tupleElems := binary)
                                                                (I: Is_true (length binary =? binaryLength)).
  Definition MemWidthCap : Z := Z.of_nat MemWidth - LgNumBytesFullCapSz.

  Variable tohostAddr: type Addr.

      Variable regsInit: type (Array NumRegs FullECapWithTag).
  Variable scrsInit: type Scrs.
  Variable csrsInit: type Csrs.
  Variable interruptsInit: type Interrupts.
  Variable revokerEpochInit: type Data.
  Variable revokerKickInit: type Bool.
  Variable revokerStartInit: type (Bit MemWidthCap).
  Variable revokerEndInit: type (Bit MemWidthCap).
  Variable revokeAddrInit: type (Bit MemWidthCap).

  Variable RevStart: Z.
  Variable RevByteSz: Z.
  Variable RevEachBitLgNumBytes: Z.
  Variable RevEachBitLgNumBytesInMem: (RevEachBitLgNumBytes < Z.of_nat MemWidth)%Z.
  Variable RevInMem: (RevStart + RevByteSz < Z.of_nat MemByteSz)%Z.
  Variable HeapStart: Z.
  Definition HeapEnd := (HeapStart + (RevByteSz * (Z.shiftl 1 RevEachBitLgNumBytes) * 8))%Z.
  Variable HeapInMem: (HeapEnd < Z.of_nat MemByteSz)%Z.
  Variable RevokerAddr: Z.
  Definition RevokerSize: Z := 4.
  Definition LgRevokerSzBytes: Z := Z.log2_up XlenBytes + Z.log2_up RevokerSize.

  Definition RevStartAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ RevStart.
  Definition HeapStartAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ HeapStart.
  Definition HeapEndAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ HeapEnd.

  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable mem_t: Tree Elem.
  Definition specTree : Tree Elem :=
    Node "" [
      Node "mem" [mem_t];
      Leaf "regs" (EReg {| regKind := Array NumRegs FullECapWithTag; regInit := Some regsInit |});
      Leaf "csrs" (EReg {| regKind := Csrs; regInit := Some csrsInit |});
      Leaf "scrs" (EReg {| regKind := Scrs; regInit := Some scrsInit |});
      Leaf "interrupts" (EReg {| regKind := Interrupts; regInit := Some interruptsInit |});
      Leaf "revokerEpoch" (EReg {| regKind := Data; regInit := Some revokerEpochInit |});
      Leaf "revokerKick" (EReg {| regKind := Bool; regInit := Some revokerKickInit |});
      Leaf "revokerStart" (EReg {| regKind := Bit MemWidthCap; regInit := Some revokerStartInit |});
      Leaf "revokerEnd" (EReg {| regKind := Bit MemWidthCap; regInit := Some revokerEndInit |});
      Leaf "revokeAddr" (EReg {| regKind := Bit MemWidthCap; regInit := Some revokeAddrInit |});
      Leaf "interrupts_in" (ERecv Interrupts)
    ].

  Definition SpecRevokerAccessState := STRUCT_TYPE {
                                           "revokerEpoch" :: Data;
                                           "revokerKick" :: Bool;
                                           "revokerStart" :: Bit MemWidthCap;
                                           "revokerEnd" :: Bit MemWidthCap }.

  Definition SpecProcessorState := STRUCT_TYPE {
                                       "regs" :: Array NumRegs FullECapWithTag;
                                       "csrs" :: Csrs;
                                       "scrs" :: Scrs;
                                       "interrupts" :: Interrupts;
                                       "revokerAccess" :: SpecRevokerAccessState }.
  Local Close Scope string_scope.

  Section Ty.
    Variable ty: Kind -> Type.

    Definition RevokerEpochAddr: Expr ty Addr := $(RevokerAddr + XlenBytes*0).
    Definition RevokerKickAddr: Expr ty Addr  := $(RevokerAddr + XlenBytes*1).
    Definition RevokerStartAddr: Expr ty Addr := $(RevokerAddr + XlenBytes*2).
    Definition RevokerEndAddr: Expr ty Addr   := $(RevokerAddr + XlenBytes*3).

    Definition isInHeap (addr: ty (Bit (AddrSz + 1))): Expr ty Bool :=
      And [Sge #addr (ConstBit HeapStartAddr); Slt #addr (ConstBit HeapEndAddr)].

    Definition revBitNum (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit (AddrSz + 1)) :=
      Srl (Sub #addr (ConstBit HeapStartAddr)) (ConstBit (bits.of_Z (Z.of_nat MemWidth) RevEachBitLgNumBytes)).

    Definition revBitByteAddr (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit (AddrSz + 1)) :=
      Srl (revBitNum addr) (ConstBit (bits.of_Z 2 3)).

    Definition revBitByteOffset (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit 3) :=
      TruncLsb ((AddrSz + 1) - 3) 3 (revBitNum addr).

    Definition isRevokerAddr (a: ty Addr) (sz: ty (Bit MemSz)) :=
      And [Sge #a RevokerEpochAddr; Slt #a RevokerEndAddr; Eq #sz $XlenBytes ].

    Definition getRevokerOffset (a: ty Addr): Expr ty (Bit (Z.log2_up RevokerSize)) :=
      TruncMsb (Z.log2_up RevokerSize) (Z.log2_up XlenBytes)
        (TruncLsb (AddrSz - LgRevokerSzBytes) LgRevokerSzBytes (Sub #a RevokerEpochAddr)).

    Definition readRevoker (offset: ty (Bit (Z.log2_up RevokerSize))) (revokerState: ty SpecRevokerAccessState):
      Expr ty Data :=
      (Or [ITE0 (Eq #offset $0) ##revokerState`"revokerEpoch";
           ITE0 (Eq #offset $1) (Const ty Data (bits.of_Z _ 0));
           ITE0 (Eq #offset $2) (castBits (Zplus_minus _ _)
                                   (ZeroExtendTo AddrSz ##revokerState`"revokerStart"));
           ITE0 (Eq #offset $3) (castBits (Zplus_minus _ _)
                                   (ZeroExtendTo AddrSz ##revokerState`"revokerEnd"))]).

    Definition getRevokerAddr (a: ty Addr): Expr ty (Bit MemWidthCap).
      refine
        (TruncMsb MemWidthCap LgNumBytesFullCapSz
           (castBits _ (TruncLsb (AddrSz - Z.of_nat MemWidth) (Z.of_nat MemWidth) (castBits _ #a)))).
      - abstract (unfold MemWidthCap; lia).
      - abstract (unfold AddrSz; lia).
    Defined.

    Definition writeRevoker (offset: ty (Bit (Z.log2_up RevokerSize))) (d: ty Data) (old: ty SpecRevokerAccessState)
      : Expr ty SpecRevokerAccessState :=
      STRUCT {
          "revokerEpoch" ::= ITE (Eq #offset $0) #d ##old`"revokerEpoch";
          "revokerKick" ::= Eq #offset $1;
          "revokerStart" ::= ITE (Eq #offset $2) (getRevokerAddr d) #old`"revokerStart";
          "revokerEnd" ::= ITE (Eq #offset $3) (getRevokerAddr d) #old`"revokerEnd"
        }.

  #[projections(primitive)]
  Record MemIfc {ty: Kind -> Type} := {
    mem_readBytes: ty Addr -> ty (Bit MemSz) -> Expr ty (Array (Z.to_nat DXlenBytes) (Bit 8));
    mem_readTag: forall {m}, ty (Bit m) -> Expr ty Bool;
    mem_readRevBit: ty (Bit (AddrSz + 1)) -> Expr ty Bool;
    mem_writeBytes: ty Addr -> ty (Array (Z.to_nat DXlenBytes) (Bit 8)) -> ty (Bit MemSz) -> Action ty mem_t (Bit 0);
    mem_writeTag: forall {m}, ty (Bit m) -> ty Bool -> Action ty mem_t (Bit 0)
  }.

    Definition interrupts: Action ty specTree (Bit 0) :=
      ( Get interrupts <- ".interrupts_in" in specTree;
        RegRead specInterrupts <- ".interrupts" in specTree;
        RegWrite ".interrupts" in specTree <- Or [#interrupts; #specInterrupts];
        Retv ).

    Variable memIfc: MemIfc (ty:=ty).

    Definition np_mem: NodePath specTree mem_t := ltac:(solveNodePath specTree ".mem"%string mem_t).

    Ltac specSimpl x :=
      let x' := eval cbv [decode alu encodeCap decodeCap readRevoker writeRevoker getRevokerAddr
                           revokerKickInit revokerEpochInit revokerStartInit revokerEndInit] in x in
      let x'' := eval cbn in x' in
      exact x''.
    Notation specSimpl x := ltac:(specSimpl x) (only parsing).

    Lemma size_bytes_eq : size (Array (Z.to_nat DXlenBytes) (Bit 8)) = 64%Z.
    Proof. compute. reflexivity. Qed.

    Lemma size_xlen_bytes_eq : size (Array (Z.to_nat XlenBytes) (Bit 8)) = 32%Z.
    Proof. compute. reflexivity. Qed.

    Lemma size_st_bytes_eq : DXlen = size (Array (Z.to_nat DXlenBytes) (Bit 8)).
    Proof. compute. reflexivity. Qed.

    Definition cpuAction: Action ty specTree (Bit 0) :=
      ( RegRead regs <- ".regs" in specTree;
        RegRead csrs <- ".csrs" in specTree;
        RegRead scrs <- ".scrs" in specTree;
        RegRead interrupts <- ".interrupts" in specTree;
        RegRead revokerEpoch <- ".revokerEpoch" in specTree;
        RegRead revokerKick <- ".revokerKick" in specTree;
        RegRead revokerStart <- ".revokerStart" in specTree;
        RegRead revokerEnd <- ".revokerEnd" in specTree;
        RegRead revokeAddr <- ".revokeAddr" in specTree;

        Let revoker : SpecRevokerAccessState <- STRUCT { "revokerEpoch" ::= #revokerEpoch;
                                                         "revokerKick" ::= #revokerKick;
                                                         "revokerStart" ::= #revokerStart;
                                                         "revokerEnd" ::= #revokerEnd };

        Let insts : Array binaryLength (Bit 8) <- Const ty _ specInst;
        Let pcc : FullECapWithTag <- #regs $[ 0 ];
        Let pcVal : Addr <- #pcc`"addr";
        Let BoundsException : Bool <- And [Slt (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"top"); Sge (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"base")];
        Let pcAluOut: PcAluOut <- STRUCT { "pcVal" ::= #pcVal;
                                           "BoundsException" ::= #BoundsException };
        Let inst: Inst <- ToBit (slice #insts #pcVal (Z.to_nat InstSz/8));
        LetL decodeOut: DecodeOut <- decode inst;

        Let aluIn: AluIn <- STRUCT { "pcAluOut" ::= #pcAluOut;
                                      "decodeOut" ::= #decodeOut;
                                      "regs" ::= #regs;
                                      "waits" ::= Const ty (Array NumRegs Bool) (Default _);
                                      "csrs" ::= #csrs;
                                      "scrs" ::= #scrs;
                                      "interrupts" ::= #interrupts };
        Let pcTag <- #pcc`"tag";
        Let pcCap <- #pcc`"ecap";
        LetL aluOut: AluOut <- alu pcTag pcCap aluIn;
        Let memAddr: Addr <- ##aluOut`"multicycleOp"`"memAddr";
        Let memSz: Bit MemSz <- Sll $1 (##aluOut`"multicycleOp"`"memSz");
        Let isCap: Bool <- isZero #memSz;
        Let ldUn: Bool <- ##aluOut`"multicycleOp"`"LoadUnsigned";

        Let isRevoker: Bool <- isRevokerAddr memAddr memSz;
        Let revokerOffset: Bit (Z.log2_up RevokerSize) <- getRevokerOffset memAddr;
        Let revokerData: Data <- readRevoker revokerOffset revoker;

        Let bytes: Array (Z.to_nat DXlenBytes) (Bit 8) <- memIfc.(mem_readBytes) memAddr memSz;
        Let fullCap: FullCap <- FromBit FullCap (@castBits ty (size (Array (Z.to_nat DXlenBytes) (Bit 8))) 64 size_bytes_eq (ToBit #bytes));
        Let ldCap: Cap <- #fullCap`"cap";
        Let ldVal: Array (Z.to_nat XlenBytes) (Bit 8) <- FromBit (Array (Z.to_nat XlenBytes) (Bit 8)) (@castBits ty 32 (size (Array (Z.to_nat XlenBytes) (Bit 8))) (eq_sym size_xlen_bytes_eq) (ITE #isRevoker #revokerData #fullCap`"addr"));
        Let ldValFinal <- ToBit (ITE #ldUn (ArrayZeroExtend #memSz #ldVal) (ArraySignExtend #memSz #ldVal));
        LetL ldECap: ECap <- decodeCap ldCap ldValFinal;
        Let ldECapFinal: ECap <- ITE #isCap #ldECap ConstDef;
        Let memTagAddr: Bit (AddrSz - MemSz) <- TruncMsb _ MemSz #memAddr;

        Let ldTag: Bool <- memIfc.(mem_readTag) memTagAddr;

        Let ldBase: Bit (AddrSz + 1) <- #ldECap`"base";
        Let revBit: Bool <- memIfc.(mem_readRevBit) ldBase;

        Let ldTagFinal: Bool <- ITE #isCap (And [#ldTag; Not #revBit]) ConstDef;
        Let ldFinal: FullECapWithTag <- STRUCT { "tag" ::= #ldTagFinal;
                                                  "ecap" ::= #ldECapFinal;
                                                  "addr" ::= #ldValFinal };

        Let ldRegIdx <- ##aluOut`"multicycleOp"`"loadRegIdx";
        Let aluOutRegs: Array NumRegs FullECapWithTag <- eq_rect _ (fun k => Expr ty k) (##aluOut`"regs") _ eq_refl;
        Let newRegs: Array NumRegs FullECapWithTag <- #aluOutRegs
                                                          @[ #ldRegIdx <- ITE (##aluOut`"multicycleOp"`"Load")
                                                                            #ldFinal
                                                                            (#aluOutRegs@[#ldRegIdx])];

        Let stECap: ECap <- ##aluOut`"multicycleOp"`"storeVal"`"ecap";

        Let stVal <- ##aluOut`"multicycleOp"`"storeVal"`"addr";
        LetL stCap: Cap <- encodeCap stECap;
        Let stBits: Bit DXlen <- {< ToBit #stCap, #stVal >};
        Let stBytes: Array (Z.to_nat DXlenBytes) (Bit 8) <- FromBit (Array (Z.to_nat DXlenBytes) (Bit 8)) (@castBits ty DXlen (size (Array (Z.to_nat DXlenBytes) (Bit 8))) size_st_bytes_eq #stBits);
        Let Store: Bool <- ##aluOut`"multicycleOp"`"Store";
        Let StoreMem: Bool <- And [#Store; Not #isRevoker];
        Let newRevoker <- ITE (And [#Store; #isRevoker])
                                  (writeRevoker revokerOffset stVal revoker)
                                  #revoker;

        Let stTag: Bool <- ##aluOut`"multicycleOp"`"storeVal"`"tag";
        LetIf _ <- If #StoreMem
        Then (
          Act liftAction np_mem (memIfc.(mem_writeBytes) memAddr stBytes memSz);
          If #isCap
            Then (Act liftAction np_mem (memIfc.(mem_writeTag) memTagAddr stTag); Retv)
            Else Retv;
          Retv
        ) Else (Retv);

        LetIf _ <- If And [#StoreMem; Eq #memAddr (Const ty _ tohostAddr)]
        Then (
          LetIf _ <- If (Eq #stVal $1)
          Then (
            System [DispString ty "SUCCESS"%string] Retv )
          Else (
            System [DispString ty "FAILURE"%string] Retv );
          Retv )
        Else (Retv);

        RegWrite ".regs" in specTree <- #newRegs;
        RegWrite ".csrs" in specTree <- #aluOut`"csrs";
        RegWrite ".scrs" in specTree <- ##aluOut`"scrs";
        RegWrite ".interrupts" in specTree <- ##aluOut`"interrupts";
        RegWrite ".revokerEpoch" in specTree <- ##newRevoker`"revokerEpoch";
        RegWrite ".revokerKick" in specTree <- ##newRevoker`"revokerKick";
        RegWrite ".revokerStart" in specTree <- ##newRevoker`"revokerStart";
        RegWrite ".revokerEnd" in specTree <- ##newRevoker`"revokerEnd";
        Retv ).

    Lemma revoker_addr_size_eq : (0 + MemSz + MemWidthCap + (32 - (0 + MemSz + MemWidthCap)) = 32)%Z.
    Proof.
      lia.
    Qed.

    Definition revoker: Action ty specTree (Bit 0) :=
      ( RegRead revokerEpoch <- ".revokerEpoch" in specTree;
        RegRead revokerKick <- ".revokerKick" in specTree;
        RegRead revokerStart <- ".revokerStart" in specTree;
        RegRead revokerEnd <- ".revokerEnd" in specTree;
        RegRead revokeAddr <- ".revokeAddr" in specTree;

        Let ldTag: Bool <- memIfc.(mem_readTag) revokeAddr;
        Let rvkAddr : Addr <- @castBits ty _ 32 revoker_addr_size_eq (ZeroExtendTo 32 {< #revokeAddr, Const ty (Bit MemSz) (bits.of_Z _ 0) >});
        Let rvkSz : Bit MemSz <- Const ty (Bit MemSz) (bits.of_Z _ 0);
        Let bytes: Array (Z.to_nat DXlenBytes) (Bit 8) <- memIfc.(mem_readBytes) rvkAddr rvkSz;
        Let fullCap: FullCap <- FromBit FullCap (@castBits ty (size (Array (Z.to_nat DXlenBytes) (Bit 8))) 64 size_bytes_eq (ToBit #bytes));
        Let ldCap: Cap <- #fullCap`"cap";
        Let ldVal: Addr <- #fullCap`"addr";
        LetL ldECap: ECap <- decodeCap ldCap ldVal;
        Let ldBase <- #ldECap`"base";
        Let revBit: Bool <- memIfc.(mem_readRevBit) ldBase;
        Let ldTagFinal <- And [#ldTag; Not #revBit];
        Act liftAction np_mem (memIfc.(mem_writeTag) revokeAddr ldTagFinal);

        Let workStart <- And [Eq #revokeAddr #revokerEnd; #revokerKick];
        Let doWork <- Slt #revokeAddr #revokerEnd;
        Let incRevokeAddr <- Add [#revokeAddr; $1];
        Let newRevokeAddr <- ITE #workStart
                                #revokerStart
                                (ITE #doWork
                                   #incRevokeAddr
                                   #revokeAddr);
        Let newEpoch <- Add [#revokerEpoch; ITE (Or [Eq #incRevokeAddr #revokerEnd; #workStart]) $1 $0];

        RegWrite ".revokerEpoch" in specTree <- #newEpoch;
        RegWrite ".revokerKick" in specTree <- Const ty Bool false;
        RegWrite ".revokeAddr" in specTree <- #newRevokeAddr;
        Retv ).
  End Ty.

  Definition spec (memIfc : forall ty, MemIfc (ty:=ty)) : Mod specTree :=
    fun ty => [cpuAction (memIfc ty); interrupts ty; revoker (memIfc ty)].

  Definition SpecInvariant (s: TreeState ElemState specTree) : Prop.
  Admitted.

  Theorem specInvariantPreserved: forall (memIfc : MemIfc (ty:=type)) old new,
      SpecInvariant old ->
      SemAction (cpuAction memIfc) old new Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Theorem interruptsInvariantPreserved: forall old new,
      SpecInvariant old ->
      SemAction (interrupts type) old new Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Theorem revokerInvariantPreserved: forall (memIfc : MemIfc (ty:=type)) old new,
      SpecInvariant old ->
      SemAction (revoker memIfc) old new Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Ltac simplifyAluExpr v :=
    let x := eval cbn delta -[evalFromBitStruct] beta iota in v in
      let x := eval cbv delta [mapSameTuple updSameTuple updSameTupleNat Bool.transparent_Is_true]
                 beta iota in x in
        let x := eval cbn delta -[evalFromBitStruct] beta iota in x in
          x.

  (*
  Definition evalCpuActionExpr (state: Expr type AllSpecState): type AllSpecState :=
    ltac:(let x := simplifyAluExpr (evalLetExpr (cpuActionExpr state)) in exact x).
  *)
End Spec.

Section PartialInitSpec.
  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable MemWidth: nat.
  Variable MemWidthGeLgBytesFullCapSz: MemWidth >= LgBytesFullCapSz.
  Variable regsInit: type (Array NumRegs FullECapWithTag).

  Variable regsInitPc:
    readNatToFinType (Default FullECapWithTag) (readSameTuple regsInit) 0 = Default FullECapWithTag.

  Definition scrsInit: type Scrs := STRUCT_CONST {
                                        "mtcc" ::= ExecRoot;
                                        "mtdc" ::= MemRoot;
                                        "mscratchc" ::= SealRoot;
                                        "mepcc" ::= ExecRoot }.

  Variable mem_t: Tree Elem.
  Definition partialInitSpec (memIfc : forall ty, MemIfc mem_t (ty:=ty)) := spec (mem_t:=mem_t) MemWidthGeLgBytesFullCapSz (Default _) regsInit scrsInit
                                                                              (Default _) (Default _) (Default _) (Default _) (Default _) (Default _) (Default _) 0%Z memIfc.
End PartialInitSpec.
