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

#[projections(primitive)]
Record MemIfc {mem_t: Tree Elem} {ty: Kind -> Type} := {
  mem_readBits: ty Addr -> Action ty mem_t (Bit DXlen);
  mem_readTag: ty (Bit (AddrSz - MemSz)) -> Action ty mem_t Bool;
  mem_readRevBit: ty (Bit (AddrSz + 1)) -> Action ty mem_t Bool;
  mem_readInst: ty Addr -> Action ty mem_t Inst;
  mem_writeBits: ty Addr -> ty (Bit DXlen) -> ty (Bit MemSzSz) -> Action ty mem_t (Bit 0);
  mem_writeTag: ty (Bit (AddrSz - MemSz)) -> ty Bool -> Action ty mem_t (Bit 0)
}.

Section Spec.
  Variable MemWidth: nat.
  Variable MemWidthGeLgBytesFullCapSz: MemWidth >= Z.to_nat LgNumBytesFullCapSz.

  Variable tohostAddr: type Addr.

  Variable regsInit: type (Array NumRegs FullECapWithTag).
  Variable scrsInit: type Scrs.
  Variable csrsInit: type Csrs.
  Variable interruptsInit: type Interrupts.

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
      Leaf "interrupts_in" (ERecv Interrupts)
    ].

  Definition np_mem: NodePath specTree mem_t := ltac:(solveNodePath specTree ".mem"%string mem_t).

  Local Close Scope string_scope.

  Section Ty.
    Variable ty: Kind -> Type.

    Definition updateArrayBySz (m: Z)
      (shamt: Expr ty (Bit m))
      (k: Kind)
      (n: nat)
      (oldVal newVal: Expr ty (Array n k))
      : Expr ty (Array n k) :=
      ArrayBuilder (fun i => ITE (ReadArrayConst (Not (invMask n shamt)) i)
                               (ReadArrayConst newVal i)
                               (ReadArrayConst oldVal i)).

    Definition updateBitsByChunkSz (n: nat) (sz: Z) (m: Z)
      (shamt: Expr ty (Bit m))
      (oldVal newVal: Expr ty (Bit (NatZ_mul n sz)))
      : Expr ty (Bit (NatZ_mul n sz)) :=
      ToBit (updateArrayBySz shamt
               (FromBit (Array n (Bit sz)) oldVal)
               (FromBit (Array n (Bit sz)) newVal)).

    Definition updateWordByByteSz := updateBitsByChunkSz (n := Z.to_nat XlenBytes) (sz := 8).

    Variable memIfc: @MemIfc mem_t ty.

    Definition memLoad (memAddr: ty Addr) (memSz: ty (Bit MemSzSz)) (ldUn: ty Bool)
      : Action ty mem_t FullECapWithTag :=
      ( Let isCap : Bool <- isAllOnes #memSz;
        Let memSzBytes : Bit MemSz <- Sll $1 #memSz;
        LetA readBits: Bit DXlen <- memIfc.(mem_readBits) memAddr;
        Let readBytes: Array (Z.to_nat DXlenBytes) (Bit 8) <- FromBit _ #readBits;
        Let readBitsFixed <- ToBit (ITE #ldUn (ArrayZeroExtend #memSzBytes #readBytes)
                                      (ArraySignExtend #memSzBytes #readBytes));
        Let fullCap: FullCap <- FromBit FullCap #readBitsFixed;
        Let ldCap: Cap <- #fullCap`"cap";
        Let ldVal: Addr <- #fullCap`"addr";
        LetL ldECap: ECap <- decodeCap ldCap ldVal;
        Let ldECapFinal: ECap <- ITE #isCap #ldECap ConstDef;
        Let memTagAddr: Bit (AddrSz - MemSz) <- TruncMsb _ MemSz #memAddr;

        LetA ldTag: Bool <- memIfc.(mem_readTag) memTagAddr;

        Let ldBase: Bit (AddrSz + 1) <- #ldECap`"base";
        LetA revBit: Bool <- memIfc.(mem_readRevBit) ldBase;

        Let ldTagFinal: Bool <- ITE #isCap (And [#ldTag; Not #revBit]) ConstDef;
        Return ((STRUCT { "tag" ::= #ldTagFinal;
                          "ecap" ::= #ldECapFinal;
                          "addr" ::= #ldVal }) : Expr ty FullECapWithTag) ).

    Definition memStore (memAddr: ty Addr) (memSz: ty (Bit MemSzSz))
                        (stTag: ty Bool) (stECap: ty ECap) (stVal: ty Addr)
                        (Store: ty Bool)
      : Action ty mem_t (Bit 0) :=
      ( Let isCap : Bool <- isAllOnes #memSz;
        LetL stCap: Cap <- encodeCap stECap;
        Let stBits: Bit DXlen <- {< ToBit #stCap, #stVal >};
        Let memTagAddr: Bit (AddrSz - MemSz) <- TruncMsb _ MemSz #memAddr;
        
        If #Store
        Then (
          Act memIfc.(mem_writeBits) memAddr stBits memSz;
          If #isCap
          Then (Act memIfc.(mem_writeTag) memTagAddr stTag; Retv);
          If (Eq #memAddr (Const ty _ tohostAddr))
          Then (
            If (Eq #stVal $1)
            Then (
              System [DispString ty "SUCCESS"%string] Retv )
            Else (
              System [DispString ty "FAILURE"%string] Retv );
            Retv );
          Retv );
        Retv).

    Definition cpuAction: Action ty specTree (Bit 0) :=
      ( RegRead regs <- ".regs" in specTree;
        RegRead csrs <- ".csrs" in specTree;
        RegRead scrs <- ".scrs" in specTree;
        RegRead interrupts <- ".interrupts" in specTree;

        Let pcc : FullECapWithTag <- #regs $[ 0 ];
        Let pcVal : Addr <- #pcc`"addr";
        Let BoundsException : Bool <- And [ Sge (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"base");
                                            Slt (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"top")];
        Let pcAluOut: PcAluOut <- STRUCT { "pcVal" ::= #pcVal;
                                           "BoundsException" ::= #BoundsException };
        LetA inst: Inst <- liftAction np_mem (memIfc.(mem_readInst) pcVal);
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
        Let memSz: Bit MemSzSz <- ##aluOut`"multicycleOp"`"memSz";
        Let ldUn: Bool <- ##aluOut`"multicycleOp"`"LoadUnsigned";
        Let memTagAddr: Bit (AddrSz - MemSz) <- TruncMsb _ MemSz #memAddr;

        LetA ldFinal: FullECapWithTag <- liftAction np_mem (memLoad memAddr memSz ldUn);

        Let ldRegIdx <- ##aluOut`"multicycleOp"`"loadRegIdx";
        Let aluOutRegs: Array NumRegs FullECapWithTag <- ##aluOut`"regs";
        Let newRegs: Array NumRegs FullECapWithTag <- #aluOutRegs
                                                          @[ #ldRegIdx <- ITE (##aluOut`"multicycleOp"`"Load")
                                                                            #ldFinal
                                                                            (#aluOutRegs@[#ldRegIdx])];
        Let stECap: ECap <- ##aluOut`"multicycleOp"`"storeVal"`"ecap";

        Let stVal <- ##aluOut`"multicycleOp"`"storeVal"`"addr";
        Let Store: Bool <- ##aluOut`"multicycleOp"`"Store";
        Let stTag: Bool <- ##aluOut`"multicycleOp"`"storeVal"`"tag";

        Act liftAction np_mem (memStore memAddr memSz stTag stECap stVal Store);

        RegWrite ".regs" in specTree <- #newRegs;
        RegWrite ".csrs" in specTree <- #aluOut`"csrs";
        RegWrite ".scrs" in specTree <- ##aluOut`"scrs";
        RegWrite ".interrupts" in specTree <- ##aluOut`"interrupts";
        Retv ).

      Definition interrupts: Action ty specTree (Bit 0) :=
      ( Get interrupts <- ".interrupts_in" in specTree;
        RegRead currInterrupts <- ".interrupts" in specTree;
        RegWrite ".interrupts" in specTree <- Or [#interrupts; #currInterrupts];
        Retv ).
  End Ty.

  Definition spec (memIfc : forall ty, @MemIfc mem_t ty) : Mod specTree :=
    fun ty => [cpuAction (memIfc ty); interrupts ty].

  Definition SpecInvariant (s: TreeState ElemState specTree) : Prop.
  Admitted.

  Theorem specInvariantPreserved: forall (memIfc : @MemIfc mem_t type) old new,
      SpecInvariant old ->
      SemAction (cpuAction memIfc) old new Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Theorem interruptsInvariantPreserved: forall old new,
      SpecInvariant old ->
      SemAction (interrupts type) old new Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Ltac simplifyAluExpr v :=
    let x := eval cbn delta -[evalFromBitStruct] beta iota in v in
      let x := eval cbv delta [mapSameTuple updSameTuple updSameTupleNat Bool.transparent_Is_true]
                 beta iota in x in
        let x := eval cbn delta -[evalFromBitStruct] beta iota in x in
          x.
End Spec.

Section PartialInitSpec.
  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable MemWidth: nat.
  Variable MemWidthGeLgBytesFullCapSz: MemWidth >= Z.to_nat LgNumBytesFullCapSz.
  Variable regsInit: type (Array NumRegs FullECapWithTag).

  Variable regsInitPc:
    readNatToFinType (Default FullECapWithTag) (readSameTuple regsInit) 0 = Default FullECapWithTag.

  Definition scrsInit: type Scrs := STRUCT_CONST {
                                        "mtcc" ::= ExecRoot;
                                        "mtdc" ::= MemRoot;
                                        "mscratchc" ::= SealRoot;
                                        "mepcc" ::= ExecRoot }.

  Variable mem_t: Tree Elem.
  Definition partialInitSpec (memIfc : forall ty, @MemIfc mem_t ty) :=
    spec (mem_t:=mem_t) (Default _) regsInit scrsInit
         (Default _) (Default _) memIfc.
End PartialInitSpec.

Section Uncore.
  Variable RevokerStartAddrAligned: Z.
  Definition RevokerNumRegs : Z := 4.
  Definition RevokerSizeBytes : Z := XlenBytes * RevokerNumRegs.
  Definition RevokerAlignBits : Z := Z.log2_up RevokerSizeBytes.

  Variable revokerEpochInit: type Data.
  Variable revokerKickInit: type Bool.
  Variable revokerStartInit: type (Bit (AddrSz - LgNumBytesFullCapSz)).
  Variable revokerEndInit: type (Bit (AddrSz - LgNumBytesFullCapSz)).
  Variable revokeAddrInit: type (Bit (AddrSz - LgNumBytesFullCapSz)).

  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable mem_t: Tree Elem.

  Definition uncoreTree : Tree Elem :=
    Node "" [
      Node "mem" [mem_t];
      Node "revoker" [
        Leaf "revokerEpoch" (EReg {| regKind := Data; regInit := Some revokerEpochInit |});
        Leaf "revokerKick" (EReg {| regKind := Bool; regInit := Some revokerKickInit |});
        Leaf "revokerStart" (EReg {| regKind := Bit (AddrSz - LgNumBytesFullCapSz); regInit := Some revokerStartInit |});
        Leaf "revokerEnd" (EReg {| regKind := Bit (AddrSz - LgNumBytesFullCapSz); regInit := Some revokerEndInit |});
        Leaf "revokeAddr" (EReg {| regKind := Bit (AddrSz - LgNumBytesFullCapSz); regInit := Some revokeAddrInit |})
      ]
    ].

  Definition uncore_np_mem: NodePath uncoreTree mem_t := ltac:(solveNodePath uncoreTree ".mem"%string mem_t).

  Definition RevokerStartAddr : Z :=
    Z.shiftl RevokerStartAddrAligned RevokerAlignBits.

  Definition RevokerEndAddr : Z :=
    Z.lor RevokerStartAddr (RevokerSizeBytes-1).

  Section Ty.
    Variable ty: Kind -> Type.
    Variable rawMemIfc: @MemIfc mem_t ty.

    Definition isRevokerAddr (a: Expr ty Addr) :=
      And [Sge a $RevokerStartAddr; Sle a $RevokerEndAddr].

    Definition getRevokerOffset (a: ty Addr): Expr ty (Bit 2) :=
      TruncMsb (Z.log2_up RevokerNumRegs) (Z.log2_up XlenBytes)
        (TruncLsb (AddrSz - RevokerAlignBits) RevokerAlignBits #a).

    Definition uncoreMemIfc : @MemIfc uncoreTree ty := {|
      mem_readBits := fun addr =>
        ( Let isRevoker: Bool <- isRevokerAddr #addr;
          Let offset: Bit 2 <- getRevokerOffset addr;
          LetIf retVal : Bit DXlen <- If #isRevoker
          Then (
            RegRead revokerEpoch <- ".revoker.revokerEpoch" in uncoreTree;
            RegRead revokerStart <- ".revoker.revokerStart" in uncoreTree;
            RegRead revokerEnd <- ".revoker.revokerEnd" in uncoreTree;
            Let revokerVal: Data <-
              (Or [ITE0 (Eq #offset $0) ##revokerEpoch;
                   ITE0 (Eq #offset $1) (Const ty Data (bits.of_Z _ 0));
                   ITE0 (Eq #offset $2) {< ##revokerStart, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >};
                   ITE0 (Eq #offset $3) {< ##revokerEnd, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >}]);
            Return (ZeroExtendTo DXlen #revokerVal)
          ) Else (liftAction uncore_np_mem (rawMemIfc.(mem_readBits) addr));
          Return #retVal );
      mem_readTag := fun addr =>
        liftAction uncore_np_mem (rawMemIfc.(mem_readTag) addr);
      mem_readRevBit := fun addr =>
        liftAction uncore_np_mem (rawMemIfc.(mem_readRevBit) addr);
      mem_readInst := fun addr =>
        liftAction uncore_np_mem (rawMemIfc.(mem_readInst) addr);
      mem_writeBits := fun addr val sz =>
        ( Let isRevoker: Bool <- isRevokerAddr #addr;
          Let offset: Bit 2 <- getRevokerOffset addr;
          Let alignedAddr <- TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #addr;
          If #isRevoker
          Then (
            (* TODO: update only upto sz bytes; keep the rest of the value same as what we had earlier *)
            If (Eq #offset $0)
            Then (
              RegRead oldEpoch <- ".revoker.revokerEpoch" in uncoreTree;
              Let newEpoch : Data <- TruncLsb Xlen Xlen #val;
              Let updatedEpoch : Data <- updateWordByByteSz #sz #oldEpoch #newEpoch;
              RegWrite ".revoker.revokerEpoch" in uncoreTree <- #updatedEpoch;
              Retv
            );
            If (Eq #offset $1)
            Then (
              RegWrite ".revoker.revokerKick" in uncoreTree <- (Const ty Bool true);
              Retv
            );
            If (Eq #offset $2)
            Then (
              RegRead oldStart <- ".revoker.revokerStart" in uncoreTree;
              Let oldAddr : Addr <- {< #oldStart, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >};
              Let newAddr : Addr <- TruncLsb Xlen Xlen #val;
              Let updatedAddr : Addr <- updateWordByByteSz #sz #oldAddr #newAddr;
              RegWrite ".revoker.revokerStart" in uncoreTree <- TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #updatedAddr;
              Retv
            );
            If (Eq #offset $3)
            Then (
              RegRead oldEnd <- ".revoker.revokerEnd" in uncoreTree;
              Let oldAddr : Addr <- {< #oldEnd, Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >};
              Let newAddr : Addr <- TruncLsb Xlen Xlen #val;
              Let updatedAddr : Addr <- updateWordByByteSz #sz #oldAddr #newAddr;
              RegWrite ".revoker.revokerEnd" in uncoreTree <- TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #updatedAddr;
              Retv
            );
            Retv
          ) Else (liftAction uncore_np_mem (rawMemIfc.(mem_writeBits) addr val sz));
          Retv );
      mem_writeTag := fun addr tag =>
        liftAction uncore_np_mem (rawMemIfc.(mem_writeTag) addr tag)
    |}.

    (* TODO: Check with Wes about this design *)
    Definition revoker: Action ty uncoreTree (Bit 0) :=
      ( RegRead revokerEpoch <- ".revoker.revokerEpoch" in uncoreTree;
        RegRead revokerKick <- ".revoker.revokerKick" in uncoreTree;
        RegRead revokerStart <- ".revoker.revokerStart" in uncoreTree;
        RegRead revokerEnd <- ".revoker.revokerEnd" in uncoreTree;
        RegRead revokeAddr <- ".revoker.revokeAddr" in uncoreTree;

        Let waiting <- Sge #revokeAddr #revokerEnd;

        If (Not #waiting)
        Then (
          Let revokeAddrFull : Addr <- {< #revokeAddr, ConstDefK (Bit LgNumBytesFullCapSz) >};
          LetA ldTag: Bool <- liftAction uncore_np_mem (rawMemIfc.(mem_readTag) revokeAddr);
          LetA bits: Bit DXlen <- liftAction uncore_np_mem (rawMemIfc.(mem_readBits) revokeAddrFull);
          Let fullCap: FullCap <- FromBit FullCap #bits;
          Let ldCap: Cap <- #fullCap`"cap";
          Let ldVal: Addr <- #fullCap`"addr";
          LetL ldECap: ECap <- decodeCap ldCap ldVal;
          Let ldBase <- #ldECap`"base";
          LetA revBit: Bool <- liftAction uncore_np_mem (rawMemIfc.(mem_readRevBit) ldBase);
          Let ldTagFinal <- And [#ldTag; Not #revBit];
          Act (liftAction uncore_np_mem (rawMemIfc.(mem_writeTag) revokeAddr ldTagFinal));
          RegWrite ".revoker.revokeAddr" in uncoreTree <- Add [#revokeAddr; $1];
          Retv)
        Else (
          If (#revokerKick)
            Then (
              RegWrite ".revoker.revokerEpoch" in uncoreTree <- Add [#revokerEpoch; $1];
              RegWrite ".revoker.revokerKick" in uncoreTree <- ConstDef;
              RegWrite ".revoker.revokeAddr" in uncoreTree <- #revokerStart;
              Retv );
          Retv);
        Retv ).
  End Ty.
End Uncore.
