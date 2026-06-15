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

From Stdlib Require Import String List ZArith Zmod Bool Psatz.
Require Import Guru.Syntax Guru.Notations Guru.Semantics Guru.Library Guru.Composition.
Require Import Cheriot.Alu Cheriot.Binary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

#[projections(primitive)]
Record MemIfc {mem_t: Tree Elem} {ty: Kind -> Type} := {
  mem_readBits: ty Addr -> Action ty mem_t (Bit DXlen);
  mem_readTag: ty (Bit (AddrSz - LgNumBytesFullCapSz)) -> Action ty mem_t Bool;
  mem_readRevBit: ty (Bit (AddrSz + 1)) -> Action ty mem_t Bool;
  mem_readInst: ty Addr -> Action ty mem_t Inst;
  mem_writeBits: ty Addr -> ty (Bit DXlen) -> ty (Bit MemSzSz) -> Action ty mem_t (Bit 0);
  mem_writeTag: ty (Bit (AddrSz - LgNumBytesFullCapSz)) -> ty Bool -> Action ty mem_t (Bit 0)
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

    Definition updateWordByByteSz := @updateBitsByChunkSz ty (Z.to_nat XlenBytes) 8.

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
        Let memTagAddr: Bit (AddrSz - LgNumBytesFullCapSz) <- TruncMsb _ LgNumBytesFullCapSz #memAddr;

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
        Let memTagAddr: Bit (AddrSz - LgNumBytesFullCapSz) <- TruncMsb _ LgNumBytesFullCapSz #memAddr;
        
        If #Store
        Then (
          Act memIfc.(mem_writeBits) memAddr stBits memSz;
          If #isCap
          Then (Act memIfc.(mem_writeTag) memTagAddr stTag; Retv)
          Else (
            Let isAligned : Bool <- isZero (TruncLsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #memAddr);
            Let memTagAddrPlusOne <- Add [#memTagAddr; $1];
            Let clearTag : Bool <- Const ty Bool false;
            Act memIfc.(mem_writeTag) memTagAddr clearTag;
            If (Not #isAligned)
              Then (memIfc.(mem_writeTag) memTagAddrPlusOne clearTag);
            Retv
          );
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
        Let memTagAddr: Bit (AddrSz - LgNumBytesFullCapSz) <- TruncMsb _ LgNumBytesFullCapSz #memAddr;

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

Definition getMemOffset {ty: Kind -> Type} (startAddr: Z) (size: Z) n (addr: Expr ty (Bit n)) :
  Expr ty (Bit (Z.log2_up size)) :=
  (let castAddr := castBits (ltac:(lia): (n = Z.log2_up size + (n - Z.log2_up size))%Z) addr in
   if Z.eqb (startAddr mod (2 ^ Z.log2_up size)) 0
   then
     TruncLsb (n - Z.log2_up size) (Z.log2_up size) castAddr
   else
     TruncLsb (n - Z.log2_up size) (Z.log2_up size) (Sub castAddr $startAddr))%guru.

Section Uncore.
  Variable RevokerStartAddr: Z.
  Definition RevokerNumRegs : nat := 4.
  Definition RevokerSizeBytes : Z := XlenBytes * Z.of_nat RevokerNumRegs.
  Definition RevokerAlignBits : Z := Z.log2_up RevokerSizeBytes.

  Variable revokeAddrInit: type (Bit (AddrSz - LgNumBytesFullCapSz)).

  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable mem_t: Tree Elem.

  Definition RevokerState : Kind := Struct [
    ("start", Bit (AddrSz - LgNumBytesFullCapSz));
    ("end", Bit (AddrSz - LgNumBytesFullCapSz));
    ("epoch", Data);
    ("kick", Bool)
  ].

  Variable revokerStateInit: type RevokerState.

  Definition uncoreTree : Tree Elem :=
    Node "" [
      Node "mem" [mem_t];
      Node "revoker" [
        Leaf "revokerState" (EReg {| regKind := RevokerState; regInit := Some revokerStateInit |});
        Leaf "revokeAddr" (EReg {| regKind := Bit (AddrSz - LgNumBytesFullCapSz); regInit := Some revokeAddrInit |})
      ]
    ].

  Definition uncore_np_mem: NodePath uncoreTree mem_t := ltac:(solveNodePath uncoreTree ".mem"%string mem_t).

  Definition RevokerEndAddr : Z :=
    RevokerStartAddr + RevokerSizeBytes - 1.

  Section Ty.
    Variable ty: Kind -> Type.
    Variable rawMemIfc: @MemIfc mem_t ty.

    Definition decodeRevokerState (s: ty RevokerState) : Expr ty (Array RevokerNumRegs (Bit 32)) :=
      ARRAY [ {< ##s`"start", Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >};
              {< ##s`"end", Const ty (Bit LgNumBytesFullCapSz) Zmod.zero >};
              ##s`"epoch";
              {< Const ty (Bit (Xlen - 1)) Zmod.zero, ToBit (##s`"kick") >} ].

    Definition encodeRevokerState (arr: ty (Array RevokerNumRegs Data)) : Expr ty RevokerState :=
      STRUCT {
        "start" ::= TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz (##arr $[0]);
        "end" ::= TruncMsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz (#arr $[1]);
        "epoch" ::= #arr $[2];
        "kick" ::= FromBit Bool (TruncLsb (Xlen - 1) 1 (#arr $[3]))
      }.

    Definition isRevokerAddr (a: ty Addr) :=
      And [Sge #a $RevokerStartAddr; Sle #a $RevokerEndAddr].

    Definition uncoreMemIfc : @MemIfc uncoreTree ty := {|
      mem_readBits := fun addr =>
        ( Let isRevoker: Bool <- isRevokerAddr addr;
          LetIf retVal : Bit DXlen <- If #isRevoker
          Then (
            RegRead revokerState <- ".revoker.revokerState" in uncoreTree;
            Let oldArray : Bit (NatZ_mul (Z.to_nat XlenBytes * RevokerNumRegs) 8) <-
                             ToBit (decodeRevokerState revokerState);
            Let bytesArr <- FromBit (Array (Z.to_nat XlenBytes * RevokerNumRegs) (Bit 8)) #oldArray;
            Let byteOffset <- getMemOffset RevokerStartAddr RevokerSizeBytes #addr;
            Let readSlice <- slice #bytesArr #byteOffset (Z.to_nat DXlenBytes);
            Return (ToBit #readSlice)
          ) Else (liftAction uncore_np_mem (rawMemIfc.(mem_readBits) addr));
          Return #retVal );
      mem_readTag := fun addr =>
        liftAction uncore_np_mem (rawMemIfc.(mem_readTag) addr);
      mem_readRevBit := fun addr =>
        liftAction uncore_np_mem (rawMemIfc.(mem_readRevBit) addr);
      mem_readInst := fun addr =>
        liftAction uncore_np_mem (rawMemIfc.(mem_readInst) addr);
      mem_writeBits := fun addr val sz => (
          Let isRevoker: Bool <- isRevokerAddr addr;
          If #isRevoker
          Then (
            RegRead revokerState <- ".revoker.revokerState" in uncoreTree;
            Let oldArray : Bit (NatZ_mul (Z.to_nat XlenBytes * RevokerNumRegs) 8) <-
                             ToBit (decodeRevokerState revokerState);
            Let bytesArr <- FromBit (Array (Z.to_nat XlenBytes * RevokerNumRegs) (Bit 8)) #oldArray;
            Let byteOffset <- getMemOffset RevokerStartAddr RevokerSizeBytes #addr;
            Let newValBytes <- FromBit (Array (Z.to_nat DXlenBytes) (Bit 8)) #val;
            LetL updatedBytesArr <- updSlice #bytesArr #byteOffset #newValBytes #sz;
            Let updatedWordArr <- FromBit (Array RevokerNumRegs Data) (ToBit #updatedBytesArr);
            Let updatedState <- encodeRevokerState updatedWordArr;
            RegWrite ".revoker.revokerState" in uncoreTree <- #updatedState;
            Retv
          ) Else (liftAction uncore_np_mem (rawMemIfc.(mem_writeBits) addr val sz));
          Retv );

      mem_writeTag := fun addr tag =>
        liftAction uncore_np_mem (rawMemIfc.(mem_writeTag) addr tag)
    |}.

    (* TODO: Check with Wes about this design *)
    Definition revoker: Action ty uncoreTree (Bit 0) :=
      ( RegRead revokerState <- ".revoker.revokerState" in uncoreTree;
        RegRead revokeAddr <- ".revoker.revokeAddr" in uncoreTree;
        LetL revokerStart : Bit (AddrSz - LgNumBytesFullCapSz) <- RetE (#revokerState`"start");
        LetL revokerEnd : Bit (AddrSz - LgNumBytesFullCapSz) <- RetE (#revokerState`"end");
        LetL revokerEpoch : Data <- RetE (#revokerState`"epoch");
        LetL revokerKick : Bool <- RetE (#revokerState`"kick");

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
          Let isOddEpoch <- FromBit Bool (TruncLsb (Xlen-1) 1 #revokerEpoch);
          If (#isOddEpoch)
          Then (
            RegWrite ".revoker.revokerState" in uncoreTree <-
                                                  (STRUCT {
                                                       "start" ::= #revokerStart;
                                                       "end" ::= #revokerEnd;
                                                       "epoch" ::= Add [#revokerEpoch; $1];
                                                       "kick" ::= #revokerKick }: Expr ty RevokerState );
            Retv)
          Else (
            If (#revokerKick)
            Then (
              LetL updatedState <- RetE (STRUCT {
                "start" ::= #revokerStart;
                "end" ::= #revokerEnd;
                "epoch" ::= {< TruncMsb (Xlen-1) 1 #revokerEpoch, Const ty (Bit 1) Zmod.one >};
                "kick" ::= Const ty Bool false
              });
              RegWrite ".revoker.revokerState" in uncoreTree <- #updatedState;
              RegWrite ".revoker.revokeAddr" in uncoreTree <- #revokerStart;
              Retv );
            Retv);
          Retv );
        Retv ).
  End Ty.
End Uncore.

Definition fixedBinary : list (bits 8) := map (fun v => bits.of_Z 8 v) binary.

Record MemConfig := {
  memStartAddr : Z;
  memSize : nat;
  memBoundProof : (memStartAddr + Z.of_nat memSize < Z.shiftl 1 Xlen)%Z
}.

Record RevConfig := {
  heapStartAddr : Z;
  numRevBits : nat;
  revLgGranularity : Z;
  revBoundProof : (heapStartAddr + Z.of_nat numRevBits * 2^revLgGranularity < Z.shiftl 1 Xlen)%Z
}.

Section Memories.
  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable config : MemConfig.

  Section Mem.
    Variable lgMemSize_ge_binary : Is_true (length binary <=? config.(memSize))%nat.

    Definition paddedBinary :=
      (fixedBinary ++ List.repeat (bits.of_Z 8 0) (config.(memSize) - length binary))%list.

    Lemma paddedBinary_length :
      length paddedBinary = config.(memSize).
    Proof.
      unfold paddedBinary, fixedBinary.
      rewrite length_app.
      rewrite repeat_length.
      rewrite length_map.
      apply Is_true_eq_true in lgMemSize_ge_binary.
      rewrite Nat.leb_le in lgMemSize_ge_binary.
      lia.
    Qed.

    Definition mem : Tree Elem :=
      Leaf "mem" (EReg {|regKind := Array config.(memSize) (Bit 8);
                              regInit := Some (Build_SameTuple (tupleElems := paddedBinary)
                                                 (Is_true_Nat_eq_implies paddedBinary_length)) |}).

    Section Ty.
      Variable ty : Kind -> Type.

      Definition readBytes (addr: Expr ty Addr) : Action ty mem (Bit DXlen) :=
        Let is_valid <- Sge addr (Const ty Addr (bits.of_Z Xlen config.(memStartAddr)));
        LetIf retVal : Bit DXlen <- If #is_valid
        Then (
          Let offset <- Sub addr (Const ty Addr (bits.of_Z Xlen config.(memStartAddr)));
          RegRead mem <- "mem" in mem;
          Return (ToBit (slice #mem #offset (Z.to_nat DXlenBytes)))
        );
        Return #retVal.

      Definition readInst (addr: Expr ty Addr) : Action ty mem Inst :=
        Let is_valid <- Sge addr (Const ty Addr (bits.of_Z Xlen config.(memStartAddr)));
        LetIf retVal : Inst <- If #is_valid
        Then (
          Let offset <- Sub addr (Const ty Addr (bits.of_Z Xlen config.(memStartAddr)));
          RegRead mem <- "mem" in mem;
          Return (ToBit (slice #mem #offset (Z.to_nat (InstSz/8))))
        );
        Return #retVal.

      Definition writeBytes (addr: Expr ty Addr) (data: Expr ty (Bit DXlen)) (sz: Expr ty (Bit MemSzSz)) :
        Action ty mem (Bit 0) :=
        Let is_valid <- Sge addr (Const ty Addr (bits.of_Z Xlen config.(memStartAddr)));
        If #is_valid
        Then (
          Let offset <- Sub addr (Const ty Addr (bits.of_Z Xlen config.(memStartAddr)));
          Let num_bytes: Bit (MemSz + 1) <- Sll $1 sz;
          RegRead memVal <- "mem" in mem;
          LetA updatedMem <-
            toAction mem (updSlice #memVal #offset (FromBit (Array (Z.to_nat DXlenBytes) (Bit 8)) data) #num_bytes);
          RegWrite "mem" in mem <- #updatedMem;
          Retv
        );
        Retv.
    End Ty.
  End Mem.

  Section Tags.
    Definition tagsStartAddr := Z.shiftr (config.(memStartAddr) + NumBytesFullCapSz - 1) LgNumBytesFullCapSz.
    Definition tagsEndAddr := Z.shiftr (config.(memStartAddr) + Z.of_nat config.(memSize)) LgNumBytesFullCapSz.
    Definition tagsSize: nat := Z.to_nat (tagsEndAddr - tagsStartAddr).
    Definition TagWidth: Z := AddrSz - LgNumBytesFullCapSz.

    Definition tags : Tree Elem :=
      Leaf "tags" (EReg {|regKind := Array tagsSize Bool;
                          regInit := Some (Build_SameTuple (tupleElems := List.repeat false tagsSize)
                                             (Is_true_Nat_eq_implies (repeat_length false tagsSize))) |}).

    Section Ty.
      Variable ty : Kind -> Type.

      Definition readTag (addr: Expr ty (Bit TagWidth)) : Action ty tags Bool :=
        Let is_valid <- Sge addr (Const ty (Bit TagWidth) (bits.of_Z TagWidth tagsStartAddr));
        LetIf retVal : Bool <- If #is_valid
        Then (
          Let offset <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) addr;
          RegRead tagsVal <- "tags" in tags;
          Return (#tagsVal@[#offset])
        );
        Return #retVal.

      Definition writeTag (addr: Expr ty (Bit TagWidth)) (tag: Expr ty Bool) : Action ty tags (Bit 0) :=
        Let is_valid <- Sge addr (Const ty (Bit TagWidth) (bits.of_Z TagWidth tagsStartAddr));
        If #is_valid
        Then (
          Let offset <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) addr;
          RegRead tagsVal <- "tags" in tags;
          RegWrite "tags" in tags <- #tagsVal@[#offset <- tag];
          Retv
        );
        Retv.
    End Ty.
  End Tags.
End Memories.

Section RevBits.
  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Variable config : RevConfig.

  Local Notation revBitGranularity := (2 ^ config.(revLgGranularity))%Z.
  Local Notation revBitsWidth := ((AddrSz + 1) - config.(revLgGranularity))%Z.

  Definition revMem : Tree Elem :=
    Leaf "revBits" (EReg {| regKind := Array config.(numRevBits) Bool;
                           regInit := Some (Build_SameTuple (tupleElems := List.repeat false config.(numRevBits))
                                              (Is_true_Nat_eq_implies (repeat_length false config.(numRevBits)))) |}).

  Section Ty.
    Variable ty : Kind -> Type.

    Definition readRevBit (addr: Expr ty (Bit (AddrSz + 1))) : Action ty revMem Bool :=
      Let is_valid <- Sge addr (Const ty (Bit _) (bits.of_Z _ config.(heapStartAddr)));
      LetIf retVal : Bool <- If #is_valid
      Then (
        Let byteOffset <- Sub addr (Const ty (Bit _) (bits.of_Z _ config.(heapStartAddr)));
        Let castByteOffset <- castBits (ltac:(lia):
                                  ((AddrSz + 1) = config.(revLgGranularity) + revBitsWidth)%Z) #byteOffset;
        Let offset <- TruncMsb revBitsWidth config.(revLgGranularity) #castByteOffset;
        RegRead revVal <- "revBits" in revMem;
        Return (#revVal@[#offset])
      );
      Return #retVal.

    Definition writeRevBit (addr: Expr ty (Bit (AddrSz + 1))) (val: Expr ty Bool) : Action ty revMem (Bit 0) :=
      Let is_valid <- Sge addr (Const ty (Bit _) (bits.of_Z _ config.(heapStartAddr)));
      If #is_valid
      Then (
        Let byteOffset <- Sub addr (Const ty (Bit _) (bits.of_Z _ config.(heapStartAddr)));
        Let castByteOffset <- castBits (ltac:(lia):
                                  ((AddrSz + 1) = config.(revLgGranularity) + revBitsWidth)%Z) #byteOffset;
        Let offset <- TruncMsb revBitsWidth config.(revLgGranularity) #castByteOffset;
        RegRead revVal <- "revBits" in revMem;
        RegWrite "revBits" in revMem <- #revVal@[#offset <- val];
        Retv
      );
      Retv.
  End Ty.
End RevBits.

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
