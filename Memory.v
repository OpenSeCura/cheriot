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
From Guru Require Import Syntax Notations Semantics Library Composition.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
   SPECIFICATION MEMORY MODEL (Memory State Tree & Actions)
   =========================================================================== *)

Record MemIfc {ty: Kind -> Type} := {
  memTree : Tree Elem ;

  (* 1. Instruction Memory Channel *)
  mem_canReadInstRq   : Action ty memTree Bool ;
  mem_readInstRq      : Expr ty Addr -> Action ty memTree (Bit 0) ;
  mem_isInstRpValid   : Action ty memTree Bool ;
  mem_getInstRp       : Action ty memTree Inst ;

  (* 2. Data + Tag Memory Channel *)
  mem_canReadMemRq    : Action ty memTree Bool ;
  mem_readMemRq       : Expr ty Addr -> Action ty memTree (Bit 0) ;
  mem_isMemRpValid    : Action ty memTree Bool ;
  mem_getMemRp        : Action ty memTree FullCapWithTag ;

  (* 3. Revocation Bit Memory Channel *)
  mem_canReadRevBitRq : Action ty memTree Bool ;
  mem_readRevBitRq    : Expr ty (Bit (AddrSz + 1)) -> Action ty memTree (Bit 0) ;
  mem_isRevBitRpValid : Action ty memTree Bool ;
  mem_getRevBitRp     : Action ty memTree Bool ;

  (* 4. Memory Write Channel *)
  mem_writeMem      : Expr ty Addr -> Expr ty FullCapWithTag -> Expr ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree (Bit 0) ;

  (* 5. FENCE.I Synchronization Channel *)
  mem_fenceI_req    : Action ty memTree (Bit 0) ;
  mem_fenceI_ack    : Action ty memTree Bool ;

  (* 6. Memory Alignment / Rotation Flag *)
  mem_needsRotation : bool
}.

Section MemoryModel.
  Variable config : MemConfig.

  Local Notation isMemAddr := (isMemAddr config).
  Local Notation isTagsAddr := (isTagsAddr config).
  Local Notation isHeapAddr := (isHeapAddr config).
  Local Notation heapEndAddr := (heapEndAddr config).
  Local Notation tagsStartAddr := (tagsStartAddr config).
  Local Notation tagsEndAddr := (tagsEndAddr config).
  Local Notation tagsSize := (tagsSize config).
  Local Notation paddedBinary := (paddedBinary config).
  Local Notation paddedBinary_length := (paddedBinary_length config).

  Definition memoryTree : Tree Elem :=
    Node "mem" [
      Leaf "mainMem" (EReg {| regKind := Array config.(mainMemSize) (Bit 8);
                              regInit := Some (Build_SameTuple (tupleElems := paddedBinary)
                                                 (Is_true_Nat_eq_implies paddedBinary_length)) |}) ;
      Leaf "tags" (EReg {| regKind := Array tagsSize Bool;
                           regInit := Some (Build_SameTuple (tupleElems := List.repeat false tagsSize)
                                               (Is_true_Nat_eq_implies (repeat_length false tagsSize))) |}) ;
      Leaf "instRpReg"   (EReg (Build_Reg (Option Inst) (Some (getDefault _)))) ;
      Leaf "bytesRpReg"  (EReg (Build_Reg (Option (Bit FullCapSz)) (Some (getDefault _)))) ;
      Leaf "tagRpReg"    (EReg (Build_Reg (Option Bool) (Some (getDefault _)))) ;
      Leaf "revBitRpReg" (EReg (Build_Reg (Option Bool) (Some (getDefault _))))
    ].

  Section Ty.
    Variable ty : Kind -> Type.

    (* 1. Instruction Memory Channel *)
    Definition canReadInstRq : Action ty memoryTree Bool :=
      RegRead rpVal <- "mem.instRpReg" in memoryTree ;
      Return (Not (##rpVal `? "Some")).

    Definition readInstRq (addr : Expr ty Addr) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isMemAddr addr ;
      If #is_valid Then (
        Let offset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) addr ;
        RegRead memVal <- "mem.mainMem" in memoryTree ;
        Let instBytes : Array (Z.to_nat (InstSz / 8)) (Bit 8) <- slice #memVal #offset (Z.to_nat (InstSz / 8)) ;
        RegWrite "mem.instRpReg" in memoryTree <- mkSome (ToBit #instBytes) ;
        Retv
      ) Else (
        RegWrite "mem.instRpReg" in memoryTree <- mkSome ConstDef ;
        Retv
      ) ;
      Retv.

    Definition isInstRpValid : Action ty memoryTree Bool :=
      RegRead rpVal <- "mem.instRpReg" in memoryTree ;
      Return (##rpVal `? "Some").

    Definition getInstRp : Action ty memoryTree Inst :=
      RegRead rpVal <- "mem.instRpReg" in memoryTree ;
      RegWrite "mem.instRpReg" in memoryTree <- ConstDef ;
      Return (##rpVal `! "Some").

    (* 2. Data + Tag Memory Channel *)
    Definition canReadMemRq : Action ty memoryTree Bool :=
      RegRead bytesVal <- "mem.bytesRpReg" in memoryTree ;
      RegRead tagVal   <- "mem.tagRpReg"   in memoryTree ;
      Return (And [ Not (##bytesVal `? "Some") ; Not (##tagVal `? "Some") ]).

    Definition readMemRq (addr : Expr ty Addr) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isMemAddr addr ;
      If #is_valid Then (
        Let offset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) addr ;
        Let tagAddr : Bit (AddrSz - LgNumBytesFullCapSz) <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
        Let tagOffset <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) #tagAddr ;
        RegRead memVal  <- "mem.mainMem" in memoryTree ;
        RegRead tagsVal <- "mem.tags"    in memoryTree ;
        Let dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <- slice #memVal #offset (Z.to_nat NumBytesFullCapSz) ;
        RegWrite "mem.bytesRpReg" in memoryTree <- mkSome (ToBit #dataBytes) ;
        RegWrite "mem.tagRpReg"   in memoryTree <- mkSome (ReadArray #tagsVal #tagOffset) ;
        Retv
      ) Else (
        RegWrite "mem.bytesRpReg" in memoryTree <- mkSome ConstDef ;
        RegWrite "mem.tagRpReg"   in memoryTree <- mkSome ConstDef ;
        Retv
      ) ;
      Retv.

    Definition isMemRpValid : Action ty memoryTree Bool :=
      RegRead bytesVal <- "mem.bytesRpReg" in memoryTree ;
      RegRead tagVal   <- "mem.tagRpReg"   in memoryTree ;
      Return (And [ ##bytesVal `? "Some" ; ##tagVal `? "Some" ]).

    Definition getMemRp : Action ty memoryTree FullCapWithTag :=
      RegRead bytesVal <- "mem.bytesRpReg" in memoryTree ;
      RegRead tagVal   <- "mem.tagRpReg"   in memoryTree ;
      RegWrite "mem.bytesRpReg" in memoryTree <- ConstDef ;
      RegWrite "mem.tagRpReg"   in memoryTree <- ConstDef ;
      Let rawBits : Bit FullCapSz <- ##bytesVal `! "Some" ;
      Let rawTag  : Bool          <- ##tagVal   `! "Some" ;
      Let rawAddr : Addr          <- TruncLsb Xlen Xlen #rawBits ;
      Let rawCap  : Cap           <- FromBit Cap (TruncMsb Xlen Xlen #rawBits) ;
      @Return ty memoryTree FullCapWithTag (STRUCT {
        "tag"  ::= #rawTag ;
        "cap"  ::= #rawCap ;
        "addr" ::= #rawAddr
      }).

    (* 3. Revocation Bit Channel *)
    Definition canReadRevBitRq : Action ty memoryTree Bool :=
      RegRead rpVal <- "mem.revBitRpReg" in memoryTree ;
      Return (Not (##rpVal `? "Some")).

    Definition readRevBitRq (base : Expr ty (Bit (AddrSz + 1))) : Action ty memoryTree (Bit 0).
    refine (
      Let is_heap : Bool <- isHeapAddr base ;
      If #is_heap Then (
        Let heapOffset : Bit (AddrSz + 1) <-
          Sub base (Const ty (Bit (AddrSz + 1)) (bits.of_Z (AddrSz + 1) config.(heapStartAddr))) ;
        Let castHeapOffset <- castBits _ #heapOffset ;
        Let totalBitIdx : Bit ((AddrSz + 1) - config.(lgRevGranularity)) <-
          TruncMsb ((AddrSz + 1) - config.(lgRevGranularity)) config.(lgRevGranularity) #castHeapOffset ;
        Let castTotalBitIdx <- castBits _ #totalBitIdx ;
        Let byteIdxInTable : Bit (((AddrSz + 1) - config.(lgRevGranularity)) - 3) <-
          TruncMsb (((AddrSz + 1) - config.(lgRevGranularity)) - 3) 3 #castTotalBitIdx ;
        Let byteIdxExt : Bit AddrSz <- castBits _ (ZeroExtendTo AddrSz #byteIdxInTable) ;
        Let revByteAddr : Addr <-
          Add [ Const ty Addr (bits.of_Z Xlen config.(revTableStartAddr)) ; #byteIdxExt ] ;
        Let bitInByte : Bit 3 <-
          TruncLsb (((AddrSz + 1) - config.(lgRevGranularity)) - 3) 3 #castTotalBitIdx ;
        Let offset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) #revByteAddr ;
        RegRead memVal <- "mem.mainMem" in memoryTree ;
        Let byteVal : Bit 8 <- ReadArray #memVal #offset ;
        Let revBit  : Bool  <- ReadArray (FromBit (Array 8 Bool) #byteVal) #bitInByte ;
        RegWrite "mem.revBitRpReg" in memoryTree <- mkSome #revBit ;
        Retv
      ) Else (
        RegWrite "mem.revBitRpReg" in memoryTree <- mkSome (ConstBool false) ;
        Retv
      ) ;
      Retv); abstract lia.
    Defined.

    Definition isRevBitRpValid : Action ty memoryTree Bool :=
      RegRead rpVal <- "mem.revBitRpReg" in memoryTree ;
      Return (##rpVal `? "Some").

    Definition getRevBitRp : Action ty memoryTree Bool :=
      RegRead rpVal <- "mem.revBitRpReg" in memoryTree ;
      RegWrite "mem.revBitRpReg" in memoryTree <- ConstDef ;
      Return (##rpVal `! "Some").

    (* 4. Memory Write Operation *)
    Definition writeMem (addr : Expr ty Addr) (val : Expr ty FullCapWithTag)
                        (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isMemAddr addr ;
      If #is_valid Then (
        Let offset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) addr ;
        Let tagAddr : Bit (AddrSz - LgNumBytesFullCapSz) <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
        Let tagOffset <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) #tagAddr ;
        Let num_bytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 memSize ;
        Let cap       : Cap                           <- val`"cap" ;
        Let data      : Addr                          <- val`"addr" ;
        Let tag       : Bool                          <- val`"tag" ;
        Let rawData   : Bit FullCapSz                 <- {< ToBit #cap, #data >} ;
        RegRead memVal  <- "mem.mainMem" in memoryTree ;
        RegRead tagsVal <- "mem.tags"    in memoryTree ;
        LetL updatedMem : Array config.(mainMemSize) (Bit 8) <-
          updSlice #memVal #offset (FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData) #num_bytes ;
        RegWrite "mem.mainMem" in memoryTree <- #updatedMem ;
        RegWrite "mem.tags"    in memoryTree <- UpdateArray #tagsVal #tagOffset #tag ;
        Retv
      ) ;
      Retv.

    (* 5. FENCE.I Synchronization Channel *)
    Definition fenceI_req : Action ty memoryTree (Bit 0) :=
      Retv.

    Definition fenceI_ack : Action ty memoryTree Bool :=
      Return (ConstBool true).

    (* 6. Top-level MemIfc Instance *)
    Definition specMemIfc : @MemIfc ty := {|
      memTree             := memoryTree ;
      mem_canReadInstRq   := canReadInstRq ;
      mem_readInstRq      := readInstRq ;
      mem_isInstRpValid   := isInstRpValid ;
      mem_getInstRp       := getInstRp ;
      mem_canReadMemRq    := canReadMemRq ;
      mem_readMemRq       := readMemRq ;
      mem_isMemRpValid    := isMemRpValid ;
      mem_getMemRp        := getMemRp ;
      mem_canReadRevBitRq := canReadRevBitRq ;
      mem_readRevBitRq    := readRevBitRq ;
      mem_isRevBitRpValid := isRevBitRpValid ;
      mem_getRevBitRp     := getRevBitRp ;
      mem_writeMem        := writeMem ;
      mem_fenceI_req      := fenceI_req ;
      mem_fenceI_ack      := fenceI_ack ;
      mem_needsRotation   := false
    |}.
  End Ty.
End MemoryModel.
