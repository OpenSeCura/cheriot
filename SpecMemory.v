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
From Cheriot Require Import SpecDefines Binary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Definition TagAddrWidth : Z := AddrSz - LgNumBytesFullCapSz.

Record MemIfc {ty: Kind -> Type} := {
  memTree : Tree Elem ;

  (* Instruction memory channel *)
  mem_readInstRq   : Expr ty Addr -> Action ty memTree (Bit 0) ;
  mem_readInstRp   : Action ty memTree (Option Inst) ;

  (* Unified Data + Tag memory channel returning FullCapWithTag *)
  mem_readMemRq    : Expr ty Addr -> Action ty memTree (Bit 0) ;
  mem_readMemRp    : Action ty memTree (Option FullCapWithTag) ;

  (* Revocation bit memory channel *)
  mem_readRevBitRq : Expr ty (Bit (AddrSz + 1)) -> Action ty memTree (Bit 0) ;
  mem_readRevBitRp : Action ty memTree (Option Bool) ;

  (* Unified Memory write channel taking FullCapWithTag *)
  mem_writeMem     : Expr ty Addr -> Expr ty FullCapWithTag -> Expr ty (Bit LgLgNumBytesFullCapSz) -> Action ty memTree (Bit 0) ;

  (* FENCE.I synchronization channel *)
  mem_fenceI_req   : Action ty memTree (Bit 0) ;
  mem_fenceI_ack   : Action ty memTree Bool ;

  (* Memory alignment / rotation flag *)
  mem_needsRotation : bool
}.

(* ===========================================================================
   SPECIFICATION MEMORY MODEL (Memory State Tree & Actions)
   =========================================================================== *)

Definition fixedBinary : list (bits 8) := map (fun v => bits.of_Z 8 v) binary.

Record MemConfig := {
  mainMemStartAddr        : Z ;
  mainMemSize             : nat ;
  mainMemBoundProof       : Is_true (mainMemStartAddr + Z.of_nat mainMemSize <? Z.shiftl 1 Xlen)%Z ;
  lgMainMemSize_ge_binary : Is_true (length binary <=? mainMemSize)%nat ;

  (* Heap & Revocation Configuration *)
  heapStartAddr           : Z ;
  heapSize                : nat ;
  lgRevGranularity        : Z ;
  revTableStartAddr       : Z ;

  (* Proofs *)
  heap_in_mainMem_proof :
    Is_true ((mainMemStartAddr <=? heapStartAddr) &&
             (heapStartAddr + Z.of_nat heapSize <=? mainMemStartAddr + Z.of_nat mainMemSize))%Z ;
  revTable_in_mainMem_proof :
    Is_true ((mainMemStartAddr <=? revTableStartAddr) &&
             (revTableStartAddr + Z.shiftr (Z.of_nat heapSize) (lgRevGranularity + 3)
              <=? mainMemStartAddr + Z.of_nat mainMemSize))%Z ;
  revTable_heap_disjoint_proof :
    Is_true ((revTableStartAddr + Z.shiftr (Z.of_nat heapSize) (lgRevGranularity + 3) <=? heapStartAddr) ||
             (heapStartAddr + Z.of_nat heapSize <=? revTableStartAddr))%Z
}.

Section MemoryModel.
  Variable config : MemConfig.

  Definition heapEndAddr :=
    config.(heapStartAddr) + Z.of_nat config.(heapSize).

  Definition paddedBinary :=
    (fixedBinary ++ List.repeat (bits.of_Z 8 0) (config.(mainMemSize) - length binary))%list.

  Lemma paddedBinary_length :
    length paddedBinary = config.(mainMemSize).
  Proof.
    unfold paddedBinary, fixedBinary.
    rewrite length_app.
    rewrite repeat_length.
    rewrite length_map.
    pose proof config.(lgMainMemSize_ge_binary) as H.
    apply Is_true_eq_true in H.
    rewrite Nat.leb_le in H.
    lia.
  Qed.

  Definition tagsStartAddr := Z.shiftr (config.(mainMemStartAddr) + NumBytesFullCapSz - 1) LgNumBytesFullCapSz.
  Definition tagsEndAddr   := Z.shiftr (config.(mainMemStartAddr) + Z.of_nat config.(mainMemSize)) LgNumBytesFullCapSz.
  Definition tagsSize : nat := Z.to_nat (tagsEndAddr - tagsStartAddr).

  Definition memoryTree : Tree Elem :=
    Node "mem" [
      Leaf "mainMem" (EReg {| regKind := Array config.(mainMemSize) (Bit 8);
                              regInit := Some (Build_SameTuple (tupleElems := paddedBinary)
                                                 (Is_true_Nat_eq_implies paddedBinary_length)) |}) ;
      Leaf "tags" (EReg {| regKind := Array tagsSize Bool;
                           regInit := Some (Build_SameTuple (tupleElems := List.repeat false tagsSize)
                                               (Is_true_Nat_eq_implies (repeat_length false tagsSize))) |}) ;
      Leaf "instRpReg" (EReg (Build_Reg (Option Inst) (Some (getDefault _)))) ;
      Leaf "memRpReg" (EReg (Build_Reg (Option FullCapWithTag) (Some (getDefault _)))) ;
      Leaf "revBitRpReg" (EReg (Build_Reg (Option Bool) (Some (getDefault _))))
    ].

  Section Ty.
    Variable ty : Kind -> Type.

    Definition isMemAddr (a : Expr ty Addr) : Expr ty Bool :=
      Sge a (Const ty Addr (bits.of_Z Xlen config.(mainMemStartAddr))).

    Definition isTagsAddr (a : Expr ty (Bit TagAddrWidth)) : Expr ty Bool :=
      Sge a (Const ty (Bit TagAddrWidth) (bits.of_Z TagAddrWidth tagsStartAddr)).

    Definition isHeapAddr (a : Expr ty (Bit (AddrSz + 1))) : Expr ty Bool :=
      And [ Sge a (Const ty (Bit (AddrSz + 1)) (bits.of_Z (AddrSz + 1) config.(heapStartAddr))) ;
            Slt a (Const ty (Bit (AddrSz + 1)) (bits.of_Z (AddrSz + 1) heapEndAddr)) ].

    (* 1. Instruction Memory Channel *)
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

    Definition readInstRp : Action ty memoryTree (Option Inst) :=
      RegRead instVal <- "mem.instRpReg" in memoryTree ;
      Return #instVal.

    (* 2. Data + Tag Memory Channel *)
    Definition readMemRq (addr : Expr ty Addr) : Action ty memoryTree (Bit 0) :=
      Let is_mem_valid : Bool <- isMemAddr addr ;
      Let tagAddr : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
      Let is_tag_valid : Bool <- isTagsAddr #tagAddr ;
      If (And [ #is_mem_valid ; #is_tag_valid ]) Then (
        Let memOffset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) addr ;
        Let tagOffset <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) #tagAddr ;
        RegRead memVal  <- "mem.mainMem" in memoryTree ;
        RegRead tagsVal <- "mem.tags"    in memoryTree ;
        Let dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <-
          slice #memVal #memOffset (Z.to_nat NumBytesFullCapSz) ;
        Let rawTag   : Bool <- ReadArray #tagsVal #tagOffset ;
        Let rawBits  : Bit FullCapSz <- ToBit #dataBytes ;
        Let rawAddr  : Addr <- TruncLsb Xlen Xlen #rawBits ;
        Let rawCap   : Cap  <- FromBit Cap (TruncMsb Xlen Xlen #rawBits) ;
        Let rp : FullCapWithTag <- STRUCT {
          "tag"  ::= #rawTag ;
          "cap"  ::= #rawCap ;
          "addr" ::= #rawAddr
        } ;
        RegWrite "mem.memRpReg" in memoryTree <- mkSome #rp ;
        Retv
      ) Else (
        RegWrite "mem.memRpReg" in memoryTree <- mkSome ConstDef ;
        Retv
      ) ;
      Retv.

    Definition readMemRp : Action ty memoryTree (Option FullCapWithTag) :=
      RegRead memVal <- "mem.memRpReg" in memoryTree ;
      Return #memVal.

    (* 3. Revocation Bit Channel *)
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

    Definition readRevBitRp : Action ty memoryTree (Option Bool) :=
      RegRead revVal <- "mem.revBitRpReg" in memoryTree ;
      Return #revVal.

    (* 4. Memory Write Operation *)
    Definition writeMem (addr : Expr ty Addr) (val : Expr ty FullCapWithTag)
                        (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Action ty memoryTree (Bit 0) :=
      Let is_mem_valid : Bool <- isMemAddr addr ;
      Let tagAddr : Bit TagAddrWidth <- TruncMsb TagAddrWidth LgNumBytesFullCapSz addr ;
      Let is_tag_valid : Bool <- isTagsAddr #tagAddr ;
      If (And [ #is_mem_valid ; #is_tag_valid ]) Then (
        Let memOffset <- getMemOffset config.(mainMemStartAddr) (Z.of_nat config.(mainMemSize)) addr ;
        Let tagOffset <- getMemOffset tagsStartAddr (Z.of_nat tagsSize) #tagAddr ;
        Let num_bytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 memSize ;
        Let cap       : Cap                           <- val`"cap" ;
        Let data      : Addr                          <- val`"addr" ;
        Let tag       : Bool                          <- val`"tag" ;
        Let rawData   : Bit FullCapSz                 <- {< ToBit #cap, #data >} ;
        RegRead memVal  <- "mem.mainMem" in memoryTree ;
        RegRead tagsVal <- "mem.tags"    in memoryTree ;
        LetL updatedMem : Array config.(mainMemSize) (Bit 8) <-
          updSlice #memVal #memOffset (FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) #rawData) #num_bytes ;
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
      memTree           := memoryTree ;
      mem_readInstRq    := readInstRq ;
      mem_readInstRp    := readInstRp ;
      mem_readMemRq     := readMemRq ;
      mem_readMemRp     := readMemRp ;
      mem_readRevBitRq  := readRevBitRq ;
      mem_readRevBitRp  := readRevBitRp ;
      mem_writeMem      := writeMem ;
      mem_fenceI_req    := fenceI_req ;
      mem_fenceI_ack    := fenceI_ack ;
      mem_needsRotation := false
    |}.
  End Ty.
End MemoryModel.
