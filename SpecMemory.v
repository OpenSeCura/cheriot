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

(* ===========================================================================
   GENERIC MEMORY INTERFACE RECORD (MemIfc)
   All read channels are split into Request (Rq) and Response (Rp) stages.
   =========================================================================== *)

Definition TagAddrWidth : Z   := AddrSz - LgNumBytesFullCapSz.

#[projections(primitive)]
Record MemIfc {mem_t: Tree Elem} {ty: Kind -> Type} := {
  (* Instruction memory channel *)
  mem_readInstRq   : Expr ty Addr -> Action ty mem_t (Bit 0) ;
  mem_readInstRp   : Action ty mem_t Inst ;

  (* Data memory bytes channel (FullCapSz = 64 bits = 8 bytes) *)
  mem_readBytesRq  : Expr ty Addr -> Action ty mem_t (Bit 0) ;
  mem_readBytesRp  : Action ty mem_t (Bit FullCapSz) ;

  (* Capability tag memory channel *)
  mem_readTagRq    : Expr ty (Bit TagAddrWidth) -> Action ty mem_t (Bit 0) ;
  mem_readTagRp    : Action ty mem_t Bool ;

  (* Revocation bit memory channel *)
  mem_readRevBitRq : Expr ty (Bit (AddrSz + 1)) -> Action ty mem_t (Bit 0) ;
  mem_readRevBitRp : Action ty mem_t Bool ;

  (* Memory write channels *)
  mem_writeBytes   : Expr ty Addr -> Expr ty (Bit FullCapSz) -> Expr ty (Bit LgLgNumBytesFullCapSz) -> Action ty mem_t (Bit 0) ;
  mem_writeTag     : Expr ty (Bit (AddrSz - LgNumBytesFullCapSz)) -> Expr ty Bool -> Action ty mem_t (Bit 0) ;

  (* FENCE.I synchronization channel *)
  mem_fenceI_req   : Action ty mem_t (Bit 0) ;
  mem_fenceI_ack   : Action ty mem_t Bool
}.

(* ===========================================================================
   SPECIFICATION MEMORY MODEL (Memory State Tree & Actions)
   =========================================================================== *)

Definition fixedBinary : list (bits 8) := map (fun v => bits.of_Z 8 v) binary.

Record MainMemConfig := {
  mainMemStartAddr : Z ;
  mainMemSize : nat ;
  mainMemBoundProof : Is_true (mainMemStartAddr + Z.of_nat mainMemSize <? Z.shiftl 1 Xlen)%Z ;
  lgMainMemSize_ge_binary : Is_true (length binary <=? mainMemSize)%nat
}.

Section MemoryModel.
  Variable config : MainMemConfig.

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
      Leaf "instRpReg" (EReg (Build_Reg Inst None)) ;
      Leaf "bytesRpReg" (EReg (Build_Reg (Bit FullCapSz) None)) ;
      Leaf "tagRpReg" (EReg (Build_Reg Bool None)) ;
      Leaf "revBitRpReg" (EReg (Build_Reg Bool None))
    ].

  Section Ty.
    Variable ty : Kind -> Type.

    Definition isMemAddr (a : Expr ty Addr) : Expr ty Bool :=
      Sge a (Const ty Addr (bits.of_Z Xlen config.(mainMemStartAddr))).

    Definition isTagsAddr (a : Expr ty (Bit TagAddrWidth)) : Expr ty Bool :=
      Sge a (Const ty (Bit TagAddrWidth) (bits.of_Z TagAddrWidth tagsStartAddr)).

    (* 1. Instruction Memory Channel *)
    Definition readInstRq (addr : Expr ty Addr) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isMemAddr addr ;
      If #is_valid Then (
        Let offset : Addr <- Sub addr (Const ty Addr (bits.of_Z Xlen config.(mainMemStartAddr))) ;
        RegRead memVal <- "mem.mainMem" in memoryTree ;
        Let instBytes : Array (Z.to_nat (InstSz / 8)) (Bit 8) <- slice #memVal #offset (Z.to_nat (InstSz / 8)) ;
        RegWrite "mem.instRpReg" in memoryTree <- ToBit #instBytes ;
        Retv
      ) Else (
        RegWrite "mem.instRpReg" in memoryTree <- ConstDef ;
        Retv
      ) ;
      Retv.

    Definition readInstRp : Action ty memoryTree Inst :=
      RegRead instVal <- "mem.instRpReg" in memoryTree ;
      Return #instVal.

    (* 2. Data Bytes Memory Channel *)
    Definition readBytesRq (addr : Expr ty Addr) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isMemAddr addr ;
      If #is_valid Then (
        Let offset : Addr <- Sub addr (Const ty Addr (bits.of_Z Xlen config.(mainMemStartAddr))) ;
        RegRead memVal <- "mem.mainMem" in memoryTree ;
        Let dataBytes : Array (Z.to_nat NumBytesFullCapSz) (Bit 8) <- slice #memVal #offset (Z.to_nat NumBytesFullCapSz) ;
        RegWrite "mem.bytesRpReg" in memoryTree <- ToBit #dataBytes ;
        Retv
      ) Else (
        RegWrite "mem.bytesRpReg" in memoryTree <- ConstDef ;
        Retv
      ) ;
      Retv.

    Definition readBytesRp : Action ty memoryTree (Bit FullCapSz) :=
      RegRead bytesVal <- "mem.bytesRpReg" in memoryTree ;
      Return #bytesVal.

    (* 3. Tag Memory Channel *)
    Definition readTagRq (addr : Expr ty (Bit TagAddrWidth)) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isTagsAddr addr ;
      If #is_valid Then (
        Let offset : Bit TagAddrWidth <- Sub addr (Const ty (Bit TagAddrWidth) (bits.of_Z TagAddrWidth tagsStartAddr)) ;
        RegRead tagsVal <- "mem.tags" in memoryTree ;
        RegWrite "mem.tagRpReg" in memoryTree <- (ReadArray #tagsVal #offset) ;
        Retv
      ) Else (
        RegWrite "mem.tagRpReg" in memoryTree <- ConstDef ;
        Retv
      ) ;
      Retv.

    Definition readTagRp : Action ty memoryTree Bool :=
      RegRead tagVal <- "mem.tagRpReg" in memoryTree ;
      Return #tagVal.

    (* 4. Revocation Bit Channel *)
    Definition readRevBitRq (addr : Expr ty (Bit (AddrSz + 1))) : Action ty memoryTree (Bit 0) :=
      RegWrite "mem.revBitRpReg" in memoryTree <- ConstBool false ;
      Retv.

    Definition readRevBitRp : Action ty memoryTree Bool :=
      RegRead revVal <- "mem.revBitRpReg" in memoryTree ;
      Return #revVal.

    (* 5. Memory Write Operations *)
    Definition writeBytes (addr : Expr ty Addr) (data : Expr ty (Bit FullCapSz)) (memSize : Expr ty (Bit LgLgNumBytesFullCapSz)) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isMemAddr addr ;
      If #is_valid Then (
        Let offset : Addr <- Sub addr (Const ty Addr (bits.of_Z Xlen config.(mainMemStartAddr))) ;
        Let num_bytes : Bit (LgNumBytesFullCapSz + 1) <- Sll $1 memSize ;
        RegRead memVal <- "mem.mainMem" in memoryTree ;
        LetL updatedMem : Array config.(mainMemSize) (Bit 8) <-
          updSlice #memVal #offset (FromBit (Array (Z.to_nat NumBytesFullCapSz) (Bit 8)) data) #num_bytes ;
        RegWrite "mem.mainMem" in memoryTree <- #updatedMem ;
        Retv
      ) ;
      Retv.

    Definition writeTag (addr : Expr ty (Bit TagAddrWidth)) (tag : Expr ty Bool) : Action ty memoryTree (Bit 0) :=
      Let is_valid : Bool <- isTagsAddr addr ;
      If #is_valid Then (
        Let offset : Bit TagAddrWidth <- Sub addr (Const ty (Bit TagAddrWidth) (bits.of_Z TagAddrWidth tagsStartAddr)) ;
        RegRead tagsVal <- "mem.tags" in memoryTree ;
        RegWrite "mem.tags" in memoryTree <- UpdateArray #tagsVal #offset tag ;
        Retv
      ) ;
      Retv.

    (* 6. FENCE.I Synchronization Channel *)
    Definition fenceI_req : Action ty memoryTree (Bit 0) :=
      Retv.

    Definition fenceI_ack : Action ty memoryTree Bool :=
      Return (ConstBool true).

    (* 7. Top-level MemIfc Instance *)
    Definition specMemIfc : @MemIfc memoryTree ty := {|
      mem_readInstRq   := readInstRq ;
      mem_readInstRp   := readInstRp ;
      mem_readBytesRq  := readBytesRq ;
      mem_readBytesRp  := readBytesRp ;
      mem_readTagRq    := readTagRq ;
      mem_readTagRp    := readTagRp ;
      mem_readRevBitRq := readRevBitRq ;
      mem_readRevBitRp := readRevBitRp ;
      mem_writeBytes   := writeBytes ;
      mem_writeTag     := writeTag ;
      mem_fenceI_req   := fenceI_req ;
      mem_fenceI_ack   := fenceI_ack
    |}.
  End Ty.
End MemoryModel.
