(*
 * Copyright 2026 Google LLC (Cherified Team)
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

From Stdlib Require Import String List ZArith Zmod Psatz.
From Guru Require Import Library Syntax Notations Composition.
From Cheriot Require Import Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope guru_scope.

Definition getMemOffset {ty: Kind -> Type} (startAddr: Z) (size: Z) n (addr: Expr ty (Bit n)) :
  Expr ty (Bit (Z.log2_up size)).
  refine
  (let castAddr := castBits _ addr in
   if Z.eqb (startAddr mod (2 ^ Z.log2_up size)) 0
   then
     TruncLsb (n - Z.log2_up size) (Z.log2_up size) castAddr
   else
     TruncLsb (n - Z.log2_up size) (Z.log2_up size) (Sub castAddr $startAddr))%guru;
    abstract lia.
  Defined.

Definition Xlen         := 32.
Definition InstSz       := 32.
Definition CompInstSz   := 16.

Definition RegIdxSz     := 5.
Definition CsrAddrSz    := 12.
Definition Cra          := 1.
Definition RegIdxSzReal := 4.
Definition CapOTypeSz   := 3.
Definition CapPermSz    := (6 : nat).
Definition CapcTSz      := 8.

Definition ScrAddrSz    := Eval compute in RegIdxSz.
Definition LgXlen       := Eval compute in Z.log2_up Xlen.
Definition Data         := Eval compute in Bit Xlen.
Definition AddrSz       := Eval compute in Xlen.
Definition Addr         := Eval compute in Bit AddrSz.
Definition Inst         := Eval compute in Bit InstSz.
Definition LgAddrSz     := Eval compute in Z.log2_up AddrSz.
Definition ExpSz        := Eval compute in LgAddrSz.
Definition NumBytesXlen := Eval compute in (Xlen / 8).
Definition NumRegs      := Eval compute in (2 ^ RegIdxSzReal).

Definition CapBSz          := Eval compute in (CapcTSz + 1).
Definition CapTSz          := Eval compute in CapBSz.

Definition Cap : Kind := STRUCT_TYPE {
                             "R" :: Bool;
                             "p" :: Array CapPermSz Bool;
                             "oType" :: Bit CapOTypeSz;
                             "cE" :: Bit ExpSz;
                             "cT" :: Bit CapcTSz;
                             "B" :: Bit CapBSz }.

Definition FullCapSz := Eval compute in (kindSize Cap + Xlen).
Definition NumBytesFullCapSz := Eval compute in (FullCapSz / 8).
Definition LgNumBytesFullCapSz := Eval compute in Z.log2_up NumBytesFullCapSz.
Definition LgLgNumBytesFullCapSz := Eval compute in Z.log2_up (LgNumBytesFullCapSz + 1).

Definition isCompressed ty (inst: ty Inst) : Expr ty Bool := Not (isAllOnes (TruncLsb (InstSz-2) 2 #inst)).
Definition getCd ty (inst: ty Inst) : Expr ty (Bit RegIdxSz) := #inst`[11:7].
Definition getCs1 ty (inst: ty Inst) : Expr ty (Bit RegIdxSz) := #inst`[19:15].
Definition getScr ty (inst: ty Inst) : Expr ty (Bit ScrAddrSz) := #inst`[24:20].

Definition CallSentryIh := 1.
Definition CallSentryId := 2.
Definition CallSentryIe := 3.
Definition RetSentryId  := 4.
Definition RetSentryIe  := 5.

Definition InstGroup := STRUCT_TYPE {
  "isCompressed"                :: Bool ;
  "isImm"                       :: Bool ;
  "isUnsigned"                  :: Bool ; (* Should be set only for Branch, Slt and Load *)
  "Branch"                      :: Bool ;
  "Cjal"                        :: Bool ;
  "AuiPcc"                      :: Bool ;
  "AuiCgp"                      :: Bool ;
  "CIncAddr"                    :: Bool ;
  "CSetAddr"                    :: Bool ;
  "Cjalr"                       :: Bool ;
  "CTestSubset"                 :: Bool ;
  "CSetBounds"                  :: Bool ;
  "CSetBounds_isExact"          :: Bool ; (* This also captures CSetBounds *)
  "CSetBounds_isRoundDown"      :: Bool ; (* This also captures CSetBounds *)
  "Seal"                        :: Bool ;
  "Unseal"                      :: Bool ;
  "Load"                        :: Bool ;
  "Store"                       :: Bool ;
  "AddSub"                      :: Bool ;
  "AddSub_isSub"                :: Bool ; (* This also captures AddSub *)
  "CGetLen"                     :: Bool ;
  "Slt"                         :: Bool ;
  "CSetEqual"                   :: Bool ;
  "Shift"                       :: Bool ;
  "Shift_isArith"               :: Bool ; (* This also captures Shift *)
  "Shift_isRight"               :: Bool ; (* This also captures Shift *)
  "Logical"                     :: Bool ;
  "Cram"                        :: Bool ;
  "Crrl"                        :: Bool ;
  "CAndPerm"                    :: Bool ;
  "Csr"                         :: Bool ;
  "Scr"                         :: Bool ;
  "Lui"                         :: Bool ;
  "CGetPerm"                    :: Bool ;
  "CGetType"                    :: Bool ;
  "CGetBase"                    :: Bool ;
  "CGetTag"                     :: Bool ;
  "CGetAddr"                    :: Bool ;
  "CGetHigh"                    :: Bool ;
  "CGetTop"                     :: Bool ;
  "CSetHigh"                    :: Bool ;
  "CClearTag"                   :: Bool ;
  "CMove"                       :: Bool ;
  "ECall"                       :: Bool ;
  "EBreak"                      :: Bool ;
  "Mret"                        :: Bool ;
  "Fence"                       :: Bool ;
  "ComparatorGeneral_checkLt"   :: Bool ; (* Should be set only for Branch and Slt *)
  "ComparatorGeneral_checkEq"   :: Bool ; (* Should be set only for Branch and CSetEqual *)
  "ComparatorGeneral_invertRes" :: Bool   (* Should be set only for Branch *)
}.

Definition FunctionalUnits := STRUCT_TYPE {
  "AdderBeforeBoundsCheck" :: Bool ;
  "AdderToOutput" :: Bool ;
  "AddCapBSz" :: Bool ;
  "ComparatorGeneral" :: Bool ;
  "CjalrUnit" :: Bool ;
  "Logical" :: Bool ;
  "CAndPerm" :: Bool ;
  "SealerUnsealer" :: Bool ;
  "Bounds" :: Bool ;
  "BoundsExact" :: Bool ;
  "Shifter" :: Bool ;
  "AdderBeforeRepCheck" :: Bool ;
  "ComparatorTopOrRep" :: Bool ;
  "ComparatorBase" :: Bool ;
  "AddrBoundsCheck" :: Bool ;
  "CapSubset" :: Bool ;
  "CapEq" :: Bool ;
  "ScrSanitizer" :: Bool ;
  "EncodeCap" :: Bool ;
  "DecodeCap" :: Bool ;
  "Deferred" :: Bool ;
  "Exception" :: Bool ;
  "ControlFlow" :: Bool ;
  "ScrCsr" :: Bool ;
  "Saturater" :: Bool ;
  "FenceI" :: Bool
}.

(* ===========================================================================
   CSR & SCR DEFINITIONS, TABLES, MAPPINGS, AND DECODERS
   =========================================================================== *)

Fixpoint enumerate_aux {A : Type} (i : Z) (l : list A) : list (A * Z) :=
  match l with
  | [] => []
  | x :: xs => (x, i) :: enumerate_aux (i + 1) xs
  end.

Definition enumerate {A : Type} (l : list A) : list (A * Z) :=
  enumerate_aux 0 l.

(* CSR Table: List of 4-tuples ("name", 12-bit address, allowReadNoAsr, allowWriteNoAsr) *)
Definition CsrTable := [
  ("mcycle"%string,    0xc00, true,  false) ;
  ("mcycleh"%string,   0xc80, true,  false) ;
  ("mtime"%string,     0xc01, true,  false) ;
  ("mtimeh"%string,    0xc81, true,  false) ;
  ("minstret"%string,  0xc02, true,  false) ;
  ("minstreth"%string, 0xc82, true,  false) ;
  ("mstatus"%string,   0x300, false, false) ;
  ("mie"%string,       0x304, false, false) ;
  ("mip"%string,       0x344, false, false) ;
  ("mcause"%string,    0x342, false, false) ;
  ("mtval"%string,     0x343, false, false) ;
  ("mshwm"%string,     0xbc1, true,  true) ;
  ("mshwmb"%string,    0xbc2, true,  true)
].

(* Lookup Functions by Name for CsrTable *)
Fixpoint getCsrEntryFromList (s : string) (table : list ((string * Z * bool * bool) * Z)) :=
  match table with
  | [] => None
  | ((name, addr, r_no_asr, w_no_asr), idx) :: rest =>
      if String.eqb s name then Some (addr, idx, r_no_asr, w_no_asr)
      else getCsrEntryFromList s rest
  end.

Definition getCsrEntryByName (s : string) := getCsrEntryFromList s (enumerate CsrTable).

Definition getCsrAddrByName (s : string) : option Z :=
  match getCsrEntryByName s with
  | Some (addr, _, _, _) => Some addr
  | None => None
  end.

Definition getCsrIdxByName (s : string) : option Z :=
  match getCsrEntryByName s with
  | Some (_, idx, _, _) => Some idx
  | None => None
  end.

Definition getCsrAllowReadNoAsrByName (s : string) : option bool :=
  match getCsrEntryByName s with
  | Some (_, _, r, _) => Some r
  | None => None
  end.

Definition getCsrAllowWriteNoAsrByName (s : string) : option bool :=
  match getCsrEntryByName s with
  | Some (_, _, _, w) => Some w
  | None => None
  end.

Definition getCsrAddr (s : string) := forceOption (getCsrAddrByName s).
Definition getCsrIdx (s : string) := forceOption (getCsrIdxByName s).
Definition getCsrAllowReadNoAsr (s : string) := forceOption (getCsrAllowReadNoAsrByName s).
Definition getCsrAllowWriteNoAsr (s : string) := forceOption (getCsrAllowWriteNoAsrByName s).

(* SCR Table: List of 2-tuples ("name", 5-bit address) *)
Definition ScrTable := [
  ("MePrevPcc"%string, 27) ;
  ("Mtcc"%string,      28) ;
  ("Mtdc"%string,      29) ;
  ("Mscratchc"%string, 30) ;
  ("MePcc"%string,     31)
].

(* Lookup Functions by Name for ScrTable *)
Fixpoint getScrEntryFromList (s : string) (table : list ((string * Z) * Z)) :=
  match table with
  | [] => None
  | ((name, addr), idx) :: rest =>
      if String.eqb s name then Some (addr, idx)
      else getScrEntryFromList s rest
  end.

Definition getScrEntryByName (s : string) := getScrEntryFromList s (enumerate ScrTable).

Definition getScrAddrByName (s : string) : option Z :=
  match getScrEntryByName s with
  | Some (addr, _) => Some addr
  | None => None
  end.

Definition getScrIdxByName (s : string) : option Z :=
  match getScrEntryByName s with
  | Some (_, idx) => Some idx
  | None => None
  end.

Definition getScrAddr (s : string) := forceOption (getScrAddrByName s).
Definition getScrIdx (s : string) := forceOption (getScrIdxByName s).

Definition CsrIdxSz := Z.log2_up (Z.of_nat (length CsrTable)).
Definition ScrIdxSz := Z.log2_up (Z.of_nat (length ScrTable)).

Definition ScrCsrIdx := [
  ("Scr"%string, Bit ScrIdxSz) ;
  ("Csr"%string, Bit CsrIdxSz)
].

Definition Cs2Source := [
  ("Reg"%string, Bit RegIdxSzReal) ;
  ("ScrCsr"%string, TaggedUnion ScrCsrIdx)
].

Section Cs2Constructors.
  Variable ty : Kind -> Type.
  Definition mkCs2Reg (idx : Expr ty (Bit RegIdxSzReal)) : Expr ty (TaggedUnion Cs2Source) :=
    UNION (Cs2Source, "Reg" ::= idx).

  Definition mkCs2Csr (idx : Expr ty (Bit CsrIdxSz)) : Expr ty (TaggedUnion Cs2Source) :=
    UNION (Cs2Source, "ScrCsr" ::= UNION (ScrCsrIdx, "Csr" ::= idx)).

  Definition mkCs2Scr (idx : Expr ty (Bit ScrIdxSz)) : Expr ty (TaggedUnion Cs2Source) :=
    UNION (Cs2Source, "ScrCsr" ::= UNION (ScrCsrIdx, "Scr" ::= idx)).
End Cs2Constructors.


(* ===========================================================================
   RISC-V & CHERIoT EXCEPTION CONSTANTS & INFO
   =========================================================================== *)

(* Standard RISC-V mcause values (DECIMAL) *)
Definition EXC_IllegalInst    := 2.
Definition EXC_Breakpoint     := 3.
Definition EXC_LoadAddrAlign  := 4.
Definition EXC_StoreAddrAlign := 6.
Definition EXC_ECallM         := 11.
Definition EXC_CHERI          := 28.

(* CHERI CheriCause values (HEXADECIMAL) *)
Definition CapEx_BoundsViolation           := 0x01.
Definition CapEx_TagViolation              := 0x02.
Definition CapEx_SealViolation             := 0x03.
Definition CapEx_TypeViolation             := 0x04.
Definition CapEx_PermitExecuteViolation    := 0x11.
Definition CapEx_PermitLoadViolation       := 0x12.
Definition CapEx_PermitStoreViolation      := 0x13.
Definition CapEx_PermitStoreCapViolation   := 0x15.
Definition CapEx_AccessSystemRegsViolation := 0x18.

Definition FetchException := STRUCT_TYPE {
  "tag"    :: Bool ;
  "seal"   :: Bool ;
  "perm"   :: Bool ;
  "bounds" :: Bool
}.

Definition DecodeException := STRUCT_TYPE {
  "illegal" :: Bool ;
  "asr"     :: Bool
}.

(* Explicit mtval struct *)
Definition CheriMtval := STRUCT_TYPE {
  "S"          :: Bool ;
  "RegIdx"     :: Bit RegIdxSz ;
  "CheriCause" :: Bit 5
}.

(* Top-level Exception Payload struct *)
Definition ExceptionInfo := STRUCT_TYPE {
  "mcause" :: Bit 5 ;
  "mtval"  :: CheriMtval
}.

Section ExceptionConstructors.
  Variable ty : Kind -> Type.

  Definition mkCheriMtval (s : Expr ty Bool) (regIdx : Expr ty (Bit RegIdxSz)) (cheriCause : Expr ty (Bit 5))
  : Expr ty CheriMtval :=
    STRUCT {
      "S"          ::= s ;
      "RegIdx"     ::= regIdx ;
      "CheriCause" ::= cheriCause
    }.

  Definition mkExceptionInfo (mcause : Expr ty (Bit 5)) (mtval : Expr ty CheriMtval)
  : Expr ty ExceptionInfo :=
    STRUCT {
      "mcause" ::= mcause ;
      "mtval"  ::= mtval
    }.
End ExceptionConstructors.

Section CsrHelpers.
  Variable ty : Kind -> Type.

  Definition getMstatusMIE (mstatus : Expr ty (Bit Xlen)) : Expr ty Bool :=
    (FromBit (Array (Z.to_nat Xlen) Bool) mstatus)$[3].

  Definition getMstatusMPIE (mstatus : Expr ty (Bit Xlen)) : Expr ty Bool :=
    (FromBit (Array (Z.to_nat Xlen) Bool) mstatus)$[7].

  Definition setMstatusMIE (mstatus : Expr ty (Bit Xlen)) (mie : Expr ty Bool) : Expr ty (Bit Xlen) :=
    ToBit ((FromBit (Array (Z.to_nat Xlen) Bool) mstatus)$[3 <- mie]).

  Definition setMstatusMPIE (mstatus : Expr ty (Bit Xlen)) (mpie : Expr ty Bool) : Expr ty (Bit Xlen) :=
    ToBit ((FromBit (Array (Z.to_nat Xlen) Bool) mstatus)$[7 <- mpie]).

  Definition encodeCheriMtval (mtval : Expr ty CheriMtval) : Expr ty (Bit Xlen) :=
    ZeroExtendTo Xlen (ToBit mtval).

  Definition encodeMcause (mcause : Expr ty (Bit 5)) : Expr ty (Bit Xlen) :=
    ZeroExtendTo Xlen mcause.
End CsrHelpers.

Section Decoders.
  Variable ty : Kind -> Type.

  (* Decodes 12-bit architectural CSR address to Option (Bit CsrIdxSz) *)
  Definition csrAddrDecoder (csrAddr : ty (Bit CsrAddrSz)) : Expr ty (Option (Bit CsrIdxSz)) :=
    caseDefault (k := Option (Bit CsrIdxSz))
      (map (fun '((_, addr, _, _), idx) =>
        (Eq #csrAddr $addr, mkSome (k := Bit CsrIdxSz) $idx)
      ) (enumerate CsrTable))
      (mkNone ty).

  (* Decodes 5-bit architectural SCR address to Option (Bit ScrIdxSz) *)
  Definition scrAddrDecoder (scrAddr : ty (Bit ScrAddrSz)) : Expr ty (Option (Bit ScrIdxSz)) :=
    caseDefault (k := Option (Bit ScrIdxSz))
      (map (fun '((_, addr), idx) =>
        (Eq #scrAddr $addr, mkSome (k := Bit ScrIdxSz) $idx)
      ) (enumerate ScrTable))
      (mkNone ty).

  Definition csrAllowReadNoAsrDecoder (csrAddr : ty (Bit CsrAddrSz)) : Expr ty Bool :=
    Or (map (fun '(_, addr, _, _) => Eq #csrAddr $addr)
            (filter (fun '(_, _, r, _) => r) CsrTable)).

  Definition csrAllowWriteNoAsrDecoder (csrAddr : ty (Bit CsrAddrSz)) : Expr ty Bool :=
    Or (map (fun '(_, addr, _, _) => Eq #csrAddr $addr)
            (filter (fun '(_, _, _, w) => w) CsrTable)).
End Decoders.

Definition CapPerms := STRUCT_TYPE { "U0" :: Bool ;
                                     "SE" :: Bool ;
                                     "US" :: Bool ;
                                     "EX" :: Bool ;
                                     "SR" :: Bool ;
                                     "MC" :: Bool ;
                                     "LD" :: Bool ;
                                     "SL" :: Bool ;
                                     "LM" :: Bool ;
                                     "SD" :: Bool ;
                                     "LG" :: Bool ;
                                     "GL" :: Bool }.

Definition ECap := STRUCT_TYPE { "R"     :: Bool;
                                 "perms" :: CapPerms;
                                 "oType" :: Bit CapOTypeSz;
                                 "cE"    :: Bit ExpSz;
                                 "top"   :: Bit (AddrSz + 2);
                                 "base"  :: Bit (AddrSz + 1) }.

Definition FullCapWithTag := STRUCT_TYPE { "tag"  :: Bool;
                                           "cap"  :: Cap;
                                           "addr" :: Addr }.

Definition FullECapWithTag := STRUCT_TYPE { "tag"  :: Bool;
                                            "ecap" :: ECap;
                                            "addr" :: Addr }.

(* ===========================================================================
   DEFERRED OPERATIONS (MemPayload, FenceOp)
   =========================================================================== *)

Definition LoadOp := STRUCT_TYPE {
  "isUnsigned" :: Bool ;
  "isLM"       :: Bool ;
  "isLG"       :: Bool
}.

Definition LoadOrStoreType := [
  ("Load"%string, LoadOp) ;
  ("Store"%string, FullCapWithTag)
].

Definition LoadOrStoreKind := TaggedUnion LoadOrStoreType.

Definition MemPayload := STRUCT_TYPE {
  "memSize" :: Bit LgLgNumBytesFullCapSz ;
  "memOp"   :: LoadOrStoreKind
}.

Definition FenceOp := STRUCT_TYPE {
  "RR" :: Bool ;
  "RW" :: Bool ;
  "WR" :: Bool ;
  "WW" :: Bool
}.

Definition DeferredUnionType := [
  ("Mem"%string,   MemPayload) ;
  ("Fence"%string, FenceOp)
].

Definition DeferredUnion := TaggedUnion DeferredUnionType.

Section DeferredConstructors.
  Variable ty : Kind -> Type.

  Definition mkFenceData (rr rw wr ww : ty Bool) : LetExpr ty (TaggedUnion DeferredUnionType) :=
    LetE fenceVal : FenceOp <- STRUCT {
      "RR" ::= #rr ;
      "RW" ::= #rw ;
      "WR" ::= #wr ;
      "WW" ::= #ww
    } ;
    RetE (UNION (DeferredUnionType, "Fence" ::= #fenceVal)).
End DeferredConstructors.

Section CapEncoding.
  Variable ty : Kind -> Type.

  Section CapPerms.
    Definition fixPerms (perms: ty CapPerms) : Expr ty CapPerms :=
      (ITE (And [##perms`"EX"; ##perms`"LD"; ##perms`"MC"])
         (##perms
            `{ "U0" <- ConstTBool false }
            `{ "SE" <- ConstTBool false }
            `{ "US" <- ConstTBool false }
            `{ "SL" <- ConstTBool false }
            `{ "SD" <- ConstTBool false })
         (ITE (And [##perms`"LD"; ##perms`"MC"; ##perms`"SD"])
            (##perms
               `{ "U0" <- ConstTBool false }
               `{ "SE" <- ConstTBool false }
               `{ "US" <- ConstTBool false }
               `{ "EX" <- ConstTBool false }
               `{ "SR" <- ConstTBool false })
            (ITE (And [##perms`"LD"; ##perms`"MC"])
               (##perms
                  `{ "U0" <- ConstTBool false }
                  `{ "SE" <- ConstTBool false }
                  `{ "US" <- ConstTBool false }
                  `{ "EX" <- ConstTBool false }
                  `{ "SR" <- ConstTBool false }
                  `{ "SL" <- ConstTBool false }
                  `{ "SD" <- ConstTBool false })
               (ITE (And [##perms`"SD"; ##perms`"MC"])
                  (##perms
                     `{ "U0" <- ConstTBool false }
                     `{ "SE" <- ConstTBool false }
                     `{ "US" <- ConstTBool false }
                     `{ "EX" <- ConstTBool false }
                     `{ "SR" <- ConstTBool false }
                     `{ "LD" <- ConstTBool false }
                     `{ "SL" <- ConstTBool false }
                     `{ "LM" <- ConstTBool false }
                     `{ "LG" <- ConstTBool false })
                  (ITE (Or [##perms`"LD"; ##perms`"SD"])
                     (##perms
                     `{ "U0" <- ConstTBool false }
                     `{ "SE" <- ConstTBool false }
                     `{ "US" <- ConstTBool false }
                     `{ "EX" <- ConstTBool false }
                     `{ "SR" <- ConstTBool false }
                     `{ "MC" <- ConstTBool false }
                     `{ "SL" <- ConstTBool false }
                     `{ "LM" <- ConstTBool false }
                     `{ "LG" <- ConstTBool false })
                     (##perms
                     `{ "EX" <- ConstTBool false }
                     `{ "SR" <- ConstTBool false }
                     `{ "MC" <- ConstTBool false }
                     `{ "LD" <- ConstTBool false }
                     `{ "SL" <- ConstTBool false }
                     `{ "LM" <- ConstTBool false }
                     `{ "SD" <- ConstTBool false }
                     `{ "LG" <- ConstTBool false })))))).

    Definition decodePerms (rawPerms: ty (Array CapPermSz Bool)) : LetExpr ty CapPerms :=
      ( LetE initPerms : CapPerms <- (ConstTDefK CapPerms) `{ "GL" <- #rawPerms $[5] };
        RetE (ITE (##rawPerms $[4])
                (ITE (##rawPerms $[3])
                   (##initPerms
                      `{ "MC" <- ConstTBool true }
                      `{ "LD" <- ConstTBool true }
                      `{ "SL" <- ##rawPerms $[2] }
                      `{ "LM" <- ##rawPerms $[1] }
                      `{ "SD" <- ConstTBool true }
                      `{ "LG" <- ##rawPerms $[0] })
                   (ITE (##rawPerms $[2])
                      (##initPerms
                         `{ "MC" <- ConstTBool true }
                         `{ "LD" <- ConstTBool true }
                         `{ "LM" <- ##rawPerms $[1] }
                         `{ "LG" <- ##rawPerms $[0] })
                      (ITE (Not (Or [##rawPerms $[1]; ##rawPerms $[0]]))
                         (##initPerms
                            `{ "MC" <- ConstTBool true }
                            `{ "SD" <- ConstTBool true })
                         (##initPerms
                            `{ "LD" <- ##rawPerms $[1] }
                            `{ "SD" <- ##rawPerms $[0] }))))
                (ITE (##rawPerms $[3])
                   (##initPerms
                      `{ "EX" <- ConstTBool true }
                      `{ "SR" <- ##rawPerms $[2] }
                      `{ "MC" <- ConstTBool true }
                      `{ "LD" <- ConstTBool true }
                      `{ "LM" <- ##rawPerms $[1] }
                      `{ "LG" <- ##rawPerms $[0] })
                   (##initPerms
                      `{ "U0" <- ##rawPerms $[2] }
                      `{ "SE" <- ##rawPerms $[1] }
                      `{ "US" <- ##rawPerms $[0] })))).

    Definition encodePerms (perms: ty CapPerms) : Expr ty (Array CapPermSz Bool) :=
      (ITE (And [##perms`"EX"; ##perms`"LD"; ##perms`"MC"])
         (ARRAY [##perms`"GL"; ConstBool false; ConstBool true; ##perms`"SR"; ##perms`"LM"; ##perms`"LG"])
         (ITE (And [##perms`"LD"; ##perms`"MC"; ##perms`"SD"])
            (ARRAY [##perms`"GL"; ConstBool true; ConstBool true; ##perms`"SL"; ##perms`"LM"; ##perms`"LG"])
            (ITE (And [##perms`"LD"; ##perms`"MC"])
               (ARRAY [##perms`"GL"; ConstBool true; ConstBool false; ConstBool true; ##perms`"LM";
                       ##perms`"LG"])
               (ITE (And [##perms`"SD"; ##perms`"MC"])
                  (ARRAY [##perms`"GL"; ConstBool true; ConstBool false; ConstBool false; ConstBool false;
                          ConstBool false])
                  (ITE (Or [##perms`"LD"; ##perms`"SD"])
                     (ARRAY [##perms`"GL"; ConstBool true; ConstBool false; ConstBool false; ##perms`"LD";
                             ##perms`"SD"])
                     (ARRAY [##perms`"GL"; ConstBool false; ConstBool false; ##perms`"U0"; ##perms`"SE";
                             ##perms`"US"])))))).

  End CapPerms.

  Section CapRelated.
    Definition get_E_from_cE (cE: ty (Bit ExpSz)) : Expr ty (Bit ExpSz) := ITE (isAllOnes #cE) $0 #cE.

    (* Mmsb is (cE != 0). This is a core property of our 5-bit cE hack *)
    Definition get_Mmsb_from_cE (cE: ty (Bit ExpSz)) : Expr ty (Bit 1) := ToBit (isNotZero #cE).

    (* Encode helpers *)
    Definition get_cT_from_T (T: ty (Bit CapTSz)) := TruncLsb 1 CapcTSz #T.

    (* We need to reconstruct Mmsb to get cE from E. Since M = T - B, Mmsb is T[8] ^ B[8] ^ (cT < cB) *)
    Definition get_Mmsb_from_T_B (T B: ty (Bit CapTSz)) : LetExpr ty (Bit 1) :=
      LetE cT <- get_cT_from_T T;
      LetE cB <- TruncLsb 1 CapcTSz #B;
      LetE Tmsb <- TruncMsb 1 CapcTSz #T;
      LetE Bmsb <- TruncMsb 1 CapcTSz #B;
      LetE carry_out <- ToBit (Slt #cT #cB);
      @RetE _ (Bit 1) (Xor [#Tmsb; #Bmsb; #carry_out]).

    Definition get_cE_from_E_T_B (E: ty (Bit ExpSz)) (T B: ty (Bit CapTSz)) : LetExpr ty (Bit ExpSz) :=
      LETE Mmsb <- get_Mmsb_from_T_B T B;
      @RetE _ (Bit ExpSz) (ITE (And [isZero #E; FromBit Bool #Mmsb]) (Const _ (Bit ExpSz) (Zmod.of_Z _ (-1))) #E).

    (* Decode helpers *)
    (* Reconstruct full 9-bit T from 8-bit cT, 9-bit B, and cE *)
    Definition get_T_from_cE_cT_B (cE: ty (Bit ExpSz)) (cT: ty (Bit CapcTSz)) (B: ty (Bit CapBSz)) : LetExpr ty (Bit CapTSz) :=
      LetE Mmsb <- get_Mmsb_from_cE cE;
      LetE cB <- TruncLsb 1 CapcTSz #B;
      LetE Bmsb <- TruncMsb 1 CapcTSz #B;
      LetE carry_out <- ToBit (Slt #cT #cB);
      LetE Tmsb <- Xor [#Bmsb; #Mmsb; #carry_out];
      @RetE _ (Bit CapTSz) ({< #Tmsb, #cT >}).

    Definition Emax := Eval compute in (Z.shiftl 1 ExpSz - CapcTSz).
    Definition get_ECorrected_from_E (E: ty (Bit ExpSz)) : Expr ty (Bit ExpSz) :=
      (ITE (Sge #E $Emax) $Emax #E).
    Definition get_E_from_ECorrected (ECorrected: ty (Bit ExpSz)): Expr ty (Bit ExpSz) := #ECorrected.
  End CapRelated.

  Section BaseTop.
    Definition BaseTop :=
      STRUCT_TYPE {
          "base"   :: Bit (AddrSz + 1);
          "top"    :: Bit (AddrSz + 2) }.

    Variable addr: ty Addr.
    Variable ECorrected: ty (Bit ExpSz).
    Variable T: ty (Bit CapTSz).
    Variable B: ty (Bit CapBSz).

    Definition get_base_top_from_ECorrected_T_B : LetExpr ty BaseTop :=
      ( LetE aMidTop: Addr <- Srl #addr #ECorrected;
        LetE aMid: Bit CapBSz <- TruncLsb (AddrSz - CapBSz) CapBSz #aMidTop;
        LetE aTop: Bit (AddrSz - CapBSz) <- TruncMsb (AddrSz - CapBSz) CapBSz #aMidTop;

        LetE aHi <- ZeroExtendTo (AddrSz - CapBSz) (ToBit (Slt #aMid #B));
        LetE aTopB <- ITE0 (isNotZero #aTop) (Sub #aTop #aHi);
        LetE base <- Sll (ZeroExtendTo (AddrSz + 1) ({< #aTopB, #B >})) #ECorrected;

        LetE tHi <- ZeroExtendTo (AddrSz - CapBSz) (ToBit (Slt #T #B));
        LetE aTopT <- Add [#aTopB; #tHi];
        LetE top <- Sll (ZeroExtendTo (AddrSz + 2) ({< #aTopT, #T >})) #ECorrected;

        @RetE _ BaseTop (STRUCT {
                                "base"   ::= #base;
                                "top"    ::= #top })).
  End BaseTop.
End CapEncoding.

Definition isSealed ty (ecap: ty ECap) : Expr ty Bool := isNotZero (##ecap`"oType").
Definition isCallSentry ty (oType: ty (Bit CapOTypeSz)) : Expr ty Bool :=
  Or [ Eq #oType $CallSentryIh; Eq #oType $CallSentryId; Eq #oType $CallSentryIe ].
Definition isRetSentry ty (oType: ty (Bit CapOTypeSz)) : Expr ty Bool :=
  Or [ Eq #oType $RetSentryId; Eq #oType $RetSentryIe ].
Definition isSentry ty (oType: ty (Bit CapOTypeSz)) : Expr ty Bool :=
  Or [ isCallSentry oType; isRetSentry oType ].
Definition isSentryIe ty (oType: ty (Bit CapOTypeSz)) : Expr ty Bool :=
  Or [ Eq #oType $CallSentryIe; Eq #oType $RetSentryIe ].
Definition isSentryId ty (oType: ty (Bit CapOTypeSz)) : Expr ty Bool :=
  Or [ Eq #oType $CallSentryId; Eq #oType $RetSentryId ].
Definition isSentryIh ty (oType: ty (Bit CapOTypeSz)) : Expr ty Bool :=
  Eq #oType $CallSentryIh.

(* ========================================================================= *)
(* DataTypes                                                                 *)
(* ========================================================================= *)

Definition DecodeOut := STRUCT_TYPE {
  "instGroup" :: InstGroup ;
  "cs1Idx"    :: Bit RegIdxSzReal ;
  "cs2Idx"    :: TaggedUnion Cs2Source ;
  "writesCd"  :: Bool ;
  "instBits"  :: Inst ;
  "decodeExc" :: DecodeException
}.

Definition RegReadIn := STRUCT_TYPE {
  "pcc"         :: FullECapWithTag ;
  "decodeOut"   :: DecodeOut ;
  "fetchExc"    :: FetchException ;
  "isFenceIAck" :: Bool
}.

Definition AluControl := STRUCT_TYPE {
  (* AdderBeforeBoundsCheck_base_isPccAddrNotCs1Addr = BranchOrCjalOrAuiPcc *)
  (* AddCapBSz_baseExp_isPccExpNotCs1Exp = BranchOrCjalOrAuiPcc *)
  (* AdderBeforeRepCheck_base_isPccBaseNotCs1Base = BranchOrCjalOrAuiPcc *)
  (* ComparatorBase_base_pccBase = BranchOrCjalOrAuiPcc *)
  (* AddrBoundsCheck_tag_isPccTagNotCs1Tag = BranchOrCjalOrAuiPcc *)
  (* AdderBeforeBoundsCheck_offset_bimm12 = Branch *)
  (* AdderBeforeBoundsCheck_offset_jimm20 = Cjal *)
  "AdderBeforeBoundsCheck_offset_uimm20_11" :: Bool ;
  "AdderBeforeBoundsCheck_offset_cs2Addr" :: Bool ;
  (* AdderBeforeBoundsCheck_offset_zimm12 = Bounds_isImm *)
  (* "AdderBeforeBoundsCheck_offset_simm12" :: Bool ; (* default option *) *)
  "AdderToOutput_base_pccAddr" :: Bool ;
  (* AdderToOutput_base_cs1Addr = AddSub (* default option *) *)
  (* AdderToOutput_base_cs1Top = CGetLen *)
  "AdderToOutput_offset_const2" :: Bool ;
  (* "AdderToOutput_offset_const4" :: Bool ; (* default option *) *)
  "AdderToOutput_offset_cs2Addr" :: Bool ;
  "AdderToOutput_offset_simm12" :: Bool ;
  (* AdderToOutput_offset_cs1Base = CGetLen *)
  "AdderToOutput_isSub" :: Bool ;
  "ComparatorGeneral_op2_isCs2AddrNotSimm12" :: Bool ;
  (* ComparatorGeneral_isUnsigned = isUnsigned *)
  "ComparatorGeneral_checkLt" :: Bool ;
  "ComparatorGeneral_checkEq" :: Bool ;
  "ComparatorGeneral_invertRes" :: Bool ;
  "Logical_op2_isCs2AddrNotSimm12" :: Bool ;
  (* SealerUnsealer_isUnseal = Unseal *)
  "Bounds_reqLimit_cs2Addr" :: Bool ;
  (* Bounds_reqLimit_zimm12 = Bounds_isImm (* default option *) *)
  "Bounds_reqLimit_cs1Addr" :: Bool ;
  "Bounds_isRoundDown" :: Bool ;
  "Bounds_isExact" :: Bool ;
  "Bounds_isImm" :: Bool ;
  (* Shifter_data_isCs1AddrNotConst1 = Shift *)
  "Shifter_shamt_cs2Addr" :: Bool ;
  (* "Shifter_shamt_shamt" :: Bool ; (* default option *) *)
  (* Shifter_shamt_AddCapBSz = BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr *)
  "Shifter_isArith" :: Bool ;
  "Shifter_isRight" :: Bool ;
  "ComparatorTopOrRep_addr_AdderBeforeBoundsCheck" :: Bool ;
  (* "ComparatorTopOrRep_addr_cs1Addr" :: Bool ; (* default option *) *)
  (* ComparatorTopOrRep_addr_cs2Addr = SealOrSetAddr *)
  (* ComparatorTopOrRep_addr_cs1OType = Unseal *)
  (* ComparatorTopOrRep_addr_cs1Top = CTestSubset *)
  (* "ComparatorTopOrRep_topRep_cs1Top" :: Bool ; (* default option *) *)
  (* ComparatorTopOrRep_topRep_AdderBeforeRepCheck = BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr *)
  (* ComparatorTopOrRep_topRep_cs2Top = SealOrUnsealOrSubset *)
  (* ComparatorBase_base_cs2Base = SealOrUnsealOrSubset *)
  "ComparatorTopOrRep_checkLte" :: Bool ;
  "ComparatorBase_addr_AdderBeforeBoundsCheck" :: Bool ;
  (* ComparatorBase_addr_cs2Addr = SealOrSetAddr *)
  (* ComparatorBase_addr_cs1Addr = CSetBounds (* default option *) *)
  (* ComparatorBase_addr_cs1OType = Unseal *)
  (* ComparatorBase_addr_cs1Base = CTestSubset *)
  (* "ComparatorBase_base_cs1Base" :: Bool ; (* default option *) *)

  (* EncodeCap_ecap_isCs2EcapNotCs1Ecap = Store *)
  (* Reg_tag_pccTag = Cjal *)
  "Reg_tag_cs1Tag" :: Bool ;
  (* Reg_tag_cs2Tag = Scr *)
  "Reg_tag_AddrBoundsCheck" :: Bool ;
  (* Reg_tag_BoundsExact = CSetBounds *)
  (* Reg_tag_CAndPerm = CAndPerm *)
  (* Reg_tag_SealerUnsealer = SealOrUnseal *)
  "Reg_ecap_pccEcap" :: Bool ;
  "Reg_ecap_cs1Ecap" :: Bool ;
  (* Reg_ecap_cs2Ecap = Scr *)
  (* Reg_ecap_cs2Addr = CSetHigh *)
  (* Reg_ecap_CAndPerm = CAndPerm *)
  (* Reg_ecap_Bounds = CSetBounds *)
  (* Reg_ecap_SealerUnsealer = SealOrUnseal *)
  (* Reg_addr_uimm20 = Lui *)
  "Reg_addr_AdderBeforeBoundsCheck" :: Bool ;
  (* Reg_addr_ComparatorGeneralLt = Slt *)
  (* Reg_addr_Shifter = Shift *)
  (* Reg_addr_Logical = Logical *)
  "Reg_addr_AdderToOutput" :: Bool ;
  "Reg_addr_Saturater" :: Bool ;
  (* Reg_addr_CGetPerm = CGetPerm *)
  (* Reg_addr_CGetType = CGetType *)
  (* Reg_addr_CGetTag = CGetTag *)
  (* Reg_addr_CGetAddr = CGetAddr *)
  (* Reg_addr_CGetHigh = CGetHigh *)
  "Reg_addr_cs2Addr" :: Bool ;
  "Reg_addr_zimm5" :: Bool ;
  "Reg_addr_cs1Addr" :: Bool ;
  (* Reg_addr_CAndPerm = CAndPerm *)
  (* Reg_addr_SealerUnsealer = SealOrUnseal *)
  (* Reg_addr_BoundsBase = CSetBounds *)
  (* Reg_addr_BoundsCram = Cram *)
  (* Reg_addr_BoundsCrrl = Crrl *)
  (* Reg_addr_CapSubset = CTestSubset *)
  (* Reg_addr_CapEq = CSetEqual *)
  "ECall" :: Bool ;
  "EBreak" :: Bool ;
  "Load" :: Bool ;
  "Store" :: Bool ;
  "Fence" :: Bool ;
  "Branch" :: Bool ;
  "Cjal" :: Bool ;
  "AddSub" :: Bool ;
  "CGetLen" :: Bool ;
  "Unseal" :: Bool ;
  "Shift" :: Bool ;
  "CTestSubset" :: Bool ;
  "CSetBounds" :: Bool ;
  "Mret" :: Bool ;
  "Cjalr" :: Bool ;
  "Scr" :: Bool ;
  "CAndPerm" :: Bool ;
  "isUnsigned" :: Bool ;
  "Lui" :: Bool ;
  "Slt" :: Bool ;
  "Logical" :: Bool ;
  "CGetPerm" :: Bool ;
  "CGetType" :: Bool ;
  "CGetBase" :: Bool ;
  "CGetTag" :: Bool ;
  "CGetAddr" :: Bool ;
  "CGetHigh" :: Bool ;
  "CGetTop" :: Bool ;
  "Cram" :: Bool ;
  "Crrl" :: Bool ;
  "CSetEqual" :: Bool ;
  "CSetHigh" :: Bool ;
  "BranchOrCjalOrAuiPcc" :: Bool ;
  "BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr" :: Bool ;
  "SealOrSetAddr" :: Bool ;
  "SealOrUnsealOrSubset" :: Bool ;
  "SealOrUnseal" :: Bool
}.

Definition AluIn := STRUCT_TYPE {
  "cs2Idx"              :: TaggedUnion Cs2Source ;
  "writesCd"            :: Bool ;
  "inst"                :: Inst ;
  "decodeExc"           :: DecodeException ;
  "fetchExc"            :: FetchException ;
  "pcc"                 :: FullECapWithTag ;
  "cs1"                 :: FullECapWithTag ;
  "cs2"                 :: FullECapWithTag ;
  "currInterruptStatus" :: Bool ;
  "aluControl"          :: AluControl ;
  "isFenceIAck"         :: Bool
}.

Definition AluInInstGroup := STRUCT_TYPE {
  "cs2Idx"              :: TaggedUnion Cs2Source ;
  "writesCd"            :: Bool ;
  "inst"                :: Inst ;
  "decodeExc"           :: DecodeException ;
  "fetchExc"            :: FetchException ;
  "pcc"                 :: FullECapWithTag ;
  "cs1"                 :: FullECapWithTag ;
  "cs2"                 :: FullECapWithTag ;
  "currInterruptStatus" :: Bool ;
  "instGroup"           :: InstGroup ;
  "isFenceIAck"         :: Bool
}.

Definition ControlFlowAddrOnlyOpType := [
  ("Branch"%string, Bool) ;
  ("Cjal"%string,   Bit 0)
].
Definition ControlFlowAddrOnlyOp := TaggedUnion ControlFlowAddrOnlyOpType.

Definition ControlFlowAddrECapOpType := [
  ("Cjalr"%string,  Bool) ;
  ("Mret"%string,   Bit 0)
].
Definition ControlFlowAddrECapOp := TaggedUnion ControlFlowAddrECapOpType.

Definition CfOpType := [
     ("ControlFlowAddrOnly"%string, ControlFlowAddrOnlyOp) ;
     ("ControlFlowAddrECap"%string, ControlFlowAddrECapOp)
].
Definition CfOp := TaggedUnion CfOpType.

Definition CfPayload := STRUCT_TYPE {
  "NewPcc" :: FullECapWithTag ;
  "CfOp"   :: CfOp
}.

Definition ScrCsrPayload := STRUCT_TYPE {
  "SpecialDest"  :: TaggedUnion ScrCsrIdx ;
  "SpecialValue" :: FullECapWithTag
}.

Definition AluOut := STRUCT_TYPE {
  "isComp"      :: Bool ;
  "dstIdx"      :: Bit RegIdxSz ;
  "dstValue"    :: FullECapWithTag ;
  "Exception"   :: Option ExceptionInfo ;
  "Deferred"    :: Option DeferredUnion ;
  "ControlFlow" :: Option CfPayload ;
  "ScrCsr"      :: Option ScrCsrPayload ;
  "isFenceI"    :: Bool ;
  "isFenceIAck" :: Bool
}.

Definition NormalFenceIType := [
  ("Normal"%string, Bit 0) ;
  ("FenceI"%string, Bit 0)
].
Definition NormalFenceIUnion := TaggedUnion NormalFenceIType.

Definition CfScrCsrType := [
  ("ControlFlow"%string, CfPayload) ;
  ("ScrCsr"%string,      ScrCsrPayload)
].
Definition CfScrCsrUnion := TaggedUnion CfScrCsrType.

Definition NotDeferredUnionType := [
  ("NormalFenceI"%string, NormalFenceIUnion) ;
  ("CfScrCsr"%string,     CfScrCsrUnion)
].
Definition NotDeferredUnion := TaggedUnion NotDeferredUnionType.

Definition NoExceptionUnionType := [
  ("Deferred"%string,    DeferredUnion) ;
  ("NotDeferred"%string, NotDeferredUnion)
].
Definition NoExceptionUnion := TaggedUnion NoExceptionUnionType.

Definition AluOpUnionType := [
  ("Exception"%string,   ExceptionInfo) ;
  ("NoException"%string, NoExceptionUnion)
].
Definition AluOpUnion := TaggedUnion AluOpUnionType.

Definition AluOutUnion := STRUCT_TYPE {
  "isComp"      :: Bool ;
  "dstIdx"      :: Bit RegIdxSz ;
  "dstValue"    :: FullECapWithTag ;
  "Op"          :: AluOpUnion ;
  "isFenceIAck" :: Bool
}.

Definition gprLeaves : list (Tree Elem) :=
  map (fun '(_, idx) =>
    Leaf ("gpr_" ++ hex_string_of_Z idx)%string
         (EReg (Build_Reg FullECapWithTag (Some (getDefault _))))
  ) (enumerate (repeat tt (Z.to_nat NumRegs))).

Definition scrLeaves : list (Tree Elem) :=
  map (fun '(name, _) =>
    Leaf name (EReg (Build_Reg FullECapWithTag (Some (getDefault _))))
  ) ScrTable.

Definition csrLeaves : list (Tree Elem) :=
  map (fun '(name, _, _, _) =>
    Leaf name (EReg (Build_Reg (Bit Xlen) (Some (getDefault _))))
  ) CsrTable.

Definition rfTree : Tree Elem :=
  Node "rf" [
    Node "gprs" gprLeaves ;
    Node "scrs" scrLeaves ;
    Node "csrs" csrLeaves ;
    Leaf "waitForFenceIAck" (EReg (Build_Reg Bool (Some false)))
  ].

Definition gprPaths : list (RegPath rfTree) :=
  map (embedRegPath (getNodePath rfTree "rf.gprs"))
      (getTreeRegPaths (getNode (getNodePath rfTree "rf.gprs"))).

Definition scrPaths : list (RegPath rfTree) :=
  map (embedRegPath (getNodePath rfTree "rf.scrs"))
      (getTreeRegPaths (getNode (getNodePath rfTree "rf.scrs"))).

Definition csrPaths : list (RegPath rfTree) :=
  map (embedRegPath (getNodePath rfTree "rf.csrs"))
      (getTreeRegPaths (getNode (getNodePath rfTree "rf.csrs"))).

Definition gprPathsWithKind : list (RegOfKind (t:=rfTree) FullECapWithTag) :=
  map (embedRegOfKind (getNodePath rfTree "rf.gprs"))
      (getTreeRegsOfKind FullECapWithTag (getNode (getNodePath rfTree "rf.gprs"))).

Definition scrPathsWithKind : list (RegOfKind (t:=rfTree) FullECapWithTag) :=
  map (embedRegOfKind (getNodePath rfTree "rf.scrs"))
      (getTreeRegsOfKind FullECapWithTag (getNode (getNodePath rfTree "rf.scrs"))).

Definition csrPathsWithKind : list (RegOfKind (t:=rfTree) (Bit Xlen)) :=
  map (embedRegOfKind (getNodePath rfTree "rf.csrs"))
      (getTreeRegsOfKind (Bit Xlen) (getNode (getNodePath rfTree "rf.csrs"))).

Definition DeferredReq := STRUCT_TYPE {
  "dstIdx" :: Bit RegIdxSz ;
  "addr"   :: Addr ;
  "op"     :: DeferredUnion
}.

Definition ExecuteOut := STRUCT_TYPE {
  "deferredReq" :: Option DeferredReq ;
  "isFenceIRq"  :: Bool
}.

Definition PendingLoad := STRUCT_TYPE {
  "dstIdx"     :: Bit RegIdxSz ;
  "byteOffset" :: Bit LgNumBytesFullCapSz ;
  "memSize"    :: Bit LgLgNumBytesFullCapSz ;
  "isUnsigned" :: Bool
}.

Definition PendingRev := STRUCT_TYPE {
  "dstIdx" :: Bit RegIdxSz ;
  "capVal" :: FullECapWithTag
}.

Definition deferredTree (capacity : nat) : Tree Elem :=
  Node "deferred" [
    Node "inputBuf" [ fifoTree capacity DeferredReq ] ;
    Node "loadBuf"  [ fifoTree capacity PendingLoad ] ;
    Node "revBuf"   [ fifoTree capacity PendingRev ]
  ].

Definition coreTree (memTree : Tree Elem) (capacity : nat) : Tree Elem :=
  Node "core" [
    rfTree ;
    Node "mem" [ memTree ] ;
    deferredTree capacity
  ].
