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

From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope guru_scope.

Definition Xlen := 32.
Definition InstSz     := 32.
Definition CompInstSz := 16.

Definition CapOTypeSz := 3.
Definition RegIdxSz   := 5.
Definition Cra       := 1.

Definition LgXlen   := Eval compute in Z.log2_up Xlen.
Definition Data     := Eval compute in Bit Xlen.
Definition AddrSz   := Eval compute in Xlen.
Definition Addr     := Eval compute in Bit AddrSz.
Definition Inst     := Eval compute in Bit InstSz.
Definition LgAddrSz := Eval compute in Z.log2_up AddrSz.
Definition ExpSz    := Eval compute in LgAddrSz.
Definition NumBytesXlen := Eval compute in (Xlen / 8).
Definition FullCapSz := 64.
Definition NumBytesFullCapSz := Eval compute in (FullCapSz / 8).
Definition LgNumBytesFullCapSz := Eval compute in Z.log2_up NumBytesFullCapSz.
Definition LgLgNumBytesFullCapSz := Eval compute in Z.log2_up (LgNumBytesFullCapSz + 1).

Definition isCompressed ty (inst: ty Inst) : Expr ty (Bit 2) := TruncLsb (InstSz-2) 2 #inst.
Definition getCd ty (inst: ty Inst) : Expr ty (Bit RegIdxSz) := #inst`[11:7].
Definition getCs1 ty (inst: ty Inst) : Expr ty (Bit RegIdxSz) := #inst`[19:15].
Definition getScr ty (inst: ty Inst) : Expr ty (Bit RegIdxSz) := #inst`[24:20].

Definition CallSentryIh := 1.
Definition CallSentryId := 2.
Definition CallSentryIe := 3.
Definition RetSentryId  := 4.
Definition RetSentryIe  := 5.

Definition RegIdxSzReal := 4.

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
  "Shifter" :: Bool ;
  "AdderBeforeRepCheck" :: Bool ;
  "ComparatorTopOrRep" :: Bool ;
  "ComparatorBase" :: Bool ;
  "AddrBoundsCheck" :: Bool ;
  "CapSubset" :: Bool ;
  "CapEq" :: Bool ;
  "ScrSanitizer" :: Bool ;
  "Deferred" :: Bool ;
  "Exception" :: Bool ;
  "NewPcc" :: Bool
}.

(* ===========================================================================
   CSR & SCR DEFINITIONS, TABLES, MAPPINGS, AND DECODERS
   =========================================================================== *)

(* CSR Table: List of 5-tuples ("name", 12-bit address, mapped index, allowReadNoAsr, allowWriteNoAsr) *)
Definition CsrTable := [
  ("mcycle"%string,    0xc00, 0,  true,  false) ;
  ("mcycleh"%string,   0xc80, 1,  true,  false) ;
  ("mtime"%string,     0xc01, 2,  true,  false) ;
  ("mtimeh"%string,    0xc81, 3,  true,  false) ;
  ("minstret"%string,  0xc02, 4,  true,  false) ;
  ("minstreth"%string, 0xc82, 5,  true,  false) ;
  ("mstatus"%string,   0x300, 6,  false, false) ;
  ("mie"%string,       0x304, 7,  false, false) ;
  ("mcause"%string,    0x342, 8,  false, false) ;
  ("mtval"%string,     0x343, 9,  false, false) ;
  ("mshwm"%string,     0xbc1, 10, true,  true) ;
  ("mshwmb"%string,    0xbc2, 11, true,  true)
].

(* Lookup Functions by Name for CsrTable *)
Fixpoint getCsrEntryFromList (s : string) (table : list (string * Z * Z * bool * bool)) :=
  match table with
  | [] => None
  | (name, addr, idx, r_no_asr, w_no_asr) :: rest =>
      if String.eqb s name then Some (addr, idx, r_no_asr, w_no_asr)
      else getCsrEntryFromList s rest
  end.

Definition getCsrEntryByName (s : string) := getCsrEntryFromList s CsrTable.

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

(* SCR Table: List of 3-tuples ("name", 5-bit address, 5-bit mapped index starting at 0) *)
Definition ScrTable := [
  ("MePrevPcc"%string, 27, 0) ;
  ("Mtcc"%string,      28, 1) ;
  ("Mtdc"%string,      29, 2) ;
  ("Mscratchc"%string, 30, 3) ;
  ("MePcc"%string,     31, 4)
].

(* Lookup Functions by Name for ScrTable *)
Fixpoint getScrEntryFromList (s : string) (table : list (string * Z * Z)) :=
  match table with
  | [] => None
  | (name, addr, idx) :: rest =>
      if String.eqb s name then Some (addr, idx)
      else getScrEntryFromList s rest
  end.

Definition getScrEntryByName (s : string) := getScrEntryFromList s ScrTable.

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

(* TaggedUnion with 3 distinct sources: Reg (4-bit GPR), Csr (CsrIdxSz CSR), Scr (ScrIdxSz SCR) *)
Definition Cs2Source := [
  ("Reg"%string, Bit RegIdxSzReal) ;
  ("Scr"%string, Bit ScrIdxSz) ;
  ("Csr"%string, Bit CsrIdxSz)
].

Section Cs2Constructors.
  Variable ty : Kind -> Type.
  Definition mkCs2Reg (idx : Expr ty (Bit RegIdxSzReal)) : Expr ty (TaggedUnion Cs2Source) :=
    UNION (Cs2Source, "Reg" ::= idx).

  Definition mkCs2Csr (idx : Expr ty (Bit CsrIdxSz)) : Expr ty (TaggedUnion Cs2Source) :=
    UNION (Cs2Source, "Csr" ::= idx).

  Definition mkCs2Scr (idx : Expr ty (Bit ScrIdxSz)) : Expr ty (TaggedUnion Cs2Source) :=
    UNION (Cs2Source, "Scr" ::= idx).
End Cs2Constructors.

(* ===========================================================================
   DEFERRED OPERATIONS (MemOp, FenceOp, MretOp)
   =========================================================================== *)

Definition MemOp := STRUCT_TYPE {
  "isStore"    :: Bool ;
  "memSize"    :: Bit LgLgNumBytesFullCapSz ;
  "isUnsigned" :: Bool ;
  "isLM"       :: Bool ;
  "isLG"       :: Bool
}.

Definition FenceOp := STRUCT_TYPE {
  "isFenceI" :: Bool ;
  "RR"       :: Bool ;
  "RW"       :: Bool ;
  "WR"       :: Bool ;
  "WW"       :: Bool
}.

Definition DeferredOpType := [
  ("MemOp"%string, MemOp) ;
  ("FenceOp"%string, FenceOp)
].

Definition DeferredOp := TaggedUnion DeferredOpType.

Section DeferredConstructors.
  Variable ty : Kind -> Type.

  Definition mkFenceI : LetExpr ty (TaggedUnion DeferredOpType) :=
    LetE fenceVal : FenceOp <- STRUCT {
      "isFenceI" ::= ConstTBool true ;
      "RR"       ::= ConstTBool false ;
      "RW"       ::= ConstTBool false ;
      "WR"       ::= ConstTBool false ;
      "WW"       ::= ConstTBool false
    } ;
    RetE (UNION (DeferredOpType, "FenceOp" ::= #fenceVal)).

  Definition mkFenceData (rr rw wr ww : ty Bool) : LetExpr ty (TaggedUnion DeferredOpType) :=
    LetE fenceVal : FenceOp <- STRUCT {
      "isFenceI" ::= ConstTBool false ;
      "RR"       ::= #rr ;
      "RW"       ::= #rw ;
      "WR"       ::= #wr ;
      "WW"       ::= #ww
    } ;
    RetE (UNION (DeferredOpType, "FenceOp" ::= #fenceVal)).
End DeferredConstructors.

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

Section Decoders.
  Variable ty : Kind -> Type.

  (* Decodes 12-bit architectural CSR address to Option (Bit CsrIdxSz) *)
  Definition csrAddrDecoder (csrAddr : ty (Bit 12)) : Expr ty (Option (Bit CsrIdxSz)) :=
    caseDefault (k := Option (Bit CsrIdxSz)) [
      (Eq #csrAddr $0xc00, mkSome $0) ;
      (Eq #csrAddr $0xc80, mkSome $1) ;
      (Eq #csrAddr $0xc01, mkSome $2) ;
      (Eq #csrAddr $0xc81, mkSome $3) ;
      (Eq #csrAddr $0xc02, mkSome $4) ;
      (Eq #csrAddr $0xc82, mkSome $5) ;
      (Eq #csrAddr $0x300, mkSome $6) ;
      (Eq #csrAddr $0x304, mkSome $7) ;
      (Eq #csrAddr $0x342, mkSome $8) ;
      (Eq #csrAddr $0x343, mkSome $9) ;
      (Eq #csrAddr $0xbc1, mkSome $10) ;
      (Eq #csrAddr $0xbc2, mkSome $11)
    ] (mkNone ty).

  (* Decodes 5-bit architectural SCR address to Option (Bit ScrIdxSz) *)
  Definition scrAddrDecoder (scrAddr : ty (Bit RegIdxSz)) : Expr ty (Option (Bit ScrIdxSz)) :=
    caseDefault (k := Option (Bit ScrIdxSz)) [
      (Eq #scrAddr $27, mkSome $0) ;
      (Eq #scrAddr $28, mkSome $1) ;
      (Eq #scrAddr $29, mkSome $2) ;
      (Eq #scrAddr $30, mkSome $3) ;
      (Eq #scrAddr $31, mkSome $4)
    ] (mkNone ty).

  Definition csrAllowReadNoAsrDecoder (csrAddr : ty (Bit 12)) : Expr ty Bool :=
    Or [ Eq #csrAddr $0xc00 ; Eq #csrAddr $0xc80 ; Eq #csrAddr $0xc01 ; Eq #csrAddr $0xc81 ;
         Eq #csrAddr $0xc02 ; Eq #csrAddr $0xc82 ; Eq #csrAddr $0xbc1 ; Eq #csrAddr $0xbc2 ].

  Definition csrAllowWriteNoAsrDecoder (csrAddr : ty (Bit 12)) : Expr ty Bool :=
    Or [ Eq #csrAddr $0xbc1 ; Eq #csrAddr $0xbc2 ].
End Decoders.

Definition CapPermSz := 6%nat.
Definition CapcMSz := 8.
Definition CapBSz := Eval compute in (CapcMSz + 1).
Definition CapMSz := Eval compute in CapBSz.

Definition Cap : Kind := STRUCT_TYPE {
                             "R" :: Bool;
                             "p" :: Array CapPermSz Bool;
                             "oType" :: Bit CapOTypeSz;
                             "cE" :: Bit ExpSz;
                             "cM" :: Bit CapcMSz;
                             "B" :: Bit CapBSz }.

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
                                 "E"     :: Bit ExpSz;
                                 "top"   :: Bit (AddrSz + 1);
                                 "base"  :: Bit (AddrSz + 1) }.

Definition FullECapWithTag := STRUCT_TYPE { "tag" :: Bool;
                                            "ecap" :: ECap;
                                            "addr" :: Addr }.



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
    Definition get_Mmsb_from_cE (cE: ty (Bit ExpSz)) : Expr ty (Bit 1) := ToBit (isNotZero #cE).
    Definition get_M_from_cE_cM (cE: ty (Bit ExpSz)) (cM: ty (Bit CapcMSz)) : Expr ty (Bit CapMSz) :=
      ({< get_Mmsb_from_cE cE, #cM >}).

    Definition get_Mmsb_from_M (M: ty (Bit CapMSz)) := TruncMsb 1 CapcMSz #M.
    Definition get_cM_from_M (M: ty (Bit CapMSz)) := TruncLsb 1 CapcMSz #M.
    Definition get_cE_from_E_M (E: ty (Bit ExpSz)) (M: ty (Bit CapMSz)) :=
      ITE (And [isZero #E; FromBit Bool (get_Mmsb_from_M M)]) (Const _ (Bit ExpSz) (Zmod.of_Z _ (-1))) #E.
    Definition Emax := Eval compute in (Z.shiftl 1 ExpSz - CapcMSz).
    Definition get_ECorrected_from_E (E: ty (Bit ExpSz)) : Expr ty (Bit ExpSz) :=
      (ITE (Sge #E $Emax) $Emax #E).
    Definition get_E_from_ECorrected (ECorrected: ty (Bit ExpSz)): Expr ty (Bit ExpSz) := #ECorrected.
  End CapRelated.

  Section BaseLength.
    Definition BaseLength :=
      STRUCT_TYPE {
          "base"   :: Bit (AddrSz + 1);
          "length" :: Bit (AddrSz + 1) }.

    Variable addr: ty Addr.
    Variable ECorrected: ty (Bit ExpSz).
    Variable M: ty (Bit CapMSz).
    Variable B: ty (Bit CapBSz).

    Definition get_base_length_from_ECorrected_M_B : LetExpr ty BaseLength :=
      ( LetE aMidTop: Addr <- Srl #addr #ECorrected;
        LetE aMid: Bit CapBSz <- TruncLsb (AddrSz - CapBSz) CapBSz #aMidTop;
        LetE aTop: Bit (AddrSz - CapBSz) <- TruncMsb (AddrSz - CapBSz) CapBSz #aMidTop;
        LetE aHi <- ZeroExtendTo (AddrSz - CapBSz) (ToBit (Slt #aMid #B));
        LetE base <- Sll (ZeroExtendTo (AddrSz + 1) ({< Sub #aTop #aHi, #B >})) #ECorrected;
        LetE length <- Sll (ZeroExtendTo (AddrSz + 1) #M) #ECorrected;
        @RetE _ BaseLength (STRUCT {
                                "base"   ::= #base;
                                "length" ::= #length })).
  End BaseLength.

  Section EncodeCap.
    Variable ecap: ty ECap.

    Definition encodeCap: LetExpr ty Cap :=
      ( LetE decodedPerms <- #ecap`"perms";
        LetE perms <- encodePerms decodedPerms;
        LetE E <- #ecap`"E";
        LetE ECorrected <- get_ECorrected_from_E E;
        LetE B <- TruncLsb (AddrSz + 1 - CapBSz) CapBSz (Sll (#ecap`"base") #ECorrected);
        LetE T <- TruncLsb (AddrSz + 1 - CapBSz) CapBSz (Sll (#ecap`"top") #ECorrected);
        LetE M <- Sub #T #B;
        @RetE _ Cap (STRUCT {
                         "R" ::= #ecap`"R";
                         "p" ::= #perms;
                         "oType" ::= #ecap`"oType";
                         "cE" ::= get_cE_from_E_M E M;
                         "cM" ::= get_cM_from_M M;
                         "B" ::= #B })).
  End EncodeCap.

  Section DecodeCap.
    Variable cap: ty Cap.
    Variable addr: ty Addr.

    Definition decodeCap: LetExpr ty ECap :=
      ( LetE encodedPerms <- #cap`"p";
        LETE perms <- decodePerms encodedPerms;
        LetE cap_cE <- #cap`"cE";
        LetE cap_cM <- #cap`"cM";
        LetE cap_B <- #cap`"B";
        LetE E <- get_E_from_cE cap_cE;
        LetE ECorrected <- get_ECorrected_from_E E;
        LetE M <- get_M_from_cE_cM cap_cE cap_cM;
        LETE base_length <- get_base_length_from_ECorrected_M_B addr ECorrected M cap_B;
        LetE base <- #base_length`"base";
        LetE length <- #base_length`"length";
        @RetE _ ECap (STRUCT {
                          "R" ::= ##cap`"R";
                          "perms" ::= #perms;
                          "oType" ::= #cap`"oType";
                          "E" ::= #E;
                          "top" ::= Add [#base; #length];
                          "base" ::= #base })).
  End DecodeCap.
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
