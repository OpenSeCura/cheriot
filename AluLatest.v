
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

(*
===============================================================================
                       CHERIOT ALU SPECIFICATION
===============================================================================

1. INSTRUCTION GROUPS
-------------------------------------------------------------------------------
Immediate Formats:
  * simm12          : 12-bit sign-extended immediate (arithmetic, loads/stores & CJALR offsets)
  * zimm12          : 12-bit zero-extended immediate (CSetBoundsImm)
  * uimm20          : 20-bit sign-extended upper immediate shifted left 12 bits (LUI)
  * uimm20_11       : 20-bit sign-extended upper immediate shifted left 11 bits (CHERIoT AUIPCC / AUICGP format)
  * bimm12          : 12-bit sign-extended branch offset (weird concatenation for branches with LSB 0)
  * jimm20          : 20-bit sign-extended jump offset (another weird concatenation for JAL with LSB 0)
  * shamt           : 5-bit shift amount
  * zimm5           : 5-bit zero-extended immediate (CSR manipulations)

Miscellaneous:
  * LoadOp          : generic load modifier (determines size and sign/zero extension)
  * interruptStatus : Current interruptm status

Branch
* BEQ rs1, rs2, bimm12
* BNE rs1, rs2, bimm12
* BLT rs1, rs2, bimm12
* BGE rs1, rs2, bimm12
* BLTU rs1, rs2, bimm12
* BGEU rs1, rs2, bimm12
    Implicit Read : pcc
    Implicit Write: pcc.addr, pcc.tag
    Functional Units:
      a) AdderBeforeBoundsCheck (computing branch target address PC + bimm12)
      b) AdderToOutput (computing sequential next PC PC + 2 / PC + 4)
      c) ComparatorGeneral (evaluating branch condition)
      d) Add_CapBSz (computing representable limit exponent)
      e) Shifter (computing representable limit shift mask 1 << Add_CapBSz)
      f) AdderBeforeRepCheck (computing representable upper limit address pcc.base + Shifter)
      g) ComparatorTopRep (checking representable upper limit AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      h) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= pcc.base)
      i) AddrBoundsCheck (validates top > addr >= base representability PC tag)

Cjal
* CJAL cd, jimm20
    Implicit Read : pcc
    Implicit Write: pcc.addr, pcc.tag
    Functional Units:
      a) AdderBeforeBoundsCheck (computing jump target address PC + jimm20)
      b) AdderToOutput (computing return link address PC + 2 / PC + 4)
      c) Add_CapBSz (computing representable limit exponent)
      d) Shifter (computing representable limit shift mask 1 << Add_CapBSz)
      e) AdderBeforeRepCheck (computing representable upper limit address pcc.base + Shifter)
      f) ComparatorTopRep (checking representable upper limit AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      g) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= pcc.base)
      h) AddrBoundsCheck (validates top > addr >= base representability PC tag)

Aui
* AUICGP cd, uimm20_11
    Implicit Read : c3 / CGP
* AUIPCC cd, uimm20_11
    Implicit Read : pcc
    Functional Units:
      a) AdderBeforeBoundsCheck (address calculation pcc.addr / cs1.addr + uimm20_11)
      b) Add_CapBSz (computing representable limit exponent)
      c) Shifter (computing representable limit shift mask 1 << Add_CapBSz)
      d) AdderBeforeRepCheck (computing representable upper limit address base + Shifter)
      e) ComparatorTopRep (checking representable upper limit AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      f) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= base)
      g) AddrBoundsCheck (validates top > addr >= base representability tag)

CIncAddr
* CIncAddr cd, cs1, rs2
* CIncAddrImm cd, cs1, simm12
    Functional Units:
      a) AdderBeforeBoundsCheck (address calculation cs1.addr + rs2 / simm12)
      b) Add_CapBSz (computing representable limit exponent)
      c) Shifter (computing representable limit shift mask 1 << Add_CapBSz)
      d) AdderBeforeRepCheck (computing representable upper limit address cs1.base + Shifter)
      e) ComparatorTopRep (checking representable upper limit AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      f) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= cs1.base)
      g) AddrBoundsCheck (validates top > addr >= base representability tag)

CSetAddr
* CSetAddr cd, cs1, rs2
    Functional Units:
      a) Add_CapBSz (computing representable limit exponent)
      b) Shifter (computing representable limit shift mask 1 << Add_CapBSz)
      c) AdderBeforeRepCheck (computing representable upper limit address cs1.base + Shifter)
      d) ComparatorTopRep (checking representable upper limit cs2.addr <= AdderBeforeRepCheck)
      e) ComparatorBase (checking representable lower limit cs2.addr >= cs1.base)
      f) AddrBoundsCheck (validates top > addr >= base representability tag)

Cjalr
* CJALR cd, cs1, simm12
    Implicit Read : pcc, interruptStatus
    Implicit Write: pcc, interruptStatus
    Functional Units:
      a) AdderBeforeBoundsCheck (computing jump target address cs1.addr + simm12)
      b) AdderToOutput (computing return link address PC + 2 / PC + 4)
      c) CjalrUnit (sentry legality / unsealing check unit)

CTestSubset
* CTestSubset rd, cs1, cs2
    Functional Units:
      a) ComparatorTopRep (checking top cs1.top <= cs2.top)
      b) ComparatorBase (checking base cs1.base >= cs2.base)
      c) CapSubset (validates top >= top2 AND base2 >= base AND permissions)

CSetBounds
* CSetBounds cd, cs1, rs2
* CSetBoundsExact cd, cs1, rs2
* CSetBoundsRoundDown cd, cs1, rs2
* CSetBoundsImm cd, cs1, zimm12
    Functional Units:
      a) Bounds (computing compressed bounds Bounds.base, Bounds.top, Bounds.E)
      b) ComparatorTopRep (verifying requested top < cs1.top)
      c) ComparatorBase (verifying requested base >= cs1.base)
      d) AddrBoundsCheck (validates top > addr >= base bounds check)

Seal
* CSeal cd, cs1, cs2
* CUnseal cd, cs1, cs2
    Functional Units:
      a) SealerUnsealer (computing sealed or unsealed capability metadata)
      b) ComparatorTopRep (checking top cs1.addr/cs1.otype < cs2.top)
      c) ComparatorBase (checking base cs1.addr/cs1.otype >= cs2.base)
      d) AddrBoundsCheck (validates top > addr >= base sealing check)

Load
* LB rd, simm12(cs1)
* LH rd, simm12(cs1)
* LW rd, simm12(cs1)
* LBU rd, simm12(cs1)
* LHU rd, simm12(cs1)
* LC cd, simm12(cs1)
    Can cause exceptions
    Functional Units:
      a) AdderBeforeBoundsCheck (memory address cs1.addr + simm12)
      b) ComparatorTopRep (checking top AdderBeforeBoundsCheck < cs1.top)
      c) ComparatorBase (checking base AdderBeforeBoundsCheck >= cs1.base)
      d) AddrBoundsCheck (validates top > addr >= base load bounds check)
      e) LoadUnit (outputs exception and LoadPostProcess LG/LM etc)

Store
* SB rs2, simm12(cs1)
* SH rs2, simm12(cs1)
* SW rs2, simm12(cs1)
* SC cs2, simm12(cs1)
    Can cause exceptions
    Functional Units:
      a) AdderBeforeBoundsCheck (memory address cs1.addr + simm12)
      b) ComparatorTopRep (checking top AdderBeforeBoundsCheck < cs1.top)
      c) ComparatorBase (checking base AdderBeforeBoundsCheck >= cs1.base)
      d) AddrBoundsCheck (validates top > addr >= base store bounds check)
      e) StoreUnit (outputs exception)

AddSub
* ADD rd, rs1, rs2
* SUB rd, rs1, rs2
* ADDI rd, rs1, simm12
    Functional Units:
      a) AdderToOutput (arithmetic calculation)

CSub
* CSub rd, cs1, cs2
    Functional Units:
      a) AdderToOutput (address difference calculation)

CGetLen
* CGetLen rd, cs1
    Functional Units:
      a) AdderToOutput (length calculation: cs1.top - cs1.base)

Slt
* SLT rd, rs1, rs2
* SLTU rd, rs1, rs2
* SLTI rd, rs1, simm12
* SLTIU rd, rs1, simm12
    Functional Units:
      a) ComparatorGeneral (integer set less than comparison)

CSetEqual
* CSetEqual rd, cs1, cs2
    Functional Units:
      a) ComparatorGeneral (compares cs1.addr == cs2.addr)
      b) CapEq (validates addr == addr2 AND ecap == ecap2 AND tag equal)

Shift
* SLL rd, rs1, rs2
* SRL rd, rs1, rs2
* SRA rd, rs1, rs2
* SLLI rd, rs1, shamt
* SRLI rd, rs1, shamt
* SRAI rd, rs1, shamt
    Functional Units:
      a) Shifter

Logical
* AND rd, rs1, rs2
* OR rd, rs1, rs2
* XOR rd, rs1, rs2
* ANDI rd, rs1, simm12
* ORI rd, rs1, simm12
* XORI rd, rs1, simm12
    Functional Units:
      a) Logical

Cram
* CRAM rd, rs1
    Functional Units:
      a) Bounds (representable alignment mask)

Crrl
* CRRL rd, rs1
    Functional Units:
      a) Bounds (computing representable rounded length)

CAndPerm
* CAndPerm cd, cs1, rs2
    Functional Units:
      a) CAndPerm

Csr
* CSRRW rd, csr, rs1
* CSRRS rd, csr, rs1
* CSRRC rd, csr, rs1
* CSRRWI rd, csr, zimm5
* CSRRSI rd, csr, zimm5
* CSRRCI rd, csr, zimm5
    Functional Units:
      None (direct CSR read routing)

Scr
* CSpecialRw cd, cSpecial, cs1
    Implicit Read : pcc.perms
    Decoder can cause exceptions if no ASR
    Functional Units:
      a) ScrSanitizer (check if the last LSB bit is 0 for certain SCR writes)

Lui
* LUI rd, uimm20
    Functional Units:
      None (direct immediate routing)

CGet
* CGetPerm rd, cs1
* CGetType rd, cs1
* CGetBase rd, cs1
* CGetTag rd, cs1
* CGetAddr rd, cs1
* CGetHigh rd, cs1
* CGetTop rd, cs1
    Functional Units:
      None (direct field extraction)

CSetHigh
* CSetHigh cd, cs1, rs2
    Functional Units:
      None (direct high word substitution & clearing tag)

CClearTag
* CClearTag cd, cs1
    Functional Units:
      None (direct tag clearing)

CMove
* CMove cd, cs1
    Functional Units:
      None (direct register copy)

Trap
* ECALL
* EBREAK
    Implicit Read : MTCC, pcc
    Implicit Write: MEPCC, pcc, mcause
    Will cause exception
    Functional Units:
      a) None (direct register copy)

Mret
* MRET
    Implicit Read : MEPCC, pcc.perms
    Implicit Write: pcc
    Decoder can cause exceptions if no ASR
    Functional Units:
      a) None (direct register copy)

-------------------------------------------------------------------------------
2. FUNCTIONAL UNIT/RESOURCE MAPPING
-------------------------------------------------------------------------------
AdderBeforeBoundsCheck:
  - ADD : Branch, Cjal, Aui, CIncAddr, CSetAddr, Cjalr, Load, Store
  inp1: pcc.addr (Branch, Cjal, Aui),
        cs1.addr (Aui, CIncAddr, CSetAddr, Cjalr, Load, Store)
  inp2: bimm12 (Branch), jimm20 (Cjal), uimm20_11 (Aui),
        cs2.addr (CIncAddr), simm12 (Cjalr, Load, Store)

AdderToOutput:
  - ADD : Branch, Cjal, Cjalr, AddSub (when ADD/ADDI)
  - SUB : AddSub (when SUB), CSub, CGetLen
  inp1: pcc.addr (Branch, Cjal, Cjalr), cs1.addr (AddSub, CSub),
        cs1.top (CGetLen)
  inp2: 2 (compressed {Branch, Cjal, Cjalr}), 4 (uncompressed {Branch, Cjal, Cjalr}),
        cs2.addr (AddSub, CSub), simm12 (AddSub), cs1.base (CGetLen)

Add_CapBSz:
  - ADD : Branch, Cjal, Aui, CIncAddr, CSetAddr
  inp1: pcc.exp (Branch, Cjal, Aui), cs1.exp (Aui, CIncAddr, CSetAddr)
  inp2: CapBSz (Branch, Cjal, Aui, CIncAddr, CSetAddr)

ComparatorGeneral:
  - EQ         : Branch (when BEQ/BNE), CSetEqual
  - LTSigned   : Branch (when BLT/BGE), Slt (when SLT/SLTI)
  - LTUnsigned : Branch (when BLTU/BGEU), Slt (when SLTU/SLTIU)
  - Invert     : Branch (when BNE, BGE, BGEU to invert EQ/LT result)
  Outputs: ComparatorGeneral.lt, ComparatorGeneral.eq
  inp1: cs1.addr (Branch, Slt, CSetEqual)
  inp2: cs2.addr (Branch, Slt, CSetEqual), simm12 (Slt)

CjalrUnit: Specialized sentry legality and unsealing check unit for indirect jumps (CJALR).
  - CheckSentryAndUnseal : Cjalr
  Outputs: CjalrUnit.tag (unsealed sentry tag), CjalrUnit.ecap (unsealed capability metadata), CjalrUnit.interruptStatus (updated interrupt status)
  inp1: cs1 (Cjalr)
  inp2: simm12 (Cjalr)
  inp3: currInterruptStatus (Cjalr)

Logical:
  - AND : Logical (when AND/ANDI)
  - OR  : Logical (when OR/ORI)
  - XOR : Logical (when XOR/XORI)
  inp1: cs1.addr (Logical)
  inp2: cs2.addr (Logical), simm12 (Logical)

CAndPerm: Specialized bitwise permission masking unit.
  - MaskPerms : CAndPerm
  Outputs: CAndPerm.tag, CAndPerm.ecap (updated tag and capability metadata word with masked permissions)
  inp1: cs1.tag (CAndPerm)
  inp2: cs1.ecap (CAndPerm)
  inp3: cs2.addr (CAndPerm)

SealerUnsealer: Specialized capability sealing and unsealing verification unit.
  - Seal   : Seal (when CSeal)
  - Unseal : Seal (when CUnseal)
  Outputs: SealerUnsealer.tag, SealerUnsealer.ecap (sealed or unsealed tag and capability metadata word)
  inp1: cs1.tag (Seal)
  inp2: cs1.ecap (Seal)
  inp3: cs2 (Seal)
  inp4: AddrBoundsCheck (Seal)

Bounds: Specialized capability bounds calculation, mask and length computation unit.
  - SetBounds   : CSetBounds
  - ComputeMask : Cram
  - ComputeLen  : Crrl
  Outputs: Bounds.base, Bounds.length, Bounds.top, Bounds.E, Bounds.cram, Bounds.crrl
  inp1: cs1 (CSetBounds, Cram, Crrl)
  inp2: cs2.addr (CSetBounds), zimm12 (CSetBounds), cs1.addr (Cram, Crrl)

Shifter:
  - ShiftLeftLogical     : Shift (when SLL/SLLI), Branch, Cjal, Aui, CIncAddr, CSetAddr
  - ShiftRightLogical    : Shift (when SRL/SRLI)
  - ShiftRightArithmetic : Shift (when SRA/SRAI)
  inp1: cs1.addr (Shift), 1 (Branch, Cjal, Aui, CIncAddr, CSetAddr)
  inp2: cs2.addr (Shift), shamt (Shift),
        Add_CapBSz (Branch, Cjal, Aui, CIncAddr, CSetAddr)

AdderBeforeRepCheck:
  - ADD : Branch, Cjal, Aui, CIncAddr, CSetAddr
  inp1: pcc.base (Branch, Cjal, Aui), cs1.base (Aui, CIncAddr, CSetAddr)
  inp2: Shifter (Branch, Cjal, Aui, CIncAddr, CSetAddr)

ComparatorTopRep: (checking against top or representable limit)
  - LTEUnsigned : CTestSubset
  - LTUnsigned  : Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal
  Outputs: ComparatorTopRep.lt, ComparatorTopRep.eq
  inp1: AdderBeforeBoundsCheck (Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store),
        cs1.addr (Seal), cs1.otype (Seal), cs1.top (CTestSubset)
  inp2: AdderBeforeRepCheck (Branch, Cjal, Aui, CIncAddr, CSetAddr),
        cs1.top (CSetBounds, Load, Store), cs2.top (Seal, CTestSubset)

ComparatorBase: (checking against base)
  - GTEUnsigned : Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Seal, Load, Store, CTestSubset
  Outputs: ComparatorBase.lt, ComparatorBase.eq
  inp1: AdderBeforeBoundsCheck (Branch, Cjal, Aui, CIncAddr, CSetAddr, Load, Store),
        cs1.addr (Seal, CSetBounds), cs1.otype (Seal), cs1.base (CTestSubset)
  inp2: pcc.base (Branch, Cjal, Aui),
        cs1.base (Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store),
        cs2.base (Seal, CTestSubset)

AddrBoundsCheck: Specialized capability address bounds and representability check unit.
  - CheckInBounds : Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal (validates top > addr >= base)
  Outputs: AddrBoundsCheck (validated Boolean capability/PC tag or in-bounds result)
  inp1: cs1.tag (Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal), pcc.tag (Branch, Cjal)
  inp2: ComparatorTopRep.lt (Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal)
  inp3: ComparatorBase.lt (Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal)
  inp4: ComparatorBase.eq (Branch, Cjal, Aui, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal)

CapSubset: Specialized capability inclusion testing unit.
  - Subset : CTestSubset (validates top >= top2 AND base2 >= base AND permissions subset)
  Outputs: CapSubset (Boolean inclusion verification result)
  inp1: ComparatorTopRep.lt (CTestSubset), ComparatorTopRep.eq (CTestSubset)
  inp2: ComparatorBase.lt (CTestSubset)
  inp3: cs1.perms (CTestSubset)
  inp4: cs2.perms (CTestSubset)
  inp5: cs1.tag (CTestSubset)
  inp6: cs2.tag (CTestSubset)

CapEq: Specialized whole capability exact equality testing unit.
  - Eq : CSetEqual (validates addr == addr2 AND ecap == ecap2 AND tag equal)
  Outputs: CapEq (Boolean exact capability equality result)
  inp1: ComparatorGeneral.eq (CSetEqual)
  inp2: cs1.tag (CSetEqual)
  inp3: cs2.tag (CSetEqual)
  inp4: cs1.ecap (CSetEqual)
  inp5: cs2.ecap (CSetEqual)

ScrSanitizer: Check if last LSB bit is 0 for certain SCR writes
  - SanitizeTag : Scr
  Outputs: ScrSanitizer (sanitized Boolean tag)
  inp1: cs1 (Scr)
  inp2: inst (Scr)

LoadUnit: Specialized load operation modifier and exception calculation unit.
  - CalcLoadOpAndException : Load
  Outputs: LoadUnit.Exception, LoadUnit.LoadPostProcess
  inp1: cs1.tag (Load)
  inp2: cs1.ecap (Load)
  inp3: AddrBoundsCheck (Load)
  inp4: LoadOp (Load)

StoreUnit: Specialized store exception calculation unit.
  - CalcStoreException : Store
  Outputs: StoreUnit.Exception
  inp1: cs1.tag (Store)
  inp2: cs1.ecap (Store)
  inp3: AddrBoundsCheck (Store)

NewPcc.tag: AddrBoundsCheck (Branch, Cjal), CjalrUnit.tag (Cjalr), pcc.tag (others)
NewPcc.ecap: CjalrUnit.ecap (Cjalr), pcc.ecap (others)
NewPcc.addr: AdderBeforeBoundsCheck (Branch taken, Cjal, Cjalr), AdderToOutput (Branch not taken, others)
NewInterruptStatus: CjalrUnit.interruptStatus (Cjalr), currInterruptStatus (others)

NewSpecial.tag: ScrSanitizer (Scr)
NewSpecial.ecap: cs1.ecap (Scr)
NewSpecial.addr: cs1.addr (Scr)

Reg.tag: 0 (Lui, AddSub, Slt, Shift, Logical, CGet, CGetLen, Cram, Crrl,
            CSub, CSetEqual, CTestSubset, Csr, CSetHigh, CClearTag, Load, Store),
         pcc.tag (Cjal),
         cs1.tag (Cjalr, CMove),
         AddrBoundsCheck (Aui, CIncAddr, CSetAddr, CSetBounds),
         CAndPerm.tag (CAndPerm),
         SealerUnsealer.tag (Seal),
         special.tag (Scr)

Reg.ecap: 0 (Lui, AddSub, Slt, Shift, Logical, CGet, CGetLen, Cram, Crrl,
             CSub, CSetEqual, CTestSubset, Csr, Load, Store),
          pcc.ecap (Aui, Cjal, Cjalr), c3.ecap (Aui),
          cs1.ecap (CIncAddr, CSetAddr, CClearTag, CMove),
          cs2.addr (CSetHigh), CAndPerm.ecap (CAndPerm),
          SealerUnsealer.ecap (Seal),
          {cs1.perms, cs1.otype, Bounds.base, Bounds.top, Bounds.E} (CSetBounds),
          special.ecap (Scr)

Reg.addr: uimm20 (Lui), AdderBeforeBoundsCheck (Aui, CIncAddr, Load, Store),
          ComparatorGeneral.lt (Slt), Shifter (Shift), Logical (Logical),
          AdderToOutput (Cjal, Cjalr, AddSub, CGetLen, CSub),
          cs1.fields (CGet), cs2.addr (CSetAddr),
          cs1.addr (CAndPerm, CClearTag, Seal, CMove, CSetHigh),
          Bounds.base (CSetBounds), Bounds.cram (Cram), Bounds.crrl (Crrl),
          CapSubset (CTestSubset), CapEq (CSetEqual), special.addr (Csr, Scr)

Exception: LoadUnit.Exception (Load), StoreUnit.Exception (Store), 0 (others)
LoadPostProcess: LoadUnit.LoadPostProcess (Load), 0 (others)
*)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Definition InstGroup := STRUCT_TYPE {
  "Branch"      :: Bool ;
  "Cjal"        :: Bool ;
  "Aui"         :: Bool ;
  "CIncAddr"    :: Bool ;
  "CSetAddr"    :: Bool ;
  "Cjalr"       :: Bool ;
  "CTestSubset" :: Bool ;
  "CSetBounds"  :: Bool ;
  "Seal"        :: Bool ;
  "Load"        :: Bool ;
  "Store"       :: Bool ;
  "AddSub"      :: Bool ;
  "CSub"        :: Bool ;
  "CGetLen"     :: Bool ;
  "Slt"         :: Bool ;
  "CSetEqual"   :: Bool ;
  "Shift"       :: Bool ;
  "Logical"     :: Bool ;
  "Cram"        :: Bool ;
  "Crrl"        :: Bool ;
  "CAndPerm"    :: Bool ;
  "Csr"         :: Bool ;
  "Scr"         :: Bool ;
  "Lui"         :: Bool ;
  "CGet"        :: Bool ;
  "CSetHigh"    :: Bool ;
  "CClearTag"   :: Bool ;
  "CMove"       :: Bool ;
  "Trap"        :: Bool ;
  "Mret"        :: Bool
}.

Definition AluControl := STRUCT_TYPE {
  "AdderBeforeBoundsCheck_base_isPccAddrNotCs1Addr" :: Bool ;
  "AdderBeforeBoundsCheck_offset_bimm12" :: Bool ;
  "AdderBeforeBoundsCheck_offset_jimm20" :: Bool ;
  "AdderBeforeBoundsCheck_offset_uimm20_11" :: Bool ;
  "AdderBeforeBoundsCheck_offset_cs2Addr" :: Bool ;
  "AdderBeforeBoundsCheck_offset_simm12" :: Bool ; (* default option *)
  "AdderToOutput_base_pccAddr" :: Bool ;
  "AdderToOutput_base_cs1Addr" :: Bool ; (* default option *)
  "AdderToOutput_base_cs1Top" :: Bool ;
  "AdderToOutput_offset_const2" :: Bool ;
  "AdderToOutput_offset_const4" :: Bool ; (* default option *)
  "AdderToOutput_offset_cs2Addr" :: Bool ;
  "AdderToOutput_offset_simm12" :: Bool ;
  "AdderToOutput_offset_cs1Base" :: Bool ;
  "AdderToOutput_isSub" :: Bool ;
  "Add_CapBSz_baseExp_isPccExpNotCs1Exp" :: Bool ;
  "ComparatorGeneral_op2_isCs2AddrNotSimm12" :: Bool ;
  "ComparatorGeneral_isUnsigned" :: Bool ;
  "ComparatorGeneral_checkLt" :: Bool ;
  "ComparatorGeneral_checkEq" :: Bool ;
  "ComparatorGeneral_invertRes" :: Bool ;
  "Logical_op2_isCs2AddrNotSimm12" :: Bool ;
  "Logical_opSel" :: Bit 2 ; (* Options: 0 (2'b00) = AND, 1 (2'b01) = OR, 2 (2'b10) = XOR *)
  "SealerUnsealer_isUnseal" :: Bool ;
  "Bounds_reqLimit_cs2Addr" :: Bool ;
  "Bounds_reqLimit_zimm12" :: Bool ; (* default option *)
  "Bounds_reqLimit_cs1Addr" :: Bool ;
  "Bounds_isRoundDown" :: Bool ;
  "Shifter_data_isCs1AddrNotConst1" :: Bool ;
  "Shifter_shamt_cs2Addr" :: Bool ;
  "Shifter_shamt_shamt" :: Bool ; (* default option *)
  "Shifter_shamt_AddCapBSz" :: Bool ;
  "Shifter_isRight" :: Bool ;
  "Shifter_isArith" :: Bool ;
  "AdderBeforeRepCheck_base_isPccBaseNotCs1Base" :: Bool ;
  "ComparatorTopRep_addr_AdderBeforeBoundsCheck" :: Bool ;
  "ComparatorTopRep_addr_cs1Addr" :: Bool ; (* default option *)
  "ComparatorTopRep_addr_cs1OType" :: Bool ;
  "ComparatorTopRep_addr_cs1Top" :: Bool ;
  "ComparatorTopRep_topRep_AdderBeforeRepCheck" :: Bool ;
  "ComparatorTopRep_topRep_cs1Top" :: Bool ; (* default option *)
  "ComparatorTopRep_topRep_cs2Top" :: Bool ;
  "ComparatorTopRep_checkLte" :: Bool ;
  "ComparatorBase_addr_AdderBeforeBoundsCheck" :: Bool ;
  "ComparatorBase_addr_cs1Addr" :: Bool ; (* default option *)
  "ComparatorBase_addr_cs1OType" :: Bool ;
  "ComparatorBase_addr_cs1Base" :: Bool ;
  "ComparatorBase_base_pccBase" :: Bool ;
  "ComparatorBase_base_cs1Base" :: Bool ; (* default option *)
  "ComparatorBase_base_cs2Base" :: Bool ;
  "AddrBoundsCheck_tag_isPccTagNotCs1Tag" :: Bool ;
  "NewPcc_tag_isAddrBoundsCheckNotCjalrUnitTag" :: Bool ;
  "NewPcc_ecap_isCjalrUnitEcapNotPccEcap" :: Bool ;
  "NewPcc_addr_isAdderBeforeBoundsCheckNotAdderToOutput" :: Bool ;
  "Reg_tag_const0" :: Bool ; (* default option *)
  "Reg_tag_pccTag" :: Bool ;
  "Reg_tag_cs1Tag" :: Bool ;
  "Reg_tag_AddrBoundsCheck" :: Bool ;
  "Reg_CAndPerm" :: Bool ;
  "Reg_SealerUnsealer" :: Bool ;
  "Reg_tag_or_ecap_special" :: Bool ;
  "Reg_ecap_const0" :: Bool ; (* default option *)
  "Reg_ecap_pccEcap" :: Bool ;
  "Reg_ecap_cs1Ecap" :: Bool ;
  "Reg_ecap_cs2Addr" :: Bool ;
  "Reg_ecap_or_addr_Bounds" :: Bool ;
  "Reg_addr_uimm20" :: Bool ; (* default option *)
  "Reg_addr_AdderBeforeBoundsCheck" :: Bool ;
  "Reg_addr_ComparatorGeneralLt" :: Bool ;
  "Reg_addr_Shifter" :: Bool ;
  "Reg_addr_Logical" :: Bool ;
  "Reg_addr_AdderToOutput" :: Bool ;
  "Reg_addr_cs1Fields" :: Bool ;
  "Reg_addr_cs2Addr" :: Bool ;
  "Reg_addr_cs1Addr" :: Bool ;
  "Reg_addr_BoundsCram" :: Bool ;
  "Reg_addr_BoundsCrrl" :: Bool ;
  "Reg_addr_CapSubset" :: Bool ;
  "Reg_addr_CapEq" :: Bool ;
  "Reg_addr_specialAddr" :: Bool ;
  "Exception_isLoadUnitNotStoreUnit" :: Bool }.

Section DecodeInstGroup.
  Variable ty : Kind -> Type.
  Variable group : ty InstGroup.

  Definition decodeInstGroup : Expr ty AluControl :=
    STRUCT {
      "AdderBeforeBoundsCheck_base_isPccAddrNotCs1Addr" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui" ] ;
      "AdderBeforeBoundsCheck_offset_bimm12" ::= ##group`"Branch" ;
      "AdderBeforeBoundsCheck_offset_jimm20" ::= ##group`"Cjal" ;
      "AdderBeforeBoundsCheck_offset_uimm20_11" ::= ##group`"Aui" ;
      "AdderBeforeBoundsCheck_offset_cs2Addr" ::= ##group`"CSetAddr" ;
      "AdderBeforeBoundsCheck_offset_simm12" ::= Const ty Bool true ;
      "AdderToOutput_base_pccAddr" ::= Or [ ##group`"Cjal"; ##group`"Cjalr" ] ;
      "AdderToOutput_base_cs1Addr" ::= Const ty Bool true ;
      "AdderToOutput_base_cs1Top" ::= ##group`"CGetLen" ;
      "AdderToOutput_offset_const2" ::= Const ty Bool false ;
      "AdderToOutput_offset_const4" ::= Const ty Bool true ;
      "AdderToOutput_offset_cs2Addr" ::= ##group`"CSub" ;
      "AdderToOutput_offset_simm12" ::= ##group`"AddSub" ;
      "AdderToOutput_offset_cs1Base" ::= ##group`"CGetLen" ;
      "AdderToOutput_isSub" ::= Or [ ##group`"CSub"; ##group`"CGetLen" ] ;
      "Add_CapBSz_baseExp_isPccExpNotCs1Exp" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui" ] ;
      "ComparatorGeneral_op2_isCs2AddrNotSimm12" ::= Or [ ##group`"Branch"; ##group`"CSetEqual" ] ;
      "ComparatorGeneral_isUnsigned" ::= Or [ ##group`"Branch"; ##group`"Slt" ] ;
      "ComparatorGeneral_checkLt" ::= Or [ ##group`"Branch"; ##group`"Slt" ] ;
      "ComparatorGeneral_checkEq" ::= Or [ ##group`"Branch"; ##group`"CSetEqual" ] ;
      "ComparatorGeneral_invertRes" ::= Const ty Bool false ;
      "Logical_op2_isCs2AddrNotSimm12" ::= ##group`"Logical" ;
      "Logical_opSel" ::= Const ty (Bit 2) Zmod.zero ;
      "SealerUnsealer_isUnseal" ::= Const ty Bool false ;
      "Bounds_reqLimit_cs2Addr" ::= ##group`"CSetBounds" ;
      "Bounds_reqLimit_zimm12" ::= Const ty Bool true ;
      "Bounds_reqLimit_cs1Addr" ::= Or [ ##group`"Cram"; ##group`"Crrl" ] ;
      "Bounds_isRoundDown" ::= ##group`"CSetBounds" ;
      "Shifter_data_isCs1AddrNotConst1" ::= ##group`"Shift" ;
      "Shifter_shamt_cs2Addr" ::= ##group`"CSetAddr" ;
      "Shifter_shamt_shamt" ::= Const ty Bool true ;
      "Shifter_shamt_AddCapBSz" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui"; ##group`"CIncAddr"; ##group`"CSetAddr" ] ;
      "Shifter_isRight" ::= ##group`"Shift" ;
      "Shifter_isArith" ::= ##group`"Shift" ;
      "AdderBeforeRepCheck_base_isPccBaseNotCs1Base" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui" ] ;
      "ComparatorTopRep_addr_AdderBeforeBoundsCheck" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui"; ##group`"CIncAddr"; ##group`"Load"; ##group`"Store" ] ;
      "ComparatorTopRep_addr_cs1Addr" ::= Const ty Bool true ;
      "ComparatorTopRep_addr_cs1OType" ::= ##group`"Seal" ;
      "ComparatorTopRep_addr_cs1Top" ::= ##group`"CTestSubset" ;
      "ComparatorTopRep_topRep_AdderBeforeRepCheck" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui"; ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CSetBounds" ] ;
      "ComparatorTopRep_topRep_cs1Top" ::= Const ty Bool true ;
      "ComparatorTopRep_topRep_cs2Top" ::= Or [ ##group`"CTestSubset"; ##group`"Seal" ] ;
      "ComparatorTopRep_checkLte" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui"; ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CTestSubset" ] ;
      "ComparatorBase_addr_AdderBeforeBoundsCheck" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui"; ##group`"CIncAddr"; ##group`"Load"; ##group`"Store" ] ;
      "ComparatorBase_addr_cs1Addr" ::= Const ty Bool true ;
      "ComparatorBase_addr_cs1OType" ::= ##group`"Seal" ;
      "ComparatorBase_addr_cs1Base" ::= ##group`"CTestSubset" ;
      "ComparatorBase_base_pccBase" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Aui" ] ;
      "ComparatorBase_base_cs1Base" ::= Const ty Bool true ;
      "ComparatorBase_base_cs2Base" ::= Or [ ##group`"CTestSubset"; ##group`"Seal" ] ;
      "AddrBoundsCheck_tag_isPccTagNotCs1Tag" ::= Or [ ##group`"Branch"; ##group`"Cjal" ] ;
      "NewPcc_tag_isAddrBoundsCheckNotCjalrUnitTag" ::= Or [ ##group`"Branch"; ##group`"Cjal" ] ;
      "NewPcc_ecap_isCjalrUnitEcapNotPccEcap" ::= ##group`"Cjalr" ;
      "NewPcc_addr_isAdderBeforeBoundsCheckNotAdderToOutput" ::= Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"Cjalr" ] ;
      "Reg_tag_const0" ::= Const ty Bool true ;
      "Reg_tag_pccTag" ::= ##group`"Cjal" ;
      "Reg_tag_cs1Tag" ::= Or [ ##group`"Cjalr"; ##group`"CMove" ] ;
      "Reg_tag_AddrBoundsCheck" ::= Or [ ##group`"Aui"; ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CSetBounds" ] ;
      "Reg_CAndPerm" ::= ##group`"CAndPerm" ;
      "Reg_SealerUnsealer" ::= ##group`"Seal" ;
      "Reg_tag_or_ecap_special" ::= ##group`"Scr" ;
      "Reg_ecap_const0" ::= Const ty Bool true ;
      "Reg_ecap_pccEcap" ::= Or [ ##group`"Aui"; ##group`"Cjal"; ##group`"Cjalr" ] ;
      "Reg_ecap_cs1Ecap" ::= Or [ ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CClearTag"; ##group`"CMove" ] ;
      "Reg_ecap_cs2Addr" ::= ##group`"CSetHigh" ;
      "Reg_ecap_or_addr_Bounds" ::= ##group`"CSetBounds" ;
      "Reg_addr_uimm20" ::= Const ty Bool true ;
      "Reg_addr_AdderBeforeBoundsCheck" ::= Or [ ##group`"Aui"; ##group`"CIncAddr"; ##group`"Load"; ##group`"Store" ] ;
      "Reg_addr_ComparatorGeneralLt" ::= ##group`"Slt" ;
      "Reg_addr_Shifter" ::= ##group`"Shift" ;
      "Reg_addr_Logical" ::= ##group`"Logical" ;
      "Reg_addr_AdderToOutput" ::= Or [ ##group`"Cjal"; ##group`"Cjalr"; ##group`"AddSub"; ##group`"CGetLen"; ##group`"CSub" ] ;
      "Reg_addr_cs1Fields" ::= ##group`"CGet" ;
      "Reg_addr_cs2Addr" ::= ##group`"CSetAddr" ;
      "Reg_addr_cs1Addr" ::= Or [ ##group`"CAndPerm"; ##group`"CClearTag"; ##group`"Seal"; ##group`"CMove"; ##group`"CSetHigh" ] ;
      "Reg_addr_BoundsCram" ::= ##group`"Cram" ;
      "Reg_addr_BoundsCrrl" ::= ##group`"Crrl" ;
      "Reg_addr_CapSubset" ::= ##group`"CTestSubset" ;
      "Reg_addr_CapEq" ::= ##group`"CSetEqual" ;
      "Reg_addr_specialAddr" ::= Or [ ##group`"Csr"; ##group`"Scr" ] ;
      "Exception_isLoadUnitNotStoreUnit" ::= ##group`"Load"
    }.
End DecodeInstGroup.

Section Alu.
  Variable ty : Kind -> Type.
  Variable pcc cs1 cs2 special : ty FullECapWithTag.
  Variable inst : ty (Bit 32).
  Variable currInterruptStatus : ty Bool.

  (* ===========================================================================
     1. GALLINA FUNCTIONAL UNIT SPECIFICATIONS
     =========================================================================== *)

  Definition AdderBeforeBoundsCheck (base offset : ty (Bit Xlen)) : LetExpr ty (Bit Xlen) :=
    LetE sum : Bit Xlen <- Add [ #base; #offset ];
    RetE #sum.

  Definition AdderToOutput (base offset : ty (Bit Xlen)) (isSub : ty Bool) : LetExpr ty (Bit Xlen) :=
    LetE op2 : Bit Xlen <- ITE #isSub (Not #offset) #offset;
    LetE cin : Bit Xlen <- ZeroExtendTo Xlen (ToBit #isSub);
    LetE sum : Bit Xlen <- Add [ #base; #op2; #cin ];
    RetE #sum.

  Definition Add_CapBSz (baseExp : ty (Bit ExpSz)) : LetExpr ty (Bit ExpSz) :=
    LetE sum : Bit ExpSz <- Add [ #baseExp; $CapBSz ];
    RetE #sum.

  Definition ComparatorOut := STRUCT_TYPE {
    "lt" :: Bool ;
    "eq" :: Bool }.

  Definition ComparatorGeneral (op1 op2 : ty (Bit Xlen)) (isUnsigned checkLt checkEq invertRes : ty Bool) :
    LetExpr ty ComparatorOut :=
    LetE flipBit : Bit 1 <- ToBit (Not #isUnsigned) ;
    let flipMsb e:= {< Xor [#flipBit; TruncMsb 1 (Xlen-1) e], TruncLsb 1 (Xlen-1) e >} in
    LetE op1_flipped : Bit Xlen <- flipMsb #op1 ;
    LetE op2_flipped : Bit Xlen <- flipMsb #op2 ;
    LetE ltRes : Bool <- Slt #op1_flipped #op2_flipped;
    LetE eqRes : Bool <- Eq #op1 #op2;
    LetE cond  : Bool <- Or [ And [ #checkLt; #ltRes ]; And [ #checkEq; #eqRes ] ];
    LetE finalRes : Bool <- ITE #invertRes (Not #cond) #cond;
    @RetE _ ComparatorOut (STRUCT { "lt" ::= #finalRes; "eq" ::= #eqRes }).

  Definition CjalrUnitRes := STRUCT_TYPE {
    "tag"             :: Bool;
    "ecap"            :: ECap;
    "interruptStatus" :: Bool }.

  Definition CjalrUnit (cs1 : ty FullECapWithTag) (instWord : ty Inst) (currIntStatus : ty Bool)
                       : LetExpr ty CjalrUnitRes :=
    LetE cs1Tag : Bool <- ##cs1`"tag" ;
    LetE cs1ECap : ECap <- ##cs1`"ecap" ;
    LetE cs1PermEx : Bool <- ##cs1ECap`"perms"`"EX" ;
    LetE cs1Sealed : Bool <- isSealed cs1ECap ;
    LetE notCs1Sealed : Bool <- Not #cs1Sealed ;

    LetE cdNum : Bit RegIdxSz <- getCd instWord ;
    LetE cs1Num : Bit RegIdxSz <- getCs1 instWord ;
    LetE immZero : Bool <- isZero (#instWord`[31:20]) ;

    LetE isCdZero : Bool <- isZero #cdNum ;
    LetE isCs1Cra : Bool <- Eq #cs1Num $Cra ;
    LetE isCdCra  : Bool <- Eq #cdNum $Cra ;
    LetE isReturn : Bool <- And [#isCdZero; #isCs1Cra] ;
    LetE isCall   : Bool <- #isCdCra ;

    LetE cs1OType : Bit CapOTypeSz <- ##cs1ECap`"oType" ;

    LetE nextPccLegal : Bool <- caseDefault [ (#isReturn, isRetSentry cs1OType);
                                              (#isCall, Or [#notCs1Sealed; isCallSentry cs1OType]) ]
                                  (Or [#notCs1Sealed; Eq #cs1OType $CallSentryIh]);

    LetE nextPccTag : Bool <- And [#cs1Tag; #cs1PermEx; #nextPccLegal; Or [#notCs1Sealed; #immZero]] ;
    LetE nextPccECap : ECap <- ##cs1ECap `{ "oType" <- $0 } ;

    LetE nextIntStatus : Bool <- ITE (And [#nextPccTag; Not (isSentryIh cs1OType)])
                                   (isSentryIe cs1OType)
                                   #currIntStatus;

    @RetE _ CjalrUnitRes (STRUCT { "tag"             ::= #nextPccTag;
                                   "ecap"            ::= #nextPccECap;
                                   "interruptStatus" ::= #nextIntStatus }).

  Definition Logical (op1 op2 : ty (Bit Xlen)) (opSel : ty (Bit 2)) : LetExpr ty (Bit Xlen) :=
    LetE andRes : Bit Xlen <- And [ #op1; #op2 ];
    LetE orRes  : Bit Xlen <- Or [ #op1; #op2 ];
    LetE xorRes : Bit Xlen <- Xor [ #op1; #op2 ];
    LetE selArr : Array 2 Bool <- FromBit _ #opSel;
    RetE (ITE (#selArr$[1]) #xorRes (ITE (#selArr$[0]) #orRes #andRes)).

  Definition TagECap := STRUCT_TYPE {
    "tag"  :: Bool ;
    "ecap" :: ECap }.

  Definition CAndPerm (capTag : ty Bool) (ecapVal : ty ECap) (rs2 : ty Data) : LetExpr ty TagECap :=
    LetE maskBits : Bit (kindSize CapPerms) <- TruncLsb (Xlen - kindSize CapPerms) (kindSize CapPerms) #rs2 ;
    LetE maskVal : CapPerms <- FromBit CapPerms #maskBits ;
    LetE oldPerms : CapPerms <- ##ecapVal`"perms" ;
    LetE rawMask : CapPerms <- And [ ##oldPerms; #maskVal ] ;
    LetE newPerms : CapPerms <- fixPerms rawMask ;
    LetE sealed : Bool <- isSealed ecapVal ;
    LetE maskAllOnesNonGL : Bool <- isAllOnes (#maskVal `{ "GL" <- ConstTBool true }) ;
    LetE keepTag : Bool <- Or [ Not #sealed; #maskAllOnesNonGL ] ;
    LetE outTag : Bool <- And [ #capTag; #keepTag ] ;
    LetE outECap : ECap <- ##ecapVal `{ "perms" <- #newPerms } ;
    @RetE _ TagECap (STRUCT { "tag" ::= #outTag; "ecap" ::= #outECap }).

  Definition SealerUnsealer (isUnseal boundsValid cs1Tag : ty Bool) (ecap1 : ty ECap) (src2 : ty FullECapWithTag)
    : LetExpr ty TagECap :=
    LetE ecap2 : ECap <- ##src2`"ecap" ;
    LetE perms1 : CapPerms <- ##ecap1`"perms" ;
    LetE perms2 : CapPerms <- ##ecap2`"perms" ;
    LetE sealed1 : Bool <- isSealed ecap1 ;
    LetE sealed2 : Bool <- isSealed ecap2 ;
    LetE cs2Addr : Data <- ##src2`"addr" ;
    LetE cs2Tag : Bool <- ##src2`"tag" ;
    LetE sealRange : Bool <- ITE (##perms1`"EX")
                               (And [ Sgt #cs2Addr $0; Sle #cs2Addr $7 ])
                               (And [ Sgt #cs2Addr $8; Sle #cs2Addr $15 ]) ;
    LetE permit : Bool <- ITE #isUnseal
                            (And [ #sealed1; ##perms2`"US" ])
                            (And [ Not #sealed1; ##perms2`"SE"; #sealRange ]) ;
    LetE outTag : Bool <- And [ #cs1Tag; #cs2Tag; #boundsValid; Not #sealed2; #permit ] ;
    LetE outOType : Bit CapOTypeSz <- ITE #isUnseal $0 (TruncLsb (AddrSz - CapOTypeSz) CapOTypeSz #cs2Addr) ;
    LetE outGL : Bool <- ITE #isUnseal (And [ ##perms1`"GL"; ##perms2`"GL" ]) (##perms1`"GL") ;
    LetE outPerms : CapPerms <- ##perms1 `{ "GL" <- #outGL } ;
    LetE outECap : ECap <- ##ecap1 `{ "oType" <- #outOType } `{ "perms" <- #outPerms } ;
    @RetE _ TagECap (STRUCT { "tag" ::= #outTag; "ecap" ::= #outECap }).

  Definition BoundsRes := STRUCT_TYPE {
    "E" :: Bit ExpSz ;
    "base" :: Bit (Xlen + 1) ;
    "top" :: Bit (Xlen + 1) ;
    "cram" :: Bit (Xlen + 1) ;
    "length" :: Bit (Xlen + 1) ;
    "exact" :: Bool }.

  (*  ===================================================================
      CSETBOUNDS ALGORITHM & INFORMAL PROOF OF CORRECTNESS
      ===================================================================

      Problem Statement:
      Given input base (AddrSz + 1 bits) and length (AddrSz + 1 bits),
      compute mantissa m (CapBSz bits), exponent e (LgAddrSz bits) s.t.:
        1) outBase = floor(base / 2^e) * 2^e
        2) outLength = m * 2^e
        3) outBase <= base
        4) outBase + outLength >= base + length
        5) outBase + (m - 1) * 2^e < base + length
        6) MSB of m is 1 unless e is 0.

      ALGORITHM DEFINITION:

      Step 1: Initial Canonical Exponent Selection & Sub-Algorithm
        Sub-Algorithm to obtain e_init:
          Let lenTrunc : Bit (AddrSz + 1 - CapBSz) = floor(length / 2^CapBSz).
          Let clz : Bit LgAddrSz = countLeadingZeros(lenTrunc).
          Let e_init : Bit LgAddrSz = (AddrSz + 1 - CapBSz) - clz.

        Bit-Width Justifications:
          - lenTrunc: length is AddrSz + 1 bits. Right shift by CapBSz leaves AddrSz + 1 - CapBSz bits.
          - clz, e_init: Since CapBSz >= 2, lenTrunc width W = AddrSz + 1 - CapBSz < AddrSz = 2^LgAddrSz.
           Thus max count W <= 2^LgAddrSz - 1, fitting in LgAddrSz bits.

        Condition Satisfied:
          if length < 2^CapBSz, then e_init = 0
          if length >= 2^CapBSz, then 2^e_init > length / 2^CapBSz >= 2^(e_init - 1).

        Proof of Condition:
          Let W = AddrSz + 1 - CapBSz be bit-width of lenTrunc.
          - If lenTrunc == 0 (length < 2^CapBSz): clz = W implies e_init = 0.
          - If lenTrunc >= 1 (length >= 2^CapBSz): Top '1' bit of lenTrunc is at index
            (W - 1) - clz = e_init - 1. Thus 2^(e_init - 1) <= lenTrunc <= 2^e_init - 1 < 2^e_init.
            Since lenTrunc = floor(length / 2^CapBSz) <= length / 2^CapBSz, we have:
              length / 2^CapBSz >= lenTrunc >= 2^(e_init - 1).
            And since length / 2^CapBSz < lenTrunc + 1 (lenTrunc is the floor(length/2^CapBSz)) <= 2^e_init,
              we strictly have: length / 2^CapBSz < 2^e_init.
            Thus 2^e_init > length / 2^CapBSz >= 2^(e_init - 1). (QED)

      Step 2: Base Candidate & Unaligned Remainders
        Let d : Bit (CapBSz + 1) = floor(length / 2^e_init).
        Let base_mod_e : Bit (AddrSz + 2 - CapBSz) = base mod 2^e_init.
        Let length_mod_e : Bit (AddrSz + 2 - CapBSz) = length mod 2^e_init.
        Let sum_mod_e : Bit (AddrSz + 2 - CapBSz) = base_mod_e + length_mod_e.
        Let iCeil : Bit 2 = ceil(sum_mod_e / 2^e_init).
        Let m_raw : Bit (CapBSz + 1) = d + iCeil.

        Bit-Width Justifications:
          - d: By Step 1 proof, length / 2^e_init < 2^CapBSz, so d <= 2^CapBSz - 1.
          - remainders: Since clz >= 0, max e_init = AddrSz + 1 - CapBSz.
                        Moduli at 2^e_init are strictly < 2^e_init,
            fitting in AddrSz + 1 - CapBSz bits; their sum needs + 1 carry bit (AddrSz + 2 - CapBSz bits total).
          - iCeil: sum_mod_e / 2^e_init < 2, so ceil <= 2 (2 bits).
          - m_raw: max(d) + max(iCeil) = 2^CapBSz + 1, fitting in CapBSz + 1 bits.

        Condition Satisfied:
          floor(base / 2^e_init) * 2^e_init + m_raw * 2^e_init >= base + length.

        Proof of Condition:
          Let c1_base = floor(base / 2^e_init) * 2^e_init.
          By standard remainder definitions:
            base = c1_base + base_mod_e
            length = d * 2^e_init + length_mod_e.
          Summing these exact inputs: base + length = c1_base + d * 2^e_init + sum_mod_e.
          Since iCeil = ceil(sum_mod_e / 2^e_init), we have iCeil * 2^e_init >= sum_mod_e.
          Adding c1_base + d * 2^e_init to both sides yields:
            c1_base + (d + iCeil) * 2^e_init >= base + length.
          Substituting m_raw = d + iCeil proves c1_base + m_raw * 2^e_init >= base + length. (QED)

      Step 3: Normalization & Base Parity Inspection
        Let b_e : Bit 1 = (base / 2^e_init) mod 2  (bit e_init of base).
        Let isOverflow : Bool = (m_raw >= 2^CapBSz).

        Final Exponent Output (e : Bit LgAddrSz):
          Let e_unsat : Bit LgAddrSz = e_init + 1  if isOverflow else  e_init
          e : Bit LgAddrSz = AddrSz + 1 - CapBSz  if (e_unsat > AddrSz - CapBSz) else  e_unsat

        Final Mantissa Output (m : Bit CapBSz):
          if not isOverflow:
            m : Bit CapBSz = TruncLsb CapBSz m_raw
          else:
            m : Bit CapBSz = 2^(CapBSz - 1) + (1 if (m_raw + b_e > 2^CapBSz) else 0)

        Conditions Satisfied:
          0) if isOverflow then m = ceil((m_raw + b_e) / 2) else m = m_raw
          1) outBase = floor(base / 2^e) * 2^e <= base
          2) outBase + m * 2^e >= base + length
          3) outBase + (m - 1) * 2^e < base + length
          4) MSB of m is 1 unless e is 0.

        Proofs of Conditions:
          0) Trivial for non overflow case.
             For overflow case, by checking all cases of m_raw in {2^CapBSz, 2^CapBSz + 1} and b_e in {0, 1},
               m is algebraically identical to ceil((m_raw + b_e) / 2).
          1) Lower Bound: By properties of integer division floor, floor(X) <= X. (QED)
          2) Upper Bound:
              Let c1_base = floor(base / 2^e_init) * 2^e_init.
              If not isOverflow (e = e_init, m = m_raw): outBase = c1_base.
                By Step 2 proof, c1_base + m_raw * 2^e_init >= base + length. (QED)
              If isOverflow (e = e_init + 1, 2^e = 2 * 2^e_init):
                By parity shift, outBase = c1_base - b_e * 2^e_init.
                Thus outBase + outLength = c1_base - b_e * 2^e_init + m * (2 * 2^e_init).
                By definition of ceiling, ceil(X) >= X. Letting X = (m_raw + b_e) / 2,
                  we have m >= (m_raw + b_e) / 2.
                Multiplying both sides of this inequality by 2 yields 2 * m >= m_raw + b_e.
                Substituting yields outBase + outLength >= c1_base + m_raw * 2^e_init >= base + length. (QED)
          3) Minimality:
              We prove outBase + (m - 1) * 2^e < base + length for both execution cases:
              - Case 1 (not isOverflow, e = e_init, m = d + iCeil, outBase = c1_base):
                  outBase + (m - 1) * 2^e_init = c1_base + d * 2^e_init + (iCeil - 1) * 2^e_init.
                  Since base + length = c1_base + d * 2^e_init + sum_mod_e, difference is:
                  (iCeil - 1) * 2^e_init - sum_mod_e.
                  Since iCeil = ceil(sum_mod_e / 2^e_init), strictly (iCeil - 1) * 2^e_init < sum_mod_e.
                  Thus outBase + (m - 1) * 2^e < base + length. (QED)
              - Case 2 (isOverflow, e = e_init + 1, granularity 2 * 2^e_init, outBase = c1_base - b_e * 2^e_init):
                  Since m = ceil((m_raw + b_e) / 2), strictly 2 * (m - 1) < m_raw + b_e.
                  Thus outLength = (m - 1) * (2 * 2^e_init) < (m_raw + b_e) * 2^e_init.
                  Summing outBase + outLength strictly yields < c1_base + m_raw * 2^e_init.
                  By Case 1 proof, any multiple below m_raw * 2^e_init strictly falls short of base + length. (QED)
          4) Normalization Form:
              For any CapBSz-bit integer m, MSB is 1 iff m >= 2^(CapBSz - 1). Assume e > 0.
              If not isOverflow: e = e_init > 0. By Step 1 proof, length / 2^CapBSz >= 2^(e_init - 1),
                implying length / 2^e_init >= 2^(CapBSz - 1). Thus m = m_raw >= d >= 2^(CapBSz - 1).
              If isOverflow: By Step 3 formula, m >= 2^(CapBSz - 1). Thus MSB is strictly 1. (QED)

      The RoundDown variation is a minor change to the above (outLength should be less than input length):
        Given base alignment 2^e_b (e_b trailing zeros), exact base retention requires e_init <= e_b.
        - If e_b <= e_init-1: length / 2^e_b >= 2^CapBSz overflows mantissa. To maximize length <= input,
          we set e = e_b and saturate m = 2^CapBSz - 1. MSB is strictly 1. (QED)
        - If e_b >= e_init: base is aligned to 2^e_init. We set e = e_init and m = d <= length / 2^e_init.
          By Step 1 of the previous proof, d >= 2^(CapBSz - 1), so MSB is strictly 1. (QED)
   *)

  Definition Bounds (base length : ty (Bit (Xlen + 1))) (isRoundDown : ty Bool) : LetExpr ty BoundsRes :=
    ( LetE lenTrunc : Bit (AddrSz + 1 - CapBSz) <- TruncMsb (AddrSz + 1 - CapBSz) CapBSz #length;
      LETE clz: Bit ExpSz <- countLeadingZerosArray (mkBoolArray (AddrSz + 1 - CapBSz) #lenTrunc) _;
      LetE e_init: Bit ExpSz <- Add [$(AddrSz + 2 - CapBSz); Not #clz];
      LetE d : Bit (CapBSz + 1) <- TruncLsb (AddrSz - CapBSz) (CapBSz + 1) (Srl #length #e_init);
      LetE mask_e : Bit (AddrSz + 2 - CapBSz) <- Not (Sll (ConstBit (Zmod.of_Z _ (-1))) #e_init);
      LetE base_mod_e : Bit (AddrSz + 2 - CapBSz) <-
                          And [TruncLsb (CapBSz - 1) (AddrSz + 2 - CapBSz) #base; #mask_e];
      LetE length_mod_e : Bit (AddrSz + 2 - CapBSz) <-
                            And [TruncLsb (CapBSz - 1) (AddrSz + 2 - CapBSz) #length; #mask_e];
      LetE sum_mod_e : Bit (AddrSz + 2 - CapBSz) <- Add [#base_mod_e; #length_mod_e];
      LetE iFloor : Bit 2 <- TruncLsb (AddrSz - CapBSz) 2 (Srl #sum_mod_e #e_init);
      LetE lost_sum : Bool <- isNotZero (And [#sum_mod_e; #mask_e]);
      LetE iCeil : Bit 2 <- Add [#iFloor; ZeroExtendTo 2 (ToBit #lost_sum)];
      LetE m_raw : Bit (CapBSz + 1) <- Add [#d; ZeroExtend (CapBSz-1) #iCeil];

      LetE b_e : Bool <- (mkBoolArray (AddrSz + 1) #base) @[ #e_init ];
      LetE isOverflow : Bool <- FromBit Bool (TruncMsb 1 CapBSz #m_raw);
      LetE e_unsat : Bit ExpSz <- Add [#e_init; ITE #isOverflow $1 $0];
      LetE isESaturated : Bool <- Sgt #e_unsat $(AddrSz - CapBSz);
      LetE e_normal : Bit ExpSz <- ITE #isESaturated $(AddrSz + 1 - CapBSz) #e_unsat;

      LetE m_raw_lsb : Bool <- FromBit Bool (TruncLsb CapBSz 1 #m_raw);
      LetE inc_ovf : Bool <- Or [#m_raw_lsb; #b_e];
      LetE m_ovf : Bit CapBSz <- {< Const _ (Bit (CapBSz - 1)) (Zmod.of_Z _ (2^(CapBSz - 2))) , ToBit #inc_ovf >};
      LetE m_normal : Bit CapBSz <- ITE #isOverflow #m_ovf (TruncLsb 1 CapBSz #m_raw);

      LETE e_b: Bit ExpSz <- countTrailingZerosArray (mkBoolArray (AddrSz + 1) #base) _;
      LetE pick_b: Bool <- Slt #e_b #e_init;
      LetE e_roundDown: Bit ExpSz <- ITE #pick_b #e_b #e_init;
      LetE m_roundDown: Bit CapBSz <- ITE #pick_b (Const ty (Bit CapBSz) (InvDefault _)) (TruncLsb 1 CapBSz #d);

      LetE ef: Bit ExpSz <- ITE #isRoundDown #e_roundDown #e_normal;
      LetE mf: Bit CapBSz <- ITE #isRoundDown #m_roundDown #m_normal;

      LetE cram: Bit (AddrSz + 1) <- Sll (ConstBit (Zmod.of_Z _ (-1))) #ef;
      LetE outBase : Bit (AddrSz + 1) <- And [#base; #cram];
      LetE outLen: Bit (AddrSz + 1) <- Sll (ZeroExtendTo (AddrSz + 1) #mf) #ef;
      LetE outTop : Bit (AddrSz + 1) <- Add [#outBase; #outLen] ;
      @RetE _ BoundsRes (STRUCT {
                          "E" ::= #ef;
                          "base" ::= #outBase;
                          "top" ::= #outTop;
                          "cram" ::= #cram;
                          "length" ::= #outLen;
                          "exact" ::= Or [isNotZero #base_mod_e; isNotZero #length_mod_e] })).

  (* If isArith is set for left shift, results are wrong *)
  Definition Shifter (val : ty (Bit Xlen)) (amt : ty (Bit 5)) (isRight isArith : ty Bool) : LetExpr ty (Bit Xlen) :=
    ( let rev e := ToBit (ArrayReverse (FromBit (Array (Z.to_nat Xlen) Bool) e)) in
      LetE inpVal : Bit Xlen <- ITE #isRight #val (rev #val) ;
      LetE signBit : Bit 1 <- ITE #isArith (TruncMsb 1 (Xlen - 1) #inpVal) (Const ty (Bit 1) Zmod.zero) ;
      LetE extVal : Bit (Xlen + 1) <- {< #signBit, #inpVal >} ;
      LetE shiftedExt : Bit (Xlen + 1) <- Sra #extVal #amt ;
      LetE shiftedXlen : Bit Xlen <- TruncLsb 1 Xlen #shiftedExt ;
      @RetE _ (Bit Xlen) (ITE #isRight #shiftedXlen (rev #shiftedXlen))
    ).

  Definition AdderBeforeRepCheck (base shifter : ty (Bit (Xlen + 1))) : LetExpr ty (Bit (Xlen + 1)) :=
    LetE repLimit : Bit (Xlen + 1) <- Add [ #base; #shifter ];
    RetE #repLimit.

  Definition ComparatorTopRep (addr topRep : ty (Bit (Xlen + 1))) (checkLte : ty Bool) : LetExpr ty ComparatorOut :=
    LetE ltRes : Bool <- Slt #addr #topRep;
    LetE eqRes : Bool <- Eq #addr #topRep;
    LetE lteRes : Bool <- Or [ #ltRes; #eqRes ];
    LetE outLt : Bool <- ITE #checkLte #lteRes #ltRes;
    @RetE _ ComparatorOut (STRUCT { "lt" ::= #outLt; "eq" ::= #eqRes }).

  Definition ComparatorBase (addr base : ty (Bit (Xlen + 1))) : LetExpr ty ComparatorOut :=
    LetE ltRes : Bool <- Slt #addr #base;
    LetE eqRes : Bool <- Eq #addr #base;
    @RetE _ ComparatorOut (STRUCT { "lt" ::= #ltRes; "eq" ::= #eqRes }).

  Definition AddrBoundsCheck (tag topLt baseLt baseEq : ty Bool) : LetExpr ty Bool :=
    LetE inBounds : Bool <- And [ #topLt; Or [ (Not #baseLt); #baseEq ] ];
    @RetE _ Bool (And [ #tag; #inBounds ]).

  Definition CapSubset (topLe baseGe tag1 tag2 : ty Bool) (perms1 perms2 : ty CapPerms) : LetExpr ty Bool :=
    LetE pAnd : CapPerms <- And [ #perms1; #perms2 ];
    LetE pEq : Bool <- Eq #pAnd #perms2;
    @RetE _ Bool (And [ #tag1; #tag2; #topLe; #baseGe; #pEq ]).

  Definition CapEq (addrEq tag1 tag2 : ty Bool) (ecap1 ecap2 : ty ECap) : LetExpr ty Bool :=
    LetE metaEq : Bool <- Eq #ecap1 #ecap2;
    LetE tagsEq : Bool <- Eq #tag1 #tag2;
    @RetE _ Bool (And [ #addrEq; #metaEq; #tagsEq ]).

  Definition ScrSanitizer (cs1 : ty FullECapWithTag) (inst : ty (Bit 32)) : LetExpr ty Bool :=
    LetE lsbZero : Bool <- Eq (TruncLsb (Xlen - 1) 1 (##cs1`"addr")) (Const ty (Bit 1) Zmod.zero);
    @RetE _ Bool (And [ ##cs1`"tag"; #lsbZero ]).

  Definition LoadUnitRes := STRUCT_TYPE {
    "Exception" :: Bool ;
    "LoadPostProcess" :: Bit 3 }.

  Definition LoadUnit (tag : ty Bool) (ecap : ty ECap) (inBounds : ty Bool) (loadOp : ty (Bit 3)) : LetExpr ty LoadUnitRes :=
    LetE exc : Bool <- Or [ (Not #tag); (Not #inBounds) ];
    @RetE _ LoadUnitRes (STRUCT { "Exception" ::= #exc; "LoadPostProcess" ::= #loadOp }).

  Definition StoreUnit (tag : ty Bool) (ecap : ty ECap) (inBounds : ty Bool) : LetExpr ty Bool :=
    LetE exc : Bool <- Or [ (Not #tag); (Not #inBounds) ];
    RetE #exc.

  (* ===========================================================================
     2. ROUTING & DATAPATH MULTIPLEXING BASED ON AluControl
     =========================================================================== *)

  Definition AluOut := STRUCT_TYPE {
    "NewPcc" :: FullECapWithTag ;
    "NewSpecial" :: FullECapWithTag ;
    "Reg" :: FullECapWithTag ;
    "Exception" :: Bool ;
    "LoadPostProcess" :: Bit 3 ;
    "NewInterruptStatus" :: Bool
  }.

  Definition aluRouting (aluControl : ty AluControl) : LetExpr ty AluOut :=
    LetE inst_val : Bit 32 <- ##inst ;

    LetE pccAddr : Bit Xlen <- ##pcc`"addr" ;
    LetE pccTag : Bool <- ##pcc`"tag" ;
    LetE pccBase : Bit (AddrSz + 1) <- ##pcc`"ecap"`"base" ;
    LetE pccExp : Bit ExpSz <- ##pcc`"ecap"`"E" ;

    LetE cs1Addr : Bit Xlen <- ##cs1`"addr" ;
    LetE cs1Tag : Bool <- ##cs1`"tag" ;
    LetE cs1Base : Bit (AddrSz + 1) <- ##cs1`"ecap"`"base" ;
    LetE cs1Top : Bit (AddrSz + 1) <- ##cs1`"ecap"`"top" ;
    LetE cs1Exp : Bit ExpSz <- ##cs1`"ecap"`"E" ;
    LetE cs1Perms : CapPerms <- ##cs1`"ecap"`"perms" ;
    LetE cs1OType : Bit CapOTypeSz <- ##cs1`"ecap"`"oType" ;

    LetE cs2Addr : Bit Xlen <- ##cs2`"addr" ;
    LetE cs2Tag : Bool <- ##cs2`"tag" ;
    LetE cs2Base : Bit (AddrSz + 1) <- ##cs2`"ecap"`"base" ;
    LetE cs2Top : Bit (AddrSz + 1) <- ##cs2`"ecap"`"top" ;
    LetE cs2Perms : CapPerms <- ##cs2`"ecap"`"perms" ;

    LetE specialAddr : Bit Xlen <- ##special`"addr" ;
    LetE specialTag : Bool <- ##special`"tag" ;

    LetE simm12 : Bit Xlen <- SignExtendTo Xlen (#inst_val`[31:20]) ;
    LetE zimm12 : Bit Xlen <- ZeroExtendTo Xlen (#inst_val`[31:20]) ;
    LetE uimm20 : Bit Xlen <- ({< #inst_val`[31:12], Const ty (Bit 12) Zmod.zero >}) ;
    LetE uimm20_11 : Bit Xlen <- ({< #inst_val`[31:31], #inst_val`[31:12], Const ty (Bit 11) Zmod.zero >}) ;
    LetE shamt : Bit 5 <- ConstExtract 7 5 20 #inst_val ;
    LetE bimm13 : Bit 13 <- ({< #inst_val`[31:31], #inst_val`[7:7], #inst_val`[30:25], #inst_val`[11:8], Const _ (Bit 1) Zmod.zero >}) ;
    LetE bimm12 : Bit Xlen <- SignExtendTo Xlen #bimm13 ;
    LetE jimm21 : Bit 21 <- ({< #inst_val`[31:31], #inst_val`[19:12], #inst_val`[20:20], #inst_val`[30:21], Const _ (Bit 1) Zmod.zero >}) ;
    LetE jimm20 : Bit Xlen <- SignExtendTo Xlen #jimm21 ;
    LetE LoadOp : Bit 3 <- ConstExtract 17 3 12 #inst_val ;

    (* AdderBeforeBoundsCheck Input Routing *)
    LetE AdderBeforeBoundsCheck_base : Bit Xlen <-
      ITE (##aluControl`"AdderBeforeBoundsCheck_base_isPccAddrNotCs1Addr") #pccAddr #cs1Addr ;
    LetE AdderBeforeBoundsCheck_offset : Bit Xlen <-
      caseDefault (k := Bit Xlen) [ (##aluControl`"AdderBeforeBoundsCheck_offset_bimm12", #bimm12) ;
                                    (##aluControl`"AdderBeforeBoundsCheck_offset_jimm20", #jimm20) ;
                                    (##aluControl`"AdderBeforeBoundsCheck_offset_uimm20_11", #uimm20_11) ;
                                    (##aluControl`"AdderBeforeBoundsCheck_offset_cs2Addr", #cs2Addr) ]
        #simm12 ;
    LETE AdderBeforeBoundsCheckOut : Bit Xlen <- AdderBeforeBoundsCheck AdderBeforeBoundsCheck_base AdderBeforeBoundsCheck_offset ;

    (* AdderToOutput Input Routing *)
    LetE AdderToOutput_base : Bit Xlen <-
      caseDefault (k := Bit Xlen) [ (##aluControl`"AdderToOutput_base_pccAddr", #pccAddr) ;
                                    (##aluControl`"AdderToOutput_base_cs1Top", TruncLsb 1 Xlen #cs1Top) ]
        #cs1Addr ;
    LetE AdderToOutput_offset : Bit Xlen <-
      caseDefault (k := Bit Xlen) [ (##aluControl`"AdderToOutput_offset_const2", Const ty (Bit Xlen) (Zmod.of_Z _ 2)) ;
                                    (##aluControl`"AdderToOutput_offset_cs2Addr", #cs2Addr) ;
                                    (##aluControl`"AdderToOutput_offset_simm12", #simm12) ;
                                    (##aluControl`"AdderToOutput_offset_cs1Base", TruncLsb 1 Xlen #cs1Base) ]
        (Const ty (Bit Xlen) (Zmod.of_Z _ 4)) ;
    LetE AdderToOutput_isSub : Bool <- ##aluControl`"AdderToOutput_isSub" ;
    LETE AdderToOutputOut : Bit Xlen <- AdderToOutput AdderToOutput_base AdderToOutput_offset AdderToOutput_isSub ;

    (* Add_CapBSz Input Routing *)
    LetE Add_CapBSz_baseExp : Bit ExpSz <-
      ITE (##aluControl`"Add_CapBSz_baseExp_isPccExpNotCs1Exp") #pccExp #cs1Exp ;
    LETE Add_CapBSzOut : Bit ExpSz <- Add_CapBSz Add_CapBSz_baseExp ;

    (* Shifter *)
    LetE Shifter_data : Bit Xlen <-
      ITE (##aluControl`"Shifter_data_isCs1AddrNotConst1") #cs1Addr (Const ty (Bit Xlen) (Zmod.of_Z _ 1)) ;
    LetE Shifter_shamt : Bit 5 <-
      caseDefault (k := Bit 5) [ (##aluControl`"Shifter_shamt_cs2Addr", TruncLsb (Xlen - 5) 5 #cs2Addr) ;
                                 (##aluControl`"Shifter_shamt_AddCapBSz", TruncLsb (ExpSz - 5) 5 #Add_CapBSzOut) ]
        #shamt ;
    LetE Shifter_isRight : Bool <- ##aluControl`"Shifter_isRight" ;
    LetE Shifter_isArith : Bool <- ##aluControl`"Shifter_isArith" ;
    LETE ShifterOut : Bit Xlen <- Shifter Shifter_data Shifter_shamt Shifter_isRight Shifter_isArith ;

    (* AdderBeforeRepCheck *)
    LetE AdderBeforeRepCheck_base : Bit (Xlen + 1) <-
      ITE (##aluControl`"AdderBeforeRepCheck_base_isPccBaseNotCs1Base") #pccBase #cs1Base ;
    LetE AdderBeforeRepCheck_shifter : Bit (Xlen + 1) <- ZeroExtendTo (Xlen + 1) #ShifterOut ;
    LETE AdderBeforeRepCheckOut : Bit (Xlen + 1) <- AdderBeforeRepCheck AdderBeforeRepCheck_base AdderBeforeRepCheck_shifter ;

    (* ComparatorTopRep *)
    LetE ComparatorTopRep_addr : Bit (Xlen + 1) <-
      caseDefault (k := Bit (Xlen + 1)) [ (##aluControl`"ComparatorTopRep_addr_AdderBeforeBoundsCheck", ZeroExtendTo (Xlen + 1) #AdderBeforeBoundsCheckOut) ;
                                          (##aluControl`"ComparatorTopRep_addr_cs1OType", ZeroExtendTo (Xlen + 1) #cs1OType) ;
                                          (##aluControl`"ComparatorTopRep_addr_cs1Top", #cs1Top) ]
        (ZeroExtendTo (Xlen + 1) #cs1Addr) ;
    LetE ComparatorTopRep_topRep : Bit (Xlen + 1) <-
      caseDefault (k := Bit (Xlen + 1)) [ (##aluControl`"ComparatorTopRep_topRep_AdderBeforeRepCheck", #AdderBeforeRepCheckOut) ;
                                          (##aluControl`"ComparatorTopRep_topRep_cs2Top", #cs2Top) ]
        #cs1Top ;
    LetE ComparatorTopRep_checkLte : Bool <- ##aluControl`"ComparatorTopRep_checkLte" ;
    LETE ComparatorTopRepOut : ComparatorOut <- ComparatorTopRep ComparatorTopRep_addr ComparatorTopRep_topRep ComparatorTopRep_checkLte ;

    (* ComparatorBase *)
    LetE ComparatorBase_addr : Bit (Xlen + 1) <-
      caseDefault (k := Bit (Xlen + 1)) [ (##aluControl`"ComparatorBase_addr_AdderBeforeBoundsCheck", ZeroExtendTo (Xlen + 1) #AdderBeforeBoundsCheckOut) ;
                                          (##aluControl`"ComparatorBase_addr_cs1OType", ZeroExtendTo (Xlen + 1) #cs1OType) ;
                                          (##aluControl`"ComparatorBase_addr_cs1Base", #cs1Base) ]
        (ZeroExtendTo (Xlen + 1) #cs1Addr) ;
    LetE ComparatorBase_base : Bit (Xlen + 1) <-
      caseDefault (k := Bit (Xlen + 1)) [ (##aluControl`"ComparatorBase_base_pccBase", #pccBase) ;
                                          (##aluControl`"ComparatorBase_base_cs2Base", #cs2Base) ]
        #cs1Base ;
    LETE ComparatorBaseOut : ComparatorOut <- ComparatorBase ComparatorBase_addr ComparatorBase_base ;

    (* AddrBoundsCheck *)
    LetE AddrBoundsCheck_tag : Bool <-
      ITE (##aluControl`"AddrBoundsCheck_tag_isPccTagNotCs1Tag") #pccTag #cs1Tag ;
    LetE AddrBoundsCheck_topLt : Bool <- ##ComparatorTopRepOut`"lt" ;
    LetE AddrBoundsCheck_baseLt : Bool <- ##ComparatorBaseOut`"lt" ;
    LetE AddrBoundsCheck_baseEq : Bool <- ##ComparatorBaseOut`"eq" ;
    LETE AddrBoundsCheckOut : Bool <- AddrBoundsCheck AddrBoundsCheck_tag AddrBoundsCheck_topLt AddrBoundsCheck_baseLt AddrBoundsCheck_baseEq ;

    LetE cs1ECap : ECap <- ##cs1`"ecap" ;

    (* SealerUnsealer *)
    LetE SealerUnsealer_isUnseal : Bool <- ##aluControl`"SealerUnsealer_isUnseal" ;
    LETE SealerUnsealerOut : TagECap <- SealerUnsealer SealerUnsealer_isUnseal AddrBoundsCheckOut cs1Tag cs1ECap cs2 ;

    (* ComparatorGeneral Input Routing *)
    LetE ComparatorGeneral_op1 : Bit Xlen <- #cs1Addr ;
    LetE ComparatorGeneral_op2 : Bit Xlen <-
      ITE (##aluControl`"ComparatorGeneral_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
    LetE ComparatorGeneral_isUnsigned : Bool <- ##aluControl`"ComparatorGeneral_isUnsigned" ;
    LetE ComparatorGeneral_checkLt    : Bool <- ##aluControl`"ComparatorGeneral_checkLt" ;
    LetE ComparatorGeneral_checkEq    : Bool <- ##aluControl`"ComparatorGeneral_checkEq" ;
    LetE ComparatorGeneral_invertRes  : Bool <- ##aluControl`"ComparatorGeneral_invertRes" ;
    LETE ComparatorGeneralOut : ComparatorOut <- ComparatorGeneral ComparatorGeneral_op1 ComparatorGeneral_op2 ComparatorGeneral_isUnsigned ComparatorGeneral_checkLt ComparatorGeneral_checkEq ComparatorGeneral_invertRes ;

    (* CjalrUnit *)
    LETE CjalrUnitOut : CjalrUnitRes <- CjalrUnit cs1 inst currInterruptStatus ;

    (* Logical Input Routing *)
    LetE Logical_op1 : Bit Xlen <- #cs1Addr ;
    LetE Logical_op2 : Bit Xlen <-
      ITE (##aluControl`"Logical_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
    LetE Logical_opSel : Bit 2 <- ##aluControl`"Logical_opSel" ;
    LETE LogicalOut : Bit Xlen <- Logical Logical_op1 Logical_op2 Logical_opSel ;

    (* CAndPerm Input Routing *)
    LETE CAndPermOut : TagECap <- CAndPerm cs1Tag cs1ECap cs2Addr ;

    (* Bounds *)
    LetE Bounds_reqLimit : Bit Xlen <-
      caseDefault (k := Bit Xlen) [ (##aluControl`"Bounds_reqLimit_cs2Addr", #cs2Addr) ;
                                    (##aluControl`"Bounds_reqLimit_cs1Addr", #cs1Addr) ]
        #zimm12 ;
    LetE Bounds_reqLimitExt : Bit (Xlen + 1) <- ZeroExtendTo (Xlen + 1) #Bounds_reqLimit ;
    LetE Bounds_isRoundDown : Bool <- ##aluControl`"Bounds_isRoundDown" ;
    LETE BoundsOut : BoundsRes <- Bounds cs1Base Bounds_reqLimitExt Bounds_isRoundDown ;

    (* CapSubset *)
    LETE CapSubsetOut : Bool <- CapSubset AddrBoundsCheck_topLt AddrBoundsCheck_baseLt cs1Tag cs2Tag cs1Perms cs2Perms ;

    (* CapEq *)
    LetE cs2ECap : ECap <- ##cs2`"ecap" ;
    LetE CapEq_generalEq : Bool <- ##ComparatorGeneralOut`"eq" ;
    LETE CapEqOut : Bool <- CapEq CapEq_generalEq cs1Tag cs2Tag cs1ECap cs2ECap ;

    (* ScrSanitizer *)
    LETE ScrSanitizerOut : Bool <- ScrSanitizer cs1 inst ;

    (* LoadUnit & StoreUnit *)
    LETE LoadUnitOut  : LoadUnitRes  <- LoadUnit cs1Tag cs1ECap AddrBoundsCheckOut LoadOp ;
    LETE StoreUnitOut : Bool <- StoreUnit cs1Tag cs1ECap AddrBoundsCheckOut ;

    (* =========================================================================
       WRITEBACK NETWORKS (WbControl defined via AluControl)
       ========================================================================= *)
    LetE NewPcc_tag : Bool <-
      ITE (##aluControl`"NewPcc_tag_isAddrBoundsCheckNotCjalrUnitTag") #AddrBoundsCheckOut (##CjalrUnitOut`"tag") ;
    LetE NewPcc_ecap : ECap <-
      ITE (##aluControl`"NewPcc_ecap_isCjalrUnitEcapNotPccEcap") (##CjalrUnitOut`"ecap") (##pcc`"ecap") ;
    LetE NewPcc_addr : Addr <-
      ITE (##aluControl`"NewPcc_addr_isAdderBeforeBoundsCheckNotAdderToOutput") #AdderBeforeBoundsCheckOut #AdderToOutputOut ;

    LetE NewSpecial_tag : Bool <- #ScrSanitizerOut ;

    LetE Reg_tag : Bool <-
      Or [ And [ ##aluControl`"Reg_tag_pccTag"         ; #pccTag ] ;
           And [ ##aluControl`"Reg_tag_cs1Tag"         ; #cs1Tag ] ;
           And [ ##aluControl`"Reg_tag_AddrBoundsCheck"; #AddrBoundsCheckOut ] ;
           And [ ##aluControl`"Reg_CAndPerm"           ; ##CAndPermOut`"tag" ] ;
           And [ ##aluControl`"Reg_SealerUnsealer"     ; ##SealerUnsealerOut`"tag" ] ;
           And [ ##aluControl`"Reg_tag_or_ecap_special"; #specialTag ] ] ;

    LetE Bounds_outECap : ECap <-
      (##cs1`"ecap") `{ "base" <- ##BoundsOut`"base" }
                     `{ "top"  <- ##BoundsOut`"top" }
                     `{ "E"    <- ##BoundsOut`"E" } ;

    LetE Reg_ecap : ECap <-
      caseDefault (k := ECap) [ (##aluControl`"Reg_ecap_pccEcap", ##pcc`"ecap") ;
                                (##aluControl`"Reg_ecap_cs1Ecap", ##cs1`"ecap") ;
                                (##aluControl`"Reg_ecap_cs2Addr", ##cs2`"ecap") ;
                                (##aluControl`"Reg_CAndPerm", ##CAndPermOut`"ecap") ;
                                (##aluControl`"Reg_SealerUnsealer", ##SealerUnsealerOut`"ecap") ;
                                (##aluControl`"Reg_ecap_or_addr_Bounds", #Bounds_outECap) ;
                                (##aluControl`"Reg_tag_or_ecap_special", ##special`"ecap") ]
        (Const ty ECap (getDefault _)) ;

    LetE Reg_addr : Data <-
      caseDefault (k := Data) [ (##aluControl`"Reg_addr_AdderBeforeBoundsCheck", #AdderBeforeBoundsCheckOut) ;
                                (##aluControl`"Reg_addr_ComparatorGeneralLt", ZeroExtendTo Xlen (ToBit (##ComparatorGeneralOut`"lt"))) ;
                                (##aluControl`"Reg_addr_Shifter", #ShifterOut) ;
                                (##aluControl`"Reg_addr_Logical", #LogicalOut) ;
                                (##aluControl`"Reg_addr_AdderToOutput", #AdderToOutputOut) ;
                                (##aluControl`"Reg_addr_cs1Fields", #cs1Addr) ;
                                (##aluControl`"Reg_addr_cs2Addr", #cs2Addr) ;
                                (##aluControl`"Reg_addr_cs1Addr", #cs1Addr) ;
                                (##aluControl`"Reg_ecap_or_addr_Bounds", TruncLsb 1 Xlen (##BoundsOut`"base")) ;
                                (##aluControl`"Reg_addr_BoundsCram", TruncLsb 1 Xlen (##BoundsOut`"cram")) ;
                                (##aluControl`"Reg_addr_BoundsCrrl", TruncLsb 1 Xlen (##BoundsOut`"length")) ;
                                (##aluControl`"Reg_addr_CapSubset", ZeroExtendTo Xlen (ToBit #CapSubsetOut)) ;
                                (##aluControl`"Reg_addr_CapEq", ZeroExtendTo Xlen (ToBit #CapEqOut)) ;
                                (##aluControl`"Reg_addr_specialAddr", #specialAddr) ]
        #uimm20 ;

    LetE ExceptionRes : Bool <-
      ITE (##aluControl`"Exception_isLoadUnitNotStoreUnit") (##LoadUnitOut`"Exception") #StoreUnitOut ;

    LetE LoadPostProcessRes : Bit 3 <- ##LoadUnitOut`"LoadPostProcess" ;

    LetE NewPccVal : FullECapWithTag <- STRUCT { "tag" ::= #NewPcc_tag ; "ecap" ::= #NewPcc_ecap ; "addr" ::= #NewPcc_addr } ;
    LetE NewSpecialVal : FullECapWithTag <- STRUCT { "tag" ::= #NewSpecial_tag ; "ecap" ::= ##cs1`"ecap" ; "addr" ::= #cs1Addr } ;
    LetE RegVal : FullECapWithTag <- STRUCT { "tag" ::= #Reg_tag ; "ecap" ::= #Reg_ecap ; "addr" ::= #Reg_addr } ;
    @RetE _ AluOut (STRUCT {
      "NewPcc" ::= #NewPccVal ;
      "NewSpecial" ::= #NewSpecialVal ;
      "Reg" ::= #RegVal ;
      "Exception" ::= #ExceptionRes ;
      "LoadPostProcess" ::= #LoadPostProcessRes ;
      "NewInterruptStatus" ::= ##CjalrUnitOut`"interruptStatus"
    }).
End Alu.
