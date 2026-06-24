
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
  * simm12    : 12-bit sign-extended immediate (arithmetic, loads/stores & CJALR offsets)
  * zimm12    : 12-bit zero-extended immediate (CSetBoundsImm)
  * uimm20    : 20-bit sign-extended upper immediate shifted left 12 bits (LUI)
  * uimm20_11 : 20-bit sign-extended upper immediate shifted left 11 bits (CHERIoT AUIPCC / AUICGP format)
  * bimm12    : 12-bit sign-extended branch offset (weird concatenation for branches with LSB 0)
  * jimm20    : 20-bit sign-extended jump offset (another weird concatenation for JAL with LSB 0)
  * shamt     : 5-bit shift amount
  * zimm5     : 5-bit zero-extended immediate (CSR manipulations)

Miscellaneous:
  * LoadOp    : generic load modifier (determines size and sign/zero extension)

Branch
* BEQ rs1, rs2, bimm12
* BNE rs1, rs2, bimm12
* BLT rs1, rs2, bimm12
* BGE rs1, rs2, bimm12
* BLTU rs1, rs2, bimm12
* BGEU rs1, rs2, bimm12
    Implicit Read : PCC
    Implicit Write: PCC.addr, PCC.tag
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
    Implicit Read : PCC
    Implicit Write: PCC.addr, PCC.tag
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
    Implicit Read : PCC
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
    Implicit Read : PCC
    Implicit Write: PCC
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
    Implicit Read : PCC.perms
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
    Implicit Read : MTCC, PCC
    Implicit Write: MEPCC, PCC, mcause
    Will cause exception
    Functional Units:
      a) None (direct register copy)

Mret
* MRET
    Implicit Read : MEPCC, PCC.perms
    Implicit Write: PCC
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
  Outputs: CjalrUnit.tag (unsealed sentry tag), CjalrUnit.ecap (unsealed capability metadata)
  inp1: cs1 (Cjalr)
  inp2: simm12 (Cjalr)

Logical:
  - AND : Logical (when AND/ANDI)
  - OR  : Logical (when OR/ORI)
  - XOR : Logical (when XOR/XORI)
  inp1: cs1.addr (Logical)
  inp2: cs2.addr (Logical), simm12 (Logical)

CAndPerm: Specialized bitwise permission masking unit.
  - MaskPerms : CAndPerm
  Outputs: CAndPerm.ecap (updated capability metadata word with masked permissions)
  inp1: cs1.perms (CAndPerm)
  inp2: cs2.addr (CAndPerm)

SealerUnsealer: Specialized capability sealing and unsealing verification unit.
  - Seal   : Seal (when CSeal)
  - Unseal : Seal (when CUnseal)
  Outputs: SealerUnsealer.ecap (sealed or unsealed capability metadata word)
  inp1: cs1 (Seal)
  inp2: cs2 (Seal)

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

NewSpecial.tag: ScrSanitizer (Scr)
NewSpecial.ecap: cs1.ecap (Scr)
NewSpecial.addr: cs1.addr (Scr)

Reg.tag: 0 (Lui, AddSub, Slt, Shift, Logical, CGet, CGetLen, Cram, Crrl,
            CSub, CSetEqual, CTestSubset, Csr, CSetHigh, CClearTag, Load, Store),
         pcc.tag (Cjal),
         cs1.tag (Cjalr, CMove, CAndPerm),
         AddrBoundsCheck (Aui, CIncAddr, CSetAddr, CSetBounds, Seal),
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
