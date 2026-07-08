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

(* TODO:
   - Create AluOutCompressed - has normal, branch/jump, csr/scr, exception, deferred in one tagged union
 *)

(*
1. INSTRUCTION GROUPS
-------------------------------------------------------------------------------
Immediate Formats:
  * simm12          : 12-bit sign-extended immediate (arithmetic, loads/stores & CJALR offsets)
  * zimm12          : 12-bit zero-extended immediate (CSetBoundsImm)
  * uimm20          : 20-bit sign-extended upper immediate shifted left 12 bits (LUI)
  * uimm20_11       : 20-bit sign-extended upper immediate shifted left 11 bits
                      (CHERIoT AUIPCC / AUICGP format)
  * bimm12          : 12-bit sign-extended branch offset
                      (weird concatenation for branches with LSB 0)
  * jimm20          : 20-bit sign-extended jump offset
                      (another weird concatenation for JAL with LSB 0)
  * shamt           : 5-bit shift amount
  * zimm5           : 5-bit zero-extended immediate (CSR manipulations)

Miscellaneous:
  * interruptStatus : Current interrupt status
  * isCompressed    : Whether the current instruction is compressed or not

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
      b) ComparatorGeneral (evaluating branch condition)
      c) AddCapBSz (computing representable limit exponent)
      d) Shifter (computing representable limit shift mask 1 << AddCapBSz)
      e) AdderBeforeRepCheck (computing representable upper limit address pcc.base + Shifter)
      f) ComparatorTopOrRep (checking representable upper limit
                             AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      g) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= pcc.base)
      h) AddrBoundsCheck (ands the two comparator outputs correctly)
      i) NewPcc (updates pcc address to AdderBeforeBoundsCheck, tag to AddrBoundsCheck)

Cjal
* CJAL cd, jimm20
    Implicit Read : pcc
    Implicit Write: pcc.addr, pcc.tag
    Functional Units:
      a) AdderBeforeBoundsCheck (computing jump target address PC + jimm20)
      b) AdderToOutput (computing return link address PC + 2 / PC + 4)
      c) AddCapBSz (computing representable limit exponent)
      d) Shifter (computing representable limit shift mask 1 << AddCapBSz)
      e) AdderBeforeRepCheck (computing representable upper limit address pcc.base + Shifter)
      f) ComparatorTopOrRep (checking representable upper limit
                             AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      g) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= pcc.base)
      h) AddrBoundsCheck (ands the two comparator outputs correctly)
      i) NewPcc (updates pcc address to AdderBeforeBoundsCheck, tag to AddrBoundsCheck)

AuiCgp/AuiPcc
* AUICGP cd, uimm20_11
    Implicit Read : c3 / CGP
* AUIPCC cd, uimm20_11
    Implicit Read : pcc
    Functional Units:
      a) AdderBeforeBoundsCheck (address calculation pcc.addr / cs1.addr + uimm20_11)
      b) AddCapBSz (computing representable limit exponent)
      c) Shifter (computing representable limit shift mask 1 << AddCapBSz)
      d) AdderBeforeRepCheck (computing representable upper limit address base + Shifter)
      e) ComparatorTopOrRep (checking representable upper limit
                             AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      f) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= base)
      g) AddrBoundsCheck (ands the two comparator outputs correctly)

CIncAddr
* CIncAddr cd, cs1, rs2
* CIncAddrImm cd, cs1, simm12
    Functional Units:
      a) AdderBeforeBoundsCheck (address calculation cs1.addr + rs2 / simm12)
      b) AddCapBSz (computing representable limit exponent)
      c) Shifter (computing representable limit shift mask 1 << AddCapBSz)
      d) AdderBeforeRepCheck (computing representable upper limit address cs1.base + Shifter)
      e) ComparatorTopOrRep (checking representable upper limit
                             AdderBeforeBoundsCheck <= AdderBeforeRepCheck)
      f) ComparatorBase (checking representable lower limit AdderBeforeBoundsCheck >= cs1.base)
      g) AddrBoundsCheck (ands the two comparator outputs correctly)

CSetAddr
* CSetAddr cd, cs1, rs2
    Functional Units:
      a) AddCapBSz (computing representable limit exponent)
      b) Shifter (computing representable limit shift mask 1 << AddCapBSz)
      c) AdderBeforeRepCheck (computing representable upper limit address cs1.base + Shifter)
      d) ComparatorTopOrRep (checking representable upper limit cs2.addr <= AdderBeforeRepCheck)
      e) ComparatorBase (checking representable lower limit cs2.addr >= cs1.base)
      f) AddrBoundsCheck (ands the two comparator outputs correctly)

Cjalr
* CJALR cd, cs1, simm12
    Implicit Read : pcc, interruptStatus
    Implicit Write: pcc, interruptStatus
    Note: This doesn't generate exceptions; just clears tag.
          The new MePrevPcc can help identify caller
    Functional Units:
      a) AdderBeforeBoundsCheck (computing jump target address cs1.addr + simm12)
      b) AdderToOutput (computing return link address PC + 2 / PC + 4)
      c) CjalrUnit (sentry legality / unsealing check unit)
      d) NewPcc (updates pcc address to AdderBeforeBoundsCheck, tag to CjalrUnit.tag, ecap to CjalrUnit.ecap)

CTestSubset
* CTestSubset rd, cs1, cs2
    Functional Units:
      a) ComparatorTopOrRep (checking top cs1.top <= cs2.top)
      b) ComparatorBase (checking base cs1.base >= cs2.base)
      c) CapSubset (validates top >= top2 AND base2 >= base AND permissions)

CSetBounds
* CSetBounds cd, cs1, rs2
* CSetBoundsExact cd, cs1, rs2
* CSetBoundsRoundDown cd, cs1, rs2
* CSetBoundsImm cd, cs1, zimm12
    Functional Units:
      a) AdderBeforeBoundsCheck (computing requested top address cs1.addr + rs2 / zimm12)
      b) Bounds (computing compressed bounds Bounds.base, Bounds.top, Bounds.E)
      c) ComparatorTopOrRep (verifying requested top AdderBeforeBoundsCheck <= cs1.top)
      d) ComparatorBase (verifying requested base >= cs1.base)
      e) AddrBoundsCheck (ands the two comparator outputs correctly)
      f) BoundsExact (checking if bounds are exact when CSetBoundsExact is used)

Seal
* CSeal cd, cs1, cs2
    Functional Units:
      a) SealerUnsealer (computing sealed capability metadata)
      b) ComparatorTopOrRep (checking top cs1.addr/cs1.otype < cs2.top)
      c) ComparatorBase (checking base cs1.addr/cs1.otype >= cs2.base)
      d) AddrBoundsCheck (ands the two comparator outputs correctly)

Unseal
* CUnseal cd, cs1, cs2
    Functional Units:
      a) SealerUnsealer (computing unsealed capability metadata)
      b) ComparatorTopOrRep (checking top cs1.addr/cs1.otype < cs2.top)
      c) ComparatorBase (checking base cs1.addr/cs1.otype >= cs2.base)
      d) AddrBoundsCheck (ands the two comparator outputs correctly)

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
      b) ComparatorTopOrRep (checking top AdderBeforeBoundsCheck < cs1.top)
      c) ComparatorBase (checking base AdderBeforeBoundsCheck >= cs1.base)
      d) AddrBoundsCheck (ands the two comparator outputs correctly)
      e) Deferred (outputs memory operation info, address, and LG/LM)
      f) Exception (outputs exception if bounds/tag/permission/alignment violation)

Store
* SB rs2, simm12(cs1)
* SH rs2, simm12(cs1)
* SW rs2, simm12(cs1)
* SC cs2, simm12(cs1)
    Can cause exceptions
    Functional Units:
      a) AdderBeforeBoundsCheck (memory address cs1.addr + simm12)
      b) ComparatorTopOrRep (checking top AdderBeforeBoundsCheck < cs1.top)
      c) ComparatorBase (checking base AdderBeforeBoundsCheck >= cs1.base)
      d) AddrBoundsCheck (ands the two comparator outputs correctly)
      e) EncodeCap (compresses cs2.ecap into cs2.cap for storing)
      f) Deferred (outputs memory operation info, address, and cap data)
      g) Exception (outputs exception if bounds/tag/permission/alignment violation)

AddSub
* ADD rd, rs1, rs2
* SUB rd, rs1, rs2
* ADDI rd, rs1, simm12
* CSub rd, cs1, cs2
    Functional Units:
      a) AdderToOutput (arithmetic calculation)

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
    Note: Decode can cause exceptions for accessing certain CSRs if no ASR
    Functional Units:
      None (direct CSR read routing)

Scr
* CSpecialRw cd, cSpecial, cs1
    Implicit Read : pcc.perms
    Note: Decoder will cause exceptions if no ASR
    Note: ScrSanitizer will untag invalid capability, but not overwrite ecap
    Note: ScrSanitizer only checks for LSB = 1'b0 for MePcc, Mtcc and MePrevPcc
    Functional Units:
      a) ScrSanitizer (check if the last LSB bit is 0 for certain SCR writes)

Lui
* LUI rd, uimm20
    Functional Units:
      None (direct immediate routing)

CGetPerm
* CGetPerm rd, cs1
    Functional Units:
      None (direct field extraction)

CGetType
* CGetType rd, cs1
    Functional Units:
      None (direct field extraction)

CGetBase
* CGetBase rd, cs1
    Functional Units:
      None (direct field extraction)

CGetTag
* CGetTag rd, cs1
    Functional Units:
      None (direct field extraction)

CGetAddr
* CGetAddr rd, cs1
    Functional Units:
      None (direct field extraction)

CGetHigh
* CGetHigh rd, cs1
    Functional Units:
      a) EncodeCap (computing compressed Cap from cs1.ecap)

CGetTop
* CGetTop rd, cs1
    Functional Units:
      None (direct field extraction)

CSetHigh
* CSetHigh cd, cs1, rs2
    Functional Units:
      a) DecodeCap (computing full ECap from rs2 (as Cap) and cs1.addr)

CClearTag
* CClearTag cd, cs1
    Functional Units:
      None (direct tag clearing)

CMove
* CMove cd, cs1
    Functional Units:
      None (direct register copy)

ECall
* ECALL
    Implicit Read : MTCC, pcc
    Implicit Write: MEPCC, pcc, mcause (8)
    Note: Will cause exception
    Functional Units:
      a) Exception (outputs exception with cause EXC_ECallM)

EBreak
* EBREAK
    Implicit Read : MTCC, pcc
    Implicit Write: MEPCC, pcc, mcause (3)
    Note: Will cause exception
    Functional Units:
      a) Exception (outputs exception with cause EXC_Breakpoint)

Mret
* MRET
    Implicit Read : MEPCC, pcc.perms
    Implicit Write: pcc
    Note: Decoder will cause exceptions if no ASR
    Functional Units:
      a) NewPcc (updates pcc address to cs2Addr)

Fence
* FENCE
* FENCE.I
* FENCE.TSO
    Functional Units:
      a) Deferred (outputs fence operation info)

-------------------------------------------------------------------------------
2. FUNCTIONAL UNIT/RESOURCE MAPPING
-------------------------------------------------------------------------------
AdderBeforeBoundsCheck:
  - ADD : Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetBounds, Cjalr, Load, Store
  base: pcc.addr (Branch, Cjal, AuiPcc),
        cs1.addr (AuiCgp, CIncAddr, CSetBounds, Cjalr, Load, Store)
  offset: bimm12 (Branch), jimm20 (Cjal), uimm20_11 (AuiPcc, AuiCgp),
        cs2.addr (CIncAddr & !isImm, CSetBounds & !isImm),
        zimm12 (CSetBounds & isImm),
        simm12 (Cjalr, Load, Store, CIncAddr & isImm)

AdderToOutput:
  - ADD : Cjal, Cjalr, AddSub (when ADD/ADDI)
  - SUB : AddSub (when SUB/CSub), CGetLen
  base: pcc.addr (Cjal, Cjalr), cs1.addr (AddSub),
        cs1.top (CGetLen)
  offset: 2 (Cjal, Cjalr) IF Compressed, 4 (Cjal, Cjalr) IF !Compressed,
        cs2.addr (AddSub & !isImm), simm12 (AddSub & isImm), cs1.base (CGetLen)

AddCapBSz:
  - ADD_CapBSz : Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr
  baseExp: pcc.exp (Branch, Cjal, AuiPcc), cs1.exp (AuiCgp, CIncAddr, CSetAddr)

ComparatorGeneral:
  - EQ         : Branch (when BEQ/BNE), CSetEqual
  - LTSigned   : Branch (when BLT/BGE), Slt (when SLT/SLTI)
  - LTUnsigned : Branch (when BLTU/BGEU), Slt (when SLTU/SLTIU)
  - Invert     : Branch (when BNE, BGE, BGEU)
  Outputs: cond, eq
  op1: cs1.addr (Branch, Slt, CSetEqual)
  op2: cs2.addr (Branch, Slt & !isImm, CSetEqual), simm12 (Slt & isImm)

CjalrUnit:
  - CheckSentryAndUnseal : Cjalr
  Outputs: tag, ecap, interruptStatus
  cs1: cs1 (Cjalr)
  inst: inst (Cjalr)
  currIntStatus: currInterruptStatus (Cjalr)

Logical:
  - AND : Logical (when AND/ANDI)
  - OR  : Logical (when OR/ORI)
  - XOR : Logical (when XOR/XORI)
  op1: cs1.addr (Logical)
  op2: cs2.addr (Logical & !isImm), simm12 (Logical & isImm)

CAndPerm:
  - MaskPerms : CAndPerm
  Outputs: tag, ecap
  tag: cs1.tag (CAndPerm)
  ecap: cs1.ecap (CAndPerm)
  cs2Addr: cs2.addr (CAndPerm)

SealerUnsealer:
  - Seal   : Seal
  - Unseal : Unseal
  Outputs: tag, ecap
  tag: cs1.tag (Seal, Unseal)
  ecap: cs1.ecap (Seal, Unseal)
  cs2: cs2 (Seal, Unseal)
  inBounds: AddrBoundsCheck (Seal, Unseal)

Bounds:
  - SetBounds   : CSetBounds
  - ComputeCram : Cram
  - ComputeCrrl : Crrl
  - RoundDown   : CSetBounds (when CSetBoundsRoundDown)
  Outputs: base, length, top, E, cram, crrl
  base: cs1.addr (CSetBounds, Cram, Crrl)
  length: cs2.addr (CSetBounds & !isImm), zimm12 (CSetBounds & isImm), cs1.addr (Cram, Crrl)

BoundsExact:
  - CalcBoundsExactTag : CSetBounds (when CSetBoundsExact)
  inBounds: AddrBoundsCheck (CSetBounds)
  boundsAreExact: Bounds.exact (CSetBounds)

Shifter:
  - ShiftLeftLogical     : Shift (when SLL/SLLI), Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr
  - ShiftRightLogical    : Shift (when SRL/SRLI)
  - ShiftRightArithmetic : Shift (when SRA/SRAI)
  data: cs1.addr (Shift), 1 (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr)
  shamt: cs2.addr (Shift & !isImm), shamt (Shift & isImm),
        AddCapBSz (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr)

AdderBeforeRepCheck:
  - ADD : Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr
  base: pcc.base (Branch, Cjal, AuiPcc), cs1.base (AuiCgp, CIncAddr, CSetAddr)
  shifter: Shifter (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr)

ComparatorTopOrRep:
  - LTEUnsigned : CTestSubset, CSetBounds
  - LTUnsigned  : Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr, Load, Store, Seal, Unseal
  Outputs: lt, eq
  addr: AdderBeforeBoundsCheck (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetBounds, Load, Store),
        cs2.addr (Seal, CSetAddr), cs1.otype (Unseal), cs1.top (CTestSubset)
  topRep: AdderBeforeRepCheck (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr),
        cs1.top (CSetBounds, Load, Store), cs2.top (Seal, Unseal, CTestSubset)

ComparatorBase:
  - GTEUnsigned : Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr, CSetBounds, Seal, Unseal, Load, Store,
                  CTestSubset
  addr: AdderBeforeBoundsCheck (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, Load, Store),
        cs2.addr (Seal, CSetAddr), cs1.otype (Unseal), cs1.addr (CSetBounds), cs1.base (CTestSubset)
  base: pcc.base (Branch, Cjal, AuiPcc),
        cs1.base (AuiCgp, CIncAddr, CSetAddr, CSetBounds, Load, Store),
        cs2.base (Seal, Unseal, CTestSubset)

AddrBoundsCheck:
  - CheckInBounds : Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal, Unseal
                    (ands the two comparator outputs correctly)
  tag: cs1.tag (AuiCgp, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal, Unseal),
        pcc.tag (Branch, Cjal, AuiPcc)
  topLt: ComparatorTopOrRep.lt
        (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal, Unseal)
  baseGe: ComparatorBase
        (Branch, Cjal, AuiPcc, AuiCgp, CIncAddr, CSetAddr, CSetBounds, Load, Store, Seal, Unseal)

CapSubset:
  - Subset : CTestSubset
  topLe: ComparatorTopOrRep.lt (CTestSubset), ComparatorTopOrRep.eq (CTestSubset)
  baseGe: ComparatorBase (CTestSubset)
  perms1: cs1.perms (CTestSubset)
  perms2: cs2.perms (CTestSubset)
  tag1: cs1.tag (CTestSubset)
  tag2: cs2.tag (CTestSubset)

CapEq:
  - Eq : CSetEqual
  addrEq: ComparatorGeneral.eq (CSetEqual)
  tag1: cs1.tag (CSetEqual)
  tag2: cs2.tag (CSetEqual)
  ecap1: cs1.ecap (CSetEqual)
  ecap2: cs2.ecap (CSetEqual)

ScrSanitizer:
  - SanitizeTag : Scr
  tag: cs1.tag (Scr)
  addr: cs1.addr (Scr)
  inst: inst (Scr)

EncodeCap:
  - Compress : CGetHigh, Store
  Outputs: cap
  ecap: cs1.ecap (CGetHigh), cs2.ecap (Store)

DecodeCap:
  - Decompress : CSetHigh
  Outputs: ecap
  cap: cs2.addr (CSetHigh)
  addr: cs1.addr (CSetHigh)

Deferred (Output):
  - Load   : Load
  - Store  : Store
  - Fence  : Fence
  Outputs: MemOp {addr, memSize, LoadOp {isUnsigned, isLM, isLG} | Store {tag, cap, addr}} OR
           FenceOp {isFenceI, RR, RW, WR, WW}
  storeCap: cs2.tag, EncodeCap, cs2.addr (Store)
  cs1Perms: cs1.perms (Load)
  inst: inst (Load, Store, Fence)
  addr: AdderBeforeBoundsCheck (Load, Store)

Exception (Output):
  - ECall  : ECall
  - EBreak : EBreak
  - Load   : Load
  - Store  : Store
  Outputs: isException, mcause, isScr, regIdx, mtval
  fetchExc: fetchExc (all)
  decodeExc: decodeExc (all)
  inst: inst (all)
  cs1Tag: cs1.tag (Load, Store)
  cs1ECap: cs1.ecap (Load, Store)
  inBounds: AddrBoundsCheck (Load, Store)
  addr: AdderBeforeBoundsCheck (Load, Store)

NewPcc (Output):
  - Mret   : Mret
  - Cjal   : Cjal
  - Cjalr  : Cjalr
  - Branch : Branch
  Outputs: tag, ecap, addr, Addr_change, Ecap_change
  isCond: ComparatorGeneral.cond (Branch)
  cs2: cs2 (Mret)
  addrIn: AdderBeforeBoundsCheck (Branch, Cjal, Cjalr)
  inBounds: AddrBoundsCheck (Branch, Cjal)
  cjalrTag: CjalrUnit.tag (Cjalr)
  cjalrEcap: CjalrUnit.ecap (Cjalr)
  pccTag: pcc.tag (all)

NewPcc
Exception
Deferred

NewInterruptStatus: CjalrUnit.interruptStatus (Cjalr), currInterruptStatus (others)

NewSpecial.tag: ScrSanitizer (Scr)
NewSpecial.ecap: cs1.ecap (Scr)
NewSpecial.addr: cs1.addr (Scr)

Reg.tag: 0 (Lui, AddSub, Slt, Shift, Logical, CGetPerm, CGetType, CGetBase, CGetTag, CGetAddr, CGetHigh,
            CGetTop, CGetLen, Cram, Crrl, CSetEqual, CTestSubset, Csr, CSetHigh, CClearTag, Load, Store),
         pcc.tag (Cjal),
         cs1.tag (Cjalr, CMove),
         cs2.tag (Scr),
         AddrBoundsCheck (AuiPcc, AuiCgp, CIncAddr, CSetAddr),
         BoundsExact (CSetBounds),
         CAndPerm.tag (CAndPerm),
         SealerUnsealer.tag (Seal, Unseal)

Reg.ecap: 0 (Lui, AddSub, Slt, Shift, Logical, CGetPerm, CGetType, CGetBase, CGetTag, CGetAddr, CGetHigh,
             CGetTop, CGetLen, Cram, Crrl, CSetEqual, CTestSubset, Csr, Load, Store),
          pcc.ecap (AuiPcc, Cjal, Cjalr),
          cs1.ecap (AuiCgp, CIncAddr, CSetAddr, CClearTag, CMove),
          DecodeCap (CSetHigh), cs2.ecap (Scr), CAndPerm.ecap (CAndPerm),
          SealerUnsealer.ecap (Seal, Unseal),
          {cs1.R, cs1.perms, cs1.otype, Bounds.E, Bounds.top, Bounds.base} (CSetBounds)

Reg.addr: uimm20 (Lui), AdderBeforeBoundsCheck (AuiPcc, AuiCgp, CIncAddr, Load, Store),
          ComparatorGeneral.cond (Slt), Shifter (Shift), Logical (Logical),
          AdderToOutput (Cjal, Cjalr, AddSub, CGetLen),
          cs1.perms (CGetPerm), cs1.otype (CGetType), cs1.base (CGetBase), cs1.tag (CGetTag),
          cs1.addr (CGetAddr), EncodeCap (CGetHigh), cs1.top (CGetTop), zimm5 (Csr & isImm),
          cs2.addr (CSetAddr, Csr & !isImm, Scr), cs1.addr (CAndPerm, CClearTag, Seal, Unseal, CMove, CSetHigh),
          Bounds.base (CSetBounds), Bounds.cram (Cram), Bounds.crrl (Crrl),
          CapSubset (CTestSubset), CapEq (CSetEqual)
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
  (* NewPcc_tag_cs2Tag = Scr *)
  (* NewPcc_tag_CjalrUnitTag = Cjalr *)
  (* EncodeCap_ecap_isCs2EcapNotCs1Ecap = Store *)
  (* NewPcc_ecap_cs2Ecap = Scr *)
  (* NewPcc_ecap_CjalrUnitEcap = Cjalr *)
  (* NewPcc_addr_cs2Addr = Mret *)
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
  (* Reg_addr_CGetPerm = CGetPerm *)
  (* Reg_addr_CGetType = CGetType *)
  (* Reg_addr_CGetBase = CGetBase *)
  (* Reg_addr_CGetTag = CGetTag *)
  (* Reg_addr_CGetAddr = CGetAddr *)
  (* Reg_addr_CGetHigh = CGetHigh *)
  (* Reg_addr_CGetTop = CGetTop *)
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

Section DecodeInstGroup.
  Variable ty : Kind -> Type.
  Variable group : ty InstGroup.

  Definition decodeInstGroup : LetExpr ty AluControl :=
    RetE (STRUCT {
      "AdderBeforeBoundsCheck_offset_uimm20_11" ::= Or [ ##group`"AuiPcc"; ##group`"AuiCgp" ] ;
      "AdderBeforeBoundsCheck_offset_cs2Addr" ::=
        Or [ And [ ##group`"CIncAddr"; Not ##group`"isImm" ];
             And [ ##group`"CSetBounds"; Not ##group`"isImm" ] ] ;
      (* "AdderBeforeBoundsCheck_offset_simm12" ::=
        Or [ ##group`"Cjalr"; ##group`"Load"; ##group`"Store";
             And [ ##group`"CIncAddr"; ##group`"isImm" ] ] ; *)
      "AdderToOutput_base_pccAddr" ::=
        Or [ ##group`"Cjal"; ##group`"Cjalr" ] ;
      "AdderToOutput_offset_const2" ::=
        And [ ##group`"isCompressed";
              Or [ ##group`"Cjal"; ##group`"Cjalr" ] ] ;
      (* "AdderToOutput_offset_const4" ::=
        And [ Not ##group`"isCompressed";
              Or [ ##group`"Cjal"; ##group`"Cjalr" ] ] ; *)
      "AdderToOutput_offset_cs2Addr" ::= And [ ##group`"AddSub"; Not ##group`"isImm" ] ;
      "AdderToOutput_offset_simm12" ::= And [ ##group`"AddSub"; ##group`"isImm" ] ;
      "AdderToOutput_isSub" ::= Or [ And [ ##group`"AddSub"; ##group`"AddSub_isSub" ]; ##group`"CGetLen" ] ;
      "ComparatorGeneral_op2_isCs2AddrNotSimm12" ::=
        Or [ ##group`"Branch"; ##group`"CSetEqual";
              And [ ##group`"Slt"; Not ##group`"isImm" ] ] ;
      "ComparatorGeneral_checkLt" ::= ##group`"ComparatorGeneral_checkLt" ;
      "ComparatorGeneral_checkEq" ::= ##group`"ComparatorGeneral_checkEq" ;
      "ComparatorGeneral_invertRes" ::= ##group`"ComparatorGeneral_invertRes" ;
      "Logical_op2_isCs2AddrNotSimm12" ::= And [ ##group`"Logical"; Not ##group`"isImm" ] ;
      "Bounds_reqLimit_cs2Addr" ::= And [ ##group`"CSetBounds"; Not ##group`"isImm" ] ;
      "Bounds_reqLimit_cs1Addr" ::= Or [ ##group`"Cram"; ##group`"Crrl" ] ;
      "Bounds_isRoundDown" ::= ##group`"CSetBounds_isRoundDown" ;
      "Bounds_isExact" ::= ##group`"CSetBounds_isExact" ;
      "Bounds_isImm" ::= And [ ##group`"CSetBounds"; ##group`"isImm" ] ;
      "Shifter_shamt_cs2Addr" ::= And [ ##group`"Shift"; Not ##group`"isImm" ] ;
      (* "Shifter_shamt_shamt" ::= And [ ##group`"Shift"; ##group`"isImm" ] ; *)
      "Shifter_isArith" ::= ##group`"Shift_isArith" ;
      "Shifter_isRight" ::= ##group`"Shift_isRight" ;
      "ComparatorTopOrRep_addr_AdderBeforeBoundsCheck" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetBounds"; ##group`"Load";
             ##group`"Store" ] ;
      (* "ComparatorTopOrRep_addr_cs1Addr" ::= ConstTBool false ; *)
      (* "ComparatorTopOrRep_topRep_cs1Top" ::=
        Or [ ##group`"CSetBounds"; ##group`"Load"; ##group`"Store" ] ; *)
      "ComparatorTopOrRep_checkLte" ::= Or [ ##group`"CTestSubset"; ##group`"CSetBounds" ] ;
      "ComparatorBase_addr_AdderBeforeBoundsCheck" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"Load"; ##group`"Store" ] ;
      (* "ComparatorBase_base_cs1Base" ::=
        Or [ ##group`"AuiCgp"; ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CSetBounds";
             ##group`"Load"; ##group`"Store" ] ; *)

      "Reg_tag_cs1Tag" ::= Or [ ##group`"Cjalr"; ##group`"CMove" ] ;
      "Reg_tag_AddrBoundsCheck" ::=
        Or [ ##group`"AuiPcc"; ##group`"AuiCgp"; ##group`"CIncAddr"; ##group`"CSetAddr" ] ;

      "Reg_ecap_pccEcap" ::= Or [ ##group`"AuiPcc"; ##group`"Cjal"; ##group`"Cjalr" ] ;
      "Reg_ecap_cs1Ecap" ::=
        Or [ ##group`"AuiCgp"; ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CClearTag";
             ##group`"CMove" ] ;
      "Reg_addr_AdderBeforeBoundsCheck" ::=
        Or [ ##group`"AuiPcc"; ##group`"AuiCgp"; ##group`"CIncAddr"; ##group`"Load";
             ##group`"Store" ] ;
      "Reg_addr_AdderToOutput" ::=
        Or [ ##group`"Cjal"; ##group`"Cjalr"; ##group`"AddSub"; ##group`"CGetLen" ] ;
      "Reg_addr_cs2Addr" ::= Or [ ##group`"CSetAddr"; ##group`"Scr"; And [ ##group`"Csr"; Not ##group`"isImm" ] ] ;
      "Reg_addr_zimm5" ::= And [ ##group`"Csr"; ##group`"isImm" ] ;
      "Reg_addr_cs1Addr" ::=
        Or [ ##group`"CClearTag"; ##group`"CMove"; ##group`"CSetHigh" ] ;
      "ECall" ::= ##group`"ECall" ;
      "EBreak" ::= ##group`"EBreak" ;
      "Load" ::= ##group`"Load" ;
      "Store" ::= ##group`"Store" ;
      "Fence" ::= ##group`"Fence" ;
      "Branch" ::= ##group`"Branch" ;
      "Cjal" ::= ##group`"Cjal" ;
      "AddSub" ::= ##group`"AddSub" ;
      "CGetLen" ::= ##group`"CGetLen" ;
      "Unseal" ::= ##group`"Unseal" ;
      "Shift" ::= ##group`"Shift" ;
      "CTestSubset" ::= ##group`"CTestSubset" ;
      "CSetBounds" ::= ##group`"CSetBounds" ;
      "Mret" ::= ##group`"Mret" ;
      "Cjalr" ::= ##group`"Cjalr" ;
      "Scr" ::= ##group`"Scr" ;
      "CAndPerm" ::= ##group`"CAndPerm" ;
      "isUnsigned" ::= ##group`"isUnsigned" ;
      "Lui" ::= ##group`"Lui" ;
      "Slt" ::= ##group`"Slt" ;
      "Logical" ::= ##group`"Logical" ;
      "CGetPerm" ::= ##group`"CGetPerm" ;
      "CGetType" ::= ##group`"CGetType" ;
      "CGetBase" ::= ##group`"CGetBase" ;
      "CGetTag" ::= ##group`"CGetTag" ;
      "CGetAddr" ::= ##group`"CGetAddr" ;
      "CGetHigh" ::= ##group`"CGetHigh" ;
      "CGetTop" ::= ##group`"CGetTop" ;
      "Cram" ::= ##group`"Cram" ;
      "Crrl" ::= ##group`"Crrl" ;
      "CSetEqual" ::= ##group`"CSetEqual" ;
      "CSetHigh" ::= ##group`"CSetHigh" ;
      "BranchOrCjalOrAuiPcc" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc" ] ;
      "BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr" ] ;
      "SealOrSetAddr" ::= Or [ ##group`"Seal"; ##group`"CSetAddr" ] ;
      "SealOrUnsealOrSubset" ::=
        Or [ ##group`"CTestSubset"; ##group`"Seal"; ##group`"Unseal" ] ;
      "SealOrUnseal" ::= Or [ ##group`"Seal"; ##group`"Unseal" ]
    }).
End DecodeInstGroup.

Section GetFunctionalUnits.
  Variable ty : Kind -> Type.
  Variable group : ty InstGroup.

  Definition getFunctionalUnitsForInstGroup : LetExpr ty FunctionalUnits :=
    RetE (STRUCT {
      "AdderBeforeBoundsCheck" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"Cjalr"; ##group`"CSetBounds";
             ##group`"Load"; ##group`"Store" ] ;
      "AdderToOutput" ::= Or [ ##group`"Cjal"; ##group`"Cjalr"; ##group`"AddSub"; ##group`"CGetLen" ] ;
      "AddCapBSz" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr" ] ;
      "ComparatorGeneral" ::= Or [ ##group`"Branch"; ##group`"Slt"; ##group`"CSetEqual" ] ;
      "CjalrUnit" ::= ##group`"Cjalr" ;
      "Logical" ::= ##group`"Logical" ;
      "CAndPerm" ::= ##group`"CAndPerm" ;
      "SealerUnsealer" ::= Or [ ##group`"Seal"; ##group`"Unseal" ] ;
      "Bounds" ::= Or [ ##group`"CSetBounds"; ##group`"Cram"; ##group`"Crrl" ] ;
      "BoundsExact" ::= ##group`"CSetBounds_isExact" ;
      "Shifter" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"Shift" ] ;
      "AdderBeforeRepCheck" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr" ] ;
      "ComparatorTopOrRep" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CTestSubset";
             ##group`"CSetBounds"; ##group`"Seal"; ##group`"Unseal";
             ##group`"Load"; ##group`"Store" ] ;
      "ComparatorBase" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CTestSubset";
             ##group`"CSetBounds"; ##group`"Seal"; ##group`"Unseal";
             ##group`"Load"; ##group`"Store" ] ;
      "AddrBoundsCheck" ::=
        Or [ ##group`"Branch"; ##group`"Cjal"; ##group`"AuiPcc"; ##group`"AuiCgp";
             ##group`"CIncAddr"; ##group`"CSetAddr"; ##group`"CSetBounds";
             ##group`"Seal"; ##group`"Unseal"; ##group`"Load"; ##group`"Store" ] ;
      "CapSubset" ::= ##group`"CTestSubset" ;
      "CapEq" ::= ##group`"CSetEqual" ;
      "ScrSanitizer" ::= ##group`"Scr" ;
      "EncodeCap" ::= Or [ ##group`"CGetHigh"; ##group`"Store" ] ;
      "DecodeCap" ::= ##group`"CSetHigh" ;
      "Deferred" ::= Or [ ##group`"Load"; ##group`"Store"; ##group`"Fence" ] ;
      "Exception" ::= Or [ ##group`"Load"; ##group`"Store"; ##group`"ECall"; ##group`"EBreak" ] ;
      "NewPcc" ::= Or [ ##group`"Mret"; ##group`"Cjal"; ##group`"Cjalr"; ##group`"Branch" ]
    }).
End GetFunctionalUnits.

Section Alu.
  Variable ty : Kind -> Type.

  Definition AdderBeforeBoundsCheck (base offset : ty (Bit Xlen)) : LetExpr ty (Bit Xlen) :=
    LetE sum : Bit Xlen <- Add [ #base; #offset ];
    RetE #sum.

  Definition AdderToOutput (base offset : ty (Bit Xlen)) (isSub : ty Bool) : LetExpr ty (Bit Xlen) :=
    LetE op2 : Bit Xlen <- ITE #isSub (Not #offset) #offset;
    LetE cin : Bit Xlen <- ZeroExtendTo Xlen (ToBit #isSub);
    LetE sum : Bit Xlen <- Add [ #base; #op2; #cin ];
    RetE #sum.

  Definition AddCapBSz (baseExp : ty (Bit ExpSz)) : LetExpr ty (Bit ExpSz) :=
    LetE sum : Bit ExpSz <- Add [ #baseExp; $CapBSz ];
    RetE #sum.

  Definition ComparatorGeneralRes := STRUCT_TYPE {
    "cond" :: Bool ;
    "eq"   :: Bool }.

  Definition ComparatorGeneral (op1 op2 : ty (Bit Xlen)) (isUnsigned checkLt checkEq invertRes : ty Bool)
  : LetExpr ty ComparatorGeneralRes :=
    LetE flipBit : Bit 1 <- ToBit (Not #isUnsigned) ;
    let flipMsb e:= {< Xor [#flipBit; TruncMsb 1 (Xlen-1) e], TruncLsb 1 (Xlen-1) e >} in
    LetE op1_flipped : Bit Xlen <- flipMsb #op1 ;
    LetE op2_flipped : Bit Xlen <- flipMsb #op2 ;
    LetE ltRes : Bool <- Slt #op1_flipped #op2_flipped;
    LetE eqRes : Bool <- Eq #op1 #op2;
    LetE cond  : Bool <- Or [ And [ #checkLt; #ltRes ]; And [ #checkEq; #eqRes ] ];
    LetE finalRes : Bool <- ITE #invertRes (Not #cond) #cond;
    @RetE _ ComparatorGeneralRes (STRUCT { "cond" ::= #finalRes; "eq" ::= #eqRes }).

  Definition CjalrUnitRes := STRUCT_TYPE {
    "tag"             :: Bool;
    "ecap"            :: ECap;
    "interruptStatus" :: Bool }.

  Definition CjalrUnit (cs1 : ty FullECapWithTag) (inst : ty Inst) (currIntStatus : ty Bool)
  : LetExpr ty CjalrUnitRes :=
    LetE cs1Tag : Bool <- ##cs1`"tag" ;
    LetE cs1ECap : ECap <- ##cs1`"ecap" ;
    LetE cs1PermEx : Bool <- ##cs1ECap`"perms"`"EX" ;
    LetE cs1Sealed : Bool <- isSealed cs1ECap ;
    LetE notCs1Sealed : Bool <- Not #cs1Sealed ;

    LetE cdNum : Bit RegIdxSz <- getCd inst ;
    LetE cs1Num : Bit RegIdxSz <- getCs1 inst ;
    LetE immZero : Bool <- isZero (#inst`[31:20]) ;

    LetE isCdZero : Bool <- isZero #cdNum ;
    LetE isCs1Cra : Bool <- Eq #cs1Num $Cra ;
    LetE isCdCra  : Bool <- Eq #cdNum $Cra ;
    LetE isReturn : Bool <- And [#isCdZero; #isCs1Cra] ;
    LetE isCall   : Bool <- #isCdCra ;

    LetE cs1OType : Bit CapOTypeSz <- ##cs1ECap`"oType" ;

    LetE nextPccLegal : Bool <- caseDefault [ (#isReturn, isRetSentry cs1OType);
                                              (#isCall, Or [#notCs1Sealed; isCallSentry cs1OType]) ]
                                  (Or [#notCs1Sealed; Eq #cs1OType $CallSentryIh]);

    LetE nextPccTag : Bool <-
      And [ #cs1Tag; #cs1PermEx; #nextPccLegal; Or [ #notCs1Sealed; #immZero ] ] ;
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
    RetE (ITE (#selArr$[1]) (ITE (#selArr$[0]) #andRes #orRes) #xorRes).

  Definition TagECap := STRUCT_TYPE {
    "tag"  :: Bool ;
    "ecap" :: ECap }.

  Definition CAndPerm (tag : ty Bool) (ecap : ty ECap) (cs2Addr : ty Data) : LetExpr ty TagECap :=
    LetE maskBits : Bit (kindSize CapPerms) <-
      TruncLsb (Xlen - kindSize CapPerms) (kindSize CapPerms) #cs2Addr ;
    LetE maskVal : CapPerms <- FromBit CapPerms #maskBits ;
    LetE oldPerms : CapPerms <- ##ecap`"perms" ;
    LetE rawMask : CapPerms <- And [ ##oldPerms; #maskVal ] ;
    LetE newPerms : CapPerms <- fixPerms rawMask ;
    LetE sealed : Bool <- isSealed ecap ;
    LetE maskAllOnesNonGL : Bool <- isAllOnes (#maskVal `{ "GL" <- ConstTBool true }) ;
    LetE keepTag : Bool <- Or [ Not #sealed; #maskAllOnesNonGL ] ;
    LetE outTag : Bool <- And [ #tag; #keepTag ] ;
    LetE outECap : ECap <- ##ecap `{ "perms" <- #newPerms } ;
    @RetE _ TagECap (STRUCT { "tag" ::= #outTag; "ecap" ::= #outECap }).

  Definition SealerUnsealer (isUnseal inBounds tag : ty Bool) (ecap : ty ECap) (cs2 : ty FullECapWithTag)
  : LetExpr ty TagECap :=
    LetE ecap2 : ECap <- ##cs2`"ecap" ;
    LetE perms1 : CapPerms <- ##ecap`"perms" ;
    LetE perms2 : CapPerms <- ##ecap2`"perms" ;
    LetE sealed1 : Bool <- isSealed ecap ;
    LetE sealed2 : Bool <- isSealed ecap2 ;
    LetE cs2Addr : Data <- ##cs2`"addr" ;
    LetE cs2Tag : Bool <- ##cs2`"tag" ;
    LetE sealRange : Bool <- ITE (##perms1`"EX")
                               (And [ Sgt #cs2Addr $0; Sle #cs2Addr $7 ])
                               (And [ Sgt #cs2Addr $8; Sle #cs2Addr $15 ]) ;
    LetE permit : Bool <- ITE #isUnseal
                            (And [ #sealed1; ##perms2`"US" ])
                            (And [ Not #sealed1; ##perms2`"SE"; #sealRange ]) ;
    LetE outTag : Bool <- And [ #tag; #cs2Tag; #inBounds; Not #sealed2; #permit ] ;
    LetE outOType : Bit CapOTypeSz <-
      ITE0 (Not #isUnseal) (TruncLsb (AddrSz - CapOTypeSz) CapOTypeSz #cs2Addr) ;
    LetE outGL : Bool <- ITE #isUnseal (And [ ##perms1`"GL"; ##perms2`"GL" ]) (##perms1`"GL") ;
    LetE outPerms : CapPerms <- ##perms1 `{ "GL" <- #outGL } ;
    LetE outECap : ECap <- ##ecap `{ "oType" <- #outOType } `{ "perms" <- #outPerms } ;
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
      LetE m_ovf : Bit CapBSz <-
        {< Const _ (Bit (CapBSz - 1)) (Zmod.of_Z _ (2^(CapBSz - 2))), ToBit #inc_ovf >};
      LetE m_normal : Bit CapBSz <- ITE #isOverflow #m_ovf (TruncLsb 1 CapBSz #m_raw);

      LETE e_b: Bit ExpSz <- countTrailingZerosArray (mkBoolArray (AddrSz + 1) #base) _;
      LetE pick_b: Bool <- Slt #e_b #e_init;
      LetE e_roundDown: Bit ExpSz <- ITE #pick_b #e_b #e_init;
      LetE m_roundDown: Bit CapBSz <-
        ITE #pick_b (Const ty (Bit CapBSz) (InvDefault _)) (TruncLsb 1 CapBSz #d);

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

  Definition BoundsExact (inBounds boundsAreExact instIsExact : ty Bool) : LetExpr ty Bool :=
    @RetE _ Bool (And [ #inBounds; Or [ Not #instIsExact; #boundsAreExact ] ]).

  (* If isArith is set for left shift, results are wrong *)
  Definition Shifter (data : ty (Bit Xlen)) (shamt : ty (Bit 5)) (isRight isArith : ty Bool)
  : LetExpr ty (Bit Xlen) :=
    ( let rev e := ToBit (ArrayReverse (FromBit (Array (Z.to_nat Xlen) Bool) e)) in
      LetE inpVal : Bit Xlen <- ITE #isRight #data (rev #data) ;
      LetE signBit : Bit 1 <-
        ITE #isArith (TruncMsb 1 (Xlen - 1) #inpVal) (Const ty (Bit 1) Zmod.zero) ;
      LetE extVal : Bit (Xlen + 1) <- {< #signBit, #inpVal >} ;
      LetE shiftedExt : Bit (Xlen + 1) <- Sra #extVal #shamt ;
      LetE shiftedXlen : Bit Xlen <- TruncLsb 1 Xlen #shiftedExt ;
      @RetE _ (Bit Xlen) (ITE #isRight #shiftedXlen (rev #shiftedXlen))
    ).

  Definition AdderBeforeRepCheck (base shifter : ty (Bit (Xlen + 1))) : LetExpr ty (Bit (Xlen + 1)) :=
    LetE repLimit : Bit (Xlen + 1) <- Add [ #base; #shifter ];
    RetE #repLimit.

  Definition ComparatorOut := STRUCT_TYPE {
    "lt" :: Bool ;
    "eq" :: Bool }.

  Definition ComparatorTopOrRep (addr topRep : ty (Bit (Xlen + 1))) (checkLte : ty Bool) : LetExpr ty ComparatorOut :=
    LetE ltRes : Bool <- Slt #addr #topRep;
    LetE eqRes : Bool <- Eq #addr #topRep;
    LetE lteRes : Bool <- Or [ #ltRes; #eqRes ];
    LetE outLt : Bool <- ITE #checkLte #lteRes #ltRes;
    @RetE _ ComparatorOut (STRUCT { "lt" ::= #outLt; "eq" ::= #eqRes }).

  Definition ComparatorBase (addr base : ty (Bit (Xlen + 1))) : LetExpr ty Bool :=
    LetE geRes : Bool <- Sge #addr #base;
    RetE #geRes.

  Definition AddrBoundsCheck (tag topLt baseGe : ty Bool) : LetExpr ty Bool :=
    LetE inBounds : Bool <- And [ #topLt; #baseGe ];
    @RetE _ Bool (And [ #tag; #inBounds ]).

  Definition CapSubset (topLe baseGe tag1 tag2 : ty Bool) (perms1 perms2 : ty CapPerms) : LetExpr ty Bool :=
    LetE pAnd : CapPerms <- And [ #perms1; #perms2 ];
    LetE pEq : Bool <- Eq #pAnd #perms2;
    @RetE _ Bool (And [ #tag1; #tag2; #topLe; #baseGe; #pEq ]).

  Definition CapEq (addrEq tag1 tag2 : ty Bool) (ecap1 ecap2 : ty ECap) : LetExpr ty Bool :=
    LetE metaEq : Bool <- Eq #ecap1 #ecap2;
    LetE tagsEq : Bool <- Eq #tag1 #tag2;
    @RetE _ Bool (And [ #addrEq; #metaEq; #tagsEq ]).

  Definition ScrSanitizer (tag : ty Bool) (addr : ty (Bit Xlen)) (inst : ty Inst)
  : LetExpr ty Bool :=
    LetE scrIdx : Bit RegIdxSz <- getScr inst ;
    LetE isMePcc : Bool <- Eq #scrIdx $(getScrAddr "MePcc"%string) ;
    LetE isMtcc : Bool <- Eq #scrIdx $(getScrAddr "Mtcc"%string) ;
    LetE isMePrevPcc : Bool <- Eq #scrIdx $(getScrAddr "MePrevPcc"%string) ;
    LetE isSpecialPcc : Bool <- Or [ #isMePcc; #isMtcc; #isMePrevPcc ] ;
    LetE lsbZero : Bool <-
      Eq (TruncLsb (Xlen - 1) 1 #addr) (Const ty (Bit 1) Zmod.zero) ;
    LetE keepTag : Bool <- Or [ Not #isSpecialPcc; #lsbZero ] ;
    @RetE _ Bool (And [ #tag; #keepTag ]).

  Definition LoadStore (cs1Perms : ty CapPerms)
                       (memSize : ty (Bit LgLgNumBytesFullCapSz))
                       (isUnsigned isLoad isStore : ty Bool)
                       (addr : ty Addr)
                       (storeTag : ty Bool)
                       (storeCap : ty Cap)
                       (storeData : ty Addr)
  : LetExpr ty (Option DeferredOp) :=
    LetE isLM : Bool <- And [ #isLoad ; ##cs1Perms`"LM" ] ;
    LetE isLG : Bool <- And [ #isLoad ; ##cs1Perms`"LG" ] ;
    LetE isUnsig : Bool <- And [ #isLoad ; #isUnsigned ] ;
    LetE loadOpVal : LoadOp <- STRUCT {
      "isUnsigned" ::= #isUnsig ;
      "isLM"       ::= #isLM ;
      "isLG"       ::= #isLG
    } ;
    LetE storeCapVal : FullCapWithTag <- STRUCT {
      "tag"  ::= #storeTag ;
      "cap"  ::= #storeCap ;
      "addr" ::= #storeData
    } ;
    LetE loadOrStoreKind : LoadOrStoreKind <- ITE #isStore
      (UNION (LoadOrStoreType, "Store" ::= #storeCapVal))
      (UNION (LoadOrStoreType, "Load" ::= #loadOpVal)) ;
    LetE memOpVal : MemOp <- STRUCT {
      "addr"        ::= #addr ;
      "memSize"     ::= #memSize ;
      "loadOrStore" ::= #loadOrStoreKind
    } ;
    LetE isMemOp : Bool <- Or [ #isLoad; #isStore ] ;
    RetE (ITE0 #isMemOp (mkSome (UNION (DeferredOpType, "MemOp" ::= #memOpVal)))).


  Definition EncodeCap (ecap: ty ECap) : LetExpr ty Cap :=
      ( LetE decodedPerms <- #ecap`"perms";
        LetE perms <- encodePerms decodedPerms;
        LetE E <- #ecap`"E";
        LetE ECorrected <- get_ECorrected_from_E E;
        LetE B <- TruncLsb (AddrSz + 1 - CapBSz) CapBSz (Sll (#ecap`"base") #ECorrected);
        LetE T <- TruncLsb (AddrSz + 1 - CapBSz) CapBSz (Sll (#ecap`"top") #ECorrected);
        LETE cE <- get_cE_from_E_T_B E T B;
        LetE cT <- get_cT_from_T T;
        @RetE _ Cap (STRUCT {
                         "R" ::= #ecap`"R";
                         "p" ::= #perms;
                         "oType" ::= #ecap`"oType";
                         "cE" ::= #cE;
                         "cT" ::= #cT;
                         "B" ::= #B })).

  Definition DecodeCap (cap: ty Cap) (addr: ty Addr) : LetExpr ty ECap :=
      ( LetE encodedPerms <- #cap`"p";
        LETE perms <- decodePerms encodedPerms;
        LetE cap_cE <- #cap`"cE";
        LetE cap_cT <- #cap`"cT";
        LetE cap_B <- #cap`"B";
        LetE E <- get_E_from_cE cap_cE;
        LetE ECorrected <- get_ECorrected_from_E E;
        LETE T <- get_T_from_cE_cT_B cap_cE cap_cT cap_B;
        LETE base_top <- get_base_top_from_ECorrected_T_B addr ECorrected T cap_B;
        @RetE _ ECap (STRUCT {
                          "R" ::= ##cap`"R";
                          "perms" ::= #perms;
                          "oType" ::= #cap`"oType";
                          "E" ::= #E;
                          "top" ::= #base_top`"top";
                          "base" ::= #base_top`"base" })).

  Definition Deferred (isLoad isStore isFence : ty Bool)
                       (cs1Perms : ty CapPerms)
                       (inst : ty (Bit Xlen))
                       (addr : ty Addr)
                       (storeTag : ty Bool)
                       (storeCap : ty Cap)
                       (storeData : ty Addr)
  : LetExpr ty (Option DeferredOp) :=
    LetE memSize : Bit LgLgNumBytesFullCapSz <- #inst`[13:12] ;
    LetE isUnsigned : Bool <- isNotZero (#inst`[14:14]) ;
    LetE isFenceI : Bool <- isNotZero (#inst`[12:12]) ;
    LetE isTso : Bool <- isNotZero (#inst`[31:31]) ;
    LetE pred_r : Bool <- isNotZero (#inst`[25:25]) ;
    LetE pred_w : Bool <- isNotZero (#inst`[24:24]) ;
    LetE succ_r : Bool <- isNotZero (#inst`[21:21]) ;
    LetE succ_w : Bool <- isNotZero (#inst`[20:20]) ;
    LetE rr : Bool <- And [ Not #isFenceI ; #pred_r ; #succ_r ] ;
    LetE rw : Bool <- And [ Not #isFenceI ; #pred_r ; #succ_w ] ;
    LetE wr : Bool <- And [ Not #isFenceI ; Not #isTso ; #pred_w ; #succ_r ] ;
    LetE ww : Bool <- And [ Not #isFenceI ; #pred_w ; #succ_w ] ;
    LetE fenceVal : FenceOp <- STRUCT {
      "isFenceI" ::= #isFenceI ;
      "RR"       ::= #rr ;
      "RW"       ::= #rw ;
      "WR"       ::= #wr ;
      "WW"       ::= #ww
    } ;
    LETE memOpOpt : Option DeferredOp <- LoadStore cs1Perms memSize isUnsigned isLoad isStore addr storeTag storeCap storeData ;
    RetE (Or [ ITE0 #isFence (mkSome (UNION (DeferredOpType, "FenceOp" ::= #fenceVal))) ;
               #memOpOpt ]).

  Definition MemException (isStore : ty Bool)
                          (cs1Tag : ty Bool)
                          (ecap : ty ECap)
                          (cs1Idx : ty (Bit RegIdxSz))
                          (inBounds : ty Bool)
                          (addr : ty Addr)
                          (memSize : ty (Bit LgLgNumBytesFullCapSz))
  : LetExpr ty (Option ExceptionInfo) :=
    LetE cs1Perms  : CapPerms       <- ##ecap`"perms" ;
    LetE cs1Otype  : Bit CapOTypeSz <- ##ecap`"oType" ;
    LetE cs1Sealed : Bool           <- isNotZero #cs1Otype ;

    LetE isCap : Bool <- Eq #memSize $3 ;

    (* 1. Exception Conditions (in Priority Order) *)
    LetE tagExc      : Bool <- Not #cs1Tag ;
    LetE sealExc     : Bool <- #cs1Sealed ;
    LetE hasPerm     : Bool <- ITE #isStore (##cs1Perms`"SD") (##cs1Perms`"LD") ;
    LetE permExc     : Bool <- Not #hasPerm ;
    LetE storeCapExc : Bool <- And [ #isStore; #isCap; Not (##cs1Perms`"MC") ] ;
    LetE boundsExc   : Bool <- Not #inBounds ;
    LetE alignExc    : Bool <- And [ #isCap; isNotZero (#addr`[2:0]) ] ; (* Misaligned ONLY for caps *)

    (* 2. Payload & ExceptionInfo Constructors *)
    LetE permCause   : Bit 5 <- ITE #isStore $CapEx_PermitStoreViolation $CapEx_PermitLoadViolation ;
    LetE alignMcause : Bit 5 <- ITE #isStore $EXC_StoreAddrAlign $EXC_LoadAddrAlign ;

    (* 3. Strict Priority Chain returning Option ExceptionInfo directly *)
    RetE (
      ITE #tagExc
        (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (ConstBool false) #cs1Idx $CapEx_TagViolation)))
        (ITE #sealExc
          (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (ConstBool false) #cs1Idx $CapEx_SealViolation)))
          (ITE #permExc
            (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (ConstBool false) #cs1Idx #permCause)))
            (ITE #storeCapExc
              (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (ConstBool false) #cs1Idx $CapEx_PermitStoreCapViolation)))
              (ITE #boundsExc
                (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (ConstBool false) #cs1Idx $CapEx_BoundsViolation)))
                (ITE #alignExc
                  (mkSome (mkExceptionInfo #alignMcause (mkCheriMtval (ConstBool false) #cs1Idx $0)))
                  (mkNone ty))))))
    ).

  Definition ExceptionUnit (isECall isEBreak isLoad isStore : ty Bool)
                           (fetchExc : ty FetchException)
                           (decodeExc : ty DecodeException)
                           (inst : ty (Bit Xlen))
                           (cs1Tag : ty Bool)
                           (cs1ECap : ty ECap)
                           (inBounds : ty Bool)
                           (addr : ty Addr)
  : LetExpr ty (Option ExceptionInfo) :=
    LetE fetchTag      : Bool <- ##fetchExc`"tag" ;
    LetE fetchSeal     : Bool <- ##fetchExc`"seal" ;
    LetE fetchExecPerm : Bool <- ##fetchExc`"perm" ;
    LetE fetchBounds   : Bool <- ##fetchExc`"bounds" ;

    LetE illegalInst   : Bool <- ##decodeExc`"illegal" ;
    LetE asrViolation  : Bool <- ##decodeExc`"asr" ;
    LetE scrIdx        : Bit RegIdxSz <- #inst`[24:20] ;
    LetE cs1Idx        : Bit RegIdxSz <- #inst`[19:15] ;
    LetE memSize       : Bit LgLgNumBytesFullCapSz <- #inst`[13:12] ;
    LETE memExcOut     : Option ExceptionInfo <-
      MemException isStore cs1Tag cs1ECap cs1Idx inBounds addr memSize ;

    LetE isMemOp : Bool <- Or [ #isLoad; #isStore ] ;

    (* 1. Fetch Mtval payloads (S = false, RegIdx = 0) *)
    LetE mtvalFetchTag  : CheriMtval <- mkCheriMtval (ConstBool false) $0 $CapEx_TagViolation ;
    LetE mtvalFetchSeal : CheriMtval <- mkCheriMtval (ConstBool false) $0 $CapEx_SealViolation ;
    LetE mtvalFetchExec : CheriMtval <- mkCheriMtval (ConstBool false) $0 $CapEx_PermitExecuteViolation ;
    LetE mtvalFetchBnds : CheriMtval <- mkCheriMtval (ConstBool false) $0 $CapEx_BoundsViolation ;

    (* 2. Decoder & System Mtval payloads *)
    LetE mtvalZero      : CheriMtval <- mkCheriMtval (ConstBool false) $0 $0 ;
    LetE mtvalAsr       : CheriMtval <- mkCheriMtval (ConstBool true) #scrIdx $CapEx_AccessSystemRegsViolation ;

    LetE sysCallExc : Option ExceptionInfo <-
      Or [ ITE0 #isECall (mkSome (mkExceptionInfo $EXC_ECallM #mtvalZero)) ;
           ITE0 #isEBreak (mkSome (mkExceptionInfo $EXC_Breakpoint #mtvalZero)) ] ;

    (* 3. Strict Priority Cascade *)
    RetE (
      ITE (Not #fetchTag)
        (mkSome (mkExceptionInfo $EXC_CHERI #mtvalFetchTag))
        (ITE #fetchSeal
          (mkSome (mkExceptionInfo $EXC_CHERI #mtvalFetchSeal))
          (ITE (Not #fetchExecPerm)
            (mkSome (mkExceptionInfo $EXC_CHERI #mtvalFetchExec))
            (ITE (Not #fetchBounds)
              (mkSome (mkExceptionInfo $EXC_CHERI #mtvalFetchBnds))
              (ITE #illegalInst
                (mkSome (mkExceptionInfo $EXC_IllegalInst #mtvalZero))
                (ITE #asrViolation
                  (mkSome (mkExceptionInfo $EXC_CHERI #mtvalAsr))
                  (ITE #isMemOp
                    #memExcOut
                    #sysCallExc))))))
    ).

  Definition NewPccRes := STRUCT_TYPE {
    "tag" :: Bool ;
    "ecap" :: ECap ;
    "addr" :: Addr ;
    "NewPccAddr_change" :: Bool ;
    "NewPccEcap_change" :: Bool
  }.

  Definition NewPcc (isMret isCjal isCjalr isBranch : ty Bool)
                    (isCond : ty Bool)
                    (cs2 : ty FullECapWithTag) (addrIn : ty Addr)
                    (inBounds cjalrTag : ty Bool) (cjalrEcap : ty ECap)
                    (pccTag : ty Bool)
  : LetExpr ty NewPccRes :=
    LetE isTakenBranch : Bool <- And [ #isBranch ; #isCond ] ;
    LetE addrChange : Bool <- Or [ #isMret ; #isCjal ; #isCjalr ; #isTakenBranch ] ;
    LetE ecapChange : Bool <- Or [ #isMret ; #isCjalr ] ;
    LetE cs2Addr : Addr <- ##cs2`"addr" ;
    LetE pccAddrOut : Addr <- ITE (#isMret) #cs2Addr #addrIn ;
    LetE pccTagOut : Bool <-
      caseDefault (k := Bool) [
          (#isMret, ##cs2`"tag") ;
          (Or [ #isBranch ; #isCjal ], #inBounds) ;
          (#isCjalr, #cjalrTag) ]
        #pccTag ;
    LetE pccEcapOut : ECap <-
      Or [ ITE0 #isMret ##cs2`"ecap" ;
           ITE0 #isCjalr #cjalrEcap ] ;
    @RetE _ NewPccRes (STRUCT {
      "tag" ::= #pccTagOut ;
      "ecap" ::= #pccEcapOut ;
      "addr" ::= #pccAddrOut ;
      "NewPccAddr_change" ::= #addrChange ;
      "NewPccEcap_change" ::= #ecapChange
    }).

  Definition AluOut := STRUCT_TYPE {
    "NewPcc" :: FullECapWithTag ;
    "NewPccEcap_change" :: Bool ;
    "NewPccAddr_change" :: Bool ;
    "Exception" :: Option ExceptionInfo ;
    "DeferredOp" :: Option DeferredOp ;
    "NewInterruptStatus" :: Bool ;
    "NewSpecial" :: FullECapWithTag ;
    "Reg" :: FullECapWithTag
  }.

  Section AluRouting.
    Variables (pcc cs1 cs2 : ty FullECapWithTag).
    Variable inst : ty Inst.
    Variable currInterruptStatus : ty Bool.
    Variable fetchExc : ty FetchException.
    Variable decodeExc : ty DecodeException.

    Definition AluRouting (aluControl : ty AluControl) : LetExpr ty AluOut :=
      LetE pccAddr : Bit Xlen <- ##pcc`"addr" ;
      LetE pccTag : Bool <- ##pcc`"tag" ;
      LetE pccBase : Bit (AddrSz + 1) <- ##pcc`"ecap"`"base" ;
      LetE pccExp : Bit ExpSz <- ##pcc`"ecap"`"E" ;

      LetE cs1Addr : Bit Xlen <- ##cs1`"addr" ;
      LetE cs1Tag : Bool <- ##cs1`"tag" ;
      LetE cs1ECap : ECap <- ##cs1`"ecap" ;
      LetE cs1Base : Bit (AddrSz + 1) <- ##cs1ECap`"base" ;
      LetE cs1Top : Bit (AddrSz + 1) <- ##cs1ECap`"top" ;
      LetE cs1Exp : Bit ExpSz <- ##cs1ECap`"E" ;
      LetE cs1Perms : CapPerms <- ##cs1ECap`"perms" ;
      LetE cs1OType : Bit CapOTypeSz <- ##cs1ECap`"oType" ;

      LetE cs2Addr : Bit Xlen <- ##cs2`"addr" ;
      LetE cs2Tag : Bool <- ##cs2`"tag" ;
      LetE cs2ECap : ECap <- ##cs2`"ecap" ;
      LetE cs2Base : Bit (AddrSz + 1) <- ##cs2`"ecap"`"base" ;
      LetE cs2Top : Bit (AddrSz + 1) <- ##cs2`"ecap"`"top" ;
      LetE cs2Perms : CapPerms <- ##cs2`"ecap"`"perms" ;

      LetE simm12 : Bit Xlen <- SignExtendTo Xlen (##inst`[31:20]) ;
      LetE zimm12 : Bit Xlen <- ZeroExtendTo Xlen (##inst`[31:20]) ;
      LetE uimm20 : Bit Xlen <- ({< ##inst`[31:12], Const ty (Bit 12) Zmod.zero >}) ;
      LetE uimm20_11 : Bit Xlen <-
        ({< ##inst`[31:31], ##inst`[31:12], Const ty (Bit 11) Zmod.zero >}) ;
      LetE shamt <- ##inst`[24:20] ;
      LetE zimm5 : Bit 5 <- ##inst`[19:15] ;
      LetE bimm13 : Bit 13 <-
        ({< ##inst`[31:31], ##inst`[7:7], ##inst`[30:25], ##inst`[11:8],
            Const _ (Bit 1) Zmod.zero >}) ;
      LetE bimm12 : Bit Xlen <- SignExtendTo Xlen #bimm13 ;
      LetE jimm21 : Bit 21 <-
        ({< ##inst`[31:31], ##inst`[19:12], ##inst`[20:20], ##inst`[30:21],
            Const _ (Bit 1) Zmod.zero >}) ;
      LetE jimm20 : Bit Xlen <- SignExtendTo Xlen #jimm21 ;
      LetE scrIdx : Bit RegIdxSz <- ##inst`[24:20] ;
      LetE cs1Idx : Bit RegIdxSz <- ##inst`[19:15] ;
      LetE memSize : Bit LgLgNumBytesFullCapSz <- ##inst`[13:12] ;
      LetE isFenceI : Bool <- isNotZero (##inst`[12:12]) ;

      LetE BranchOrCjalOrAuiPcc : Bool <- ##aluControl`"BranchOrCjalOrAuiPcc" ;
      LetE BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr : Bool <-
        ##aluControl`"BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr" ;

      LetE AdderBeforeBoundsCheck_base : Bit Xlen <-
        ITE (#BranchOrCjalOrAuiPcc) #pccAddr #cs1Addr ;
      LetE AdderBeforeBoundsCheck_offset : Bit Xlen <-
        caseDefault (k := Bit Xlen) [
            (##aluControl`"Branch", #bimm12) ;
            (##aluControl`"Cjal", #jimm20) ;
            (##aluControl`"AdderBeforeBoundsCheck_offset_uimm20_11", #uimm20_11) ;
            (##aluControl`"AdderBeforeBoundsCheck_offset_cs2Addr", #cs2Addr) ;
            (##aluControl`"Bounds_isImm", #zimm12) ]
          #simm12 ;
      LETE AdderBeforeBoundsCheckOut : Bit Xlen <-
        AdderBeforeBoundsCheck AdderBeforeBoundsCheck_base AdderBeforeBoundsCheck_offset ;

      LetE AdderToOutput_base : Bit Xlen <-
        caseDefault (k := Bit Xlen) [
            (##aluControl`"AdderToOutput_base_pccAddr", #pccAddr) ;
            (##aluControl`"CGetLen", TruncLsb 1 Xlen #cs1Top) ]
          #cs1Addr ;
      LetE AdderToOutput_offset : Bit Xlen <-
        caseDefault (k := Bit Xlen) [
            (##aluControl`"AdderToOutput_offset_const2", Const ty (Bit Xlen) (Zmod.of_Z _ (CompInstSz/8))) ;
            (##aluControl`"AdderToOutput_offset_cs2Addr", #cs2Addr) ;
            (##aluControl`"AdderToOutput_offset_simm12", #simm12) ;
            (##aluControl`"CGetLen", TruncLsb 1 Xlen #cs1Base) ]
          (Const ty (Bit Xlen) (Zmod.of_Z _ (InstSz/8))) ;
      LetE AdderToOutput_isSub : Bool <- ##aluControl`"AdderToOutput_isSub" ;
      LETE AdderToOutputOut : Bit Xlen <-
        AdderToOutput AdderToOutput_base AdderToOutput_offset AdderToOutput_isSub ;

      LetE AddCapBSz_baseExp : Bit ExpSz <-
        ITE (#BranchOrCjalOrAuiPcc) #pccExp #cs1Exp ;
      LETE AddCapBSzOut : Bit ExpSz <- AddCapBSz AddCapBSz_baseExp ;

      LetE Shifter_data : Bit Xlen <-
        ITE (##aluControl`"Shift")
            #cs1Addr (Const ty (Bit Xlen) (Zmod.of_Z _ 1)) ;
      LetE Shifter_shamt : Bit RegIdxSz <-
        caseDefault (k := Bit RegIdxSz) [
            (##aluControl`"Shifter_shamt_cs2Addr", TruncLsb (Xlen - RegIdxSz) RegIdxSz #cs2Addr) ;
            (#BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr, #AddCapBSzOut) ]
          #shamt ;
      LetE Shifter_isRight : Bool <- ##aluControl`"Shifter_isRight" ;
      LetE Shifter_isArith : Bool <- ##aluControl`"Shifter_isArith" ;
      LETE ShifterOut : Bit Xlen <-
        Shifter Shifter_data Shifter_shamt Shifter_isRight Shifter_isArith ;

      LetE AdderBeforeRepCheck_base : Bit (Xlen + 1) <-
        ITE (#BranchOrCjalOrAuiPcc) #pccBase #cs1Base ;
      LetE AdderBeforeRepCheck_shifter : Bit (Xlen + 1) <- ZeroExtendTo (Xlen + 1) #ShifterOut ;
      LETE AdderBeforeRepCheckOut : Bit (Xlen + 1) <-
        AdderBeforeRepCheck AdderBeforeRepCheck_base AdderBeforeRepCheck_shifter ;

      LetE ComparatorTopOrRep_addr : Bit (Xlen + 1) <-
        caseDefault (k := Bit (Xlen + 1)) [
            (##aluControl`"ComparatorTopOrRep_addr_AdderBeforeBoundsCheck",
             ZeroExtendTo (Xlen + 1) #AdderBeforeBoundsCheckOut) ;
            (##aluControl`"SealOrSetAddr", ZeroExtendTo (Xlen + 1) #cs2Addr) ;
            (##aluControl`"Unseal", ZeroExtendTo (Xlen + 1) #cs1OType) ;
            (##aluControl`"CTestSubset", #cs1Top) ]
          (ZeroExtendTo (Xlen + 1) #cs1Addr) ;
      LetE ComparatorTopOrRep_topRep : Bit (Xlen + 1) <-
        caseDefault (k := Bit (Xlen + 1)) [
            (#BranchOrCjalOrAuiPccOrAuiCgpOrIncAddrOrSetAddr, #AdderBeforeRepCheckOut) ;
            (##aluControl`"SealOrUnsealOrSubset", #cs2Top) ]
          #cs1Top ;
      LetE ComparatorTopOrRep_checkLte : Bool <- ##aluControl`"ComparatorTopOrRep_checkLte" ;
      LETE ComparatorTopOrRepOut : ComparatorOut <-
        ComparatorTopOrRep ComparatorTopOrRep_addr ComparatorTopOrRep_topRep ComparatorTopOrRep_checkLte ;

      LetE ComparatorBase_addr : Bit (Xlen + 1) <-
        caseDefault (k := Bit (Xlen + 1)) [
            (##aluControl`"ComparatorBase_addr_AdderBeforeBoundsCheck",
             ZeroExtendTo (Xlen + 1) #AdderBeforeBoundsCheckOut) ;
            (##aluControl`"SealOrSetAddr", ZeroExtendTo (Xlen + 1) #cs2Addr) ;
            (##aluControl`"Unseal", ZeroExtendTo (Xlen + 1) #cs1OType) ;
            (##aluControl`"CTestSubset", #cs1Base) ]
          (ZeroExtendTo (Xlen + 1) #cs1Addr) ;
      LetE ComparatorBase_base : Bit (Xlen + 1) <-
        caseDefault (k := Bit (Xlen + 1)) [
            (#BranchOrCjalOrAuiPcc, #pccBase) ;
            (##aluControl`"SealOrUnsealOrSubset", #cs2Base) ]
          #cs1Base ;
      LETE ComparatorBaseOut : Bool <- ComparatorBase ComparatorBase_addr ComparatorBase_base ;

      LetE AddrBoundsCheck_tag : Bool <-
        ITE (#BranchOrCjalOrAuiPcc) #pccTag #cs1Tag ;
      LetE AddrBoundsCheck_topLt : Bool <- ##ComparatorTopOrRepOut`"lt" ;
      LetE AddrBoundsCheck_baseGe : Bool <- ##ComparatorBaseOut ;
      LETE AddrBoundsCheckOut : Bool <-
        AddrBoundsCheck AddrBoundsCheck_tag AddrBoundsCheck_topLt
                        AddrBoundsCheck_baseGe ;

      LetE cs1ECap : ECap <- ##cs1`"ecap" ;

      LetE SealerUnsealer_isUnseal : Bool <- ##aluControl`"Unseal" ;
      LETE SealerUnsealerOut : TagECap <-
        SealerUnsealer SealerUnsealer_isUnseal AddrBoundsCheckOut cs1Tag cs1ECap cs2 ;

      LetE ComparatorGeneral_op1 : Bit Xlen <- #cs1Addr ;
      LetE ComparatorGeneral_op2 : Bit Xlen <-
        ITE (##aluControl`"ComparatorGeneral_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
      LetE ComparatorGeneral_isUnsigned : Bool <- ##aluControl`"isUnsigned" ;
      LetE ComparatorGeneral_checkLt    : Bool <- ##aluControl`"ComparatorGeneral_checkLt" ;
      LetE ComparatorGeneral_checkEq    : Bool <- ##aluControl`"ComparatorGeneral_checkEq" ;
      LetE ComparatorGeneral_invertRes  : Bool <- ##aluControl`"ComparatorGeneral_invertRes" ;
      LETE ComparatorGeneralOut : ComparatorGeneralRes <-
        ComparatorGeneral ComparatorGeneral_op1 ComparatorGeneral_op2
                          ComparatorGeneral_isUnsigned ComparatorGeneral_checkLt
                          ComparatorGeneral_checkEq ComparatorGeneral_invertRes ;

      LETE CjalrUnitOut : CjalrUnitRes <- CjalrUnit cs1 inst currInterruptStatus ;

      LetE Logical_op1 : Bit Xlen <- #cs1Addr ;
      LetE Logical_op2 : Bit Xlen <-
        ITE (##aluControl`"Logical_op2_isCs2AddrNotSimm12") #cs2Addr #simm12 ;
      LetE Logical_opSel : Bit 2 <- ##inst`[13:12] ;
      LETE LogicalOut : Bit Xlen <- Logical Logical_op1 Logical_op2 Logical_opSel ;

      LETE CAndPermOut : TagECap <- CAndPerm cs1Tag cs1ECap cs2Addr ;

      LetE Bounds_reqLimit : Bit Xlen <-
        caseDefault (k := Bit Xlen) [ (##aluControl`"Bounds_reqLimit_cs2Addr", #cs2Addr) ;
                                       (##aluControl`"Bounds_reqLimit_cs1Addr", #cs1Addr) ]
          #zimm12 ;
      LetE Bounds_reqLimitExt : Bit (Xlen + 1) <- ZeroExtendTo (Xlen + 1) #Bounds_reqLimit ;
      LetE Bounds_isRoundDown : Bool <- ##aluControl`"Bounds_isRoundDown" ;
      LETE BoundsOut : BoundsRes <- Bounds cs1Base Bounds_reqLimitExt Bounds_isRoundDown ;

      LetE Bounds_boundsExact : Bool <- ##BoundsOut`"exact" ;
      LetE Bounds_instIsExact : Bool <- ##aluControl`"Bounds_isExact" ;
      LETE BoundsExactOut : Bool <- BoundsExact AddrBoundsCheckOut Bounds_boundsExact Bounds_instIsExact ;

      LETE CapSubsetOut : Bool <-
        CapSubset AddrBoundsCheck_topLt AddrBoundsCheck_baseGe cs1Tag cs2Tag cs1Perms cs2Perms ;

      LetE CapEq_addrEq : Bool <- ##ComparatorGeneralOut`"eq" ;
      LETE CapEqOut : Bool <- CapEq CapEq_addrEq cs1Tag cs2Tag cs1ECap cs2ECap ;

      LETE ScrSanitizerOut : Bool <- ScrSanitizer cs1Tag cs1Addr inst ;

      LetE isMret : Bool <- ##aluControl`"Mret" ;
      LetE isCjal : Bool <- ##aluControl`"Cjal" ;
      LetE isCjalr : Bool <- ##aluControl`"Cjalr" ;
      LetE isBranch : Bool <- ##aluControl`"Branch" ;
      LetE isCond : Bool <- ##ComparatorGeneralOut`"cond" ;

      LetE cjalrTag : Bool <- ##CjalrUnitOut`"tag" ;
      LetE cjalrEcap : ECap <- ##CjalrUnitOut`"ecap" ;
      LETE NewPccOut : NewPccRes <-
        NewPcc isMret isCjal isCjalr isBranch isCond cs2 AdderBeforeBoundsCheckOut
               AddrBoundsCheckOut cjalrTag cjalrEcap pccTag ;

      LetE NewPcc_tag : Bool <- ##NewPccOut`"tag" ;
      LetE NewPcc_ecap : ECap <- ##NewPccOut`"ecap" ;
      LetE NewPcc_addr : Addr <- ##NewPccOut`"addr" ;
      LetE NewPccEcap_change : Bool <- ##NewPccOut`"NewPccEcap_change" ;
      LetE NewPccAddr_change : Bool <- ##NewPccOut`"NewPccAddr_change" ;

      LetE NewSpecial_tag : Bool <- #ScrSanitizerOut ;

      LetE Reg_tag : Bool <-
        Or [ And [ ##aluControl`"Cjal"                  ; #pccTag ] ;
             And [ ##aluControl`"Reg_tag_cs1Tag"         ; #cs1Tag ] ;
             And [ ##aluControl`"Scr"                    ; #cs2Tag ] ;
             And [ ##aluControl`"Reg_tag_AddrBoundsCheck"; #AddrBoundsCheckOut ] ;
             And [ ##aluControl`"CSetBounds"             ; #BoundsExactOut ] ;
             And [ ##aluControl`"CAndPerm"               ; ##CAndPermOut`"tag" ] ;
             And [ ##aluControl`"SealOrUnseal"           ; ##SealerUnsealerOut`"tag" ] ] ;


      LetE capToEncode : ECap <- ITE (##aluControl`"Store") (#cs2ECap) (#cs1ECap) ;
      LETE encodedCap : Cap <- EncodeCap capToEncode ;
      LetE cs2AddrAsCap : Cap <- FromBit Cap #cs2Addr ;
      LETE decodedECap : ECap <- DecodeCap cs2AddrAsCap cs1Addr ;
      LetE Bounds_outECap : ECap <- STRUCT { "R"     ::= ##cs1ECap`"R" ;
                                             "perms" ::= ##cs1ECap`"perms" ;
                                             "oType" ::= ##cs1ECap`"oType" ;
                                             "E"     ::= ##BoundsOut`"E" ;
                                             "top"   ::= ##BoundsOut`"top" ;
                                             "base"  ::= ##BoundsOut`"base" };

      LetE Reg_ecap : ECap <-
        caseDefault (k := ECap) [ (##aluControl`"Reg_ecap_pccEcap", ##pcc`"ecap") ;
                                   (##aluControl`"Reg_ecap_cs1Ecap", ##cs1`"ecap") ;
                                   (##aluControl`"Scr", ##cs2`"ecap") ;
                                   (##aluControl`"CSetHigh", #decodedECap) ;
                                   (##aluControl`"CAndPerm", ##CAndPermOut`"ecap") ;
                                   (##aluControl`"SealOrUnseal", ##SealerUnsealerOut`"ecap") ;
                                   (##aluControl`"CSetBounds", #Bounds_outECap) ]
          (Const ty ECap (getDefault _)) ;

      LetE Reg_addr : Data <-
        caseDefault (k := Data) [
            (##aluControl`"Reg_addr_AdderBeforeBoundsCheck", #AdderBeforeBoundsCheckOut) ;
            (##aluControl`"Slt",
             ZeroExtendTo Xlen (ToBit (##ComparatorGeneralOut`"cond"))) ;
            (##aluControl`"Shift", #ShifterOut) ;
            (##aluControl`"Logical", #LogicalOut) ;
            (##aluControl`"Reg_addr_AdderToOutput", #AdderToOutputOut) ;
            (##aluControl`"CGetPerm", ZeroExtendTo Xlen (ToBit (##cs1ECap`"perms"))) ;
            (##aluControl`"CGetType", ZeroExtendTo Xlen #cs1OType) ;
            (##aluControl`"CGetBase", TruncLsb 1 Xlen #cs1Base) ;
            (##aluControl`"CGetTag",  ZeroExtendTo Xlen (ToBit #cs1Tag)) ;
            (##aluControl`"CGetAddr", #cs1Addr) ;
            (##aluControl`"CGetHigh", ZeroExtendTo Xlen (ToBit #encodedCap)) ;
            (##aluControl`"CGetTop",  TruncLsb 1 Xlen #cs1Top) ;
            (##aluControl`"Reg_addr_cs2Addr", #cs2Addr) ;
            (##aluControl`"Reg_addr_zimm5", ZeroExtendTo Xlen #zimm5) ;
            (##aluControl`"Reg_addr_cs1Addr", #cs1Addr) ;
            (##aluControl`"CAndPerm", #cs1Addr) ;
            (##aluControl`"SealOrUnseal", #cs1Addr) ;
            (##aluControl`"CSetBounds", TruncLsb 1 Xlen (##BoundsOut`"base")) ;
            (##aluControl`"Cram", TruncLsb 1 Xlen (##BoundsOut`"cram")) ;
            (##aluControl`"Crrl", TruncLsb 1 Xlen (##BoundsOut`"length")) ;
            (##aluControl`"CTestSubset", ZeroExtendTo Xlen (ToBit #CapSubsetOut)) ;
            (##aluControl`"CSetEqual", ZeroExtendTo Xlen (ToBit #CapEqOut)) ]
          #uimm20 ;

      LetE ecall : Bool <- ##aluControl`"ECall" ;
      LetE ebreak : Bool <- ##aluControl`"EBreak" ;
      LetE isLoad : Bool <- ##aluControl`"Load" ;
      LetE isStore : Bool <- ##aluControl`"Store" ;

      LETE ExceptionRes : Option ExceptionInfo <-
        ExceptionUnit ecall ebreak isLoad isStore
                      fetchExc decodeExc inst
                      cs1Tag cs1ECap AddrBoundsCheckOut AdderBeforeBoundsCheckOut ;

      LetE isFence : Bool <- ##aluControl`"Fence" ;
      LetE storeTag : Bool <- #cs2Tag ;
      LetE storeData : Addr <- #cs2Addr ;
      LETE DeferredOpRes : Option DeferredOp <-
        Deferred isLoad isStore isFence cs1Perms inst AdderBeforeBoundsCheckOut storeTag encodedCap storeData ;

      LetE NewPccVal : FullECapWithTag <-
        STRUCT { "tag" ::= #NewPcc_tag; "ecap" ::= #NewPcc_ecap;
                 "addr" ::= #NewPcc_addr } ;
      LetE NewSpecialVal : FullECapWithTag <-
        STRUCT { "tag" ::= #NewSpecial_tag; "ecap" ::= ##cs1`"ecap";
                 "addr" ::= #cs1Addr } ;
      LetE RegVal : FullECapWithTag <-
        STRUCT { "tag" ::= #Reg_tag; "ecap" ::= #Reg_ecap; "addr" ::= #Reg_addr } ;

      @RetE _ AluOut (STRUCT {
        "NewPcc" ::= #NewPccVal ;
        "NewPccEcap_change" ::= #NewPccEcap_change ;
        "NewPccAddr_change" ::= #NewPccAddr_change ;
        "Exception" ::= #ExceptionRes ;
        "DeferredOp" ::= #DeferredOpRes ;
        "NewInterruptStatus" ::= ##CjalrUnitOut`"interruptStatus" ;
        "NewSpecial" ::= #NewSpecialVal ;
        "Reg" ::= #RegVal
      }).
  End AluRouting.
End Alu.
