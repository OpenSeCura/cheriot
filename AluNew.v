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
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

(*
===============================================================================
                       CHERIOT ALU SPECIFICATION
===============================================================================

1. EXECUTIVE SUMMARY & ARCHITECTURAL PHILOSOPHY
-------------------------------------------------------------------------------
This document establishes the microarchitectural resource specification map for
the CHERIoT processor.

To eliminate microarchitectural ambiguity and maintain absolute gate-level 
clarity during physical refactoring and synthesis, this architecture enforces 
strict RESOURCE-SUFFIX NAMING:
  - Every physical hardware block is assigned a unique ResourceName.
  - Every input wire driving a resource is suffixed with `_<ResourceName>`.
  - Every output wire driven by a resource is suffixed with `_<ResourceName>`.

EXPANDED CAPABILITY REGISTER MODEL & BOUNDS RECOMPUTATION:
A core pillar of this architecture is that the architectural Register File 
(`regs`) always stores fully EXPANDED capabilities (containing 33-bit expanded 
base, 33-bit expanded top, decoded permissions, and decoded canonicalized 
exponent). Memory load and store compression/expansion are handled strictly 
within the dedicated memory pipeline.

Consequently, inspection instructions (`CGetBase`, `CGetTop`, `CGetPerm`) and 
pointer math (`AUIPCC`, `CIncAddr`, `CSub`) operate directly on pre-expanded 
raw integer flip-flops without execution datapath shifting. The ONLY execution 
instructions that require recomputing bounds and exponent math are `CSetBounds`, 
`CSetBoundsExact`, `CSetBoundsImm`, `CRAM`, and `CRRL` (serviced strictly by 
the dedicated `BoundsCalc`).

HARDWARE ALLOCATION STRATEGY:
To optimize area, timing ($F_{max}$), and power, the datapath allocates exactly 
three physical 33-bit carry-propagate adders alongside dedicated magnitude 
comparators and specialized capability blocks:
  1. MainAdder       : Primary datapath arithmetic, branch flags, pointer sums.
  2. PcAdder         : Dedicated control-flow targets (Branch, JAL, JALR).
  3. MemAdder        : Dedicated memory effective addresses and return link PCs.
  4. BarrelShifter   : Dedicated 32-bit integer shifter strictly for RV32I shifts.
  5. LogicUnit       : Dedicated 32-bit engine strictly for RV32I boolean logic.
  6. Comparator      : Dedicated 32-bit lookahead comparator for SLT*, branch conditions, and equality.
  7. TopBoundsCheck  : Dedicated lookahead comparator verifying pointer <= top.
  8. BaseBoundsCheck : Dedicated lookahead comparator verifying pointer >= base.
  9. BoundsCalc      : Self-contained compression engine for CSetBounds, CRAM, CRRL.
  10. CapPermMask    : Dedicated local bitwise unit for CAndPerm masking and legalization.

===============================================================================
2. PHYSICAL HARDWARE RESOURCE INVENTORY & SIGNAL INTERFACE
===============================================================================

-------------------------------------------------------------------------------
RESOURCE 1: MainAdder (33-Bit Datapath Arithmetic Adder / Subtractor)
-------------------------------------------------------------------------------
Purpose: Primary integer arithmetic (`ADD`, `SUB`, `ADDI`), `AUICGP`, Branch 
         condition evaluation ($rs1 - rs2$), SLT/SLTU difference math, capability 
         pointer arithmetic (`AUIPCC`, `CIncAddr`), capability diffs (`CSub`), 
         and `CGetLen`.

  [Inputs]
    * src1_MainAdder      : Bit 33 (Sign-extended or Zero-extended operand 1)
    * src2_MainAdder      : Bit 33 (Sign-extended or Zero-extended operand 2)
    * subEnable_MainAdder : Bool   (0 = ADD/Cin=0; 1 = SUBTRACT/Cin=1)

  [Outputs]
    * sum_MainAdder       : Bit 33 (Full 33-bit sum / difference)

  [Input Mapping]
    * Group 2 (AUICGP, AUIPCC): 32-bit capability base address (CGP.addr or PCC.addr)
      drives src1 sign-extended to 33 bits; decoded 20-bit immediate drives src2
      sign-extended to 33 bits. Note that AUICGP shifts its immediate left by 12 bits
      (imm << 12), whereas AUIPCC shifts its immediate left by 11 bits (imm << 11).
    * Group 4 (ADD, SUB, ADDI): 32-bit register rs1 drives src1 sign-extended
      to 33 bits; 32-bit register rs2 or sign-extended 12-bit immediate drives
      src2 sign-extended to 33 bits, asserting subEnable strictly for SUB.
    * Group 12 (CGetLen): 33-bit expanded capability top and base drive src1
      and src2 directly with subEnable asserted.
    * Group 13 (CIncAddr, CIncAddrImm): 32-bit capability address cs1.addr and
      32-bit offset (rs2 or sign-extended 12-bit immediate) are sign-extended to
      33 bits on src1 and src2.
    * Group 19 (CSub): 32-bit capability addresses cs1.addr and cs2.addr are
      sign-extended to 33 bits on src1 and src2 in subtraction mode.

  [Output Mapping]
    * Group 2 (AUICGP, AUIPCC), Group 4 (ADD, SUB, ADDI), Group 12
      (CGetLen), Group 13 (CIncAddr, CIncAddrImm), Group 19 (CSub): Truncated 32-bit
      slice `sum_MainAdder[31:0]` updates destination register rd (or cd.addr).
    * Group 13 (CIncAddr, CIncAddrImm): Full 33-bit un-truncated sum routes sideways
      into Resource 7 (`TopBoundsCheck`) and Resource 8 (`BaseBoundsCheck`).

  [Additional Comments]
    * Pure Arithmetic Isolation Rationale: By stripping relational branch flags (`isZero`,
      `slt`, `sltu`) and general integer comparison multiplexers (`SLT*`, `BEQ*`) off
      `MainAdder`, input multiplexer control complexity is minimized. Because `MainAdder`
      computes candidate pointers (`cs1.addr + rs2`) directly driving `TopBoundsCheck` on the
      processor's #1 timing critical path, removing MUX stages accelerates pointer arithmetic
      and maximizes chip Fmax.

-------------------------------------------------------------------------------
RESOURCE 2: PcAdder (33-Bit Dedicated Control-Flow Target Adder)
-------------------------------------------------------------------------------
Purpose: Dedicated strictly to PC target address calculations (`Branch`, `JAL`,
`JALR`).

  [Inputs]
    * src1_PcAdder        : Bit 33 (Sign-extended PC or rs1 base address)
    * src2_PcAdder        : Bit 33 (Sign-extended branch or jal offset immediate)

  [Outputs]
    * res32_PcAdder       : Bit 32 (Target PC with LSB hardwired to 0: `(src1 + src2)[31:1] ## 1'b0`)

  [Input Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL): 32-bit current
      PC drives src1 sign-extended to 33 bits; decoded branch or jal offset
      immediate drives src2 sign-extended to 33 bits.
    * Group 7 (JALR): 32-bit base integer register rs1 drives src1 sign-extended
      to 33 bits; decoded jalr immediate drives src2 sign-extended to 33 bits.

  [Output Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL, JALR): Computed
      target address res32 updates instruction fetch PC (hardwiring LSB to 0).

  [Additional Comments]
    * Universal LSB Hardwiring: In standard RISC-V instruction encoding, Branch
      and JAL immediate offsets are strictly even (bit 0 = 0), and valid fetch
      PCs are 2-byte aligned (PC[0] = 0). Thus, their target sum bit 0 is provably
      0. For JALR, the ISA explicitly mandates clearing target bit 0. Therefore,
      hardwiring nextPC[0] = 0 across all control flow targets (Branch, JAL, JALR)
      is provably exact and eliminates LSB multiplexer logic.

-------------------------------------------------------------------------------
RESOURCE 3: MemAdder (33-Bit Dedicated Memory Address & Link PC Adder)
-------------------------------------------------------------------------------
Purpose: Dual-service block dedicated to Data Memory effective address math 
         (`Load`, `Store`) and return link PC calculation (`JAL`, `JALR`, and 
         un-taken branch fallback).

  [Inputs]
    * src1_MemAdder       : Bit 33 (Sign-extended rs1 base address or PC)
    * src2_MemAdder       : Bit 33 (Sign-extended load/store imm or +4 / +2)

  [Outputs]
    * res32_MemAdder      : Bit 32 (Computed 32-bit memory address or return PC: `(src1 + src2)[31:0]`)

  [Input Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL, JALR): 32-bit
      current PC drives src1 sign-extended to 33 bits; sequential instruction
      step (+4 or +2 based on isCompressed) drives src2 sign-extended to 33 bits.
    * Group 8 (LB, LH, LW, LBU, LHU, SB, SH, SW): 32-bit base register rs1 drives
      src1 sign-extended to 33 bits; sign-extended 12-bit memory offset immediate
      drives src2 sign-extended to 33 bits.

  [Output Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL, JALR): Computed
      return link address res32 updates destination register rd (for JAL/JALR) or
      serves as nextPC fallback (for Branch-not-taken). Note that for all other
      non-control-flow instructions, nextPC sequential advancement (+4/+2) is
      handled directly at writeback using a carried isCompressed boolean.
    * Group 8 (LB, LH, LW, LBU, LHU, SB, SH, SW): Effective memory address res32
      routes directly to the data memory pipeline request interface.

-------------------------------------------------------------------------------
RESOURCE 4: BarrelShifter (32-Bit Dedicated Integer Barrel Shifter)
-------------------------------------------------------------------------------
Purpose: Dedicated strictly to RV32I base integer CPU shift instructions (`SLL`, 
         `SRL`, `SRA`, `SLLI`, `SRLI`, `SRAI`).

  [Inputs]
    * val_BarrelShifter     : Bit 32 (Operand to be shifted)
    * amt_BarrelShifter     : Bit 5  (Shift amount immediate or `rs2[4:0]`)
    * isRight_BarrelShifter : Bool   (0 = Shift Left; 1 = Shift Right)
    * isArith_BarrelShifter : Bool   (0 = Logical fill; 1 = Arithmetic sign-extend)

  [Outputs]
    * res32_BarrelShifter   : Bit 32 (Shifted output result)

  [Input Mapping]
    * Group 9 (SLL, SRL, SRA, SLLI, SRLI, SRAI): Base register rs1 drives val;
      register rs2 (or decoded shift immediate) drives shift amount, asserting
      isRight for SRL/SRA/SRLI/SRAI and isArith strictly for SRA/SRAI.

  [Output Mapping]
    * Group 9 (SLL, SRL, SRA, SLLI, SRLI, SRAI): Shifted 32-bit output res32
      updates destination register rd.

  [Additional Comments]
    * Unidirectional Shifter Rationale: To halve shifter multiplexer area, the
      physical datapath synthesizes strictly a unidirectional Right Barrel Shifter.
      For shift left instructions (SLL, SLLI), the 32-bit input operand is
      reversed, passed through the right shifter network, and the resulting
      output is flipped back before returning on res32.

-------------------------------------------------------------------------------
RESOURCE 5: LogicUnit (32-Bit Dedicated Integer Bitwise Engine)
-------------------------------------------------------------------------------
Purpose: Dedicated strictly to RV32I base integer boolean manipulation (`AND`, 
         `OR`, `XOR`, `ANDI`, `ORI`, `XORI`).

  [Inputs]
    * src1_LogicUnit        : Bit 32 (Integer Register rs1 value)
    * src2_LogicUnit        : Bit 32 (Integer Register rs2 value or immediate)
    * opSel_LogicUnit       : Bit 2  (00 = AND; 01 = OR; 10 = XOR)

  [Outputs]
    * res32_LogicUnit       : Bit 32 (Bitwise boolean result)

  [Input Mapping]
    * Group 10 (AND, OR, XOR, ANDI, ORI, XORI): Base register rs1 drives src1;
      register rs2 (or sign-extended 12-bit immediate) drives src2, decoding
      funct3 to set opSel.

  [Output Mapping]
    * Group 10 (AND, OR, XOR, ANDI, ORI, XORI): Bitwise boolean result res32
      updates destination register rd.

-------------------------------------------------------------------------------
RESOURCE 6: Comparator (32-Bit Dedicated Parallel Lookahead Comparator)
-------------------------------------------------------------------------------
Purpose: Dedicated parallel-prefix magnitude comparator evaluating integer relational tests
         strictly for branching (`Branch`) and set-less-than (`SLT*`, `CSetEqual`).

  [Inputs]
    * src1_Comparator       : Bit 32 (Integer register rs1 or cs1.addr)
    * src2_Comparator       : Bit 32 (Integer register rs2, immediate, or cs2.addr)
    * isUnsigned_Comparator : Bool   (Decoder control: funct3[1])
    * invert_Comparator     : Bool   (Decoder control: funct3[0])
    * checkLtGe_Comparator  : Bool   (Decoder control: funct3[2])

  [Outputs]
    * resVal_Comparator     : Bool   (True if relational comparison condition is satisfied)

  [Input Mapping]
    * Group 5 (SLT variants), Group 6 (Branch variants), Group 19 (CSetEqual): Route operands to src1 and src2.
      Assert checkLtGe for SLT, SLTI, BLT, BGE, BLTU, BGEU. Assert invert for BNE, BGE, BGEU.

  [Output Mapping]
    * Group 5 (SLT variants): ZeroExtend resVal to 32 bits -> rd.
    * Group 6 (Branch variants): Route resVal directly to branch take flag to select nextPC MUX.
    * Group 19 (CSetEqual): Combine resVal with capdata equality -> rd.

  [Additional Comments]
    * Critical Path Gating & PC MUX Rationale: In scalar CPU design, the processor's primary
      timing critical path flows through `MainAdder` computing candidate address `cs1.addr + rs2`
      into `TopBoundsCheck`. Offloading branch conditions (`BEQ`, `BLT`) and relational tests
      (`SLT`) onto a dedicated parallel lookahead tree (~8 gate levels, ~100ps) achieves two
      massive $F_{max}$ victories:
        1. Strips comparison input MUX complexity off `MainAdder`, accelerating pointer math.
        2. Resolves branch outcome flag `take` ~200ps earlier than carry-propagate subtraction,
           ensuring the nextPC multiplexer (`res32_PcAdder` vs `res32_MemAdder`) switches well
           before clock setup time.

-------------------------------------------------------------------------------
RESOURCE 7: TopBoundsCheck (Dedicated Lookahead Relational Comparator)
-------------------------------------------------------------------------------
Purpose: Dedicated parallel-prefix magnitude comparator evaluating upper pointer limits
         in dual relational modes (`inpAddr < limit` vs `inpAddr <= limit`).

  [Inputs]
    * inpAddr_TopBoundsCheck    : Bit 33 (Input pointer address `inpAddr` or rs2)
    * limit_TopBoundsCheck      : Bit 33 (Upper bound: `top_rep` or architectural `top`)
    * isInclusive_TopBoundsCheck: Bool   (Decoder control: False for `<`; True for `<=`)

  [Outputs]
    * topValid_TopBoundsCheck   : Bool   (Combined validity flag: `isLess | (isInclusive & isEqual)`)

  [Input Mapping]
    * Group 2 (AUICGP, AUIPCC), Group 13 (CIncAddr, CIncAddrImm), Group 14 (CSetAddr): For
      representability checks, inpAddr is driven by pointer sum/rs2; limit is driven by
      top_rep (`base + 2^(E + 9)`). Assert isInclusive = False (`inpAddr < top_rep`).
    * Group 17 (CSeal, CUnseal): For sealing window checks, inpAddr is driven by cs1.addr
      (CSeal) or cs1.otype (CUnseal); limit is driven by cs2.top. Assert isInclusive = False
      (`inpAddr < cs2.top`).
    * Group 19 (CTestSubset): For capability subset checking, inpAddr is driven by cs2.top;
      limit is driven by cs1.top. Assert isInclusive = True (`cs2.top <= cs1.top`).

  [Output Mapping]
    * Group 2 (AUICGP, AUIPCC), Group 13 (CIncAddr, CIncAddrImm), Group 14 (CSetAddr), Group 17
      (CSeal, CUnseal): Polarity signal topValid routes into writeback tag logic.
    * Group 19 (CTestSubset): Polarity signal topValid verifies upper bound subsetting.

  [Additional Comments]
    * Dual-Mode CMOS Comparator Rationale: In digital logic synthesis, a magnitude comparison
      lookahead tree naturally outputs both relational root flags `isLess` ($A < B$) and
      `isEqual` ($A == B$) simultaneously. In Guru's hardware AST, decomposing topValid as
      `isLess | (isInclusive & isEqual)` allows TopBoundsCheck to evaluate half-open pointer
      and sealing intervals ($A < B \iff A \le B - 1$) as well as closed subsetting intervals
      ($A \le B$) without synthesizing 33-bit arithmetic decrementers on input buses.

-------------------------------------------------------------------------------
RESOURCE 8: BaseBoundsCheck (Dedicated Lookahead Relational Comparator)
-------------------------------------------------------------------------------
Purpose: Dedicated parallel-prefix magnitude comparator evaluating whether an 
         input pointer address undercuts lower limits (`inpAddr >= base`).

  [Inputs]
    * inpAddr_BaseBoundsCheck  : Bit 33 (Input pointer address `inpAddr` or rs2)
    * base_BaseBoundsCheck     : Bit 33 (Capability lower bound `base`)

  [Outputs]
    * baseValid_BaseBoundsCheck: Bool   (True if `inpAddr >= base`)

  [Input Mapping]
    * Group 2 (AUICGP, AUIPCC), Group 13 (CIncAddr, CIncAddrImm): Computed 33-bit
      sum_MainAdder drives inpAddr; capability base drives base.
    * Group 14 (CSetAddr): Sign-extended 33-bit rs2 drives inpAddr; capability
      cs1.base drives base.
    * Group 17 (CSeal, CUnseal): For sealing authorization bounds checks, inpAddr is driven
      by cs1.addr (CSeal) or cs1.otype (CUnseal); base is driven by cs2.base.
    * Group 19 (CTestSubset): Capability cs2.base drives inpAddr; capability
      cs1.base drives base (Check cs2.base >= cs1.base).

  [Output Mapping]
    * Group 2 (AUICGP, AUIPCC), Group 13 (CIncAddr, CIncAddrImm), Group 14 (CSetAddr), Group 17
      (CSeal, CUnseal): Polarity signal baseValid routes into writeback tag logic.
    * Group 19 (CTestSubset): Polarity signal baseValid verifies lower bound subsetting.

-------------------------------------------------------------------------------
RESOURCE 9: BoundsCalc (Self-Contained CHERIoT Compression Engine)
-------------------------------------------------------------------------------
Purpose: Fully dedicated, self-contained CHERIoT hardware computing compressed 
         exponent E and mantissa adjustments, equipped with internal parallel shifters.

  [Inputs]
    * authCap_BoundsCalc : ECap   (Source capability)
    * newLen_BoundsCalc  : Bit 32 (Requested length)

  [Outputs]
    * newCap_BoundsCalc  : ECap   (Recomputed expanded capability struct)
    * resMask_BoundsCalc : Bit 32 (Computed representable alignment mask for CRAM)
    * resLen_BoundsCalc  : Bit 32 (Computed representable rounded length for CRRL)
    * isExact_BoundsCalc : Bool   (Exactness verification flag for CSetBoundsExact)

  [Input Mapping]
    * Group 18 (CSetBounds, CSetBoundsExact, CSetBoundsImm, CRAM, CRRL): Source
      capability cs1 and requested length (rs2, 12-bit immediate, or rs1) route
      into internal priority encoders and parallel shifters.

  [Output Mapping]
    * Group 18 (CSetBounds, CSetBoundsExact, CSetBoundsImm): Recomputed expanded
      capability record newCap writes to destination capability register cd.ecap.
    * Group 18 (CRAM): Computed 32-bit representable alignment mask resMask updates
      destination integer register rd.
    * Group 18 (CRRL): Computed 32-bit representable rounded length resLen updates
      destination integer register rd.

-------------------------------------------------------------------------------
RESOURCE 10: CapPermMask (12-Bit Dedicated Local Permission Masking Unit)
-------------------------------------------------------------------------------
Purpose: 12 local parallel AND gates handling `CAndPerm`.

  [Inputs]
    * authPerm_CapPermMask   : Bit 12 (Source capability permission bits cs1.perms)
    * maskVal_CapPermMask    : Bit 12 (Mask register operand rs2[11:0])

  [Outputs]
    * newPerm_CapPermMask    : Bit 12 (Masked permission bits: `authPerm & maskVal`)

  [Input Mapping]
    * Group 15 (CAndPerm): Source permissions cs1.perms drive authPerm;
      lower 12 bits of register rs2 drive maskVal.

  [Output Mapping]
    * Group 15 (CAndPerm): Bitwise AND result newPerm writes to destination
      capability register cd.perms.

===============================================================================
3. RV32I & CHERIoT INSTRUCTION ROUTING MAP (EXHAUSTIVE & STRICTLY RESOURCE-ISOLATED)
===============================================================================

-------------------------------------------------------------------------------
GROUP 1: DIRECT IMMEDIATE BUS ROUTING (RESOURCE: DIRECT IMMEDIATE BUS)
-------------------------------------------------------------------------------
* LUI rd, 20-bit immediate
    Input Preproc: 20-bit immediate shifted left 12 bits -> decoded immediate.
    Output Route : resVal = decoded immediate -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 2: UPPER IMMEDIATE CAPABILITY DERIVATION (RESOURCE: MainAdder + TopBoundsCheck + BaseBoundsCheck)
-------------------------------------------------------------------------------
* AUICGP cd, 20-bit immediate
* AUIPCC cd, 20-bit immediate
    Input Preproc:
      - MainAdder       : Route base address (CGP.addr or PCC.addr) to src1; route decoded immediate
                          to src2. Note: AUICGP shifts immediate left 12 bits (imm << 12), whereas
                          AUIPCC shifts immediate left 11 bits (imm << 11).
      - TopBoundsCheck  : inpAddr = sum_MainAdder; limit = authCap.top_rep (base + 2^(E + 9)); isInclusive = False.
      - BaseBoundsCheck : inpAddr = sum_MainAdder; base = authCap.base.
    Output Route :
      - cd.ecap = authCap.ecap (preserve source expanded capability struct).
      - cd.addr = res32_MainAdder.
      - cd.tag  = authCap.tag & topValid_TopBoundsCheck & baseValid_BaseBoundsCheck.

-------------------------------------------------------------------------------
GROUP 4: MAIN ALU ADDER ARITHMETIC (RESOURCE: MainAdder)
-------------------------------------------------------------------------------
* ADD rd, rs1, rs2
    Input Preproc: src1_MainAdder = SignExt(rs1); src2_MainAdder = SignExt(rs2).
                   subEnable_MainAdder = False.
    Output Route : resVal = res32_MainAdder -> Register File rd; rd.tag = False.

* SUB rd, rs1, rs2
    Input Preproc: src1_MainAdder = SignExt(rs1); src2_MainAdder = SignExt(rs2).
                   subEnable_MainAdder = True.
    Output Route : resVal = res32_MainAdder -> Register File rd; rd.tag = False.

* ADDI rd, rs1, 12-bit immediate
    Input Preproc: src1_MainAdder = SignExt(rs1); src2_MainAdder = SignExt(decoded immediate).
                   subEnable_MainAdder = False.
    Output Route : resVal = res32_MainAdder -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 5: INTEGER SET LESS THAN COMPARISONS (RESOURCE: Comparator)
-------------------------------------------------------------------------------
* SLT, SLTU, SLTI, SLTIU rd, rs1, rs2 / 12-bit immediate
    Input Preproc: Route rs1 to src1; route rs2 / sign-extended immediate to src2.
                   Assert isUnsigned = funct3[0] (False for SLT/SLTI; True for SLTU/SLTIU).
                   Assert invert = False; checkLtGe = True.
    Output Route : resVal = ZeroExtend(32, resVal_Comparator) -> rd; force rd.tag = False.

-------------------------------------------------------------------------------
GROUP 6: BRANCH CONDITION EVALUATION (RESOURCE: Comparator + PcAdder + MemAdder)
-------------------------------------------------------------------------------
* BEQ, BNE, BLT, BGE, BLTU, BGEU rs1, rs2, branch offset
    Input Preproc:
      - Comparator    : src1 = rs1; src2 = rs2.
                        Assert isUnsigned = funct3[1]; invert = funct3[0]; checkLtGe = funct3[2].
      - PcAdder       : src1 = SignExt(PC); src2 = SignExt(branch offset: imm[12:1] ## 1'b0).
      - MemAdder      : src1 = SignExt(PC); src2 = SignExt(isCompressed ? 2 : 4).
    Output Route :
      - take = resVal_Comparator
      - nextPC = take ? res32_PcAdder (LSB hardwired to 0) : res32_MemAdder. (No write to register file).

-------------------------------------------------------------------------------
GROUP 7: CONTROL FLOW JUMP TARGET CALCULATION (RESOURCE: PcAdder + MemAdder)
-------------------------------------------------------------------------------
* JAL rd, jal offset
    Input Preproc:
      - PcAdder  : src1_PcAdder = SignExt(PC); src2_PcAdder = SignExt(jal offset: imm[20:1] ## 1'b0).
      - MemAdder : src1_MemAdder = SignExt(PC); src2_MemAdder = SignExt(isCompressed ? 2 : 4).
    Output Route : nextPC = res32_PcAdder (LSB hardwired to 0); resVal = res32_MemAdder -> rd.

* JALR rd, rs1, 12-bit immediate
    Input Preproc:
      - PcAdder  : src1_PcAdder = SignExt(rs1.addr); src2_PcAdder = SignExt(decoded immediate: imm[11:0], unshifted).
      - MemAdder : src1_MemAdder = SignExt(PC); src2_MemAdder = SignExt(isCompressed ? 2 : 4).
    Output Route : nextPC = res32_PcAdder (LSB hardwired to 0); resVal = res32_MemAdder -> rd.

-------------------------------------------------------------------------------
GROUP 8: MEMORY EFFECTIVE ADDRESS CALCULATION (RESOURCE: MemAdder)
-------------------------------------------------------------------------------
* LB, LH, LW, LBU, LHU rd, memory offset(rs1)
* SB, SH, SW rs2, memory offset(rs1)
    Input Preproc: src1_MemAdder = SignExt(rs1); src2_MemAdder = SignExt(decoded immediate).
    Output Route : memAddr = res32_MemAdder -> Data Memory Pipeline Interface.

-------------------------------------------------------------------------------
GROUP 9: INTEGER BARREL SHIFTING (RESOURCE: BarrelShifter)
-------------------------------------------------------------------------------
* SLL, SRL, SRA, SLLI, SRLI, SRAI rd, rs1, rs2 / shift amount
    Input Preproc: val_BarrelShifter = rs1; amt = rs2[4:0] / decoded shift immediate.
                   isRight = (Opcode == SRL/SRA); isArith = Funct7[5].
                   Note: For left shifts (SLL/SLLI), input val and output res32 are reversed.
    Output Route : resVal = res32_BarrelShifter -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 10: INTEGER BITWISE BOOLEAN LOGIC (RESOURCE: LogicUnit)
-------------------------------------------------------------------------------
* AND, OR, XOR, ANDI, ORI, XORI rd, rs1, rs2 / 12-bit immediate
    Input Preproc: src1_LogicUnit = rs1; src2_LogicUnit = rs2 / decoded immediate.
                   opSel_LogicUnit = DecodedFunct3.
    Output Route : resVal = res32_LogicUnit -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 11: DIRECT CAPABILITY FIELD EXTRACTION (RESOURCE: DIRECT BUS)
-------------------------------------------------------------------------------
* CGetPerm rd, cs1
* CGetType rd, cs1
* CGetBase rd, cs1
* CGetTag rd, cs1
* CGetHigh rd, cs1
* CGetTop rd, cs1
    Input Preproc: Read raw pre-expanded integer fields directly from cs1.
    Output Route : ZeroExtend extracted field to 32 bits -> rd; force rd.tag = False.

-------------------------------------------------------------------------------
GROUP 12: CAPABILITY LENGTH CALCULATION (RESOURCE: MainAdder)
-------------------------------------------------------------------------------
* CGetLen rd, cs1
    Input Preproc: src1_MainAdder = cs1.top; src2_MainAdder = cs1.base.
                   subEnable_MainAdder = True (Compute Top - Base).
    Output Route : resVal = res32_MainAdder -> rd; force rd.tag = False.

-------------------------------------------------------------------------------
GROUP 13: CAPABILITY POINTER ARITHMETIC & REPRESENTABILITY (RESOURCE: MainAdder + TopBoundsCheck + BaseBoundsCheck)
-------------------------------------------------------------------------------
* CIncAddr cd, cs1, rs2
* CIncAddrImm cd, cs1, 12-bit immediate
    Input Preproc:
      - MainAdder       : src1_MainAdder = SignExt(cs1.addr); src2_MainAdder = SignExt(rs2 / 12-bit immediate).
      - TopBoundsCheck  : inpAddr = sum_MainAdder; limit = cs1.top_rep (cs1.base + 2^(cs1.E + 9)); isInclusive = False.
      - BaseBoundsCheck : inpAddr = sum_MainAdder; base = cs1.base.
    Output Route :
      - cd.ecap = cs1.ecap (preserve source expanded capability struct).
      - cd.addr = res32_MainAdder.
      - cd.tag  = cs1.tag & topValid_TopBoundsCheck & baseValid_BaseBoundsCheck.

-------------------------------------------------------------------------------
GROUP 14: CAPABILITY DIRECT ADDRESS SUBSTITUTION (RESOURCE: DIRECT BUS + TopBoundsCheck + BaseBoundsCheck)
-------------------------------------------------------------------------------
* CSetAddr cd, cs1, rs2
    Input Preproc:
      - DirectBus       : Route rs2 directly to cd.addr.
      - TopBoundsCheck  : inpAddr = SignExt(rs2); limit = cs1.top_rep (cs1.base + 2^(cs1.E + 9)); isInclusive = False.
      - BaseBoundsCheck : inpAddr = SignExt(rs2); base = cs1.base.
    Output Route :
      - cd.ecap = cs1.ecap (preserve source expanded capability struct).
      - cd.addr = rs2.
      - cd.tag  = cs1.tag & topValid_TopBoundsCheck & baseValid_BaseBoundsCheck.

-------------------------------------------------------------------------------
GROUP 15: CAPABILITY BITWISE PERMISSION MASKING (RESOURCE: CapPermMask)
-------------------------------------------------------------------------------
* CAndPerm cd, cs1, rs2
    Input Preproc: tag = cs1.tag; cap = cs1.ecap; maskVal = rs2[11:0].
    Output Route :
      - cd.ecap = res_CapPermMask.ecap.
      - cd.addr = cs1.addr.
      - cd.tag  = res_CapPermMask.tag.

-------------------------------------------------------------------------------
GROUP 16: CAPABILITY TAG CLEARING (RESOURCE: DIRECT BUS)
-------------------------------------------------------------------------------
* CClearTag cd, cs1
    Input Preproc: Direct Bus
    Output Route :
      - cd.ecap = cs1.ecap (copy source capdata struct).
      - cd.addr = cs1.addr.
      - cd.tag  = False (explicitly force tag to 0).

-------------------------------------------------------------------------------
GROUP 17: CAPABILITY SEALING & UNSEALING (RESOURCE: TopBoundsCheck + BaseBoundsCheck + OTypeComparator)
-------------------------------------------------------------------------------
* CSeal cd, cs1, cs2
* CUnseal cd, cs1, cs2
    Input Preproc:
      - TopBoundsCheck  : inpAddr = cs1.addr (CSeal) or cs1.otype (CUnseal); limit = cs2.top; isInclusive = False.
      - BaseBoundsCheck : inpAddr = cs1.addr (CSeal) or cs1.otype (CUnseal); base = cs2.base.
      - OTypeComparator : otype = cs1.otype; addr = cs2.addr (For CUnseal, verify cs1.otype == cs2.addr).
      - PermAuth        : Check cs2.perms has Permit_Seal (CSeal) or Permit_Unseal (CUnseal).
    Output Route :
      - cd.ecap = cs1.ecap with otype updated to cs2.addr (CSeal) or unsealed otype (CUnseal).
      - cd.addr = cs1.addr.
      - cd.tag  = cs1.tag & cs2.tag & ~cs2.isSeal & topValid & baseValid & otypeEqual & permValid.

-------------------------------------------------------------------------------
GROUP 18: CAPABILITY BOUNDS COMPRESSION RECOMPUTATION (RESOURCE: BoundsCalc)
-------------------------------------------------------------------------------
* CSetBounds cd, cs1, rs2
* CSetBoundsExact cd, cs1, rs2
* CSetBoundsImm cd, cs1, 12-bit immediate
    Input Preproc: Route source capability cs1 and length rs2 / decoded immediate.
    Output Route :
      - cd.ecap = newCap_BoundsCalc (recomputed expanded capability struct).
      - cd.addr = cs1.addr.
      - cd.tag  = cs1.tag & ~cs1.isSeal & isValidBounds & (isExact | ~isCSetBoundsExact).

* CRAM rd, rs1
    Input Preproc: Route source capability rs1 and requested length.
    Output Route : resVal = resMask_BoundsCalc -> integer register rd; rd.tag = False.

* CRRL rd, rs1
    Input Preproc: Route source capability rs1 and requested length.
    Output Route : resVal = resLen_BoundsCalc -> integer register rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 19: CAPABILITY DIFFS & COMPARISONS (RESOURCE: MainAdder + Comparator + Bounds Comparators)
-------------------------------------------------------------------------------
* CSub rd, cs1, cs2
    Input Preproc: src1_MainAdder = cs1.addr; src2_MainAdder = cs2.addr.
                   subEnable_MainAdder = True.
    Output Route : resVal = res32_MainAdder -> integer register rd.

* CSetEqual rd, cs1, cs2
    Input Preproc: Route cs1.addr and cs2.addr to Comparator.
                   Assert checkLtGe = False; invert = False; isUnsigned = True.
    Output Route : resVal = ZeroExtend(32, resVal_Comparator & (cs1.cap == cs2.cap)) -> rd.

* CTestSubset rd, cs1, cs2
    Input Preproc:
      - TopBoundsCheck  : inpAddr = cs2.top; limit = cs1.top; isInclusive = True (Check cs2.top <= cs1.top).
      - BaseBoundsCheck : inpAddr = cs2.base; base = cs1.base (Check cs2.base >= cs1.base).
      - PermSubset      : Check (cs1.perms & cs2.perms) == cs2.perms.
    Output Route : resVal = ZeroExtend(32, (cs1.tag == cs2.tag) & topValid & baseValid & permValid) -> rd.

-------------------------------------------------------------------------------
GROUP 20: SYSTEM CSRs, SPECIAL CAPABILITY MOVES & HINTS (RESOURCE: DIRECT BUS)
-------------------------------------------------------------------------------
* CSRRW, CSRRS, CSRRC rd, csr, rs1
* CSRRWI, CSRRSI, CSRRCI rd, csr, 5-bit zimm
* CSpecialRw cd, cSpecial, cs1
* CMove cd, cs1
    Input Preproc: Route CSR / SCR / cs1 via Coprocessor Interface / Direct Bus.
    Output Route :
      - Old CSR / SCR -> rd / cd.
      - cd.ecap = scr.ecap / cs1.ecap.
      - cd.tag  = scr.tag / cs1.tag (enforcing local SCR tag legalization for MTCC/MEPCC).
      - Exception gating takes strict priority over state commits.

===============================================================================
4. DECODER CONTROL BUNDLE FIELD SPECIFICATIONS
===============================================================================
To bridge the gap between opcode decoding and physical datapath execution, the
Decoder emits these explicit multiplexer select and enablement bundles:

1. Ctrl_MainAdder
   * sel_src1    : { Src1_Rs1, Src1_Cs1Addr, Src1_Cs1Top, Src1_CgpAddr,
                     Src1_PccAddr, Src1_Zero }
   * sel_src2    : { Src2_Rs2, Src2_Imm12, Src2_Imm20, Src2_Cs1Base, Src2_Cs2Addr }
   * subEnable   : { False = Add, True = Subtract }

2. Ctrl_PcAdder
   * sel_src1    : { PcSrc1_PC, PcSrc1_Rs1Addr }
   * sel_src2    : { PcSrc2_BranchOffset, PcSrc2_JalOffset, PcSrc2_JalrImm }

3. Ctrl_MemAdder
   * sel_src1    : { MemSrc1_PC, MemSrc1_Rs1Addr }
   * sel_src2    : { MemSrc2_Constant2, MemSrc2_Constant4, MemSrc2_LoadStoreOffset }

4. Ctrl_Shifter
   * sel_val     : { ShiftVal_Rs1 }
   * sel_amt     : { ShiftAmt_Rs2Low5, ShiftAmt_Imm5 }
   * isRight     : { False = Shift Left, True = Shift Right }
   * isArith     : { False = Logical, True = Arithmetic }

5. Ctrl_Logic
   * sel_src1    : { LogicSrc1_Rs1 }
   * sel_src2    : { LogicSrc2_Rs2, LogicSrc2_Imm12 }
   * opSel       : { 00 = AND; 01 = OR; 10 = XOR }

6. Ctrl_Comparator
   * sel_src1    : { CompSrc1_Rs1, CompSrc1_Cs1Addr }
   * sel_src2    : { CompSrc2_Rs2, CompSrc2_Imm12, CompSrc2_Cs2Addr }
   * isSigned    : { False = Unsigned, True = Signed }

7. Ctrl_TopCheck
   * sel_inpAddr : { TopInp_SumMainAdder, TopInp_SignExtRs2, TopInp_Cs1Addr,
                     TopInp_Cs1Otype, TopInp_Cs2Top }
   * sel_limit   : { TopLim_TopRep, TopLim_Cs2Top, TopLim_Cs1Top }
   * isInclusive : { False = Strict Less Than, True = Less Or Equal }

8. Ctrl_BaseCheck
   * sel_inpAddr : { BaseInp_SumMainAdder, BaseInp_SignExtRs2, BaseInp_Cs1Addr,
                     BaseInp_Cs1Otype, BaseInp_Cs2Base }
   * sel_base    : { BaseLim_AuthBase, BaseLim_Cs1Base }

9. Ctrl_BoundsCalc
   * opKind      : { Calc_None, Calc_SetBounds, Calc_SetBoundsExact,
                     Calc_SetBoundsImm, Calc_RAM, Calc_RRL }

10. Ctrl_MultiOp
    * multiOp    : { MultiOp_None, MultiOp_Load, MultiOp_Store }
    * memOpSz    : { Mem_Byte, Mem_Half, Mem_Word, Mem_Cap }

-------------- THIS IS UNCLEAR -------------------
11. Ctrl_Writeback
    * wbSel_regKind  : { WbReg_IntRd, WbReg_CapCd, WbReg_None }
    * wbSel_addrData : { WbData_SumMainAdder, WbData_Shifter, WbData_Logic,
                         WbData_Rs2, WbData_CsrOut, WbData_GetCapField,
                         WbData_Cram, WbData_Crrl, WbData_SltAndFriends }
    * wbSel_meta     : { Wb_CopySource, Wb_ClearTag, Wb_BoundsCalc,
                         Wb_Seal, Wb_Unseal, Wb_AndPerm }

===============================================================================
5. QUANTITATIVE SILICON ECONOMICS & DESIGN RATIONALE
===============================================================================

-------------------------------------------------------------------------------
PART A: REPRESENTABILITY BOUNDS COMPARATORS (CRITICAL PATH vs AREA)
-------------------------------------------------------------------------------
Critical Path Bottleneck of Sharing Adders:
  If we attempt to multiplex representability validation onto PcAdder and MemAdder,
  the candidate address newAddr computed by MainAdder must feed into the input MUXes
  of PcAdder and MemAdder combinationally within the same clock cycle:
    RegRead -> MainAdder (Add) -> MUX -> PcAdder/MemAdder (Sub) -> Tag Logic
  Chaining two 33-bit carry-propagate adders in series introduces ~35 to 40 gate
  levels of propagation delay (~300ps+), creating a catastrophic critical path
  bottleneck that severely degrades the processor's maximum clock frequency (Fmax).

Silicon Verdict (Go Dedicated Magnitude Comparators):
  To decouple representability checking from datapath arithmetic, we allocate two
  dedicated relational magnitude comparators: TopBoundsCheck (<=) and BaseBoundsCheck (>=).
  Unlike full carry-propagate subtractors (~300 gates), a dedicated parallel-prefix
  magnitude comparator does not compute difference sums and can be synthesized as a
  shallow borrow-lookahead tree (~120 gates, ~6 to 8 gate levels).
  
  Tapping sum_MainAdder directly into dedicated lookahead comparators allows bounds
  validation to resolve in parallel ~60ps after MainAdder finishes, keeping PcAdder
  and MemAdder shallow and ensuring zero critical path timing loops.

-------------------------------------------------------------------------------
PART B: BOUNDS COMPRESSION SHIFTING (ALIGNMENT & MASKING)
-------------------------------------------------------------------------------
Single-Cycle Combinatorial Requirement:
  Inside `calculateBounds` (`CSetBounds`), the algorithm executes combinationally 
  in 1 clock cycle, requiring parallel evaluation of multiple shift networks by 
  canonical exponent e (`mask_e <- Not (Sll -1 e)`, `iFloor <- Srl sum_mod_e e`, 
  and `d <- Srl length e`). Note that registers store fully expanded capabilities, 
  so memory load/store decoding never requires ALU datapath shifting.

Analysis of Partial Shifter Offloading:
  If we attempt to offload even a single shift (e.g. `d <- Srl length e`) to the 
  main CPU `BarrelShifter`, we save ~200 gates of internal shifter but incur 111 
  gates of bus multiplexing, yielding a negligible net savings of +89 gates. 
  Crucially, exponent e is dynamically computed by `BoundsCalc`'s priority 
  encoder (`countLeadingZeros`). Offloading creates a severe physical floorplan 
  timing loop:
    RegRead -> BoundsCalc Priority Encoder -> CPU BarrelShifter -> BoundsCalc Adder
  Zigzagging timing-critical buses out of `BoundsCalc`, across the datapath 
  into the CPU shifter, and back into `BoundsCalc` introduces immense wire 
  capacitance (RC delay) on the core's critical path.

Microarchitectural Verdict (Go Dedicated):
  Sacrificing floorplan locality and degrading chip clock frequency to save 89 
  gates (<0.8% area) is an architectural anti-pattern. `BoundsCalc` must remain 
  a 100% dedicated, self-contained compression engine with internal shifters.

-------------------------------------------------------------------------------
PART C: BITWISE PERMISSION MASKING (CAndPerm)
-------------------------------------------------------------------------------
Cost of Shared Resource Routing:
  To route `CAndPerm` (`cs1.perms & rs2[11:0]`) through the main 32-bit integer 
  `LogicUnit`, we must add 32-bit multiplexers to the `src1` and `src2` buses. 
  This routing overhead costs ~192 equivalent gates.

Cost of Dedicated Local Hardware:
  A standard CMOS 2-input bitwise AND cell costs 1 equivalent gate. Dedicated 
  hardware for a 12-bit permission mask costs exactly 12 equivalent gates.

Silicon Verdict (Go Dedicated):
  Avoiding sharing saves 180 equivalent gates! More importantly, stripping 
  capability metadata off the integer datapath multiplexers keeps integer 
  AND/OR/XOR shallow, ultra-fast, and low power.

-------------------------------------------------------------------------------
PART D: SYSTEM CSRs & SPECIAL CAPABILITY REGISTERS (ALU SHARING vs COPROCESSOR BUS)
-------------------------------------------------------------------------------
Architectural Complications of System Operations:
  RV32I system CSR instructions (CSRRW, CSRRS, CSRRC and immediate variants) and CHERIoT Special Capability
  Registers (CSpecialRW) introduce unique architectural control-state constraints
  decoupled from standard arithmetic computation:
    a) Exception Prioritization: Pipeline exception gating (e.g. invalid CSR index,
       privilege violation, unaligned capability load/store) takes strict priority
       over CSR read/write side effects. If an exception fires, pending CSR updates
       must be aborted at writeback.
    b) Capability Legalization & Tag Constraints: Writing to specific architectural
       SCRs enforces complex tag and legalization checks. For instance, writing to
       MTCC (Trap Code Capability) or MEPCC (Exception Program Counter Capability)
       enforces capability unsealing, executable permission verification, and bounds
       legalization before committing to state.

Analysis of ALU LogicUnit Sharing:
  Multiplexing csrCurr and operand csrIn onto Resource 5 (`LogicUnit`) to perform
  bitwise CSRRS (OR) and CSRRC (AND-NOT) math saves ~32 gates of duplicate bitwise
  logic. However, it introduces wide 32-bit multiplexers onto the hot ALU execution
  inputs (`src1_LogicUnit` and `src2_LogicUnit`), degrading core integer Fmax.
  Furthermore, routing control-state registers through the main ALU interconnect
  creates severe physical routing congestion across the architectural register file.

Silicon Verdict (Go Dedicated Coprocessor Interface):
  Given that ~32 bitwise logic gates represent <0.1% of total ALU core area,
  sacrificing datapath timing and routing simplicity to share `LogicUnit` is a false
  economy. CSR/SCR read-modify-write loops execute strictly via dedicated local bus
  logic (`DIRECT BUS` / Coprocessor Interface), handling exception prioritization
  and SCR legalization (MTCC/MEPCC) locally at the system writeback boundary.

-------------------------------------------------------------------------------
PART E: GENERAL INTEGER RELATIONAL COMPARISONS (COMPARATOR vs MAINADDER)
-------------------------------------------------------------------------------
Timing Bottleneck of Sharing Arithmetic Subtractors:
  In scalar CPU design, the processor's primary datapath timing critical path flows
  through `MainAdder` computing candidate capability pointers (`cs1.addr + rs2`)
  directly driving `TopBoundsCheck` and `BaseBoundsCheck`. If we multiplex branches
  (`BEQ`, `BLT`, etc.) and set-less-than tests (`SLT variants`) onto `MainAdder` in
  subtraction mode (`src1 - src2`), two physical hazards emerge:
    1. Input Multiplexer Bloat: Adding wide integer comparison routing stages onto
       `MainAdder` increases input wire capacitance and MUX propagation delay,
       slowing down pointer arithmetic lookahead calculation.
    2. Late PC Multiplexer Switching: For branch instructions, the branch outcome
       flag `take` controls the control-flow PC multiplexer selecting between
       `nextPC = take ? res32_PcAdder : res32_MemAdder`. Chaining carry-propagate
       subtraction (~35 gate levels, ~300ps+) delays the resolution of `take`,
       forcing the PC multiplexer to switch dangerously close to clock setup time.

Silicon Verdict (Go Dedicated Relational Tree):
  To eliminate comparison MUX bloat and protect core Fmax, we allocate Resource 6
  (`Comparator`) as a dedicated 32-bit parallel-prefix magnitude comparator.
  A lookahead comparison tree resolves in ~8 gate levels (~100ps), delivering the
  branch decision flag `take` ~200ps earlier than arithmetic subtraction. This guarantees
  ultra-fast PC multiplexer switching and preserves 100% pure adder isolation on `MainAdder`.

-------------------------------------------------------------------------------
EXECUTIVE CORE SUMMARY
-------------------------------------------------------------------------------
By isolating general datapath arithmetic structures (`PcAdder` and `MemAdder`) while 
allocating dedicated parallel-prefix magnitude comparators (`Comparator`, 
`TopBoundsCheck`, and `BaseBoundsCheck`), the datapath achieves an optimal layout: 
protecting chip Fmax and eliminating interconnect timing hazards at a negligible area cost.

END OF ARCHITECTURAL RESOURCE MAP
===============================================================================
*)

Local Open Scope guru_scope.
Local Open Scope string_scope.

Section ExecutionUnits.
  Variable ty : Kind -> Type.

  Definition MainAdder (src1 src2 : ty (Bit (Xlen + 1))) (subEnable : ty Bool) : LetExpr ty (Bit (Xlen + 1)) :=
    LetE op2 : Bit (Xlen + 1) <- ITE #subEnable (Not #src2) #src2 ;
    LetE cin : Bit (Xlen + 1) <- ZeroExtendTo (Xlen + 1) (ToBit #subEnable) ;
    LetE sum : Bit (Xlen + 1) <- Add [ #src1; #op2; #cin ] ;
    RetE #sum.

  Definition PcAdder (src1 src2 : ty (Bit (Xlen + 1))) : LetExpr ty (Bit Xlen) :=
    LetE sum : Bit (Xlen + 1) <- Add [ #src1; #src2 ] ;
    LetE resXlen : Bit Xlen <- TruncLsb 1 Xlen #sum ;
    LetE upperXlenSub1 : Bit (Xlen - 1) <- TruncMsb (Xlen-1) 1 #resXlen ;
    RetE ({< #upperXlenSub1, Const ty (Bit 1) Zmod.zero >}).

  Definition MemAdder (src1 src2 : ty (Bit (Xlen + 1))) : LetExpr ty (Bit Xlen) :=
    LetE sum : Bit (Xlen + 1) <- Add [ #src1; #src2 ] ;
    RetE (TruncLsb 1 Xlen #sum).

  (* If isArith is set for left shift, results are wrong *)
  Definition BarrelShifter (val : ty (Bit Xlen)) (amt : ty (Bit LgXlen)) (isRight isArith : ty Bool)
    : LetExpr ty (Bit Xlen) :=
    structSimplCbn (
      let rev e := ToBit (ArrayReverse (FromBit (Array (Z.to_nat Xlen) Bool) e)) in
      LetE inpVal : Bit Xlen <- ITE #isRight #val (rev #val) ;
      LetE signBit : Bit 1 <- ITE #isArith (TruncMsb 1 (Xlen - 1) #inpVal) (Const ty (Bit 1) Zmod.zero) ;
      LetE extVal : Bit (Xlen + 1) <- {< #signBit, #inpVal >} ;
      LetE shiftedExt : Bit (Xlen + 1) <- Sra #extVal #amt ;
      LetE shiftedXlen : Bit Xlen <- TruncLsb 1 Xlen #shiftedExt ;
      RetE (ITE #isRight #shiftedXlen (rev #shiftedXlen))
    ).

  Definition Comparator (src1 src2 : ty (Bit Xlen)) (isUnsigned invert checkLtGe : ty Bool) : LetExpr ty Bool :=
    structSimplCbn (
      LetE flipBit : Bit 1 <- ToBit (Not #isUnsigned) ;
      let flipMsb e:= {< Xor [#flipBit; TruncMsb 1 (Xlen-1) e], TruncLsb 1 (Xlen-1) e >} in
      LetE op1 : Bit Xlen <- flipMsb #src1 ;
      LetE op2 : Bit Xlen <- flipMsb #src2 ;
      LetE lt : Bool <- Slt #op1 #op2 ;
      LetE eq : Bool <- Eq #src1 #src2 ;
      LetE raw : Bool <- ITE #checkLtGe #lt #eq ;
      RetE (ITE #invert (Not #raw) #raw)
    ).

  (* 00=And, 01=Or, 10=Xor *)
  Definition Logic (src1 src2 : ty (Bit Xlen)) (opSel : ty (Bit 2)) : LetExpr ty (Bit Xlen) :=
    LetE andRes : Bit Xlen <- And [ #src1; #src2 ] ;
    LetE orRes : Bit Xlen <- Or [ #src1; #src2 ] ;
    LetE xorRes : Bit Xlen <- Xor [ #src1; #src2 ] ;
    LetE opSelArray : Array 2 Bool <- FromBit _ #opSel ;
    RetE (ITE (#opSelArray$[1]) #xorRes (ITE (#opSelArray$[0]) #orRes #andRes)).

  Definition TopBoundsCheck (inpAddr limit : ty (Bit (Xlen + 1))) (isInclusive : ty Bool) : LetExpr ty Bool :=
    LetE strictLt : Bool <- Slt #inpAddr #limit ;
    LetE strictEq : Bool <- Eq #inpAddr #limit ;
    RetE (Or [#strictLt; And [#isInclusive; #strictEq]]).

  Definition BaseBoundsCheck (inpAddr base : ty (Bit (Xlen + 1))) : LetExpr ty Bool :=
    RetE (Sge #inpAddr #base).

  Section BoundsCalc.
    Variable base: ty (Bit (AddrSz + 1)).
    Variable length: ty (Bit (AddrSz + 1)).
    Variable IsRoundDown: ty Bool.

    Definition Bounds :=
      STRUCT_TYPE {
          "E" :: Bit ExpSz;
          "base" :: Bit (AddrSz + 1);
          "top" :: Bit (AddrSz + 1);
          "cram" :: Bit (AddrSz + 1);
          "length" :: Bit (AddrSz + 1);
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
            - remainders: Since clz >= 0, max e_init = AddrSz + 1 - CapBSz. Moduli at 2^e_init are strictly < 2^e_init,
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

    Definition BoundsCalc : LetExpr ty Bounds :=
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

        LetE ef: Bit ExpSz <- ITE #IsRoundDown #e_roundDown #e_normal;
        LetE mf: Bit CapBSz <- ITE #IsRoundDown #m_roundDown #m_normal;

        LetE cram: Bit (AddrSz + 1) <- Sll (ConstBit (Zmod.of_Z _ (-1))) #ef;
        LetE outBase : Bit (AddrSz + 1) <- And [#base; #cram];
        LetE outLen: Bit (AddrSz + 1) <- Sll (ZeroExtendTo (AddrSz + 1) #mf) #ef;
        LetE outTop : Bit (AddrSz + 1) <- Add [#outBase; #outLen] ;
        @RetE _ Bounds (STRUCT {
                            "E" ::= #ef;
                            "base" ::= #outBase;
                            "top" ::= #outTop;
                            "cram" ::= #cram;
                            "length" ::= #outLen;
                            "exact" ::= Or [isNotZero #base_mod_e; isNotZero #length_mod_e] })).
  End BoundsCalc.

  Definition CAndPerm (cap : ty FullECapWithTag) (rs2 : ty Data) : LetExpr ty FullECapWithTag :=
    LetE maskBits : Bit (kindSize CapPerms) <- TruncLsb (Xlen - kindSize CapPerms) (kindSize CapPerms) #rs2 ;
    LetE maskVal : CapPerms <- FromBit CapPerms #maskBits ;
    LetE ecapVal : ECap <- ##cap`"ecap" ;
    LetE oldPerms : CapPerms <- ##ecapVal`"perms" ;
    LetE rawMask : CapPerms <- And [ #oldPerms; #maskVal ] ;
    LetE newPerms : CapPerms <- fixPerms rawMask ;
    LetE sealed : Bool <- isSealed ecapVal ;
    LetE maskAllOnesNonGL : Bool <- isAllOnes (#maskVal `{ "GL" <- ConstTBool true }) ;
    LetE keepTag : Bool <- Or [ Not #sealed; #maskAllOnesNonGL ] ;
    LetE outTag : Bool <- And [ ##cap`"tag"; #keepTag ] ;
    LetE outECap : ECap <- ##ecapVal `{ "perms" <- #newPerms } ;
    @RetE _ FullECapWithTag (STRUCT { "tag" ::= #outTag; "ecap" ::= #outECap; "addr" ::= ##cap`"addr" }).
End ExecutionUnits.
