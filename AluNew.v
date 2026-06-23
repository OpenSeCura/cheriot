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
This document establishes the microarchitectural execute unit specification map for
the CHERIoT processor.

To eliminate microarchitectural ambiguity and maintain absolute gate-level 
clarity during physical refactoring and synthesis, this architecture enforces 
strict EXECUTE-UNIT DOT NAMING:
  - Every physical hardware block is assigned a unique ExecuteUnitName.
  - Every input or output of an execute unit is prefixed with `ExecuteUnitName_`.

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
  1. MainAdder        : Primary datapath arithmetic, branch flags, pointer sums.
  2. PcAdder          : Dedicated control-flow targets (Branch, JAL, JALR).
  3. MemAdder         : Dedicated memory effective addresses and return link PCs.
  4. Shifter          : Dedicated 32-bit integer shifter strictly for RV32I shifts.
  5. LogicUnit        : Dedicated 32-bit engine strictly for RV32I boolean logic.
  6. Comparator       : Dedicated 32-bit lookahead comparator for SLT*, branch conditions, and equality.
  7. TopBoundsCheck   : Dedicated lookahead comparator verifying pointer <= top.
  8. BaseBoundsCheck  : Dedicated lookahead comparator verifying pointer >= base.
  9. BoundsCalc       : Self-contained compression engine for CSetBounds, CRAM, CRRL.
  10. CAndPerm        : Dedicated local bitwise unit for CAndPerm masking and legalization.
  11. SealerUnsealer  : Dedicated local authorization and object-type tagging unit for CSeal/CUnseal.
  12. ScrSanitizer    : Dedicated local capability sanitization unit for special scratch registers.
  13. BranchJalPccTag : Dedicated control-flow target representability and tag validation unit.
  14. CjalrPcc        : Dedicated CJALR target capability metadata, tag, and interrupt evaluation unit.
  15. MultiOp         : Dedicated memory effective address and multicycle system interaction unit.

===============================================================================
2. PHYSICAL HARDWARE EXECUTE UNIT INVENTORY & SIGNAL INTERFACE
===============================================================================

-------------------------------------------------------------------------------
EXECUTE UNIT 1: MainAdder (33-Bit Datapath Arithmetic Adder / Subtractor)
-------------------------------------------------------------------------------
Purpose: Primary integer arithmetic (`ADD`, `SUB`, `ADDI`), `AUICGP`, Branch 
         condition evaluation ($rs1 - rs2$), SLT/SLTU difference math, capability 
         pointer arithmetic (`AUIPCC`, `CIncAddr`), capability diffs (`CSub`), 
         and `CGetLen`.

  [Inputs]
    * MainAdder_src1      : Bit 33 (Sign-extended or Zero-extended operand 1)
    * MainAdder_src2      : Bit 33 (Sign-extended or Zero-extended operand 2)
    * MainAdder_subEnable : Bool   (0 = ADD/Cin=0; 1 = SUBTRACT/Cin=1)

  [Outputs]
    * MainAdder_sum       : Bit 33 (Full 33-bit sum / difference)
    * MainAdder_res       : Bit 32 (Derived truncated slice `MainAdder_sum[31:0]`)

  [Input Mapping]
    * Group 2 (AUICGP, AUIPCC): 32-bit capability base address (CGP.addr or PCC.addr)
      drives src1 sign-extended to 33 bits; decoded 20-bit immediate drives src2
      sign-extended to 33 bits. Note that both AUICGP and AUIPCC shift their immediate
      left by exactly 11 bits (imm << 11).
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
      slice `MainAdder_sum[31:0]` updates destination register rd (or cd.addr).
    * Group 13 (CIncAddr, CIncAddrImm): Full 33-bit un-truncated sum routes sideways
      into Execute Unit 7 (`TopBoundsCheck`) and Execute Unit 8 (`BaseBoundsCheck`).

  [Additional Comments]
    * Pure Arithmetic Isolation Rationale: By stripping relational branch flags (`isZero`,
      `slt`, `sltu`) and general integer comparison multiplexers (`SLT*`, `BEQ*`) off
      `MainAdder`, input multiplexer control complexity is minimized. Because `MainAdder`
      computes candidate pointers (`cs1.addr + rs2`) directly driving `TopBoundsCheck` on the
      processor's #1 timing critical path, removing MUX stages accelerates pointer arithmetic
      and maximizes chip Fmax.

-------------------------------------------------------------------------------
EXECUTE UNIT 2: PcAdder (33-Bit Dedicated Control-Flow Target Adder)
-------------------------------------------------------------------------------
Purpose: Dedicated strictly to PC target address calculations (`Branch`, `JAL`,
`JALR`).

  [Inputs]
    * PcAdder_src1 : Bit 33 (Sign-extended PC or rs1 base address)
    * PcAdder_src2 : Bit 33 (Sign-extended branch or jal offset immediate)

  [Outputs]
    * PcAdder_res  : Bit 32 (Target PC with LSB hardwired to 0: `(src1 + src2)[31:1] ## 1'b0`)

  [Input Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL): 32-bit current
      PC drives src1 sign-extended to 33 bits; decoded branch or jal offset
      immediate drives src2 sign-extended to 33 bits.
    * Group 7 (JALR): 32-bit capability base address cs1.addr drives src1 sign-extended
      to 33 bits; decoded jalr immediate drives src2 sign-extended to 33 bits.

  [Output Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL, JALR): Computed
      target address res updates instruction fetch PC (hardwiring LSB to 0).

  [Additional Comments]
    * Universal LSB Hardwiring: In standard RISC-V instruction encoding, Branch
      and JAL immediate offsets are strictly even (bit 0 = 0), and valid fetch
      PCs are 2-byte aligned (PC[0] = 0). Thus, their target sum bit 0 is provably
      0. For JALR, the ISA explicitly mandates clearing target bit 0. Therefore,
      hardwiring nextPC[0] = 0 across all control flow targets (Branch, JAL, JALR)
      is provably exact and eliminates LSB multiplexer logic.

-------------------------------------------------------------------------------
EXECUTE UNIT 3: MemAdder (33-Bit Dedicated Memory Address & Link PC Adder)
-------------------------------------------------------------------------------
Purpose: Dual-service block dedicated to Data Memory effective address math 
         (`Load`, `Store`) and return link PC calculation (`JAL`, `JALR`, and 
         un-taken branch fallback).

  [Inputs]
    * MemAdder_src1 : Bit 33 (Sign-extended rs1 base address or PC)
    * MemAdder_src2 : Bit 33 (Sign-extended load/store imm or +4 / +2)

  [Outputs]
    * MemAdder_res  : Bit 32 (Computed 32-bit memory address or return PC: `(src1 + src2)[31:0]`)

  [Input Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL, JALR): 32-bit
      current PC drives src1 sign-extended to 33 bits; sequential instruction
      step (+4 or +2 based on isCompressed) drives src2 sign-extended to 33 bits.
    * Group 8 (LB, LH, LW, LBU, LHU, SB, SH, SW): 32-bit base register rs1 drives
      src1 sign-extended to 33 bits; sign-extended 12-bit memory offset immediate
      drives src2 sign-extended to 33 bits.

  [Output Mapping]
    * Group 6 (BEQ, BNE, BLT, BGE, BLTU, BGEU), Group 7 (JAL, JALR): Computed
      return link address res updates destination register rd (for JAL/JALR) or
      serves as nextPC fallback (for Branch-not-taken). Note that for all other
      non-control-flow instructions, nextPC sequential advancement (+4/+2) is
      handled directly at writeback using a carried isCompressed boolean.
    * Group 8 (LB, LH, LW, LBU, LHU, SB, SH, SW): Effective memory address res
      routes directly to the data memory pipeline request interface.

-------------------------------------------------------------------------------
EXECUTE UNIT 4: Shifter (32-Bit Dedicated Integer Barrel Shifter)
-------------------------------------------------------------------------------
Purpose: Dedicated strictly to RV32I base integer CPU shift instructions (`SLL`, 
         `SRL`, `SRA`, `SLLI`, `SRLI`, `SRAI`).

  [Inputs]
    * Shifter_val     : Bit 32 (Operand to be shifted)
    * Shifter_amt     : Bit 5  (Shift amount immediate or `rs2[4:0]`)
    * Shifter_isRight : Bool   (0 = Shift Left; 1 = Shift Right)
    * Shifter_isArith : Bool   (0 = Logical fill; 1 = Arithmetic sign-extend)

  [Outputs]
    * Shifter_res     : Bit 32 (Shifted output result)

  [Input Mapping]
    * Group 9 (SLL, SRL, SRA, SLLI, SRLI, SRAI): Base register rs1 drives val;
      register rs2 (or decoded shift immediate) drives shift amount, asserting
      isRight for SRL/SRA/SRLI/SRAI and isArith strictly for SRA/SRAI.

  [Output Mapping]
    * Group 9 (SLL, SRL, SRA, SLLI, SRLI, SRAI): Shifted 32-bit output res
      updates destination register rd.

  [Additional Comments]
    * Unidirectional Shifter Rationale: To halve shifter multiplexer area, the
      physical datapath synthesizes strictly a unidirectional Right Barrel Shifter.
      For shift left instructions (SLL, SLLI), the 32-bit input operand is
      reversed, passed through the right shifter network, and the resulting
      output is flipped back before returning on res.

-------------------------------------------------------------------------------
EXECUTE UNIT 5: LogicUnit (32-Bit Dedicated Integer Bitwise Engine)
-------------------------------------------------------------------------------
Purpose: Dedicated strictly to RV32I base integer boolean manipulation (`AND`, 
         `OR`, `XOR`, `ANDI`, `ORI`, `XORI`).

  [Inputs]
    * LogicUnit_src1  : Bit 32 (Integer Register rs1 value)
    * LogicUnit_src2  : Bit 32 (Integer Register rs2 value or immediate)
    * LogicUnit_opSel : Bit 2  (00 = AND; 01 = OR; 10 = XOR)

  [Outputs]
    * LogicUnit_res   : Bit 32 (Bitwise boolean result)

  [Input Mapping]
    * Group 10 (AND, OR, XOR, ANDI, ORI, XORI): Base register rs1 drives src1;
      register rs2 (or sign-extended 12-bit immediate) drives src2, decoding
      funct3 to set opSel.

  [Output Mapping]
    * Group 10 (AND, OR, XOR, ANDI, ORI, XORI): Bitwise boolean result res
      updates destination register rd.

-------------------------------------------------------------------------------
EXECUTE UNIT 6: Comparator (32-Bit Dedicated Parallel Lookahead Comparator)
-------------------------------------------------------------------------------
Purpose: Dedicated parallel-prefix magnitude comparator evaluating integer relational tests
         strictly for branching (`Branch`) and set-less-than (`SLT*`, `CSetEqual`).

  [Inputs]
    * Comparator_src1       : Bit 32 (Integer register rs1 or cs1.addr)
    * Comparator_src2       : Bit 32 (Integer register rs2, immediate, or cs2.addr)
    * Comparator_isUnsigned : Bool   (Decoder control: funct3[1])
    * Comparator_invert     : Bool   (Decoder control: funct3[0])
    * Comparator_checkLtGe  : Bool   (Decoder control: funct3[2])

  [Outputs]
    * Comparator_resVal     : Bool   (True if relational comparison condition is satisfied)

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
           ensuring the nextPC multiplexer (`PcAdder_res` vs `MemAdder_res`) switches well
           before clock setup time.

-------------------------------------------------------------------------------
EXECUTE UNIT 7: TopBoundsCheck (Dedicated Lookahead Relational Comparator)
-------------------------------------------------------------------------------
Purpose: Dedicated parallel-prefix magnitude comparator evaluating upper pointer limits
         in dual relational modes (`inpAddr < limit` vs `inpAddr <= limit`).

  [Inputs]
    * TopBoundsCheck_inpAddr     : Bit 33 (Input pointer address `inpAddr` or rs2)
    * TopBoundsCheck_limit       : Bit 33 (Upper bound: `top_rep` or architectural `top`)
    * TopBoundsCheck_isInclusive : Bool   (Decoder control: False for `<`; True for `<=`)

  [Outputs]
    * TopBoundsCheck_topValid    : Bool   (Combined validity flag: `isLess | (isInclusive & isEqual)`)

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
EXECUTE UNIT 8: BaseBoundsCheck (Dedicated Lookahead Relational Comparator)
-------------------------------------------------------------------------------
Purpose: Dedicated parallel-prefix magnitude comparator evaluating whether an 
         input pointer address undercuts lower limits (`inpAddr >= base`).

  [Inputs]
    * BaseBoundsCheck_inpAddr   : Bit 33 (Input pointer address `inpAddr` or rs2)
    * BaseBoundsCheck_base      : Bit 33 (Capability lower bound `base`)

  [Outputs]
    * BaseBoundsCheck_baseValid : Bool   (True if `inpAddr >= base`)

  [Input Mapping]
    * Group 2 (AUICGP, AUIPCC), Group 13 (CIncAddr, CIncAddrImm): Computed 33-bit
      MainAdder_sum drives inpAddr; capability base drives base.
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
EXECUTE UNIT 9: BoundsCalc (Self-Contained CHERIoT Compression Engine)
-------------------------------------------------------------------------------
Purpose: Fully dedicated, self-contained CHERIoT hardware computing compressed 
         exponent E and mantissa adjustments, equipped with internal parallel shifters.

  [Inputs]
    * BoundsCalc_base        : Bit (AddrSz + 1) (Candidate base capability address)
    * BoundsCalc_length      : Bit (AddrSz + 1) (Candidate requested length)
    * BoundsCalc_isRoundDown : Bool             (True for CRAM/CRRL rounding down mode)

  [Outputs]
    * BoundsCalc_outE        : Bit ExpSz        (Computed canonical exponent)
    * BoundsCalc_outBase     : Bit (AddrSz + 1) (Computed representable base address)
    * BoundsCalc_outTop      : Bit (AddrSz + 1) (Computed representable top address)
    * BoundsCalc_cram        : Bit (AddrSz + 1) (Computed representable alignment mask for CRAM)
    * BoundsCalc_outLen      : Bit (AddrSz + 1) (Computed representable rounded length for CRRL)
    * BoundsCalc_exact       : Bool             (Exactness verification flag for CSetBoundsExact)

  [Input Mapping]
    * Group 18 (CSetBounds, CSetBoundsExact, CSetBoundsImm, CRAM, CRRL): Base address
      and requested length (rs2, simm12, or rs1) route via separate input MUXes
      alongside the isRoundDown boolean flag.

  [Output Mapping]
    * Group 18 (CSetBounds, CSetBoundsExact, CSetBoundsImm): Writeback stage routes
      BoundsCalc_outE, BoundsCalc_outBase, and BoundsCalc_outTop to construct destination capability.
    * Group 18 (CRAM): Writeback stage routes BoundsCalc_cram -> integer register rd.
    * Group 18 (CRRL): Writeback stage routes BoundsCalc_outLen -> integer register rd.

-------------------------------------------------------------------------------
EXECUTE UNIT 10: CAndPerm (Dedicated Local Bitwise Permission Masking Unit)
-------------------------------------------------------------------------------
Purpose: Dedicated local hardware handling bitwise capability permission masking (`CAndPerm`).

  [Inputs]
    * CAndPerm_cap : FullECapWithTag (Target capability operand `cs1`)
    * CAndPerm_rs2 : Data            (Raw mask register operand `rs2`)

  [Outputs]
    * CAndPerm_res : FullECapWithTag (Legalized capability result with updated tag and permissions)

  [Input Mapping]
    * Group 15 (CAndPerm): Source capability cs1 and raw mask register rs2 route directly.

  [Output Mapping]
    * Group 15 (CAndPerm): Legalized capability record res writes to destination capability register cd.ecap
                           and cd.tag.

-------------------------------------------------------------------------------
EXECUTE UNIT 11: SealerUnsealer (Dedicated Capability Sealing & Unsealing Unit)
-------------------------------------------------------------------------------
Purpose: Dedicated local hardware authorizing and applying capability sealing (`CSeal`) and unsealing (`CUnseal`).

  [Inputs]
    * SealerUnsealer_isUnseal    : Bool            (Sealing polarity: False = Seal, True = Unseal)
    * SealerUnsealer_boundsValid : Bool            (True if candidate address is within `cs2` bounds)
    * SealerUnsealer_src1        : FullECapWithTag (Target capability operand `cs1`)
    * SealerUnsealer_src2        : FullECapWithTag (Authorizing capability operand `cs2`)

  [Outputs]
    * SealerUnsealer_res         : FullECapWithTag (Authorized capability result with updated tag and object type)

  [Input Mapping]
    * Group 17 (CSeal, CUnseal): Target capability cs1 and authorizing capability cs2 route directly
                                 into internal bounds verification and otype tagging logic.

  [Output Mapping]
    * Group 17 (CSeal, CUnseal): Authorized capability record res writes to destination capability register cd.ecap
                                 and cd.tag.

-------------------------------------------------------------------------------
EXECUTE UNIT 12: ScrSanitizer (Dedicated Special Capability Register Sanitization Unit)
-------------------------------------------------------------------------------
Purpose: Dedicated local hardware sanitizing capability writes into special capability registers
         (to be used for `MEPCC` and `MTCC`).

  [Inputs]
    * ScrSanitizer_inpCap : FullECapWithTag (Candidate capability operand `cs1` to commit into SCR)

  [Outputs]
    * ScrSanitizer_outCap : FullECapWithTag (tag cleared if not a good MEPCC/MTCC capability).

  [Input Mapping]
    * Group 21 (CSpecialRw): Source capability cs1 routes directly.

  [Output Mapping]
    * Group 21 (CSpecialRw): Sanitized capability record outCap commits to destination SCR register file.

-------------------------------------------------------------------------------
EXECUTE UNIT 13: BranchJalPccTag (Dedicated Next PCC Tag & Representability Verification Unit)
-------------------------------------------------------------------------------
Purpose: Verifies target PC representability for branches (`BEQ`, `BLT`, etc.) and jumps (`CJAL`, `CJALR`),
         validating capability tag, execution permissions, and sentry object-type constraints before committing.

  [Inputs]
    * BranchJalPccTag_isBranch    : Bool            (Asserted for conditional branch instructions)
    * BranchJalPccTag_isCjal      : Bool            (Asserted for direct jump CJAL instructions)
    * BranchJalPccTag_isCjalr     : Bool            (Asserted for indirect jump CJALR instructions)
    * BranchJalPccTag_branchTaken : Bool            (Branch condition evaluation result from Comparator)
    * BranchJalPccTag_topValid    : Bool            (Output from TopBoundsCheck evaluating target PC <= top)
    * BranchJalPccTag_baseValid   : Bool            (Output from BaseBoundsCheck evaluating target PC >= base)
    * BranchJalPccTag_cs1         : FullECapWithTag (Candidate target capability operand cs1 for CJALR)

  [Outputs]
    * BranchJalPccTag_nextTag     : Bool            (Computed valid tag for next instruction PC capability)

  [Input Mapping]
    * Group 6 (Branches), Group 7 (CJAL, CJALR): Appropriate opcode decode flags assert isBranch/isCjal/isCjalr;
      TopBoundsCheck and BaseBoundsCheck evaluate jump target PC address against PCC or cs1 bounds.

  [Output Mapping]
    * Group 6 (Branches), Group 7 (CJAL, CJALR): nextTag drives the pcc_tag commit routing multiplexer.

-------------------------------------------------------------------------------
EXECUTE UNIT 14: CjalrPcc (Dedicated CJALR Target Metadata & Legality Verification Unit)
-------------------------------------------------------------------------------
Purpose: Dedicated architectural evaluation unit for `CJALR` jump target capability metadata (`PCC.ecap`),
         return link capability (`rd.ecap`), tag validity (`PCC.tag`), and interrupt status (`MIE`),
         enforcing CHERIoT Sail sentry unsealing and return sealing rules.

  [Inputs]
    * CjalrPcc_pccECap             : ECap            (Current authorizing Program Counter Capability metadata)
    * CjalrPcc_cs1                 : FullECapWithTag (Authorizing jump target capability operand $cs1$)
    * CjalrPcc_inst                : Inst            (Raw 32-bit instruction word encoding $cd$, $cs1$, and $simm12$)
    * CjalrPcc_currInterruptStatus : Bool            (Current architectural interrupt enable status `MIE`)

  [Outputs]
    * CjalrPcc_nextPccTag          : Bool (Legalized target PCC tag validity flag)
    * CjalrPcc_nextPccECap         : ECap (Unsealed target PCC capability metadata struct)
    * CjalrPcc_linkECap            : ECap (Return link capability metadata potentially sealed as backward sentry)
    * CjalrPcc_interruptStatus     : Bool (Updated architectural interrupt enable status `MIE`)
    * CjalrPcc_isChangingInterrupt : Bool (Asserted when unsealing an ie/id sentry updates MIE and nextPccTag is valid)

  [Input Mapping]
    * Group 7 (CJALR): Current pccECap drives pccECap; authorizing capability cs1 drives cs1;
      raw instruction word drives inst; interruptStatus drives currInterruptStatus. (Not connected yet).

  [Output Mapping]
    * Group 7 (CJALR): Struct outputs CjalrPcc_nextPccTag, CjalrPcc_nextPccECap, CjalrPcc_linkECap,
      CjalrPcc_interruptStatus, and CjalrPcc_isChangingInterrupt (Not connected yet).

-------------------------------------------------------------------------------
EXECUTE UNIT 15: MultiOp (Dedicated Multicycle Memory & System Operation Unit)
-------------------------------------------------------------------------------
Purpose: Dedicated local hardware managing multicycle loads, stores, and system operations.

  [Inputs]
    * MultiOp_kind    : Option Bool (None = None, Some False = Load, Some True = Store)
    * MultiOp_memOpSz : Bit 2       (Encoding Lg(NumBytesXlen): 0=1B, 1=2B, 2=4B, 3=8B)

  [Outputs]
    * MultiOp_res     : Data        (Memory or system interaction control bundle)

===============================================================================
3. RV32I & CHERIoT INSTRUCTION ROUTING MAP (EXHAUSTIVE & STRICTLY EXECUTE-UNIT-ISOLATED)
===============================================================================

-------------------------------------------------------------------------------
GROUP 1: DIRECT IMMEDIATE BUS ROUTING (EXECUTE UNIT: DIRECT IMMEDIATE BUS)
-------------------------------------------------------------------------------
* LUI rd, uimm20
    Input Preproc: 20-bit immediate shifted left 12 bits -> decoded immediate.
    Output Route : resVal = decoded immediate -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 2: UPPER IMMEDIATE CAPABILITY DERIVATION (EXECUTE UNIT: MainAdder + TopBoundsCheck + BaseBoundsCheck)
-------------------------------------------------------------------------------
* AUICGP cd, uimm20_11
    Implicit Read: c3 / CGP (ABI General Purpose Capability Register 3).
* AUIPCC cd, uimm20_11
    Implicit Read: PCC (Program Counter Capability).
    Input Preproc:
      - MainAdder       : Route base address (CGP.addr or PCC.addr) to src1; route decoded immediate
                          to src2. Note: Both AUICGP and AUIPCC shift immediate left 11 bits (imm << 11).
      - TopBoundsCheck  : inpAddr = MainAdder_sum; limit = authCap.top_rep (base + 2^(E + 9)); isInclusive = False.
      - BaseBoundsCheck : inpAddr = MainAdder_sum; base = authCap.base.
    Output Route :
      - cd.ecap = authCap.ecap (preserve source expanded capability struct).
      - cd.addr = MainAdder_res.
      - cd.tag  = authCap.tag & TopBoundsCheck_topValid & BaseBoundsCheck_baseValid.

-------------------------------------------------------------------------------
GROUP 4: MAIN ALU ADDER ARITHMETIC (EXECUTE UNIT: MainAdder)
-------------------------------------------------------------------------------
* ADD rd, rs1, rs2
    Input Preproc: MainAdder_src1 = SignExt(rs1); MainAdder_src2 = SignExt(rs2).
                   MainAdder_subEnable = False.
    Output Route : resVal = MainAdder_res -> Register File rd; rd.tag = False.

* SUB rd, rs1, rs2
    Input Preproc: MainAdder_src1 = SignExt(rs1); MainAdder_src2 = SignExt(rs2).
                   MainAdder_subEnable = True.
    Output Route : resVal = MainAdder_res -> Register File rd; rd.tag = False.

* ADDI rd, rs1, simm12
    Input Preproc: MainAdder_src1 = SignExt(rs1); MainAdder_src2 = SignExt(decoded immediate).
                   MainAdder_subEnable = False.
    Output Route : resVal = MainAdder_res -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 5: INTEGER SET LESS THAN COMPARISONS (EXECUTE UNIT: Comparator)
-------------------------------------------------------------------------------
* SLT rd, rs1, rs2
* SLTU rd, rs1, rs2
* SLTI rd, rs1, simm12
* SLTIU rd, rs1, simm12
    Input Preproc: Route rs1 to src1; route rs2 / sign-extended immediate to src2.
                   Assert isUnsigned = funct3[0] (False for SLT/SLTI; True for SLTU/SLTIU).
                   Assert invert = False; checkLtGe = True.
    Output Route : resVal = ZeroExtend(32, Comparator_resVal) -> rd; force rd.tag = False.

-------------------------------------------------------------------------------
GROUP 6: BRANCH CONDITION EVALUATION (EXECUTE UNIT: Comparator + PcAdder + MemAdder + Bounds Comparators + BranchJalPccTag)
-------------------------------------------------------------------------------
* BEQ rs1, rs2, bimm12
* BNE rs1, rs2, bimm12
* BLT rs1, rs2, bimm12
* BGE rs1, rs2, bimm12
* BLTU rs1, rs2, bimm12
* BGEU rs1, rs2, bimm12
    Implicit Read : PCC.addr (strictly the 32-bit address field to compute target PCC.addr + bimm12).
    Implicit Write: PCC.addr, PCC.tag (cleared if target PC violates representability bounds on taken branch).
    Input Preproc:
      - Comparator    : src1 = rs1; src2 = rs2.
                        Assert isUnsigned = funct3[1]; invert = funct3[0]; checkLtGe = funct3[2].
      - PcAdder       : src1 = SignExt(PC); src2 = SignExt(branch offset: imm[12:1] ## 1'b0).
      - MemAdder      : src1 = SignExt(PC); src2 = SignExt(isCompressed ? 2 : 4).
    Output Route :
      - take = Comparator_resVal
      - nextPC = take ? PcAdder_res (LSB hardwired to 0) : MemAdder_res. (No write to register file).

-------------------------------------------------------------------------------
GROUP 7: CONTROL FLOW JUMP TARGET CALCULATION (EXECUTE UNIT: PcAdder + MemAdder + Bounds Comparators + BranchJalPccTag)
-------------------------------------------------------------------------------
* CJAL cd, jimm20
    Implicit Read : PCC (entire Program Counter Capability record to construct return sentry PCC + 2 and jump target).
    Implicit Write: PCC.addr, PCC.tag (cleared if target PC violates representability bounds).
    Input Preproc:
      - PcAdder  : PcAdder_src1 = SignExt(PC); PcAdder_src2 = SignExt(jal offset: imm[20:1] ## 1'b0).
      - MemAdder : MemAdder_src1 = SignExt(PC); MemAdder_src2 = SignExt(isCompressed ? 2 : 4).
    Output Route : nextPC = PcAdder_res (LSB hardwired to 0); resVal = MemAdder_res -> cd.addr
                   (unsealed sentry link).

* CJALR cd, cs1, simm12
    Implicit Read : PCC (entire Program Counter Capability record to construct return sentry PCC + 2).
    Implicit Write: PCC (full capability jump record replacement PCC <- cs1 + simm12).
                    PCC.tag is cleared if cs1 lacks Execute permission or if sealing constraints are not met
                    (e.g. sealed but not a valid Sentry). CJALR itself does not throw exceptions.
                    (Note: Clearing the tag here instead of throwing an exception diverges from the official CHERIoT spec).
    Input Preproc:
      - PcAdder  : PcAdder_src1 = cs1.addr; PcAdder_src2 = SignExt(decoded immediate: imm[11:0], unshifted).
      - MemAdder : MemAdder_src1 = SignExt(PC); MemAdder_src2 = SignExt(isCompressed ? 2 : 4).
    Output Route : nextPC = PcAdder_res (LSB hardwired to 0);
                   resVal = MemAdder_res -> cd.addr (unsealed sentry link).

-------------------------------------------------------------------------------
GROUP 8: MEMORY EFFECTIVE ADDRESS CALCULATION (EXECUTE UNIT: MemAdder)
-------------------------------------------------------------------------------
* LB rd, imm12(cs1)
* LH rd, imm12(cs1)
* LW rd, imm12(cs1)
* LBU rd, imm12(cs1)
* LHU rd, imm12(cs1)
    Fault Triggers: CapEx_TagViolation, CapEx_SealViolation, CapEx_PermitLoadViolation,
                    CapEx_BoundsViolation, Load Access Fault, Load Address Misaligned (LH/LW/LHU).
* LC cd, imm12(cs1)
    Fault Triggers: CapEx_TagViolation, CapEx_SealViolation, CapEx_PermitLoadViolation,
                    CapEx_BoundsViolation, Load Access Fault, Load Address Misaligned.
* SB rs2, imm12(cs1)
* SH rs2, imm12(cs1)
* SW rs2, imm12(cs1)
    Fault Triggers: CapEx_TagViolation, CapEx_SealViolation, CapEx_PermitStoreViolation,
                    CapEx_BoundsViolation, Store Access Fault, Store Address Misaligned (SH/SW).
* SC cs2, imm12(cs1)
    Fault Triggers: CapEx_TagViolation, CapEx_SealViolation, CapEx_PermitStoreViolation,
                    CapEx_PermitStoreCapViolation, CapEx_BoundsViolation, Store Access Fault,
                    Store Address Misaligned.
    Input Preproc: MemAdder_src1 = cs1.addr; MemAdder_src2 = SignExt(decoded immediate).
    Output Route : memAddr = MemAdder_res -> Data Memory Pipeline Interface.

-------------------------------------------------------------------------------
GROUP 9: INTEGER BARREL SHIFTING (EXECUTE UNIT: Shifter)
-------------------------------------------------------------------------------
* SLL rd, rs1, rs2
* SRL rd, rs1, rs2
* SRA rd, rs1, rs2
* SLLI rd, rs1, shamt
* SRLI rd, rs1, shamt
* SRAI rd, rs1, shamt
    Input Preproc: Shifter_val = rs1; amt = rs2[4:0] / decoded shift immediate.
                   isRight = (Opcode == SRL/SRA); isArith = Funct7[5].
                   Note: For left shifts (SLL/SLLI), input val and output res are reversed.
    Output Route : resVal = Shifter_res -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 10: INTEGER BITWISE BOOLEAN LOGIC (EXECUTE UNIT: LogicUnit)
-------------------------------------------------------------------------------
* AND rd, rs1, rs2
* OR rd, rs1, rs2
* XOR rd, rs1, rs2
* ANDI rd, rs1, simm12
* ORI rd, rs1, simm12
* XORI rd, rs1, simm12
    Input Preproc: LogicUnit_src1 = rs1; LogicUnit_src2 = rs2 / decoded immediate.
                   LogicUnit_opSel = DecodedFunct3.
    Output Route : resVal = LogicUnit_res -> Register File rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 11: DIRECT CAPABILITY FIELD EXTRACTION (EXECUTE UNIT: DIRECT BUS)
-------------------------------------------------------------------------------
* CGetPerm rd, cs1
* CGetType rd, cs1
* CGetBase rd, cs1
* CGetTag rd, cs1
* CGetAddr rd, cs1
* CGetHigh rd, cs1
* CGetTop rd, cs1
    Input Preproc: Read raw pre-expanded integer fields directly from cs1.
    Output Route : ZeroExtend extracted field to 32 bits -> rd; force rd.tag = False.

-------------------------------------------------------------------------------
GROUP 12: CAPABILITY LENGTH CALCULATION (EXECUTE UNIT: MainAdder)
-------------------------------------------------------------------------------
* CGetLen rd, cs1
    Input Preproc: MainAdder_src1 = cs1.top; MainAdder_src2 = cs1.base.
                   MainAdder_subEnable = True (Compute Top - Base).
    Output Route : resVal = MainAdder_res -> rd; force rd.tag = False.

-------------------------------------------------------------------------------
GROUP 13: CAPABILITY POINTER ARITHMETIC & REPRESENTABILITY (EXECUTE UNIT: MainAdder + TopBoundsCheck + BaseBoundsCheck)
-------------------------------------------------------------------------------
* CIncAddr cd, cs1, rs2
* CIncAddrImm cd, cs1, simm12
    Input Preproc:
      - MainAdder       : MainAdder_src1 = SignExt(cs1.addr); MainAdder_src2 = SignExt(rs2 / 12-bit immediate).
      - TopBoundsCheck  : inpAddr = MainAdder_sum; limit = cs1.top_rep (cs1.base + 2^(cs1.E + 9));
                          isInclusive = False.
      - BaseBoundsCheck : inpAddr = MainAdder_sum; base = cs1.base.
    Output Route :
      - cd.ecap = cs1.ecap (preserve source expanded capability struct).
      - cd.addr = MainAdder_res.
      - cd.tag  = cs1.tag & TopBoundsCheck_topValid & BaseBoundsCheck_baseValid.

-------------------------------------------------------------------------------
GROUP 14: CAPABILITY DIRECT ADDRESS SUBSTITUTION (EXECUTE UNIT: DIRECT BUS + TopBoundsCheck + BaseBoundsCheck)
-------------------------------------------------------------------------------
* CSetAddr cd, cs1, rs2
* CSetHigh cd, cs1, rs2
    Input Preproc:
      - DirectBus       : Route rs2 directly to cd.addr.
      - TopBoundsCheck  : inpAddr = SignExt(rs2); limit = cs1.top_rep (cs1.base + 2^(cs1.E + 9)); isInclusive = False.
      - BaseBoundsCheck : inpAddr = SignExt(rs2); base = cs1.base.
    Output Route :
      - cd.ecap = cs1.ecap (preserve source expanded capability struct).
      - cd.addr = rs2.
      - cd.tag  = cs1.tag & TopBoundsCheck_topValid & BaseBoundsCheck_baseValid.

-------------------------------------------------------------------------------
GROUP 15: CAPABILITY BITWISE PERMISSION MASKING (EXECUTE UNIT: CAndPerm)
-------------------------------------------------------------------------------
* CAndPerm cd, cs1, rs2
    Input Preproc: Route target capability cs1 and raw register rs2 into CAndPerm.
    Output Route :
      - cd.ecap = CAndPerm_res.ecap.
      - cd.addr = cs1.addr.
      - cd.tag  = CAndPerm_res.tag.

-------------------------------------------------------------------------------
GROUP 16: CAPABILITY TAG CLEARING (EXECUTE UNIT: DIRECT BUS)
-------------------------------------------------------------------------------
* CClearTag cd, cs1
    Input Preproc: Direct Bus
    Output Route :
      - cd.ecap = cs1.ecap (copy source capdata struct).
      - cd.addr = cs1.addr.
      - cd.tag  = False (explicitly force tag to 0).

-------------------------------------------------------------------------------
GROUP 17: CAPABILITY SEALING & UNSEALING (EXECUTE UNIT: TopBoundsCheck + BaseBoundsCheck + SealerUnsealer)
-------------------------------------------------------------------------------
* CSeal cd, cs1, cs2
* CUnseal cd, cs1, cs2
    Input Preproc:
      - TopBoundsCheck  : inpAddr = cs2.addr (CSeal) or cs1.otype (CUnseal); limit = cs2.top; isInclusive = False.
      - BaseBoundsCheck : inpAddr = cs2.addr (CSeal) or cs1.otype (CUnseal); base = cs2.base.
      - SealerUnsealer  : Route isUnseal flag, boundsValid (topValid & baseValid), cs1, and cs2.
    Output Route :
      - cd.ecap = SealerUnsealer_res.ecap.
      - cd.addr = cs1.addr.
      - cd.tag  = SealerUnsealer_res.tag.

-------------------------------------------------------------------------------
GROUP 18: CAPABILITY BOUNDS COMPRESSION RECOMPUTATION (EXECUTE UNIT: BoundsCalc)
-------------------------------------------------------------------------------
* CSetBounds cd, cs1, rs2
* CSetBoundsExact cd, cs1, rs2
* CSetBoundsRoundDown cd, cs1, rs2
* CSetBoundsImm cd, cs1, simm12
    Input Preproc: Route source capability cs1 and length rs2 / decoded immediate.
    Output Route :
      - cd.ecap = BoundsCalc_newCap (recomputed expanded capability struct).
      - cd.addr = cs1.addr.
      - cd.tag  = cs1.tag & ~cs1.isSeal & isValidBounds & (isExact | ~isCSetBoundsExact).

* CRAM rd, rs1
    Input Preproc: Route source capability rs1 and requested length.
    Output Route : resVal = BoundsCalc_resMask -> integer register rd; rd.tag = False.

* CRRL rd, rs1
    Input Preproc: Route source capability rs1 and requested length.
    Output Route : resVal = BoundsCalc_resLen -> integer register rd; rd.tag = False.

-------------------------------------------------------------------------------
GROUP 19: CAPABILITY DIFFS & COMPARISONS (EXECUTE UNIT: MainAdder + Comparator + Bounds Comparators)
-------------------------------------------------------------------------------
* CSub rd, cs1, cs2
    Input Preproc: MainAdder_src1 = cs1.addr; MainAdder_src2 = cs2.addr.
                   MainAdder_subEnable = True.
    Output Route : resVal = MainAdder_res -> integer register rd.

* CSetEqual rd, cs1, cs2
    Input Preproc: Route cs1.addr and cs2.addr to Comparator.
                   Assert checkLtGe = False; invert = False; isUnsigned = True.
    Output Route : resVal = ZeroExtend(32, Comparator_resVal & (cs1.cap == cs2.cap)) -> rd.

* CTestSubset rd, cs1, cs2
    Input Preproc:
      - TopBoundsCheck  : inpAddr = cs2.top; limit = cs1.top; isInclusive = True (Check cs2.top <= cs1.top).
      - BaseBoundsCheck : inpAddr = cs2.base; base = cs1.base (Check cs2.base >= cs1.base).
      - PermSubset      : Check (cs1.perms & cs2.perms) == cs2.perms.
    Output Route : resVal = ZeroExtend(32, (cs1.tag == cs2.tag) & topValid & baseValid & permValid) -> rd.

-------------------------------------------------------------------------------
GROUP 20: DIRECT CAPABILITY REGISTER COPY (EXECUTE UNIT: DIRECT BUS)
-------------------------------------------------------------------------------
* CMove cd, cs1
    Input Preproc: Direct Bus
    Output Route : cd = cs1 (Direct 1:1 expanded capability record move).

-------------------------------------------------------------------------------
GROUP 21: SYSTEM CSRs & SPECIAL CAPABILITY MOVES (EXECUTE UNIT: DIRECT BUS)
-------------------------------------------------------------------------------
* CSRRW rd, csr, rs1
* CSRRS rd, csr, rs1
* CSRRC rd, csr, rs1
* CSRRWI rd, csr, zimm5
* CSRRSI rd, csr, zimm5
* CSRRCI rd, csr, zimm5
* CSpecialRw cd, cSpecial, cs1
    Decode-Stage Fault Trigger: System Register Violation (SrViolation) if !PCC.perms.AccessSystemRegisters
                                (trapped combinationally prior to Execute dispatch).
    Input Preproc: Route CSR / SCR via Direct Bus. Route cs1 -> ScrSanitizer_inpCap.
    Output Route :
      - Old CSR / SCR -> rd / cd.
      - New SCR committed from ScrSanitizer_outCap (tag cleared if not a good MEPCC/MTCC capability).
      - Exception gating takes strict priority over state commits.

-------------------------------------------------------------------------------
GROUP 22: EXPLICIT SYNCHRONOUS SYSTEM TRAPS (EXECUTE UNIT: TRAP CONTROL)
-------------------------------------------------------------------------------
* ECALL
* EBREAK
    Fault Triggers: Environment Call Exception (mcause = 11), Breakpoint Exception (mcause = 3).
    Input Preproc: Route MTCC via Trap Control network.
    Output Route : MEPCC = PCC; PCC = MTCC; mcause = trap_cause.

-------------------------------------------------------------------------------
GROUP 23: PRIVILEGED EXCEPTION RETURN (EXECUTE UNIT: EXCEPTION RETURN)
-------------------------------------------------------------------------------
* MRET
    Implicit Read : MEPCC (exception return root).
    Implicit Write: PCC (PCC <- MEPCC).
    Decode-Stage Fault Trigger: System Register Violation (SrViolation) if !PCC.perms.AccessSystemRegisters
                                (trapped combinationally prior to Execute dispatch).
    Input Preproc: Route MEPCC via Trap Control network.
    Output Route : PCC = MEPCC.

===============================================================================
4. UNIVERSAL HARDWARE TRAP & EXCEPTION SUMMARY (RISC-V & CHERI FAULTS)
===============================================================================

*** ARCHITECTURAL DIVERGENCE: mePrevPcc ***
This architecture diverges from the official CHERIoT SAIL specification by introducing a new
CSR: `mePrevPcc`. This register stores the `PCC` of every committed instruction. By doing this,
control flow instructions (like CJALR) no longer need to synchronously fault on invalid targets.
Instead, they can write an untagged/invalid capability to `PCC`. The fault is postponed to the 
subsequent Instruction Fetch (IF) stage. The OS trap handler can then read `mePrevPcc` to 
perfectly attribute the fault back to the exact instruction that performed the invalid jump.

Whenever normal instruction execution aborts due to a synchronous hardware fault
(Tag, Seal, Bounds, Permission, Alignment violation) OR an explicit trap (ECALL, EBREAK):
  * Universal Trap Read : Hardware reads MTCC (Machine Trap Vector Root).
  * Universal Trap Write: PCC <- MTCC; MEPCC <- faulting PCC; mcause <- trap cause;
                          mstatus (interrupt status commit); mtval <- fault info.
                          (Note: mePrevPcc is implicitly preserved upon trap to indicate the source of the jump
                           if this was a fetch fault).

1. Standard RISC-V Exceptions (mcause records identifier, mtval records PC / addr):
  * mcause = 1 : Instruction Access Fault      -> Fetch (IF)
  * mcause = 2 : Illegal Instruction           -> Decode (ID)
  * mcause = 3 : Breakpoint (EBREAK)           -> Execute (EX)
  * mcause = 4 : Load Address Misaligned       -> Execute (EX)
  * mcause = 5 : Load Access Fault             -> Execute (EX)
  * mcause = 6 : Store Address Misaligned      -> Execute (EX)
  * mcause = 7 : Store Access Fault            -> Execute (EX)
  * mcause = 11: Environment Call (ECALL)      -> Execute (EX)

2. CHERI-Only Exceptions (mcause = 28 / 0x1C; mtval = {cap_idx[15:5], cheri_cause[4:0]}):
  * cheri_cause = 1 : CapEx_BoundsViolation             -> Fetch (IF) / Execute (EX)
  * cheri_cause = 2 : CapEx_TagViolation                -> Fetch (IF) / Execute (EX)
  * cheri_cause = 3 : CapEx_SealViolation               -> Fetch (IF) / Execute (EX)
  * cheri_cause = 17: CapEx_PermitExecuteViolation      -> Fetch (IF) / Execute (EX)
  * cheri_cause = 18: CapEx_PermitLoadViolation         -> Execute (EX)
  * cheri_cause = 19: CapEx_PermitStoreViolation        -> Execute (EX)
  * cheri_cause = 21: CapEx_PermitStoreCapViolation     -> Execute (EX)
  * cheri_cause = 24: CapEx_AccessSystemRegsViolation   -> Decode (ID)

===============================================================================
5. DECODER CONTROL BUNDLE FIELD SPECIFICATIONS
===============================================================================
To bridge the gap between opcode decoding and physical datapath execution, the
Decoder emits these explicit multiplexer select and enablement bundles:

1. Ctrl_MainAdder
   * sel_src1    : { Rs1, Cs1Addr, Cs1Top, CgpAddr, PccAddr, Zero }
   * sel_src2    : { Rs2, simm12, uimm20_11, Cs1Base, Cs2Addr }
   * subEnable   : { True = Subtract, False = Add }

2. Ctrl_PcAdder
   * sel_src1    : { PC, Rs1Addr }
   * sel_src2    : { bimm12, jimm20, simm12 }

3. Ctrl_MemAdder
   * sel_src1    : { PC, Rs1Addr }
   * sel_src2    : { Constant2, Constant4, simm12 }

4. Ctrl_Shifter
   * sel_val     : { Rs1 }
   * sel_amt     : { Rs2Low, shamt }
   * isRight     : { True = Shift Right, False = Shift Left }
   * isArith     : { True = Arithmetic, False = Logical }

5. Ctrl_Logic
   * sel_src1    : { Rs1 }
   * sel_src2    : { Rs2, simm12 }
   * opSel       : { 00 = AND, 01 = OR, 10 = XOR }

6. Ctrl_Comparator
   * sel_src1    : { Rs1, Cs1Addr }
   * sel_src2    : { Rs2, simm12, Cs2Addr }
   * isSigned    : { True = Signed, False = Unsigned }

7. Ctrl_TopCheck
   * sel_inpAddr : { MainAdder_sum, SignExtRs2, Cs1Addr, Cs1Otype, Cs2Addr, Cs2Top, PcAdder }
   * sel_limit   : { TopRep, Cs2Top, Cs1Top, PccTop }
   * isInclusive : { True = Less Or Equal, False = Strict Less Than }

8. Ctrl_BaseCheck
   * sel_inpAddr : { MainAdder_sum, SignExtRs2, Cs1Addr, Cs1Otype, Cs2Addr, Cs2Base, PcAdder }
   * sel_base    : { AuthBase, Cs1Base, PccBase }

9. Ctrl_BoundsCalc
   * sel_base    : { Cs1Addr, Zero }
   * sel_length  : { Rs2, simm12, Rs1 }
   * isRoundDown : { True = Round Down, False = Round Up / Exact }

10. Ctrl_CAndPerm
    * enable     : { True = Enable CAndPerm, False = Disable }

11. Ctrl_SealerUnsealer
    * isUnseal   : { True = CUnseal mode, False = CSeal mode }

12. Ctrl_ScrSanitizer
    * enable     : { True = Enable ScrSanitizer, False = Disable }

13. Ctrl_BranchJalPccTag
    * isBranch   : { True = Branch Mode, False = Disable }
    * isCjal     : { True = CJAL Mode, False = Disable }
    * isCjalr    : { True = CJALR Mode, False = Disable }

14. Ctrl_MultiOp
    * multiOp    : Option Bool (* None = No MultiOp, Some True = Store, Some False = Load *)
    * memOpSz    : { Byte, Half, Word, Cap } (* Encoding is Lg(NumBytesXlen): 0=1B, 1=2B, 2=4B, 3=8B *)

===============================================================================
6. WRITEBACK CONTROL SPECIFICATIONS
===============================================================================
Centralized One-Hot Commit Routing Architecture:
  The ID Decoder evaluates instruction opcodes and combinationally emits explicit
  one-hot boolean control lines. Whenever an execution or system execute unit commits
  multiple components of a capability record (`FullECapWithTag`), the exact same
  control signal drives the corresponding datapath MUXes across `addr`, `ecap`, and `tag`.

-------------------------------------------------------------------------------
1. GENERAL PURPOSE & CAPABILITY REGISTER FILE (regs[rd] / regs[cd])
-------------------------------------------------------------------------------
  * Register Enablement:
      reg_writeEnable : Bool

  * reg_addr MUX Selects (32-bit Integer Address):
      reg_addr_MainAdder          (* ADD, SUB, AUICGP, CIncAddr, CGetLen, etc. *)
      reg_addr_PcAdder            (* CJAL, CJALR -> return sentry link address PC+2/PC+4 *)
      reg_addr_Shifter            (* SLL, SRL, SRA *)
      reg_addr_Logic              (* AND, OR, XOR *)
      reg_addr_Comparator         (* SLT, SLTU *)
      reg_addr_uimm20             (* LUI -> uimm20 << 12 *)
      reg_addr_rs2                (* CSetAddr *)
      reg_addr_cs1Addr            (* CClearTag, CSetBounds* *)
      reg_DirectCs1               (* CMove -> cs1.addr *)
      reg_CAndPerm                (* CAndPerm -> CAndPerm_res.addr *)
      reg_Sealer                  (* CSeal, CUnseal -> SealerUnsealer_res.addr *)
      reg_addr_csrRead            (* CSRRS, CSRRC, CSRRW *)
      reg_ScrRead                 (* CSpecialRw -> scrReadData.addr *)
      reg_addr_capField           (* CGetPerm, CGetTag, etc. *)
      reg_addr_BoundsCalc_cram    (* CRAM *)
      reg_addr_BoundsCalc_length  (* CRRL *)

  * reg_ecap MUX Selects (Expanded Capability Metadata Struct):
      reg_ecap_null               (* Integer ops, LUI, CGet*, CRAM, CSR*, etc. -> null_ecap *)
      reg_ecap_cs1                (* AUICGP, CIncAddr, CSetAddr, CClearTag *)
      reg_ecap_Pcc                (* CJAL, CJALR -> return sentry capability metadata *)
      reg_DirectCs1               (* CMove -> cs1.ecap *)
      reg_CAndPerm                (* CAndPerm -> CAndPerm_res.ecap *)
      reg_Sealer                  (* CSeal, CUnseal -> SealerUnsealer_res.ecap *)
      reg_ecap_BoundsCalc         (* CSetBounds* -> BoundsCalc_newCap *)
      reg_ScrRead                 (* CSpecialRw -> scrReadData.ecap *)

  * reg_tag MUX Selects (1-bit Capability Tag):
      reg_tag_False               (* Integer ops, ADD, LUI, CClearTag, CGet*, etc. -> False *)
      reg_tag_cs1BoundsValid      (* AUICGP, CIncAddr, CSetAddr -> cs1.tag & boundsCheck *)
      reg_tag_Pcc                 (* CJAL, CJALR -> return sentry tag (gated by permitExecute) *)
      reg_DirectCs1               (* CMove -> cs1.tag *)
      reg_CAndPerm                (* CAndPerm -> CAndPerm_res.tag *)
      reg_Sealer                  (* CSeal, CUnseal -> SealerUnsealer_res.tag *)
      reg_tag_BoundsCalc          (* CSetBounds* -> validBounds *)
      reg_ScrRead                 (* CSpecialRw -> scrReadData.tag *)

-------------------------------------------------------------------------------
2. PROGRAM COUNTER CAPABILITY (PCC)
-------------------------------------------------------------------------------
  * pcc_addr MUX Selects (Program Counter Address):
      pcc_addr_SeqNext            (* Sequential PC+2 / PC+4 *)
      pcc_Branch                  (* Conditional branch target PCC.addr + bimm12 *)
      pcc_CjalTarget              (* CJAL target PCC.addr + jimm20 *)
      pcc_CjalrTarget             (* CJALR target cs1.addr + simm12 with LSB cleared *)
      pcc_Mepcc                   (* MRET -> restore from MEPCC.addr *)

  * pcc_ecap MUX Selects (Program Counter Metadata Struct):
      pcc_ecap_Current            (* Sequential ops, branches, and CJAL keep current PCC metadata *)
      pcc_CjalrTarget             (* CJALR -> unsealed cs1 metadata *)
      pcc_Mepcc                   (* MRET -> MEPCC.ecap *)

  * pcc_tag MUX Selects (Program Counter Capability Tag):
      pcc_tag_Current             (* Sequential ops keep current PCC.tag *)
      pcc_tag_BranchJalPccTag        (* Control flow ops (Branch, CJAL, CJALR) route BranchJalPccTag_nextTag *)
      pcc_Mepcc                   (* MRET -> MEPCC.tag *)

-------------------------------------------------------------------------------
3. SYSTEM & SPECIAL REGISTERS (specialRegs: CSRs, SCRs)
-------------------------------------------------------------------------------
  * Write Enablement:
      specialReg_writeEnableData : Bool   (* Asserted for both CSR updates and SCR updates *)
      specialReg_writeEnableCap  : Bool   (* Asserted for SCR updates (ecap/tag); hardwired False for CSRs *)

===============================================================================
7. QUANTITATIVE SILICON ECONOMICS & DESIGN RATIONALE
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
  
  Tapping MainAdder_sum directly into dedicated lookahead comparators allows bounds
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
  main CPU `Shifter`, we save ~200 gates of internal shifter but incur 111 
  gates of bus multiplexing, yielding a negligible net savings of +89 gates. 
  Crucially, exponent e is dynamically computed by `BoundsCalc`'s priority 
  encoder (`countLeadingZeros`). Offloading creates a severe physical floorplan 
  timing loop:
    RegRead -> BoundsCalc Priority Encoder -> CPU Shifter -> BoundsCalc Adder
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
Cost of Shared Execute Unit Routing:
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
  RV32I system CSR instructions (`CSRRW`, `CSRRS`, `CSRRC` and imm variants) and
  CHERIoT Special Capability Registers (`CSpecialRW`) introduce unique architectural
  control-state constraints decoupled from standard arithmetic computation:
    a) Exception Prioritization: Pipeline exception gating (e.g. invalid CSR index,
       privilege violation, unaligned capability load/store) takes strict priority
       over CSR read/write side effects. If an exception fires, pending CSR updates
       must be aborted at writeback.
    b) Capability Legalization & Tag Constraints: Writing to specific architectural
       SCRs enforces complex tag and legalization checks. For instance, writing to
       MTCC (Trap Code Capability) or MEPCC (Exception Program Counter Capability)
       enforces capability unsealing, executable permission verification, and bounds
       legalization before committing to state.
    c) Microarchitectural CSR / MEPCC Read Symmetry: For standard CSR bitwise
       instructions (`CSRRS`, `CSRRC`), the integer mask `rs1` routes to port
       `src1`, while target CSR read data routes onto `src2`. To maintain strict
       symmetry and avoid crossbar multiplexing onto `src1`, return operations
       (`MRET`) route `MEPCC` onto `src2`, allowing `out_pcc` to grab `src2` at
       writeback with zero extra hardware routing.

Analysis of ALU LogicUnit Sharing:
  Multiplexing csrCurr and operand csrIn onto Execute Unit 5 (`LogicUnit`) to perform
  bitwise CSRRS (OR) and CSRRC (AND-NOT) math saves ~32 gates of duplicate bitwise
  logic. However, it introduces wide 32-bit multiplexers onto the hot ALU execution
  inputs (`LogicUnit_src1` and `LogicUnit_src2`), degrading core integer Fmax.
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
       `nextPC = take ? PcAdder_res : MemAdder_res`. Chaining carry-propagate
       subtraction (~35 gate levels, ~300ps+) delays the resolution of `take`,
       forcing the PC multiplexer to switch dangerously close to clock setup time.

Silicon Verdict (Go Dedicated Relational Tree):
  To eliminate comparison MUX bloat and protect core Fmax, we allocate Execute Unit 6
  (`Comparator`) as a dedicated 32-bit parallel-prefix magnitude comparator.
  A lookahead comparison tree resolves in ~8 gate levels (~100ps), delivering the
  branch decision flag `take` ~200ps earlier than arithmetic subtraction. This guarantees
  ultra-fast PC multiplexer switching and preserves 100% pure adder isolation on `MainAdder`.

-------------------------------------------------------------------------------
PART F: METADATA SPECIALIZATION UNITS (BOUNDSCALC, CANDPERM)
-------------------------------------------------------------------------------
False Economy of Micro-Sharing:
  In execution datapath design, it can be tempting to search for sub-expression sharing
  opportunities across distinct specialized instructions (e.g., sharing the `isSealed`
  tag check across `CAndPerm` and `CSetBounds`).

Silicon Verdict (Go Dedicated Encapsulated Blocks):
  Given that simple 3-input OR checks represent negligible standard-cell area (<3 gates),
  attempting to multiplex and route shared intermediate flags across isolated computation blocks
  introduces routing congestion and wiring capacitance bloat. We allocate self-contained,
  dedicated hardware blocks (`BoundsCalc`, `CAndPerm`) for capability metadata operations.
  Any minor combinational redundancy is deliberately ignored at the RTL level, allowing backend
  synthesis tools (Synopsys DC) to perform local Boolean optimization cleanly.

-------------------------------------------------------------------------------
EXECUTIVE CORE SUMMARY
-------------------------------------------------------------------------------
By isolating general datapath arithmetic structures (`PcAdder` and `MemAdder`) while 
allocating dedicated parallel-prefix magnitude comparators (`Comparator`, 
`TopBoundsCheck`, and `BaseBoundsCheck`), the datapath achieves an optimal layout: 
protecting chip Fmax and eliminating interconnect timing hazards at a negligible area cost.

END OF ARCHITECTURAL EXECUTE UNIT MAP
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
  Definition Shifter (val : ty (Bit Xlen)) (amt : ty (Bit LgXlen)) (isRight isArith : ty Bool)
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

  Definition SealerUnsealer (isUnseal boundsValid : ty Bool) (src1 src2 : ty FullECapWithTag)
    : LetExpr ty FullECapWithTag :=
    LetE ecap1 : ECap <- ##src1`"ecap" ;
    LetE ecap2 : ECap <- ##src2`"ecap" ;
    LetE perms1 : CapPerms <- ##ecap1`"perms" ;
    LetE perms2 : CapPerms <- ##ecap2`"perms" ;
    LetE sealed1 : Bool <- isSealed ecap1 ;
    LetE sealed2 : Bool <- isSealed ecap2 ;
    LetE cs2Addr : Data <- ##src2`"addr" ;
    
    (* OType Legalization range check for CSeal *)
    LetE sealRange : Bool <- ITE (##perms1`"EX")
                               (And [ Sgt #cs2Addr $0; Sle #cs2Addr $7 ])
                               (And [ Sgt #cs2Addr $8; Sle #cs2Addr $15 ]) ;
                               
    LetE permit : Bool <- ITE #isUnseal
                            (And [ #sealed1; ##perms2`"US" ])
                            (And [ Not #sealed1; ##perms2`"SE"; #sealRange ]) ;
                            
    LetE outTag : Bool <- And [ ##src1`"tag"; ##src2`"tag"; #boundsValid; Not #sealed2; #permit ] ;
    LetE outOType : Bit CapOTypeSz <- ITE #isUnseal $0 (TruncLsb (AddrSz - CapOTypeSz) CapOTypeSz #cs2Addr) ;
    LetE outGL : Bool <- ITE #isUnseal (And [ ##perms1`"GL"; ##perms2`"GL" ]) (##perms1`"GL") ;
    LetE outPerms : CapPerms <- ##perms1 `{ "GL" <- #outGL } ;
    LetE outECap : ECap <- ##ecap1 `{ "oType" <- #outOType } `{ "perms" <- #outPerms } ;
    @RetE _ FullECapWithTag (STRUCT { "tag" ::= #outTag; "ecap" ::= #outECap; "addr" ::= ##src1`"addr" }).

  Definition ScrSanitizer (enable : ty Bool) (inpCap : ty FullECapWithTag)
    : LetExpr ty FullECapWithTag :=
    LetE ecap : ECap <- ##inpCap`"ecap" ;
    LetE perms : CapPerms <- ##ecap`"perms" ;
    LetE addr : Data <- ##inpCap`"addr" ;
    LetE isLsbSet : Bool <- FromBit Bool (TruncLsb (AddrSz - 1) 1 #addr) ;
    LetE sealed : Bool <- isSealed ecap ;
    LetE noExec : Bool <- Not (##perms`"EX") ;
    LetE invalid : Bool <- Or [ #isLsbSet; #sealed; #noExec ] ;
    LetE condClear : Bool <- And [#enable; #invalid];
    LetE outTag : Bool <- And [ ##inpCap`"tag"; Not #condClear ] ;
    @RetE _ FullECapWithTag (STRUCT { "tag" ::= #outTag; "ecap" ::= #ecap; "addr" ::= #addr }).

  (* TODO: return updated interrupt status; also needs to route current interrupt status *)
  Definition BranchJalPccTag (isBranch isCjal isCjalr branchTaken topValid baseValid : ty Bool)
                          (cs1 : ty FullECapWithTag) : LetExpr ty Bool :=
    LetE cs1Tag : Bool <- ##cs1`"tag" ;
    LetE cs1ECap : ECap <- ##cs1`"ecap" ;
    LetE cs1PermEx : Bool <- ##cs1ECap`"perms"`"EX" ;
    LetE notSealed : Bool <- Not (isSealed cs1ECap) ;
    LetE cs1OType <- ##cs1ECap`"oType" ;
    LetE sentry : Bool <- isSentry cs1OType ;
    LetE boundsValid : Bool <- And [#topValid; #baseValid] ;
    (* TODO: This is not correct according to CHERIoT Sail spec. In Sail execute(CJALR):
       1. If cs1 is sealed (isSealed), simm12 MUST be 0 (simm12 == 0).
       2. If cd == zreg & cs1 == ra (return): cs1 must be unsealed OR a backward sentry (isCapBackwardSentry).
       3. If cd == ra (call): cs1 must be unsealed OR a forward sentry (isCapForwardSentry).
       4. Else (tail/outlined call): cs1 must be unsealed OR a forward inherit sentry (isCapForwardInheritSentry). *)
    LetE cjalrLegal : Bool <- And [ #cs1Tag; #cs1PermEx; #boundsValid; Or [#notSealed; #sentry] ] ;
    RetE (Or [ And [ #isCjalr; #cjalrLegal ] ;
               And [ Or [ #isCjal; #isBranch ] ; #boundsValid ] ;
               And [ #isBranch; Not #branchTaken ] ]).

  Definition CjalrPccOut := STRUCT_TYPE { "nextPccTag"          :: Bool;
                                          "nextPccECap"         :: ECap;
                                          "linkECap"            :: ECap;
                                          "interruptStatus"     :: Bool;
                                          "isChangingInterrupt" :: Bool }.

  Definition CjalrPcc (pccECap : ty ECap) (cs1 : ty FullECapWithTag) (inst : ty Inst) (currInterruptStatus : ty Bool)
                      : LetExpr ty CjalrPccOut :=
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

    LetE cs1OType <- ##cs1ECap`"oType" ;

    (* This nonsense has to be fixed with a new CRet instruction please! *)
    LetE nextPccLegal : Bool <- caseDefault [ (#isReturn, isRetSentry cs1OType);
                                              (#isCall, Or [#notCs1Sealed; isCallSentry cs1OType]) ]
                                  (Or [#notCs1Sealed; Eq #cs1OType $CallSentryIh]);

    (* We unset the tag instead of raising an exception because we have mePrevPcc *)
    LetE nextPccTag : Bool <- And [#cs1Tag; #cs1PermEx; #nextPccLegal; Or [#notCs1Sealed; #immZero]] ;
    LetE nextPccECap : ECap <- #cs1ECap `{ "oType" <- $0 } ;

    LetE nextIntStatus : Bool <- Or [isSentryIe cs1OType; And [Not (isSentryId cs1OType); #currInterruptStatus]] ;

    LetE bwdSentryOType : Bit CapOTypeSz <- ITE #currInterruptStatus $RetSentryIe $RetSentryId ;
    LetE linkECap : ECap <- #pccECap `{ "oType" <- ITE0 #isCall #bwdSentryOType } ;

    LetE isChangingInterrupt : Bool <-
      And [ #nextPccTag ; Or [ isSentryIe cs1OType ; isSentryId cs1OType ] ] ;

    @RetE _ CjalrPccOut (STRUCT { "nextPccTag"          ::= #nextPccTag;
                                  "nextPccECap"         ::= #nextPccECap;
                                  "linkECap"            ::= #linkECap;
                                  "interruptStatus"     ::= #nextIntStatus;
                                  "isChangingInterrupt" ::= #isChangingInterrupt }).

End ExecutionUnits.

Definition AluControl := STRUCT_TYPE {
  (* 1. Ctrl_MainAdder *)
  "MainAdder_src1_Rs1" :: Bool ;
  "MainAdder_src1_Cs1Addr" :: Bool ;
  "MainAdder_src1_Cs1Top" :: Bool ;
  "MainAdder_src1_CgpAddr" :: Bool ;
  "MainAdder_src1_PccAddr" :: Bool ;
  "MainAdder_src1_Zero" :: Bool ;
  
  "MainAdder_src2_Rs2" :: Bool ;
  "MainAdder_src2_simm12" :: Bool ;
  "MainAdder_src2_uimm20_11" :: Bool ;
  "MainAdder_src2_Cs1Base" :: Bool ;
  "MainAdder_src2_Cs2Addr" :: Bool ;
  
  "MainAdder_subEnable" :: Bool ;

  (* 2. Ctrl_PcAdder *)
  "PcAdder_src1_PC_Rs1Addr" :: Bool ; (* True = PC, False = Rs1Addr *)
  
  "PcAdder_src2_bimm12" :: Bool ;
  "PcAdder_src2_jimm20" :: Bool ;
  "PcAdder_src2_simm12" :: Bool ;

  (* 3. Ctrl_MemAdder *)
  "MemAdder_src1_PC_Rs1Addr" :: Bool ; (* True = PC, False = Rs1Addr *)
  
  "MemAdder_src2_Constant2" :: Bool ;
  "MemAdder_src2_Constant4" :: Bool ;
  "MemAdder_src2_simm12" :: Bool ;

  (* 4. Ctrl_Shifter *)
  (* Shifter_val: always Rs1 *)
  
  "Shifter_amt_Rs2Low_shamt" :: Bool ; (* True = Rs2Low, False = shamt *)
  
  "Shifter_isRight" :: Bool ;
  "Shifter_isArith" :: Bool ;

  (* 5. Ctrl_Logic *)
  (* Logic_src1: always Rs1 *)
  
  "Logic_src2_Rs2_simm12" :: Bool ; (* True = Rs2, False = simm12 *)
  
  "Logic_opSel" :: Bit 2 ; (* 00 = AND, 01 = OR, 10 = XOR *)

  (* 6. Ctrl_Comparator *)
  "Comparator_src1_Rs1_Cs1Addr" :: Bool ; (* True = Rs1, False = Cs1Addr *)
  
  "Comparator_src2_Rs2" :: Bool ;
  "Comparator_src2_simm12" :: Bool ;
  "Comparator_src2_Cs2Addr" :: Bool ;
  
  "Comparator_isSigned" :: Bool ;

  (* 7. Ctrl_TopCheck *)
  "TopCheck_inpAddr_SumMainAdder" :: Bool ;
  "TopCheck_inpAddr_SignExtRs2" :: Bool ;
  "TopCheck_inpAddr_Cs1Addr" :: Bool ;
  "TopCheck_inpAddr_Cs1Otype" :: Bool ;
  "TopCheck_inpAddr_Cs2Addr" :: Bool ;
  "TopCheck_inpAddr_Cs2Top" :: Bool ;
  "TopCheck_inpAddr_PcAdder" :: Bool ;
  
  "TopCheck_limit_TopRep" :: Bool ;
  "TopCheck_limit_Cs2Top" :: Bool ;
  "TopCheck_limit_Cs1Top" :: Bool ;
  "TopCheck_limit_PccTop" :: Bool ;
  
  "TopCheck_isInclusive" :: Bool ;

  (* 8. Ctrl_BaseCheck *)
  "BaseCheck_inpAddr_SumMainAdder" :: Bool ;
  "BaseCheck_inpAddr_SignExtRs2" :: Bool ;
  "BaseCheck_inpAddr_Cs1Addr" :: Bool ;
  "BaseCheck_inpAddr_Cs1Otype" :: Bool ;
  "BaseCheck_inpAddr_Cs2Addr" :: Bool ;
  "BaseCheck_inpAddr_Cs2Base" :: Bool ;
  "BaseCheck_inpAddr_PcAdder" :: Bool ;
  
  "BaseCheck_base_AuthBase_Cs1Base" :: Bool ; (* True = AuthBase, False = Cs1Base *)
  "BaseCheck_base_PccBase" :: Bool ;

  (* 9. Ctrl_BoundsCalc *)
  "BoundsCalc_base_Cs1Addr_Zero" :: Bool ; (* True = Cs1Addr, False = Zero *)
  
  "BoundsCalc_length_Rs2" :: Bool ;
  "BoundsCalc_length_simm12" :: Bool ;
  "BoundsCalc_length_Rs1" :: Bool ;
  
  "BoundsCalc_isRoundDown" :: Bool ;

  (* 10. Ctrl_CAndPerm *)
  "CAndPerm_enable" :: Bool ;

  (* 11. Ctrl_SealerUnsealer *)
  "SealerUnsealer_isUnseal" :: Bool ;

  (* 12. Ctrl_ScrSanitizer *)
  "ScrSanitizer_enable" :: Bool ;

  (* 13. Ctrl_BranchJalPccTag *)
  "BranchJalPccTag_isBranch" :: Bool ;
  "BranchJalPccTag_isCjal" :: Bool ;
  "BranchJalPccTag_isCjalr" :: Bool ;

  (* 14. Ctrl_MultiOp *)
  "MultiOp_kind" :: Option Bool ; (* None = None, Some False = Load, Some True = Store *)
  "MultiOp_memOpSz" :: Bit (Z.log2_up NumBytesXlen) (* 0=Byte (1B), 1=Half (2B), 2=Word (4B), 3=Cap (8B) *)
}.

Definition WbControl := STRUCT_TYPE {
  (* 1. GENERAL PURPOSE & CAPABILITY REGISTER FILE (regs) *)
  "reg_writeEnable" :: Bool ;

  (* reg_addr MUX Selects *)
  "reg_addr_MainAdder" :: Bool ;
  "reg_addr_PcAdder" :: Bool ;
  "reg_addr_Shifter" :: Bool ;
  "reg_addr_Logic" :: Bool ;
  "reg_addr_Comparator" :: Bool ;
  "reg_addr_uimm20" :: Bool ;
  "reg_addr_rs2" :: Bool ;
  "reg_addr_cs1Addr" :: Bool ;
  "reg_DirectCs1" :: Bool ;
  "reg_CAndPerm" :: Bool ;
  "reg_Sealer" :: Bool ;
  "reg_addr_csrRead" :: Bool ;
  "reg_ScrRead" :: Bool ;
  "reg_addr_capField" :: Bool ;
  "reg_addr_BoundsCalc_cram" :: Bool ;
  "reg_addr_BoundsCalc_length" :: Bool ;

  (* reg_ecap MUX Selects *)
  "reg_ecap_null" :: Bool ;
  "reg_ecap_cs1" :: Bool ;
  "reg_ecap_Pcc" :: Bool ;
  (* reg_DirectCs1 *)
  (* reg_CAndPerm *)
  (* reg_Sealer *)
  "reg_ecap_BoundsCalc" :: Bool ;
  (* reg_ScrRead *)

  (* reg_tag MUX Selects *)
  "reg_tag_False" :: Bool ;
  "reg_tag_cs1BoundsValid" :: Bool ;
  "reg_tag_Pcc" :: Bool ;
  (* reg_DirectCs1 *)
  (* reg_CAndPerm *)
  (* reg_Sealer *)
  "reg_tag_BoundsCalc" :: Bool ;
  (* reg_ScrRead *)

  (* 2. PROGRAM COUNTER CAPABILITY (PCC) *)
  (* pcc_addr MUX Selects *)
  "pcc_addr_SeqNext" :: Bool ;
  "pcc_Branch" :: Bool ;
  "pcc_CjalTarget" :: Bool ;
  "pcc_CjalrTarget" :: Bool ;
  "pcc_Mepcc" :: Bool ;

  (* pcc_ecap MUX Selects *)
  "pcc_ecap_Current" :: Bool ;
  (* pcc_CjalrTarget *)
  (* pcc_Mepcc *)

  (* pcc_tag MUX Selects *)
  "pcc_tag_Current" :: Bool ;
  "pcc_tag_BranchJalPccTag" :: Bool ;
  (* pcc_Mepcc *)

  (* 3. SYSTEM & SPECIAL REGISTERS (specialRegs) *)
  "specialReg_writeEnableData" :: Bool ;
  "specialReg_writeEnableCap" :: Bool
}.

Definition AluOutput := STRUCT_TYPE {
  (* 1. Architectural Commit Targets *)
  "reg"             :: FullECapWithTag ;
  "pcc"             :: FullECapWithTag ;
  "special"         :: FullECapWithTag ;
  "interruptStatus" :: Bool ;

  (* 2. Extra Control Flow & Predictor Outputs *)
  "pcc_SeqNext"     :: Data ;
  "pcc_Branch"      :: Bool ;
  "branchTaken"     :: Bool ;
  "pcc_CjalTarget"  :: Bool ;
  "pcc_CjalrTarget" :: Bool
}.

Section AluDatapath.
  Variable ty : Kind -> Type.

  Variable pccECap : ty ECap.
  Variable pccAddr : ty Data.
  Variable src1 src2 : ty FullECapWithTag.
  Variable inst : ty Inst.
  Variable interruptStatus : ty Bool.
  Variable aluCtrl : ty AluControl.
  Variable wbCtrl : ty WbControl.

  (* TODO: Implement CHERIoT Sail link register sealing rules for CJAL / CJALR.
     When destination register is cra (x1): seal return capability as backward sentry
     (otype_sentry_bie = 5 if mstatus.MIE == 1 else otype_sentry_bid = 4).
     When destination register is not cra: output unsealed capability (otype = 0).
     Requires routing cd == cra (is_cd_cra) and mstatus.MIE into ALU datapath. *)
  Definition Alu : LetExpr ty AluOutput := (
    (* 1. Unpack Capability Slices *)

    LetE src1Addr : Data <- ##src1`"addr" ;
    LetE src1ECap : ECap <- ##src1`"ecap" ;
    LetE src1Tag : Bool <- ##src1`"tag" ;

    LetE src2Addr : Data <- ##src2`"addr" ;
    LetE src2ECap : ECap <- ##src2`"ecap" ;
    LetE src2Tag : Bool <- ##src2`"tag" ;

    (* Extract immediate slices from 32-bit inst word using direct bit extraction *)
    LetE simm12 : Data <- SignExtendTo AddrSz (#inst`[31:20]) ;
    LetE uimm20 : Data <- ({< #inst`[31:12], Const ty (Bit 12) Zmod.zero >}) ;
    LetE uimm20_11 : Data <- ({< #inst`[31:31], #inst`[31:12], Const ty (Bit 11) Zmod.zero >}) ;
    LetE shamt : Bit LgXlen <- ConstExtract (Xlen - (20 + LgXlen)) LgXlen 20 #inst ;
    LetE rs2Low : Bit LgXlen <- TruncLsb (Xlen - LgXlen) LgXlen #src2Addr ;

    LetE bimm13 : Bit 13 <- ({< #inst`[31:31], #inst`[7:7], #inst`[30:25], #inst`[11:8],
                                Const _ (Bit 1) Zmod.zero >}) ;
    LetE bimm12 : Data <- SignExtendTo AddrSz #bimm13 ;

    LetE jimm21 : Bit 21 <- ({< #inst`[31:31], #inst`[19:12], #inst`[20:20], #inst`[30:21],
                                Const _ (Bit 1) Zmod.zero >}) ;
    LetE jimm20 : Data <- SignExtendTo AddrSz #jimm21 ;

    (* Unpack AluControl flags needed for execution unit calls *)
    LetE MainAdder_subEnable        <- ##aluCtrl`"MainAdder_subEnable" ;
    LetE shiftRight   <- ##aluCtrl`"Shifter_isRight" ;
    LetE shiftArith   <- ##aluCtrl`"Shifter_isArith" ;
    LetE logicOpSel   <- ##aluCtrl`"Logic_opSel" ;
    LetE compSigned   <- ##aluCtrl`"Comparator_isSigned" ;
    LetE BoundsCalc_isRoundDown  <- ##aluCtrl`"BoundsCalc_isRoundDown" ;
    LetE SealerUnsealer_isUnseal <- ##aluCtrl`"SealerUnsealer_isUnseal" ;
    LetE ScrSanitizer_enable        <- ##aluCtrl`"ScrSanitizer_enable" ;

    LetE Comparator_isUnsigned <- Not #compSigned ;
    LetE constFalse   <- Const ty Bool false ;

    (* 2. Instantiate Shared Arithmetic & Logic Units *)
    LetE MainAdder_src1 : Bit (Xlen + 1) <-
      Or [ ITE0 ##aluCtrl`"MainAdder_src1_Rs1"     (ZeroExtendTo (Xlen+1) #src1Addr) ;
           ITE0 ##aluCtrl`"MainAdder_src1_Cs1Addr" (ZeroExtendTo (Xlen+1) #src1Addr) ;
           ITE0 ##aluCtrl`"MainAdder_src1_Cs1Top"  (##src1ECap`"top") ;
           ITE0 ##aluCtrl`"MainAdder_src1_CgpAddr" (ZeroExtendTo (Xlen+1) #src1Addr) ;
           ITE0 ##aluCtrl`"MainAdder_src1_PccAddr" (ZeroExtendTo (Xlen+1) #pccAddr) ] ;

    LetE MainAdder_src2 : Bit (Xlen + 1) <-
      Or [ ITE0 ##aluCtrl`"MainAdder_src2_Rs2"       (ZeroExtendTo (Xlen+1) #src2Addr) ;
           ITE0 ##aluCtrl`"MainAdder_src2_simm12"    (SignExtendTo (Xlen+1) #simm12) ;
           ITE0 ##aluCtrl`"MainAdder_src2_uimm20_11" (ZeroExtendTo (Xlen+1) #uimm20_11) ;
           ITE0 ##aluCtrl`"MainAdder_src2_Cs1Base"   (##src1ECap`"base") ;
           ITE0 ##aluCtrl`"MainAdder_src2_Cs2Addr"   (ZeroExtendTo (Xlen+1) #src2Addr) ] ;

    LETE MainAdder_sum : Bit (Xlen + 1) <- MainAdder MainAdder_src1 MainAdder_src2 MainAdder_subEnable ;
    LetE MainAdder_res : Data <- TruncLsb 1 Xlen #MainAdder_sum ;

    LetE cs1OType <- ##src1ECap`"oType" ;

    LetE PcAdder_src1 : Bit (Xlen + 1) <-
      ITE ##aluCtrl`"PcAdder_src1_PC_Rs1Addr" (ZeroExtendTo (Xlen+1) #pccAddr) (ZeroExtendTo (Xlen+1) #src1Addr) ;
    LetE PcAdder_src2 : Bit (Xlen + 1) <-
      Or [ ITE0 ##aluCtrl`"PcAdder_src2_bimm12" (SignExtendTo (Xlen+1) #bimm12) ;
           ITE0 ##aluCtrl`"PcAdder_src2_jimm20" (SignExtendTo (Xlen+1) #jimm20) ;
           ITE0 ##aluCtrl`"PcAdder_src2_simm12" (SignExtendTo (Xlen+1) #simm12) ] ;
    LETE PcAdder_res : Data <- PcAdder PcAdder_src1 PcAdder_src2 ;

    LetE Comparator_src2 : Data <- ITE ##aluCtrl`"Comparator_src2_simm12" #simm12 #src2Addr ;
    LETE Comparator_resVal : Bool <- Comparator src1Addr Comparator_src2 Comparator_isUnsigned constFalse constFalse ;

    LetE TopBoundsCheck_inpAddr : Bit (Xlen + 1) <-
      Or [ ITE0 ##aluCtrl`"TopCheck_inpAddr_SumMainAdder" #MainAdder_sum ;
           ITE0 ##aluCtrl`"TopCheck_inpAddr_SignExtRs2"   (SignExtendTo (Xlen+1) #src2Addr) ;
           ITE0 ##aluCtrl`"TopCheck_inpAddr_Cs1Addr"      (ZeroExtendTo (Xlen+1) #src1Addr) ;
           ITE0 ##aluCtrl`"TopCheck_inpAddr_Cs1Otype"     (ZeroExtendTo (Xlen+1) #cs1OType) ;
           ITE0 ##aluCtrl`"TopCheck_inpAddr_Cs2Addr"      (ZeroExtendTo (Xlen+1) #src2Addr) ;
           ITE0 ##aluCtrl`"TopCheck_inpAddr_Cs2Top"       (##src2ECap`"top") ;
           ITE0 ##aluCtrl`"TopCheck_inpAddr_PcAdder"      (ZeroExtend 1 #PcAdder_res) ] ;

    LetE TopBoundsCheck_limit : Bit (Xlen + 1) <-
      Or [ ITE0 ##aluCtrl`"TopCheck_limit_TopRep" (##src1ECap`"top") ;
           ITE0 ##aluCtrl`"TopCheck_limit_Cs2Top" (##src2ECap`"top") ;
           ITE0 ##aluCtrl`"TopCheck_limit_Cs1Top" (##src1ECap`"top") ;
           ITE0 ##aluCtrl`"TopCheck_limit_PccTop" (##pccECap`"top") ] ;

    LetE TopBoundsCheck_isInclusive : Bool <- ##aluCtrl`"TopCheck_isInclusive" ;
    LETE TopBoundsCheck_topValid : Bool <- TopBoundsCheck TopBoundsCheck_inpAddr TopBoundsCheck_limit TopBoundsCheck_isInclusive ;

    LetE BaseBoundsCheck_inpAddr : Bit (Xlen + 1) <-
      Or [ ITE0 ##aluCtrl`"BaseCheck_inpAddr_SumMainAdder" #MainAdder_sum ;
           ITE0 ##aluCtrl`"BaseCheck_inpAddr_SignExtRs2"   (SignExtendTo (Xlen+1) #src2Addr) ;
           ITE0 ##aluCtrl`"BaseCheck_inpAddr_Cs1Addr"      (ZeroExtendTo (Xlen+1) #src1Addr) ;
           ITE0 ##aluCtrl`"BaseCheck_inpAddr_Cs1Otype"     (ZeroExtendTo (Xlen+1) #cs1OType) ;
           ITE0 ##aluCtrl`"BaseCheck_inpAddr_Cs2Addr"      (ZeroExtendTo (Xlen+1) #src2Addr) ;
           ITE0 ##aluCtrl`"BaseCheck_inpAddr_Cs2Base"      (##src2ECap`"base") ;
           ITE0 ##aluCtrl`"BaseCheck_inpAddr_PcAdder"      (ZeroExtend 1 #PcAdder_res) ] ;

    LetE BaseBoundsCheck_base : Bit (Xlen + 1) <-
      ITE ##aluCtrl`"BaseCheck_base_PccBase" (##pccECap`"base") (##src1ECap`"base") ;

    LETE BaseBoundsCheck_baseValid : Bool <- BaseBoundsCheck BaseBoundsCheck_inpAddr BaseBoundsCheck_base ;

    LetE BranchJalPccTag_isBranch <- ##aluCtrl`"BranchJalPccTag_isBranch" ;
    LetE BranchJalPccTag_isCjal   <- ##aluCtrl`"BranchJalPccTag_isCjal" ;
    LetE BranchJalPccTag_isCjalr  <- ##aluCtrl`"BranchJalPccTag_isCjalr" ;
    LETE BranchJalPccTag_nextTag : Bool <- BranchJalPccTag BranchJalPccTag_isBranch BranchJalPccTag_isCjal BranchJalPccTag_isCjalr Comparator_resVal TopBoundsCheck_topValid BaseBoundsCheck_baseValid src1 ;

    LetE Shifter_amt : Bit LgXlen <- ITE ##aluCtrl`"Shifter_amt_Rs2Low_shamt" #rs2Low #shamt ;
    LETE Shifter_res : Data <- Shifter src1Addr Shifter_amt shiftRight shiftArith ;

    LetE LogicUnit_src2 : Data <- ITE ##aluCtrl`"Logic_src2_Rs2_simm12" #src2Addr #simm12 ;
    LETE LogicUnit_res : Data <- Logic src1Addr LogicUnit_src2 logicOpSel ;

    LetE BoundsCalc_base : Bit (AddrSz + 1) <- ITE0 ##aluCtrl`"BoundsCalc_base_Cs1Addr_Zero"
                                        (ZeroExtendTo (AddrSz+1) #src1Addr) ;
    LetE BoundsCalc_length : Bit (AddrSz + 1) <-
      Or [ ITE0 ##aluCtrl`"BoundsCalc_length_Rs2"    (ZeroExtendTo (AddrSz+1) #src2Addr) ;
           ITE0 ##aluCtrl`"BoundsCalc_length_simm12" (SignExtendTo (AddrSz+1) #simm12) ;
           ITE0 ##aluCtrl`"BoundsCalc_length_Rs1"    (ZeroExtendTo (AddrSz+1) #src1Addr) ] ;
    LETE BoundsCalc_res : Bounds <- BoundsCalc BoundsCalc_base BoundsCalc_length BoundsCalc_isRoundDown ;
    LetE BoundsCalc_outECap : ECap <-
      ##src1ECap `{ "base" <- ##BoundsCalc_res`"base" }
                 `{ "top"  <- ##BoundsCalc_res`"top" }
                 `{ "E"    <- ##BoundsCalc_res`"E" } ;

    LETE CAndPerm_res : FullECapWithTag <- CAndPerm src1 src2Addr ;
    LETE SealerUnsealer_res : FullECapWithTag <- SealerUnsealer SealerUnsealer_isUnseal src1Tag src1 src2 ;
    LETE ScrSanitizer_outCap : FullECapWithTag <- ScrSanitizer ScrSanitizer_enable src1 ;

    (* 3. Commit Routing Datapath MUXes (wbCtrl) *)
    LetE pcc_SeqNext : Data <- Add [ #pccAddr; $4 ] ;
    LetE BoundsCalc_cram : Data <- TruncLsb 1 Xlen (##BoundsCalc_res`"cram") ;
    LetE BoundsCalc_outLen : Data <- TruncLsb 1 Xlen (##BoundsCalc_res`"length") ;

    LetE regAddr : Data <-
      Or [ ITE0 ##wbCtrl`"reg_addr_MainAdder"          #MainAdder_res ;
           ITE0 ##wbCtrl`"reg_addr_PcAdder"            #PcAdder_res ;
           ITE0 ##wbCtrl`"reg_addr_Shifter"            #Shifter_res ;
           ITE0 ##wbCtrl`"reg_addr_Logic"              #LogicUnit_res ;
           ITE0 ##wbCtrl`"reg_addr_Comparator"         (ZeroExtendTo Xlen (ToBit #Comparator_resVal)) ;
           ITE0 ##wbCtrl`"reg_addr_uimm20"             #uimm20 ;
           ITE0 ##wbCtrl`"reg_addr_rs2"                #src2Addr ;
           ITE0 ##wbCtrl`"reg_addr_cs1Addr"            #src1Addr ;
           ITE0 ##wbCtrl`"reg_DirectCs1"               #src1Addr ;
           ITE0 ##wbCtrl`"reg_CAndPerm"                (##CAndPerm_res`"addr") ;
           ITE0 ##wbCtrl`"reg_Sealer"                  (##SealerUnsealer_res`"addr") ;
           ITE0 ##wbCtrl`"reg_addr_csrRead"            #src2Addr ;
           ITE0 ##wbCtrl`"reg_ScrRead"                 #src2Addr ;
           ITE0 ##wbCtrl`"reg_addr_capField"           #src2Addr ;
           ITE0 ##wbCtrl`"reg_addr_BoundsCalc_cram"    #BoundsCalc_cram ;
           ITE0 ##wbCtrl`"reg_addr_BoundsCalc_length"  #BoundsCalc_outLen ] ;

    LetE regECap : ECap <-
      Or [ ITE0 ##wbCtrl`"reg_ecap_null"       (Const ty ECap (getDefault _)) ;
           ITE0 ##wbCtrl`"reg_ecap_cs1"        #src1ECap ;
           ITE0 ##wbCtrl`"reg_ecap_Pcc"        #pccECap ;
           ITE0 ##wbCtrl`"reg_DirectCs1"       #src1ECap ;
           ITE0 ##wbCtrl`"reg_CAndPerm"        (##CAndPerm_res`"ecap") ;
           ITE0 ##wbCtrl`"reg_Sealer"          (##SealerUnsealer_res`"ecap") ;
           ITE0 ##wbCtrl`"reg_ecap_BoundsCalc" #BoundsCalc_outECap ;
           ITE0 ##wbCtrl`"reg_ScrRead"         #src2ECap ] ;

    LetE regTag : Bool <-
      Or [ And [ ##wbCtrl`"reg_tag_False" ; #constFalse ] ;
           And [ ##wbCtrl`"reg_tag_cs1BoundsValid" ; #src1Tag;
                 And [#TopBoundsCheck_topValid; #BaseBoundsCheck_baseValid] ] ;
           ##wbCtrl`"reg_tag_Pcc" ;
           And [ ##wbCtrl`"reg_DirectCs1" ; #src1Tag ] ;
           And [ ##wbCtrl`"reg_CAndPerm" ; ##CAndPerm_res`"tag" ] ;
           And [ ##wbCtrl`"reg_Sealer" ; ##SealerUnsealer_res`"tag" ] ;
           And [ ##wbCtrl`"reg_tag_BoundsCalc" ; #src1Tag ] ;
           And [ ##wbCtrl`"reg_ScrRead" ; #src2Tag ] ] ;

    LetE out_reg : FullECapWithTag <- STRUCT { "tag" ::= #regTag; "ecap" ::= #regECap; "addr" ::= #regAddr } ;

    LetE nextPccAddr : Data <-
      Or [ ITE0 ##wbCtrl`"pcc_addr_SeqNext" #pcc_SeqNext ;
           ITE0 ##wbCtrl`"pcc_Branch"       #PcAdder_res ;
           ITE0 ##wbCtrl`"pcc_CjalTarget"   #PcAdder_res ;
           ITE0 ##wbCtrl`"pcc_CjalrTarget"  #PcAdder_res ;
           ITE0 ##wbCtrl`"pcc_Mepcc"        #src2Addr ] ;

    LetE unsealedCs1ECap : ECap <- #src1ECap `{ "oType" <- $0 } ;

    LetE nextPccECap : ECap <-
      Or [ ITE0 ##wbCtrl`"pcc_ecap_Current" #pccECap ;
           ITE0 ##wbCtrl`"pcc_CjalrTarget"  #unsealedCs1ECap ;
           ITE0 ##wbCtrl`"pcc_Mepcc"        #src2ECap ] ;

    LetE nextPccTag : Bool <-
      Or [ ##wbCtrl`"pcc_tag_Current" ;
           And [ ##wbCtrl`"pcc_tag_BranchJalPccTag" ; #BranchJalPccTag_nextTag ] ;
           And [ ##wbCtrl`"pcc_Mepcc" ; #src2Tag ] ] ;

    LetE out_pcc : FullECapWithTag <- STRUCT { "tag" ::= #nextPccTag;
                                               "ecap" ::= #nextPccECap;
                                               "addr" ::= #nextPccAddr } ;

    LetE out_special : FullECapWithTag <-
      ITE ##wbCtrl`"specialReg_writeEnableCap" #ScrSanitizer_outCap #src1 ;

    @RetE _ AluOutput (STRUCT {
      "reg"             ::= #out_reg ;
      "pcc"             ::= #out_pcc ;
      "special"         ::= #out_special ;
      "interruptStatus" ::= Const ty Bool true;
      "pcc_SeqNext"     ::= #pcc_SeqNext ;
      "pcc_Branch"      ::= ##wbCtrl`"pcc_Branch" ;
      "branchTaken"     ::= #Comparator_resVal ;
      "pcc_CjalTarget"  ::= ##wbCtrl`"pcc_CjalTarget" ;
      "pcc_CjalrTarget" ::= ##wbCtrl`"pcc_CjalrTarget"
    })
  ).
End AluDatapath.
