# Cheriot
CHERIoT ISA specification, formal verification, and implementation in [Guru](https://github.com/Cherified/Guru).

The Makefile expects [CHERIoT RTOS](https://github.com/CHERIoT-Platform/cheriot-rtos) installed in ${CHERIOT_ROOT}/cheriot-rtos and [CHERIoT LLVM](https://github.com/CHERIoT-Platform/llvm-project) in ${CHERIOT_ROOT}/cheriot-llvm.
Use this [link](https://github.com/CHERIoT-Platform/cheriot-rtos/blob/main/docs/GettingStarted.md#building-cheriot-llvm) to build LLVM.
The object that is being initialized in the Binary file is some executable binary compiled for CHERIoT

## Architectural & Specification Differences (`cheriot-sail` vs. Our Specification)

While `cheriot-sail` is the defacto standard specification, our ISA specification (and hence the implementation) incorporate several targeted architectural modifications and optimized encodings:

1. **`MePrevPcc` Special Capability Register (SCR index 27) & Deferred Jump Faults**:
   - In `cheriot-sail`, invalid `CJALR` targets/sentries synchronously raise hardware exceptions in the execute stage.
   - In our ISA specification, `CJALR`, `CJAL`, and branches do **not** synchronously fault on invalid targets/sentries. Instead, they clear `PCC.tag` (marking `PCC` invalid). The exception is deferred until the subsequent **Instruction Fetch (IF)** stage.
   - The architectural register **`MePrevPcc`** records the `PCC` of every committed instruction, allowing the OS trap handler to accurately attribute the fetch exception back to the source jump instruction.

2. **5-bit `cE` Capability Encoding**:
   - In standard CHERIoT, capability bounds use a compressed exponent E.
   - In our ISA specification (`SpecDefines.v`), `cE` is 5 bits (`ExpSz = 5`), `cT` is 8 bits (`CapcTSz = 8`), `B` is 9 bits (`CapBSz = 9`), and permissions `p` are 6 bits.
   - The property M_msb = (cE != 0) is leveraged such that cE = 0x1F (all ones) represents E = 0 with M_msb = 1, allowing exact 32-bit representation of decompressed bounds.

3. **`ScrSanitizer` Tag Sanitization**:
   - Tag validation on SCR writes only checks LSB = 0 for `MePcc`, `Mtcc`, and `MePrevPcc`. Writing an invalid target clears the tag rather than raising an immediate fault or modifying the capability metadata.

4. **Unified `MTVAL` Encoding for All Exceptions**:
   - In our ISA specification, all exceptions, including standard RISC-V exceptions, set `MTVAL` in the same structured format (`{S, RegIdx, Cause}`) that CHERI exceptions use, regardless of whether `MCAUSE` is a CHERI or standard RISC-V cause code.
   - For example:
     - **Illegal Instruction** (`EXC_IllegalInst`): `MTVAL.RegIdx` points to `PCC` (the PC capability where the illegal instruction was fetched).
     - **Misaligned Accesses** (`EXC_LoadAddrMisaligned`, `EXC_StoreAddrMisaligned`): `MTVAL.RegIdx` points to the capability register (`cs1`) performing the dereference.

5. **MMIO Register Decoding & Peripheral Interrupt Semantics**:
   - **Word-Aligned Register Decoding**: For peripherals (`SpecRevoker.v`, `Clint.v`, `Plic.v`, `Uart.v`), register offset decoding ignores the low 2 bits (`LgNumBytesXlen`), treating accesses within a 4-byte boundary as addressing the corresponding 32-bit register.
   - **Revoker W1C Semantics**: In `SpecRevoker.v`, the `interruptStatus` register implements true Write-1-to-Clear (W1C) semantics: writing a word with bit 0 set clears the interrupt, while bit 0 = 0 leaves the status untouched. Writes to unrelated registers do not disturb `interruptStatus`.
   - **CLINT Sticky Interrupt Latch**: In `Clint.v`, standard RISC-V timer comparisons (`mtime >= mtimecmp`) are unsigned (`Sge`). To prevent dropped interrupts when `mtimecmp = 2^64 - 1` and `mtime` rolls over to 0, an internal sticky latch (`interruptPending`) captures the match and holds the interrupt asserted across rollover. The latch is cleared only when software reprograms `mtimecmp` (or writes `mtime`) such that the comparator threshold is in the future (`mtime < mtimecmp`).

---

## Multi-Core Memory Consistency & Pipeline Refinement Specification

This section defines the formal operational contract for memory ordering (`FENCE`), instruction synchronization (`FENCE.I`), and pipeline refinement for the CHERIoT processor in Coq.

The specification models a multi-core system as an **atomic, 1-step interleaved transition system** on shared memory (`specMemTree`). To allow the hardware implementation to pipeline, buffer, and reorder memory accesses without violating the sequential specification, program traces must satisfy the following contracts.

### 1. The Multi-Core Program Validity Contract (`FENCE`)

#### Definition 1: True Dependency on a Single Core
A later memory access `I2` has a **True Dependency** on an earlier memory access `I1` on the same core if and only if:
* `I1` is a load and varying the value loaded by `I1` (while keeping all other register and memory state unchanged) produces a different **target address** or **store data** for `I2`.

*(Pseudo-dependencies, such as `y = x * 0` or `y = x XOR x`, where the address and data remain constant regardless of `I1`'s loaded value, are NOT true dependencies).*

#### Definition 2: The Multi-Core Precondition Filter Rule
In the atomic specification, for any two distinct memory addresses `A` and `B`:

**Whenever:**
1. Core 1 performs an access `access1(A)` and later performs `Store(B)`.
2. Core 2 performs `Load(B)` (observing Core 1's write to `B`) and later performs `access2(A)`.
3. At least one of `access1(A)` or `access2(A)` is a `Store` (i.e., the accesses to `A` conflict across the two cores).

**The program trace is Valid if and only if:**
* Either there is an appropriate `FENCE` (i.e. `FENCE(R, W)` or `FENCE(W,W)`) in between `access1(A)` and `Store(B)` OR there is a True Dependency from `access1(A)` to `Store(B)`.
* Either there is an appropriate `FENCE` (i.e. `FENCE(R, W)` or `FENCE(R,R)`) in between `Load(B)` and `access2(A)` OR there is a True Dependency from `Load(B)` to `access2(A)`.

---

### 2. The Instruction Synchronization Contract (`FENCE.I`)

#### The Dynamic `FENCE.I` Rule
On any dynamic execution trace executed on the atomic specification:
* Whenever a trace contains a `Store(A)` and later a `Fetch(A)`, there must be a `FENCE.I` in between.

---

### 3. The Refinement Theorem

A ValidProgram is one where all traces generated when executed on the atomic specification satisfy the `FENCE` Rule (Section 1) and the `FENCE.I` Rule (Section 2).

```coq
Theorem pipeline_refines_spec : forall (p : Program) (result : FinalState),
  ValidProgram p -> Pipeline_Exec p result -> Spec_Exec p result.
```
