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
   - In standard CHERIoT, capability bounds use a compressed exponent $E$.
   - In our ISA specification (`SpecDefines.v`), `cE` is 5 bits (`ExpSz = 5`), `cT` is 8 bits (`CapcTSz = 8`), `B` is 9 bits (`CapBSz = 9`), and permissions `p` are 6 bits.
   - The property $M_{msb} = (cE \ne 0)$ is leveraged such that $cE = 0x1F$ (all ones) represents $E = 0$ with $M_{msb} = 1$, allowing exact 32-bit representation of decompressed bounds.

3. **`ScrSanitizer` Tag Sanitization**:
   - Tag validation on SCR writes only checks $\text{LSB} = 0$ for `MePcc`, `Mtcc`, and `MePrevPcc`. Writing an invalid target clears the tag rather than raising an immediate fault or modifying the capability metadata.

4. **Unified `MTVAL` Encoding for All Exceptions**:
   - In our ISA specification, all exceptions, including standard RISC-V exceptions, set `MTVAL` in the same structured format (`{S, RegIdx, Cause}`) that CHERI exceptions use, regardless of whether `MCAUSE` is a CHERI or standard RISC-V cause code.
   - For example:
     - **Illegal Instruction** (`EXC_IllegalInst`): `MTVAL.RegIdx` points to `PCC` (the PC capability where the illegal instruction was fetched).
     - **Misaligned Accesses** (`EXC_LoadAddrMisaligned`, `EXC_StoreAddrMisaligned`): `MTVAL.RegIdx` points to the capability register (`cs1`) performing the dereference.
