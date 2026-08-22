# CHERIoT Multi-Core Memory Consistency & Pipeline Refinement Specification

This document defines the formal operational contract for memory ordering (`FENCE`), instruction synchronization (`FENCE.I`), and pipeline refinement for the CHERIoT processor in Coq.

The specification models a multi-core system as an **atomic, 1-step interleaved transition system** on shared memory (`specMemTree`). To allow the hardware implementation to pipeline, buffer, and reorder memory accesses without violating the sequential specification, program traces must satisfy the following contracts.

---

## 1. The Multi-Core Program Validity Contract (`FENCE`)

### Definition 1: True Dependency on a Single Core
A later memory access `I2` has a **True Dependency** on an earlier memory access `I1` on the same core if and only if:
* `I1` is a load and varying the value loaded by `I1` (while keeping all other register and memory state unchanged) produces a different **target address** or **store data** for `I2`.

*(Pseudo-dependencies, such as `y = x * 0` or `y = x XOR x`, where the address and data remain constant regardless of `I1`'s loaded value, are NOT true dependencies).*

---

### Definition 2: The Multi-Core Precondition Filter Rule
In the atomic specification, for any two distinct memory addresses `A` and `B`:

**Whenever:**
1. Core 1 performs an access `access1(A)` and later performs `Store(B)`.
2. Core 2 performs `Load(B)` (observing Core 1's write to `B`) and later performs `access2(A)`.
3. At least one of `access1(A)` or `access2(A)` is a `Store` (i.e., the accesses to `A` conflict across the two cores).

**The program trace is Valid if and only if:**
* Either there is an appropriate `FENCE` (i.e. `FENCE(R, W)` or `FENCE(W,W)`) in between `access1(A)` and `Store(B)` OR there is a True Dependency from `access1(A)` to `Store(B)`.
* Either there is an appropriate `FENCE` (i.e. `FENCE(R, W)` or `FENCE(R,R)`) in between `Load(B)` and `access2(A)` OR there is a True Dependency from `Load(B)` to `access2(A)`.
---

## 2. The Instruction Synchronization Contract (`FENCE.I`)

### The Dynamic `FENCE.I` Rule
On any dynamic execution trace executed on the atomic specification:
* Whenever a trace contains a `Store(A)` and later a `Fetch(A)`, there must be a `FENCE.I` in between.
---

## 3. The Refinement Theorem

A ValidProgram is one where all traces generated when executed on the atomic specification satisfy the `FENCE` Rule (Section 1) and the `FENCE.I` Rule (Section 2).

```
Theorem pipeline_refines_spec : forall (p : Program) (result : FinalState),
  ValidProgram p -> Pipeline_Exec p result -> Spec_Exec p result.
```