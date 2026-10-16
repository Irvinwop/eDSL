# Two-array sums through local CFG proofs

The `Pair32` instance verifies the exact 35-byte GCC 13 two-loop function in
[`fixtures/cfg/pair.c`](../fixtures/cfg/pair.c). It uses the reusable
[CFG/local-obligation interface](cfg.md), without adding a whole-function shape
recognizer or extending the sequential ISA.

The independent result is `sum32 (valuesA ++ valuesB)`: the sum of two lists
modulo 2^32, zero-extended to full RAX. This specification does not describe
instruction selection, loop order, or argument registers.

## Current input and result contracts

[`Pair32.Pre`](../EDSL/Pair32/Contract.lean) requires current executable bytes,
current four-byte array contents and nonwrapping spans for both lists, full
RSI/RCX counts, and a complete current return slot. RDI/RSI describe A; RDX/RCX
describe B. Both empty inputs allow arbitrary unused pointers, including
unmapped or noncanonical addresses.

The immutable arrays may overlap whenever their current contents agree. The
contract does not require input/input separation. It requires each input's
own current contents; matching code and A alone cannot establish B's premise.

`Post` requires the mathematical result in full RAX, unchanged full memory,
the actual return RIP and RSP advance, preserved GPRs outside
`[rax,rsi,rdi,rcx,rdx,rsp]`, and preserved nonarithmetic flags. The profile is a
callable function: caller startup, subsequent caller execution, native CPU
conformance and asynchronous interference remain outside this theorem.

## Compose the two loops

The checked graph has 14 instructions and cutpoints at entry and the two
headers. The same local instruction proofs cover both phases with different
counter/pointer registers. A first-phase invariant retains the current B
arguments as well as the remaining A suffix; switching phases constructs the
B invariant from those retained arguments and unchanged current RAM.

The rank is `remainingA + lengthB + 1` in A and `remainingB` in B, with a larger
entry rank. Every back edge decreases its phase count, and the A-to-B transfer
decreases even when A is empty. Local annotations contain current-state facts,
not an assumed successful future execution.

[`Pair32.Correctness`](../EDSL/Pair32/Correctness.lean) composes these obligations
into actual execution for every modeled undefined-AF choice stream, prefix
safety and divergence exclusion. Optional local accounting establishes exactly
`6*(lengthA+lengthB)+6` retired model instructions, including RET. The ordered
operand footprint lists all A words, then all B words, then the eight-byte
return operand. Aliased operands remain separate read events in that list.
These counts establish neither hardware timing nor a minimum across different
implementations.

## Keep both resource admissions current

[`Pair32.Resources`](../EDSL/Pair32/Resources.lean) combines two current
`OS.ArrayResources.Admission` instances over the same shared state and worker.
They agree on code and the return context while retaining independent input
loans. Each input must be separated from code/stack under the existing array
resource contract; there is no additional input/input disjointness condition.

B reads use B's current admission, and the complete return operand uses the
stack loan. The resource theorem retains both admissions in the returned
state. For each observed read, its origin theorem exposes a real execution
prefix, the actual step and operand, both current admissions there, current
loan permission, and a successful load from that state's RAM. Identical read
records from aliased inputs need not have a unique phase or occurrence in this
existential origin API; the exact ordered footprint separately establishes
their repetitions. Empty arrays do not
consult their unused input loan IDs. These are logical resource and modeled
RAM guarantees, with physical OS enforcement still an explicit boundary.

## Evidence and reproduction

```sh
lake build EDSL
lake env lean -DwarningAsError=true tests/Pair32.lean
lake env lean -DwarningAsError=true tests/Pair32Resources.lean
EDSL_GCC=gcc-13 bash scripts/verify-cfg.sh
```

The Lean cases include nonvacuous current-memory witnesses, all four
empty/nonempty combinations, modular wrap, all-AF results and exact traces,
arbitrary unused pointers, compatible aliases, current B mutations and
full-width argument checks. Resource cases exhibit real current admissions
and test loan authority and complete operand spans.

The integration script compiles and links the owned function, checks raw and
explicit-span ELF imports, then emits separate functional modules binding the
fresh bytes to the proved instance. ELF correctness additionally binds modeled
loading and explicit caller data/stack premises. Native observations use
independent algebraic expectations, readonly guarded inputs, identical and
partially overlapping inputs, full RAX and SysV preservation. Evidence goes
to `artifacts/cfg-fixtures/pair/`.

Static `edsl-cfg-import` success remains a finite-code import verdict. The
supplemental functional proof establishes the task result; arbitrary imported
functions still require their own independent specification, admission and
local proofs.
