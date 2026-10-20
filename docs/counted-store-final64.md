# A fresh counted-store client with a final store

`tests.fixtures.CountedStoreFinal64` supplies a client proof of the independently
registered `countedStore64` task. Its claim, `EDSL.CountedStoreFinal64.claim`,
stays outside `EDSL.Grading.Known` and the grader's trusted import snapshot.
Reference and body packets reconstruct the client proof under the bounded
grading policy. The task and domain are unchanged. The default aggregate
decoder allowance is now 300000 work steps, increased from 200000 for this
complete loop proof (about 243000 steps). Packet bytes, declaration count,
expression depth and kernel heartbeat caps are unchanged.
The controller now apportions its existing heartbeat cap with cumulative
prefix ceilings, matching the pinned kernel API's cumulative counter. This
corrects an artificially low cap on packets with many helpers; the configured
total is unchanged. See [grading limits](grading.md).
The shared `CountedStore64.Common.Frame` API is parameterized by arbitrary
candidate bytes. It proves code, stack, permission, outside-memory, register
and flag preservation through the ordinary machine operations. The client
reuses these generic lemmas and checks its own invariant and local steps in
the packet. The common library adds no selected byte window or task claim.

The owned `fixtures/counted-store-final64.c` fixture produces these identical
20 bytes with GCC13 GNU23 (`gnu2x`) `-Os` and Clang18 GNU23 (`gnu2x`)
`-O1 -falign-loops=1`, with LTO/CET disabled:

```text
48 89 f0 48 85 d2 74 0b 48 ff c0 48 ff ca 75 f8 48 89 07 c3
```

They copy RSI to RAX, test the full RDX count and return immediately on zero.
The positive path increments RAX and decrements RDX until zero, then stores
RAX through RDI and returns. The original [GCC](counted-store64.md) and
[Clang](counted-store64-clang.md) profiles store during each iteration. This
different placement satisfies the same final-state contract: RAX is
`argument + count` modulo `2^64`, zero count retains the old target value, and
positive counts leave the returned value in the target. The fixture's volatile
target and GNU asm barrier are compiler inputs; the proof concerns final
machine bytes and establishes no C/volatile/asm semantics or source preservation.

The proof covers every admitted full64 count and every modeled AF stream.
Admission supplies present code, current target bytes/permissions, a disjoint
caller return slot and the existing address facts. It adds no successful-run
or future ownership-mutation premise. The independent postcondition preserves
bytes outside the target, complete permission maps, callee-saved registers and
nonarithmetic flags. The actual RET reads the original full eight-byte caller
slot and restores the caller control flow and stack position.

The current-resource proof tracks the same evolved OS world through every
actual checked ordinary store. Returned ownership retains allocation identities,
owners/epochs, live loans, outside cells, permissions and complete RAM coupling,
with authority for another arbitrary checked full64 store. This uses the same
ordinary-RAM resource domain as the [fixed task](counted-store64-grading.md).
Atomic operations, syscalls and concurrent interference remain outside it.
Instruction accounting is separate from the registered result contract;
successful grading does not establish a global operation minimum.

`execution_exact` proves four model instructions for zero count and
`3*N+5` for positive count, including RET, with exactly the original STACK8
operand read. `resource_exact` retains this accounting together with the
functional result, current OS effects and usable returned authority. The
`cost_comparison` theorem compares these concrete loops: the final-store cost
is at most Clang's `4*N+4` and GCC's `6*N+4`, and strictly below Clang's when
`N > 1`. This comparison makes no claim about other implementations, source
effects, cycles or micro-ops.

Lean regressions cover zero retention, high-half and maximum counts, exact
instruction counts that cannot wrap, insufficient fuel and reusable returned
ownership. Two admitted supported-code counterexamples check the independent
contract: an inverted back edge returns the wrong value, and replacing the
final store by a register move returns the correct RAX but fails the memory
postcondition. These are project-owned synthetic examples.

Run the complete integration after building the client proof:

```sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store-final64.sh
```

The script compiles and links both final artifacts, rejects relocations and
checks the complete extracted `.text` identity. It builds only the required
client module, performs the targeted axiom audit and a fresh kernel replay,
checks client isolation, exports reference/body packets and grades both raw and
explicit-span ELF artifacts for each compiler. Changed bytes, task and selected
span reject those packets. Both unchanged direct convenience shape APIs reject
this different window; the fixed-contract grader accepts its independent proof.
Packet rejection, unsupported analysis or timeout establishes no defect.

The independent native oracle executes both extracted byte windows for 504
calls each, with full64 arguments, practical counts, aligned/unaligned/page-edge
targets above 4GiB, two old values, complete data-page frames and SysV ABI checks.
It also rejects six unchanged generic owned mutants using GCC-shaped loops;
these test the oracle rather than mutate the final-store implementation. Native
observations do not execute huge counts or observe intermediate store counts.
The native checks alone can be run without Lean:

```sh
bash scripts/verify-counted-store-final64.sh --native-only
```

Evidence and provenance go to `artifacts/counted-store-final64/`; native-only
success explicitly excludes proof checks. The [supported machine profile](coverage.md#supported-machine-profile)
requires ordinary RAM, stable code/data, disabled alignment checking/CET and
no asynchronous changes. This proves no physical CPU/kernel conformance,
whole-OS safety, concurrent visibility, physical timing or global optimum.
