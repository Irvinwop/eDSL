# Full64 locked AND, OR and XOR

`X86.LockedSet64` is an additive instruction profile for
`f0 48 {21,09,31} 37` and `c3`: locked AND/OR/XOR of `[RDI]` with RSI, followed
by an actual current-stack RET. The existing OR-only certifier, managed worker
scheduler and union proof grader keep their original scope.

## Instruction and resource contracts

Each successful logical instruction reads the current complete eight-byte
word, emits its operation, mask, address, before and after values, and performs
one full64 functional RMW. All GPRs are preserved. Defined logical flags use
the full64 result; AF is a separate arbitrary Boolean at each retired
instruction. The execution relation quantifies every choice stream, retains
all ordered events and operand accesses, and proves evaluator soundness,
completeness and uniqueness for fixed choices. Failed steps preserve their
precise fault before advancing the choice stream.

The same support gates apply to every mask, including unchanged results:
aligned, canonical, nonwrapping eight-byte RAM in one virtual 64-byte line and
4-KiB page; all eight bytes readable, writable and nonexecutable. There is no
no-change shortcut that weakens write authority. Unsupported prefixes, widths,
registers, operations and addresses fail explicitly.

`OS.Atomics64.logicalUpdate` authorizes the current stored actor handle and
persistent cell before reading or changing RAM. It checks current ownership,
epoch, allocation containment and permissions. Its complete projected memory
equals the CPU primitive's memory, with matching event identity and operation.
Well-formedness, allocation-wide reservation, current peer authority, registry
frontiers, every ordinary loan's actual cells and other registered allocations
survive. Revoked handles/cells, wrong actors and stale ownership fail before
mutation. Specializing to OR equals the unchanged `logicalDiscard` by `rfl`.

`LogicalMachine` proves both directions between actual decoded CPU dispatch
and the checked OS operation. `LogicalRoutine.correct` proves the exact
five-byte callable routines for all masks and AF choices: one event, two
retired instructions, current RAM readback, independent natural-bit result,
actual caller return, RSP adjustment and all other registers preserved.
The `AtomicSet64` contract supplies current named code/caller-slot loans;
their disjointness from the atomic operand is derived from resource invariants.
It retains the returned well-formed world, exact loan cells, registries and
outside-operand memory. It returns no old value in RAX.

`AtomicSet64.Domain` reuses the operation-neutral fresh byte installation and
resource constructor. Every old word and mask has an admitted invocation for
each operation, with actual initialized RAM and real code/caller loans. These
inhabited-domain proofs are separate from the certifier's trusted imports.

## Modification orders and cost

`LogicalTrace` retains every checked update to one persistent registered cell.
Operations, actors, handles and masks may vary. Present authority constructs a
real trace for every finite authorized request list, with exactly those labels.
Current-before chaining and readback bind the value proof to actual RAM.
Retirement, re-enrollment, unrelated writers, instruction-level thread
scheduling and generic spawn/join need a wider relation.

Homogeneous traces have separate independent contracts:

| Operation | A final bit is present exactly when |
| --- | --- |
| AND | The initial word and every actual mask contain it. |
| OR | The initial word or at least one actual mask contains it. |
| XOR | Its initial membership plus the number of containing mask occurrences is odd. |

Duplicate XOR masks count twice and cancel; unchanged events are retained.
Mixed traces preserve the actual ordered operations and cannot use a
homogeneous theorem without proving the operation tags.

Separate accounting proves `instructions = events.length + 1`. A returning
execution that changes any observed byte needs at least two instructions in
this logical/RET profile. The five-byte routines attain two. This is a bound
on modeled retired instructions, with no global x86 optimum, micro-op,
CPU-time or energy claim.

## Exact artifacts and validation

```
lake build edsl-certify-atomic-set64
lake env .lake/build/bin/edsl-certify-atomic-set64 and routine.bin Certificate.lean
lake env .lake/build/bin/edsl-certify-atomic-set64 xor --elf routine.elf Certificate.lean
bash scripts/verify-atomic-set64.sh
```

The certifier selects `and`, `or` or `xor` as the requested independent set
operation. Raw input must be the complete five bytes. ELF input binds the
entire literal file and checked parser to one complete executable segment
starting at entry, with no executable prefix, suffix or BSS. Section names,
symbol spans and disassembler output cannot override PT_LOAD byte authority.
Present resources, fresh loading and platform assumptions remain explicit.
Unsupported code exits 3, malformed input 4, usage 2, IO failure 5, and failed
certificate checking 1; none establishes a program defect.

The integration script freshly compiles nine functions: all three operations
with GCC13 and Clang18 GNU23, and Clang18's GNU++26 subset (`-std=gnu++2c`).
It checks raw/full-ELF and wrong-operation/container inputs, audits theorems,
roundtrips every emitted literal to the original whole input, and replays
stored proofs in a fresh kernel environment. Unique runs preserve failures,
source copies (including the CI workflow), source stability and manifests.
CI caches the pinned toolchain and Lake outputs while rerunning these checks.

The separate native script uses independent per-bit, endian, guard, GPR and
defined-flag oracles, AF=0/1 controls, owned semantic mutants and finite
threaded intersection/union/parity workloads with checked creates/joins.
Loaded project-owned assembly slots must match all nine complete final
extractions before execution. They operate on actual initialized aligned C
atomic storage kept live through joins. C++ output is observed as machine
bytes; no cast between C and C++ atomic object types is used or justified.
Unlocked single-thread controls deliberately pass: finite observations do
not establish LOCK atomicity. Native evidence is never a theorem premise.

## Remaining assumptions

The architectural model is informed by the
[Intel software developer manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
Physical LOCK refinement remains external: ordinary coherent WB RAM, stable
translation/code/private context, no problematic physical aliases or
mixed-width/MMIO/DMA interference, normal supported user controls, CET off,
and valid atomic representation, initialization and lifetime. Callable native
interpretation also requires canonical, nonwrapping post-return RSP.

These results do not establish C/C++ source preservation or memory orders,
TSO64, pthread/kernel refinement or whole-OS safety. The existing OR-only
managed scheduler and grader remain available under their documented contracts.
The separate [atomic set proof grader](atomic-set64-grading.md) accepts arbitrary
literal windows with checked proofs of uninterrupted set results, including
mixed-operation implementations. It reuses a windowed grading loader and does
not change this convenience certifier's one-operation complete-segment format.
The additive [mixed-operation scheduler](atomic-set-workers.md) handles finite
managed AND/OR/XOR bodies with current peer RAM, pinned resources and checked
collection under its own model contracts.
