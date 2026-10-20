# Full64 locked OR and resource foundation

This is an additive abstract-machine and current-resource profile. The
strict decoder recognizes `f0 48 09 37` (`LOCK OR qword [RDI], RSI`) and `c3`
(`RET`). It has its own event-retaining engine. It is not enrolled in the
existing scalar grader, legacy32 executor or TSO backend. A separate managed
worker layer and standalone callable certifier use these exact bytes. The
reusable memory primitive also defines AND/XOR; their instruction
encodings and OS operations are not admitted by this profile. The additive
[LockedSet64 profile](atomic-set64.md) now implements all three instructions
and checked OS operations; this document's managed scheduler and grader remain
OR-only.

## Checked behavior

`X86.AtomicEvent64` stores full64 address/before/after words. `LogicalEvent64`
retains the operation and mask selected by the actual instruction. One
`logicalRmwQWord` transition reads the current eight bytes and performs one
full64 update, with complete permissions/readback/outside-byte frames.
Abstract indivisibility is part of this single transition. It does not follow
from an ordinary `store64` or two adjacent DWORD accesses.

The operand must be naturally eight-byte aligned, canonical and nonwrapping,
contained in one virtual 64-byte line and 4-KiB page, readable and writable
at every byte. The executor additionally requires all eight operand bytes to
be nonexecutable. Even an unchanged-value OR requires write permission and
emits one event. Unsupported encodings and failed support checks return
explicit errors; they do not fall back to a weaker operation.

`LockedLogical64.execute` preserves every GPR, including RAX, and sets the
logical flags from the full64 result. AF is a separate arbitrary Boolean;
the remaining undefined-choice machinery does not choose a favorable value.
RET uses the actual current RSP and changes only RSP/RIP. Its existing modular
RSP update requires separate canonical/nonwrap post-RSP assumptions when
interpreted as a native callable ABI.

`LockedLogical64.Execution` provides `run`, `Executes`, continuing `Block`,
soundness/completeness, fixed-choice uniqueness and `AllExecutions`. Ordered
full64 events and operand accesses remain in the result. Each successful
instruction retires once; RET emits no RMW. Failed steps return their actual
fault before advancing the choice stream. The engine represents one
uninterrupted CPU execution, not an OS scheduler.

## Current resources and lifetime

`OS.Atomics64` wraps the existing borrowing/legacy32 world with distinct typed
cell and handle identities. A registered cell reserves its **whole allocation**
until explicit owner retirement. Closing the last handle leaves that
reservation intact. Retirement requires no stored handles and removes only
the registration, not the allocation.

Enrollment and every authorization check the current owner/epoch, complete
eight-byte containment in one allocation, permissions and nonexecute gate.
Ordinary mutations and read loans are blocked on registered allocations even
at disjoint subregions. Legacy32/64 registration conflicts and ordinary read
loans are excluded in both creation orders. Only checked wrappers are admitted
by the new history; there is no unrestricted legacy-history constructor.
Removed cell/handle IDs cannot be revived below their monotone frontiers.

`logicalDiscard` authorizes the stored actor/handle/cell, reads current RAM and
emits the full labeled OR event. Its private checked store has an exact
projection to the RMW memory, plus allocation, loan, permission and outside8
frames. `Machine.logicalDiscard_step` and its converse bind that OS operation
to the actual decoded step and identical event, for every AF choice.

`Routine.correct` proves the exact five-byte OR/RET routine has two retired
instructions and one event, preserves non-RSP registers, and returns to the
current caller slot with the independent per-bit union result in RAM. It
derives successful execution from present resource authority. Code and stack
disjointness/readability are explicit premises; this theorem does not acquire
their loans or create/join native threads. The old word is event data, not an
ABI return value.

## Histories and independent contracts

The general labeled `History` includes only successful checked lifecycle,
ordinary-resource and OR operations, plus idle. It preserves well-formedness,
permanent revocation and actual surviving loan cells. It permits retirement
and re-enrollment, so it makes no address-only value-stability promise.

`OrTrace` restricts an arbitrary finite schedule to OR operations on one
persistent registered cell. Each event is an actual operation output; its
before-word equals current RAM. The chain/readback theorem and independent
natural-number bit-membership contract prove that every final bit occurs in
the initial word or an actual event mask. Repeated/overlapping masks and
unchanged-value events remain included. `OrTrace.enabled` constructs a real
trace from any finite list of currently authorized requests without a
future-success hypothesis. This is a modification order for those operations,
not a C memory-order or liveness/fairness theorem.

## Managed creation, dispatch and join

`OS.AtomicThreads64.Start` references an already registered cell and the code
and caller-slot allocation tickets. Successful spawn acquires one distinct
actor handle and two read loans. Creation failure exposes no partial state.
The applying, returning and completed phases all retain those resources.
Completion does not release the handle: only successful join revokes that
worker's handle and both loans. The cell remains registered after join until
explicit owner retirement. A completed unjoined worker prevents retirement.

Each selection executes one actual OR or RET against a fresh projection of
current shared RAM. The private context has only registers, RIP and flags;
there is no earlier RAM snapshot to restore. Actual event identity, operands,
current-before/readback and CPU/OS memory equality are proved. RET and join
retain peer updates, and join returns the private context with unchanged RAX.
All other worker contexts and resources are framed.

The managed history admits only checked spawn/dispatch/join/mutate/retire and
idle operations. Raw lower-layer close/loan-finish/history operations cannot
enter it. Every finite legal supplied schedule, including arbitrary AF choices,
is constructively enabled from current worker/resource validity and remaining
selection counts. Two selections complete an initially applying worker and
emit exactly one RMW. Extra selection of a completed worker fails.
Dispatch-only schedules on one persistent cell project to `OrTrace`; RET
stutters on current RAM, and the independent union theorem includes duplicate,
overlapping and zero masks. This is safety and finite enabledness, without an
unconditional scheduling/fairness or native pthread theorem.

## Exact raw and full-ELF callable certificates

`AtomicLogical64.Resources` requires current actor authority and named code
and caller-slot loans. Their allocation identities derive complete target
disjointness; no future successful execution is an admission premise.
`ResultContract` specifies the natural-number bit-set union, actual event and
current OS transition, full64 RAM/register frames, exact count and every
surviving loan's actual cells. The caller supplies canonical/nonwrapping ABI
facts and the locked profile's physical interpretation assumptions.

From the repository, build and invoke:

```sh
lake build edsl-certify-atomic-logical64
lake env .lake/build/bin/edsl-certify-atomic-logical64 function.bin certificate.lean
lake env .lake/build/bin/edsl-certify-atomic-logical64 --elf function.elf certificate.lean
```

The raw checker accepts the entire five-byte input. The ELF checker parses
the literal full file with the restricted ELF64LE ET_EXEC loader and requires
exactly one executable segment, beginning at entry, with five file and memory
bytes. Executable prefixes, suffixes and BSS fail. Other nonexecutable segments
remain loader data. Full file bytes, parsed metadata, installed code and
fresh-load behavior are bound to the callable theorem. This verifies a callable
entry under the stated current resources, not Linux process startup.

Section/symbol tables do not override program-header byte claims. A changed
symbol size or an unused static relocation section can therefore leave the
formal callable certificate valid. Runtime relocation/dynamic program headers
are outside the loader. The separate native provenance extractor additionally
requires matching complete `.text`/FUNC spans and no relocation records.

The certifier emits typed literal Lean data and checks its universal claims
with the kernel and axiom audit before reporting `CERTIFIED`. Large full files
use small byte chunks and balanced concatenation at the existing Lean limits.
Its failure statuses are 2 for usage, 3 for unsupported input, 4 for malformed
input, 1 for certificate-check failure and 5 for IO failure; none establishes
a program defect. The separate [atomic union proof grader](atomic-logical64-grading.md)
accepts serialized proofs for selected windows under a fixed current-resource
contract. This convenience certifier keeps its complete-segment requirement.

## Validation and remaining boundaries

The Lean tests execute the actual decoder, primitives and OS wrappers. They
cover all eight permission bytes, bit63 and literal endian results, both AF
choices, current memory across actors, zero-handle registration, both conflict
orders, stale identities, independent allocations and code/stack loan frames.
Symbolic tests establish live well-formed authority for arbitrary old64/mask64
and independent membership results. Managed tests cover all six two-worker
interleavings and every AF choice, literal event chains, private registers,
peer-current RAM at RET/join, creation/join failures and lifetime gates.
Artifact tests cover raw/container mutations and current-resource admission.

`scripts/verify-atomic-logical64.sh` freshly compiles GCC13/Clang18 GNU23
fixtures, validates complete final ELF/raw identity, obtains callable kernel
certificates, independently recovers every emitted literal byte for comparison
with the original file, and replays all certificate terms plus both production
graphs in one fresh kernel. It builds with warnings as errors, audits transitive
dependencies and retains sources/statuses/manifests on incomplete runs.
The dedicated cached CI always runs these checks.

The native harness executes the exact fresh extracted bytes, independently
checks bit membership, endian bytes, guards, all GPRs and defined/preserved
flags, and checks owned threaded workloads after successful joins. Forced AF
controls pass; 33 owned semantic mutants fail their appropriate oracles. An
unlocked single-thread control deliberately passes, illustrating why these
finite observations do not establish LOCK indivisibility. Native observations
are separate from, and never premises of, the universal Lean theorems.

The separate atomic union grader accepts arbitrary proof submissions for the
strict OR/RET machine. Mixed-width atomic dispatch, wider atomic instructions,
store-buffer integration and C memory-order preservation remain future work.
The existing scalar/legacy32 tools keep their original scope.
The two-instruction count is exact for this routine. In the restricted OR/RET
instruction language, `Executes.changed_byte_lower_bound` proves that any
returning execution which changes an observed byte needs at least two retired
instructions. This is not a global x86 minimum, micro-op count or timing bound.

Physical interpretation additionally needs coherent ordinary WB RAM, stable
translation/permissions, contiguous injective physical backing and compatible
physical line/page layout, no unmanaged aliases or overlapping mixed-width
accesses, and no MMIO/DMA/non-temporal interference. The abstract memory does
not verify those conditions. Normal four-level user control state, CET off,
the existing stack alignment-check assumptions, stable code/private context,
and a correctly initialized live native atomic object with external lifetime
discipline also remain required. No physical LOCK, Linux kernel, complete
Arch system or source-language refinement is proved by these modules.
