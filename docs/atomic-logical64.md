# Full64 locked OR and resource foundation

This is an additive abstract-machine and current-resource foundation. The
strict decoder recognizes `f0 48 09 37` (`LOCK OR qword [RDI], RSI`) and `c3`
(`RET`). It has its own event-retaining engine. It is not enrolled in the
existing scalar grader, legacy32 executor, managed-thread executor or TSO
backend. The reusable memory primitive also defines AND/XOR; their instruction
encodings and OS operations are not admitted by this profile.

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

## Validation and remaining boundaries

The Lean tests execute the actual decoder, primitives and OS wrappers. They
cover all eight permission bytes, bit63 and literal endian results, both AF
choices, current memory across actors, zero-handle registration, both conflict
orders, stale identities, independent allocations and code/stack loan frames.
Symbolic tests establish live well-formed authority for arbitrary old64/mask64
and independent membership results. CI builds with warnings as errors, audits
transitive theorem dependencies and replays the stored EDSL proofs in a fresh
kernel. The cache never skips these checks.

This foundation does not yet provide managed full64 spawn/dispatch/join,
standalone raw/full-ELF atomic certificates, native observation/replay,
mixed-width atomic dispatch, store-buffer integration or C memory-order
preservation. The existing scalar/legacy32 tools keep their original scope.
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
