# Private futex service and exact request stubs

`EDSL.OS.Futex` implements one registered four-byte word in one stable address
space, with WAIT_PRIVATE, expected32, null timeout, and WAKE_PRIVATE with count
one. It composes actual `OS.Suspend` instruction/drain execution, current
`OS.Atomics` resources, an explicit service queue, and typed raw results.
The kernel, scheduler, native thread runtime and hardware remain external.

## Capture, service, and return

`Physical.issue` first runs actual decoding/execution. On SYSCALL it binds the
actual pending `Saved.identifier`, classifies the full request and retains a
fresh compatible call handle in the same adapter transition. A keeper already
reserves the mutable allocation. Handles preserve allocation lifetime without
freezing the word's value. Capture checks complete four-byte containment in the
configured lower-userspace interval and non-executable word storage. This
interval is a target contract, not a derived proof of Linux `access_ok`.

The canonical requests use full RAX=202, RDI=W, RSI=128/129, zero R10/R8/R9,
and zero-extended expected32 in RDX for WAIT or full RDX=1 for WAKE1. Other
request profiles return an explicit unsupported error, without a partial state.
The model has one registration; `spaceId` does not establish isolation between
multiple modeled processes or private-key resolution in Linux.

Comparison reads the live call pin against current resource RAM. Equality and
queue insertion form one transition; mismatch makes WAIT ready with full raw
RAX=-11. WAKE chooses any eligible invocation, removes precisely it, returns
one and readies that waiter with zero. An empty wake returns zero and saves no
credit. There is no FIFO or priority guarantee. A queued retry retains the same
invocation/pin and must compare again; spurious zero readiness is also allowed.
Changing W alone does not notify a waiter. Zero establishes no predicate,
mutex acquisition or payload ownership.

Only a ready call can resume. Its stored operation-specific outcome supplies
RAX; flags/RCX/R11 may vary arbitrarily. Actual Suspend resumption uses current
RAM internally. Call deletion and closure of its unique nonkeeper pin happen
in the same pure transition. The keeper remains through actual user RETs.
Parked and idle traces may continue forever; no fairness or eventual completion
is assumed. SYSCALL requires its own FIFO empty and does not flush it or peers.

## What the proofs cover

`Runtime.Invariant` combines the service's pending-call/queue/pin invariant with
**equality of the entire managed and physical RAM**. `schedule_invariant` proves
these properties for every successful mixed adapter prefix, with an actual
`Atomics.History`. Service actions stutter RAM, and actual drains/atomic events
have checked managed updates with the same full memory effect. Old word values
come from current RAM. `synchronize_enabled` supplies positive replay enabledness
from current `Physical.Ready` authority; compare, each eligible wake choice,
retry, spurious completion and ready resume have separate enabledness theorems.

Runtime preserves the whole loan map. `Runtime.loan_frame` consequently retains
existing code/return-stack loans and their bytes/permissions for every accepted
active prefix, with no assumed final successful return. Pins and loans have
different contracts: the mutable W allocation must not have an ordinary read
loan. `Examples.FutexSafety.waiter_stack_frame` connects the actual adopted
cohort's complete eight-byte return stack to this universal prefix theorem.

`Lifecycle.collect` checks actual RETs, empty FIFOs, no pending invocations,
no service records and an empty queue before closing the caller's declared loan
and producer-handle plan plus the keeper. Enabledness follows from current
live/distinct plan records. Exact effects preserve RAM, all frontiers, and
unlisted handles/loans. Collection closes reservations; later managed release
and reuse are separate operations. Revoked handles cannot revive.

The adapter can reject an otherwise executable physical effect when it lacks
a matching grant/handle. Its pure error result does not roll native hardware
back or enforce native mapping lifetime. An ordinary unauthorized store can
currently enter a physical FIFO and be rejected at replay of its later drain.
`Runtime.Invariant` does not itself assert payload authority for every queued
store, a live keeper in a call-free state, or a complete per-worker client
control/loan contract. Call-free registration enabledness requires the separate
current keeper fact. Deriving `Physical.Ready`, FIFO authorization and protected
completion for every physical interleaving of an admitted concrete client is
further work; successful adapter safety is not that coverage theorem.

`Publication` proves current-word mismatch, sole-waiter wake, absence of wake
credits and spurious-word framing. The owned examples exhibit both comparison
orders and retry across actual XCHG publication. A generalized no-lost-wakeup
proof over all physical client schedules remains further work. It must exclude
later reset writes and preexisting buffered writes to W; a wake alone does not
establish these conditions. Publication of a separate payload before XCHG and a
blocking-mutex/acquisition contract are also not claimed here.

## Exact artifact and native evidence

`edsl-certify-futex wait INPUT CERTIFICATE.lean` and the `wake-one` profile accept
exact raw bytes. `--elf` binds literal entire ELF bytes to checked parsing,
loading and the entry code window. WAIT's 13 bytes retire three instructions
through entry and four including RET; WAKE1's 18 bytes retire four/five. The
standalone certificate proves exact request invocation and conditional current-
RAM RET behavior, including full RAX and RSP+8. Current executable code, eight
readable stack bytes and a canonical return target are explicit return premises.
It is a caller-supplied-stack function contract, not process startup, a service
completion certificate or a kernel proof. `Futex.Stubs.exact_stub_request`
connects its independent request specification to the service classifier.

`scripts/verify-futex.sh` certifies raw and full-ELF owned assembly outputs,
compares the same stubs in final native executables, and checks full raw
mismatch, empty-wake, misalignment and unreadable-WAIT results using an external
assembly register trampoline. Native EINVAL/EFAULT cases are observations;
isolated bad-input service profiles are not implemented. Aligned unmapped WAKE
is not classified as EFAULT. Unsupported/count/continuation/truncation and ELF
mutations are rejected, not run as blocking native mutants.

The threaded observer uses an attempt handshake, never sleeps as evidence of
queue membership. A positive wake count while W stays zero is recorded separately
in `queued-wake-observation.txt`. A bounded inconclusive race may pass the
sequential checks while recording `inconclusive`; it supplies no positive wake,
progress or defect conclusion. A watchdog expiry is explicitly inconclusive.

Lean tests exercise actual syscall capture, delayed current-word comparison,
either of two eligible wake choices, retry, spurious return, stale resume,
indefinite parking, ignored early wake, peer FIFO preservation/publication,
active cleanup rejection, exact resource collection and release/reuse rejection.
Synthetic admission cases reject upper-canonical addresses, incomplete interval
containment and executable W storage after actual SYSCALL decoding.

## Target boundary

The selected profile assumes coherent ordinary RAM, stable nonaliasing mappings,
managed lifetime, a fixed worker cohort and the declared Linux userspace interval.
Signals/restart, cancellation, timeouts, PI/robust/requeue/bitset/shared futexes,
dynamic workers, native VM interference and arbitrary kernel faults are outside
it. No kernel instruction cost, micro-operation minimum or elapsed-time bound
follows from user instruction accounting.

ABI/specification evidence comes from pinned Linux v6.12 primary sources:
[syscall table](https://github.com/torvalds/linux/blob/v6.12/arch/x86/entry/syscalls/syscall_64.tbl),
[futex UAPI](https://github.com/torvalds/linux/blob/v6.12/include/uapi/linux/futex.h),
[dispatch](https://github.com/torvalds/linux/blob/v6.12/kernel/futex/syscalls.c),
[key resolution](https://github.com/torvalds/linux/blob/v6.12/kernel/futex/core.c),
[compare/enqueue and wake](https://github.com/torvalds/linux/blob/v6.12/kernel/futex/waitwake.c),
and [errno constants](https://github.com/torvalds/linux/blob/v6.12/include/uapi/asm-generic/errno-base.h).
Reading those sources does not prove their implementation or the installed kernel.
