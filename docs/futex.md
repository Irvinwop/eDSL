# Private futex service and exact clients

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
`Runtime.Invariant` alone does not assert payload authority for every queued
store, a live keeper in a call-free state, or a complete per-worker client
control/loan contract. The separate current client admission below supplies
those obligations and derives positive coverage for its fixed code profiles.

`Publication` proves current-word mismatch, sole-waiter wake, absence of wake
credits and spurious-word framing. The owned examples exhibit both comparison
orders and retry across actual XCHG publication. A generalized no-lost-wakeup
proof over all physical client schedules and a blocking-mutex/acquisition
contract remain further work. A wake alone establishes neither publication nor
an acquisition right.

## Preserved client admission and physical coverage

`Clients.Admitted` covers a fixed cohort of exact WAIT clients, publishers and
separate ordinary payload writers. A publisher executes
`STORE [P],0x11223344; XCHG [W],1; WAKE_PRIVATE(1); RET`, including its intervening
MOV instructions. A peer writes `0x55667788` to its own separately granted word
and may return with that store still buffered. WAIT retains an arbitrary
zero-extended expected32. The actual decoder chooses instructions throughout.

Admission records current finite control, complete physical/resource RAM
equality, fixed keeper/producer handles, current ordinary-write grants, exact
executable code, and read loans for each code window and all eight return-stack
bytes. Each actual FIFO entry has current authority, including entries owned by
returned producers. Code and the current private context derive authorization
at STORE enqueue. The fixed handles precede a resource-handle frontier; fresh
call pins remain at or above it, independently of the invocation-ID frontier.
Admission contains no promise of future replay, service completion or return.
`Examples.FutexClient.initial_admitted` constructs a nonempty four-client witness
through checked adoption, loans and handle issuance.

`issue_lift` and `drain_lift` prove that every successful actual `Suspend`
issue/drain has an enabled managed transition with identical suspended output
and observation, preserving admission. `MachineTrace.lift` extends this to any
finite actual issue/drain prefix without assuming a successful managed trace.
`demand_enabled` and `extend_prefix` additionally enable current typed service
phase/queue choices after an admitted prefix. These theorems derive replay and
capture success from current resources; they add no expected-opcode execution
gate and require no empty peer FIFO.

`ready_ret_enabled` starts with an actual typed ready call and derives both
resumption and the subsequent decoded RET. It retains the full raw RAX result,
arbitrary full flags/RCX/R11, the client's protected target and RSP+8, present
RAM, and all peer worker/pending records. A call becoming ready, scheduler
fairness and eventual return are separate obligations.

`publisher_exchange_publishes_payload` uses actual XCHG retirement, own FIFO
emptiness and concrete STORE/FIFO control to establish current P=`0x11223344`
before and after the exchange and W=1 afterward. Peer payload separation follows
from the explicit static contract, derived from checked distinct allocation
tickets in the witness. `published_word_trace` retains W=1 across every later
admitted mixed prefix: actual code writes only one atomically, all FIFO heads
have grants disjoint from W, and service actions leave RAM unchanged. This
includes preexisting FIFOs and returned producers. It is a safety and
publication result, not a complete no-lost-wake or acquisition theorem.

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

`edsl-certify-futex-client publish-payload-wake INPUT CERTIFICATE.lean` is a
separate exact 32-byte profile for the publisher above. Raw and `--elf` outputs
contain literal artifact bytes checked by the Lean kernel. Its specification
binds the bytes to the selected publisher's current code and consumes current
admission, positive issue/drain/service lifts, same-member XCHG publication and
typed protected RET. `Specification.lift_prefix` retains that artifact binding
and contract after an actual finite issue/drain prefix; its managed trace is a
conclusion. `Specification.published_word_trace` exposes the later W=1 safety
theorem. The generated semantic theorem is conditional on current admission,
membership and code binding; the CLI does not construct an admitted runtime
from a file. The ELF form also requires agreement with current RAM and that same
client's entry.
The WAIT/WAKE1 invocation certifier retains its original, narrower meaning.

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

`scripts/verify-futex-clients.sh` assembles the publisher with Clang/GCC, compares
the same 32 bytes extracted after native linking, and certifies raw bytes and a
full standalone ELF. An external register trampoline invokes those bytes. The
observer checks P/W and full raw empty-WAKE results, plus 32 bounded WAIT/WAKE
races with actual joins. Its attempt handshake does not establish queue
membership; watchdog or scheduling bounds are inconclusive. Synthetic wrong
destinations, values, counts, RETs, truncations and invocation-only artifacts are
rejected without executing them. Certificates, hashes, build commands and
observations are stored under `artifacts/futex-client-fixtures/`.

## Target boundary

The selected profile assumes coherent ordinary RAM, stable nonaliasing mappings,
managed lifetime, a fixed worker cohort and the declared Linux userspace interval.
Signals/restart, cancellation, timeouts, PI/robust/requeue/bitset/shared futexes,
dynamic workers, native VM interference and arbitrary kernel faults are outside
it. Neither whole Linux kernel nor distribution safety is proved. Native
trampoline/pthread/kernel conformance remains external evidence, and no
scheduling progress, kernel instruction cost, micro-operation minimum or
elapsed-time bound follows from user instruction accounting.

ABI/specification evidence comes from pinned Linux v6.12 primary sources:
[syscall table](https://github.com/torvalds/linux/blob/v6.12/arch/x86/entry/syscalls/syscall_64.tbl),
[futex UAPI](https://github.com/torvalds/linux/blob/v6.12/include/uapi/linux/futex.h),
[dispatch](https://github.com/torvalds/linux/blob/v6.12/kernel/futex/syscalls.c),
[key resolution](https://github.com/torvalds/linux/blob/v6.12/kernel/futex/core.c),
[compare/enqueue and wake](https://github.com/torvalds/linux/blob/v6.12/kernel/futex/waitwake.c),
and [errno constants](https://github.com/torvalds/linux/blob/v6.12/include/uapi/asm-generic/errno-base.h).
Reading those sources does not prove their implementation or the installed kernel.
