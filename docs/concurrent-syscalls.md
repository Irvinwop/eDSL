# Concurrent syscall boundaries

`EDSL.OS.Suspend` adds pending syscall invocations to the supported `OS.TSO`
scheduler. It executes actual shared instruction bytes and preserves peer
memory changes across a suspended caller's return. This is a service-neutral
mechanism: an external completion chooses the raw return value. It does not
specify Linux read, futex, signals, privileged entry/return, or kernel behavior.

The existing `OS.TSO` scheduler still stops at `syscallBoundary`. Existing
synchronous process proofs retain their original `X86.Returns` contract and
no-interference assumptions. The new wrapper and `X86.ReturnsAt` are separate
interfaces.

## Execution and lifecycle

A wrapper state contains the current TSO machine, a monotonically increasing
invocation frontier and a pending map indexed by immutable worker index. Each
saved record contains its unique invocation ID, worker index and the complete
request produced by actual SYSCALL execution. Its user memory is an entry
snapshot, not the memory to install at return.

A live unreturned worker without a pending call fetches and decodes shared
executable bytes. Ordinary instructions execute the existing `TSO.execute`;
`IssueEffect.machine` proves the exact corresponding `TSO.issue` result. An
actual decoded SYSCALL captures its request and `RIP+2` continuation and records
one fresh pending invocation. Entry retains the machine state, including every
context, return marker, queue and memory byte. While the invocation is pending,
selecting that worker produces a parked observation and leaves the entire
wrapper state unchanged. Peers and independent FIFO drains can still run.

This first syscall profile requires an empty **caller** FIFO. A nonempty caller
FIFO produces `pendingStores`; the model neither flushes nor discards it. Peer
FIFOs may remain nonempty. This is an explicit supported-profile condition, not
an assertion that a physical SYSCALL flushes stores. The existing ordinary-RAM,
alignment, stable-permission, no-alias and fixed-code limitations of
[buffered execution](store-buffers.md) still apply.

A resume action supplies the worker index, exact current invocation ID, raw
64-bit result, flags, RCX and R11. It supplies no memory or replacement request.
The scheduler checks the actual live unreturned caller, pending record, matching
ID, record owner and empty own FIFO. It then installs a return context against
**current shared RAM**, retains every peer worker and FIFO, and removes the
pending record. The allocation frontier is unchanged. Missing workers,
already-returned callers, absent pending records, stale IDs, wrong owners and
unsupported own queues are explicit failures. Each failed attempt returns an
error rather than an updated state.

Only an actual RET sets a returned marker. Entering, parking and resuming are
distinct from RET. A return marker does not imply publication of unrelated
ordinary stores; `Finished` retains the underlying TSO quiescence requirement.

## Return and prefix contracts

`ReturnsAt request current raw after` specifies the exact saved continuation,
full RAX result, equality of the entire output memory to `current`, and all
saved entry registers except RAX, RCX and R11. Flags, RCX and R11 are explicit
unconstrained choices. `resumeAt` constructs every admitted complete return
state; its characterization retains every flag and register field. When
`current` is entry memory, this contract is equivalent to the existing
`Returns`, and the old `resume` is unchanged.

`WellFormed` contains only current facts: checked FIFOs, pending worker
existence, unreturned status, empty own queue, complete saved/current private
context equality, correct owner/index, allocated invocation IDs and unique
pending IDs. It does not equate historical entry RAM with current RAM, assume
a future successful return, or require a desired endpoint. It survives every
successful issue, drain, resume and trace prefix.

`prefix_safety` retains this invariant, the complete memory frame and the exact
allocation frontier. `MemoryFrame` preserves permissions, mapped-byte domain
and executable bytes; it permits peer data contents to change. Arbitrary code
images retain their exact byte binding through successful prefixes and resume.
Actual entry evidence binds the saved snapshot to entry RAM, so preservation
of an entry image is derived through the intervening trace.

`consumed_identity_never_resumes` proves that no future successful trace can
revive a completed invocation, even on another worker. The proof follows actual
pending-record origins and the monotone allocation frontier. It does not assume
that future completions reject a guessed stale ID. A later syscall receives a
new ID.

`resume_available` constructs a completion for every pending valid caller and
every permitted raw result and private clobber choice. This establishes that
the mechanism has an available completion, not that a service completes or
chooses any particular result. `parked_forever` constructs a genuine infinite
parked trace. The scheduler also has explicit idle actions. Neither fairness
nor eventual service progress is hidden in these interfaces. Well-formedness
alone does not establish enabled execution of arbitrary runnable code: real
instruction fetch, memory faults and unsupported instructions remain possible.

## Costs and evidence

An entered invocation retires its actual SYSCALL exactly once. Resumption,
parked selections, idle, locked stalls and store drains retire no user
instructions. Other retirements and atomic events are the underlying actual
TSO observations. `schedule_call_count` equates allocation-frontier growth with
actual entry observations; `schedule_action_count` distinguishes all action
categories. These are model instruction/action counts, not kernel work,
micro-operations, elapsed time or a service-cost bound.

`Examples.Suspend` and `tests/Suspend.lean` execute owned request/RET bytes and
peer XCHG/store bytes. Their independent observations cover a peer update
between entry and return, arbitrary full-width results and permitted private
clobbers, saved continuation/stack behavior, parked selection, peer FIFO
retention, and publication before or after resume. They also check stale and
double completion, a new invocation after resumption, unsupported caller queues
and precise second-byte fetch failures. Universal frame and lifecycle theorems
supply full-state guarantees alongside concrete observable checks.

No new native artifact profile or Linux service certificate is introduced here.
The existing compiler/native integrations remain separate evidence for their
existing profiles. These scheduler proofs do not prove a native context switch,
thread identity, Linux memory-order conformance or the installed kernel.

The generic wrapper does not carry an ownership or borrowing world and does
not authenticate arbitrary peer stores against one. Existing mutex/resource
proofs retain their own contracts. Composing a service with live resource pins,
mutable wait words, code/stack loans and authorized peer effects requires an
explicit service/resource relation. Private futex wait/wake, queue admission,
spurious completion, signals/restart, timeouts, cancellation and kernel
linearization remain further work.
