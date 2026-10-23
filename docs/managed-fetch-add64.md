# Managed full64 scheduling and histories

`OS.TSO64` connects actual instruction decoding to current managed memory,
private thread contexts and mixed-width FIFO publication. `OS.TSO64History`
projects successful schedules to checked OS operations and an independent
modulo-2^64 counter relation. Their separate
[concurrent certificate composition](concurrent-fetch-add-certificates.md)
covers the frozen fetch-add function for both compilers. See the
[current coverage](coverage.md) for the complete corpus measurement.

## Execution and authority

A state contains one current `Atomics64` world and a list of workers. Each
worker retains registers, RIP, flags, phase, its original code/caller leases,
ordinary ownership tickets, atomic handles and a private pending FIFO. Scheduler
`tid` is the worker-list index; the OS actor is a separate resource identity.
Two contexts may have the same actor without becoming the same protocol thread.

`step` admits `issue tid af` and `drain tid`. Issue rebuilds local memory from
current published RAM and the issuing worker's newest matching pending bytes.
Current code-loan fetch and production decoders select the instruction. Ordinary
execution delegates to `Sequential`; full64 LOCK XADD delegates to `LockedAdd64`
and the checked current OS fetch-add bridge. Dispatch has no expected-PC table.

Ordinary Bool-choice scalar/control execution, loads and RET commit private
registers/RIP/flags. Legacy DWORD atomics, syscalls and vector-only independent
flag effects remain excluded. Branches retain the original code loan; a later
fetch rechecks its destination against that loan.
A store enqueues exactly its actual prestate address, tagged width, value and
original ticket. Drain rechecks current authority and publishes the FIFO head
through a real checked OS mutation. It leaves the CPU context unchanged and
refines `StoreBuffer.Mixed.publishOldest` on the erased payload.

A nonempty own FIFO makes LOCK XADD return `.blocked` with the entire state
unchanged. Peer FIFOs may remain nonempty. Once enabled, the current joint
OS/machine effect retains the actual decoded source input, full old response,
ADD flags, RIP advance and one RMW8 event. A zero input still performs a fully
authorized eight-byte operation. Blocked attempts and drains retire zero
instructions; ordinary instructions, RMW and RET retire one in this model.

Forwarding supplies bytes, while current ownership and permissions authorize
access. The supported ordinary data profile requires naturally aligned,
non-crossing full-RW ordinary RAM, current grants/epochs, and exclusion of
ordinary read loans and both atomic reservation modes. Read-only data-loan
loads, other widths and unsupported instruction forms fail closed.

Resource identities, permissions, loans, handle registries and grant lists stay
fixed during an issue/drain run. Shared RAM evolves through publication and
RMW. External release, protection, transfer, registration and loan-lifetime
changes need separate transition rules and preservation proofs.

## Return and publication

RET uses the original caller slot, current original loan, actual RSP and actual
memory. Changing RSP creates no replacement-slot authority. Original loan
retention does not imply that RET is enabled at a changed RSP.

A returned worker may still have buffered stores. `collect` requires returned
phase and an empty own FIFO, then reads RAX. It releases no loans, tickets or
handles. `publish_worker` derives a finite own-drain suffix from the current
well-formed state and retained grants; it supplies neither scheduler fairness
nor eventual whole-program completion.

## Independent arithmetic and event origins

`AtomicFetchAddHistory64.Step` records actual checked OS fetch-add, checked
mutation, or an unchanged world. It retains the typed event's actor, handle,
persistent cell and actual input. Allocation reservation and ownership frames
derive unchanged selected-cell reads for unrelated operations. Desired target
values and assumed successor invariants are absent from admission.

`TSO64History.step_history` and `schedule_history` project every actual scheduler
action, including quiet issue/RET/block/drain positions and other-cell updates.
`schedule_sequential` derives `ModuloCounter.Sequential`; `schedule_retained`
derives persistent descriptor, full-eight-byte validity and reservation at the
endpoint. `step_event_origin` retains the actual issuing context, decoded
instruction, current prestate operands and joint machine/OS effect.

The OS history's event-to-ID label functions are sequential client names.
Equal zero-update events may receive equal labels. Complete-call protocols
require distinct occurrence labels and invocation/point/response origins from
the same actual execution.

## Invocation boundaries

`Concurrency.CallTrace` supplies actual-step replay, client emission origins,
exact indexed event boundaries and complete logical protocols. Its generic
`Invocations` extension checks a client-supplied present-state predicate for
every invocation, including invokes inside an execute emission. It preserves
the original replay result and exposes an executable exact earlier prefix.
All events in one execute emission share that entry's prestate; list offsets
create no additional machine transitions.

A concrete ABI client must prove what its gate establishes about entry RIP,
arguments, current code bytes and original caller resources. Generic gate
acceptance itself supplies none of those interpretations. Complete-call
arithmetic and actual RET responses need a concrete client. A checker conditional
on accepted labels does not establish that every admissible execution of a
particular function accepts.

## Finite complete-call client

`OS.FetchAddCalls64` instantiates the generic adapter with actual scheduler
steps and a selected persistent cell. Its checked state carries current
well-formedness and liveness; successor facts follow from the actual step.
An RMW mark supplies an occurrence ID. Input, full old response and scheduler
thread come from the real decoded operation, with the resource actor retained
separately. Quiet annotations cannot hide a selected-cell update, including zero.

A response mark must match an actual RET and its complete RAX. `returned_origin`
derives current original-slot authority, actual RSP, local/current memory reads,
real RET execution and the installed returned context. Pending stores remain.
`point_at` and `response_at` expose the exact earlier entry prefixes and actual
schedules for the selected interval positions.

`checked_complete` runs actual replay and the logical protocol check, then
derives the OS history, final selected-cell read, `ModuloCounter.LegalHistory`,
real-time linearization, interval boundaries and modular fold/total. Arithmetic
is a consequence of actual OS operations, not another admission gate. Identical
zero events can have distinct supplied IDs for different scheduler contexts.

Invocation labels in this client are environmental. The next layer adds current
entry facts; universal body/argument proofs, accepted-completion proofs and exact
frozen-file binding remain necessary for a frozen function certificate. Response
at RET also establishes no resource release or completed publication.

## Present scalar-entry admission

`OS.FetchAddABI64` supplies the concrete gate for a cell-pointer and full64 delta
in RDI/RSI. Its image parameter supplies an entry and complete declared bytes.
The gate checks actual entry RIP, running phase, empty own FIFO, selected-cell
pointer, delta, original caller RSP, every executable image byte and complete
containment in the original code loan. Current selected-handle authority and
the canonical original-slot return target are checked in the same state.

Represented scalar-entry checks include a nonwrapping/canonical post-RSP,
`(RSP + 8) mod 16 = 0` and clear DF. The
[x86-64 psABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex)
defines the calling-convention requirements; SIMD/x87 and other unrepresented
state remain external. Fresh checked caller-slot fixtures exercise the proper
entry alignment and reject a readable but misaligned original slot.

`gate_sound` derives `EntryFacts` from those current checks and well-formed
resources. Gated replay reuses `CallTrace.Invocations` and the real call adapter;
`checked_complete` preserves the same original result and independent legal
history. Every interval obtains entry facts at its exact executable invocation
prefix, together with actual indexed RMW and RET origins.

These are present admission and conditional finite-history guarantees. The
image parameter itself does not identify a frozen ELF function. The separate
body checker below supplies universal behavior; composing it with this gate
and complete-call histories remains an integration obligation.

## Shared atomic-method checker

`X86.VCGen.AtomicMethods` checks complete finite instruction windows against the
production decoders. Its family admits padding (including CET-off ENDBR64), a
full64 argument copy, LOCK XADD and RET. Relative cutpoints are proof data;
execution still uses the ordinary managed scheduler and existing ISA semantics.
`Corpus.V1.FetchAddBodies` instantiates the same proof for both unchanged frozen
compiler byte sequences.

`all_completed_origin` covers every admitted register file and current resource
state, every successful finite interleaving, and every completed own outcome.
It derives exactly one own typed RMW, the original delta, actual current old
word returned at RET, and the event's exact prefix and suffix in that schedule.
Peer updates may change the selected cell between invocation and the RMW. The
proof retains original code/caller authority, empty own FIFO, register/stack
frames and nonarithmetic flags, including DF. Returning methods explicitly
exclude RSP as the locked source; the raw locked instruction rule supports it.

Current enabledness and a decreasing instruction count derive bounded own
completion. GCC uses four modeled retired instructions including ENDBR64;
Clang uses three. Enough successful own issues also imply return under arbitrary
successful peer interleavings. These counts establish neither scheduler fairness
nor a hardware or algorithmic minimum.

The frozen body's invocation base remains a parameter. Whole-file identity
and universal byte-sequence behavior do not by themselves install the function
at its real ELF address. Actual-address checked resources, complete-call/ABI
composition, two-context nonvacuity and registry acceptance remain necessary
before corpus credit. The [concurrent certificate layer](concurrent-fetch-add-certificates.md)
now supplies these obligations for both frozen windows using one generic batch
proof. Its independent contract quantifies arbitrary admitted populations and
inputs; its useful loaded witness separately proves actual overlapping calls.

## Validation and target scope

The scheduler suites check real two-context interleavings, full64 carry/wrap and
peer responses, own blocking, mixed-width forwarding/FIFO publication, current
RAM after peer drains, aliases/source RSP and actual authority denials. A further
regression combines an own pending DWORD, a later peer QWORD publication and an
actual load: the result merges own low bytes with current peer high bytes. RET
retains the pending obligation until publication enables collection.

`bash scripts/verify-locked-add64-native.sh` captures 3,072 owned CPU executions
across every source GPR, twelve direct bases, ignored REX.X, full64 boundary
values and aliases, including RSP as source. Actual CPU flags are compared with
the existing `LockedAdd64.step` alongside all GPRs, memory and event frames.
Four corrupted captures must fail their semantic gates; altered extracted code
must fail before execution. Evidence under `artifacts/locked-add64-native/`
records sources, compiler/CPU, outcomes and closed checksums. This is finite
runtime conformance evidence; it adds no universal hardware theorem or corpus
credit.

`lake build ManagedFetchAdd64Tests` builds shared fixture and test dependencies
through Lake's source/dependency traces. CI caches test proof outputs separately
from production outputs and explicitly audits their imported declarations.
Production fresh-kernel replay remains a separate check.

The profile inherits abstract long mode, CET/IBT/shadow-stack-disabled execution,
coherent WB RAM, stable translation/permissions and suitable physical backing
and aliases. Published x86-TSO refinement, physical LOCK behavior, native Linux
thread/resource enforcement, GNU source atomic orders, scheduler fairness and
hardware operation lower bounds require further proofs or stated platform
contracts. The closed managed batch does have a proved finite global completion
schedule and bounded own progress; those do not establish fairness or liveness
for an arbitrary native scheduler.
