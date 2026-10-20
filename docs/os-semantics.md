# OS semantics: the environment is part of the theorem

Status: narrow implemented contracts plus requirements for the broader OS
domain. **Lean 4** contains a sequential address-space model, its machine-memory
bridge, an allocation-identity/ownership registry with shared read loans,
a managed read-worker instruction scheduler, shared atomic handles and mutable
MOV/XCHG/RET workers and counted locked-add workers with checked
OS-cell/lifecycle composition,
a separate mutex/protected-payload invariant protocol,
a restricted ELF loader,
a raw Linux exit60 contract and a bounded
stream-write/return contract. The general OS eDSL, runtime, broader concurrency and kernel
implementation proofs remain planned.
GNU C23, GNU C++26, LLVM IR and assembly are modeled domains rather than the
implementation language. The initial platform is Linux/x86-64; its assumptions
are specified in [the platform model](platform-model.md).

The [OS implementation track](os-implementation.md) extends this plan from
contracts to concrete kernel/runtime/driver machine code. C, Rust, assembly and
other implementation languages feed the same binary verifier. This can
incrementally replace contract assumptions with checked implementation results;
kernel execution additionally requires the privileged architecture profile.

## Current implemented slice

The [address-space contract](address-space.md) models byte-granular map, protect
and unmap operations with permission revocation and disjoint framing. Checked
ordinary machine stores project to the corresponding OS cell updates. This
does not yet model page-granular Linux syscalls, allocation failure or concurrent
mapping changes. The [ELF loader](elf.md) validates a restricted complete static
container and derives executable entry-byte binding from modeled installation;
Linux loader conformance remains external.

The [ownership layer](ownership.md) tracks principal authority, never-reused
allocation IDs and revoking transfer epochs over that same byte space. Checked
whole-allocation operations preserve valid disjoint live regions and full
mappedness; revocation persists through arbitrary finite managed histories,
including same-address reuse. Owned stores compose with actual store/RET bytes.
This is a sequential proof discipline, not raw-pointer generation checking,
authenticated identity, linear permissions or concurrent enforcement.

The [borrowing wrapper](borrowing.md) checks readable contained shared loans and
freezes their whole allocations against managed stores, protection, transfer and
release. Arbitrary finite guarded histories preserve each surviving loan's
exact record/cells/permissions and cannot revive a finished loan ID. Checked
reads compose with the actual load/RET bytes; independently established buffers
retain their contents under the same history conditions. These remain logical
sequential rules. Protected invariants, thread/scheduler identity, concurrent
adequacy, language provenance and allocator refinement remain ahead.

The [read-worker lifecycle](threads.md) now composes checked root-managed spawn,
actual per-instruction load/RET dispatch against current shared memory and join.
Each worker retains internal data/code/stack loans until its completed result
is collected. Arbitrary managed interleavings preserve the initial word result
and permanently revoke joined thread and loan IDs. Two successful selections
suffice under the supported instruction scheduler; an infinite idle trace
shows progress is not automatic. This is an abstract read-only lifecycle
contract. Native pthread/clone refinement, identity authentication, context
switching, locks and wider atomics remain required. Separate mutable exchange
and counted locked-add worker profiles are described below.
There is no new general SC or weak-memory claim.

The [atomic-exchange foundation](atomic-exchange.md) checks exact MOV/XCHG/RET
bytes, retains a singleton indivisible RMW event and projects the update to OS
cells. The [shared-handle wrapper](atomic-handles.md) delegates stored authority
to distinct actors and reserves their allocation against conflicting ordinary
operations. Well-formedness, permanent handle revocation and surviving read-loan
stability hold across admitted mixed histories. Exchange-only schedules prove
old/new chaining and multiset conservation; checked handles admit every
replacement word. The same-cell value-flow result excludes administrative gaps
where all handles close and ordinary writes become possible again. These are
logical managed contracts, with actor authentication, general memory ordering
and concrete runtime/kernel refinement still external.

The [mutable atomic-worker lifecycle](atomic-workers.md) now connects those
handles to checked root spawn, actual per-instruction MOV/XCHG/RET dispatch and
join. Each worker owns code/stack read loans and an atomic handle until join;
the old value is captured at its actual exchange and survives peer updates.
Every successful later join returns that event's old word across arbitrary
admitted mixed histories. Joined thread/handle/loan IDs stay revoked. Three own
selections suffice in a successful supplied instruction schedule, while idling
can continue forever. Dispatch-only schedules at one address have actual event
chaining and multiset conservation. The latter does not establish final-memory
chaining across mixed-history gaps without reservations. Native creation,
publication, scheduling and join remain external; locks and general ordering
are still required.

The [counted counter-worker lifecycle](counter-workers.md) now schedules an
exact JRCXZ/MOV/LOCK-XADD/LOOP/MOV/RET routine against current shared cells.
Full 64-bit RCX supplies each worker's independent iteration request. Each
successful selection executes one actual decoded instruction; a worker needs
exactly `3*count+3` own selections through completion and returns zero.
For every successful supplied dispatch schedule completing a finite admitted
entry-phase registry at one address, the final counter is the independently
observed initial word plus all published requests modulo 2^32. Checked full
collection returns zeros, removes all workers and revokes their handles/loans,
preserving counter cells. A constructive finite completion/collection path
exists for every such registry. Mixed histories retain resource/private-context
invariants, but this sum does not cover ordinary stores across unreserved gaps.
Native creation/publication/context switching/join, runtime cleanup and general
weak-memory refinement remain external; idling can prevent progress forever.

The separate [mutex protocol](mutex.md) now protects one payload word with a
distinct lock allocation, exclusive fresh guards and a local closed invariant.
Successful acquire and busy/reentrant attempts retain their actual XCHG events.
The holder may open the invariant while storing; release requires it to hold on
the current payload. Both allocations remain reserved while registered,
including unlocked intervals. Mixed histories preserve authority and permanent
guard revocation across re-registration, and a finite critical-section cycle
exists for every admitted unlocked state and invariant-satisfying final value.
Existing exact exchange/load/store bytes implement accepted operations. Guard
and invariant checks are logical admission; a complete native client worker,
publication/memory-order mapping, blocking/wakeup and runtime conformance remain
separate work. This wrapper does not silently merge with the atomic-worker model.

The [complete mutex worker replay](mutex-workers.md) now admits a fixed cohort
with checked code/stack loans. Each supplied dispatch proves one actual decoded
instruction against current shared cells and unchanged peer contexts, including
busy flag-dependent retries and temporary invariant opening. Generic worker
preservation and credit accounting prove modular +2 per worker, zero machine
returns and unlocked state for all successful completing supplied schedules.
No final-value check is a premise. The predicate must be closed under +2, and
the program invariant proves release admission. Exact own-step costs account
for real busy retries. Enabledness, constructive completion and arbitrary
machine-execution coverage remain next. Checked cohort collection closes
the retained loans without changing cells. Native identity and scheduling,
weak-memory adequacy, pthread/runtime and kernel remain outside the proof.

The [process slice](process-exit.md) checks a standalone twelve-byte entry that
sets exit status42 and requests raw Linux exit60. Its ABI request records the
userspace state before privileged execution: low 32 RAX bits select the syscall,
and arguments use RDI, RSI, RDX, R10, R8 and R9. The model does not execute
privileged syscall entry, model kernel registers or prove Linux implementation
behavior. The entry needs no caller return address, stack contents, startup
data or runtime, and its certificate admits every modeled initial register and
flags state.

The exit contract permits arbitrary waiting and a status-completion transition.
All completed traces agree on status42. Eventual completion separately requires
`LinuxExit.Fair`, an abstract progress assumption for completion; ordinary
scheduler fairness alone does not discharge it. Both an admitted infinite wait
and a terminating fair trace are proved. Resource closure and other kernel
cleanup remain outside the model. The process interpretation assumes one
thread and an unintercepted raw exit; multithreaded exit, `exit_group`, libc
wrappers, signals and competing termination events are not covered.

`edsl-certify-process` checks full observed ELF bytes through the modeled loader
and composes user execution with this explicit exit contract. The owned Clang
and GCC assembly fixtures are also executed natively to observe status42;
wrong-status and wrong-syscall mutations must be rejected. These runs provide
interface evidence, not a proof that Linux implements the abstract contract.

The [stream-write slice](process-write.md) adds bounded readable-buffer binding,
raw negative errno encoding, nondeterministic partial/error completion and
return to userspace with flags/RCX/R11 unconstrained. A full-file certificate
joins a write request to subsequent exit instructions for every admitted outcome.
Output is a prefix; complete output requires a full successful transfer, and
progress is conditional on write completion and the exit contract. The stable
stream has no concurrent writers or descriptor mutation; regular-file offsets,
direct I/O, devices, signals and durability remain outside this contract.

## What the OS contributes

A program's arithmetic can be correct while its result is wrong because a
worker was never joined, memory was freed too early, a write was partial, or a
signal interrupted cleanup. The OS domain gives these interactions a meaning
that survives every compiler and language boundary.

Some distinctions useful for reading the plan:

- A **process** owns an address space and resources such as file descriptors.
  Its **threads** share much of that state while each has its own registers,
  execution stack, thread-local storage, and scheduling state.
- **Virtual memory** is the address space seen by a process. Being mapped and
  accessible is separate from owning a live C/C++ object at that address.
- An **atomic operation** has specified indivisibility and ordering rules. A
  **lock** is a protocol that uses such operations and sometimes kernel waits
  to protect a larger invariant.
- The **kernel** mediates system calls. **libc**, pthreads, allocators, loaders,
  and language runtimes add userspace behavior around those calls. Their
  contracts need their own proof or an explicit trust assumption.
- **Safety** says a bad event never occurs. **Liveness** says something good
  eventually occurs. Returning the right count after join is different from
  proving join will eventually return.

The current proofs establish correctness relative to explicit OS contracts.
A proof of the Linux implementation is a further track. Linux's userspace
interface is documented by the [kernel uAPI guide](https://docs.kernel.org/userspace-api/index.html) and
the [Linux man-pages project](https://www.kernel.org/doc/man-pages/). Turning
that documentation into Lean definitions and validating those definitions is
project work; documentation alone is not a checked refinement proof.

## Semantic structure to implement

The proposed operational semantics relates a program step, its visible event,
and a new world. This is mathematical notation, not an existing API:

```text
Step(platform, program, world, event, program', world')
World = processes + threads + objects + mappings + handles + waits
      + memory-order state + pending events + environment state
```

The world is modular: a program that does no networking need not carry a TCP
implementation. Each used capability supplies a state space, permitted
transitions, invariants, and an explicit description of interference from the
environment. Composition must prove that one module cannot silently invalidate
another module's assumptions.

Represent thread IDs, handles, allocations, and synchronization objects with
semantic identities and generations, not just reused integer addresses. Track
which process owns a descriptor table, which open file description holds an
offset, and which mappings alias the same shared backing object. Source object
identities must relate to machine addresses through a separate representation
relation.

Visible events include input/output bytes and their accepted lengths, external
call/return, process/thread start and exit, allocation and revocation, blocking
and waking, delivery of a signal, and specified faults. Internal machine steps
can be silent. An observation policy decides which events a theorem exposes;
it cannot hide an externally visible failure merely to make equivalence hold.
Concurrency histories may additionally retain memory events used by the memory
model even when those events are not public I/O.

An operation that blocks spans invocation, an arbitrary waiting interval, and
completion or interruption. Do not model every syscall or library call as one
indivisible machine step. A proven linearization point may justify an abstract
atomic operation, but must be established for that implementation.

For each operation, require all of the following before marking it supported:

1. Typed inputs/results and exact success, failure, interruption, and partial
   completion cases, including raw syscall versus library error conventions.
2. Object/resource identity, required ownership or permission, creation,
   transfer, aliasing, and destruction obligations.
3. Preconditions for size, bounds, layout, alignment, initialization,
   protection, calling context, and platform capability.
4. A transition relation, externally visible effects, framing rule for
   unaffected resources, and permitted environment interference.
5. Memory-order and synchronization guarantees at language, runtime, kernel,
   and ISA boundaries, with no invented ordering edges.
6. Blocking, spurious return, timeout clock, cancellation, and restart behavior.
7. Cleanup obligations after every failure prefix; identify resources still
   live when an operation partially completes.
8. Separate safety, termination, fairness, and resource-bound statements.
9. A concrete native mapping and its Lean preservation theorem, or a named
   external contract assumption when implementation verification is pending.
10. Independent evidence against the actual interface: ABI inspection,
    executable integration scenarios, published specification cross-checks,
    and model/litmus checks where appropriate. Record versions and limitations.

## Memory and resource reasoning

Develop an ownership/separation discipline with an adequacy theorem connecting
its proof rules to the operational semantics. Permissions may be exclusive,
shared read-only, or controlled by a synchronization invariant. Ghost ownership
is proof state, not a hardware protection mechanism. Allocation uniqueness,
deallocation revocation, and splitting/recombining permissions need proofs.

Keep these levels separate:

| Level | Required state and obligations |
| --- | --- |
| Language object | Lifetime, type/layout, initialized bytes, array bounds, aliasing, provenance, effective-type/object-model rules for the chosen source fragment |
| Allocator | Ownership of returned region, requested versus usable size, alignment, overflow checks, failure, realloc invalidation and preservation, arena/thread interaction |
| Virtual mapping | Address interval, page size, permissions, backing object and offset, sharing/copy-on-write, guard pages, map/unmap/protect effects |
| Machine memory | Byte addressability, endian layout, supported atomic widths/alignment, ordinary write-back versus other memory types, permitted faults |
| Physical backing | Residency, overcommit, reclaim, NUMA placement and pinning only when relevant; these are not implied by successful allocation |

A non-null allocation does not establish all future access will complete in an
environment permitting OOM termination. Address reuse does not resurrect a
freed object. Mapping permission does not establish C/C++ pointer validity.
`MAP_SHARED` establishes a sharing mechanism, not an application-level
synchronization protocol. Linux documents mapping/protection distinctions and
anonymous mapping initialization in
[`mmap(2)`](https://man7.org/linux/man-pages/man2/mmap.2.html).

Start with bounded static objects; add successful/failed anonymous mapping and
an explicitly bounded allocator before arbitrary heap APIs. Stack and TLS
ownership must cover startup, callback entry, join, exception unwinding if
introduced, and destruction. Memory passed to the kernel stays live for every
interval in which that interface may use it; asynchronous I/O and DMA need
longer lifetimes than a synchronous call.

## Concurrency and weak memory

Sequential consistency (SC) means operations appear in a suitable single total
order. It is a useful first *language fragment*, but is not a blanket model of
x86 or C/C++ concurrency. Build the first concurrent interface from selected SC
atomic operations and create/join, then prove its lowering against the machine
memory model. The [x86-TSO research model](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf)
demonstrates behavior ordinary interleaving semantics excludes; it is a HOL4
formalization, not a ready-made Lean dependency.

The later memory model must track reads-from, per-location modification order,
program order, synchronization and happens-before, with the precise consistency
conditions of each pinned language/IR/ISA fragment. Source data-race freedom and
the treatment of undefined behavior need explicit theorems. Source, LLVM, and
machine-level orders are related by proofs, not by sharing enum names. Ordinary
x86 write-back memory, non-temporal accesses, MMIO, and device/DMA ordering need
different rules.

Include atomic load/store/exchange/fetch operations, compare-exchange success
and failure orders, spurious weak-CAS failure, fences, alignment and width,
initialization and destruction, synchronization scope, and lock-free
capability. A wide atomic implemented with a runtime lock must not satisfy a
requested lock-free contract. Arithmetic wraparound is distinct from lost
updates. Proving an integer counter result requires a bound preventing wrap,
or an explicitly modular result.

For synchronization libraries, prove preservation of protected invariants and
publication of data, not merely that a lock bit changes. Required cases include
ownership, reentrancy policy, lock order, reader/writer policy, try-lock results,
condition predicate rechecking, lost wakeups, spurious wakeups, destruction with
waiters, robust-owner death, and process-shared versus process-private state.
The futex compare-and-block contract is a building block; it does not turn
arbitrary data accesses into a correct mutex protocol. See
[`futex(2)`](https://man7.org/linux/man-pages/man2/futex.2.html) and the
[kernel robust-futex description](https://docs.kernel.org/locking/robust-futexes.html).

Do not use the [Linux Kernel Memory Model](https://docs.kernel.org/dev-tools/lkmm/index.html)
as the userspace C/C++ memory model. It specifies kernel concurrency constructs.
Even the [kernel memory-barrier guide](https://docs.kernel.org/core-api/wrappers/memory-barriers.html)
explicitly limits its own authority. `volatile`, a foreign call, or entering the
kernel is not a substitute for the synchronization theorem required by an
application.

## Scheduling, progress, and time

Model safety under every permitted scheduling and memory behavior, including
preemption between instructions and arbitrary delays. Model interruption of
long-running external operations through their contract. A scheduler that
never runs a worker is a legitimate counterexample to unconditional
termination unless the environment excludes it.

Each progress theorem states its assumptions separately:

- **Weak fairness:** an action that remains enabled eventually runs.
- **Strong fairness:** an action enabled repeatedly eventually runs. This is
  stronger and must not be silently assumed.
- **Environmental progress:** a peer sends data, storage completes a request,
  a lock holder releases its lock, or an admitted worker is eventually given
  sufficient execution steps. Scheduler fairness alone does not imply these.
- **Bounded response:** a numerical delay bound requires an explicit scheduler,
  interruption, resource, and timing model beyond eventual fairness.

Deadlock freedom does not imply starvation freedom. Lock freedom concerns
system-wide progress; wait freedom bounds an individual operation's own steps
under its defined model. Neither implies bounded wall-clock latency on Linux.
Affinity, priorities, real-time policies, CPU quotas, oversubscription, and NUMA
placement are separate capabilities. Do not promise any fairness property from
the name of a native lock or scheduler.

Clocks need identity and units, monotonicity/adjustment rules, wrap/overflow,
resolution, and relative versus absolute deadlines. A timeout can permit a
return without guaranteeing prompt CPU scheduling after its deadline. Signals,
deferred/asynchronous cancellation, timer delivery, and request cancellation
must identify interruption points and which resources remain owned.

## Coverage and priority matrix

The table lists requirements for the broader domain. The implemented
address-space, ELF and single-thread exit slices above cover parts of P0/P1;
the remaining breadth is planned. P0 establishes a small sequential platform
proof; P1 adds resource lifetime and basic concurrency; P2 builds production
interaction semantics; P3 is driven by concrete programs. An unused P3
capability need not block a theorem that explicitly excludes it.

| Priority | Domain | Requirements and representative proof obligations |
| --- | --- | --- |
| P0 | Process startup and exit | Static ELF entry, initial registers/stack/mappings, arguments/environment constraints, normal/fault exit, observable status; relate loaded bytes to checked bytes |
| P0 | Bounded computation and external output | Static object ownership, instruction safety, raw `write`/exit interface; output prefix, short write/error cases, no assumed terminal or disk delivery |
| P1 | Mapping and allocation | Anonymous map/unmap, zero initialization, non-overlap, page protection, allocation failure, cleanup, address reuse, bounded allocator correctness |
| P1 | Threads and TLS | Create/start/join/exit, publication, argument/result lifetime, stack/TLS ownership, failure after some workers started; detach introduced only with a reclamation protocol |
| P1 | Atomics | Selected aligned SC load/store/RMW first; ordering refinement, race freedom, non-wrapping result or modular contract, capability checks |
| P2 | Locks and waits | Mutexes, condition variables, futexes, semaphores, barriers, reader/writer locks; invariant transfer, no lost wakeups, spurious wake handling, owner death, priority inheritance |
| P2 | Weaker atomics and reclamation | Acquire/release, relaxed, fences, CAS, ABA, hazard/epoch/RCU-style lifetime when required; publication and reclamation proof, not stress-test inference |
| P2 | Signals and cancellation | Masks, pending/delivered events, handler frames/alternate stacks, async-signal-safe calls, `EINTR`/restart, cleanup handlers; never assume all signals are blockable |
| P2 | Files and descriptors | Open file descriptions, descriptor duplication/reuse, offsets, read/write partial completion, EOF, nonblocking behavior, append, close races, file locks, permission changes |
| P2 | Processes and IPC | Spawn/exec/wait, fork restrictions in multithreaded callers, inheritance and close-on-exec, pipes, shared mappings, descriptor transfer, process/thread exit distinction |
| P2 | Time and scheduling | Clock contracts, timers, affinity, policy/priority, resource limits, quotas; distinguish safety, fairness, eventual termination, and latency |
| P3 | Filesystem namespace and persistence | Paths, symbolic links and races, directory handles, rename/link/unlink, metadata, mount/filesystem configuration, crash states and flush ordering |
| P3 | Networking | Endpoint identities, stream versus datagram behavior, short send/receive, EOF, backpressure, shutdown, address resolution as an external service, peer/protocol assumptions |
| P3 | Async I/O and event loops | Readiness versus completion, request/buffer lifetime, `epoll`/`io_uring`-style queues, duplicate/late completions, cancellation races, reclamation |
| P3 | Security and ambient environment | Credentials, capabilities, namespaces, seccomp/LSM policy, working directory, locale, environment variables, resource exhaustion, external actors and permitted interference |
| P3 | Runtime and dynamic composition | libc/allocator/pthread versioned contracts, C++ initialization/exceptions/unwind/TLS destructors when used, dynamic loader, shared libraries, symbol interposition, FFI callback contracts |
| P3 | Devices and specialized memory | MMIO, DMA, IOMMU, coherent/noncoherent buffers, device commands, interrupts, memory types, persistence domains; device-specific refinement and barriers |
| P3 | Execution substrate | Hypervisor/emulator/WSL, CPU feature exposure, kernel configuration, firmware/microcode, debugger/ptrace restrictions; state which components are trusted |

Persistence needs a crash semantics distinct from ordinary successful I/O.
For example, `fsync` of a file does not itself establish the directory-entry
durability a protocol may need, as described in
[`fsync(2)`](https://man7.org/linux/man-pages/man2/fsync.2.html). Likewise a
descriptor's integer being closed is not a proof that another thread cannot
still hold an in-flight operation on its open file description; see
[`close(2)`](https://man7.org/linux/man-pages/man2/close.2.html).

## Implementation order and evidence gates

1. **Semantic foundation.** Define events, finite/infinite executions,
   outcomes, explicit faults, nondeterminism, world invariants, and framing in
   Lean. Prove the basic proof rules sound against transitions. Check examples
   with genuine alternative outcomes so the model cannot exclude bad behavior
   by construction.
2. **First platform slice.** The standalone static exit42 entry is implemented
   with exact ELF binding and a conditional OS progress theorem. Extend it to
   a bounded single-thread computation with startup data and richer control flow.
   One static stream write now has an output-prefix/error theorem for arbitrary
   admitted returns and exact output on the separate full-transfer path.
   `write` may be partial or fail; its return
   value is not delivery to a human or persistent storage
   ([`write(2)`](https://man7.org/linux/man-pages/man2/write.2.html)). No
   unproved source-to-binary edge may be labelled verified.
3. **Memory resources.** Add map/unmap and a bounded allocator, proving lifetime
   and cleanup for success/failure. Exercise the actual native boundary,
   including fault/protection cases in isolated child processes. OS resource
   failure remains a modeled outcome, not a contradiction.
4. **Threads plus SC atomics.** The abstract counted-worker program now proves
   its modular result and checked collection for every successful completing
   supplied dispatch schedule, with constructive finite completion separate
   from arbitrary scheduler progress. Next choose a pinned pthread runtime as
   an explicit external contract; verify the project's wrapper and ABI,
   including publication and native failure/cleanup. Add concrete memory-model
   correspondence and a separate no-overflow theorem for natural-number totals.
   Partial creation failure needs its own whole-program cleanup theorem.
   Termination additionally requires worker scheduling and runtime progress.
5. **Publication and waits.** A first checked mutex/payload-invariant protocol
   now exists with exact operation bridges; native client and memory-order
   correspondence remain unproved. Add acquire/release message passing and a
   condition-wait/futex protocol. Require forbidden-outcome proofs, a
   memory-model mapping theorem, and real contention/wakeup integration cases.
   Test assertions and model oracles must be stated independently of emitted
   source and lowering code.
6. **Broader modules.** Add domains only with all per-operation obligations and
   a program demonstrating why they are needed. Add persistence, devices,
   advanced reclamation, and stronger progress claims as separate proof tracks.

The native pthread contracts used at step 4 must cover start timing and
joinability ([`pthread_create(3)`](https://man7.org/linux/man-pages/man3/pthread_create.3.html))
and the completed-thread resource lifecycle
([`pthread_join(3)`](https://man7.org/linux/man-pages/man3/pthread_join.3.html)).
Thread creation returning successfully is not a scheduling order guarantee.
Signal behavior is a separate environment module, documented by
[`signal(7)`](https://man7.org/linux/man-pages/man7/signal.7.html).

Each gate needs both checked proofs about the model and evidence that the
selected native interface matches that model. Stress tests, litmus executions,
sanitizers, disassembly, and model exploration can find mistakes, but cannot
replace a missing universal theorem. A deterministic test scheduler is useful
only if it does not remove the scheduling behavior the theorem is supposed to
cover.

## Shortcuts that would invalidate the goal

- Assuming allocation, thread creation, blocking I/O, or joining always succeeds.
- Proving the intended source result while trusting an unnamed compiler,
  assembler, linker, loader, runtime, or foreign function along the path.
- Treating all shared-memory operations as SC, or all syscalls as full barriers.
- Ignoring uninitialized bytes, provenance, address reuse, signals, cancellation,
  or failure cleanup because the happy-path demo did not exercise them.
- Using total-correctness wording for a safety/partial-correctness theorem, or
  silently assuming fair scheduling or cooperating peers.
- Treating a contract assumption about Linux as a proof of Linux, or treating a
  proof of an ISA model as proof that physical hardware obeys that model.
- Inferring operation-count, wall-clock, persistence, or side-channel guarantees
  from functional correctness; each needs its own semantics and theorem.

For reusable concurrent ownership proofs, evaluate
[Iris-Lean](https://github.com/leanprover-community/iris-lean) before inventing a
new logic. It already provides a Lean 4 Iris port with proof tooling and an
example language. A proof for its example language does not automatically
apply to C/C++, LLVM, Linux, or x86: the instantiated language semantics,
adequacy theorem, and refinement connections remain required project work.
