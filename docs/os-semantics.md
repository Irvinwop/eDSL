# OS semantics and coverage map

The OS eDSL is a primary domain spanning all language and machine-code paths.
Everything in this document is planned coverage, not an implemented API.
The initial target is Linux/x86-64. The scope is broad; implementation proceeds
through small executable slices with documented contracts.

## Required domains

| Area | Operations and properties to represent |
| --- | --- |
| Threads | Creation, join/detach, exit, result publication, thread-local storage, identity, stack ownership, failure, and cancellation policy |
| Scheduling and CPU placement | Affinity, topology, priorities, scheduler policies, yielding, NUMA placement, and explicit progress assumptions |
| Locks and waits | Mutexes, reader/writer locks, condition variables, semaphores, barriers, events, futex-style wait/wake, ownership, recursion, and process sharing |
| Atomicity and ordering | Load/store, exchange, read-modify-write, compare/exchange, fences, ordering, synchronization scope, alignment, supported widths, and lock-free requirements |
| Allocated memory | Allocation/deallocation, arenas, alignment, initialization, ownership, borrowing, sharing, lifetime, aliasing, bounds, and allocation failure |
| Virtual and shared memory | Mapping/unmapping, permissions, guard pages, protection changes, shared/file-backed mappings, page size, residency, huge pages, and persistence requirements |
| Processes and IPC | Spawn/exec, fork restrictions, wait, exit, inherited resources, pipes, shared memory, sockets, and descriptor/handle transfer |
| Files and filesystem | Open/close, offsets, positional I/O, metadata, directories, mapping, locking, durability, and atomicity of individual operations |
| Networking | Endpoints, connect/accept, send/receive, buffering, backpressure, shutdown, and connection ownership |
| Asynchronous I/O | Readiness/completion, event loops, request lifetime, cancellation, timeout, and resource reclamation |
| Time and signals | Clock identity, monotonic vs wall time, deadlines, timer lifetimes, signal delivery/masking, interruption, and signal-handler restrictions |
| Execution environment | Arguments, environment, working directory, dynamic libraries, resource limits, credentials, permissions, and platform capabilities |
| Device interaction | Explicit address spaces, MMIO, device access, DMA/coherency contracts, and target-specific barriers when required by a program |

## Contract for every operation

Every proposed OS operation needs a short specification covering:

1. Inputs, outputs, resource identity, ownership transfer, and lifetime.
2. Preconditions: alignment, access permissions, target support, and context
   restrictions such as thread affinity or signal safety.
3. Observable effects, synchronization edges, and ordering guarantees.
4. Blocking, progress, fairness, wakeup, deadline, and cancellation behavior.
5. Failure paths, interruption, partial completion, and cleanup obligations.
6. The native mapping for each supported backend/OS/ABI combination.
7. Independent evidence that the mapping preserves the specified behavior.

Lock-free and wait-free requirements must be explicit capabilities, not inferred
from API names. Synchronization scope must distinguish threads within a process,
processes sharing a mapping, and device interactions where supported.

## First executable slice

The first implementation should describe and execute this workload:

1. Allocate shared state with an explicit owner and lifetime.
2. Start workers that update an atomic counter.
3. Join every worker and observe the final count.
4. Release the state only after all workers have stopped using it.
5. Report thread-creation and allocation failures and clean up any resources
   already created.

The arithmetic outcome follows from the number of completed increments, not
from the emitted source text. This checks resource lifetime, thread lifecycle,
atomic update preservation, and interoperability. It does not establish all
memory-ordering properties. Add separate publication and wait/wake scenarios
with defined synchronization, plus appropriate model or litmus validation.

## Verification priorities

Reject invalid memory-order combinations, unsupported atomic widths/alignment,
unavailable target capabilities, and known resource misuse with useful
diagnostics. Treat dynamic lifetime and aliasing obligations as runtime or
caller contracts wherever static checking cannot establish them.

Use real threads, native waits, and real mappings for integration coverage of
those behaviors. Tests should cover contention, publication, cleanup after
partial failure, spurious wakeups where permitted, and timeout/interruption
paths. A passing stress test alone does not prove a memory-model mapping.

Compare generated executions against independently stated outcomes and native
reference behavior. Inspect IR, assembly, and ABI details where an executable
test cannot establish a required property. Record the target and toolchain
versions used for those checks.
