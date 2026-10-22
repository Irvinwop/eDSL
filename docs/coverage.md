# Implemented coverage and remaining trust

This is the capability index for eDieSeL's implemented verification profiles.
Use [implementation status](implementation-status.md) for the current
**18/40-function, 36/80-artifact** validated conditional frozen-corpus total,
including **three distinct managed concurrent functions**; **22 functions /
44 artifacts** remain. Other callable fixtures and model proofs remain useful
without adding corpus coverage. The latest
[managed plain64 measurement](../corpus/measurements/managed-plain64-v1/)
records the accepted source and full-gate evidence.

Every entry below has a restricted contract. Follow its reference for exact
encodings, APIs, hypotheses and rejection behavior; instruction support is not
shared automatically between execution engines. The [trust boundary](trust.md)
collects environmental assumptions and evidence distinctions.

## Supported machine profile

The common physical interpretation is x86-64 long-mode userspace, flat
addressing and 48-bit canonical addresses, with valid control state, alignment
checking and CET disabled, no single-step/breakpoint interference and no
asynchronous state changes outside the admitted model. Modeled flags alone do
not justify execution under unmodeled physical debug/alignment controls.

Memory exposes accessible bytes, execute permission and per-byte write
permission. Complete operand checks precede writes. Certificates require
nonwrapping code/data/stack ranges, actual executable-byte binding and canonical
return targets. Misaligned ordinary RAM accesses are admitted under the disabled
alignment-checking assumption; atomic profiles impose their own alignment and
line/page restrictions. Translation, physical aliases, native permission
enforcement, MMIO/DMA and real exception delivery remain external.

| Execution profile | Implemented scope | Exact reference |
| --- | --- | --- |
| Legacy `X86` | Selected LEA/MOV, RET, CMP/JNZ, JRCXZ/LOOP, XCHG32, LOCK XADD32 and userspace SYSCALL boundaries | [Exact functions](#checked-results), [control flow](control-flow.md), [exchange](atomic-exchange.md), [fetch-add](fetch-add.md) |
| `X86.Sequential` | Choice-indexed execution, ordinary 32/64-bit memory/register operations, arithmetic/logical operations, comparisons and restricted branches | [MOV/XCHG](sequential-moves.md), [arithmetic](sequential-arithmetic64.md), [memory ADD](sequential-add-memory64.md), [logical operations](sequential-logical64.md) |
| Sequential corpus extensions | Selected CMP/TEST, byte reads/order, CMOV32, unary/counter/displacement forms, logical shift by one, exact NOPs and ENDBR64 | [Corpus ISA](sequential-corpus-isa.md), [byte order](sequential-byte-order.md), [CMOV32](sequential-cmov32.md), [unary](sequential-unary.md), [shift](shift-one.md), [popcount](popcount.md) |
| Conditional control | Register-only CMOV64 and all sixteen unprefixed short rel8 Jcc conditions | [CMOV64](sequential-cmov64.md), [short branches](sequential-short-jcc.md) |
| Call/return | Separate `X86.CallReturn` engine with direct calls, actual RAM return targets, PUSH/POP and owned private stack writes | [Owned calls](call-stack.md) |
| Concurrent engines | Selected instruction families, current shared memory, explicit atomic events and optional FIFO buffering | [Workers](#mutable-atomic-worker-lifecycle), [buffers](#buffered-machine-execution), [full64 fetch-add](managed-fetch-add64.md) |

Operand widths, REX/prefix rules, supported base/SIB/displacement forms and
register coverage vary by family. Unsupported forms reject. A changed RSP
retains original authority without creating a new RET binding. Memory CMOV,
general indirect calls, privileged execution and arbitrary x86 remain outside
these profiles. Ordinary functional stores establish no atomicity theorem;
modeled indivisible RMWs have separate physical-conformance assumptions.

## Checked results

`EDSL.X86.Executes` is an unbounded finite transition closure with evaluator
soundness/completeness and deterministic result/count proofs. `AtomicExecutes`
also records ordered RMW events. The separate
`X86.Sequential.AllExecutions` contract constructs terminating actual
execution for every undefined-AF stream and derives reachable-prefix safety
and no divergence.

| Narrow function profile | Exact bytes | Result on admitted entries |
| --- | --- | --- |
| `increment` | `8d 47 01 c3` | Zero-extended low32 increment in RAX |
| `load32` | `8b 07 c3` | Zero-extended little-endian four-byte load |
| `store32` | `89 37 c3` | Low32 RSI stored at RDI, outside bytes/permissions retained |
| `exchange32` | `89 f0 87 07 c3` | Actual old32 return, replacement and one indivisible event |
| `fetch-add32` | `89 f0 f0 0f c1 07 c3` | Actual old32 return, modular addition and ADD flags |

The first three retire two modeled instructions; the atomic routines retire
three. Each needs exact current code, a readable stack8 return slot and a
canonical continuation. Data access, permissions and store/code/stack separation
remain explicit. Named entry points include
`Examples.Compiler.Increment.terminates_and_all_results_match`,
`Examples.Compiler.MemoryOps.load_correct`, `store_correct` and
`store_value_and_frame`, plus their admitted-value witnesses. See
[execution sources](../EDSL/X86/Execution.lean) and
[compiler examples](../EDSL/Examples/Compiler/MemoryOps.lean).

## Sequential functions and calls

| Capability | Contract and implementation reference |
| --- | --- |
| Scalar specifications and reusable proofs | [VC generator](reusable-checker.md), [scalar-call/resource adapter](pure-call.md), [spec-indexed ELF certificates](elf-certificates.md) |
| Arithmetic, comparisons and logical results | [Modular addition](compiler-arithmetic.md), [comparisons](comparison64.md), [logical sets](logical64.md), [signed clamp](compiler-clamp32.md), [unary functions](unary-functions.md), [popcount](popcount.md), [unsigned average](unsigned-average.md) |
| Read-only loops and searches | [Array maximum](array-maximum64.md), [array sum](array-sum64.md), [bounded byte scans](bounded-byte-scans.md), [first matches](first-match-searches.md), [paired byte comparison](paired-byte-comparison.md), [byte equality](byte-equality.md), [read-only call transport](read-only-call-transport.md) |
| Owned mutations | [Memory64](memory64.md), [pointer-returning stores](store-return32.md), [full64 store/return](store-return-value64.md), [counted stores](counted-store64.md), [Clang counted stores](counted-store64-clang.md), [final-store loop](counted-store-final64.md), [direct-add clients](counted-store-direct64.md) |
| Private stacks and DATA8 | [Direct nested calls](call-stack.md), [callable store/reload](call-memory64.md), [counted helper calls](call-memory-loop64.md) |
| Fixed-contract proof packets | [Interface/tasks](grading.md), [call-stack](call-stack-grading.md), [DATA8](call-memory64-grading.md), [counted DATA8](call-memory-loop64-grading.md), [counted store](counted-store64-grading.md) |

These contracts retain actual execution, ABI/return frames and the declared
current resources. Private stack bytes may remain changed where the frame
permits it. Counted DATA8 admits all full64 values/counts with 32 private bytes;
its independent post is `RAX=x+n mod 2^64`, old DATA at zero and
`DATA=x+n-1 mod 2^64` otherwise. Different looped/closed-form implementations
can meet the same contract. Costs, code shape and read order constrain
acceptance only where explicitly stated.

## Counted loop

`increment-loop` checks `89 f8 e3 05 8d 40 01 e2 fb c3`. It adds the full initial
RCX count to low32 RDI modulo 2^32, clears RCX and preserves flags/memory.
`IncrementLoop.loop_executes` uses a decreasing natural rank for every 64-bit
count; exact cost is `2*initial_RCX.toNat+3`, including RET. Raw/full-ELF
certificates cover owned assembly, without C/C++ source-loop preservation.
See [control flow](control-flow.md).

## Ordinary sum32 loops

[`EDSL.Sum32.sound`](../EDSL/Sum32/Correctness.lean) proves the independent
natural list sum modulo 2^32 for restricted pointer/count and indexed shapes.
It covers all AF streams, full RAX zero extension, RAM/ABI frames, ordered
element reads and the original stack8 read. Current code/array/stack loans
compose through `OS.ArrayResources.Admission`; empty input needs no input loan
or readable/canonical data pointer. The checker caps static code at 64 bytes
and 32 instructions, not the dynamic input count. See [sum32](sum32.md).

## Reusable CFGs and local proof obligations

[`CFG.check`](../EDSL/X86/Sequential/CFG.lean) validates an explicit finite
instruction partition, actual decode, closed successors and static depths.
The initial read-only profile caps windows at 64 bytes/32 instructions and
excludes stores, locked operations and syscalls. Row-20 Clang byte equality uses
an explicit 128-byte/32-node [CFG profile](cfg-profiles.md) for its complete
68-byte function; the default 64-byte path rejects it. GCC's 46-byte window
retains the 64-byte/32-node profile. These static limits leave the standard
300,000-step/depth-128 scalar packet limits unchanged and add no equality packet
API. See [byte equality](byte-equality.md). Sparse local obligations add
independent postconditions, actual current read permission and decreasing
ranks; optional equations derive exact instruction/read totals. The importer
alone establishes static facts. [CFGs](cfg.md), [stride sums](cfg.md) and
[two-array sums](pair32.md) describe worked proofs, including compatible
read-only aliases and empty-input exceptions.

## Abstract OS address-space contracts

[`OS.AddressSpace`](../EDSL/OS/AddressSpace.lean) checks fresh zero-filled
mapping, protection, unmapping and byte writes, with revocation and outside
frames. `load32_after_protect` and the word-store bridge compose operations
with actual binary loads/stores. This byte-granular sequential model excludes
page tables, aliases, allocation failure and concurrent revocation; abstract
unmap requires full mappedness, unlike Linux's hole-tolerant operation.
See [address spaces](address-space.md).

## Sequential ownership and allocation lifetimes

[`OS.Ownership`](../EDSL/OS/Ownership.lean) adds live allocation IDs, owner
and transfer epochs. Checked operations preserve `WellFormed`; release and
epoch changes permanently revoke old managed authority, including same-address
reuse. Owned stores retain current RAM coupling and frames. This is no native
allocator, stale-pointer enforcement, linear-token logic or C/C++ provenance
model. See [ownership](ownership.md).

## Shared read borrowing

[`OS.Borrowing`](../EDSL/OS/Borrowing.lean) checks stored lender/borrower
authority and contained readable regions. Overlapping read loans freeze the
whole allocation while any remains; guarded histories preserve surviving
records, bytes and permissions and permanently revoke finished IDs.
`borrowed_load32_correct` connects authority to actual load/RET bytes. Raw
accesses bypass this discipline. See [borrowing](borrowing.md).

## Managed read-worker lifecycle

[`OS.Threads`](../EDSL/OS/Threads.lean) schedules actual load/RET instructions
against current shared cells. Spawn retains code/data/stack loans through join;
results and permanent ID revocation survive admitted histories. Two successful
own selections complete the routine, while infinite idling remains possible.
Native creation, publication, context switching and join are external contracts.
See [threads](threads.md).

## Shared atomic handles and reservations

[`OS.Atomics`](../EDSL/OS/Atomics.lean) checks stored actor authority and
reserves an entire allocation while a handle survives. Histories retain
handles/loans, revoke closed IDs and connect exchanges to actual events.
Same-cell chains require the stated exchange-only history or continuous
reservation; arbitrary ordinary stores across reservation gaps are excluded.
See [handles](atomic-handles.md) and [exchange](atomic-exchange.md).

[Managed full64 loads and publication](managed-atomic-access64.md) recheck
current handle/cell authority and retain reservation, metadata, permissions,
unrelated bytes and live loans. The [buffered scheduler](managed-store-trace.md)
uses these checks for managed accesses; source acquire/release preservation
remains a separate obligation. [Atomic method foundations](atomic-call-contracts.md)
provide independent call contracts, constructive finite queue closure and
legality under order weakening. The implemented fetch-add/plain finite-cohort
adapters do not supply a general machine call adapter beyond those profiles.

[Plain load/store certification](managed-plain-methods.md) reuses one checked
padding/MOV64/RET method family for GCC and Clang, the independent universal
`Plain64.Claim`, whole-loaded-image resources and homogeneous/mixed witnesses.
The CLI retains these gates through each same-file cohort certificate. Plain uses
`managed-tso64-plain64-cohort-v1`, distinct from fetch-add's model below.
Acquire/release are declared interface annotations; constructed closed legal
histories require initialized resources and initially and finally empty queues.
General prefix/returned-call results permit valid incoming FIFOs and stores
pending at RET. The shared bound is 64 own issues per worker, with witness AF
indices local to each block; it supplies no timing, minimum-cost or fairness
claim. See the [measurement](../corpus/measurements/managed-plain64-v1/).

## Mutable atomic-worker lifecycle

Managed [exchange workers](atomic-workers.md) retain actual old values through
join. [Locked logical](atomic-logical64.md) and [mixed AND/OR/XOR
workers](atomic-set-workers.md) add separate full64 profiles and ordered
mathematical histories. [Atomic union](atomic-logical64-grading.md) and
[set proof packets](atomic-set64-grading.md) check fixed independent callable
contracts. Compound-call linearizability, common buffer integration and native
source-order mapping do not follow from uninterrupted equivalence.

## Locked fetch-add and modular counters

[Fetch-add32](fetch-add.md) proves exact bytes, ADD flags, current-handle
composition and finite same-cell modular sums. [Fetch-add64](atomic-fetch-add64.md),
[managed scheduling](managed-fetch-add64.md) and
[complete-call certificates](concurrent-fetch-add-certificates.md) connect actual
full64 RMW/RET origins to real-time-ordered independent histories and caller
frames. The corpus result uses `managed-tso64-closed-batch-v1`, with no foreign
RMWs; native thread authority and published x86-TSO remain separate.
The [TSO32 checker](tso-counter.md) and [finite-call adapter](counter-call-linearizability.md)
are distinct contracts.

## Counted atomic workers

`OS.CounterThreads` schedules the exact nineteen-byte locked-add loop with
full64 iteration requests and zero returns. Completing dispatch schedules from
a prepared finite entry cohort prove initial-plus-requested sum modulo 2^32;
checked collection revokes resources. Constructive completion exists, with
`3*count.toNat+3` own instructions per worker. `CounterCertificate.sound`
binds raw/full-ELF artifacts, retaining prepared resources and shared-address
premises. General mixed-history writes and native lifecycle behavior remain
outside it. See [counter workers](counter-workers.md).

## Protected payloads and mutex guards

`OS.Mutex` reserves distinct lock/payload allocations and grants fresh exclusive
guards from actual zero-observing XCHG events. The invariant may open while
held and must close at release. [Complete worker proofs](mutex-workers.md)
add current readiness, architectural prefix lifting, +2 modular totals, zero
returns and precise collection. Completed entry schedules cost
`13*n+4*busy`; entry completion exists at `13*n`, with a continuation of at
most `15*n` instructions from admitted intermediate states. These compare
schedules of the fixed routine, not arbitrary programs or schedulers.
See [mutex contracts](mutex.md).

## Buffered machine execution

`OS.TSO` adds FIFO publication, newest-own-store forwarding and locked-operation
stalls; RET can leave stores pending. `OS.MutexTSO` relates actual buffers to
logical replay for its fixed worker and proves prefix lifting, completed totals,
publication and resource collection. Constructive completion asserts an available
path. [Mixed-width buffers](mixed-store-buffer.md) and [managed full64
execution](managed-fetch-add64.md) are separately scoped extensions. None
establishes physical/published x86-TSO or source memory-order refinement.
The [plain cohort adapter](managed-plain-methods.md) separates returned calls
from drain closure and retains actual writer identities in closed histories.
See [store buffers](store-buffers.md).

## Concurrent syscall lifecycle

`OS.Suspend` captures actual requests, parks fresh invocation IDs and resumes
against current shared RAM while retaining peer contexts/FIFOs. IDs are one-use;
entry requires an empty caller FIFO without assuming a syscall flush.
Service outcomes, resource authorization and progress need additional contracts.
See [concurrent syscalls](concurrent-syscalls.md).

## Restricted ELF loading

[The restricted loader](elf.md) checks complete ELF64LE x86-64 `ET_EXEC` files,
LOAD bounds/permissions, disjoint rounded pages, fresh mappings, exact segment
bytes and BSS zeros. Its caps are 65,536 file bytes, 16 program headers,
65,536 memory bytes per segment and a file-backed entry window of at most
64 bytes. Page padding, Linux startup, relocation, PIE and dynamic linking are
unsupported. [Numeric windows](elf-function-window.md) and
[named-symbol checks](elf-function-symbol.md) use distinct profiles suitable for
the frozen full-file certificates; their limits are not the loader's limits.

## Live compiler-output certificates

The narrow `edsl-certify` profiles check observed raw/full-ELF bytes and emit
kernel-checked theorems. Other correct encodings can reject. Broader library
proofs and fixed-task proof packets have their own supported interfaces.
[Named ELF import](named-elf-import.md) supplies checked artifact/CFG facts;
independent functional and current-resource proofs still complete verification.
Finite native fixtures supplement conformance evidence, without source/OS/CPU
refinement. See [the new-function guide](verify-a-function.md).

## Standalone exit process

`edsl-certify-process` binds a complete restricted ELF to exit60/status42 in
three user instructions, for every modeled initial register/flags state and
without a caller stack/runtime. All completed OS traces have status42;
eventual completion additionally requires `LinuxExit.Fair`. The profile is
single-threaded and unintercepted, with kernel execution and cleanup external.
See [process exit](process-exit.md).

## Bounded stream write and exit

The write-exit42 profile binds loaded `OK\n` bytes, permits short writes, zero,
raw errors and waiting, and reaches exit after any admitted return. Full output
requires full transfer; eight user instructions exclude loading/kernel work.
Stable stream/buffer identity, the external return frame and error-with-no-bytes
behavior are assumptions. See [bounded write](process-write.md).

## Private futex adapter

`OS.Futex` supports one-word private WAIT/null-timeout and WAKE1, with fresh
pins, current-RAM compare/enqueue, eligible wake choices, retries/spurious
readiness and quiescent cleanup. Fixed-client proofs lift actual issue/drain
prefixes and establish publisher payload/W=1 persistence under current resource
admission. The byte checker does not synthesize that admission.
[Notification](futex-notification.md) requires one designated waiter expecting
a value other than one. [Predicate rechecking](futex-predicate.md) adds a 0/1
protocol and a postnotification return1/currentW1 suffix within 14 runtime
actions. No native futex implementation, general blocking acquisition or
unconditional progress is proved. See [futex scope](futex.md).

## Reproduce

Use [build and validation](validation.md) for maintained commands and each
capability's reference for exact fixtures, prerequisites and failure statuses.
The reusable API starts at [`EDSL`](../EDSL.lean); [`EDSL.All`](../EDSL/All.lean)
is the full audit catalogue. [Historical measurements](compiler-corpus.md)
retain their recorded counts; they do not establish a fresh validation run.

For `edsl-certify`, exit 0 means the emitted certificate checked; exit 3 means
unsupported, and other nonzero results mean certification failed. An existing
certificate filename is no success receipt. The [sum32 CLI](sum32.md#reproduce-and-rejection-behavior)
also distinguishes malformed input (4) from unsupported code/layout (3).
[CFG import](cfg.md#import-raw-bytes-or-a-function-from-an-elf) success establishes
static graph facts, with local functional/access proofs still required.
