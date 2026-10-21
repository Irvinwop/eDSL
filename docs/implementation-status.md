# Implementation status

eDieSeL is a Lean 4 project for direct verification of final machine code.
It currently provides restricted x86-64 userspace semantics, reusable proof
infrastructure and conditional artifact certificates. Kernel and whole-OS
verification are project goals; no native kernel or physical CPU refinement is
implemented.

## Status definitions

- **Implemented** means the repository contains the named API, executable or
  checked theorem for its documented subset. Environmental hypotheses remain
  part of every result.
- **Experimental** identifies narrow models and tooling whose integration or
  target correspondence remains limited. It does not imply native support.
- **Planned** identifies capabilities without an implemented verification path.
  A design document or native fixture does not establish such a path.

## Frozen corpus coverage

The fixed [compiler corpus](compiler-corpus.md) contains 40 functions and
80 exact final-ELF windows. Current validated conditional coverage is
**16/40 functions**, **32/80 artifacts**, and **one distinct concurrent function**;
**24 functions / 48 artifacts** remain. Both GCC and Clang
outputs must pass for a function to count. Certificates for different routines
and successful decode/native checks do not increase these totals.

| Certified frozen functions, both compiler profiles | Contract/reference |
| --- | --- |
| `c_min_u64`, `c_max_u64` | [Independent full64 unsigned order](corpus-certificates.md) |
| `c_add_mod64` | [Addition modulo 2^64, including overflow](corpus-scalar-certificates.md) |
| `c_clamp_i32` | [Signed low32 clamp, equal endpoints and arbitrary upper argument bits](compiler-clamp32.md) |
| `c_atomic_fetch_add64` | [Managed closed-batch concurrent history and current-resource contract](concurrent-fetch-add-certificates.md) |
| `c_strnlen_bytes` | [Bounded first-NUL search](bounded-byte-scans.md) |
| `c_memchr_index`, `c_linear_search_u32` | [Earliest matching index or full64 SIZE_MAX](first-match-searches.md) |
| `c_memcmp_bytes` | [Unsigned lexicographic comparison with signed low32 result](paired-byte-comparison.md) |
| `c_abs_i32`, `c_byteswap64` | [Independent absolute-value and byte-reversal contracts](unary-functions.md) |
| `c_popcount_loop` | [Full64 set-bit cardinality and all-input termination](popcount.md) |
| `c_average_u64` | [Floor of the unbounded natural sum divided by two](unsigned-average.md) |
| `c_parity_loop` | [Full64 set-bit cardinality modulo two, returned in unsigned low32](parity.md) |
| `c_rotl64` | [Full64 bit-origin left rotation by the unsigned low32 count modulo 64](rotate.md) |
| `c_bytes_equal` | [Complete-list equality, canonical low8 Boolean result, unconstrained upper56](byte-equality.md) |

The concurrent contract is `managed-tso64-closed-batch-v1`. Its actual schedules,
histories, caller/resource frames and bounds on each worker's own instruction
selections remain conditional on that model. Published x86-TSO, GNU source atomic
orders and native Linux refinement are separate obligations.

The [byte-equality measurement](../corpus/measurements/byte-equality-v1/)
records the latest validated total above. The combined full-project/corpus
certificate gate and external fresh kernel replay passed on source
`383d1f1ef928f551b89a8424ae46c8bb019ce2e2`. See
[commit-specific CI results in GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions).
Earlier measurement files retain their historical counts. See
[remaining blockers](corpus-blockers.md).

## Implemented foundations

| Area | Present capability | Scope/reference |
| --- | --- | --- |
| Proof infrastructure | Lean 4.35.0, warnings as errors, transitive axiom audit and fresh replay tooling | [Trust](trust.md); no third-party Lean package dependency |
| Machine execution | Restricted decoder, memory/stack semantics, unbounded execution and evaluator correspondence | [Machine profile and exact-byte functions](coverage.md#supported-machine-profile) |
| Reusable verification | Production-ISA VCG, sparse loop cutpoints, all-AF execution, real read origins and independent postconditions | [Checker](reusable-checker.md), [CFGs](cfg.md), [scalar calls](pure-call.md) |
| Artifact binding | Raw bytes, restricted ELF loading, numeric windows, named symbols and spec-indexed complete-file certificates | [ELF](elf.md), [named functions](elf-function-symbol.md), [certificate API](elf-certificates.md) |
| Sequential resources | Address spaces, allocation lifetimes/epochs, read loans, checked stores and current-RAM bridges | [Address spaces](address-space.md), [ownership](ownership.md), [borrowing](borrowing.md) |
| Loops and calls | Restricted sums/scans, owned direct calls, DATA8 effects and counted helper contracts | [Capability index](coverage.md#sequential-functions-and-calls) |
| Proof packets | Fixed independent tasks, exact raw/full-ELF binding and fresh kernel-checked helper declarations | [Proof-packet interface](grading.md); task/ISA profiles remain restricted |
| Cost results | Exact modeled instruction/read totals and selected lower bounds | [Cost model](cost-model.md); no CPU-time or unrestricted optimum claim |

The reusable import is [`EDSL`](../EDSL.lean); [`EDSL.All`](../EDSL/All.lean)
collects the full audit catalogue. Implementation remains in Lean. C/C++ and
assembly fixtures exercise generated domains; they do not supply formal
GNU C/C++ or LLVM semantics.

## Implemented experimental models

These models have scoped Lean proofs; their native OS/hardware correspondence
remains open. They are separate profiles, not one interchangeable backend.

| Area | Present guarantee | Important limit |
| --- | --- | --- |
| Read and atomic workers | Actual instruction dispatch, current shared cells, retained results and resource revocation through join | [Managed lifecycles](threads.md) and [atomic workers](atomic-workers.md) assume logical actors and guarded histories |
| Counters and atomic sets | Modular/ordered histories, managed finite cohorts and selected complete-call contracts | [Counters](counter-workers.md), [mixed set workers](atomic-set-workers.md), [full64 fetch-add](managed-fetch-add64.md); no general source-order mapping |
| Managed qword histories | Complete computed access traces, unique managed publications, full-word load sources and checked finite C23 graph extraction | [Checked atomic traces](checked-atomic-traces.md) retain complete initial objects, actual writer identities and publication ranks; `verify` continues to use the full graph-legality checker with empty initial/final queues |
| Execution views and writer order | View monotonicity, actual access authority and source-writer ranks, mixed store/RMW publication order, cross-cell publication coverage, exact-source load transfer, exact writer successor views and generic write/read, read/read and strict read/write rank bounds including RMW read sides | [Views and sources](checked-atomic-traces.md#execution-views), [publication coverage](checked-atomic-traces.md#publication-coverage), [exact-source transfer](checked-atomic-traces.md#exact-source-view-transfer) and [generic read sides](checked-atomic-traces.md#read-sides-of-loads-and-rmws); finite successful well-formed/sequenced/final-quiescent runs permit incoming FIFOs |
| Structural graphs and sequencing | `Built.wellFormed` derives structural well-formedness from mapping alone; `Executed` derives universal all-row sequencing coherence, no-future sequencing and same-cell RMW predecessors | [Graph contracts](checked-atomic-traces.md#universal-graph-sequencing); actual scan, initial invariants, empty incoming publication map, final quiescence and complete structural mapping are explicit; registry/RAM manifest provenance remains separate |
| Finite no-acquire legality | `executed.legal_without_acquire checked` proves `C23Atomic.Legal` for every mapped actual finite run with `orders.noAcquire run.events = true`; `relaxed_legal` covers `Orders.relaxed` | [No-acquire fragment](checked-atomic-traces.md#universal-no-acquire-legality); declared annotations exclude synchronizes-with (SW), reducing happens-before (HB) to sequencing without a graph-legality checker; general acquiring/release-sequence mappings and graph-build totality remain open |
| C23 atomic event constraints | Typed relaxed/acquire/release graphs, sound finite admission and generic message-passing rules | [Atomic event model](c23-atomic-events.md), [checker](c23-atomic-checker.md); no full C frontend or machine-to-source preservation |
| Atomic method foundations | Independent completed-call contracts, constructive finite queue publication and legality under order weakening | [Call contracts](atomic-call-contracts.md); a general machine call adapter and universal operational legality for acquiring interfaces remain open |
| Managed load/store methods | Shared decoder-backed padding/MOV64/RET proofs, current-resource enabledness, finite interleaving closure, indexed access/response origins, complete finite call cohorts and whole scanner/call correspondence | [Method family](managed-plain-methods.md); one invocation per initial worker; acquiring/release-sequence HB correspondence and final-ELF contracts remain separate |
| Managed-word TSO refinement | Finite classified actual scheduler traces to an independent uniform64 memory fragment | [Projection and boundaries](word-tso-refinement.md); no full HOL4, physical or source-order correspondence |
| Mutex workers and buffers | Fixed-routine architectural/buffered prefix lifting, totals, resource collection and constructive completion | [Mutex workers](mutex-workers.md), [store buffers](store-buffers.md); existence of completion does not imply every scheduler completes |
| Concurrent syscalls | Fresh pending IDs, peer execution and resumption against current RAM | [Suspension](concurrent-syscalls.md) requires an empty caller FIFO and external service contracts |
| Private futex clients | Restricted WAIT/WAKE1 service, publication, notification and predicate rechecking | [Futex](futex.md), [predicate loop](futex-predicate.md); explicit client policies and no native kernel proof |
| Standalone processes | Exit42 and bounded stream-write/exit ELF certificates | [Exit](process-exit.md), [write](process-write.md); progress, loader and syscall implementation contracts remain explicit |

`Executed` does not require initial quiescence. Ordinary incoming queues and
views outside the graph's access events remain permitted, but `Built` still
requires an in-run event for every managed publication. This graph mapping
excludes incoming managed entries and gives their drains no invented instruction
origins. Clients separately enumerate the actual initial registry and
RAM manifest; structural `Built` does not authenticate it.

`noAcquire` checks declared annotations rather than machine bytes and never
weakens an acquiring order. A false result leaves synchronization and HB
obligations open. The universal result concerns the finite C23 atomic fragment;
full C23 semantics, a source frontend, source/compiler preservation, native or
kernel correspondence and fairness remain separate. Frozen corpus totals are
unchanged.

Current resource and synchronization proofs can express specific access,
lifetime, framing and protocol safety properties. They do not establish general
security analysis, noninterference or whole-OS safety.

## Planned capabilities

- Justified release/acquire and release-sequence mappings, all-HB coherence,
  HB acyclicity and no-future-HB reads for universal acquiring-fragment legality.
- Broader instruction/effect coverage, general interprocedural automation,
  richer pending histories and interoperable concurrency/resource profiles.
- Native thread/runtime, Linux loader and syscall refinement; privileged ISA,
  page tables, interrupts, devices and concrete kernel component proofs.
- Whole-program resource/failure composition and explicit attacker/observation
  models for broader security properties.
- GNU C23/GNU C++26/LLVM eDSLs, source/IR preservation, other architectures and
  OS adapters.

The [roadmap](roadmap.md) orders these dependencies. The
[coverage index](coverage.md) links exact APIs, target limitations and failure
behavior; [validation](validation.md) lists checks.
