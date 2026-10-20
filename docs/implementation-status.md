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
80 exact final-ELF windows. Current locally accepted conditional coverage is
**15/40 functions**, **30/80 artifacts**, and **one distinct concurrent function**;
**25 functions / 50 artifacts** remain. Both GCC and Clang
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

The concurrent contract is `managed-tso64-closed-batch-v1`. Its actual schedules,
histories, caller/resource frames and bounds on each worker's own instruction
selections remain conditional on that model. Published x86-TSO, GNU source atomic
orders and native Linux refinement are separate obligations.

The [parity and rotation measurement](../corpus/measurements/parity-rotation-v1/)
records the latest locally accepted total above. The combined full-project/corpus
gate and fresh kernel replay passed. Commit-specific CI results are available in
[GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions). Earlier
measurement files retain their historical counts. See
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
| Mutex workers and buffers | Fixed-routine architectural/buffered prefix lifting, totals, resource collection and constructive completion | [Mutex workers](mutex-workers.md), [store buffers](store-buffers.md); existence of completion does not imply every scheduler completes |
| Concurrent syscalls | Fresh pending IDs, peer execution and resumption against current RAM | [Suspension](concurrent-syscalls.md) requires an empty caller FIFO and external service contracts |
| Private futex clients | Restricted WAIT/WAKE1 service, publication, notification and predicate rechecking | [Futex](futex.md), [predicate loop](futex-predicate.md); explicit client policies and no native kernel proof |
| Standalone processes | Exit42 and bounded stream-write/exit ELF certificates | [Exit](process-exit.md), [write](process-write.md); progress, loader and syscall implementation contracts remain explicit |

Current resource and synchronization proofs can express specific access,
lifetime, framing and protocol safety properties. They do not establish general
security analysis, noninterference or whole-OS safety.

## Planned capabilities

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
