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
**20/40 functions**, **40/80 artifacts**, and **three distinct concurrent functions**;
**20 functions / 40 artifacts** remain. Both GCC and Clang
outputs must pass for a function to count. Certificates for different routines
and successful decode/native checks do not increase these totals.

| Certified frozen functions, both compiler profiles | Contract/reference |
| --- | --- |
| `c_min_u64`, `c_max_u64` | [Independent full64 unsigned order](corpus-certificates.md) |
| `c_add_mod64` | [Addition modulo 2^64, including overflow](corpus-scalar-certificates.md) |
| `c_mul_mod64` | [Full64 natural product modulo 2^64 under independent flag choices](flag-choices.md) |
| `c_sign_i32` | [Signed low32 order result, all inputs and independent flag choices](shift-right32.md) |
| `c_clamp_i32` | [Signed low32 clamp, equal endpoints and arbitrary upper argument bits](compiler-clamp32.md) |
| `c_atomic_fetch_add64` | [Managed closed-batch concurrent history and current-resource contract](concurrent-fetch-add-certificates.md) |
| `c_atomic_load_acquire64`, `c_atomic_store_release64` | [Independent full64 Claim, loaded resources and same-file cohort witnesses](managed-plain-methods.md) |
| `c_strnlen_bytes` | [Bounded first-NUL search](bounded-byte-scans.md) |
| `c_memchr_index`, `c_linear_search_u32` | [Earliest matching index or full64 SIZE_MAX](first-match-searches.md) |
| `c_memcmp_bytes` | [Unsigned lexicographic comparison with signed low32 result](paired-byte-comparison.md) |
| `c_abs_i32`, `c_byteswap64` | [Independent absolute-value and byte-reversal contracts](unary-functions.md) |
| `c_popcount_loop` | [Full64 set-bit cardinality and all-input termination](popcount.md) |
| `c_average_u64` | [Floor of the unbounded natural sum divided by two](unsigned-average.md) |
| `c_parity_loop` | [Full64 set-bit cardinality modulo two, returned in unsigned low32](parity.md) |
| `c_rotl64` | [Full64 bit-origin left rotation by the unsigned low32 count modulo 64](rotate.md) |
| `c_bytes_equal` | [Complete-list equality, canonical low8 Boolean result, unconstrained upper56](byte-equality.md) |

Fetch-add uses `managed-tso64-closed-batch-v1`; load/store use the distinct
`managed-tso64-plain64-cohort-v1`. Their schedules, histories, caller/resource
frames and own-issue bounds remain conditional on those models. Acquire/release
are declared interface annotations. Plain closed legal histories require
initialized resources and initially and finally empty queues; general prefix
and returned-call results permit valid incoming queues and pending stores at RET.
Published/physical x86-TSO, source/compiler ordering preservation and native
Linux/kernel refinement remain separate obligations.

The [signed signum measurement](../corpus/measurements/signed-signum32-v1/)
records the latest accepted source and full-project/corpus gate evidence.
Both original named ELF functions reuse the vector VCG, resource adapter and
trusted execution/task registry.
Earlier measurement files retain their historical counts. See
[remaining blockers](corpus-blockers.md).

## Implemented foundations

| Area | Present capability | Scope/reference |
| --- | --- | --- |
| Proof infrastructure | Lean 4.35.0, warnings as errors, transitive axiom audit and fresh replay tooling | [Trust](trust.md); no third-party Lean package dependency |
| Machine execution | Restricted decoder, memory/stack semantics, unbounded execution and evaluator correspondence | [Machine profile and exact-byte functions](coverage.md#supported-machine-profile) |
| Reusable verification | Production-ISA VCG, sparse loop cutpoints, all-AF execution, real read origins and independent postconditions | [Checker](reusable-checker.md), [CFGs](cfg.md), [scalar calls](pure-call.md) |
| Independent flag choices | Full flag-vector executor/VCG, reusable resource and named-ELF certificates, trusted execution/task registry and multiplication/signum packet grading | [Flag choices](flag-choices.md); both original multiplication and signum artifact pairs included in corpus acceptance |
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
| Checked ordinary effects in TSO64 | Checked step admission from current OS gates, complete local-CPU reconstruction, mixed DWORD/QWORD FIFO forwarding, pending stores at RET and own-drain CPU preservation; generic actual-schedule simulation and cut transport | [Effect/scheduler bridge](effect-scheduler-bridge.md); clients prove the universal origin lift law; successful schedules supply no independent fault-freedom or progress theorem; no opcode, authority-profile or corpus-coverage extension |
| Family-indexed traces and checked lifts | Explicit RMW families throughout connected histories, passive/resource frames, ordinary readiness and actual-schedule folds; current-step laws retain executor selection evidence | [Shared simulation laws](effect-scheduler-bridge.md#instruction-families-and-checked-steps); default XADD clients remain supported; mixed blocks use the separate adapter below; counted loops and independent progress remain separate obligations |
| Resumable mixed instruction blocks | Present-state admission and generated ordinary/RMW obligations, exact FIFO-blocked idle histories, current selector/effect evidence, checked schedule/cut/return transport, shared Nat RMW accounting, caller-only ordinary-node transport, explicit idle-stable completion and stable metadata/permission/selector authority | [Mixed resumption](mixed-resumption.md); clients prove independent contracts, cutpoint invariants and block obligations; general Post is historical at RET; stable assertions extend to full finite returned histories; program-specific counts remain client obligations; no fairness, termination, hardware/OS, lifecycle, ABI or corpus-coverage extension |
| Frozen counter per-worker annotations | Complete 49-byte GCC and 86-byte Clang windows, independent current admission, all uint32 counts, exact full-history unit-RMW counts and void-call return frames under production TSO64 | [Counter annotations](counter-contracts.md); conditional on an actual finite returned schedule; no-other-writes, lifetime/join and constructive completion gates remain; no new corpus credit |
| Counter cohort value and queue closure | Actual returned two-slot GCC/Clang schedules derive the common cell’s modular sum from independent requests; generic caller-only cohorts retain empty queues and classify every original issue | [Counter verification](counter-contracts.md); value theorem permits inherited owned-only FIFOs; closure requires initially empty FIFOs; lifecycle, constructive completion and corpus admission remain separate |
| Counters and atomic sets | Modular/ordered histories, managed finite cohorts and selected complete-call contracts | [Counters](counter-workers.md), [mixed set workers](atomic-set-workers.md), [full64 fetch-add](managed-fetch-add64.md); no general source-order mapping |
| Managed qword histories | Complete computed access traces, unique managed publications, full-word load sources and checked finite C23 graph extraction | [Checked atomic traces](checked-atomic-traces.md) retain complete initial objects, actual writer identities and publication ranks; `verify` continues to use the full graph-legality checker with empty initial/final queues |
| Initialized graph construction | `Captured.inputs_ready` derives all input adequacy requirements; `Captured.build_legal` proves existing builder success, actual execution correspondence and finite-fragment legality for arbitrary declared orders | [Construction contract](checked-atomic-traces.md#graph-construction-from-actual-execution); well-formed initialized resources, empty initial/final queues, actual scan at an arbitrary offset with an empty incoming publication map, and actual registry/RAM enumeration; no caller-supplied graph, key/value/rank or legality oracle |
| Execution views and writer order | View monotonicity, actual access authority and source-writer ranks, mixed store/RMW publication order, cross-cell publication coverage, exact-source transfer for loads and RMWs, exact writer successor views and generic write/read, read/read and strict read/write rank bounds | [Views and sources](checked-atomic-traces.md#execution-views), [publication coverage](checked-atomic-traces.md#publication-coverage), [exact-source transfer](checked-atomic-traces.md#exact-source-view-transfer) and [generic read sides](checked-atomic-traces.md#read-sides-of-loads-and-rmws); finite successful well-formed/sequenced/final-quiescent runs permit incoming FIFOs |
| Structural graphs and sequencing | `Built.wellFormed` derives structural well-formedness from mapping alone; `Executed` derives universal all-row sequencing coherence, no-future sequencing and same-cell RMW predecessors | [Graph contracts](checked-atomic-traces.md#universal-graph-sequencing); actual scan, initial invariants, empty incoming publication map, final quiescence and complete structural mapping are explicit; registry/RAM manifest provenance remains separate |
| Acquiring graph order and coherence | Actual clocks order sequencing, RF, release members and HB; actual view transport derives all four HB coherence conditions and `Executed.legal` for arbitrary declared annotations | [HB order](checked-atomic-traces.md#happens-before-order-for-acquiring-annotations) and [acquiring fragment](checked-atomic-traces.md#universal-acquiring-fragment-legality); conditional on actual scan and complete structural mapping, which `Captured` derives at its initialized empty-queue boundary |
| Finite no-acquire legality | `executed.legal_without_acquire checked` proves `C23Atomic.Legal` when `orders.noAcquire run.events = true`; `relaxed_legal` covers `Orders.relaxed` | [No-acquire fragment](checked-atomic-traces.md#universal-no-acquire-legality); a compatible special case that reduces HB to sequencing without a graph-legality checker |
| C23 atomic event constraints | Typed relaxed/acquire/release graphs, sound finite admission and generic message-passing rules | [Atomic event model](c23-atomic-events.md), [checker](c23-atomic-checker.md); no full C frontend or machine-to-source preservation |
| Atomic method foundations | Independent completed-call contracts, constructive finite queue publication and legality under order weakening | [Call contracts](atomic-call-contracts.md); a general machine call adapter beyond the supported finite cohorts and native memory-order correspondence remain open |
| Managed load/store methods | Shared decoder-backed padding/MOV64/RET proofs, enabledness, mixed-cohort completion from actual prefixes with exact remaining issue/AF choices, separate drain closure, complete call/scanner correspondence, constructed finite atomic histories and scalar ABI return frames | [Method family](managed-plain-methods.md); one invocation per actual initial slot, including already-returned workers; completion constructs one finite suffix; atomic history requires initialized scans and empty endpoint queues |
| Independent plain-method admission | Present-only Plain64 catalog, inputs and `Pre`; separate static byte-shape evidence derives actual-slot invocations, exact requests, current references and actual FIFO/counter boundaries | [Admission bridge](managed-plain-methods.md#admit-a-registered-image-independently); scalar ABI/resource entry is explicit; shared loaded-image and witness adapters supply the separate useful-population gates |
| Useful plain64 execution witnesses | Constructed overlapping high-word cohorts and actual writer RET < publication < acquiring access, with persistent source identity and exact initializer-offset RF rows, for both complete frozen ELF files | [Shared constructors](managed-plain-methods.md#construct-overlapping-and-delayed-publication-executions); initially empty queues, two admitted workers, declared interface orders and block-local AF indices; CLI named rows project from each same-file cohort certificate; accepted evidence is in the managed plain64 measurement |
| Cohort RAM and resource frames | Independent prefix/return frame predicates; full-cell equality outside all target qwords plus actual incoming FIFO footprints; current target authority, original resources and scalar ABI frames derived through the shared adapter | [Footprint and frame adapter](managed-plain-methods.md#frame-complete-ram-cells); incoming ordinary/managed entries keep their real address/width; prefix frames need no final completion or quiescence; return frames permit pending publications |
| Independent plain-call safety and progress | Actual queue suffix/allocation counters, exact target selectors, flags, saved registers, full code and original caller reads; running-worker enabledness and derived 64-issue upper bound | [Safety and progress](managed-plain-methods.md#derive-safety-and-progress); current-only admission plus separate static shapes and actual execution; no fairness, timing or minimum-operation claim |
| Independent plain-call completed behavior | Same-run unique access and RET, full64 selected reads or exact managed enqueues, complete call coverage, scalar return/queue frames and exclusion of RMW/blocked observations | [Behavior adapter](managed-plain-methods.md#derive-safety-and-progress); arbitrary valid incoming FIFOs; independent Post and closed History use exactly the same calls |
| Full independent plain-call contract | `PlainCallClaim64.claim` supplies every `Plain64.Claim` obligation: prefix safety, completed behavior, closed output, enabledness, chosen completion, real drain closure and a derived positive uniform bound | [Shared claim](managed-plain-methods.md#use-the-full-independent-contract); static shapes remain separate from present-only Pre; shared adapters supply the frozen-ELF resources and homogeneous/mixed witnesses required by the CLI cohort gates |
| Independent chosen completion and closure | Every original suffix AF matches the thread's own-prefix count; actual remaining counts, already-returned skipping and saved replies; separate actual drains retain CPU responses | [Completion](managed-plain-methods.md#complete-a-mixed-cohort-from-an-actual-prefix); constructs one finite schedule, not fairness or forced publication before RET |
| Full closed output from independent admission | Actual finished schedule derives full `ClosedPost`: same Post, scanner, initialized live registry, exact complete machine events and source keys, actual builder/History, target-only full-cell frame and collection | [Closed output](managed-plain-methods.md#construct-the-complete-atomic-history); empty endpoint queues and arbitrary counters/offset; no supplied graph/source/initializer oracle |
| Partial method execution and positions | Chosen finite prefixes, stopping before RET, literal peer preservation, exact preceding own-issue counts at accesses/returns and unique issue positions | [Shared prefix APIs](managed-plain-methods.md#use-the-full-independent-contract); actual production schedules and arbitrary admitted cutpoints; no algorithmic optimality or physical cost claim |
| Whole-ELF plain-call resources | Actual managed setup and two-worker attachment, preserved caller reads, complete loaded-cell/permission frames, fresh targets and constructed closed executions | [Loaded ELF batches](managed-plain-methods.md#admit-the-complete-loaded-elf); arbitrary full64 data/counters; shared homogeneous/mixed adapters implement overlap and selected-writer RF evidence, retained by CLI cohort registration |
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

`Captured` is the raw construction context for empty initial queues. It includes
actual registry/RAM enumeration and derives both `Built` and `Executed`, then
finite-fragment legality for arbitrary declared orders. The builder and verifier
are unchanged; legality-checker totality and construction for arbitrary incoming
managed queues remain separate obligations.

`noAcquire` checks declared annotations rather than machine bytes and never
weakens an acquiring order. A false result leaves synchronization and HB
obligations outside that special-case theorem; `executed.legal` handles them
through actual view transport. The universal results concern the finite C23
atomic fragment;
full C23 semantics, a source frontend, source/compiler preservation, native or
kernel correspondence and fairness remain separate. These graph theorems alone
add no corpus credit.

Current resource and synchronization proofs can express specific access,
lifetime, framing and protocol safety properties. They do not establish general
security analysis, noninterference or whole-OS safety.

## Planned capabilities

- Source/interface-order justification, repeated method invocation composition,
  and graph construction for broader incoming-queue boundaries.
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
