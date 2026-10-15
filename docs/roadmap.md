# Roadmap and acceptance gates

This is a research and engineering plan, not a claim that complete GNU C23,
GNU C++26, LLVM, x86-64, or Linux semantics already exist in Lean. Work is
ordered by proof dependencies. There are no completion-date promises.

## Decisions for the initial direction

- Lean 4 is the implementation/proof/embedding language.
- OS behavior is a first-class semantic domain across every language layer.
- Existing compilers are untrusted producers. Direct binary verification is the
  main path; source/IR translation validation adds an optional stronger guarantee.
- Start with x86-64 userspace and a restricted Linux/System V/ELF profile.
- Begin with a small function before process loading, memory and concurrency.
- Report physical-platform and OS conformance assumptions explicitly.
- Use explicit cost models and restricted candidate classes for lower bounds.
- Apache-2.0 plus NOTICE/citation metadata; DCO 1.1 for contributions.
- Publish code and owned fixtures, with real findings/evidence kept out of Git
  and CI artifacts. Validate concrete OS components to discharge contracts.

## Dependency graph

```mermaid
flowchart LR
    M0[0 Foundation] --> M1[1 Semantic contracts]
    M1 --> M2[2 Exact function bytes]
    M2 --> M3[3 Static Linux process]
    M3 --> M4[4 Owned memory and loops]
    M4 --> M5[5 Threads and SC atomics]
    M5 --> M6[6 Weak memory and waits]
    M2 --> M7[7 LLVM and richer languages]
    M2 --> M9[9 Cost proofs]
    M6 --> M8[8 Wider OS and linking]
    M7 -. optional preservation .-> M8
    M2 --> K[Kernel component and privileged ISA track]
    M4 --> K
    M6 -. concurrency support .-> K
    K --> M10[10 More targets and less trust]
    M8 --> M10
```

### 0. Foundation — current repository

Present: pinned Lean/Lake project; generic refinement composition and safety
transfer; a tiny abstract-machine correctness/lower-bound example; transitive
axiom audit; optional native dialect checks; design documents; licensing and
contribution policy. CI must build/audit Lean and retain native probes as a
separate check. The first concrete function-byte profile is now implemented;
see [coverage](coverage.md) for exact theorems, supported instructions and trust.

### 1. Semantic contracts and reuse decisions

Define trace/outcome types, admitted initial states, divergence/fault/deadlock
policy, environment coupling, memory/resource identities, observations and
refinement. Prove composition, nonvacuity obligations and suitable safety/
termination transfer lemmas. Decide operational versus event-graph concurrency
representations and their correspondence.

Evaluate reusable Lean bitvector, SSA, temporal and resource-logic libraries;
record revisions, licenses, supported Lean versions, axiom dependencies,
performance and gaps. Establish a per-feature support/proof ledger.

Exit: reviewed theorem templates and an executable toy semantics whose proofs
exercise the interfaces; no circular correctness-by-checker-definition.

Implemented so far: deterministic x86 function and first-syscall execution
closures, evaluator soundness/completeness, result determinism and user-divergence
exclusion. The raw exit contract adds infinite OS observation traces, an
all-completed-results theorem, explicit conditional progress, an indefinite-wait
counterexample and a nonempty fair trace. General temporal composition and
shared-memory nondeterminism remain future work.

### 2. First real artifact: a restricted function

The first increment contract is implemented for `8d 47 01 c3`, with live
Clang C/C++ and GCC C certificates and native boundary checks. Full scope and
remaining artifact/physical-conformance assumptions are in [coverage](coverage.md).
The memory extension also checks `8b 07 c3` (32-bit load) and `89 37 c3`
(32-bit store), each from Clang C/C++ and GCC C. Permission, little-endian value,
outside-footprint framing, preserved code/return stack and two-step termination
are proved. The counted assembly increment loop now has all-count correctness,
termination and exact cost through a backward branch; wider control flow remains ahead.

Choose a loop-free unsigned fixed-width function specification with edge cases.
Select a small x86-64 instruction subset, prove exact-byte decoding and
instruction semantics, and state entry/return/register/stack assumptions.
Compile ordinary source in any available language or supply assembly. A formal
frontend is not needed to prove the resulting binary meets the independent
function specification. Use source/IR annotations as untrusted proof hints.

Invoke a pinned compiler/configuration, ingest its exact function bytes, and
produce a checked proof/certificate relating those bytes to the specification.
Handle all admitted inputs, including wraparound. Initially reject general memory,
foreign calls, exceptions, unsupported instructions and unknown control flow.

Exit: a named Lean theorem for actual compiler output, with recorded build and
caller/platform assumptions; changed immediate values, wrong widths, unsupported
bytes, and mismatched manifests fail validation. Prefer a second compiler or
optimization configuration to expose compiler-specific assumptions.

### 3. Static process and minimal Linux contract

Implemented supporting OS contract: byte-granular mapping/protection/unmapping
with permission-revocation and disjoint-framing proofs. A protection change
outside a binary load's footprint preserves its contract, with a concrete
admitted-entry witness. Independent Linux VM probes cover zero filling, denied
access and adjacent-page preservation. Page-granular VM syscall refinement and
general startup-data obligations remain unimplemented; see [scope](address-space.md).

The restricted ELF container step is now implemented: bounded ELF64LE parsing,
validated load segments and page freshness, exact file-byte/BSS installation,
preservation of existing cells and entry `CodeAt` derivation. Full observed files
are embedded in generated Lean certificates, with compiler profiles checked
through the modeled loader. The function profiles retain explicit caller
stack/data conditions. See [ELF scope](elf.md).

The first standalone process result is implemented: a checked static ELF entry
executes `mov edi,42; mov eax,60; syscall` in exactly three user instructions,
for every modeled initial register/flags state, without caller stack contents,
startup data or runtime. `edsl-certify-process` generates the full-file Lean
certificate. The modeled single-thread, unintercepted raw exit60 contract gives
status42 on every completed trace and eventual completion under explicit
abstract completion progress. Indefinite waiting is admitted without that
assumption, and a terminating fair trace witnesses nonvacuity. Owned Clang/GCC
assembly ELFs receive certificates and native status checks; wrong status and
syscall mutations are rejected. See [process scope](process-exit.md).

The bounded stream-write extension is also implemented: exact message bytes are
bound through the loaded ELF, raw results include partial counts and negative
errors, and every admitted return resumes at checked exit instructions. Completed
user executions cost eight instructions and accept a message prefix; full output
is conditional on a full transfer. Native owned pipe checks exercise successful
output and unavailable nonblocking capacity. Stable stream/return contracts remain
explicit; see [write scope](process-write.md).

Remaining work: Linux loader conformance, startup stack/auxiliary state when
used, privileged syscall entry and concrete kernel execution/cleanup. Extend
the process profile to control flow, retry protocols and resource lifetimes.
Add descriptor identity, signals/interruption and wider I/O without assuming
all external effects succeed. Preserve explicit loader/kernel
contracts until implementation proofs discharge them.

Exit: a process-level trace/result theorem linked to the final artifact, with
all reachable code/runtime and external contracts accounted for.

### 4. Owned memory, calls and loops

Implemented foundation: sequential four-byte ordinary-RAM reads/writes, explicit
per-byte mappedness/write permissions, read-after-write, disjoint framing and
nonvacuous compiler-profile witnesses. Language-object provenance, a runtime
allocator, concurrent atomicity and calls beyond the modeled return remain ahead.
The counted-loop extension now proves modular increment for every 64-bit count
with a decreasing natural variant and exact `2*count+3` cost, preserving flags
and memory. Raw/full-ELF certificates cover the owned assembly from Clang/GCC;
this is not a compiler source-loop preservation theorem. See [control flow](control-flow.md).

The OS/machine memory bridge now proves that checked word stores update natural-
address OS cells exactly as the machine store updates projected memory. Actual
compiler store bytes implement that OS update for all admitted values, retaining
permissions and outside-footprint cells. Physical backing and aliases remain
future obligations.

The sequential ownership registry is now implemented over `AddressSpace.Space`.
Fresh IDs distinguish lifetimes at remapped addresses; transfer epochs revoke
previous authority even across A→B→A or self-transfer. Checked whole-allocation
allocate/adopt/transfer/release/protect and owned word stores preserve the live
registry invariant. Revocation persists through every later managed history.
The owned-store theorem composes with exact machine bytes and has admitted
states for every old word/source argument. Regressions cover reuse, transfer,
cross-allocation stores, hidden cells, final-byte overlap and exact readback.
See [ownership contracts and limits](ownership.md).

Shared read borrowing is now implemented over that registry. Each stored loan
names a current lender ticket and readable contained subregion; multiple loans
freeze their whole allocation until all finish. Checked histories preserve
loan records, exact cells and permissions, and finished IDs stay revoked.
Authorized word reads compose with actual load/RET bytes; arbitrary-history
read and independent buffer stability have checked proofs. Every 32-bit value
has an admitted symbolic binary witness. See [borrowing scope](borrowing.md).

These remain proof-level authorities: raw pointers contain no epoch, principal
IDs are proof data and copyable tickets/loans do not form a linear-token logic.
The [managed read-worker slice](threads.md) now connects borrowed code/data/stack
to actual instruction scheduling and checked start/completion/join contracts.
Next add protected invariants, mutable workers and concrete thread/runtime
refinement. Region splitting, mutable borrowing, broader
stack/heap object lifetimes, language provenance, allocator search/failure/cleanup,
calls and richer memory-loop invariants remain required. Concurrent safety needs
an interference model that enforces or accounts for resource transitions.

Exit: a buffer/loop binary has target memory safety, functional correctness and
explicit termination/resource bounds. Add source definedness/preservation only
when claiming a source-level result. Native fault
injection and differential runs supplement these proofs.

### 5. First concurrency slice

Implemented prerequisite: a root-managed read-worker lifecycle with three
internal loans, actual load/RET instruction scheduling against current shared
memory, checked result collection and permanent thread/loan-ID revocation.
All six two-worker instruction interleavings have independent byte/result
regressions; symbolic witnesses cover every 32-bit word. Arbitrary admitted
histories preserve results, and successful schedules with two selections of a
load-pending worker complete it. Idle scheduling need not make progress. This
abstract read-only profile does **not** satisfy the counter workload or concrete
OS/runtime refinement exit below. See [thread contracts](threads.md).

Implemented atomic prerequisite: the `exchange32` profile certifies exact
`MOV EAX,ESI; XCHG DWORD PTR [RDI],EAX; RET` bytes from Clang/GCC in three
instructions with a singleton indivisible RMW-event trace. Guarded OS exchanges
project the same current-cell update while excluding live read loans, and
arbitrary finite same-cell exchange histories prove old/new value chaining.
Native eight-thread token conservation supplements those model proofs;
see [atomic-exchange scope](atomic-exchange.md).

Shared atomic authority is now implemented with distinct actor handles,
whole-allocation reservations, read-loan exclusion, guarded mutation,
well-formedness, permanent handle revocation and surviving read-loan stability.
Checked exchanges use current shared cells and have exact XCHG/compiler-byte
bridges. Arbitrary finite exchange-only schedules prove value chaining and
multiset conservation; symbolic witnesses cover every old/new pair. This
prerequisite still lacks mutable worker contexts and lifecycle scheduling,
protected invariants, counter algorithms and concrete ordering/runtime
refinement. Next connect handle ownership and private old results to actual
per-instruction worker dispatch and join. See [shared-handle scope](atomic-handles.md).

Specify real thread start/join, argument publication, ownership transfer,
creation failure and partial cleanup. Use sequentially consistent atomics first,
with a proved mapping to the chosen machine model. If libc/pthreads is used,
validate its relevant bytes or expose its contract as a remaining assumption.

Workload: shared state, workers performing independently counted increments,
joins, final count and safe reclamation, with failure paths. Prove safety across
all admitted schedules and state additional progress assumptions separately.

Exit: named counter/lifecycle theorems through the full modeled chain; no claim
that testing or SC-only interleavings establishes weak-memory correctness.

### 6. Weak memory, locks, blocking and interference

Add acquire/release and relaxed atomics, compare/exchange, fences, target memory
ordering, publication, mutexes, condition variables and wait/wake. Specify
spurious wakeups, lost-wakeup prevention, interruption, timeouts, cancellation,
process sharing and fairness requirements. Extend signal and scheduling models
where these primitives require them.

Exit: independently specified publication and blocking protocols have appropriate
all-execution proofs/model correspondence, with rejected invalid memory orders
and unsupported guarantees. Safety and liveness claims remain distinct.

### 7. Optional LLVM/source guarantees and richer proof hints

Pin LLVM semantics and implement supported SSA, memory, UB/poison and atomic
constructs. Prove/check source→LLVM, LLVM→LLVM and LLVM→machine relations
separately when those preservation claims are requested. Direct machine-code
proofs remain usable without these layers. Add corresponding machine semantics
and certificates for loops, calls, transformed control flow and vectorization.

Grow GNU C23 and GNU C++26 feature ledgers incrementally. C++ elaboration,
classes, exceptions, templates, standard libraries, modules and coroutines are
separate obligations. General source import needs parsing/elaboration evidence;
a Clang AST dump alone cannot establish source correspondence.

Exit per feature: represented, modeled, executable, proven and artifact-validated
statuses are recorded independently, including exact unsupported cases.

### 8. Program-wide OS behavior and composition

Add processes/signals/IPC, filesystem/durability, networking, async I/O,
time/deadlines, environment/permissions and devices as demanded by workloads.
Extend mapping, TLS, dynamic linking, shared libraries, relocation and loading
only with explicit dependency closure. Model external peers and failures.

Exit per facility: operation contract, native mapping, resource/progress rules,
ABI/link/load obligations, proof evidence and runtime conformance evidence.
No automatic claim of complete POSIX or Linux verification.

### 9. Cost, complexity and restricted optimality

This can proceed from milestone 2 without waiting for all OS coverage. Define
instrumented semantics and counts, prove target bounds, then restricted lower
bounds and certified synthesis/search coverage. Separate work, span, memory,
instructions and elapsed time. Do not claim global optimality from a bounded
search or hardware timing from an ISA step count.

Implemented: exact two-instruction increment/load/store and three-instruction
exchange counts, the increment lower bound for zero input/RAX, and an exact three-instruction first-syscall
count for exit42, plus `2*count+3` for the all-count assembly loop. Any supported
first-syscall candidate requesting exit60/status42 from initial RAX = RDI = 0
needs at least three user instructions; the checked
entry attains that bound. These bounds cover the supported ISA and count no
loading or kernel work. All-x86 optimality and elapsed-time bounds remain out
of scope.

Exit: at least one useful validated function has a target cost theorem; an
optimality claim also quantifies over a specified candidate class and includes
an attaining witness. See [cost model](cost-model.md).

### 10. More targets, automation and trust reduction

Add architectures/OS adapters only with explicit models and capability tables.
Verify concrete runtime/library implementations, improve proof certificates and
checkers, and investigate a verified-kernel platform as a separate route.
In parallel, [ingest concrete OS builds](os-implementation.md) and prove selected
kernel/runtime/driver components implement their contracts at machine level.
Compose those proofs to remove specific OS assumptions. Record checked failures
in the [private findings workflow](findings.md), with no promotion of timeout or
unsupported analysis into a vulnerability claim.
Do not transplant a seL4 theorem onto Linux. Address JIT/self-modifying code,
security/noninterference and detailed time only as separately scoped projects.

Exit per extension: proof composition and trust ledger identify exactly which
assumptions were discharged and which new ones were introduced.

## Workstreams and parallelism

Independent specialists can work on semantic foundations, source languages,
LLVM, ISA/decoding, ELF/ABI/loading, OS/resources, concurrency, validators,
costs, and proof/build tooling. Each owns bounded modules and proof obligations;
interface reviews precede integration. More workers do not remove dependencies
or establish the adequacy of a model by consensus.

Run parallel research and prototype spikes before library choices; pair each
implementation with an independent semantics/proof review. Scale later workers
across feature/target matrices only after the core interfaces are stable. Keep
one integrator responsible for cross-layer observations, assumptions and proof
composition, so individually proved components describe the same execution.

## Risks and decision gates

| Risk | Required response |
| --- | --- |
| Incomplete/changing C++/GNU/LLVM semantics | Versioned restricted subsets; feature-level scope and rejection |
| Pointer/memory mismatch across layers | Explicit object/address/provenance relations before optimization proofs |
| Weak-memory or scheduler assumptions hidden | Cross-layer event model; separate safety/progress and declared fairness |
| Final binary differs from modeled assembly | Exact-byte decoding and link/load validation |
| OS/kernel/library contract is mistaken | Contract review, primary specifications, conformance evidence and visible assumptions |
| Proof search does not scale | Small slices, compositional invariants, checked certificates and profiling |
| Vacuous theorem or unsupported input accepted | Nonemptiness witnesses, independent specifications, adversarial certificates |
| Reuse project incompatible or outside scope | Bounded evaluation with a written adopt/port/rebuild decision |
| Lower-bound claim changes with instruction set | Fix the candidate/cost model and reprove after capability changes |

## Completion reports

Each milestone report must list named theorems and their hypotheses, exact
supported constructs and platform profile, artifact bindings, remaining trusted
components, reproducible commands and meaningful negative checks. Tests check
independent behavior and plausible regressions; they do not substitute for
proofs or repeat the implementation as expected results.
