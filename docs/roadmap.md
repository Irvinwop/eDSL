# Roadmap and acceptance gates

eDieSeL aims to verify programs, kernels, operating systems and security
properties against independent contracts over their exact final machine code.
The implemented foundation is a restricted x86-64 userspace verifier in Lean 4.
General source-language semantics, native kernel verification and physical CPU
refinement remain future work. See [implementation status](implementation-status.md)
for present support and [coverage](coverage.md) for the relevant APIs.

## Current scaling priority

Expand reusable verification against the unchanged
[40-function GCC/Clang corpus](compiler-corpus.md). Current conditional coverage
is **16/40 functions and 32/80 artifacts**, including **one distinct concurrent
function** under the managed closed-batch model. Both compiler outputs must
meet the independent contract before a function counts. Compilation, extraction,
decoding and native tests are separate evidence.

The next synchronization targets are `c_atomic_load_acquire64` and
`c_atomic_store_release64`. The shared machine trace refinement and
[C23 atomic event constraints](c23-atomic-events.md) are foundations; these
functions still need a complete machine call adapter, universal operational
ordering for acquiring interfaces and complete final-file binding.
[Call contracts, finite publication and order weakening](atomic-call-contracts.md)
provide reusable foundations;
the existing trace verifier checks each supplied finite graph with the full
legality checker. The universal no-acquire theorem below is a separate API.
The [shared load/store method family](managed-plain-methods.md) supplies body
progress, interference closure, indexed access/RET origins and finite call-cohort
extraction and whole scanner/call correspondence without per-compiler execution
proofs.

Published-position monotonicity, per-worker FIFO issue/publication order
and [pending selection rank bounds](checked-atomic-traces.md#pending-writers-and-fifo-order)
are shared across arbitrary traces. General own-pending/published view monotonicity
and same-thread mixed store/RMW publication order are proved for the finite
execution model. Actual access authority and source-writer ranks connect those
views to identity-based RF writer rows. Reusable
[publication coverage](checked-atomic-traces.md#publication-coverage) bounds
every actual target view of the writing thread at its instruction's successor
cut. Access authority extends the bound to earlier cuts; the load corollary
retains the exact source writer identity, including across different cells.
These execution-level APIs allow nonempty initial mixed FIFOs.
`AtomicTrace.verify` retains its empty initial-queue boundary.
[Exact-source load transfer](checked-atomic-traces.md#exact-source-view-transfer)
propagates these numerical views through actual published reads and own
forwarding, including other-cell views and current handle aliases.
[Exact writer successor views and operational coherence](checked-atomic-traces.md#writer-successor-views-and-operational-coherence)
and [generic read sides](checked-atomic-traces.md#read-sides-of-loads-and-rmws)
give same-cell write/read and read/read source-rank bounds and strict read/write
rank order across cells, including RMW reads. Actual RMW sources are same-cell
publication predecessors, with global rank gaps allowed. These operational
coherence and predecessor results start the publication map empty; writer
successor views accept arbitrary incoming metadata.

[Structural well-formedness](checked-atomic-traces.md#structural-graph-well-formedness)
follows from `Built` alone. An actual scan with initial resource invariants,
sequenced queues, final quiescence and complete structural mapping forms
`Graph.Executed`, which supplies [universal all-row sequencing coherence](checked-atomic-traces.md#universal-graph-sequencing),
no-future sequencing and RMW predecessors. Initial quiescence is not a premise:
ordinary incoming entries and views outside graph access events remain permitted.
Every managed publication must still have an in-run event. This mapping excludes
incoming managed entries and gives their drains no invented instruction origins.
Actual initial registry/RAM enumeration remains separate from structural `Built`.

[Universal finite-fragment legality](checked-atomic-traces.md#universal-no-acquire-legality)
is proved for every `Executed` context with `orders.noAcquire run.events = true`,
including `Orders.relaxed`. Absence of acquiring annotations excludes
synchronizes-with (SW), so happens-before (HB) reduces to sequencing.
This uses execution constraints and structural mapping
without a graph-legality checker. The Boolean checks declared annotations, not
machine bytes; a false result leaves HB obligations open. Acquiring semantics
are never silently lowered. `verify` retains its full-checker behavior, and
corpus credit is unchanged.

The next universal obligations are justified declared release/acquire and
release-sequence mappings, coherence over all resulting HB paths, HB acyclicity
and no-future-HB reads. General acquiring-fragment legality, graph-construction
totality and repeated invocations remain open. Full C23/frontend semantics,
source/compiler preservation, native/kernel correspondence and fairness remain
separate capabilities.
The [blocker report](corpus-blockers.md) identifies later instruction, memory
and synchronization gaps. Keep the frozen inputs and denominator unchanged;
new configurations require a new corpus version.

## Design commitments

- Implement semantics, eDSLs and proof infrastructure in Lean 4, using the
  `EDSL` library namespace.
- Treat compiler, assembler and linker output as untrusted. Prove the desired
  behavior directly over final bytes; source/IR preservation is an optional
  additional guarantee.
- Include OS resources, ownership, effects and synchronization in contracts.
  State physical platform and native runtime assumptions explicitly.
- Fail explicitly on unsupported operations or guarantees. Independent
  specifications, admitted-state witnesses and audited proofs define success.
- Keep security findings and their evidence private. A failed proof, timeout
  or unsupported input does not establish a defect.

## Dependency graph

| Remaining capability | Required foundations | Evidence needed to close the gap |
| --- | --- | --- |
| More compiler-output functions | Exact ISA rules, shared VCG, independent specifications and resource adapters | Both frozen compiler windows certified with useful admitted inputs |
| Writable loops and richer calls | Current ownership, actual memory effects, stack/alias frames and loop invariants | All admitted executions satisfy result, safety and return-resource contracts |
| More concurrent methods | Current actor authority, real event origins and allowed interference | Independent object histories, real-time order and explicit progress scope |
| Universal acquiring-fragment legality | Structural graph well-formedness, all-row sequencing coherence, RMW predecessors and exact-source view transfer | Justified release/acquire and release-sequence mappings; all HB coherence, acyclicity and no-future-HB obligations |
| Native memory-order correspondence | Existing FIFO/locked-operation models plus a defined target relation | Refinement to the selected published machine model; separate source-order proofs |
| Whole-program OS behavior | Loader/ABI closure, resource identities, failure and asynchronous effects | Composition over all reachable code and declared external contracts |
| Concrete kernel/runtime components | Exact deployed builds, privileged ISA, interrupts and shared invariants | Implementation proofs discharging the same contracts used by clients |
| Broader security properties | Explicit observations, attacker/environment model and component composition | Named safety or relational theorems with feasible assumptions |

Exact code, independent semantics and current access authority underpin every
track. Source/LLVM frontends are optional dependencies of source-preservation
claims. Cost proofs can grow alongside functional verification.

## Remaining capabilities

### Reusable binary verification

Extend the [VC generator](reusable-checker.md), sparse cutpoints and shared
[scalar](pure-call.md)/buffer resource adapters according to measured blockers.
Factor repeated instruction reasoning without hiding program-specific invariants,
termination ranks or mathematics. The initial read-only CFG profile remains
bounded; static graph admission alone proves no functional result.

Broader writable effects, indirect control flow, recursion and interprocedural
automation require explicit new rules. General invariant inference, automatic
resource-witness construction and an unregistered general-purpose certifier
remain tooling work. Existing spec-indexed [ELF certificates](elf-certificates.md)
provide a library interface, not that complete importer/CLI.

### Memory, ownership and concurrency

Extend allocation/loan composition, region splitting, mutable borrowing and
language-object/provenance relations. Native allocator failure/cleanup and
thread creation, publication, context switching and join remain external
contracts. Proof-level IDs do not authenticate native actors or enforce access.

Shared qword histories identify actual store issues and the newest publication
or RMW supplying a managed load, with explicit initial RAM/queue boundaries.
Grow beyond finite complete-call histories and the managed closed cohort:
pending calls, richer peers, other-cell event projection and mixed effects need
separate composition proofs. Compound uninterrupted equivalence does not prove
linearizability under interleaving. A callable spinlock with ordinary-store
release needs ownership transfer and FIFO publication; an XCHG-release proof
cannot supply that guarantee.

The [managed-word trace refinement](word-tso-refinement.md) covers an independent
uniform64 memory fragment. Extend it to a justified correspondence with the
complete selected published x86-TSO model before claiming that broader result.
The [checked atomic-trace API](checked-atomic-traces.md) extracts complete
managed accesses, writer identities and publication-based graphs for finite
successful runs with declared interface orders. Extend universal mapped-run
legality from the no-acquire fragment to acquiring interfaces by proving the
release-sequence/SW mapping and every resulting HB obligation. Authenticate the
initial registry/RAM manifest separately, preserve complete publication coverage
and justify source-to-interface annotations. Graph-build totality remains a
separate obligation. Add compare/exchange and fences only with justified mappings.
Extend private futex protocols beyond the current policies to blocking
acquisition, multiple waiters, interruption,
timeouts, cancellation and process sharing. Separate safety, enabledness,
constructive completion and eventual progress assumptions.

### Processes, operating systems and kernels

Extend restricted ELF loading with justified relocation/linking, startup state,
TLS and reachable runtime dependencies. Add descriptor lifetimes, retries,
signals, IPC, filesystem/network effects and devices as required by workloads;
include resource exhaustion and partial failure.

Use the [OS implementation plan](os-implementation.md) to prove selected concrete
runtime or kernel paths. Privileged instructions, translation, interrupts,
preemption, devices and boot invariants are additional semantic work. Component
proofs must compose under the same memory/resource model and discharge named
client assumptions before broader OS claims follow.

### Security-property verification

Build on current access-authority, memory-frame, lifetime and synchronization
proofs to specify isolation, information flow and other security behavior.
Noninterference, attacker-controlled interaction and speculative or timing
observations each need an explicit model and theorem. Current conditional
resource proofs establish no whole-kernel or distribution security result.
Checked violations need feasible states and justified properties; use the
[findings workflow](findings.md) to distinguish them from analysis failures.

### Optional source/IR guarantees and additional targets

Pin the GNU C23, GNU C++26 and LLVM subsets before adding parsing, elaboration
and preservation proofs. LLVM UB/poison, source object lifetimes, atomics and
C++ runtime features are separate obligations. Compiler-produced fixtures do
not establish a source eDSL or frontend. Other ISAs and OS adapters need their
own semantics, ABI/resource profiles and evidence; external theorems require an
explicit checked bridge. See the [research map](research-map.md).

### Cost and trust reduction

Extend exact instruction/read accounting and restricted lower bounds with a
fixed candidate class and an attaining witness. Retired instructions, scheduler
actions, memory use and elapsed time are different measures. Bounded search
establishes no unrestricted optimum; ISA counts establish no CPU timing bound.
See the [cost model](cost-model.md).

Reduce trust through concrete loader/runtime proofs and checked evidence from
external proof search. Retain exact artifact binding, toolchain pinning,
transitive axiom auditing and fresh kernel replay as distinct obligations.
Changes to semantics or candidate classes require revisiting dependent claims.

## Completion reports

A completed capability needs named theorems and exact hypotheses, supported and
rejected constructs, final-artifact binding, useful admitted states, remaining
environmental assumptions and reproducible validation. Report universal proofs,
finite native observations and historical measurements separately. The
[trust boundary](trust.md) defines what each evidence category establishes;
[validation](validation.md) collects maintained commands.
