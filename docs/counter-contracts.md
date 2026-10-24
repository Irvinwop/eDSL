# Compiled counter verification

The complete frozen GCC and Clang `c_counter_worker` windows have per-worker
annotations against the production TSO64 scheduler. For every admitted actual
finite schedule whose selected worker has returned, the proofs establish exactly
`iterations.toNat` unit increments and the common void-call return contract.
They cover every unsigned 32-bit iteration count, arbitrary upper RSI bits and
initial flags, and well-formed incoming FIFOs.

| Direct import | Complete window | Public APIs |
| --- | --- | --- |
| `EDSL.Corpus.V1.CounterGCC` | 49 bytes / 17 nodes | `rules`, `annotations`, `entry_of_pre`, `completed_count` |
| `EDSL.Corpus.V1.CounterClang` | 86 bytes / 28 nodes | `rules`, `annotations`, `entry_of_pre`, `completed_count` |

The namespaces match their modules. `entry_of_pre` derives the current Entry
from the common independent `Pre`; it takes no future run or generated block.
The builders use canonical caller and original-stack facts supplied by that Pre.
GCC retains both RET paths and its two-increment loop; Clang retains the
remainder loop, eight-increment loop and zero-remainder path with arbitrary RDX.
Their complete checked graphs are described in [mixed instruction graphs](mixed-cfg.md).

The two-worker final-value theorem below composes these annotations over one
actual production schedule. Lifecycle/join, constructive completion and the
complete corpus certificate gates remain, so coverage is unchanged. Successful
finite-run correctness does not assert that every scheduler returns a worker.

Import `EDSL.Corpus.V1.CounterAssertions` for the common assertions, in namespace
`EDSL.Corpus.V1.CounterCommon`:

- `Call` independently names the pointer, unsigned 32-bit iteration count,
  atomic target cell and return address. `Site` fixes the compiler window and
  original worker/resources. `descriptor` reuses the complete checked graph.
- `Pre` requires current loaded code, well-formed resources, running entry PC,
  RDI, low32 RSI, protected caller stack, a canonical return target and the
  scheduler's actual first matching atomic selector linked to the target cell.
  It requires no future execution, initial shared-word value, empty FIFO,
  upper32 RSI value, or initial flag value. Actor and worker index are distinct.
- `LiveData` carries the pointer, caller stack, saved ABI context and current
  selector. `OwnIncrements` authenticates every earlier own RMW with its real
  typed issue and compiler-specific ADD or INC tag, along with unit delta and
  independently named actor, pointer and target.
- `Inv` combines those shared facts with compiler-local register arithmetic,
  parameterized by the exact natural-number count of the full history.
  `Inv.idle` preserves them through authenticated peer issues, FIFO drains and
  unchanged own blocked attempts.
- `Post` requires exactly the requested number of own RMWs, authenticated unit
  increments, actual returned phase and caller PC, callee-saved registers,
  nonarithmetic flags, and the original RSP plus eight in modular Word arithmetic.
  It makes no RAX-result or current shared-memory assertion. `stablePost` allows
  later idle positions; `completed_count` projects to the entire observation
  list of a successful finite returned schedule **given separately proved
  compiler annotations and current Entry**.

The shared `EDSL.Corpus.V1.CounterIncrement` adapter constructs current locked
continuations from the actual selected effect, preserving the complete typed
issue, next frame and context, historical unit-increment witnesses and exact
Nat tally. The compiler modules supply their register arithmetic and graph edges.

`Mixed.LocalRules` combines an idle-stable invariant and one current instruction
rule per graph node. `LocalRules.annotations` generates the existing finite
blocks from the checked depth decrease, so neither compiler repeats scheduler
or block-induction proofs. See [mixed resumption](mixed-resumption.md).

The generic current ordinary-step adapter is in
`EDSL.OS.TSO64.EffectSimulation.Mixed.CallerContinuation` and the public
`EDSL.OS.TSO64.EffectSimulation` umbrella. `One.of_callerContinuation` takes CPU
execution, protected reads and a result continuation for every flag choice.
It derives current authority, read/queue readiness and the real ordinary or
returned finish with the existing FIFO. It has no additional byte-window bound.

`EDSL.OS.TSO64.Increment64` specializes an actual arithmetic machine effect to
INC or encoded ADD-imm8(1). It retains the complete effect, current old/new word,
authorized handle/cell, actual instruction length, RIP, and every GPR. It does
not establish the scheduler's first selector by itself. XADD is excluded.

`EDSL.X86.Sequential.CounterArithmetic` supplies unsigned32 Nat laws for SUB2,
signed ADD-imm8(-8), LEA32(base-1) despite arbitrary upper bits, AND7 modulo eight,
and low-byte AND1 modulo two. Arithmetic parity is separate from the CPU parity
flag; ADD and SUB retain their different flag semantics.

Build the support directly with `lake build CounterContractSupport`. These
modules also belong to the complete catalogue and the fresh certificate gate.
Universal Lean proofs check the stated laws; no additional fixed-value tests
are needed for these adapters.

Import `EDSL.Corpus.V1.CounterCohort` for the common
`two_completed_total` theorem. It takes two independently admitted calls, their
actual initial scheduler slots zero and one, an exhaustive two-worker initial
state, an independently registered common cell and its current initial word.
For an actual successful finite owned-only arithmetic schedule whose two workers
have returned, it derives an actual final RAM read with

`final.toNat = (initial.toNat + left.iterations.toNat + right.iterations.toNat) % 2^64`.

Either worker may use GCC or Clang, and the uint32 requests may differ. Actors
remain separate from scheduler slots. Counts retain every occurrence in the
complete observation list, including identical event payloads. Each worker's
event facts come from its own checked completion proof; no equality between
independently produced stateful ghost histories is assumed. The final RAM value
uses the actual OS history conservation theorem. Nonempty initial FIFOs are
permitted for this value theorem because checked owned-only publications cannot
modify registered atomic allocations.

`EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort` supplies the separate generic
queue-closure API. Independently annotated subjects share a family/profile and
a source caller-only policy law. Present initial Entries, exhaustive live-slot
coverage and empty initial FIFOs derive empty FIFOs throughout the actual run.
Every original action/observation position is retained as an ordinary, RET or
native RMW issue; successful drains and blocked attempts are excluded. Each
subject keeps its own related ghost at the same actual prefix state. Each
subject may have a different instruction graph.

For frozen counter calls, import `EDSL.Corpus.V1.CounterCohortClosure` and provide
a collection of `CohortSubject` values with their present `Pre` and owned-only
profile. `counterCohort` selects the existing GCC/Clang annotations, and
`counterCohort_entries` derives all initial Entries. With exhaustive initial slot
coverage and empty queues, `counterCohort_closed` supplies the generic closure
result. Clients do not reprove instruction rules or scheduler induction.

The supporting `Mixed.IssuePreservation` API extracts the actual current typed
ordinary issue and proves exact queue, store-counter, resource and world
preservation under the caller-only policy, including RET. `Mixed.EventCounts`
partitions RMW occurrences across a duplicate-free exhaustive tid list in Nat,
and connects same-target unit events to the OS history's mathematical input sum.
Neither list arithmetic nor queue closure alone establishes a final RAM value.

Lifecycle/resource release, constructive completion, the complete no-other-writes
contract and corpus certificate admission remain separate work.
An inherited FIFO may still drain writes, so the count assertion does not claim
that the call causes no other shared writes. All results retain the existing
long-mode/CET-off, coherent scalar WB RAM, stable translation/no-alias,
ownership and protected-loan assumptions. They add no fairness, termination,
physical CPU/Linux, compiler-preservation or minimum-operation guarantee.
