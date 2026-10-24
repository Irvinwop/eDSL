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

The APIs below compose these annotations over the production scheduler.
Returned-run theorems apply to a supplied successful execution. Ranked completion
constructs one finite returned execution from present admission, exact worker
slots and empty queues. It can then establish the two-worker value, byte frame
and logical resource cleanup for that same execution. The complete corpus
certificate gates remain open, so coverage is unchanged. None of these results
asserts that every scheduler returns a worker.

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

For logical resource cleanup after an actual returned execution, import
`EDSL.Corpus.V1.CounterRetirement`. `counterCohort_retireAll` derives current
cleanup admission and capability separation from the original manifests,
initial empty queues and the same successful schedule.
`two_completed_retired_total` carries the modular RAM sum through that actual
cleanup. The three generic lifecycle modules provide the reusable operations
and proofs; see [Worker resource cleanup](resource-cleanup.md) for admission,
outputs and limits.

## Preserve RAM outside the counter

Import `EDSL.Corpus.V1.CounterFrame` for `two_completed_frame` and
`two_completed_total_frame`, in `CounterCommon`. For an actual finite returned
pair, initial empty queues and the independently registered common cell derive
byte equality outside that cell's modular eight-byte span. The precise query
condition is `8 ≤ (query - cell.address).toNat`. The combined theorem retains
the modular total above and this byte frame for the same final RAM.

The generic `Mixed.Cohort.schedule_frame` proof obtains actual RMW addresses
from checked authorization and the stable cell registry. Clients supply the
observed cell identities, not desired operand addresses or a future RAM frame.
Current caller-only issue evidence handles ordinary instructions and RET;
cohort closure retains empty queues through the same actual schedule.

An inherited FIFO may still drain writes. The earlier count and value APIs
permit those queues under their stated profiles; this stronger byte-frame API
requires them to be initially empty.

## Construct a finite returned execution

Import `EDSL.Corpus.V1.CounterCompletion` for the following `CounterCommon`
APIs:

| API | Inputs and result |
| --- | --- |
| `counterCohort_complete` | Independently admitted subjects, exact slots `0..n-1`, a well-formed initial state with exactly `n` workers, empty queues and arbitrary per-thread AF choices yield an actual finite returned schedule |
| `two_complete_total_frame` | Two independent admissions in slots zero and one, exactly two workers, empty queues and one registered common target yield that schedule, its modular sum and its outside-byte frame |
| `two_complete_retired_total_frame` | The same initial inputs, cleanup shapes and capability separation additionally yield actual production resource retirement, capability revocations and preservation of the result and byte frame |

The compiler adapters select existing local rules and rank laws directly from
each independent `Pre`. The initial invariant comes from that admission;
clients do not provide a future successful schedule, a returned state, a desired
result or a termination oracle. Different compilers may be selected only when
their independent loaded-code admissions hold together in the same initial
state; the APIs do not arrange such a combined image.

The returned `RankedCohort.Suffix` contains actual scheduler execution,
well-formed final state, empty final queues, actual returned workers, retained
per-worker histories and typed retirement positions. Every AF value follows
that thread's own issue index. Its `issue_upper_bound` bounds the length of the
constructed issue-only trace by the initial sum of ranks. This proves existence
of one finite completion for every choice function, with no fairness premise.
It does not force an arbitrary scheduler to finish, compute a minimum number
of operations or measure CPU time. The proof does not add a native execution
witness or corpus certificate.

## Reuse the completion infrastructure

The `EDSL.OS.TSO64.EffectSimulation` umbrella exposes the generic layers;
none imports a frozen counter client or grading:

| Direct import under `EDSL.OS.TSO64.EffectSimulation.Mixed` | Reusable contract |
| --- | --- |
| `LocalInvariant` | Retain the every-node invariant on the same explicit ghost through actual steps and traces |
| `RankedLocal` | Positive local ranks, idle stability and strict decrease on actual own retirement; current running-worker enabledness |
| `RankedPotential` | Finite sums of Nat measures, pointwise nonincrease and one-component strict decrease |
| `ChoiceTrace` | Issue-only AF choices from arbitrary per-thread offsets and concatenation for interleaved threads |
| `RankedCohort` | One subject per actual slot; finite returned completion and an issue upper bound from present current invariants |
| `RankedPrefix` | Retain exact collective ghosts across an executed prefix and construct its finite completion with continuous per-thread choices |
| `CohortFrame` | Byte preservation outside a registered common cell through an actual caller-only schedule |

For another program, provide its checked mixed graph, independent entry and
postconditions, and `LocalRules` with an invariant at each node. These reuse
the existing scheduler and local-invariant fold. To construct completion, also
prove `RankLaws`: positivity at running nodes, equality under authenticated
idle extensions, and strict decrease for both running successor continuations
of an actual retirement. Assemble subjects with a common profile and RMW
family, exact exhaustive slots and caller-only policy. With present empty
queues, `RankedCohort.complete_from_current` works from the current ghosts and
arbitrary choice offsets; `complete` starts each offset at zero. The generic
fold preserves each subject's own full history through the same actual steps.

After an interleaved prefix has executed, `RankedCohort.complete_after_prefix`
lifts its exact current ghosts and constructs a new suffix. It proves execution
and choice accounting for the concatenated trace. Only the prefix is supplied
as a successful run; the future suffix follows from the current invariants and
ranks. Its action bound is the prefix length plus the potential at the cut.

`ChoiceTrace.chosen_append` accounts for every thread's issues in the entire
prefix, including repeated and interleaved issuers. The separate
`EDSL.Grading.ConcurrentTask.ChoiceTrace` bridge proves that the zero-offset
predicate equals the existing Plain64 grading predicate. OS modules have no
grading dependency. Program-specific functional results, target-cell evidence
and lifecycle admission remain separate obligations.

All results retain the existing long-mode/CET-off, coherent scalar WB RAM,
stable translation/no-alias, ownership and protected-loan assumptions. Complete
corpus admission, source/compiler preservation, physical CPU/Linux and native
join correspondence remain separate work. No fairness, minimum-operation or
whole-system security guarantee follows from these model theorems.
