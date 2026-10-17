# Costs, minimum operations, and optimality

Status: checked instruction counts and restricted lower bounds, plus a plan for
richer costs. The x86-64 profile proves two-instruction function results, a
three-instruction first-syscall result and a counted loop's `2*count+3` cost.
Matching lower bounds apply to specified
input and initial-state cases within the supported ISA; see [coverage](coverage.md) and
the [process exit contract](process-exit.md). The original
[abstract example](../EDSL/Examples/Increment.lean) is retained. No complete-ISA
optimum or timing bound is proved.

## What can be proved

Yes: a formal model can establish exact counts, upper/lower bounds, and sometimes
optimality. The claim must name the operation, input domain, permitted programs,
execution paths, and machine/environment assumptions.

| Quantity | Example theorem | Additional requirements |
| --- | --- | --- |
| Source operations | A loop performs exactly `n` additions | Loop semantics, input bounds, termination proof |
| Target instructions | Every terminating run retires at most `f(n)` modeled instructions | Exact code, control flow, ISA step model, call/runtime accounting |
| Memory work | At least `n` unknown input cells must be inspected | Restricted access model, no precomputed summaries/side information, information-dependency proof |
| Comparison complexity | Finding a maximum needs at least `n - 1` comparisons for `n >= 1` | Comparison-only model, arbitrary ordered inputs, all legal algorithms quantified |
| Concurrent work/span | Total work is `W`; critical path is at least `D` | Event/dependency model, distinction between program, scheduler and kernel work |
| Space/resource bounds | Peak live owned memory is at most `b(n)` | Allocation, deallocation, sharing, failure and runtime overhead model |
| CPU cycles or elapsed time | Execution takes at most a stated bound | Microarchitecture and environment bounds; ISA semantics alone are insufficient |

For the comparison example, each nonmaximum candidate must lose a comparison.
A comparison eliminates at most one candidate, giving a route to an independent
`n - 1` lower-bound proof. That argument does not establish the minimum number
of SIMD instructions on x86-64.

## Define the optimization problem first

A proposed theorem needs these parameters:

1. A nonempty set of admitted inputs and a specification of correct outcomes.
2. A candidate language/ISA, operand widths, memory and initial-state rules,
   available constants, lookup tables, libraries, parallelism and precomputation.
3. A cost function over executions, including which instructions, calls,
   accesses, allocation, synchronization, retries and kernel work count.
4. A quantifier: exact per input, best case, worst case, expected cost under an
   explicit distribution, amortized cost over a sequence, or per-thread/total work.
5. A completion requirement. Ignoring diverging runs can give a nonterminating
   implementation an attractive but meaningless cost claim.

Do not collapse operation count, instruction count, micro-ops, memory traffic,
and elapsed time into one quantity. An instruction can have multiple effects,
a vector instruction can handle multiple values, and one ISA instruction can
perform an unbounded retry or substantial hidden work under another model.

## The theorem shapes

For a selected finite-execution model, write `Correct p` for independently
specified total correctness and `Cost p input run` for the selected metric.
A lower bound concerns every correct candidate and its relevant runs:

```text
for every p in CandidateClass,
  Correct(p) implies WorstCaseCost(p, n) >= LowerBound(n)
```

An optimal implementation also needs a witness attaining that bound and a proof
that it is in the same candidate class. Showing a candidate is shorter than
compiler output proves an improvement over that output, not a global minimum.
For nondeterminism, choose carefully whether the bound covers all schedules,
only fair schedules, a worst-case environment, or an explicitly probabilistic
model. Define worst-case cost over diverging executions, rather than discarding
them. State nonemptiness and resource feasibility so the claim is not vacuous.

Functional refinement does not automatically preserve cost. Unobserved extra
work can preserve output behavior. Use cost-instrumented semantics and prove a
cost-aware simulation or a separate target-level bound. Source-level bounds
must not be reported as executable instruction counts without this connection.

## What the repository currently proves

The machine execution relations count supported user instructions. Function
execution includes the terminal `RET`; first-syscall execution includes
`SYSCALL` and stops at the userspace request boundary. Loading, privileged
execution, kernel cleanup and waiting are outside these counts.

| Checked result | Candidate and initial-state scope |
| --- | --- |
| Increment, load32 and store32 exact cost: two instructions | Their checked byte profiles, for every admitted function entry; includes return-stack and memory preconditions |
| `Write32.minimum_modeled_instructions`: at least two instructions, attained by `89 37 c3` | Any actual returning candidate in the current sequential ISA satisfying the independent word-store Pre/Post on a useful input, where old value differs from requested low32 value; includes RET |
| `StoreReturn32.minimum_modeled_instructions`: at least three instructions | Any actual returning candidate under the registered ordinary-store raw policy and independent pointer-store Pre/Post, with a useful value change and initial RAX different from the target; includes RET |
| `Exchange.atomic_execution`: exactly three instructions and one RMW event | Every admitted `exchange32` function entry, including supported atomic operand, disjoint code/stack and readable return; no latency or minimum-cost claim |
| `FetchAdd.atomic_execution`: exactly three instructions and one modular-add RMW event | Every admitted `fetch-add32` entry with its atomic operand and code/return-stack conditions; includes arithmetic flags, excludes runtime/kernel work and establishes no optimality |
| `Increment.zero_input_lower_bound`: at least two instructions | Every supported terminating function execution producing the increment result from zero input and zero initial RAX |
| `Exit42.reaches_request`: exactly three instructions | Its twelve checked entry bytes, every modeled initial register/flags state and admitted code mapping |
| `Exit42.zero_register_lower_bound`: at least three instructions | Every supported first-syscall execution from initial RAX = RDI = 0 requesting raw exit60 with status42 |
| `Process.viaWrite_results`: exactly eight user instructions | Every completed bounded stream-write/exit execution for its checked bytes, including partial/error returns; excludes kernel and waiting steps |
| `IncrementLoop.actual_bytes_correct`: exactly `2*count+3` | Every 64-bit initial RCX count and modular input value, admitted executable bytes and return stack; induction proves termination, including zero count |
| `ArrayMaximum64.GCC.execution_exact`: exactly `7*n+5`; `Clang.execution_accounting`: four for empty input, `6*n+5` otherwise | Complete final 26/32-byte compiler outputs, every admitted full64 array and AF stream, current input/code/caller-slot resources; includes RET and proves original ordered DATA8/STACK8 reads |
| `ArraySum64.GCC.execution_exact`: exactly `5*n+6`; `Clang.execution_accounting`: four for empty input, `4*n+5` otherwise | Complete final 22/25-byte compiler outputs, every admitted full64 array and AF stream; independent sum modulo 2^64, current resources, actual RET and original ordered DATA8/STACK8 reads |
| `CounterThreads.completed_selection_count`: exactly `3*count+3` own selections through completion | Every well-formed entry-phase counter worker with full 64-bit initial RCX, exact locked-add-loop code and retained handle/code/stack resources; successful supplied schedules may interleave peers |
| `MutexReplay.machine_completed_observations`: exactly `13*n+4*busy` instructions | Every completed admitted architectural interleaving of the fixed 37-byte mutex worker, starting with `n` entry workers; a zero-busy schedule attains the `13*n` lower bound |

The [array maximum clients](array-maximum64.md) prove their counts separately
from the registered mathematical result and current-resource policy. Different
loop shapes satisfy the same task with different counts. No lower bound on
comparisons, input loads or arbitrary correct machine programs is established
by those two exact executions; micro-ops and physical timing remain outside
the count.
The [modular array-sum clients](array-sum64.md) similarly prove exact counts
for two complete implementations. These establish no lower bound among all
correct sum implementations.

The word-store bound quantifies over arbitrary candidate bytes and actual
executions, without a CFG, read-only policy or fixed instruction-selection
premise. Any actual returning step is RET and preserves memory; a useful
word-store result must change memory. A returning tail has positive cost,
including after an atomic step, so a correct memory-changing return needs at
least two instructions. `Write32.claim_minimum` derives this bound directly
from the registered `Claim .write32` for any supplied actual execution.

`Write32.exact_two` proves attainment for every admitted `89 37 c3` entry and
AF stream. `resource_exact_two` retains the same actual returned OS history,
current RAM coupling and complete resource frame. `optimal_for_useful_input`
compares that execution against every candidate meeting the same mathematical
input contract. These theorems live in
[`Write32.Accounting`](../EDSL/Grading/Write32/Accounting.lean).
The useful-input condition is essential: the regression proof in
[`Write32Accounting`](../tests/Write32Accounting.lean) exhibits an admitted
already-equal input where RET alone satisfies the raw Post in one instruction.
RET-only code still fails the universal registered task on useful inputs.
This result concerns the present modeled instruction subset and counts neither
micro-ops nor CPU time. Grader acceptance imposes no optimality requirement.

The pointer-return bound additionally requires the registered ordinary-store
`RawPolicy` and an initial RAX different from the target pointer. RET preserves
both RAM and RAX. Each policy-admitted preceding instruction preserves either
RAM (read-only effects) or all registers (ordinary stores), so changing both RAM
and RAX before returning requires at least three modeled instructions.
`StoreReturn32.claim_minimum` derives the post and policy from the registered
`Claim .storeReturn32` for the same supplied actual execution and AF stream.
Candidate bytes, instruction selection and control flow are unrestricted
within that policy and the present sequential ISA.

`StoreReturn32.exact_three` and `resource_exact_three` expose attainment by all
three direct pointer-store shapes, including the actual current OS return and
loan frame. `optimal_for_useful_input` compares them with candidates meeting
the same independent input and policy, useful-value and initial-RAX conditions.
These are separate accounting theorems, not grader acceptance requirements.
See [the lower bound](../EDSL/StoreReturn32/LowerBound.lean) and
[attainment](../EDSL/StoreReturn32/Accounting.lean).

The initial-RAX condition matters: a real useful store/RET execution can satisfy
the pointer post in two instructions when RAX already contains the target.
The [boundary regressions](../tests/StoreReturnAccounting.lean) construct present
admission and actual execution, rather than assuming a successful result.
They also exhibit an admitted already-equal word where pointer-copy/RET meets
the post in two despite an initially different RAX and the same raw policy.
That case shows why the useful-value condition is separately necessary.
The three-instruction bound does not cover atomic profiles, physical x86,
micro-ops, cycles, kernel/runtime work or unrestricted source programs.

The process lower bound is an independent argument about the candidate class:
each supported ordinary step preserves at least one of RAX and RDI, and the
terminal syscall snapshot preserves both. A request for exit60/status42 changes
both zero registers, so two ordinary steps and the syscall are necessary.
`Invokes.changing_two_registers_costs_three` proves this generic bound; the
specific exit theorem derives the register changes from the syscall contract.
The owned entry `mov edi,42; mov eax,60; syscall` attains three. This is an
optimum for that initial-state case within the current supported ISA, not a
claim about all x86 encodings or every initial state. The standalone certificate
admits arbitrary initial registers, but its lower-bound theorem requires the
two zero-register hypotheses.

The process proof also separates three user instructions from OS progress.
Every completed trace of the modeled exit contract reports status42; eventual
completion requires the explicit `LinuxExit.Fair` assumption. An admitted
infinite waiting trace shows why the instruction bound does not imply kernel
termination. Even fair traces have no numerical delay bound.

The counter-worker count includes the zero guard, each iteration's MOV, locked
addition and LOOP, then the final MOV and RET. Only selections of that worker
consume its remaining-instruction variant; peer selections and idle intervals
do not. `completed_event_count` separately proves one addition per requested
iteration, and `completed_total_events` sums those actual events over a finite
completed registry. `finish_collect_counter` constructs a completing schedule
and checked collection. This establishes neither completion for every scheduler
nor a finite waiting/latency bound. Creation, dispatch bookkeeping, join,
contention and kernel work are excluded, and no cheaper-candidate lower bound
is claimed. See [counter-worker scope](counter-workers.md).

The separate [mutex protocol](mutex.md) reuses three-instruction XCHG and
two-instruction payload load/store routines. Its guard and invariant checks are
logical admission conditions, with no machine-code cost assigned to them.
`critical_cycle` constructs a finite protocol execution; it does not establish
a complete instruction-interleaved worker count, lock latency, waiting bound
or minimum-cost mutex implementation.

The subsequent [complete-worker proof](mutex-workers.md) establishes
`13 * workers + 4 * busy exchanges` user instructions for every completed
admitted architectural interleaving from an entry cohort. `schedule_potential`
derives the count from actual instruction dispatch and real 1→1 exchanges;
`completed_cost` needs no final-value checker. Architectural lifting carries the
result to the instruction-only machine. `machine_entry_minimum` proves that all
completed entry executions take at least `13 * workers` instructions, and
`machine_entry_completion` constructs a
zero-busy schedule attaining that bound. The candidate class here consists of
schedules for the same fixed routine, not alternative programs.

From any admitted intermediate state, `machine_completion` constructs a
finishing schedule with no new busy exchanges and exactly the remaining
`potentialSum`, bounded by `15 * workers` future instructions. Readiness and
invariant preservation enable every chosen unfinished step. This establishes
an available completion path, not completion for all schedulers. Runtime/kernel
work, cycles, elapsed time and minimum operations over other implementations
remain outside these results.

The separate buffered scheduler records retired user instructions, blocked
locked issues and FIFO drains as different observations. `retiredCount` counts
only the first category. `MutexTSO.completed_observations` now transfers the
`13*n + 4*busy` retired-instruction result to every completing admitted buffered
trace. Queue/credit conservation proves exactly `2*n` actual drains: each issued
store is either still pending or has drained once, and actual completion
implies empty queues for this routine. Therefore the exact number of abstract
actions is `15*n + 4*busy + blockedCount`. A constructed no-busy, no-stall entry
execution attains `15*n` actions and `13*n` retired instructions, with matching
lower bounds for completing schedules of these same bytes. These action counts
do not measure hardware cycles, micro-operations, runtime or kernel work.

The concurrent syscall wrapper counts actual SYSCALL entry as one retirement.
Its resumption, parked selections and idle retire none, alongside the existing
separate drain/stall observations. Fresh-call frontier growth equals actual
entry observations. These counts exclude kernel work and do not bound service
completion or waiting. See [the syscall boundary](concurrent-syscalls.md).

The original tiny abstract machine has only `add amount`, natural-number inputs
and unit instruction cost. Its checked increment implementation has length one,
and every candidate meeting that contract has length at least one. This example
illustrates the quantifiers independently of the x86 results.

## Planned proof and tooling work

1. Extend the existing instruction counts with execution events carrying
   nonnegative costs, path composition, finite and infinite-run accounting,
   and lemmas for sequential composition and loops.
2. Extend the checked counted-loop proof to calls, more branch conditions and
   memory loops, keeping the counting boundary and admitted environment explicit.
3. Implement a restricted straight-line candidate grammar and prove search
   coverage for a finite size bound. An untrusted synthesizer can suggest a
   candidate; Lean checks semantics and the absence of cheaper candidates.
4. Require a coverage/completeness proof before describing bounded exhaustive
   search as optimal within its grammar. An SMT `unsat` result needs a supported
   checked certificate; a timeout gives no bound.
5. Develop useful lower bounds with independent arguments: dependencies,
   comparison decision trees, adversaries, or information flow, matched to the
   exact candidate model. Some global optimization questions are undecidable;
   support restricted claims rather than promising a universal minimizer.
6. Add shared-memory event costs, retries, contention, allocation and kernel
   work after their semantics exist. The present syscall instruction count
   includes none of that work. Fairness can imply eventual scheduling without
   any finite bound on when scheduling occurs.
7. Evaluate microarchitecture-aware analysis separately. Pin CPU model, cache
   and predictor assumptions, frequency and interference bounds, interrupt and
   page-fault behavior, device delays and scheduler policy before claiming time.

[Souper](https://github.com/google/souper) is a research reference for
SMT-assisted LLVM superoptimization; its original repository is archived.
[Alive2](https://github.com/AliveToolkit/alive2) informs bounded LLVM validation.
Neither supplies a Lean proof of global optimality.
[llvm-mca](https://llvm.org/docs/CommandGuide/llvm-mca.html) estimates performance
using scheduling models; estimates and benchmark measurements are evidence for
model selection, not universal timing theorems.
