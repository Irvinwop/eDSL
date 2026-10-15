# Costs, minimum operations, and optimality

Status: plan, plus a deliberately small checked example in
[Increment.lean](../EDSL/Examples/Increment.lean). No real ISA or timing bound is
currently proved.

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

The tiny machine has a single instruction family, `add amount`, natural-number
inputs, sequential execution, and unit cost per instruction. Its specification
requires the output to be input plus one for every input.

The checked theorems establish that:

- A one-instruction implementation meets that independent functional contract.
- Every program in that language meeting the contract has length at least one:
  an empty program leaves input zero unchanged and therefore fails.
- The one-instruction implementation attains the bound and is optimal within
  this candidate language.

This is intentionally a small example of the quantifiers. It says nothing
about C overflow, x86 instruction encodings, CPU cycles, Linux, or a compiler's
output. It also does not claim a useful general lower-bound technique has
already been implemented.

## Planned proof and tooling work

1. Add execution events with nonnegative costs, path composition, finite and
   infinite-run accounting, and lemmas for sequential composition and loops.
2. Prove exact/upper bounds for the first validated bitvector function, including
   return and calling-convention overhead under a stated counting boundary.
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
6. Add shared-memory event costs, retries, contention, allocation and syscalls
   only after their semantics exist. Fairness can imply eventual scheduling
   without any finite bound on when scheduling occurs.
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
