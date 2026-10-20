<a id="verification-plan-source-compiler-output-architecture-and-os"></a>

# Verification contracts and proof evidence

eDieSeL proves properties of particular machine-code artifacts under stated
execution and resource models. The current library includes restricted
sequential function verification, exact ELF bindings and specialized OS and
concurrency results. [Coverage](coverage.md) records implemented profiles;
source/IR preservation and broader deployment composition remain future work.

<a id="1-the-statement-we-eventually-want"></a>

## 1. State the independent contract

The primary route is [direct binary verification](binary-first.md). Start with
a requirement independent of the candidate: a mathematical result, permitted
memory effects, resource preservation, I/O behavior or a synchronization
property. Specify admitted inputs and environments before proving the code.
Admission describes present facts; it cannot assume the desired result or a
future successful execution. Useful admitted states must exist.

The general notation below describes proof obligations, not a universal API:

| Object | Meaning |
| --- | --- |
| `B` | Exact executable bytes and relevant code/data dependencies |
| `M` | Selected semantics, ABI/OS profile and artifact scope |
| `P` | Preconditions on inputs, initial state and current resources |
| `R` | Allowed interference and environment responses |
| `Q` | Independent property of observable executions |
| `Obs` | Observations used by the property |
| `S` | Optional source program with pinned semantics for a preservation claim |

```text
For every initial state satisfying P and environment satisfying R,
every covered execution of B in M satisfies Q on its observations.
```

The theorem must say whether it covers execution prefixes, completed runs or
all maximal executions. Returned values, designated memory, I/O, ownership and
specified failures may all matter. Termination, faults, deadlock and divergence
must remain distinguishable: an infinite silent loop cannot masquerade as a
successful terminating execution.

Security properties follow the same discipline. Access-authority and framing
proofs can establish stated resource protections under the model. Confidentiality
or noninterference needs a suitable relation between executions; a functional
result alone supplies no general side-channel or whole-system security theorem.

## 2. Separate the questions being proved

| Claim | Required evidence |
| --- | --- |
| The specification captures the requirement | Independent review, useful inputs and meaningful counterexamples |
| The function satisfies that specification | A semantic theorem for all admitted inputs and machine choices |
| A CFG describes these bytes | Checked instruction partition, decoding and successor facts |
| The theorem concerns this final artifact | Checked complete-file/function binding and current executable-code premises |
| Resource effects are permitted | Current ownership/lifetime facts and preservation at actual execution steps |
| A source program is preserved | Source definedness, import/emission correspondence and source-to-target refinement |
| OS calls and linked code meet their contracts | Matching implementation/composition proofs or explicit external assumptions |
| The program always completes | A termination or temporal argument under stated progress assumptions |

Compilation, a disassembly listing and successful sample runs establish none
of these semantic claims by themselves. A function proof can remain conditional
on a caller or OS contract without proving its native implementation.

## 3. Direct verification and optional compiler-preservation routes

### Direct binary verification: the primary route

The current [reusable checker](reusable-checker.md) generates verification
conditions from production sequential semantics. `VCGen.sound` connects a
proved formula, checked CFG and current code binding to actual modeled
execution. `VCGen.Cutpoints` supports loops through sparse invariants and
strictly decreasing ranks. Shared scalar and buffer adapters connect those
proofs to current caller resources.

There are two proof patterns: construct an artifact-specific Lean proof term,
or prove acceptance by a Lean checker whose soundness theorem yields the
semantic result. Proof search, imported graphs and external hints can remain
untrusted because their evidence is checked. An annotation cannot override the
bytes fetched by the machine model.

A static import establishes structure and binding. The independent result,
permitted reads, ABI frame, current resources and termination conditions remain
client obligations. See [Verify a new function](verify-a-function.md) and
[standalone ELF certificates](elf-certificates.md).

### Translation validation: an additional source-preservation guarantee

This broader route is planned. For exact source `S` and output `B`, prove that
for every permitted input and related initial state, every maximal target
execution has a permitted source execution with related observations and
outcomes under related environments. The relation must couple the same external
inputs and interference rather than invent replies that hide a wrong result.

Also prove that all admitted source executions avoid undefined behavior and
satisfy the desired property. A transfer theorem must show that the selected
observation relation preserves that property. Target divergence and infinite
stuttering require explicit treatment; matching finite prefixes is insufficient
for total correctness.

Certificates could supply block correspondences, invariants, memory mappings,
call contracts and checked witnesses. General source/LLVM import and arbitrary
compiler-transformation validation are not current capabilities. External
validators can suggest evidence but do not supply an assumed Lean soundness
bridge.

### Verified lowering: a complementary route

Future source eDSL subsets can use proved Lean transformations. Pass proofs
still need justified source emission/import, final-byte decoding, ABI/link/load
composition and runtime contracts. Source-to-LLVM, LLVM transformations and
LLVM-to-machine lowering are distinct obligations. The [language plan](languages.md)
describes their semantic boundaries.

All routes distinguish a proved result, a replayed counterexample, unsupported
input, timeout/unknown and an invalid certificate. A solver counterexample is
a candidate until validated. Failure to produce a proof establishes no defect.

## 4. Bind the theorem to the real build

Current standalone scalar ELF certificates are indexed by the independent
specification, complete file bytes and requested symbol name. Checked metadata
selects the actual function; the semantic theorem concerns those same selected
bytes. A useful loaded-call witness supplies present resources at that address,
and the universal theorem applies to every admitted call. File binding alone
creates no caller authority or native startup guarantee.

A broader release/deployment manifest should additionally record:

- Relevant linked code/data, entry points, relocation/load-address policy,
  libraries, stack/TLS setup and permitted symbol resolutions.
- Semantic revisions, ISA features, ABI/OS/runtime contracts, theorem names,
  proof dependencies and the assumption/axiom report.
- Input/resource bounds, permitted interference, thread/schedule scope,
  observations and progress conditions.
- Available build inputs and exact compiler/assembler/linker options for
  reproduction; parsing, preprocessing and language/IR revisions when source
  preservation is claimed.

This consolidated manifest remains a design requirement, not a promised
existing output format. Compiler identity helps reproduce a candidate; direct
machine-code correctness does not assume the compiler is correct.

Bind theorem parameters to byte vectors or proved decoding/selection of them.
A filename or digest alone supplies no equality theorem. Hash-based deployment
adds integrity/collision and replacement-prevention assumptions. Changing the
bytes, specification, selected entry or semantic premises requires rechecking
the relevant proof and binding.

## 5. Close the assembly-to-execution gap

| Layer | Current boundary and remaining obligations |
| --- | --- |
| Function bytes | Checked decoding and execution under current code, caller, memory and profile premises |
| Restricted ELF | Checked loading/selection and exact named-file binding; callable proofs retain current text and resource premises |
| Narrow process models | Selected startup/write/exit results under explicit OS contracts; no general runtime or Linux implementation proof |
| General object/static linking | Future relocation, dependency closure, startup, library, stack and TLS composition |
| Dynamic execution | Future dependency resolution, interposition, GOT/PLT, constructors, TLS and allowed-address proofs |
| Runtime code mutation | Future code-validity and instruction-fetch coherence rules for JIT, patching or self-modification |

A selected-function certificate binds its complete container without proving
all code in that container safe. Foreign calls need result, memory-footprint,
ownership, interference, error and progress contracts. Those contracts remain
assumptions until matched by concrete implementation and composition proofs.
The [platform model](platform-model.md) details the native boundary.

## 6. Concurrency and the OS are semantic layers

Memory safety depends on mappings, lifetime and authority; concurrent behavior
also depends on ordering, interference and thread lifecycle. A sequential
interleaving model cannot establish arbitrary weak-memory behavior. Source
atomics, IR atomics, machine RMWs and OS synchronization need explicit relations
when a theorem spans those levels.

State allowed allocation/thread-creation failures, partial I/O, spurious
wakeups, interruption, cancellation, peer termination and exhaustion. Prove
cleanup/recovery or state the environmental exclusion. External aborts retain
the specified prefix-safety obligation. A lock supplies no automatic fairness
assumption.

| Evidence | Scope |
| --- | --- |
| Native, sanitizer or differential observations | Finite evidence that may expose defects or model disagreement |
| Bounded exploration | Only the stated input, heap, thread, event and step/context bounds |
| Checked finite-state closure | All executions of that finite model, including cycles |
| Inductive safety proof | Executions covered by the invariant and its resource/environment premises |
| Termination or temporal proof | Completion under the stated progress, fairness and interference conditions |

A two-thread proof does not cover arbitrary populations without a parameterized
argument. Race freedom, deadlock freedom, starvation freedom, lock freedom and
wait freedom require different theorems. Liveness transfer needs preservation
of progress/fairness premises or a separate target proof.

The [managed full64 profile](managed-fetch-add64.md) and its
[frozen certificates](concurrent-fetch-add-certificates.md) state their closed
cohort, completed-history, prefix-resource and own-progress obligations. These
model results do not establish native scheduling or Linux enforcement.

## 7. Proof trust policy

Lean checks proof terms against the formal definitions. The intended meaning
of those definitions, the selected kernel/foundations and the computing
environment remain trust boundaries. See [trust](trust.md) for the ledger and
[validation](validation.md) for maintained checks.

Required proof evidence uses pinned dependencies, warnings as errors, audited
transitive theorem axioms and fresh kernel replay. Claims advertised as proved
must contain no `sorryAx`, project semantic axioms or unchecked solver results.
Review hypotheses and useful admission even when the axiom report is clean.

Native evaluation can add compiler/runtime trust beyond ordinary kernel
reduction; it must be labeled and excluded from the strict proof profile.
A passing executable checker is distinct from a kernel-checked acceptance
proof. Environmental and foreign-library assumptions must remain explicit in
the theorem contract/report, including physical exclusions not encoded as
fields in the current modeled state. Hashes and CI results identify evidence;
they do not replace proof terms.

## 8. Dependency order and validation gates

An extension needs independently specified behavior, sound semantics/checking,
useful present admission, exact artifact binding and current-resource
composition before it supports an artifact claim. Broader language or OS claims
also need every relevant preservation and implementation boundary discharged
or explicitly assumed. The [roadmap](roadmap.md) tracks planned work.

Independent behavioral and rejection checks should expose plausible wrong
arithmetic, bad bytes, lost authority, ABI damage or failure-path omissions.
Native conformance checks remain distinct from mathematical proof evidence;
[validation](validation.md) documents how each is reproduced.

## 9. External work: what can be used and what still needs proof

The [research map](research-map.md) collects compiler, LLVM, ISA, program-logic
and verified-kernel references. Reusing a definition, tool or external theorem
requires revision/subset alignment and an audited proof bridge where needed.
Those references do not constitute a source frontend, Lean checker or
end-to-end program/OS theorem in eDieSeL.
