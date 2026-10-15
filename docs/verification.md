# Verification plan: source, compiler output, architecture, and OS

Status: proposed design and acceptance criteria. The pipeline described here is
not implemented. Small Lean theorems in the repository establish only their
stated mathematical models; they do not certify a production compiler, binary,
CPU, or operating system.

The intended result is a Lean 4 proof about a **particular executable artifact**
running with a **particular architecture, ABI, and OS contract**. It must explain
which inputs, environment actions, failure outcomes, and schedules it covers.
OS behavior is part of the theorem, including synchronization, memory lifetime,
blocking, interruption, and resource failure.

## 1. The statement we eventually want

Start with an independently defined program specification: for example, every
successful execution of a two-worker counter returns the sum of their work,
each created worker is joined, and every failure path releases resources it
owns. Whether every execution eventually succeeds is a separate question.

Use the following planned objects. These are mathematical interfaces to
design, not existing APIs:

| Object | Meaning |
| --- | --- |
| `S` | A typed source program with a pinned language-semantics revision |
| `B` | The exact final executable bytes, including relevant linked code/data |
| `M` | Artifact manifest, target profile, semantics revisions, and proof scope |
| `P` | Preconditions on inputs, initial memory, resources, and environment |
| `R` | Allowed environmental interference and OS responses |
| `Q` | Independently specified predicate on observable executions |
| `Obs` | Explicit projection from an execution to the observations used by `Q` |

The intended refinement obligation is, schematically:

```text
For every permitted input and related source/target initial state,
and every target environment satisfying the recorded rely contract R,
for every maximal execution t of Load(B, M) in MachineOS(M),
there exists a source execution s in SourceOS(S, M)
under a related environment, such that observations and outcomes match.
```

The environment relation couples the same externally supplied inputs and
permitted interference across both layers; it cannot invent convenient replies
to hide an incorrect output. Source nondeterminism can be resolved differently
by compilation, provided every resulting target behavior is allowed. A proof
about one favorable target run is insufficient.

`SourceDefined(S, P, R)` must establish that **all** source executions covered by
the precondition and rely contract avoid undefined behavior. Then a theorem
that **all** covered source observations satisfy `Q`, together with the above
refinement proof, can transfer `Q` to all covered target executions. Define and
prove this transfer lemma for the chosen observation relation; do not assume
arbitrary predicates transfer through arbitrary erasure of events.

The observations include return/exit values, designated memory visible to a
caller, externally relevant I/O, resource operations, and specified failures.
They distinguish termination, faults, deadlock, and divergence. An infinite
execution with only finitely many visible events must still carry a divergence
outcome; otherwise an implementation that spins forever can appear equivalent
to a terminating source. Prefix safety proofs can use finite traces, while
termination and liveness require additional arguments about maximal executions,
stuttering, and progress.

This is a conditional mathematical result. Applying it to a physical execution
also requires that the CPU, kernel, loader, libraries, and environment satisfy
the recorded model assumptions. A kernel version string is evidence of
identity, not a proof of that conformance.

## 2. Separate the questions being proved

| Claim | Required evidence | What does not establish it |
| --- | --- | --- |
| Specification is the intended requirement | Human-reviewed statement, examples, and independent counterexamples | A theorem whose conclusion repeats its hypothesis |
| Source program implements the specification | Lean proof including definedness and permitted errors | Source type checking or passing example inputs |
| Emitted source represents the Lean eDSL | Printer/parser correspondence or validated translation | Reading a pretty-printed program |
| This compiler output refines this source | Checked artifact-specific certificate or applicable compiler theorem | Compiler reputation, an optimization flag, or executable comparison |
| Linked/loaded program implements the validated code | Checked binary, relocation, ABI, and initial-state obligations | An assembly-text proof alone |
| Program runs correctly with OS services | Runtime refinement plus explicit OS/environment contracts | A pure function proof with syscalls erased |
| Program always completes | Well-founded or temporal argument under stated progress assumptions | Safety, race freedom, or many successful runs |

This separation follows the useful precedent in CompCert's documented
semantic-preservation boundary: its principal compiler theorem concerns source
and assembly representations, while preprocessing, external assembling, and
linking need their own treatment. It is a reference for structuring obligations,
not a claim that CompCert supports this project's GNU C23/C++26 scope.
([CompCert manual](https://compcert.org/man/manual001.html))

## 3. Two compiler routes

### Translation validation: the main route for existing compilers

Accept a compiler as an untrusted producer of candidate code. For each
compilation, attempt to prove a relation between the source semantics and the
produced artifact. The compiler, optimizer, assembler, linker, proof search,
AI-generated hints, and external solvers need not be correct if their results
are independently checked by the proof boundary.

Planned certificate contents include block correspondences, invariants,
simulation relations, memory mappings, call contracts, instruction decodings,
relocation facts, and proof witnesses for generated verification conditions.
Loops require invariants or another induction argument. Optimizations such as
inlining, vectorization, and transformed loops may need certificates unlike
simple instruction-by-instruction matching.

There are two acceptable checking patterns:

1. Produce a Lean proof term of the artifact-specific theorem and have the
   kernel check it.
2. Define a certificate checker in Lean and prove its soundness against
   independently defined semantics. A checked acceptance result then yields
   the artifact theorem through that soundness proof.

Neither route may replace the difficult step with `axiom compiler_correct`, a
`Refines` proposition defined as certificate acceptance, or an assumed theorem
that the imported external solver is sound. A checker is allowed to reject a
correct compilation; soundness comes before completeness or automation.

An arbitrary compiler can be submitted to this workflow, but arbitrary
programs and transformations will not automatically become provable. Results
must distinguish **proved**, **disproved with a checked counterexample**,
**unsupported**, **timeout/unknown**, and **invalid certificate**. A solver's
counterexample is initially a candidate until replay validates it. `unknown`
never means success.

Alive2 is an available external tool for finding LLVM transformation problems
and informing certificate design. Its own documentation excludes
interprocedural transformations; it is not an existing Lean checker of source
to final machine code. Any use must pin its revision and report its bounds and
scope. ([Alive2 repository](https://github.com/AliveToolkit/alive2))

### Verified lowering: a complementary route

For small eDSL subsets, implement transformations in Lean and prove each pass
preserves the required semantics. Composing pass proofs can avoid rediscovering
a certificate per program. This route still needs a justified text/byte emitter,
assembler or decoder relation, linking/loading model, and runtime/OS boundary.

Do not begin by attempting to prove all of GCC or Clang correct. Begin with a
narrow supported subset, use direct machine-code proofs to close the artifact
gap, and add validated intermediate steps where they reduce proof effort.
Source-to-LLVM, LLVM-to-LLVM, and LLVM-to-machine-code are separate obligations.

## 4. Bind the theorem to the real build

Every release proof should carry a machine-readable manifest, with a reviewed
human-readable rendering. Required fields are planned as follows:

- Exact input bytes, transitive included files, preprocessing configuration,
  generated files, and resulting typed source representation.
- Compiler executable identity and revision, complete ordered arguments,
  response-file contents, target triple, CPU features, data layout, optimization
  pipeline, relevant environment, and plugins. Record semantic options such as
  signed-overflow, aliasing, floating-point, exception, and threading modes.
- Exact LLVM revision/IR dialect where used; assembler, linker, linker script,
  startup objects, libraries, LTO inputs, and post-link transformations.
- Exact final artifact bytes; entry points; executable/loadable segments;
  symbol resolution; relocation policy; ABI; stack/TLS initialization; and
  allowed load-address ranges.
- ISA-model revision, CPU feature set, OS-contract revision, kernel/runtime
  identities where relevant, filesystem/environment requirements, and excluded
  asynchronous or external actions.
- Input domain, resource limits, concurrency bounds, scheduler/fairness
  assumptions, observation policy, trusted components, and theorem names.

Bind theorem parameters to the actual byte vectors or a proved decoding of
them. Hashes help identify artifacts and caches, but a bare filename or digest
does not prove that the bytes supplied to a checker or loader match. If a
deployment uses hashes instead of full equality, its integrity/collision
assumption belongs in the deployment argument. A changed binary, library,
profile, or assumption invalidates the old certificate until rechecked.

Compiler identity is recorded for reproducibility and semantic configuration;
the correctness of the compiler executable is not an assumption in translation
validation. Conversely, inspecting the compiler's claimed AST is insufficient
to prove that it parsed the submitted source correctly. The source-import
boundary must itself be checked or explicitly trusted.

## 5. Close the assembly-to-execution gap

Plan distinct proof layers, extending coverage only when each layer has a
defined semantics and a validation gate:

1. **Function bytes.** Decode the exact bytes in a designated code region,
   establish instruction semantics, entry/return conventions, and legal control
   flow. Prove memory accesses and branch targets stay within the contract.
   This proves a function under caller/loader assumptions, not process startup.
2. **Object files.** Parse bounded ELF structures; validate symbols, section
   ranges, alignment, and each supported relocation. Reject overlapping,
   malformed, or unsupported executable content. Disassembler output is a
   hint, not the definition of the binary.
3. **Static linked executable.** Validate final code/data and all reachable
   callees, entry state, startup/termination, segment permissions, mappings,
   stack, auxiliary data, and any initial TLS. Include CRT and statically
   linked libc bytes or explicit contracts with a stated trust boundary.
4. **Position-independent and dynamic execution.** Add proofs parameterized
   over allowed base addresses, relocation application, GOT/PLT resolution,
   symbol visibility/versioning, constructors/destructors, TLS, and loader
   behavior. Bind every dependency and permitted resolution. Preloading,
   interposition, IFUNC dispatch, plugins, and `dlopen` require explicit models
   and closure of the reachable code; reject them before that exists.
5. **Runtime mutation.** JIT compilation, self-modifying code, hot patching,
   and executable memory changes require new code-validity invariants and
   instruction-fetch coherence rules. Exclude them from earlier profiles.

ELF loading/linking and the x86-64 calling convention are separate
specifications, so neither can be inferred from instruction correctness.
([System V gABI](https://www.sco.com/developers/gabi/latest/contents.html),
[x86-64 psABI source](https://gitlab.com/x86-psABIs/x86-64-ABI))

Foreign calls need functional behavior, memory footprints, ownership transfer,
threading effects, and failure/progress contracts. A contract for `malloc`, a
pthread operation, or a syscall wrapper is not a verification of that library's
implementation. Eventually validate concrete implementations against those
contracts; until then show them as assumptions in the result.

## 6. Concurrency and the OS are semantic layers

The same execution must account for language-level atomic rules, compiler/IR
memory rules, architectural ordering, and the OS resource model. Sequentially
interleaving all source instructions is insufficient for weak memory. A shared
counter proof needs a valid atomic lowering and thread lifetime relation, not
just an arithmetic invariant.

Record which outcomes are allowed after allocation or thread-creation failure,
spurious wakeup, interruption, cancellation, signal delivery, peer termination,
and resource exhaustion. Either prove recovery/cleanup or exclude an outcome
through an explicit environmental assumption. Do not silently assume that
syscalls always succeed or that locks guarantee fair scheduling.

| Evidence level | Honest scope |
| --- | --- |
| Native stress, sanitizer, and differential runs | Bugs can be detected; absence of bugs is not proved |
| Bounded exploration/certificate | Only the stated input, heap, thread, event, and step/context bounds |
| Complete finite reachable-state graph with a checked closure argument | All executions of that finite model, including cycles; model size restrictions remain |
| Inductive safety invariant with a sound concurrent logic | Unbounded executions covered by the invariant, with explicit resource/environment premises |
| Temporal/progress proof | Only the stated fairness, interference, and progress conditions |

A proof for two threads does not cover an arbitrary number of threads. A
parameterized theorem over `n` needs its own invariant and proof. A step-bound
result must not be relabeled as unbounded because no counterexample appeared.
Likewise, race freedom, deadlock freedom, starvation freedom, lock freedom,
wait freedom, and scheduler fairness are distinct properties.

For liveness, show that the refinement preserves the relevant fairness and
progress premises, or prove target liveness separately. Infinite target
stuttering cannot be justified by matching only finite source prefixes. For
security properties comparing multiple runs, such as noninterference, add an
appropriate relational theorem; a single-execution refinement result is not a
general side-channel or confidentiality proof.

## 7. Proof trust policy

Lean's kernel checks proof terms, including those built by automation. The
project must still trust the chosen logical foundations, kernel implementation,
and computing environment, and must review whether its formal semantics match
the intended machine. Proof checking does not establish the adequacy of a
badly specified model. ([Lean reference](https://lean-lang.org/doc/reference/latest/))

Planned release gates:

- Rebuild pinned source dependencies and record the Lean version/commit and
  package revisions. Do not accept unreviewed compiled imports as proof evidence.
- Audit exported theorem dependencies with `#print axioms` and a documented
  allowlist for the pinned Lean foundations. Reject `sorryAx`, project-specific
  semantic axioms, and unreported foreign trust dependencies.
- Keep physical-world and external-library assumptions explicit as theorem
  parameters and in the generated report; audit them even when axiom checking
  reports no unexpected axioms.
- Prefer proofs checked by ordinary kernel reduction or proof terms. If native
  evaluation mechanisms add compiler/runtime trust, label that enlarged trust
  boundary and exclude it from the strict proof profile. A passing executable
  checker alone is not the same claim as a kernel-checked acceptance proof.
- Keep proof search and certificate generation outside the trusted argument;
  recheck their witnesses. Cryptographic checksums and CI status are transport
  and workflow evidence, not replacements for proofs.

Lean documents native-evaluation trust separately from kernel validation; the
exact mechanism depends on the pinned release. Use that release's validation
guide rather than assuming a tactic name always has the same trust footprint.
([Validating a Lean proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/))

## 8. Dependency order and validation gates

This order complements the [roadmap](roadmap.md); OS contract design starts at
the beginning even when the first machine-code proof is sequential.

| Gate | Required work before advancing | Independent failure to catch |
| --- | --- | --- |
| V0: semantic foundations | State, steps, finite/infinite executions, observations, UB, preconditions, and transfer theorem | A spinning or faulting target passes a terminating-source claim |
| V1: tiny source and ISA slice | Typed unsigned arithmetic/control flow, precise ABI, decoder, exact function bytes, universal-input proof | A wrong operation, wrong register, truncated immediate, or clobbered preserved register |
| V2: compiler-output validation | Candidate compiler invocation, manifest binding, checked source-to-bytes relation, honest unknown/rejection | A changed byte, source input, flag/profile, or forged certificate reuses success |
| V3: memory and static processes | Object lifetime/provenance, stack/heap bounds, ELF load/link layer, startup, narrow OS calls | Out-of-bounds access, bad relocation, wrong entry state, or unmodeled failure |
| V4: first OS concurrency slice | Thread start/join and failure cleanup, shared memory, supported atomic lowering, weak-memory model | Lost update, data race, premature reclamation, missing join, or unfair-run liveness overclaim |
| V5: composition and richer languages | Modular call/link proof, supported GNU C/C++ elaboration, LLVM revision, runtime contracts | Mismatched layout, invalid attribute, exception/lifetime mismatch, or hidden helper call |
| V6: wider deployment | Dynamic loading, more ISAs/OS contracts, signals/I/O/IPC as demanded by examples | Unbound dependency, unsupported capability, environmental interference, or model-version mismatch |

Use meaningful proof examples and rejection cases at each gate. Compare native
executions to independent specifications to find model errors, but keep such
testing distinct from the formal evidence. Before a gate is met, its status
remains planned or experimental and the missing assumptions remain visible.

## 9. External work: what can be used and what still needs proof

| Reference | Intended role | Missing connection to this project |
| --- | --- | --- |
| CompCert | Study compiler refinement and proof boundaries | Its Rocq theorems and supported C dialect are not Lean GNU C23/C++26 proofs |
| Alive2 | Run external LLVM diagnostics; study transformation certificates | No assumed Lean acceptance theorem or final-binary/OS coverage |
| [Vellvm](https://github.com/vellvm/vellvm) | Study formal LLVM semantics and executable interpreters | A Rocq development; revision/subset alignment and any bridge into Lean require explicit work |
| [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/) | Study C memory/provenance and permitted nondeterminism | Its modeled C fragment and tools are references, not full GNU C23 semantics in Lean |
| Lean kernel and libraries | Implement definitions and check proofs | Still require a reviewed semantics, artifact binding, and explicit external assumptions |

These are existing external artifacts or semantic research references. None is
currently an integrated eDSL dependency or a completed end-to-end proof route.
