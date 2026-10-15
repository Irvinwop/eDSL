# Language and target semantics plan

Status: proposed scope and work packages. No complete GNU C23, GNU C++26, LLVM
IR, assembly, or OS semantics is currently implemented by this project.

The eDSLs are embedded **in Lean 4**. C and C++, LLVM IR, assembly, and OS
operations are the languages being represented and reasoned about. Creating a
Lean value that represents thread creation must not create a host thread.
Small native helpers may eventually use C/C++/assembly, with their effects and
trust boundaries exposed separately.

## 1. Share contracts without erasing differences

Use typed Lean representations for each language and explicit relations
between them. Share vocabulary for bit widths, layouts, calling conventions,
memory/resource identities, events, and OS contracts. Do not force all language
semantics into a single evaluator that treats them as interchangeable.

For each supported construct, the implementation must eventually provide:

1. Syntax, typing/well-formedness, source locations, and target restrictions.
2. Operational or denotational semantics, including failure and nondeterminism.
3. Proof rules for its independently specified behavior and definedness.
4. A lowering relation and its proof or artifact-specific validator.
5. An emission/import boundary tied to actual text or bytes.
6. Capability reporting and a rejection path for unsupported cases.

Every language has a distinct relationship to OS behavior: a C atomic, LLVM
atomic, locked x86 instruction, and mutex operation are related constructs with
different obligations. Runtime calls must expose effects rather than hide them
inside opaque pure expressions.

## 2. Define the supported subset precisely

Track at least these statuses per construct and target profile:

| Status | Meaning |
| --- | --- |
| Planned | A requirement or design exists |
| Represented | A typed AST can describe it |
| Modeled | A reviewed Lean semantics exists |
| Executable | An interpreter/emitter/helper can run it |
| Proven | Named Lean theorems establish the stated obligations |
| Validated artifact | A proof has been checked for particular final bytes and assumptions |

These statuses do not imply each other automatically. Successful parsing,
compilation, LLVM verification, test execution, and proof checking establish
different facts. Public support matrices should identify the precise semantics
revision, platform, features, and theorem names; a `-std` switch is not a
language-support certificate.

The initial target proposal is Linux userspace, x86-64, ELF, and a pinned System
V ABI profile. Begin with a small register-only function, then stack/owned
memory, a static process, and the first thread/atomic/OS slice. ISA and OS models
remain replaceable interfaces so additional targets have explicit proof work.

## 3. GNU C23

The selected dialect is `-std=gnu23`, with a fixed compiler and documented
extension set. GCC defines GNU dialect modes as the base language plus GNU
extensions; implementation options can change the contract, so record them
alongside the source. ([GCC dialect options](https://gcc.gnu.org/onlinedocs/gcc/C-Dialect-Options.html))

Required semantic work packages:

- **Scalar and aggregate values:** fixed-width integers versus C integer types,
  promotions, conversions, signedness, overflow, shifts, division edge cases,
  Boolean values, enums, arrays, structs/unions, bit fields, padding, alignment,
  and target layout. Mathematical integers must not stand in for C arithmetic.
- **Evaluation and control:** sequencing, permitted operand-evaluation orders,
  short-circuiting, assignment, calls, function pointers, branches, loops,
  recursion, scope, and nonlocal control where eventually supported.
- **Objects and pointers:** allocated objects, subobjects, byte representations,
  initialization, effective types/aliasing, provenance, lifetime, pointer
  arithmetic, one-past values, casts, and access permissions. Initially reject
  integer-pointer round trips and other idioms until their chosen contract is
  explicit and matches the pinned compiler profile.
- **Concurrency:** ordinary versus atomic objects, memory orders, modification
  order, reads-from/happens-before constraints, fences, data-race freedom, and
  thread-local storage. C atomics and GNU `__atomic`/`__sync` builtins need
  separately specified interfaces.
- **External effects:** volatile access, inline assembly, allocation, libc,
  pthreads, syscalls, signals, I/O, environment, and resource limits. A volatile
  access alone does not establish interthread synchronization.
- **Additional C23/GNU features:** introduce each feature only with typing,
  semantics, lowering, and rejection coverage. Statement expressions,
  attributes, vector builtins, packed layout, extensions to control flow, and
  compiler intrinsics cannot inherit correctness merely from being accepted by
  the compiler.

Consult the chosen ISO text and identified WG14 documents; pin document numbers
and record deviations instead of calling an arbitrary draft “the C23
semantics.” [WG14](https://www.open-std.org/jtc1/sc22/wg14/) identifies the C23
standard and its document register. Semantic gaps around memory and provenance
require explicit design decisions; [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/)
is a useful formal-semantics reference with a stated fragment, not a completed
Lean GNU C23 implementation.

First C subset: unsigned fixed-width scalar operations with proved widths,
typed functions, local bindings, conditionals, and no implicit external calls.
Add owned memory and loops with invariants before shared-memory programs.
Avoid promising general source ingestion while only supporting generated C.

## 4. GNU C++26

Use `-std=gnu++26` with pinned frontend, standard-library revision, ABI options,
and an identified language revision. Feature detection and toolchain acceptance
must remain separate from the semantic model.

Start with a common executable subset of C and C++ whose correspondence is
proved rather than assumed. Add C++ features through separate work packages:

| Area | Required obligations |
| --- | --- |
| Expressions and types | Value categories, references, conversions, overload resolution, evaluation order, and language-specific UB |
| Initialization/lifetime | Construction, destruction, temporaries, lifetime extension, placement construction, storage reuse, and cleanup on partial construction |
| Classes/layout | Subobjects, inheritance, virtual dispatch, vtables, access-adjustment thunks, object representation, and ABI-specific layout |
| Templates/compile-time execution | Substitution/constraints, specialization, instantiation, constant evaluation, and evidence that elaborated functions correspond to the submitted source |
| Exceptions | Throw/catch, cleanup edges, unwinding ABI/runtime, `noexcept`, termination, and FFI boundaries |
| Standard library | Contracts and implementation obligations for every used facility, including allocators, containers, threads, atomics, locks, and I/O |
| Modules/linkage | Translation units, ODR obligations, symbol identity, inline definitions, initialization order, and linkage |
| Advanced facilities | Coroutines, reflection, parallel execution, SIMD, and other features when demanded by concrete examples; each requires an explicit scope decision |

A proof about template-instantiated LLVM code can establish behavior of that
lowered artifact. It does not establish that an unverified frontend performed
C++ template instantiation, overload resolution, or constant evaluation
correctly. Likewise, disabling exceptions or RTTI restricts the profile; it does
not establish a theorem about programs that use those facilities.

Use the selected WG21 text for the abstract-machine and observable-behavior
rules. The publicly available [C++ draft abstract-machine section](https://eel.is/c++draft/intro.abstract)
is a reference whose exact revision must be recorded for implementation.
Library contracts and source-to-elaborated-core proofs are substantial separate
projects. There is no planned near-term claim to fully verify arbitrary GNU
C++26 programs.

## 5. LLVM IR

LLVM is a versioned semantic target, not generic assembly. Pin the IR dialect,
bitcode reader, target triple, data layout, address spaces, calling conventions,
intrinsic definitions, and optimization pipeline.

The IR model needs SSA/PHI rules, blocks and terminators, integer and
floating-point operations, pointer operations, memory accesses and alignment,
attributes, intrinsics, calls, exceptional control flow, atomics, fences,
metadata with semantic consequences, and module linkage. LLVM's own
[language reference](https://llvm.org/docs/LangRef.html) is the specification
starting point. A well-formed module is not a proof that it refines its source.

Distinguish immediate UB, poison, `undef`, and `freeze`; their differences affect
which transformations are valid. Flags and attributes such as overflow promises,
in-bounds pointer operations, nonnull/alignment requirements, and memory-effect
promises generate proof obligations. Never add such promises solely because an
optimizer benefits. ([LLVM UB manual](https://llvm.org/docs/UndefinedBehavior.html))

Use the [LLVM atomics guide](https://llvm.org/docs/Atomics.html) when specifying
ordering and scope mappings. The semantics must separately justify source
atomics to LLVM atomics, LLVM operations to target instructions/runtime calls,
and those operations' interaction with the OS model. A stronger-looking
instruction alone does not discharge all three obligations.

Initial LLVM subset: scalar integer SSA, branches, returns, and explicitly
contracted calls. Then add memory and loops; add atomics only with the shared
concurrency model. Reject unsupported intrinsics, attributes, metadata, and
address spaces. The frontend may synthesize helper calls even when the original
source has none; dependency closure must discover or reject them.

[Vellvm](https://github.com/vellvm/vellvm) is an existing Rocq formalization to
study; [Alive2](https://github.com/AliveToolkit/alive2) is an existing external
LLVM transformation tool. Neither currently supplies a Lean proof bridge or
this project's whole-program OS theorem. Pin revisions and licensing before
reuse, and treat importing their results as a new explicit proof/trust task.

## 6. Assembly and machine code

Represent typed instructions and operands with an architecture-specific
semantics. Also model registers and aliases, flags, instruction pointer,
memory, address calculations, alignment, exceptions, privilege restrictions,
and feature availability. The initial ISA is a deliberately small x86-64
subset; it must not accept an instruction just because an external assembler
knows its encoding.

The decoder must connect exact bytes to this semantics, with instruction
lengths, prefixes, immediate sign/zero extension, and relative addressing.
Instruction boundaries cannot be assumed from an untrusted disassembly listing.
Control-flow and code-validity invariants must account for all reachable
targets, including indirect calls/returns. Reject unsupported encodings and
unexpected executable regions.

The [Intel architecture manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
provide architectural instruction/system behavior. Pin a manual revision and
feature profile; AMD-specific behavior and other ISAs need their own specified
coverage. Architectural semantics do not supply a cycle-accurate cache,
speculation, or scheduling model.

Separate instruction behavior from ABI obligations: argument/result locations,
callee-saved registers, stack alignment, red zone, variadic calls, aggregate
passing, TLS, unwinding, process entry, and syscall conventions. Function-call
and Linux-syscall conventions are different interfaces. Unknown clobbers and
unknown memory effects cannot be treated as absent.

GNU inline assembly requires an additional contract between the C/C++ frontend
and assembly semantics: constraints, early clobbers, tied operands, memory and
condition-code clobbers, labels/control flow, and optimizer-visible effects.
GCC documents that a memory clobber constrains compiler assumptions; hardware
ordering still needs its own argument.
([GCC extended assembly](https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html))

Inline assembly escape hatches carry proof obligations or explicit unchecked
assumptions. A raw instruction string with an asserted postcondition cannot be
presented as a verified operation.

## 7. Undefinedness and nondeterminism across languages

Do not collapse these cases into a generic “error”:

| Category | Planned treatment |
| --- | --- |
| Ill-formed input / failed typing | Reject before execution semantics |
| Unsupported feature/profile | Report the missing capability; no verified result |
| Undefined behavior | Prove unreachable under the stated precondition for every covered execution |
| Implementation-defined behavior | Fix and record the selected implementation choice/profile |
| Unspecified/permitted choices | Model the allowed choices and quantify over them as required |
| OS/library failure | An ordinary modeled outcome with a contract and cleanup obligations |
| Trap/fault | Explicit machine outcome; prove absent or permitted by the specification |
| Deadlock/divergence | Explicit maximal-execution outcomes; separate progress proofs |

For example, unsigned wraparound can be a defined result, signed overflow can
violate a source precondition, an LLVM operation can produce poison, and the
corresponding machine instruction can compute a concrete wrapped value. The
last fact does not retroactively make the source program defined. The lowering
proof must connect the exact contracts.

Memory allocation addresses, thread schedules, weak-memory executions, I/O
replies, interruption, and resource availability introduce nondeterminism at
different levels. Identify which choices the program controls and which belong
to the environment. Refine sets of permitted behaviors; never infer a universal
result from a single interpreter run. See the quantifiers and progress
conditions in [the verification plan](verification.md).

## 8. Program ingress and cross-language boundaries

Support two ingress paths explicitly:

- **Lean-authored eDSL:** construct a typed Lean program; prove its specification;
  emit source/IR/assembly and validate or prove each lowering. The text emitter
  is still an obligation: semantic correctness of the Lean AST does not prove
  an arbitrary printer emitted that AST.
- **Imported external program:** bind exact text, preprocessing/includes,
  parsing, typing, elaboration, and language revision before proving behavior.
  Initially an importer can have a visibly trusted frontend boundary, or can
  prove only the lowered artifact against an independent specification. That
  narrower result is not a proof of source-language compilation correctness.

Cross-language linking needs contracts for symbol names/linkage, layouts,
calling conventions, pointer/lifetime ownership, allowed aliasing, error
propagation, and thread interactions. C/C++ exceptions across foreign
boundaries, callbacks into an OS/runtime, dynamic symbol interposition, and
libraries that create threads need separate rules. A runtime call's type alone
does not describe its effects.

First support complete, small dependency closures. Add modular linking only
after proving that contract-compatible components compose under shared-memory
interference. Add dynamic components after the load/link layer can establish
the same contract for the actual resolved bytes.

## 9. Required deliverables for a new feature

For each increment, require a short semantics decision record identifying
source references and unresolved interpretation choices; Lean syntax and
semantics; at least one independently specified behavioral theorem; relevant
lowering/validation evidence; a target capability entry; and rejection behavior
for missing premises. Add meaningful tests or proof counterexamples when they
can catch a plausible wrong arithmetic rule, lifetime rule, ordering, ABI
mapping, or failure-path omission. Do not add tests that merely restate a
constructor's fields.

Keep [OS coverage](os-semantics.md), [architecture](architecture.md),
[verification](verification.md), and the [roadmap](roadmap.md) consistent with
actual theorem coverage. Broad syntax coverage must not outrun honest claims
about source semantics, final bytes, or OS behavior.
