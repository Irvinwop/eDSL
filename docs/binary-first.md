# Binary-first verification

Status: restricted x86-64 function, memory, loop and OS composition results are
implemented, with live compiler-output certificates. A reusable read-only CFG
layer now supports local proofs against independent contracts. See
[coverage](coverage.md) for exact scope; general program ingestion, grading and
the broader pipeline below remain planned.

## One machine-code target for many implementation languages

Compile C, C++, Rust, generated code or another implementation language to the
chosen target, then verify the exact final machine code against a specification
written independently in Lean. Assembly text is an intermediate artifact;
decoding final linked bytes closes assembler, relocation and post-link gaps.

The default theorem is schematically:

```text
For every admitted initial state and environment,
every maximal execution of these exact loaded bytes in MachineOS(profile)
satisfies the independently defined specification.
```

The property can cover returned values, memory safety, ownership, I/O, resource
cleanup, concurrency and explicit failures. Termination requires its own proof
under stated progress assumptions. Proof search is untrusted; the proof term
or sound-checker acceptance evidence is checked in Lean.

This avoids needing a complete C, C++, Rust and LLVM semantics before proving
useful executable properties. A separate source-to-output preservation theorem
is needed only when the requested guarantee includes the original source's
language-defined meaning. A binary property can be valuable without that claim.

## What work is shared and what remains

| Shared work | Remaining obligation |
| --- | --- |
| One exact-byte decoder and ISA semantics per architecture/profile | Cover each used instruction, fault, memory type and concurrency feature |
| One proof/checker interface over binary behavior | Invariants, summaries and certificates for the particular program |
| One ABI/link/load model for the selected deployment | Bind all relevant code, relocations, libraries and initial state |
| OS contracts and concrete implementation proofs | Cover relevant interference, failure and progress, and compose the proofs |
| Machine-level cost metrics | Prove counts/bounds for the selected input/candidate/environment model |

Every CPU architecture still needs a suitable model: x86-64 and AArch64 do not
share an instruction semantics merely because both have assembly syntax.
Compiling an entire kernel also does not supply its specification, invariants,
or device model. Optimizations can make recovery of invariants harder even
when all instructions are supported.

## Source and IR as assistance

The current [CFG workflow](cfg.md) turns a raw function window or explicit ELF
entry span into checked graph facts and a typed local-proof interface. An agent
can supply cutpoint invariants, decreasing ranks and local instruction/read
proofs without adding a whole-function recognizer. The actual interpreter still
decodes the exact current bytes. Static import is a starting point for a proof;
it does not certify the task's functional answer.

For objective grading, the task's independent specification, admissible inputs
and required theorem type must be fixed before candidate verification. The
proof must establish that contract for the candidate's exact bytes and every
admitted behavior. It cannot substitute a convenient candidate-specific result
predicate. Automating that task interface and general proof discovery remains
future work.

Source structure, LLVM IR, symbols, debug mappings and compiler optimization
remarks can suggest functions, invariants, ownership and simulation relations.
Check those suggestions against the machine semantics; a debug line table is
not a proof. LLVM need not be a trusted mandatory intermediate representation.

Rust's compiler can emit assembly, LLVM IR, bitcode and object files through
[`--emit`](https://doc.rust-lang.org/rustc/command-line-arguments.html#--emit-specifies-the-types-of-output-files-to-generate).
Use the exact OS build's target, configuration, dependencies, runtime and
compiler options. An unrelated example compiled to `.ll` does not represent
the deployed OS. An IR-only proof is labeled as such until its correspondence
to final bytes is established. Compiler-specific UB/poison assumptions must
not be imported as unjustified facts about a safe execution.

No source language earns or loses a safety verdict by its name, use of an
`unsafe` keyword, or the verifier failing to finish. A finding requires a
checked violation of a justified property under feasible conditions.

## First implementation gate

Take a small, loop-free fixed-width function, an independent input/output
contract, and its exact compiler-generated function bytes. Prove decoding,
register/flag semantics, ABI conditions and the contract for all admitted
inputs. Reject malformed bytes, unsupported instructions and wrong results.
Repeat with another source language or compiler/configuration using the same
binary proof interface. Add memory, loops, process loading and OS interaction
only with their corresponding models.

Source eDSLs remain part of the project: they support readable specifications,
generation, reuse of verified passes and optional preservation proofs. They do
not block the first direct binary-property theorem.
