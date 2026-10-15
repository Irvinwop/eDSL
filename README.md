# eDSL

**Lean 4 eDSLs and proofs for GNU C23, GNU C++26, LLVM IR, assembly, and the
operating-system behavior of programs.**

The goal is to prove that a particular compiler-produced executable satisfies
an independently stated specification on a particular architecture and OS
profile. Threads, locks, atomicity, memory ordering, allocation, mappings,
resource lifetimes, and failures are central parts of that statement.

The implementation and proof language is **Lean 4**. C/C++, LLVM IR, and
assembly are the languages being modeled and generated. Native fixtures and
necessary runtime shims can use C/C++/assembly.

The repository is **public**. Any actual security findings, metadata and
reproducers stay in ignored local storage and are never committed or uploaded
to CI. The [findings policy](findings/README.md) keeps them separate from the
owned synthetic fixtures used to test the verifier.

## What the eventual guarantee means

Given an independent specification, final executable bytes, build identity,
and platform profile, produce a Lean-checked proof that every admitted
execution satisfies the specification, under its explicit input and environment
assumptions. Termination and progress require their own proofs and scheduler
assumptions. Unsupported code, invalid certificates, and timeouts are reported;
they do not count as proofs.

The main strategy is **direct binary verification**: any supported source
language/compiler produces candidate code, and Lean checks that the final bytes
meet the specification. One machine-code semantics serves those inputs.
Source/IR semantics and translation validation add optional source-preservation
guarantees; they are not prerequisites for a direct binary-property theorem.
We can also prove small lowering passes correct in Lean. These routes do not
make an arbitrary Linux kernel, physical CPU, library, or dynamic loader
verified by assumption. Their contracts
and remaining trust must appear in the result.

## Current status

Implemented and checked:

- A pinned Lean 4 / Lake project, with warnings treated as errors.
- A generic behavior-refinement interface, composition, and safety transfer.
- A restricted x86-64 byte decoder, instruction/stack/memory semantics, and an
  unbounded execution relation with evaluator soundness and completeness.
- All-input theorems for actual Clang/GCC increment, 32-bit load and 32-bit store
  bytes, including register/memory framing, return behavior and termination.
- Little-endian mapped-memory reads and guarded writes with per-byte permissions,
  read-after-write and disjoint code/stack preservation proofs.
- A Lean certificate CLI and live C/C++ compile→link→byte extraction→proof→native
  integration checks, with fail-closed rejection cases.
- A two-instruction lower bound within the supported ISA subset.
- Transitive axiom auditing, including generated certificates.
- Optional native GNU23/GNU++26 compiler probes retained from the bootstrap.

The certifier accepts three exact function profiles, each returning in two modeled
instructions. Other correct encodings remain unsupported. ELF loading,
Linux kernel/concurrency models and general source eDSLs/validators remain
planned. See the precise
[implemented coverage and trust boundary](docs/coverage.md).

## Read the plan

| Document | Question it answers |
| --- | --- |
| [Implemented coverage](docs/coverage.md) | What can run and what has actually been proved? |
| [Roadmap and acceptance gates](docs/roadmap.md) | What must be built, in what order, and how will completion be established? |
| [Architecture](docs/architecture.md) | How do Lean models, compilers, certificates, and platform contracts fit together? |
| [Binary-first verification](docs/binary-first.md) | How can one machine-code target reduce source-language proof work? |
| [Verification](docs/verification.md) | What exact theorem connects the source to final executable bytes? |
| [Language domains](docs/languages.md) | What semantics do GNU C23, GNU C++26, LLVM IR, and assembly each need? |
| [OS semantics](docs/os-semantics.md) | Which OS facilities matter, and what must be proved or assumed about them? |
| [Platform model](docs/platform-model.md) | How do ISA, ABI, memory, loader, libraries, and kernel compose? |
| [OS implementation proofs](docs/os-implementation.md) | How can source/IR/assembly inputs discharge concrete OS contracts? |
| [Findings and reporting](docs/findings.md) | How do checked defects enter a private reporting queue? |
| [Costs and lower bounds](docs/cost-model.md) | When can we prove operation counts or optimality? |
| [Trust and evidence](docs/trust.md) | What is currently trusted, checked, assumed, or outside the claim? |
| [Reuse assessment](docs/research-map.md) | Which existing projects should be evaluated before building new machinery? |

Start with the roadmap, then the OS and platform documents. The proposed first
real target is a restricted x86-64 function, followed by a static Linux process,
owned memory, and a thread/atomic workload. General GNU C++26 ingestion and a
fully verified Linux kernel are substantial separate research work.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build EDSL edsl-certify
lake env lean -DwarningAsError=true tests/X86.lean
lake env lean -DwarningAsError=true tests/Memory.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
bash scripts/verify-compilers.sh
```

`lean-toolchain` pins Lean 4.35.0. The library currently needs no third-party
Lean packages. The audit rejects transitive axiom dependencies outside Lean's
standard `propext`, `Quot.sound`, and `Classical.choice`; it also rejects proof
holes. Its negative check injects an untrusted transitive dependency and
requires rejection. The bundled `leanchecker` replays the stored proofs in a
fresh kernel environment. These check the current declarations, not the adequacy of a future
language, OS, or hardware model. The compiler integration command also needs
Linux/x86-64, Clang, GCC and binutils; it uses only owned synthetic fixtures.

The optional native compiler probes are separate from proofs:

```sh
cmake -S . -B build -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++
cmake --build build
```

These require exact `-std=gnu23` and `-std=gnu++26` acceptance, checked with
Clang 18.1.3 for the bootstrap. They establish language-mode/syntax availability,
not complete language support or semantic preservation.

## License and contributions

[Apache-2.0](LICENSE), with attribution in [NOTICE](NOTICE) and research citation
metadata in [CITATION.cff](CITATION.cff). Contributions require a
[DCO 1.1 sign-off](CONTRIBUTING.md); contributors retain their copyrights.
