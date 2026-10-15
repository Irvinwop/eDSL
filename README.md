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
- An exact atomic-exchange byte profile with a labeled indivisible RMW event,
  OS-cell projection, guarded resource authority and same-cell value-flow histories.
- Shared atomic handles with per-actor authorization, allocation reservations,
  permanent revocation, read-loan stability and exchange-trace value conservation.
- Mutable atomic workers with actual MOV/XCHG/RET instruction scheduling,
  retained old results through join, resource revocation and schedule value-flow proofs.
- A counted assembly loop with a proved invariant and termination for every
  64-bit count, modular arithmetic result and exact `2*count+3` user-instruction cost.
- Little-endian mapped-memory reads and guarded writes with per-byte permissions,
  read-after-write and disjoint code/stack preservation proofs.
- A sequential OS address-space model with checked mapping, protection and
  unmapping, permission-revocation proofs and composition with a binary contract.
- A checked OS word store whose cell update projects exactly to the machine
  store, with all-input compiler-binary composition and retained permissions.
- A sequential allocation registry with fresh lifetime IDs, revoking transfer
  epochs, managed-history invariants and owned-store composition with exact bytes.
- Shared read loans with whole-allocation freezing, permanent loan-ID revocation,
  managed-history byte/permission stability and actual binary-load composition.
- Managed read workers with checked spawn/join, current-shared-memory instruction
  scheduling, arbitrary-history result proofs and permanent thread/loan revocation.
- A restricted ELF64 loader with bounds, permissions, BSS and page-collision
  checks; full-file certificates derive executable entry-code binding.
- A standalone exit42 ELF certificate, first-syscall execution proofs and an
  explicit single-thread Linux exit contract separating status from progress.
- A bounded stream-write/exit certificate covering short transfers, raw errors
  and an explicit return contract; complete output is conditional on full transfer.
- A Lean certificate CLI and live C/C++ compile→link→byte extraction→proof→native
  integration checks, with fail-closed rejection cases.
- Matching two-instruction function and three-instruction syscall lower bounds
  within the supported ISA subset, under stated initial-register conditions.
- Transitive axiom auditing, including generated certificates.
- Optional native GNU23/GNU++26 compiler probes retained from the bootstrap.

The function certifier accepts three two-instruction profiles, the three-instruction
`exchange32` profile and the counted `increment-loop` profile. The process certifier
accepts exit42 (three user instructions) and write-exit42 (eight across a completed write). Other correct
encodings remain unsupported. Linux loader/kernel refinement, broader syscalls,
locks, weak memory and general source eDSLs/validators remain planned. See
the precise [implemented coverage and trust boundary](docs/coverage.md).

## Read the plan

| Document | Question it answers |
| --- | --- |
| [Implemented coverage](docs/coverage.md) | What can run and what has actually been proved? |
| [Address-space contracts](docs/address-space.md) | How do mapping and permission changes connect to binary proofs? |
| [Ownership and lifetimes](docs/ownership.md) | What prevents stale authority after release, address reuse or transfer? |
| [Shared read borrowing](docs/borrowing.md) | What keeps borrowed bytes and permissions stable across managed operations? |
| [Read-worker scheduling](docs/threads.md) | How do actual machine instructions compose with spawn, shared resources and join? |
| [Atomic exchange](docs/atomic-exchange.md) | How does an exact XCHG event update OS cells and respect existing read authority? |
| [Shared atomic handles](docs/atomic-handles.md) | How can actors share an atomic word while blocking conflicting resource changes? |
| [Mutable atomic workers](docs/atomic-workers.md) | How do interleaved MOV/XCHG/RET instructions retain actual old values through join? |
| [ELF container verification](docs/elf.md) | How do complete ELF bytes establish the executable entry code? |
| [Standalone exit contract](docs/process-exit.md) | What connects ELF entry execution to exit status, and what progress is assumed? |
| [Stream output and exit](docs/process-write.md) | How do short writes and errors compose with the next userspace instructions? |
| [Counted control flow](docs/control-flow.md) | How are a backward branch, loop invariant, termination and input-dependent cost proved? |
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

Start with the roadmap, then the OS and platform documents. Restricted x86-64
functions, a counted loop and bounded stream-write/exit entries are checked;
ownership, lifetimes, shared read borrowing and managed read-worker scheduling
are checked too. An atomic-exchange foundation now connects XCHG events and
guarded OS cells. Shared atomic handles now preserve reservations and resource
lifetimes. Mutable atomic workers execute actual instructions against shared
cells and retain exchanged values privately through join. Next come protected
invariants and the thread/atomic counter workload, with concrete runtime refinement.
General GNU C++26 ingestion and a fully verified Linux kernel are substantial
separate research work.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build EDSL edsl-certify edsl-certify-process
lake env lean -DwarningAsError=true tests/X86.lean
lake env lean -DwarningAsError=true tests/Memory.lean
lake env lean -DwarningAsError=true tests/AddressSpace.lean
lake env lean -DwarningAsError=true tests/OSComposition.lean
lake env lean -DwarningAsError=true tests/WordStore.lean
lake env lean -DwarningAsError=true tests/ELF.lean
lake env lean -DwarningAsError=true tests/Process.lean
lake env lean -DwarningAsError=true tests/Write.lean
lake env lean -DwarningAsError=true tests/ControlFlow.lean
lake env lean -DwarningAsError=true tests/Ownership.lean
lake env lean -DwarningAsError=true tests/Borrowing.lean
lake env lean -DwarningAsError=true tests/Threads.lean
lake env lean -DwarningAsError=true tests/AtomicExchange.lean
lake env lean -DwarningAsError=true tests/OSAtomicExchange.lean
lake env lean -DwarningAsError=true tests/Atomics.lean
lake env lean -DwarningAsError=true tests/AtomicThreads.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
bash scripts/verify-compilers.sh
bash scripts/verify-process.sh
bash scripts/verify-loops.sh
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
