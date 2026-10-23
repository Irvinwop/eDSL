# eDieSeL

[![Lean proofs](https://github.com/Irvinwop/eDieSeL/actions/workflows/lean.yml/badge.svg)](https://github.com/Irvinwop/eDieSeL/actions/workflows/lean.yml)

**Prove program behavior in Lean 4, from exact machine code to memory and OS resources.**

eDieSeL is a formal verification library for reasoning about what programs do
and which resources they may access. It combines executable machine semantics,
independent behavioral contracts, and proofs checked by Lean's kernel. The
long-term aim is verification of applications, kernels, and operating-system
components, including functional correctness and security properties.

The current implementation targets selected x86-64 programs and explicit OS
resource models. Whole-kernel verification and complete C, C++, or LLVM
frontends are future work. See the [capability overview](docs/implementation-status.md)
and [trust model](docs/trust.md) for the supported boundaries.

## Start here

- **[Verify a function](docs/verify-a-function.md)** — a complete worked example,
  from an independent specification to a reusable proof and resource contract.
- **[Verify an ELF function](docs/named-elf-import.md)** — import a named function
  and bind its proof to the exact executable bytes.
- **[Browse the documentation](docs/README.md)** — guides for memory ownership,
  concurrency, language semantics, and extending the library.

Install [elan](https://github.com/leanprover/elan), then build the worked example:

```sh
git clone https://github.com/Irvinwop/eDieSeL.git
cd eDieSeL
lake build EDSL.Examples.Verification.Double
```

The example proves a small machine-code function computes unsigned modular
doubling, while preserving its caller's memory and ABI obligations. Its
mathematical result is specified separately from the instructions:

```lean
result value output := output.toNat = (2 * value.toNat) % 2^64
```

Lean is pinned to **4.35.0**, with warnings treated as errors and no third-party
Lean packages. The Lean namespace remains `EDSL`; existing `edsl-*` commands
retain their names. [Build and validation instructions](docs/validation.md)
cover the full library, theorem audit, and fresh kernel replay.

## How verification works

1. Supply exact program bytes and a mathematical contract.
2. Check decoding and control flow against those bytes.
3. Prove generated verification conditions; loops also need invariants and
   termination arguments.
4. Apply shared ABI and OS-resource rules, then bind the result to the selected
   function in the complete executable.

New programs reuse the checker and resource adapters. Program-specific work
focuses on the contract, mathematics, and loop invariants. An unsupported
instruction or OS effect requires a shared semantic extension before that
program can be certified.

## Current capabilities

| Area | Implemented scope |
| --- | --- |
| Machine code | A restricted x86-64 instruction set, checked control-flow graphs, reusable verification-condition generation, and sparse loop proofs |
| Memory and calls | Byte and word access, caller/return contracts, ownership, borrowing, lifetimes, and preservation of memory permissions |
| Concurrency | Selected atomic, mutex, store-buffer, and futex protocols under explicit managed models |
| Executable binding | Checked ELF layouts and named-function selection, with certificates tied to exact final bytes |
| Languages | Lean models and design work for GNU C23, GNU C++26, LLVM IR, and assembly; complete source frontends and compiler-preservation proofs remain incomplete |

The fixed GCC/Clang `-O2` evaluation corpus has validated conditional
certificates for **19/40 functions and 38/80 compiler artifacts**, including
**three distinct concurrent functions**: fetch-add, acquire-load and release-store
under their recorded managed models. **21 functions / 42 artifacts** remain.
See the [corpus results](docs/compiler-corpus.md) and
[multiplication measurement](corpus/measurements/multiply-modulo64-v1/)
for the accepted source, proof scope and environmental assumptions.

A certificate records the machine and resource assumptions under which its
contract holds. Connecting these models to native Linux, physical CPUs, and
complete operating systems requires further
[verification obligations](docs/verification.md).

## Project layout

| Path | Contents |
| --- | --- |
| [`EDSL/`](EDSL/) | Lean semantics, resource models, proof infrastructure, and examples |
| [`EDSL.lean`](EDSL.lean) | Reusable sequential verification API |
| [`EDSL/All.lean`](EDSL/All.lean) | Full proof catalogue for audits and replay |
| [`Tools/`](Tools/) | Command-line entrypoints |
| [`docs/`](docs/README.md) | Guides, architecture, capabilities, and roadmap |
| [`tests/`](tests/) and [`fixtures/`](fixtures/) | Contract regressions, rejection checks, and native fixtures |
| [`corpus/`](corpus/) | Frozen compiler outputs and reproducible measurements |

Contributions use [Apache-2.0](LICENSE) with [DCO sign-off](CONTRIBUTING.md).
See [contribution guidance](CONTRIBUTING.md), the [roadmap](docs/roadmap.md),
and the [security policy](SECURITY.md). Research citation metadata is available
in [CITATION.cff](CITATION.cff).
