# eDSL

Embedded domain-specific languages for **GNU C23 (`gnu23`), GNU C++26
(`gnu++26`), LLVM IR, assembly, and the operating-system behavior of a program**.

The OS domain is the project's highest priority. Threads, locks, atomicity,
memory ordering, allocation, virtual memory, and resource lifetimes belong in
the program model, with explicit semantics that survive compilation. Processes,
I/O, networking, scheduling, signals, timers, and other program-visible OS
facilities are also in scope.

## Project status

This is the initial repository foundation: project scope, a proposed
architecture, an OS requirements map, a roadmap, and GNU language-mode build
checks. The eDSL APIs, shared representation, OS runtime, and code generators
are **planned; they are not implemented yet**.

Implementation will use C, C++, and assembly. The initial implementation target
is Linux on x86-64; additional OS and CPU targets are planned. Embedding API
details remain open, including the boundary between C-hosted and C++-hosted
builders.

## Domains

| Domain | Intended coverage |
| --- | --- |
| GNU C23 | Types, expressions, control flow, functions, object layout, GNU extensions, and C interoperability |
| GNU C++26 | Typed composition, C++ declarations and expressions, templates where needed, lifetimes, and C++ interoperability |
| LLVM IR | Explicit types, control flow, memory operations, atomics, target layout, calling conventions, and verification |
| Assembly | Target-specific instructions, registers, constraints, clobbers, ABI rules, fences, and object emission |
| **OS / runtime** | **Threads, synchronization, atomicity, memory, processes, I/O, scheduling, time, and resource ownership across every language/backend** |

The language domains need their own precise constructs, with a shared core for
composition. Target-specific behavior must remain expressible. Unsupported
semantics must produce a diagnostic instead of silently changing the program's
contract.

## Start here

- [Architecture and embedding proposal](docs/architecture.md)
- [OS semantics and coverage map](docs/os-semantics.md)
- [Implementation roadmap](docs/roadmap.md)
- [Contributing and verification](CONTRIBUTING.md)

## Build the initial toolchain checks

Use CMake 3.25 or newer and compilers accepting the exact `-std=gnu23` and
`-std=gnu++26` switches. Clang 18.1.3 has been checked locally for this bootstrap;
accepting these modes does not establish complete language or library support.
Future implementation features will need their own capability checks.

```sh
cmake -S . -B build -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++
cmake --build build
```

These checks compile C and C++ atomic operations and GNU statement expressions
in the requested language modes. They establish a compiler baseline; they do
not test an eDSL implementation or OS backend. LLVM and assembly dependencies
will be added with their first implementations.
