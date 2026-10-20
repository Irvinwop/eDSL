# Research and reuse map

eDieSeL currently uses pinned Lean 4 and its bundled facilities, with no
third-party Lean package dependency. The projects below are research references
or candidates for reuse, not implemented integrations. External proofs do not
become Lean theorems without an explicit checked bridge or reproof.

## Semantic and proof infrastructure

| Primary source | Relevance | Integration boundary |
| --- | --- | --- |
| [Lean / Std](https://lean-lang.org/doc/reference/latest/) | Kernel, inductive models, bitvectors and proof/build tools | The current foundation; language, ISA and OS adequacy remain project obligations |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Algebra, orders and mathematical proof infrastructure | Candidate reuse; no compiler-output or platform certificate follows from adoption |
| [Iris-Lean](https://github.com/leanprover-community/iris-lean) | Concurrent resource logic and proof-mode infrastructure | Requires a compatible language/OS instantiation and adequacy argument |
| [lean-mlir](https://github.com/opencompl/lean-mlir) | Lean SSA/IR theory and compiler reasoning | Does not supply the GNU frontend or final executable/OS connection |

Review Iris-Lean's [compatibility differences](https://github.com/leanprover-community/iris-lean/blob/master/docs/compatibility.md)
before transferring an Iris-Rocq argument. The existing ownership/loan registries
are not themselves an integration of concurrent separation logic.

## Languages, compilers and machine code

| Primary source | Relevance | Integration boundary |
| --- | --- | --- |
| [CompCert](https://compcert.org/man/manual001.html) | Semantic-preservation structure and explicit compiler boundaries | Rocq proofs and supported source subsets need an explicit relation to this project |
| [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/) | C object memory, provenance and semantics design | No complete GNU C23 semantics has been imported into Lean |
| [Vellvm](https://github.com/vellvm/vellvm) | Formal LLVM semantics | Version/subset correspondence, a Lean bridge and OS/ISA composition remain work |
| [Alive2](https://github.com/AliveToolkit/alive2) | LLVM validation diagnostics and certificate design | Solver diagnostics do not supply Lean checking or source/final-byte preservation |
| [Souper](https://github.com/google/souper) | Restricted synthesis and superoptimization techniques | Search needs checked results and an explicit candidate class for any optimality claim |
| [x86isa](https://github.com/acl2/acl2/tree/master/books/projects/x86isa) | Executable ISA models and machine-code proofs | ACL2 results are external; concurrency/OS assumptions require their own relation |
| [Sail](https://github.com/rems-project/sail) | ISA definitions and model generation | No complete x86-to-Lean verification stack is assumed |
| [Reopt VCG](https://github.com/GaloisInc/reopt-vcg) | Binary/LLVM verification-condition generation | Does not supply a checked theorem for eDieSeL's selected contracts |
| [Islaris](https://www.cl.cam.ac.uk/~pes20/2022-pldi-islaris.pdf), [seL4 translation validation](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf), [decompilation into logic](https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf) | Design references for binary proofs and validation | Their proof systems/models are not imported dependencies |

## Concurrency and operating systems

| Primary source | Relevance | Integration boundary |
| --- | --- | --- |
| [x86-TSO](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf) | Formal weak-memory model and correspondence techniques | The implemented FIFO models have no proved refinement to this published model |
| [Linux Kernel Memory Model](https://docs.kernel.org/dev-tools/lkmm/index.html) | Contracts for relevant Linux kernel primitives | Distinct from userspace C/C++ orders; concrete machine correspondence must be justified |
| [seL4 proofs](https://sel4.systems/Verification/proofs.html) | Concrete kernel verification and configuration/assumption discipline | No theorem transfers automatically to Linux or to an application/runtime composition |

These references inform the [roadmap](roadmap.md) and
[concrete OS implementation plan](os-implementation.md). Current target and
trust limits remain in [coverage](coverage.md) and [trust](trust.md).

## Required evaluation record

Before adopting, adapting or porting a dependency, record:

1. Exact revision, license/attribution, Lean and transitive versions, maintenance
   assessment and reproducible build.
2. Exported definitions/theorems, supported semantic subset, hypotheses, axiom
   dependencies and native/solver trust paths.
3. A representative integration proof at the intended semantic boundary,
   including unsupported constructs and required adapters.
4. Checking time, memory, artifact size and expected scaling.
5. The adopt/adapt/port/reference-only decision and remaining proof obligations.

Changes to foundational representations require a new compatibility review.
Select reuse by its semantic and trust fit, with checked evidence at the
project's own boundary.
