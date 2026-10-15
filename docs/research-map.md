# Reuse assessment and research dependencies

Status: evaluation plan. No third-party Lean dependency has been adopted.
The current library uses the pinned Lean toolchain and its bundled facilities.
The following projects are candidates or references, not completed integrations.

| Project / primary source | Why evaluate it | What it does not supply here |
| --- | --- | --- |
| [Lean / Std](https://lean-lang.org/doc/reference/latest/) | Kernel, inductive models, bitvectors, proof automation and build tools | Adequate C/LLVM/ISA/OS semantics or artifact certificates |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Mathematical relations, orders, algebra and reusable proof infrastructure | Compiler-output correctness or a native OS model |
| [Iris-Lean](https://github.com/leanprover-community/iris-lean) | Concurrent separation logic, resource reasoning and proof-mode infrastructure | The project's language/OS instantiation, Linux runtime verification or x86 memory semantics |
| [lean-mlir](https://github.com/opencompl/lean-mlir) | Lean SSA/IR theory and compiler-reasoning experience | A complete GNU frontend, all LLVM semantics or a final executable/OS theorem |
| [CompCert](https://compcert.org/man/manual001.html) | Compiler refinement structure, semantic preservation and proof boundaries | GNU C23/C++26 coverage or automatic transfer of Rocq proofs into Lean |
| [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/) | C semantics, object memory and provenance design | Full GNU C23 semantics already checked in Lean |
| [Vellvm](https://github.com/vellvm/vellvm) | Formal LLVM semantics and interpreters | A Lean bridge, version/subset correspondence or complete OS/ISA connection |
| [Alive2](https://github.com/AliveToolkit/alive2) | External LLVM validation diagnostics and certificate-design lessons | Lean checking, general interprocedural proof, source/frontend correctness or final-byte validation |
| [Souper](https://github.com/google/souper) | Restricted synthesis/superoptimization techniques | A maintained mandatory dependency or a global optimality proof; original repository is archived |
| [x86isa](https://github.com/acl2/acl2/tree/master/books/projects/x86isa) | Executable ISA modeling and machine-code proof techniques | Automatic Lean import or every concurrency/OS assumption this project needs |
| [x86-TSO](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf) | Formal weak-memory model and correspondence ideas | A complete current x86 ISA or Lean userspace/compiler mapping |
| [Sail](https://github.com/rems-project/sail) | ISA-definition and model-generation ecosystem | An assumed complete x86-to-Lean verification stack |
| [Reopt VCG](https://github.com/GaloisInc/reopt-vcg) | Binary/LLVM verification-condition generation | A kernel-checked Lean theorem for this project's compiler/platform profile |
| [seL4 proofs](https://sel4.systems/Verification/proofs.html) | A concrete verified-kernel route and explicit configuration/assumption discipline | A theorem about Linux or automatic application/runtime composition |

Iris-Lean's documented [compatibility differences](https://github.com/leanprover-community/iris-lean/blob/master/docs/compatibility.md)
need review before selecting its logic or transferring an Iris-Rocq argument.
Likewise, theorems checked in Rocq, HOL4, Isabelle or ACL2 remain external
results until an explicit checked bridge or reproof exists.

## Required evaluation record

For each prospective dependency, record:

1. Exact repository/revision, license and attribution requirements, Lean and
   transitive dependency versions, maintenance state and build reproduction.
2. Exported definitions and theorems, their semantic subset and hypotheses,
   axiom dependencies, and any native/solver trust paths.
3. A small representative integration proof using the project's own intended
   semantic boundary; report unsupported constructs and required adapters.
4. Proof elaboration/checker time, memory, artifact size and expected scaling.
5. A reviewed adopt / adapt / port / reference-only decision and remaining
   proof obligations. Changes to foundational representations require a new
   compatibility review.

Prefer reuse where the semantic and trust boundary fits. Do not select a
library solely because its name mentions LLVM, Iris or x86, and do not rebuild
major proof infrastructure before checking existing work.
