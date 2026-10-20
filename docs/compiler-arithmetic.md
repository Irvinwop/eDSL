# Compiler addition through the generic PureCall API

`EDSL.Arithmetic64.addition` fixes two full64 arguments in RDI and RSI. Its
domain is `True`, including zero and overflow. Its result is specified in
natural numbers: `result.toNat = (left.toNat + right.toNat) % 2^64`. Usefulness
requires both operands to be nonzero and does not restrict admission. The
registered `addModulo64` task selects this fixed specification; candidates
cannot select weaker arithmetic.

`EDSL.X86.VCGen.CompilerArithmetic` reuses
`CompilerComparisons.Compiler` and the existing generic PureCall contract,
resource adapter and generated-WP soundness theorem. It adds no routine-specific
contract, resource domain, interpreter, CLI, registry entry or ISA operation.

| Compiler selector | Complete frozen body | Instructions |
| --- | --- | --- |
| `defaultGCC` | `f30f1efa488d0437c3` | ENDBR64; LEA RAX,[RDI+RSI]; RET |
| `defaultClang` | `488d0437c3` | LEA RAX,[RDI+RSI]; RET |

The public APIs are `bytes`, `graph`, `checked`, `valid`, `entry`,
`entry_offset`, `generated_vc`, `raw_semantics`, `executes` and `observations`.
The proposed CFG is validated by the production `CFG.check`, including decoding
and complete byte coverage. One parameterized generated-WP proof reduces the
production executor for both compiler profiles, then discharges the natural
modulo arithmetic independently. No instruction interpreter or index-search
macro is added.

`raw_semantics compiler` is a universal `Grading.ReadOnlySemanticClaim` for
`PureCall.readOnlyTask Arithmetic64.addition`. It comes from
`pureCall_semantics_of_generated`, including every-prefix policy and the generic
current-resource bridge. The contract retains full RAM and permissions, returns
through the original caller slot, advances RSP by eight, preserves SysV
callee-saved registers and nonarithmetic flags. All initial registers and flags
and every AF stream remain universal.

`Observed` projects to that independent `PureCall.Post` and separately proves
exactly three retired instructions for GCC and two for Clang, one original
STACK8 operand read and equality of all flags. These counts include RET and
GCC's ENDBR64. Instruction fetches are not operand reads. These observations
are not domain restrictions or an operation-cost minimum. LEA does not access
the computed integer, so its result may be noncanonical.

Clients supply present `PureCall.ResourcePre` and usefulness
evidence at its actual ELF address to `PureCall.nonvacuous_of_resource`, then
compose `raw_semantics`. This module constructs no special resource domain and
assumes no successful future execution or output as admission evidence.

The inherited `PureCall.Pre` requires current executable exact bytes, full64
argument bindings, the readable original eight-byte caller return slot, a
canonical continuation, nonwrapping stack extent and canonical post-RET RSP.
Stable ordinary modeled RAM and the production `Sequential.targetProfile`
(long mode, IBT and shadow stacks disabled, multi-byte NOP support) are
environmental assumptions. Decoding ENDBR64 does not establish CPU/MSR state.
The existing native alignment and platform limitations are unchanged.

`tests/CompilerArithmetic.lean` uses `CallResources.Domain` with supplied
modeled mappings at distinct compiler-specific addresses, original loans and
unrelated writable/inaccessible cells. Both profiles are checked against
literal wrapping, high-bit, full64 carry, noncanonical integer and zero-input
expectations. Arbitrary caller registers/flags/AF streams, actual decoded
execution, ABI/RAM/resource frames, the real authorized read origin, GCC's
extra prefix step and rejection of swapped compiler graphs are covered.

Only addition is implemented. Multiplication, source/IR preservation, native
loading/ownership authority, physical CPU correspondence and concurrent
refinement are excluded. There is no new native conformance fixture or claim.
No ELF certificate, trusted registration, grading integration or frozen corpus
count increase (2/40 or 4/80) is established here.

Worker-local exact build, transitive audit, negative audit, imported fresh
closure replay, review and hash receipts live under ignored
`.cache/arithmetic-semantics-work/`; those local receipts are not public
certificates. Build only these modules and their needed dependencies with
Lean 4.35.0 and warnings as errors. Compile the test to an importable
`lib/tests/CompilerArithmetic.olean` before replaying
`lake env env LEAN_PATH=<lib>:<.lake/build/lib/lean> leanchecker --fresh tests.CompilerArithmetic`.
Elaborating the test source alone does not perform that stored-proof replay.
