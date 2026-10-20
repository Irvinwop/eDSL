# Frozen compiler comparison clients

Validated with Lean 4.35.0 and warnings as errors: the library, new tests,
manifest-derived byte equalities and a cold source replay all passed. The test
audit accepted 6,791 project declarations with no unapproved axioms. The cold
replay rebuilt the 115-job library closure and its separate audit dependency.

`EDSL.X86.VCGen.CompilerComparisons` has two parameters: `Compiler.defaultGCC`
or `Compiler.defaultClang`, and `Operation.minimum` or `Operation.maximum`.
It selects the complete frozen `corpus/v1` output for `c_min_u64` or
`c_max_u64`. No compiler invocation, prefix stripping or reconstructed source
program supplies the candidate code. There is one graph/proof/registration
path for all four parameter combinations.

The recorded profiles are Ubuntu GCC 13.3.0 and Clang 18.1.3, using
`-std=gnu2x -O2 -march=x86-64 -mtune=generic -fno-pie`, with the recorded
warning options, and linked with `-no-pie -pthread -Wl,--build-id=none`.
The immutable provenance files and source/final-image seals are authoritative
for those recorded build inputs. The GCC ENDBR64 instruction remains present.

| Compiler | Operation | Complete bytes (hex) | Manifest file offset | Manifest VA | Size | Retired instructions |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| GCC | minimum | `f30f1efa4839fe4889f8480f46c6c3` | 11600 | 4205904 | 15 | 5 |
| GCC | maximum | `f30f1efa4839fe4889f8480f43c6c3` | 11616 | 4205920 | 15 | 5 |
| Clang | minimum | `4889f04839f7480f42c7c3` | 4832 | 4199136 | 11 | 4 |
| Clang | maximum | `4889f04839f7480f47c7c3` | 4848 | 4199152 | 11 | 4 |

The symbol, file-offset and VA columns are untrusted manifest labels in this
client. Independent symbol identity, literal full-ELF/current-mapping binding
and useful witnesses at those actual VAs require separate composition. The
existing `Comparison64.Domain` witnesses use their existing synthetic code
address; they establish useful raw/current domains without interpreting code.

The fixed `targetProfile` is the production sequential target: 64-bit long
mode, CET indirect-branch tracking disabled, CET shadow stacks disabled, and
multi-byte NOP support. Its ENDBR64 interpretation is a no-op that retires
once. The model does not inspect hardware feature controls, implement an IBT
tracker or enforce a shadow stack. These are environmental assumptions even
though the GCC build emitted a CET landing instruction.

`valid` checks proposed graph data against every actual instruction byte using
the shared production CFG checker. `generated_vc` reduces the production
VCGen WP with a shared tactic, for both compiler profiles and both operations.
Its remaining obligations use full64 CMP flag facts and mathematical natural
order; no per-instruction step proof, local VC, alternative evaluator, solver
result or future-run admission premise is supplied. GCC compares the operands
in the opposite order from Clang and uses non-strict conditions. Both are
checked against the independent `Comparison64.MathematicalResult` contract.

`verifies` yields a real production `Sequential.run` for every admitted initial
state and every AF stream. `Post` pairs the existing independent
`Comparison64.Post` with separate exact observations. It gives the unsigned
mathematical minimum/maximum of the full64 arguments, complete unchanged RAM
and permission maps, the actual stack-loaded return target, RSP advanced by
eight, SysV callee-saved registers, and all nonarithmetic flags. Other incoming
registers, flags and memory remain arbitrary. Arithmetic flags are unconstrained
by the contract. `observations` applies to any actual execution with the same
AF stream and proves the exact retired count and ordered operand-read list:
one eight-byte read of the original caller slot. Instruction fetches are
checked separately by executable code binding; they are not operand reads.

`raw_semantics` uses the generic `readOnly_policy_memory` theorem to establish
the policy at every actual continuing prefix. `readOnly_semantics` reuses
`Comparison64.readOnly_semantics_of_raw` to retain the complete original OS
world and the current code/caller loans before each step and after return.
`claim compiler operation` inhabits the existing registered `.minimum64` or
`.maximum64` task with independent useful raw/resource witnesses. No task,
grading profile, admission predicate or global instruction budget is added.

These are conditional exact-byte and current-resource claims. The callable
profile assumes stable ordinary RAM, live executable/caller mappings and
loans, four-level canonical addressing, disabled alignment checking, the
modeled SysV ABI, and no asynchronous interference, MMIO, signals or concurrent
agents between modeled steps. The code is fetched from actual current modeled
executable RAM. Native loading, lifetime of physical mappings, native thread
authentication, OS interference control and physical CPU refinement require
separate evidence. LA57, privilege transitions and exception handling remain
outside the callable model. The target does not silently weaken CET semantics.

The claims alone add zero frozen-corpus end-to-end certificates. Symbol
binding, full-ELF/current mapping and actual-address nonvacuity are separate
from this module; native loader/OS/physical-CPU correspondence is separate
again. Proof failure, timeout or unsupported input does not establish a defect.

`tests/VCGenCompilerComparisons.lean` exercises universal registered claims,
resource execution with real read origins, full-width/sign/borrow/equality
boundaries, GCC's additional retired prefix step, rejection of swapped task
contracts on a useful high-half input, and absent caller authority against the
real OS permission predicate. It audits imported and local project declarations.
Existing shared policy tests remain the authority for concrete caller-loan
revocation and unrelated-loan containment; this client does not duplicate them.

The isolated worker's ignored `.cache/corpus-claims-work/check-frozen.sh`
independently checks both frozen seals, the exact recorded compiler/linker
arguments and unique selected manifest rows, then reads their windows directly
from the final ELFs. It generates Lean equality checks from those independently
extracted bytes, binding the public constants to the frozen inputs. This is
validation evidence for byte provenance; formal symbol/current-image identity
still needs the separate composition described above.
