# Independent flag choices

Some x86 instructions leave several status flags undefined. A verifier must
admit every permitted combination: assigning all undefined bits the same
Boolean would omit executions. The shared engine accepts an arbitrary
`ChoiceStream Choice`, with one fresh element per retired instruction.
Returning executions record the complete final state, exact instruction count
and ordered operand reads. Continuing blocks and fault prefixes record their
finite costs and reads; a failed bounded run returns only `Error`.

## Vector execution and checking

[`FlagChoices`](../EDSL/X86/Sequential/FlagChoices.lean) contains independent
CF, PF, AF, ZF, SF and OF components. `representatives active` enumerates a
declared list of active bits. Every valuation agrees with a representative
on those bits; four distinct bits have sixteen representatives. Finite checking
implies universal quantification only with `Invariant active predicate`, which
proves that inactive bits cannot affect the predicate. Duplicate list entries
can repeat representatives.

[`MachineChoices`](../EDSL/X86/Sequential/MachineChoices.lean) provides
`executeWith` and `stepWith`. Each actual instruction and prestate determine
the active bits. `stepWith` decodes current executable memory and retains
fetch faults, operand-access checks and complete observations.
[`ExecutionChoices`](../EDSL/X86/Sequential/ExecutionChoices.lean) provides
`runWith`, `ExecutesWith`, `BlockWith` and `AllExecutionsWith`.

[`VCGen.Choices`](../EDSL/X86/VCGen/Choices.lean) provides bounded `wpWith`,
`decidableWPWith`, `checkChoices` and byte-bound soundness. The decision procedure
enumerates only active bits, using a proof of equality of the entire observation
when the active bits agree. `CheckedTraceWith` records actual decoded reads,
their permission and successful memory access at their original states.
Zero fuel, faults, missing successors, syscalls and atomic boundaries fail closed.
[`TacticsWith`](../EDSL/X86/VCGen/TacticsWith.lean) supplies reusable graph-based
proof reduction; proposed graphs still require the production byte check.

## Register-only IMUL

The vector path supports the four-byte REX.W `0F AF /r` form with register
operands. REX.R/B extend the registers and REX.X is ignored. Other widths,
LOCK, repeated prefixes and memory operands remain unsupported. Required bytes
must be executable; a missing byte reports its actual fetch address.

[`Multiply`](../EDSL/X86/Sequential/Multiply.lean) captures both prestate
operands, writes the low64 product and sets CF=OF from signed overflow.
PF/AF/ZF/SF are independently undefined, including for a zero result.
Other registers, nonarithmetic flags and complete memory permissions are framed.
The flag contract follows [Intel SDM volume 2A, IMUL](https://cdrdv2-public.intel.com/812383/253666-sdm-vol-2a.pdf),
PDF pages 610–612, revision 253666-082US. These abstract choices conservatively
cover unspecified flag values; they do not assert that hardware realizes every pattern.

[`WordMath.Multiplication`](../EDSL/WordMath/Multiplication.lean) defines the
result using unbounded natural multiplication modulo the word size, and
characterizes signed overflow using integer arithmetic. The independent
contract names no instruction or successful execution.
[`MultiplyBodies`](../EDSL/Corpus/V1/MultiplyBodies.lean) applies the shared vector
VCG to both unchanged frozen `c_mul_mod64` bodies, including GCC's ENDBR64.
The body contract covers every full64 argument pair and vector stream, the
original return-slot read, ABI and complete memory frames, and modeled counts
of GCC4/Clang3 instructions. [`MultiplyWindows`](../EDSL/Corpus/V1/MultiplyWindows.lean)
separately authenticates each complete named extent in its frozen ELF file.
These examples supply small graph records checked against the bytes. Automatic
term-based graph discovery for these bodies exceeds the strict elaboration
limit; it is not required by the soundness theorem.

## Compatibility and remaining work

Existing `execute`, `step`, `Choices`, `run` and Bool VCG APIs retain their
signatures. The Bool executor rejects IMUL. Equality of possible finite Bool
and vector outcomes requires the explicit old-prefix `Safe` premise; there is
no global simulation of the extended ISA by one Bool. Existing uniformly
bounded total-correctness proofs transfer without new admission assumptions,
because their universal totality supplies that safety. Finite simulation
alone does not imply unbounded termination.

`ExecutionModel` selects either the original Bool executor or the complete
flag-vector executor. `ReadOnlyPolicyFor`, `ReadOnlySemanticClaimFor` and
`PureCall.ELFCertificateFor` retain the original admission and current-resource
contracts for that selected execution domain.
`VCGen.pureCall_semantics_of_generatedWith` lifts one byte-checked vector WP
proof through the shared scalar/resource bridge; clients do not need a new
resource-preservation proof for each program. The original Bool APIs remain
available, with exact compatibility theorems.

`Grading.registry` binds an execution model and its entire independent task.
Legacy identifiers retain the original Bool contracts. `multiplyModulo64` fixes
the vector model and full64 natural multiplication modulo 2^64, together with
the shared resource policy. `Corpus.CertificateFor` adapts neutral ELF
certificates to that trusted binding, retaining useful-domain evidence
separately from universal resource admission.

The objective grader accepts serialized reference/body packets for both frozen
multiply bodies under its default limits. The packet gate checks client
isolation, raw and synthetic ELF-container acceptance, and changed-byte/extent
rejection. Exact original named-ELF binding comes from `MultiplyRegistered`,
not those synthetic containers. The [multiplication measurement](../corpus/measurements/multiply-modulo64-v1/)
records the accepted source, full corpus gate and stored acceptance assertions
replayed in a fresh kernel environment. At that milestone, coverage was
**19/40 functions and 38/80 artifacts**, including three distinct concurrent functions.
Native CPU/Linux correspondence, concurrency and source/compiler preservation
remain separate obligations. The callable target assumes stable ordinary RAM,
64-bit mode, disabled CET/IBT/shadow stacks and no asynchronous interference.

The [signed signum measurement](../corpus/measurements/signed-signum32-v1/)
adds both original `c_sign_i32` artifacts through the same registry, vector VCG
and resource adapters, together with reusable low32 SHR/SAR rules. Its accepted
full corpus gate and stored assertions establish conditional coverage of
**20/40 functions and 40/80 artifacts**, including three concurrent functions.
See [shift and signum contracts](shift-right32.md) for all-input and flag scope.

The [IMUL regressions](../tests/SequentialMultiply.lean) exercise sixteen literal
flag words, signed boundaries, aliases, register banks and precise faults.
A decoded IMUL/JZ/JP program returns all four values 0,1,2,3: the vector checker
accepts their union and rejects the diagonal-only {0,3} contract that a correlated
Bool model would wrongly accept. It also rejects denied return-read permission
despite readable RAM. These checks accompany axiom audits and fresh kernel replay.
