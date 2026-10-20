# Full64 parity registration

`parity64` fixes `Arithmetic64.parity64`: full64 RDI is the sole argument,
every word is admitted, and unsigned low32 RAX equals the independent
cardinality of the set input bit positions modulo two. Upper32 RAX is
unconstrained. The useful witness `0x8000000000000001` inhabits the present raw
and current-resource domains without restricting universal admission.

The generic grader maps `parity64` to this fixed task. Candidate bytes and
proof terms cannot select a different mathematical contract. The existing
`PureCall.Candidate` constructor supplies useful admission even for unsupported
instruction bytes; admission does not assume successful execution.

`EDSL.Corpus.V1.ParityCertificates` composes `Scalar.certificate`, the neutral
`ELF.CallerResources.Stack.standard` provider, the complete named-file checks,
and the accepted generated body proofs. Each compiler's constructor supplies
only its own semantic evidence. No interpreter, runtime or instruction chain
is added for parity.

| Exact `c_parity_loop` artifact | Selected virtual address | Symbol length | Certificate |
| --- | --- | --- | --- |
| Default GCC | `0x402e20` | 33 bytes | `ParityCertificates.gcc_certificate` |
| Default Clang | `0x401390` | 36 bytes | `ParityCertificates.clang_certificate` |

The symbol extents retain GCC's ENDBR64, both RETs and padding, and Clang's
six-byte NOP. Complete ELF contents, name, extent and executable LOAD selection
are checked together. The standard logical caller supplies its original
eight-byte stack slot at `0x700008` and return address `0x654321`.

The registered claim includes total execution for every AF stream, the scalar
ABI return and unchanged RAM, current original caller/code authority at return,
and the original read authority at every execution prefix. The target assumes
stable ordinary modeled RAM, canonical code/stack/return addresses, supplied
logical ownership and caller loans, disabled CET/IBT/shadow stacks and no
asynchronous interference. Native CPU/Linux refinement, source/IR/compiler
preservation, concurrency and physical cost are separate obligations.

`ParityTests` owns the focused ISA/audit, body, registered resource and grading
test roots. `tests.GradingParity` passes both literal whole-symbol claims through
the existing controller with default limits. It requires rejection of the
same-shape `populationCount64` task and a changed final RET specifically as
`kernel declTypeMismatch`. `tests.ParityResources` applies the registered
complete-file certificate through `Certificate.resource` to independently
specified even/odd answers, retaining the original return, stack, RAM and
resource guarantees. The earlier `tests.ParityBodies` covers zero, highest bit,
all ones, separated bits, dirty scratch state, missing return slots and actual
STACK versus DATA read authority.

Build the focused regressions with `lake build ParityTests`. Run
`bash scripts/verify-corpus-certificates.sh --full-project` for the complete
catalogue, aggregate axiom audit, fresh kernel replay, final-file checks and
installed proof-packet checks. The packet checks exercise both body and
reference forms at the default limits and require the precise rejection
diagnostics described above.

Registration, code discovery and a successful focused test are separate from
end-to-end corpus acceptance. The [implementation status](implementation-status.md)
and [corpus results](compiler-corpus.md) record accepted coverage; measurement
records identify the exact inputs and validation scope.

## Shared instruction support

The client uses the production sequential decoder, executor and VCG. New
programs can reuse `X86.Sequential.ParityISA` without importing a frozen
corpus proof. The supported encodings added here are register XOR32 (`31/33`),
AND32 with a sign-extended immediate byte (`83 /4`), register CMP64 with a
sign-extended immediate byte (`48/49 83 /7`), and the exact six-byte padding
sequence `66 0f 1f 44 00 00`. Other constructed logical operations having an
executor definition does not imply their byte encodings are supported.

`execute_logicalReg32_context`, `execute_logicalImm32_context` and
`execute_cmpImm64_context` describe arbitrary states and register operands.
They provide result, full-memory, nondestination-register and nonarithmetic-flag
facts without adding memory-read authority. Logical32 writes clear the upper
half of the destination and quantify over the undefined AF choice; CMP defines
its subtraction flags. The choice witness lemma relates admitted logical-flag
observations to that model without claiming hardware realizes both AF values.

For another scalar loop, use `vcgen_graph`, checked CFG validity, sparse
cutpoint invariants and `pureCall_semantics_of_cutpoints`. The parity-specific
work is the cardinality-modulo-two invariant and strict unsigned remainder
rank. ABI, stack reads, original caller authority, every-prefix preservation
and complete-file binding use the shared adapters described in
[Verify a new function](verify-a-function.md). No new command driver or
program-specific evaluator is required.
