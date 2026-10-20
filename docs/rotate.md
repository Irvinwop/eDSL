# Full64 rotation and reusable ROL semantics

The registered `rotateLeft64` task specifies a left rotation independently by
the origin of each output bit. Full64 RDI supplies the value; low32 RSI modulo
64 supplies the count, with arbitrary upper32 RSI. Every value and count is
admitted. The unchanged frozen `c_rotl64` outputs have complete named-file
certificates through `EDSL.Corpus.V1.RotationCertificates`:

| Artifact | Virtual address | Bytes | Modeled retired instructions |
| --- | --- | ---: | ---: |
| GCC | `0x402de0` | 13 | 5 |
| Clang | `0x401350` | 9 | 4 |

The counts include RET and GCC ENDBR64; they are execution conclusions, not
physical timing or minimum-cost claims. Shared generated-WP proofs establish
the independent result for every undefined-flag choice stream. The existing
scalar and ELF constructors retain full RAM and permissions, the original
caller, current code authority, ABI obligations and every-prefix read authority.
`RotationTests` includes body, resource, instruction and grading regressions.
The [measurement record](../corpus/measurements/parity-rotation-v1/) distinguishes
the full local gate, installed packet checks and publication CI.

## Shared instruction foundation

`EDSL.X86.Sequential.Rotate` supplies reusable local-machine proofs for
`Instruction.rolCL64 destination`. The production authenticated decoder,
executor, shared execution engine, CFG discovery/checking, bounded VCG,
whole-memory frames, return proofs and current-resource adapters consume this
same instruction. No program-specific evaluator or second VCG is introduced.
The instruction foundation can be reused without importing a corpus client.

## Encoding and semantics

The admitted bytes are exactly one `48` or `49`, `D3`, and a register-mode
`/0` ModRM. Length is three. B selects RAX..RDI or R8..R15. RSP/R12 need no
SIB; RBP/R13 need no displacement in register mode. The helper
`decodeREXWAt` assumes its prefix was authenticated by its caller; `decodeAt`
and `step` authenticate current executable RAM. All three successful fetches
are needed, and no byte after ModRM is fetched. An inaccessible instruction
byte reports its exact address. REX.R/X aliases, extra/legacy prefixes, other
widths, memory operands, immediate counts and other group operations remain
unsupported; rejection does not claim an encoding is invalid on hardware.
Noncanonical fetches retain the existing `inaccessibleInstruction` behavior.
Rejected REX aliases stop after the opcode; rejected memory/group forms stop
after ModRM, without trying to fetch an address suffix.

Both the destination and RCX are read from the prestate, including destination
RCX. The effective count is `rolCount64 oldRCX = oldRCX.toNat % 64`, proved
equivalent to old CL modulo 64. `rolCount64_low32` bridges arbitrary low32
inputs zero-extended by MOV32. The result satisfies the independent bit-origin
relation `WordMath.IsRotateLeft64`, using `rotateLeft64_satisfies` rather than
a new scalar specification. Count high bits do not restrict the domain.

| Masked count | Destination | CF | OF |
| --- | --- | --- | --- |
| 0 | original full word | preserved | preserved |
| 1 | rotate left | result bit 0 | result bit 63 XOR result bit 0 |
| 2..63 | rotate left | result bit 0 | arbitrary independent Bool |

Every other flag, including AF/PF/ZF/SF, is preserved. Undefined OF is a
single unconstrained value, not unrestricted program behavior. Counts 64/128
preserve all flags; 65 has defined OF. `RolFlags64Admissible` specifies this
flag table without calling `rolFlags64`. The admissibility equivalence and
observed-witness theorem prove that both Bool executions exhaust exactly this
contract; inactive choices need not yield distinct outcomes.

A successful step is always plain `.next`, RIP + 3, with no operand reads,
stores, locked event, syscall or return. Full Memory equality preserves the
read function and both permission maps; all fifteen other GPRs survive.
The zero-count theorem additionally preserves the entire register function
and flags. Fallthrough RIP uses existing modular Word arithmetic; a subsequent
fetch checks canonicality and accessibility.

## Neutral choice interface and migration

`ChoiceFlag` names `af` and `of`, with `bitIndex` and `mask`.
`Instruction.choiceFlag : Instruction → State → Option ChoiceFlag` selects AF
for the existing XOR/TEST/logical/SHR instructions, OF for ROL exactly when
old RCX's masked count exceeds one, and none otherwise.

There is still one Bool per retired instruction. The types of `execute`,
`step`, `Choices`, `Engine`, `run`, `wp` and `decidableWP` are unchanged.
Existing binders named `af` are retained to avoid breaking named arguments;
the Bool's general meaning is now the flag selected by `choiceFlag`.
Fresh schedule positions are consumed even when ignored. IMUL stays
unsupported: its undefined SF/ZF/AF/PF require four independent bits (16
combinations), which one Bool cannot express.

The old theorem

```lean
execute_af_independent state instruction left right
  (noChoice : instruction.choosesAF = false)
```

is removed. That implication would be false for ROL. Its replacement is

```lean
execute_choice_independent state instruction left right
  (noChoice : instruction.choiceFlag state = none)
```

The actual old callers are the two proofs
`execute_negReg32_af_independent` / `execute_bswapReg64_af_independent` in
`Sequential/Unary.lean`, and branch pruning in `VCGen/Core.lean`. The unary
proof statements stay unchanged. The VCG's private decision helper is renamed
`decidableChoice` and prunes only when the actual state's neutral metadata is
none; otherwise it checks both Bool branches. `Instruction.choosesAF` keeps
its original AF-only type and meaning. `choiceFlag_af_iff` proves this identity.
`tests/native/RegisterCapture.lean` and its old policy are unchanged.

`execute_choice_context`, `ChoiceStateAdmissible`,
`execute_choice_observed_witness` and `execute_choice_admissible_iff` apply to
all active AF/OF instructions: observations, registers, memory and RIP agree
outside the selected flag, that bit equals the supplied Bool, and an observed
bit gives an exact execution witness when the complete defined-state frame
matches. These facts establish model admissibility, without promising that a
particular processor realizes both undefined outcomes.

CallReturn's `choiceFlag` delegates to Sequential; its extension instructions
add no choices. `liftSequential_choiceFlag`, `execute_liftSequential` and
neutral independence preserve the shared complete execution observation.
`current_rolCL64_step` retains the same original OS world, caller/code loans,
permissions and ownership epochs through a decoded step. The existing
`VCGen.PureCall` bridge continues to quantify all choice streams and to retain
the original readable return slot; changing RSP grants no new read authority.

## Assumptions and validation scope

The existing target profile assumes long mode, four-level canonical addressing,
stable ordinary modeled memory, CET/IBT/shadow stacks disabled and no
asynchronous interference. Operand addresses and a stack are unnecessary for
ROL itself. Physical CPU/Linux/loading, exception-priority, PUSHFQ observability,
source/compiler preservation and concurrent refinement are not established.

`tests/SequentialRotate.lean` checks independent literal counts/results/flags,
AF preservation, both OF choices, RCX aliasing, both banks, fetch permissions,
truncation/prefix/group rejection, graph/literal integration, real generated
VCG execution and current-resource policy. It refuses mutated actual bytes
and either fixed value for undefined OF. `tests/RotateAudit.lean` audits the
production proof dependencies, including the shared resource bridge.

Lean is pinned to 4.35.0 with warnings as errors. The focused validation
checks the production import closure and instruction tests, audits theorem
dependencies, and replays the resulting objects in a fresh Lean kernel.
Those focused checks cover the instruction foundation. The registered client
and complete-file certificate above additionally require the body, resource,
packet and aggregate checks recorded in the measurement. Native conformance
and physical CPU refinement remain separate obligations.

## Primary references

Intel SDM [Vol.2B RCL/RCR/ROL/ROR](https://cdrdv2.intel.com/v1/dl/getContent/671241)
and [Vol.2A REX fields / IMUL](https://cdrdv2.intel.com/v1/dl/getContent/671199)
are the review's references. The stable official
[Vol.2B 253667-080US PDF](https://cdrdv2-public.intel.com/782151/253667-sdm-vol-2b.pdf)
was inspected as the content endpoints were unavailable to the browser.
Its ROL64-CL encoding table and explicit Flags Affected rule (printed pages
4-527, 4-529–4-530) establish the six-bit count, masked-zero preservation,
defined one-bit OF and preserved AF/PF/ZF/SF. This model follows the explicit
flag rule over the unqualified undefined-OF pseudocode branch.
