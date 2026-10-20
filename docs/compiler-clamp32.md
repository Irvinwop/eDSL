# Signed low32 clamp through shared verification rules

`Scalar32.clampSigned` fixes signed 32-bit value, lower and upper arguments in
RDI, RSI and RDX. Only their low32 bits are bound; upper halves remain arbitrary.
Admission requires `lower ≤ upper`, including equal endpoints and both signed
extremes. The independent `Clamped` relation requires an in-range result, the
original value inside the interval, and the nearest endpoint outside it.
Usefulness selects an interior witness and does not restrict admission.
The fixed `clampSigned32` registry entry owns this specification.

`X86.VCGen.CompilerClamp32` checks both unmodified frozen compiler bodies using
production `CFG.check` and discharges their generated WP through the existing
PureCall adapter. It introduces no instruction interpreter, program-specific
resource Domain or future-execution premise.

| Compiler | Complete bytes | Retired instructions |
| --- | --- | ---: |
| GCC | `f30f1efa39d789f00f4ed739f70f4dc2c3` | 7 |
| Clang | `89d039d70f4cc739f70f4cc6c3` | 6 |

GCC retains its ENDBR64 and the legacy-first decoder's MOV EAX,ESI form.
Both clients use CMP32 and register CMOV32. A false CMOV32 condition still clears
the destination's upper32, including an RSP destination or self alias; the
[shared ISA rules](sequential-cmov32.md) model that behavior explicitly.

`raw_semantics`, `executes` and `observations` cover arbitrary initial registers,
flags and AF streams subject to the present code, argument and original caller
slot contract. The result includes the independent mathematical relation, full
RAM and permission equality, actual caller return, RSP advancement, SysV
callee-saved registers, nonarithmetic flags and every-prefix resource policy.
Separate observations establish zero upper RAX, the exact 7/6 counts and the
single original STACK8 operand read. Instruction fetches are outside that
operand trace. Counts establish no minimum, physical micro-operation or timing
claim.

Tests exercise signed overflow boundaries, equal INT32_MIN/MAX endpoints,
arbitrary upper halves, actual decoded execution, original caller authority and
signed-to-unsigned condition mutations. A GCC observation also checks RDX after
a false CMOV32 so later RAX narrowing cannot hide an incorrect retained high
argument half. The actual controller/kernel accepts the fixed clamp claim and
rejects an unrelated valid program proof under this task.

The [named final-file adapter](corpus-clamp-windows.md) separately checks the
complete ELF, unique symbol, extent and actual-address resources. The profile
requires sequential long mode, CET/IBT and shadow stacks disabled, stable
ordinary modeled RAM and supplied caller resources. Native ownership, full
native ABI alignment, physical CPU/OS refinement, source preservation,
asynchronous interference and concurrent histories remain separate obligations.
