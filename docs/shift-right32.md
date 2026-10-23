# Low32 right shifts and independent flag choices

The sequential x86-64 model supports register-only `SHR r32, imm8` and
`SAR r32, imm8`, encoded as `C1 /5` and `C1 /7`. It accepts no prefix or one
W=0 REX prefix, and nonzero counts after masking the immediate to five bits.
Memory operands, zero effective counts, other widths and other shift encodings
are rejected. OR register encodings `09` and `0B` use the existing low32
logical-operation semantics.

For admitted shifts, the old low32 destination supplies the operand and the
complete destination receives the zero-extended result. Logical shift is
unsigned division by a power of two; arithmetic shift is signed division rounded
toward negative infinity. The last shifted-out old bit becomes CF. PF, ZF and SF
describe the result. AF is independently undefined; OF is defined for count one
and independently undefined for larger counts. Other flags, other registers and
complete memory, including permission maps, are preserved.

These rules follow the [Intel instruction reference, SAL/SAR/SHL/SHR](https://cdrdv2-public.intel.com/782151/253667-sdm-vol-2b.pdf),
printed pages 4-592–4-595. Hardware correspondence retains the sequential
profile's long-mode, disabled-CET and stable ordinary-memory assumptions.

## Reuse in a proof

Import `EDSL.X86.Sequential.ShiftRight32` for result, flag and state-transformer
laws. Use `EDSL.X86.Sequential.MachineChoices` for the production vector executor,
and `EDSL.X86.VCGen.Choices` for weakest preconditions over independently checked
code graphs. A plain Bool cannot express all AF/OF combinations, so the Bool
executor rejects this family.

`RegisterChoiceEffect` is the common boundary for register-local vector
operations. Each registered family proves its active-bit agreement, empty
operand-read trace and full-memory frame once. The shared CFG and resource
policy proofs consume those laws without new opcode cases. Compiler-specific
proofs still need an independent contract, a checked byte graph and the
corresponding generated obligations.

`EDSL.WordMath.Signum` and `EDSL.Scalar32.Signum` provide an independent signed
signum contract and reusable shift/order algebra. They include every low32
input, including the minimum signed value, and leave argument upper halves
arbitrary. These components alone do not certify a compiler artifact; the
published corpus measurement remains unchanged.

## Validation

`tests/SequentialShiftRight32.lean` checks the actual decoder and executor
against independent result and flag snapshots, both off-diagonal AF/OF choices,
masked counts, register banks, operand direction, truncation and per-byte fetch
permissions. `tests/WordMathSignum.lean` refutes wrong shift kinds, a wrong count,
XOR in place of OR and a reversed zero test using the independent order contract.
Both belong to the existing `ChoiceTests` Lake target.
