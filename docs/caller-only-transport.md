# Caller-only execution across changed RAM

`EDSL.X86.Sequential.CallerOnly` proves exact memory transport for the production
sequential executor. Replacing memory preserves the complete success or exact
error under the stated caller-read agreement. A successful result carries the
replacement memory while retaining its result constructor, all registers, RIP,
flags and operand-read trace.

These execution laws underlie the [generic OS WP lift](caller-only-os-proofs.md).
They do not transport an arbitrary memory-dependent postcondition across
interference.

## Admitted instructions

`CallerOnly` is a decidable finite classification of the existing instruction
constructors, with their existing operand parameters:

| Group | Admitted constructors |
| --- | --- |
| Legacy private context | `leaEaxRdiDisp8`, `leaEaxRaxDisp8`, `movEaxEdi`, `movEaxEsi`, `mov32`, `cmpEaxZero`, `jnz`, `jrcxz`, `loopRcx` |
| Legacy return | `legacy ret` |
| Byte and 32-bit context | `xorSelf32`, `logicalReg32`, `logicalImm32`, `test32`, `cmp32`, `cmpReg8`, `subReg32`, `negReg32`, `movzxReg8`, `movReg32`, `movSignImm32`, `setcc`, `movImm8`, `cmovReg32`, `addImm32`, `inc32` |
| 64-bit context | `bswapReg64`, `shrOne64`, `rolCL64`, `test64`, `cmp64`, `cmpImm64`, `movReg64`, `cmovReg64`, `lea64`, `addReg64`, `logicalReg64`, `xchgReg64`, `xchgRax64`, `addImm64`, `inc64`, `dec64` |
| Branches and padding | `je`, `jcc`, `jmp`, `endbr64IbtDisabled`, `nop` with an existing `NopEncoding` parameter |

All DATA reads, ordinary stores, locked operations and syscalls are excluded.
`imulReg64` and `shiftRightImm32` remain excluded because their independently
undefined flag profiles require the vector interface. Native locked families
use a different instruction type and receive no admission here.

`CallerOnly.boolChoiceProfile` proves compatibility with the production Bool
interface. `readOnly` implies `CFG.readOnly`; the converse fails because that
classifier also admits DATA loads. `noStore` and `unlocked` exclude both store
intents and locked results. `result` proves that every actual successful result
is ordinary or the original RET and preserves the input memory.

`operandReads` gives the exact footprint: no operand reads for the context
operations, and one STACK8 read at the pre-instruction RSP for RET. `reads` and
`noDataReads` derive the corresponding facts from an actual successful production
observation. Instruction fetch is separate from these operand reads.

## Exact execution and error transport

The public theorems live in `EDSL.X86.Sequential.CallerOnly`:

- `execute_memory_eq` compares `execute` on an input with replacement memory to
  the original complete observation mapped by `Observation.mapMemory`.
- `execute_error_iff` preserves every exact `Error` in both directions.
- `executeWith_uniform_memory_eq` gives the same complete observation law for
  `executeWith` and `FlagChoices.uniform af`, using the proved Bool profile.

Registers, flags, RIP, instruction and Bool choice remain the same inputs.
The only memory premise is conditional on the instruction actually being RET:

```lean
readWord replacement (input.registers .rsp) =
  readWord input.memory (input.registers .rsp)
```

This compares the complete STACK8 primitive result, allowing equal faults as
well as equal returned words. It uses the current RSP. A readable original caller
slot supplies no agreement at a shifted RSP; changing the caller word can also
turn a valid return into a noncanonical-target rejection.

Other RAM and permission maps may differ subject to that agreement. Context-only
instructions need no memory premise. Success installs the replacement memory
in the output rather than retaining the old RAM. Branch and return canonicality
checks and all other production rejection behavior remain intact.

These laws execute an already decoded instruction. They require no code-memory
equality and do not establish that fetching from the replacement memory decodes
the same instruction. An actual step still needs its current fetch/decode proof.
The uniform-vector theorem supplies no transport law for the excluded vector-only
instructions.

## Integration and validation

OS use must separately identify current RSP with the protected original caller
slot, authenticate current code and decoding, supply current resource authority
and prove any postcondition stable under the permitted memory changes. This
module adds no OS WP rule, scheduler admission or passive-interference invariant.
Existing ISA and target limitations remain. It adds no frozen-corpus coverage,
source/compiler preservation, physical CPU/OS correspondence, fairness or
termination claim.

`tests/CallerOnlyTransport.lean` checks literal RET and ROL bytes through
production decoding and execution. It covers arbitrary context, architectural
RET frames, current-RSP inaccessible-byte faults, changed-caller rejection,
rotation against the independent bit-origin specification, selected undefined
OF and exact noncanonical branch faults across changed RAM.

Run `lake build EffectSimulationTests` under the existing strict profile:
warnings as errors, `autoImplicit=false`, 300000 heartbeats and recursion depth
128. `EDSL.All` imports the production module; the existing full-project gate
builds the target and imports the regressions into its dependency audit and fresh
kernel replay. See [validation](validation.md) for the full gate command.
