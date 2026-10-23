# Register immediate SUB32 and CMP32

The ordinary sequential x86 model supports register SUB32 and CMP32 with
sign-extended imm8 operands. Import the reusable contracts directly:

```lean
import EDSL.X86.Sequential.Immediate32
```

The contracts are in namespace `EDSL.X86.Sequential`; `EDSL.All` includes the
module in the full proof catalogue.

The shared `Sequential.Instruction`, production decoder and ordinary executor
contain two generic register forms:

| Bytes | Constructor | Length | Register effect |
| --- | --- | --- | --- |
| `83 /5 ib`, mod=3 | `subImm32 destination immediate false` | 3 | Write the zero-extended width32 subtraction result |
| `40/41 83 /5 ib`, mod=3 | `subImm32 destination immediate true` | 4 | Same; REX.B selects the register bank |
| `83 /7 ib`, mod=3 | `cmpImm32 left immediate false` | 3 | Preserve every GPR and upper half |
| `40/41 83 /7 ib`, mod=3 | `cmpImm32 left immediate true` | 4 | Same; REX.B selects the register bank |

All sixteen GPRs, including RSP, are ordinary register operands. The immediate
is the original fetched byte, sign-extended to **32** bits. If that byte has
unsigned value `b`, its signed value is `i = b` for `b < 128` and `i = b - 256`
otherwise. Both forms compute `(low32(register) - i) mod 2^32`, independently of
the original upper32 bits. SUB writes that result as a zero-extended full64
value and frames every other GPR. CMP discards the result and preserves the
complete register file. Neither reads operand memory, stores data, performs an
atomic operation or issues a syscall. Instruction fetch still authenticates
the code bytes. RIP advances by three bytes, or four with a prefix, using the
model's 64-bit addition; the data-read observation is empty. The existing
`cmp32` register/register and `cmpImm64` constructors retain their meanings.

Both forms use the existing `cmpFlags32` subtraction laws. With `x` the unsigned
low32 register value and `y = i mod 2^32`, CF is unsigned borrow (`x < y`) and
AF is low-nibble borrow (`x mod 16 < y mod 16`). PF is even parity of the
result's low byte; ZF tests `x = y`; SF is the width32 result sign; OF tests
whether `signed32(x) - i` lies outside `[-2^31, 2^31)`. Every other modeled flag
bit and the complete RAM/permission maps survive. All six arithmetic flags are
defined, so both Bool choices and uniform flag vectors have the same result.
SUB uses the same subtraction flag primitive as CMP. Addition of the negated
immediate would give different CF/AF.

For example, low32 zero minus immediate `ff` produces one with CF=AF=1. Low32
zero minus `80` produces 128, with CF=1 and AF=0. Low32 `80000000` minus one
produces `7fffffff`, setting OF and AF. CMP produces the same flags while
retaining every original register bit.

## Decoder and failure behavior

`decodeCounter32At` remains the common decoder for register-only `83` and `FF`
groups. Its opcode check, canonical-prefix check and original ModRM fetch keep
their order. After rejecting mod≠3, the `83 /5` and `/7` branches fetch the
original immediate at offset 2, or offset 3 after a prefix. Existing ADD32,
AND32 and INC32 dispatch is retained. Each required byte still uses the actual
`fetchByte` primitive and its canonicality, availability and execute-permission
checks. No extra suffix byte is required.

Register-only `83 /5 ib` and `/7 ib` decode to the two supported forms, with an
instruction-fetch fault when their required immediate byte is unavailable.
Still-excluded selectors `/1`, `/2`, `/3` and `/6` reject before an immediate
fetch. Memory forms reject after ModRM, before any SIB, displacement or
immediate fetch. Noncanonical W=0 group prefixes
`42..47` reject before ModRM; their enclosing prefix dispatcher still first
fetches the opcode. Repeated prefixes, operand/address overrides, LOCK, byte
widths, the `81` imm32 group and unmodeled SUB64 are excluded. Existing CMP64
remains a separately supported family and is never lowered to CMP32.

The legacy-first `decodeAt` order is unchanged: `83 f8 00` remains
`.legacy .cmpEaxZero`. `83 f8` with a nonzero immediate decodes to `cmpImm32`.
Its missing immediate still reports the original instruction-fetch fault.
Generic `decodeAt_transport` retains its public successful-fetch contract.
Its private shared-opcode proof transports the third byte when ModRM is
`f8`, preserving the distinction between legacy zero and new nonzero CMP.
It imposes no equality on failed source fetches. Every successful source fetch
at offsets 0–14 must be retained, including any available bytes after the
instruction; the decoder itself consumes only the selected instruction bytes.

## Contracts and shared propagation

[`EDSL.X86.Sequential.Immediate32`](../EDSL/X86/Sequential/Immediate32.lean)
provides `signExtend8_toNat32`, direct `execute_subImm32`/`execute_cmpImm32` and
`step_subImm32`/`step_cmpImm32` equations, `execute_subImm32_context` for the
arbitrary-state modular result and complete frame, and `execute_subImm32_signed`
for the signed modular result. `execute_cmpImm32_context` preserves the complete
register file. `execute_subImm32_flags` and `execute_cmpImm32_flags` state all
six mathematical subtraction flags; the corresponding `*_choice_independent`
lemmas equate both Bool choices. These proofs use existing word and `cmpFlags32`
lemmas, without proof holes, project axioms or unchecked solver results.

Length positivity/bounds, ordinary read/store/result/memory/flag laws, CFG
fallthrough and return exclusion cover both constructors. Both forms satisfy
raw `CallerOnly`; its constructive decider and exact memory/observation
transport apply. Transport of decoded execution across changed RAM still needs
the successful code-fetch agreement described above. The existing Bool-choice
and effect registration handles these fully defined forms through its ordinary
path. Literal rendering covers both constructors. These rules retain the
existing scheduler profiles and current-authority requirements.

`tests/Immediate32.lean` exercises real production decode/execute/step through
independent mathematical observations: signed-byte endpoints, borrow and nibble
borrow, signed overflow and full literal flags, arbitrary register frames,
SUB upper32 clearing, RSP/R12 and other high-bank mappings, every required byte's
read/execute faults, truncations, excluded groups/widths/memory/prefixes, legacy
priority, relocated code and exact CallerOnly memory transport. The proof
and test modules use `autoImplicit=false`, warnings as errors, 300000 heartbeats
and recursion depth 128. Closed observations use kernel-checked `decide`.

## Validation and limits

Run the strict regression target from the repository root:

```sh
lake build Immediate32Tests
```

The target is rooted at `tests.Immediate32` and fixes warnings as errors,
`autoImplicit=false`, 300000 heartbeats and recursion depth 128. Building it
compiles the production contracts and regression proofs. Compilation is
separate from an aggregate axiom audit, fresh kernel replay and full source CI.

The full-project gate also builds `Immediate32Tests` and `EDSL.All`:

```sh
bash scripts/verify-corpus-certificates.sh --full-project
```

Its stored `CorpusFullReplay` aggregate explicitly imports `tests.Immediate32`;
the production contracts enter through `EDSL.All`. The gate audits the aggregate
and replays its stored proofs in a fresh kernel environment alongside the
existing catalogue, corpus checks and registered packet gates. It records source,
input and module identities. Running a target build alone supplies no evidence
that this full gate or full source CI has passed. See
[build and validation](validation.md) for the wider validation procedure.

The unsupported-group cases in `tests/SequentialCounter32.lean` and
`tests/SequentialParityISA.lean` use `83 d0 01` (excluded `/2` ADC). The former
`83 e8 01` case is now a supported SUB instruction; the revised cases retain
meaningful rejection coverage for the current grammar.

The GCC `83 ee 02` and Clang `83 fe 08` encodings are recognized by this generic
family. Recognition of those instructions supplies no complete counter-program
certificate. Frozen corpus bytes, specifications and proofs are unchanged, so
this adds no corpus credit, per-program counter proof or TSO RMW certificate.
Support is limited to the subset above and the existing ordinary sequential
target/environmental assumptions. There is no physical hardware refinement,
compiler preservation, scheduler fairness or concurrent execution correctness
claim.
