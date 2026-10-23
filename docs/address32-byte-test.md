# LEA32 and immediate byte TEST

The sequential x86 model supports 32-bit effective-address results and
immediate byte tests through reusable decoder, executor and resource
contracts. These instruction families alone add no certified corpus results.

The frozen GCC `c_counter_worker` manifest window contains
`f30f1efa85f67427 8d46ff 40f6c601 740f ...`:
`LEA EAX,[RSI-1]` starts at offset 8, and `TEST SIL,1` at offset 11.
The complete function is 49 bytes. The Clang window is 86 bytes and uses other
forms, including `83e107`, rather than these instructions. Exact manifest
windows remain the inputs to corpus certification.

[`Instruction`](../EDSL/X86/Sequential/Model.lean),
[`Decode`](../EDSL/X86/Sequential/Decode.lean), and
[`Machine`](../EDSL/X86/Sequential/Machine.lean) carry the two reusable families.
They have no program-specific counter, ABI, loop, scheduler, or evaluator rule.

## LEA32

`Instruction.lea32 destination address prefixed` evaluates the existing
full64 `Address` in the **prestate**, truncates the effective address to low32,
and zero extends it to the full64 destination. It preserves every flag bit,
every other full64 GPR, and the entire RAM/permission maps. It performs no
operand read, store, canonicality check, DATA access, or stack access. RSP is
an ordinary possible destination or address register; its use grants no
permission for a later RET.

The accepted bytes are `8D /r` with no prefix or exactly one W=0 REX byte
`40..47`. REX.R/B extend the destination/base and REX.X extends a SIB index.
X has no effect without SIB. Every low32 destination in both GPR banks is
available with the appropriate encoding. Address registers remain full64.
There is no `67` address-size override and no `66` operand-size override.

The address subset is precisely the existing LEA64 subset:

| ModRM mode | Plain address | SIB address |
| --- | --- | --- |
| mod00 | Real base except encoded rm5; rm4 requires SIB | Real base and real index, scale 1/2/4/8; encoded base5 rejects even with B=1; encoded index4 rejects with X=0 and selects R12 with X=1 |
| mod01 | Every real base, including RBP/R13, plus signed disp8 | Every real base, optional real index, scale 1/2/4/8, signed disp8; encoded index4 with X=0 means no index, with X=1 means R12 |

Register mode, mod10/disp32, RIP-relative, absolute/missing-base forms, mod00
no-index SIB, repeated REX, legacy prefixes, and other widths reject. Existing
REX.W LEA64 forms retain their previous meaning. The legacy-first decoder
still returns `.legacy (.leaEaxRaxDisp8 d)` for `8d40ib` and
`.legacy (.leaEaxRdiDisp8 d)` for `8d47ib`.

Lengths are `(prefixed ? 3 : 2) + address.suffixBytes`. SIB and an explicit
zero displacement retain their actual encoded length. The prefixed path
reuses `decodeQWordAddressAt` and `decodeDisp8AddressAt`; the unprefixed path
uses the same subset at its shorter offsets.

[`Address32`](../EDSL/X86/Sequential/Address32.lean) contains a full destination,
width, flags, register, memory, and RIP context contract, signed disp8/SIB
integer laws modulo the result width, and the narrowing relation to the
existing `execute_lea64_context`. Its address arithmetic lemmas apply to the
same `Address.eval` used by LEA64. Bool and vector choices are inactive, and
the current OS authority wrapper retains the same complete memory/world.

## TEST low8 immediate

`Instruction.testImm8 operand immediate prefixed` ANDs the old operand's
low8 with the **raw imm8**, discards the result, and preserves the entire
full64 register file and RAM/permissions. It sets CF=OF=0, PF to even parity
of the byte, ZF to byte equality with zero, and SF to result bit7. It preserves
all bits outside the six arithmetic status flags.

AF is **undefined**. `logicalFlags8` uses the existing `statusFlags` constructor
and `LogicalFlagsAdmissible` contract. The Bool argument selects AF, and
`executeWith` projects only `choices.get .af`. `choosesAF = true`,
`choiceFlag = some .af`, `undefinedFlags = [.af]`, and `boolChoiceProfile = true`.
The model admits either AF value, independently of the old AF, operands, and
other vector components. This overapproximation makes no claim that hardware
realizes both values. AF is neither forced to zero nor preserved.

Accepted encodings are register-only `F6 /0 ib`:

| Prefix | Accepted operands |
| --- | --- |
| None | AL, CL, DL, BL (rm0..3 only) |
| Exactly `40` | AL, CL, DL, BL, SPL, BPL, SIL, DIL |
| Exactly `41` | R8B through R15B |

Without REX, rm4..7 denote AH/CH/DH/BH. They are unmodeled and reject before
fetching the immediate. The canonical `40/41` subset follows the existing
byte-immediate/SETcc and opcode-group API patterns. Unused REX.R/X aliases
`42..47`, REX.W, legacy prefixes, repeated REX, memory F6, all nonzero group
selectors (including /1), and accumulator opcode A8 are unsupported. They
are not lowered into a different TEST or logical operation. Length is four
with REX and three without it.

[`TestImmediate8`](../EDSL/X86/Sequential/TestImmediate8.lean) contains the
mathematical byte-mask law, complete register/memory/defined-flag contracts,
AF outcome completeness, inactive vector independence, choice-frame laws,
and current OS memory-authority transport.

## Errors and integration

Every required opcode, ModRM, SIB, displacement, and immediate byte is fetched
through `fetchByte`. A missing, unreadable, nonexecutable, or noncanonical
instruction byte reports `inaccessibleInstruction` at that actual address.
Unsupported addressing modes reject before an unneeded displacement fetch;
SIB restrictions are checked after fetching SIB. For TEST, unsupported
canonical-prefix aliases reject after the operation byte and before ModRM;
memory, selectors, and high-byte banks reject after ModRM and before imm8.
The enclosing legacy-first grammar retains its existing prefix/error order:
for example initial `67` reports `unsupportedOpcode 67`, while recognized
padding/LOCK prefixes retain their existing suffix checks and errors.

Success transport retains the same fifteen-byte fetch extent. `DecodeTransport`
classifies 8D as a shared legacy opcode, and transports the required third byte
for legacy `8d40`/`8d47` as well as existing `83f8` overlap. Its premise covers
every successful source fetch below offset 15, including any mapped trailing
bytes. Failed source fetches impose no condition. A finite source code window
ending at the instruction therefore needs no following byte.

Both new constructors are admitted by read-only CFG and caller-only policies,
with ordinary fallthrough, no store intent, no operand reads, and no locked
result. The existing generic vector registration needs no new branch: both
families stay in its Bool-compatible path.

The shared `execute_choice_context` theorem includes the TEST AF case.
`EDSL.All` exports both contract modules, and the strict `AddressByteTests`
Lake target includes both regression modules. The full-project corpus gate
builds that target and includes the regressions in its fresh replay.

[`tests/Address32.lean`](../tests/Address32.lean) and
[`tests/TestImmediate8.lean`](../tests/TestImmediate8.lean) observe public
decoding/stepping against literal results, flags, banks, and lengths. They
cover signed displacement endpoints, aliases, SIB scales, noncanonical operand
addresses without data access, arbitrary-state frames, AF choices, vector
projection, exact truncations/read/execute faults, unsupported prefixes,
high-byte rejection, and rejection before unnecessary suffix fetching.
The contract and regression modules use warnings as errors, `autoImplicit=false`, 300000 heartbeats, and recursion
depth 128. The proofs use ordinary kernel-checked terms under the repository axiom
allowlist.

The contracts remain conditional local ISA semantics under `targetProfile`:
64-bit mode, CET/IBT and shadow stacks disabled, and its existing instruction
support assumptions. Abstract flag/RAM framing is not native or physical
processor evidence. There is no new compiler, ABI, memory-model, corpus,
frozen-function, runtime, or concurrency certification claim.
