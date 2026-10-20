# Corpus-selected low32 logic and CMP64 immediates

`EDSL.X86.Sequential.ParityISA` supplies reusable machine rules for arbitrary
registers and states. It extends the shared decoder and executor; there is no
parity-program interpreter or parity contract proof.

| Supported family | Bytes | Prefixes | Length |
| --- | --- | --- | --- |
| XOR32, r/m destination | `31 /r`, mod=3 | none or one `40`–`47` | 2 or 3 |
| XOR32, reg destination | `33 /r`, mod=3 | none or one `40`–`47` | 2 or 3 |
| AND32, signed imm8 | `83 /4 ib`, mod=3 | none or one `40`/`41` | 3 or 4 |
| CMP64, signed imm8 | `83 /7 ib`, mod=3 | exactly `48`/`49` | 4 |
| NOP6 | exactly `66 0f 1f 44 00 00` | part of exact bytes | 6 |

XOR32 uses REX.R/B for its register banks and ignores X. Group-1 immediate
forms admit only the listed canonical prefixes; unused R/X bits reject.
Memory operands, additional prefixes, other widths, other group selectors,
imm32 encodings and accumulator-special encodings do not acquire support.
Existing ADD/INC and full64 logical families retain their prior acceptance.
Unprefixed `31 /r` self-XOR keeps the existing `xorSelf32` constructor.
The legacy decoder and its success embedding retain their original interface.
Every required instruction byte needs successful executable fetch; missing
bytes keep their exact `inaccessibleInstruction` address.

`LogicalOp.eval` now works at any BitVec width. `logicalReg32` and
`logicalImm32` share `LogicalOp` and `logicalFlags32`; their decoder currently
admits only the XOR-register and AND-immediate operations listed above.
Constructing a semantic instruction does not establish a byte encoding.
Both operands use the prestate, including self aliases and RSP. Results are
computed at width32 and zero extended over the entire destination. The AND
immediate is sign extended from eight bits to 32 before the operation.
CF/OF clear; PF uses the low byte and ZF/SF use the 32-bit result. AF is the
sole undefined flag, selected independently on every logical step. The existing
`LogicalFlagsAdmissible` family characterizes both outcomes, and
`logicalFlags32_observed_witness` recovers the AF witness of a concrete admitted
flag observation. It does not claim hardware realizes both choices.

`cmpImm64` subtracts the imm8 sign extended to 64 bits from the old register.
It writes no GPR. CF and AF are unsigned borrows; OF is signed subtraction
overflow. All six arithmetic flags are defined, independently of the executor's
AF argument. `execute_cmpImm64_context` connects JA to strict unsigned order.
NOP6 preserves every flag and register without evaluating its apparent address.

The context rules preserve complete RAM, read/execute/write permission maps,
all nondestination GPRs and every nonarithmetic flag. These families have no
operand reads, store intents, locked events or system effects. The shared CFG,
fetch transport, CallReturn lifting, literal generation and VCG consume the
same production semantics. No weaker fallback is introduced.

The unchanged frozen GCC and Clang row12 `c_parity_loop` windows are accepted
by the shared CFG checker with exact instruction spans and branch targets.
`tests/SequentialParityISA.lean` checks those layouts and independent literal
instruction vectors, including high halves, banks, aliases, signed immediates,
defined flags, undefined AF choices and rejection/fetch boundaries.
The generic VCG also checks a synthetic signed-AND/RET window against independent
value, count and stack-read contracts; it rejects a fixed AF promise and a
changed immediate byte.
`tests/ParityISAAudit.lean` checks transitive theorem dependencies.

Run the production modules and the two focused source checks with the pinned
toolchain. Each Lean invocation holds the shared build lock:

```sh
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
export LEAN_NUM_THREADS=1
flock /tmp/edsl-lean-build.lock lake build \
  EDSL.X86.Sequential.ParityISA EDSL.X86.Sequential.CFGDiscovery \
  EDSL.X86.Sequential.Return EDSL.X86.Sequential.Literals \
  EDSL.X86.CallReturn.DecodeTransport EDSL.Sum32.Artifact EDSL.X86.VCGen.Core
flock /tmp/edsl-lean-build.lock lake env lean -j1 \
  -DwarningAsError=true tests/SequentialParityISA.lean
flock /tmp/edsl-lean-build.lock lake env lean -j1 \
  -DwarningAsError=true tests/ParityISAAudit.lean
```

These commands compile current source against Lake's imported objects. A fresh
project-source check additionally compiles the complete scoped project import
closure in dependency order into an empty object directory, using only that
directory in `LEAN_PATH` and the pinned toolchain's system libraries. Obtain the
system prefix with `flock /tmp/edsl-lean-build.lock lean -j1 --print-prefix`.
Source compilation and `leanchecker --fresh` replay of stored objects are
distinct checks.

The shared ISA checks establish no parity body certificate or new corpus
coverage. They do not execute the corpus binaries or establish an end-to-end
parity proof, resource/task contracts, physical CPU/OS refinement, concurrency,
whole-binary safety or performance credit.

The architectural references are the existing backend's Intel SDM revision 093
[AND and CMP, volume 2A](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf),
[XOR, volume 2D](https://cdrdv2-public.intel.com/929356/334569-093-sdm-vol-2d.pdf),
and [NOP and REX definitions, combined volumes](https://cdrdv2.intel.com/v1/dl/getContent/671200).
The same `targetProfile` applies: 64-bit mode, CET/IBT/shadow stacks disabled,
and multi-byte NOP support. These are environmental assumptions.
