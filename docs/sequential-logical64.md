# Register AND64, OR64 and XOR64

The separate Lean `X86.Sequential` backend models full64 register logical
operations through `LogicalOp.band`, `bor`, `bxor` and
`Instruction.logicalReg64 operation destination source`. One REX.W byte
`48`–`4f` is followed by a register-only mod=11 instruction:

| Operation | r/m destination, reg source | reg destination, r/m source |
| --- | --- | --- |
| AND | `21 /r` | `23 /r` |
| OR | `09 /r` | `0b /r` |
| XOR | `31 /r` | `33 /r` |

Each encoding occupies three bytes. R and B extend the ModRM reg and r/m
fields; X is ignored. Both full64 operands come from the pre-state, including
aliases and RSP. The result replaces only the destination. Complete RAM,
permission maps and every nondestination register survive, with no operand
read, store intent or locked event.

CF and OF clear. PF, ZF and SF describe the result; AF is an independent
unspecified Boolean choice on each instruction. All other flag bits survive.
The existing logical-flag admissibility theorem characterizes both allowed AF
outcomes. A concrete CPU observation supplies its captured AF witness; it
does not require the hardware to realize both undefined outcomes.

Only register forms in this profile are supported. Memory operands, immediate
forms, W=0 and additional/repeated prefixes reject. The older unprefixed
32-bit self-XOR decoder retains its original meaning. Recognized forms with
missing required instruction bytes retain instruction-fetch failures.
The legacy concurrent/TSO backend retains its existing instruction subset.

Current OS resources follow complete RAM equality in the same borrowing
world: code and original caller-slot loans, allocation ownership, epochs and
permissions survive. Replacing RSP grants no new stack authority and does
not bind its new value to the caller slot. Actual RET still reads the slot
at the machine's current RSP and needs the original binding for the resource
bridge. The resource regression exercises this distinction through actual
logical instructions and a subsequent RET.

The architectural references are Intel SDM revision 093:
[AND, volume 2A, printed pages 3-60–3-61](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf),
[OR, volume 2B, printed pages 4-163–4-164](https://cdrdv2-public.intel.com/929354/253667-093-sdm-vol-2b.pdf),
[XOR, volume 2D, printed pages 6-40–6-41](https://cdrdv2-public.intel.com/929356/334569-093-sdm-vol-2d.pdf),
and volume 2A section 2.2.1.2, printed pages 2-8–2-9, for REX fields.

## Independent native checks

`scripts/verify-sequential-logical64.sh` builds owned instruction windows into
a linked ELF section and compares the extracted final section with the actual
executed bytes before probing. An altered extraction must reject before any
probe and emit no Lean observations. The C oracle requests named operations
and operands without decoding opcodes, REX or ModRM. It checks all sixteen
registers and every defined or preserved captured flag; only undefined AF is
excluded from that comparison. Safe owned mutants test incorrect semantics.

The assembly observer supports arbitrary modeled RSP by capturing registers
through RIP-relative stores and restoring the saved host stack before flags
are captured. Incoming flags are the effective user-mode flags captured on
the machine. Successful snapshots become Lean theorems replaying the actual
`Sequential.step` with the captured AF witness, followed by the transitive
axiom audit. Exact instruction bytes are the only readable modeled memory.
RIP comes from extracted continuation labels; the empty operand-read list is
an independently requested model footprint, not a hardware access trace.

```sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-logical64.sh
bash scripts/verify-sequential-logical64-imports.sh
```

Evidence and hashes live under `artifacts/sequential-logical64/`. The separate
cached CI job runs alongside the main proof suite. The harness is
single-threaded, non-PIE Linux x86-64 with CET and alignment checking disabled.
Finite observations do not establish universal CPU or OS correctness,
asynchronous interference, physical timing, speculation, concurrency or
whole-kernel safety. This extension itself supplies no complete source/IR
preservation theorem, general compiler-output certifier or global operation
minimum.

The owned native run covers 216 instruction windows and 2,592 snapshots,
864 per operation. For each operation it samples both opcode directions,
each register as source and destination, every self alias, all R/B banks
and ignored X combinations. Twelve value profiles include zero, high halves,
sign-only results and low-byte parity changes. Fifteen safe negative windows
change the operation, written operand, source, width or carry flag. This is
finite selected coverage, rather than every register pair and input value.

`scripts/verify-sequential-logical64-imports.sh` separately exercises typed
rendering through the public importer for an owned window of 19 bytes in raw
and full-ELF form. It checks all six logical opcodes, exact instruction lengths,
closed CFG edges and literal ELF entry binding. This static certificate leaves
functional correctness, termination and current caller resources as separate
proof obligations. That window is never executed by the import check.

Complete GCC/Clang scalar clients, independent fixed tasks and raw/full-ELF
proof grading build on this instruction foundation; see
[logical compiler clients](logical64.md). Their model proofs and finite native
whole-call observations retain separate scopes.
