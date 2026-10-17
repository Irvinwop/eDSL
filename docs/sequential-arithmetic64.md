# LEA64 and register ADD64

The separate Lean `X86.Sequential` backend accepts one REX.W prefix
`48`–`4f` followed by LEA `8d /r` or register ADD `01 /r` / `03 /r`.
LEA accepts the existing mod=00 full64 base/SIB address subset: real base and
index, scales 1/2/4/8, with R/B/X selecting the destination/base/index banks.
Encoded base5, missing index, displacements and RIP-relative forms reject.
With X=1, SIB index4 denotes R12. Plain-base forms ignore X. LEA occupies
three bytes for a plain base and four bytes for SIB. It computes the effective
address from the pre-state without accessing operand memory, checks no
canonicality condition on the computed value and preserves every flag.

Register ADD requires mod=11 and occupies three bytes. Opcode `01` writes
r/m from r/m+reg; `03` writes reg from reg+r/m. R/B extend those fields and
X is ignored. Both operands come from the pre-state, including self-add and
RSP aliases. The modular full64 result sets CF/PF/AF/ZF/SF/OF according to
`addFlags64`, preserving every other bit. The existing arithmetic theorems
relate carry to the natural sum and overflow to the signed mathematical sum.
Memory ADD, W=0, LOCK and extra/repeated prefixes remain unsupported.

`execute_lea64_context` and `execute_addReg64_context` retain complete memory
and every nondestination register. Both have empty operand reads, no store
intent, no locked event and no undefined-AF choice. Current OS resources
transport in the same world through the actual decoded steps. A changed RSP
retains the original caller-slot loan and bytes; it supplies no authority or
return-slot binding at the new address. The resource regressions include an
admitted world where LEA computes a noncanonical RSP and a subsequent RET
faults while the original caller bytes and reusable store authority survive.

These additions do not expand the legacy sequential/TSO instruction profile
or the sum32 shape checker. Separate [direct-add compiler clients](counted-store-direct64.md)
prove complete outputs against the existing independent full64 result and
current-resource contract; native compiler observations remain distinct evidence.
The architectural references are Intel's
[ADD entry, volume 2A, pages 3-14–3-15](https://cdrdv2-public.intel.com/868140/253666-089-sdm-vol-2a.pdf#page=132)
and [LEA entry, pages 3-539–3-540](https://cdrdv2-public.intel.com/868140/253666-089-sdm-vol-2a.pdf#page=657).

## Independent native conformance

`scripts/verify-sequential-arithmetic64.sh` supplies finite native/model
conformance evidence for the sequential LEA64 and register ADD64 extension.
It builds owned single-instruction windows into a dedicated linked ELF section,
extracts that exact final section and requires byte-for-byte identity with the
executed section before running any probe. An altered extraction must reject
before execution and produce no Lean observation file.

The C observer specifies requested operations without an opcode, REX, ModRM or
SIB decoder. It independently checks all 16 registers and complete captured
RFLAGS. LEA expectations use unsigned modular `base + index * scale`, preserving
all flags. ADD expectations use a 65-bit unsigned sum for carry, sign comparison
for overflow, nibble addition for auxiliary carry and low-byte population count
for parity, with exact zero/sign flags and all other flags preserved.

The 60 LEA windows produce 240 observations over four value profiles. They cover
all 16 destinations, all 12 admitted plain bases, all scales and REX.R/X/B
combinations, ignored X without SIB, extended registers, RSP/R12 bases, RBP/R12
indices and destination/base/index aliases. Inputs include values above 4GiB,
noncanonical values and modular wrapping. LEA does not dereference these values.

The 56 ADD windows produce 672 observations over 12 arithmetic vectors. Both
`01 /r` and `03 /r` directions exercise every register as source/destination,
with all 16 self-adds, RSP on either side, all register banks and ignored-X
combinations. Vectors cover zero, full64 carry, signed overflow, nibble carry,
parity, nonzero high halves and wraparound. This samples selected combinations
rather than every register pair or every input value.

The assembly capture supports arbitrary modeled RSP. It performs no stack
access between installing that value and capturing every register through
RIP-relative stores, then restores its saved host stack before recording flags.
Requests alternate `0x202` and `0xed7`; expectations use the effective user-mode
flags captured before each instruction. This covers those profiles, including
DF preservation, rather than arbitrary privileged flag settings.

All 912 successful CPU snapshots become Lean theorems invoking the actual
`Sequential.step` on literal bytes and captured pre/post states for both AF
choices. Lean's kernel checks their reductions, followed by the project's
transitive theorem-dependency audit. The replay state makes only the exact
instruction bytes accessible, with no data mapping. No LEA address computation
can obtain a value from memory in that model. RIP expectations use extracted
continuation labels; empty operand-read lists are independently requested
semantics, not observations of hardware memory-access traces.

Nine safe owned register-only negative windows test wrong address scale/base,
narrow LEA, LEA flag damage, wrong ADD source, narrow ADD, omitted flag updates,
cleared carry and wrong direction. Each must fail the independent C contract;
their observations are excluded from positive replay. They make no data or
stack accesses through arbitrary register values.

```sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-arithmetic64.sh
```

Evidence and hashes are written under `artifacts/sequential-arithmetic64/`.
The harness is single-threaded, non-PIE, Linux x86-64, with alignment checking
and CET disabled. These finite checks do not establish universal instruction,
CPU or OS correctness, physical fault delivery, timing, speculation, concurrent
visibility, atomicity or whole-kernel safety. They provide no source-language
preservation or performance minimum.
