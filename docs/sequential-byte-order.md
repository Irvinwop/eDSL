# Byte loads, register comparisons and subtraction

The sequential x86-64 model supports the instruction families needed by the
frozen GCC/Clang `c_memcmp_bytes` windows. The shared decoder, machine, literal
encoder, fetch transport, read-only CFG rules and return inversion use the
same constructors. This ISA support and finite native conformance alone do
not establish either function's correctness.

| Constructor | Accepted form | Operand reads | State change |
| --- | --- | --- | --- |
| `movzxMem8` | `0F B6 /r`, restricted mod=00 base/SIB | DATA1 | Zero-extend the byte to low32 and clear upper32 |
| `movzxReg8` | `0F B6 /r`, mod=3 | None | Zero-extend the source low byte to low32 and clear upper32 |
| `cmpReg8` | `38 /r` or `3A /r`, mod=3 | None | Width8 subtraction flags, with both GPRs retained |
| `subReg32` | `29 /r` or `2B /r`, mod=3 | None | Width32 difference, upper32 clear and subtraction flags |

Each accepts no prefix or one W=0 REX40..47, recording its presence for exact
instruction length. REX.R/B select the appropriate operand bank and REX.X
extends a SIB index. Effective addresses use full64 registers and prestate
values, including destination/address aliases. Register self-aliases likewise
read both operands before the write. The two CMP/SUB opcode directions retain
their proper left-minus-right ordering.

MOVZX preserves every flag. CMP8 and SUB32 set CF/PF/AF/ZF/SF/OF at their
respective widths and preserve other flag bits. All four retain complete RAM,
execute/write permissions, and every GPR outside the specified destination.
Register operations never obtain a DATA read. The memory form reads precisely
one byte, without an alignment requirement or authority for neighboring bytes.
Code still requires every instruction byte to be readable and executable.

Unprefixed AH/CH/DH/BH operands are explicitly unsupported. A REX prefix makes
the corresponding low-byte fields SPL/BPL/SIL/DIL. Unsupported prefix
combinations, REX.W, displacement/RIP-relative/absent address components and
memory SUB fail closed. Unsupported encodings are not evidence of a program
defect. The existing static limits remain 64 code bytes, 32 nodes and nine
instruction-fetch bytes. The CET/IBT-disabled and other callable-profile
assumptions in [the sequential target](sequential-corpus-isa.md) remain explicit.

`Sequential.ByteOrder` provides reusable execution, flags, read-footprint and
framing lemmas. `tests/SequentialByteOrderISA.lean` checks independent flag and
result vectors, operand direction, prefix banks, poisoned upper words,
prestate aliases, exact DATA1 boundary behavior and rejected forms. The earlier
search test no longer rejects the now-supported `CMP AL,DL`; the new tests
check its actual subtraction direction.

Run `bash scripts/check-sequential-byte-order-native.sh` on Linux x86-64 to
compile the owned C/assembly probe and compare its actual CPU observations
with production `Sequential.step` through the pinned Lean interpreter. The
probe supplies 15,648 records: 15,456 supported MOVZX/CMP8/SUB32 observations
and 192 native AH observations that the model must explicitly reject. Real
read-only and guard-page controls exercise a final-byte load, a widened read
and a forbidden write. The validator checks full flags, all GPRs, RIP, exact
read footprints, both AF choices, capture corruption and high-byte exclusions.

The native result and flags come from CPU snapshots, without a copied model
arithmetic formula. This is finite conformance evidence under the probe's
ordinary-RAM and interference assumptions. It supplies no physical read trace,
universal hardware/OS refinement, source-preservation theorem, concurrency
proof, whole-function certificate or minimum physical operation count.
