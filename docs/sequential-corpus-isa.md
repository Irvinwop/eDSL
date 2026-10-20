# Sequential comparison and padding subset

The sequential target supports low32 register CMP/TEST, restricted CMP8
memory/immediate and CMP8/CMP32 memory/register forms, sign-extended register
immediate moves, and exact padding encodings. These extend the shared
decoder, executor and read-only CFG checker. ISA support alone does not
establish a whole-function certificate or source preservation. The
[bounded byte-scan proofs](bounded-byte-scans.md) compose the added byte form
and NOP9 with independent function and current-resource contracts.

`cmp32 left right prefixed` subtracts low32 right from low32 left, discards
the result and sets CF/PF/AF/ZF/SF/OF at width32. `test32` computes the low32
AND, discards it, clears CF/OF, sets PF/ZF/SF, and permits both independent AF
choices. Both preserve every GPR, all other flag bits and complete memory.
Neither records an operand read. `prefixed` records three-byte versus two-byte
encoding length; manually constructing an instruction does not authenticate
its encoding. Actual execution decodes the current executable bytes.

Supported comparisons are `39 /r`, `3B /r` and `85 /r`, with ModRM.mod=3.
They accept no prefix or exactly one REX40..47. R/B extend their respective
register fields; X is ignored in register mode. CMP's two opcode directions
retain their correct subtraction order. REX.W families retain their previous
subset and semantics. The original register-comparison batch added no byte,
word, immediate or memory comparison forms; the later CMP8 subset is below.
The existing legacy CMP-EAX-zero case remains supported.
Repeated prefixes and other prefix combinations remain unsupported.

`cmpMemImm8` supports only unprefixed `80 /7 ib` with the existing mod=00
base/SIB addresses. A SIB requires a real base and index. Register operands,
displacements, RIP-relative/absent bases, missing indices, REX prefixes and other
byte comparison forms outside the supported constructors remain unsupported.
It reads exactly one DATA byte,
subtracts the immediate at width 8, and sets CF/PF/AF/ZF/SF/OF. GPRs, complete
memory/permissions and nonarithmetic flags are preserved. Fetches and the operand
read use the actual current machine and report their precise failures.

`endbr64IbtDisabled` recognizes only `f3 0f 1e fa` and advances RIP by four.
The named target profile assumes 64-bit mode, CET indirect-branch tracking
and shadow stacks disabled, and multi-byte NOP support. These are external
conditions for hardware correspondence; the model neither reads control MSRs
nor proves these conditions from the instruction bytes. It models no CET
tracker, suppression state or shadow-stack behavior. ENDBR32, alternate hint
encodings, extra prefixes and incomplete encodings are rejected.

`nop` supports the following complete encodings:

| Constructor | Bytes | Length |
| --- | --- | --- |
| `.one` | `90` | 1 |
| `.two` | `66 90` | 2 |
| `.three` | `0f 1f 00` | 3 |
| `.four` | `0f 1f 40 00` | 4 |
| `.five` | `0f 1f 44 00 00` | 5 |
| `.nine` | `66 0f 1f 84 00 00 00 00 00` | 9 |

All preserve flags, GPRs and memory. Apparent NOP address operands are never
evaluated and cause no operand memory operation. Every instruction byte must
still be readable and executable, including SIB and displacement bytes. Other
NOP operands, displacements and aliases, lengths 6–8 and padding longer than
nine bytes remain unsupported. Instruction-length and successful-fetch
transport now cover the supported maximum of nine bytes. The
64-byte/32-instruction CFG bounds remain unchanged.

The legacy decoder and executor are unchanged and retain successful embedding
theorems. Rejections of malformed encodings beginning with newly recognized
prefixes can now report `unsupportedEncoding` or a precise instruction-fetch
failure rather than `unsupportedOpcode`. A rejection establishes unsupported
input, not a defect in the program.

The architecture reference is [Intel SDM, combined volumes](https://cdrdv2.intel.com/v1/dl/getContent/671200),
order 325462-093US (September 2026): volume 2A CMP pages 3-161–162 and ENDBR64
page 3-288; volume 2B NOP page 4-160 and TEST pages 4-721–722; volume 2A section
2.2.1 describes REX fields. These instruction descriptions determine the
width, operand direction, flag contract and exact NOP subset above.

`tests/SequentialCompare32.lean` checks independent order/overflow/parity
vectors, operand banks, framing, truncation, rejection and CFG closure.
`tests/SequentialPadding.lean` checks exact lengths, instruction fetch permissions,
unsupported aliases and CFG composition. `scripts/verify-sequential-compare32.sh`
binds an independent native C/assembly oracle and actual-step Lean replay to
the executed final ELF section. Finite native agreement supports conformance
of the tested observations; it is not a universal CPU, OS or concurrency proof.
The native fixture assumes no asynchronous/debug interference, and its
requested operand-read footprint is not a physical memory-access trace.
The frozen v1 corpus definition and its normal compiler flags are unchanged.

`tests/SequentialByteComparison.lean` covers byte-width arithmetic and flags,
addressing, exact DATA1 reads, boundary faults, full-fetch transport and NOP9.
The owned native fixture and `tests/SequentialByteNative.lean` compare actual
CPU flags against the production step for all 65,536 byte/immediate pairs,
with a guard-page DATA1 boundary and a NOP9 probe whose apparent operand address
is noncanonical. These finite observations support the implemented subset;
they supply no proof oracle, physical-memory trace or universal hardware theorem.

The [first-match search extension](first-match-searches.md) adds unprefixed
`cmpMemReg8` (`38 /r`) and `cmpMemReg32` (`39 /r`) with the same restricted
mod=00 base/index/SIB addresses. The memory operand is the left subtraction
operand. CMP8 uses only AL/CL/DL/BL; AH/CH/DH/BH, REX forms, displacements and
other unsupported encodings reject explicitly. CMP32 uses low32 of the eight
low-bank GPRs. Actual DATA1/DATA4 reads, subtraction flags, complete memory,
GPR and nonarithmetic-flag frames use the production executor. SIB scale 2
means multiplication by four with full64 base and index.

`movSignImm32` supports only REX.W `48/49 C7 /0`, ModRM.mod=3: it sign-extends
the immediate from 32 to 64 bits, writes the selected GPR and preserves all
flags. It performs no operand read. Memory forms, other REX prefixes and `/1`
through `/7` reject. `Sequential.Search` proves public-step and same-constructor
encoding rules; manually constructing an instruction still grants no decoder
acceptance.

`SequentialSearchISA` covers actual decoding, operand direction, widths,
full64 sign extension, frames, instruction fetch and precise read faults.
`check-sequential-search-native.sh` checks the public model against 132,152
finite native observations and schema/guard controls. The corpus, static CFG
limits and environmental assumptions remain unchanged.
