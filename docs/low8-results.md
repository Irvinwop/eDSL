# Low-byte results

The shared `EDSL.X86.Sequential` model implements register SETcc and MOVimm8.
Import `EDSL.X86.Sequential.Low8` for the result, resource and VCG proofs.
Namespace, source paths and command names retain their existing spelling.
This foundation adds no corpus acceptance.

`Instruction.setcc condition destination prefixed` replaces bits 0–7 with
exactly zero or one, using `Condition.holds` on the **incoming flags**.
`Instruction.movImm8 destination immediate prefixed` replaces those bits with
the complete literal byte. Both preserve bits 8–63, all flags, every other
GPR, and the entire memory (read, execute and write maps). They produce no
operand reads. `replaceLow8` is pure; `State` is unchanged.

| Family | Accepted bytes | Length |
| --- | --- | --- |
| SETcc | `0F 90..9F C0..C3` | 3 |
| SETcc with REX | `40/41 0F 90..9F C0..C7` | 4 |
| MOVimm8 | `B0..B3 ib` | 2 |
| MOVimm8 with REX | `40/41 B0..B7 ib` | 3 |

All sixteen existing conditions are available. Without REX, codes 0–3 select
AL/CL/DL/BL. Codes 4–7 would select AH/CH/DH/BH and reject. REX40 selects the
low bytes of RAX..RDI, including SPL/BPL/SIL/DIL; REX41 selects R8B..R15B.
SETcc requires mod=3 and reg=0. Other real ModRM.reg aliases and REX42..4F
aliases reject conservatively. Memory SETcc, C6 MOV, other prefixes and
repeated prefixes remain unsupported. These rejections are model limitations,
not statements that all rejected encodings are architecturally invalid.

The production decoder fetches every required byte with execute permission.
Missing/nonexecutable required suffixes return their precise instruction-fetch
fault; unsupported recognized forms return `unsupportedEncoding`. Complete
instructions do not require an extra following byte. Helper decoders assume
the supplied lead bytes were authenticated by their caller; `decodeAt` checks
the full encoding and retains legacy-first embedding.

`replaceLow8_eq_append`, `replaceLow8_widths` and `replaceLow8_bits` characterize
the result independently by slices and bits. `execute_setcc_context` and
`execute_movImm8_context` supply a single complete `Low8Context` and the same
observation for both Bool choices. `current_setcc_step` and
`current_movImm8_step` retain the **same** current OS world and original
caller-resource handles. An RSP destination grants no new stack authority.
Writes to callee-saved registers do not establish ABI preservation; current
RET resources and policy remain separate obligations. Checked graphs, byte
transport, operand-read classification, CallReturn lifting, bounded and
cutpoint VCG use the existing production pipeline.

Architectural references reviewed on 2026-10-20 (specific editions, not a claim
about the newest manual): Intel SDM [Volume 2B, 253667-060US, September 2016](https://www.intel.com.tw/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf),
MOV pp. 4-35–4-37 and SETcc pp. 4-596–4-598; [Volume 2A,
253666-082US, December 2023](https://cdrdv2-public.intel.com/812383/253666-sdm-vol-2a.pdf),
§2.2.1/Table 2-4 for REX and opcode/register fields; [combined SDM,
325462-089US](https://cdrdv2-public.intel.com/868137/325462-089-sdm-vol-1-2abcd-3abcd-4.pdf),
SETcc p. 4-614 explicitly describes the ignored ModRM.reg field; and
[Volume 1, 253665-060US, September 2016](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-1-manual.pdf),
§3.4.1.1 for unchanged upper bits of byte writes. The target inherits
the repository's 64-bit, ordinary RAM and CET-disabled assumptions.

`tests/SequentialLow8.lean` exercises actual decode/step/run/CFG/VCG against
literal expectations, plus symbolic current-resource transport. The audit is
`tests/Low8Audit.lean`, which checks imported theorem dependencies.
These checks cover the modeled instruction subset and its shared proof adapters.
They establish no physical CPU refinement, native conformance, final-file
certificate, grading, compiler or physical OS refinement, or minimum-cost result.
