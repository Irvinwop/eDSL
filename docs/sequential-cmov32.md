# Low32 conditional register moves

`X86.Sequential` models register-only CMOV32: unprefixed `0f 40..4f /r`, or
exactly one non-W REX byte `40..47` followed by that encoding. ModRM must
have mod=11. The respective instruction lengths are three and four bytes.
R extends the destination, B extends the source, and X is ignored. All sixteen
conditions and all sixteen GPRs, including RSP and self-aliases, are admitted.
Every required instruction byte is fetched from executable current memory.

Both outcomes select a pre-instruction low32 value and zero-extend it to the
full64 destination. A false condition **still clears bits 63:32**, including
for self-aliases or RSP. Every other GPR, every flag, and complete memory and
permission maps remain unchanged. There is no operand read or store intent,
and the undefined-AF argument has no effect. The corresponding CMOV64 false
case continues to preserve the entire old destination.

This follows Intel's [CMOVcc operation, volume 2A, printed page 3-159](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=277):
the false branch clears the high destination half for operand size 32 in
IA-32e mode. The target assumes 64-bit mode, processor support for CMOV,
CET indirect-branch tracking and shadow stacks disabled, ordinary RAM, and
no asynchronous interference during the modeled sequential execution.

Memory CMOV, operand16, address override, repeated/extra prefixes and other
opcode families fail closed. A memory CMOV needs an unconditional source-read
contract even when the condition is false; this register extension does not
supply that contract. The original legacy sequential/TSO decoder is unchanged.
The reused decoder transport, CFG checker, execution/accounting theorems and
generic VCG cover the new constructor. The Sum32 shape checker keeps its
specialized loop shape; its artifact writer can print the constructor.

`OS.CallResources.current_cmovReg32_step` derives actual success from byte
decoding and current memory coupling, preserving the same complete borrowing
world, owner/epoch metadata, cells, permissions and loans. Replacing RSP
preserves the original caller-slot resource and its bytes; it grants no read
permission at a truncated or selected replacement pointer. A later RET still
requires current RSP to equal the original caller slot.

`tests/SequentialCmov32.lean` contains independent high-half, register-bank,
condition-order, signed-overflow, fetch, prefix and CFG mutation regressions.
It also composes CMOV32 with RET through the shared VCG. Resource regressions
exercise an untaken RSP truncation and both RAX outcomes followed by authorized
RET. The native fixture and verifier check selected real CPU observations
against independent operand/condition contracts and emit complete observation
rows. The native script itself performs no Lean replay or theorem audit.
Finite hardware observations do not establish universal CPU correspondence,
concurrency, memory fault delivery, timing, a global operation minimum or any
whole-OS claim. This instruction extension adds no corpus certificate by itself.
