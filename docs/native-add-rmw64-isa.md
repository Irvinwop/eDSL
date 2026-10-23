# Qword arithmetic read-modify-write

This CPU family provides checked decoding, execution, memory and flag contracts,
with explicit compatibility for the existing XADD model. OS and scheduler
dispatch retain their separate interfaces and resource contracts.

`EDSL.X86.AddRMW64` represents one additive qword RMW family:

| Tag | Exact bytes | Length | Captured delta | GPR result | Flags |
| --- | --- | --- | --- | --- | --- |
| `xadd old` | unchanged `old.bytes` | 5 | prestate `old.source` | source receives full old qword | `addFlags64` |
| `addImm8 e` | `f0 rex 83 modrm imm8` | 5 | imm8 sign extended to 64 | all GPRs preserved | `addFlags64` |
| `inc e` | `f0 rex ff modrm` | 4 | 1 | all GPRs preserved | `incFlags64`, incoming CF preserved |

New records retain raw REX/ModRM/imm8. They admit only REX 48/49 and group
/0, using the existing `LockedAdd64.indirect64`: mod00, real base, no SIB,
RIP-relative operand or displacement. Thus RSP/R12 and RBP/R13 bases are
excluded. Other encodings fail closed. The narrower new REX profile is a
support restriction, not an assertion that all other architectural encodings
are invalid. XADD retains all old REX48..4f, source registers, ignored X bits,
base/source aliases and source RSP unchanged.

The third current executable byte selects ADD or INC. The selected decoder
then authenticates its whole window and no-wrap bound. ADD reuses the existing
five-byte fetch; INC fetches four bytes with no fifth-byte query. Every other
probe, including probe failure, delegates to the unchanged eager legacy
decoder. A failed probe itself supplies no authority or replacement error.
Recognition follows the selected complete fetch, so an inaccessible selected
tail takes precedence over an unsupported encoding. Errors return only `Error`.
No global equality with the old decoder is asserted after admitting new opcodes.

`execute` applies `dataOnly64` and exactly one `fetchAddQWord`. Address, delta,
writeback and flags all use the prestate. The complete before/after/delta event
and singleton `rmw8` access remain the legacy types, including when no GPR
receives the old word. `Effect` exports primitive, framing, full permissions,
code preservation and full64 flag contracts. CF's common equation is tagged;
`add_carry` requires a non-INC tag. XADD compatibility is explicit through
`execute_xadd`, `decodeAt_xadd_iff`, `step_xadd`, `effect_xadd_iff` and
`Effect.xadd`, which recovers all legacy effect methods and flag/source laws.

## ISA references

The encoding, flag and addressing rules follow the Intel
[SDM Vol. 2A, 253666-093US, September 2026](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf):
ADD pp. 3-14–15, INC pp. 3-457–458, LOCK pp. 3-565–566, and
REX/addressing §2.2.1 pp. 2-7–12.

ADD specifies REX.W 83 /0 ib, sign extension to destination width, and all six
arithmetic status flags. INC specifies REX.W FF /0, addition of one, defined
OF/SF/ZF/AF/PF and unchanged CF. LOCK permits these memory-destination forms.
REX.W selects qword width, B extends the base, X extends only a SIB index,
and R is ignored for opcode-extension groups. R12 requires SIB; mod00 r/m101
remains RIP-relative even with B=1. The model intentionally supports fewer
forms. These references inform the source model, not a proved hardware theorem.

## Environmental and integration limits

The single indivisible transition is the existing abstract RAM primitive.
Its interpretation requires coherent WB RAM, stable translation and permissions,
contiguous injective physical backing with compatible line/page layout, and
exclusion of unmanaged aliases, mixed-width, MMIO, DMA and non-temporal
interference. The virtual checks alone do not prove physical LOCK refinement.
The existing long-mode/canonical-address and CET-disabled target limits remain.

The CPU layer does not supply OS ownership, live reservations, code/caller loans,
disjoint stacks, resource lifetime through joins, other-writer exclusion, or
fairness/progress. OS/scheduler integration requires those contracts. This family supplies neither a counter-body evaluator nor a whole-loop
event-count certificate, source-language memory-order refinement, or a releasing
join. Native agreement is a separate validation obligation.

`tests/AddRMW64.lean` checks literal arithmetic and flag observations through
production decoding and execution, including negative immediates, wrap,
overflow, parity and nibble boundaries, both incoming CF values, all GPRs,
XADD aliases and RSP, four-byte fetch boundaries, and denial cases.
Run `lake build AddRMW64Tests`; the full certificate gate also includes these
regressions in its fresh kernel replay and dependency audit.
