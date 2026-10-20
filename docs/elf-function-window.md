# Literal ELF function-window bridge

`EDSL.ELF.FunctionWindow` checks an explicit address and byte span against a
complete literal ELF64LE x86-64 ET_EXEC file. It reuses `Segment`, `Image`,
`valid`, `install`, `fresh`, `checkCode` and their existing proofs. It does not
change `EDSL.ELF.parse` or `EDSL.ELF.load`.

The interface authenticates an **address/span**, not a symbol or complete
function. Symbol identity, section contents and function-boundary checking are
pending. A UI must describe a selection by its numeric address, file offset
and length; a name obtained from `readelf`, a manifest or `corpus/Extract.lean`
is an unverified label. The checker cannot establish that an interval contains
a whole function or has no incoming branches.

## Inputs and checks

`check file table window bytes : Bool` takes the full `List X86.Byte`, an
untrusted `Table` witness, a `Window` containing natural address/file offset,
and the selected literal bytes. A witness is convenient data for a certificate
producer, with no proof authority. The checker reads the literal file again:

- Every ELF header byte is matched by bounded little-endian field reads.
  The PHDR count must equal the witness list length. Every field of every
  declared program-header row, including its physical-address field, is matched
  at its declared position. Omitting a competing LOAD cannot pass this check.
- All PT_LOADs become the `Image` in original table order. The existing image
  validator requires valid segments, an executable file-backed entry, and
  ordered disjoint rounded pages across **all** LOADs. Partial byte overlaps,
  identical mappings, shared pages and unsorted LOADs are rejected.
- A nonempty selected span must fit wholly inside a readable executable
  file-backed LOAD, with its file offset equal to that LOAD's translation.
  The declared source interval must equal the selected bytes. The existing
  executable byte-fetch checker also checks those bytes in `install` at the
  selected address, which need not equal the ELF entry.

The source-file bound remains 65,536 bytes; the program-header bound remains
16; each LOAD's memory-size bound remains 65,536 bytes. A selected span has
1–64 bytes and lies below `2^47`. These inherit the existing profile rather
than increasing its limits. The header requires ELF version 1, 64-bit little
endian, ET_EXEC, EM_X86_64, OSABI 0 or 3, ABI version 0, zero identifier padding
and flags, 64-byte ELF/section headers and 56-byte program headers. Program and
section tables must be bounded and aligned to eight bytes. Section counts are
positive, ordinary, and bounded by the file limit; extended numbering and
sectionless files are unsupported. Section-table contents are opaque.

In addition to LOADs the accepted program types are NULL, DYNAMIC, INTERP,
NOTE, PHDR, GNU_EH_FRAME, GNU_STACK, GNU_RELRO and GNU_PROPERTY. Their declared
file extents, file/memory-size relation, flags and address extents are bounded.
GNU_STACK must request RW with zero file/memory sizes. These rows do not map
cells or execute anything. Their payload syntax, dynamic tags, relocation
targets, interpreter strings, unwind tables, properties and physical-address
semantics are outside the contract. TLS and unknown program types fail closed.

`check` returns false on any failed check. `admit file table window bytes prior`
returns `.error .invalidImage` if checking fails, or `.error .mappingCollision`
if any prior cell occupies any rounded LOAD page, including inaccessible cells
and cells in page padding. It otherwise returns exactly the checked image and
`install file table.image prior`. This is an explicit abstract LOAD admission,
not the legacy parser's process-loading API. Failures establish no defect.

Installation copies exact LOAD file bytes and zero-fills BSS. It does not map
rounded page padding. Rounded pages are nevertheless used to reject competing
segments and prior mappings. This is the existing cell-space abstraction, not
an implementation of Linux page tables or physical page reservation.

## Proof contracts

`Field.Holds` states bounded little-endian decoding independently of the
checker result. `Layout` states header syntax, complete table correspondence,
supported row kinds and the existing validated LOAD layout. `Selection` states
the selected bounds, a covering executable LOAD with its exact translation,
and equality to the literal source slice. Neither predicate is defined as
successful IO extraction or successful `check`.

| API | Kernel-checked conclusion |
| --- | --- |
| `checkLayout_sound` | Successful layout checking implies `Layout`. |
| `selection_sound` | Successful full checking implies `Layout` and `Selection`. |
| `Selection.file_byte` | Every selected byte is the corresponding full-file byte. |
| `Layout.no_competing_pages` | Any two distinct LOAD descriptions occupy disjoint rounded pages. |
| `selected_segment` | A validated covering LOAD and disjoint pages against every distinct competing LOAD. |
| `checked_code` | `CodeAt` at `window.base` in the exact modeled installation over any prior space. This byte-fetch fact alone does not admit resource replacement. |
| `admit_ok` | Successful admission used the checked image, passed freshness and returned exactly its installation. |
| `admitted_sound` | Layout, selection, `CodeAt` in admitted memory, and preservation of every pre-existing caller cell. |
| `admitted_current_code` | `CodeAt` in current memory, under explicit `TextUnchanged` evidence. |

`TextUnchanged installed current window length` requires equality of readable
byte observations and executable permissions at every selected address. It
does not assume the selected bytes as its conclusion. The concrete checked
installation supplies their value. This environmental condition must cover
relocation, runtime patching, unmapping, protection changes and concurrent
modification before the call. Accepting DYNAMIC metadata does not prove that a
dynamic linker leaves executable text unchanged or that executable relocation
is safe. This is a condition at the initial modeled state; exclusion of
interference during a Sequential execution remains a separate synchronization
obligation. No relocation is performed by this model.

The result has exactly the `X86.CodeAt` signature consumed by
`X86.VCGen.run_sound`; `tests/ELFFunctionWindow.lean` type-checks the generic
composition:

```lean
have code : X86.CodeAt initial.memory selected.base bytes :=
  admitted_current_code admitted unchanged
exact X86.VCGen.run_sound graphValid code pc vc choices
```

The decoder-validated CFG, PC, independently stated postcondition, generated
VC and operand-read authority remain separate premises. Successful extraction
does not discharge them. Abstract cell freshness/preservation also does not
establish physical allocation ownership, ABI entry/return invariants, return
stack ownership, OS resources, synchronization, Linux conformance, source/IR
preservation, dynamic startup, TLS, PLT resolution, or CET/hardware support.

## Validation and integration

The leaf tests construct an independent ELF layout and perform an actual
modeled MOV/RET through admission at a non-entry address, checking its result,
return address/stack, instruction count and preservation of an inaccessible
caller cell. Negative fixtures cover truncated headers/tables/text, missing
execute/read permission, an unsupported metadata type, an incorrect offset despite duplicated matching bytes,
changed source/code bytes, BSS extension, mismatched PHDR count, LOAD metadata
mutation, shared-page and partial competing mappings, the source-size bound,
and a hidden prior mapping in page padding. Tests and theorem applications use
kernel reduction; there is no native decision procedure or external solver.

Validation records source hashes, exact commands and exits, and literal
full-file replay sources. Snapshot labels identify the tested inputs; kernel
checking establishes the stated theorem. Revalidate after changing the file,
headers, selected span, or dependencies. Artifact selection alone supplies no
functional proof or corpus certification credit.
