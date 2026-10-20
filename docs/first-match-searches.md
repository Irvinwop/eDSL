# First-match byte and u32 searches

The frozen `c_memchr_index` and `c_linear_search_u32` functions share one
width-parametric proof for each compiler layout. The fixed tasks require the
first equal element, or full64 `SIZE_MAX` if no element matches. The byte task
compares eight bits; the u32 task compares all 32 bits in little-endian memory.
The [measurement](../corpus/measurements/first-match-searches-v1/README.md)
records the passed full-project gate and fresh replay, with conditional coverage
of **8/40 functions and 16/80 artifacts** and one distinct concurrent function.

| Compiler | Function | Entry | Complete extent |
| --- | --- | --- | ---: |
| GCC 13.3.0 | `c_memchr_index` | `0x403000` | 40 bytes |
| GCC 13.3.0 | `c_linear_search_u32` | `0x4030e0` | 40 bytes |
| Clang 18.1.3 | `c_memchr_index` | `0x401550` | 34 bytes |
| Clang 18.1.3 | `c_linear_search_u32` | `0x4017f0` | 34 bytes |

All bytes, padding and return sites belong to the unchanged final linked ELFs.
GCC retains ENDBR64 under the explicit CET-off assumption. Source, compiler
options and historical measurements remain frozen.

## Independent contract

[`FirstMatch`](../EDSL/Grading/FirstMatch.lean) defines the earliest matching
index or list length independently of instructions. Prefix lemmas supply
existence, uniqueness and the absence of earlier matches.
[`IndexSearch`](../EDSL/Grading/IndexSearch.lean) encodes an absent match as
`SIZE_MAX` and fixes the byte and u32 specifications. The task registry chooses
the specification; candidates cannot substitute their own postcondition.

RDI contains the full64 base and RSI the full64 element count `n < 2^64`.
Only RDX's low8 or low32 key bits are relevant; arbitrary upper bits are allowed.
Positive inputs require their complete nonwrapping readable snapshot: `n` bytes
or `4*n` bytes. Word alignment and disjointness from compatible read-only
snapshots, code or the original caller slot are not required. Empty inputs
return `SIZE_MAX`, with no DATA reads, input loan or data-pointer validity.
Executable code and the original STACK8 return slot remain required.

[`Elements`](../EDSL/BufferCall/Elements.lean) connects each complete
little-endian word to the shared byte-snapshot admission. Every DATA1/DATA4 read
must fit wholly inside the admitted snapshot with current authority. Readable
neighboring bytes or the old three-byte loan cannot authorize a word read.

## Reused checking and resources

[`Sequential.Search`](../EDSL/X86/Sequential/Search.lean) exposes the production
rules for unprefixed memory/register CMP8 (`38 /r`), CMP32 (`39 /r`), and
register-only REX.W C7 `/0` sign-extended immediate moves. The supported
comparison addressing forms use the existing full64 base/index/SIB subset.
CMP8 permits AL/CL/DL/BL sources; AH/CH/DH/BH are rejected. Unsupported prefixes,
displacements and memory-C7 forms fail explicitly. C7 changes no flags and
performs no operand read. All instruction bytes still require executable fetch.

[`VCGen.IndexSearch`](../EDSL/X86/VCGen/IndexSearch.lean) shares actual snapshot
reads, key truncation, SIB scaling, frame preservation and rank arithmetic across
both widths. [`IndexSearchBodies`](../EDSL/Corpus/V1/IndexSearchBodies.lean)
discharges one sparse-cutpoint proof per compiler layout through the existing
production decoder, executor and sound VCG. The complete CFGs authenticate every
byte. Entry rank is `n+1`; loop rank is `n-i`. The annotations do not restrict
admission through future execution or checker success.

The universal result covers arbitrary admitted snapshots, initial states,
relocations and AF streams. It retains complete RAM and permissions, original
return RIP, RSP+8, SysV callee-saved registers and nonarithmetic flags. The shared
BufferCall bridge retains current code, caller and input authority at every
continuing prefix and return. This remains a sequential callable contract.

[`FrozenFunction`](../EDSL/Corpus/V1/FrozenFunction.lean) shares bounded static
symbol selection. Its computed mapping hints are untrusted: the original
complete-file checker authenticates each requested name, entire unique extent
and executable layout in
[`IndexSearchWindows`](../EDSL/Corpus/V1/IndexSearchWindows.lean).
[`ReadOnlyResources`](../EDSL/Corpus/ReadOnlyResources.lean) shares checked
adoption/borrowing with an actual manager history. The
[loaded witnesses](../EDSL/Corpus/V1/IndexSearchResources.lean) reuse only the
previous scan initialization, retain every installed cell/permission and old
loan, and issue a new exact eight-byte loan for the u32 input. They provide
useful actual calls separately from universal body correctness.
[`IndexSearchCertificates`](../EDSL/Corpus/V1/IndexSearchCertificates.lean)
composes both kinds of evidence through the existing fixed-task certificate API.

## Validation and limits

Regressions exercise first versus later duplicates, no match, final elements,
full-width sentinel, dirty key upper bits, u32 values equal only in low8/low16,
unaligned/high addresses, inaccessible neighbors, compatible aliases and empty
unmapped/noncanonical pointers. Resource regressions check altered arguments,
wrong symbols/entries, short or revoked loans, exact spans and installed data
outside the function.

The native probe compares 132,152 CPU observations with the public machine:
131,072 CMP8 pairs across both frozen encodings, 1,024 CMP32 corner cases and 56
RAX/R8 C7 cases. It checks flags, register/RIP frames and exact DATA footprints;
guard-boundary and malformed-capture controls fail closed. These are finite
conformance observations, not a physical CPU refinement theorem.

`dynamic_bound` gives conservative model-instruction bounds of `7*(n+2)` for
GCC and `6*(n+2)` for Clang. These are output upper bounds, not admission caps,
minimum operation counts, CPU cycles or performance claims. Static profile
limits remain 64 bytes / 32 instructions.

Stable ordinary RAM, no asynchronous interference, modeled ownership,
four-level canonical addressing, long mode and disabled CET remain assumptions.
Physical x86 refinement, native Linux/loader authority, source/IR preservation,
synchronization and minimum hardware cost remain separate work.
