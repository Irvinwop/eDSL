# ELF container verification

`edsl-certify --elf` accepts a restricted ELF container and proves its supported
entry function's behavior in the Lean machine/OS model. The generated certificate
contains **every observed file byte**, a checked parser result and a checked
executable entry window. It does not depend on section names, symbols or
`objcopy` to establish the entry bytes.

This is function verification after modeled loading, with a caller-provided
return stack and data. It is not a theorem that Linux `execve` can start the
container as a complete process. The owned fixture ELFs use function entries
without a CRT; a Linux process startup contract is separate work.

## Supported profile

- ELF64, little endian, `ET_EXEC`, `EM_X86_64`, version 1, OSABI 0 or 3,
  ABI version 0 and zero identification padding/processor flags.
- A 64-byte ELF header and 56-byte program headers; a nonempty table aligned
  to eight bytes and completely inside the file.
- At most 65,536 file bytes, 16 program headers and 65,536 memory bytes per
  segment. These are explicit current resource limits, not ELF-format limits.
- `PT_LOAD`, ignored `PT_NULL`, and at most one optional `PT_GNU_STACK` with
  RW/nonexecutable flags and zero file/memory size. Other program-header types
  reject explicitly, including interpreters, dynamic linking and TLS.
- Nonempty load segments with `filesz ≤ memsz`, complete file ranges, virtual
  start at least 4096 and virtual end at most `2^47`. Address arithmetic uses
  naturals before conversion to 64-bit words.
- Supported load permissions R, RX, RW and RWX. Write-only/execute-only and
  additional flag bits are unsupported by the current memory interface.
- Pinned 4096-byte pages, matching file/virtual page offsets, and `p_align`
  zero/one or a power of two with matching offset congruence.
- Load segments in ascending virtual order with disjoint **page-rounded** ranges.
  Sharing a page is unsupported even when exact byte intervals do not overlap.
- A nonempty entry window of at most 32 bytes entirely inside one executable,
  file-backed segment. Entry in BSS or a hole is rejected.

The field layouts, file-to-memory copy/BSS relation, flags and alignment rules
come from the primary [ELF header specification](https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.eheader.html)
and [program-header specification](https://refspecs.linuxfoundation.org/elf/gabi4+/ch5.pheader.html).
The caps and rejection policy above define this implementation's supported subset.
Section tables and physical-address fields are not used for this userspace image.

## State and proofs

`ELF.parse` validates the input and returns an `Image`. `parse_valid` proves that
success implies the semantic validation predicate. `checkParsed_sound` checks the
metadata printed by the certificate generator against the entire observed file;
the native generator's own parse result is not trusted on its own.

`ELF.load` takes an existing OS `Space`. It requires all rounded load pages to be
unmapped, including hidden cells, then initializes exact segment intervals with
file bytes followed by BSS zeros and final permissions. `install` is the pure
image constructor; checked-loading claims use `load` or establish its parsing and
freshness conditions explicitly.

Generic checked results include:

- `readNat_bound`: successful field reads are within the observed file.
- `selected_valid`: a selected segment belongs to a validated image and contains
  the queried address.
- `segment_inside_pages`: each segment byte lies in its freshness-checked pages.
- `install_file_byte` and `install_bss`: initialized bytes come from the exact
  file offset or are zero in BSS, with the segment's permissions.
- `install_outside` and `install_preserves_existing`: bytes outside the image
  retain their cells, and a fresh validated load preserves every existing cell.
- `load_ok`: checked success identifies the parser result, freshness evidence
  and initialized space.
- `checkCode_sound` and `checked_entry_code`: successful executable-window checks
  establish the independently stated `X86.CodeAt` predicate. The entry bytes are
  independent of caller cells because an empty caller could not supply a
  successful instruction fetch.

An ELF certificate includes a `certified` theorem proving successful modeled
loading together with termination, exact result/count and absence of divergence
for the selected binary profile. Fresh caller mappings, readable return stack,
canonical return target and applicable data/store-disjointness conditions remain
explicit. Its entry-code binding is derived rather than assumed. The currently
supported increment/load/store profiles still execute in exactly two modeled
instructions; that count excludes loading and process startup.

The file and candidate metadata are rechecked with ordinary kernel reduction
(`decide`), followed by the transitive axiom audit. No native-evaluation/solver
axioms are whitelisted. Proof resource options do not change the logical claim.

## Evidence and reproduction

```sh
lake build EDSL edsl-certify
lake env lean -DwarningAsError=true tests/ELF.lean
lake exe edsl-certify --elf increment FUNCTION.elf artifacts/ELF.lean
bash scripts/verify-compilers.sh
```

The integration script checks raw and full-ELF certificates for Clang C/C++ and
GCC C across all three profiles: eighteen certificates for nine compiler/profile
combinations. It executes the certified function bytes natively and records both
certificate hashes alongside the linked ELF. Mutated ELF code and ELF load/store
contract mismatches must reject. These are owned synthetic fixtures only.

`tests/ELF.lean` independently exercises an ELF with a nonzero segment file/page
offset and BSS. Its loaded function must give modular wraparound, perform RET and
preserve hidden caller data; RX code must remain nonwritable and executable.
Rejection cases cover truncation, byte order, unsupported headers, file overruns,
`filesz > memsz`, noncanonical ranges, invalid alignment, entry in BSS, insufficient
file-backed entry windows, changed code, page sharing and hidden caller collisions
in page padding. The file-backed-window test includes bytes that would otherwise
match executable BSS, so removing that check is observable.

## Remaining boundary

The abstraction installs exact segment bytes and BSS, leaving page padding
unmapped. Linux maps rounded file pages and treats padding/tails differently;
there is no Linux-loader refinement theorem yet. The profile rejects page sharing
rather than modeling Linux's permission-merging or overlap behavior.

Relocations, PIE, dynamic linking, runtime/CRT dependency closure, startup
stack/auxv/TLS, syscalls, threads and asynchronous interference remain ahead.
Physical page backing, aliases, protection keys and concurrent revocation are
also outside the current OS cell model. The ISA/control-state and physical
conformance assumptions in [coverage](coverage.md) continue to apply.

Exit 3 means unsupported or mismatched input, not a defect verdict. Other nonzero
results mean failure to certify. A previously existing certificate path is not
evidence of success for a later invocation.
