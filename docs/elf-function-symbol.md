# Checked ELF function symbols

`EDSL.ELF.FunctionSymbol` binds a requested byte name and its complete declared
symbol extent to a window of a literal ELF64 file. It reuses
`FunctionWindow` for program headers, executable LOAD mappings, exact code
bytes, admission and current-memory transport. A host `readelf`, `nm`, parser or
manifest may propose witnesses; its output has no authority in these theorems.

The checker verifies all 64 bytes of every declared section header. Each
SHT_SYMTAB and SHT_DYNSYM row has exactly 24 bytes and is checked against the
literal file, with its declared count, linked SHT_STRTAB and complete string
bytes. The section-name table is checked as well. Every referenced name offset
must be in bounds and reach a terminating NUL. ELF suffix references are
supported; a name is compared as exact bytes without host-string conversion.
The tables include the null symbol and the local/nonlocal partition described
by `sh_info`.

The requested nonempty name must occur exactly once across both symbol tables.
A duplicate rejects the selection even when the other occurrence is local,
undefined or in the dynamic table. The selected symbol must be a defined
global `STT_FUNC`, and its entire positive declared size must equal the selected
code length. Its defining section must be executable, allocated SHT_PROGBITS.
The symbol extent must fit the section, whose file/address mapping must agree
with the selected executable LOAD's mapping over that same extent. A matching
prefix or an unrelated copy of the bytes does not satisfy this contract.

`checked_sound` exposes the exact metadata, symbol contract and underlying
`FunctionWindow` selection. `checked_symbol` supplies the actual symbol row,
complete linked strings and terminating exact name. `checked_mapping` records the declared size and
agreement of the section and LOAD mappings. `admitted_sound` also supplies
executable `CodeAt` and preservation of every prior cell, subject to the
existing fresh-page admission check. `admitted_current_code` requires explicit
`FunctionWindow.TextUnchanged` for readable code bytes and execute permissions
at the current program state. These are the code premises a separate ISA
checker or program theorem can consume.

The profile supports ELF64 little-endian x86-64 ET_EXEC within
`FunctionWindow`'s existing file and LOAD limits. It requires one static symbol
table, permits at most one dynamic symbol table, and checks both completely.
Repeated tables, extended section indexes/counts, compressed symbol/string
tables, missing or unterminated names, unsupported visibility bits, and any
ambiguous requested name reject. String tables use ordinary flags zero or
SHF_ALLOC; selected text uses SHF_ALLOC | SHF_EXECINSTR exactly. Declared code
windows are currently at most 64 bytes. These restrictions are acceptance
limits, not evidence of a defect in rejected files.

This is a bounded byte-binding profile rather than general ELF well-formedness.
Section alignment fields are recorded exactly but are not separately validated;
unrelated section payloads remain opaque.

A symbol name, binding or declared size does not establish program behavior,
an actual source-language function boundary, ABI correctness, absence of
relocations, dynamic-linker behavior, native startup or an OS/hardware
refinement. Installed abstract memory is the existing loader model. Runtime
patches, interpreters, relocations, ownership and concurrent text modification
still require their own explicit environment reasoning. Names can be false or
misleading; semantic contracts must be proved separately over the exact code.

The tests use an independently encoded synthetic ELF and mutations of file
metadata and matching witnesses to exercise ambiguity, string bounds, declared
extents and mapping agreement. Native inspection of a real file is separate
metadata evidence and does not count as a kernel-checked certificate.
