# Frozen arithmetic windows

`EDSL.Corpus.V1.ArithmeticWindows` selects the complete `c_add_mod64` function
from each ordinary frozen v1 compiler file. `Compiler` aliases the existing
`CompilerComparisons.Compiler`; `file`, `name`, `bytes`, `function` and `input`
are public data, `body` projects the selected bytes, and `checked compiler`
proves `(input compiler).check (file compiler) name = true`.

| Compiler | Symbol table / row | Defining section | Address | File offset | Complete bytes |
| --- | --- | --- | --- | --- | --- |
| GCC | 27 / 131 | 14 (`.text`) | `0x402da0` | `0x2da0` | `f30f1efa488d0437c3` (9 bytes) |
| Clang | 26 / 108 | 13 (`.text`) | `0x401320` | `0x1320` | `488d0437c3` (5 bytes) |

The adapter reuses the existing complete literal `GCC.file` (41016 bytes) and
`Clang.file` (44240 bytes), program tables, metadata and their already proved
`metadataAccepted`/`layoutAccepted` equations. The named checks validate the
unique occurrence across all symbol tables, global FUNC metadata, complete
declared extent, section mapping, executable LOAD coverage, exact file bytes
and bytes fetched from the checked installed image. GCC's ENDBR64 remains in
the selected extent.

GCC now exposes `chunkTail`, `fileDropChunks` and `fileByteChunks`. Their public
types use public names; the equations wrap existing private normalizers in the
same namespace. They preserve every earlier declaration and proof. The new
adapter uses these public equations and Clang's existing `fileDropAt` to avoid
repeating complete-file prefix scans for the selected source interval.

The complete frozen SHA-256 identities are:

* GCC: `3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3`.
* Clang: `d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.

Read-only native extraction supplies provenance: unique symbol/table row,
section-derived offset, complete bytes, manifest agreement and full hashes.
The ELFs are never executed for this work, and native output supplies no Lean
proof field. The complete named checker equations and transitive axiom audit
are kernel proof evidence. The public normalization equations are API lemmas;
no fixture-assignment tests are added. Existing malformed-symbol/ELF rejection
coverage remains applicable.

The existing checker accepts only its bounded ELF64 little-endian x86-64
ET_EXEC profile, complete ordinary section/symbol/string tables and at most
64 selected bytes. It checks layout and modeled installation; unsupported or
ambiguous names, incomplete extents, mismatched bytes and invalid metadata
reject. A failed check supplies no defect finding.

This module establishes exact named-file/window binding. Addition semantics,
costs, registered task integration and useful fresh current-resource admission
remain separate obligations. It establishes no source/IR preservation, native
OS startup, physical processor refinement, current native ownership or corpus
certification increase.
