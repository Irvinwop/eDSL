# Exact frozen clamp function windows

`Corpus.V1.ClampWindows` reuses the complete literal GCC/Clang files, program
headers, section/symbol/string metadata and accepted LOAD layout. Its untrusted
selection hints become evidence through the same production named-function
checker used by the other scalar certificates. No file or metadata array is
copied and no compiler option or frozen input changes.

| Compiler | Symbol | Address | File offset | Extent |
| --- | --- | ---: | ---: | ---: |
| GCC | `c_clamp_i32` | 4205872 | 11568 | 17 |
| Clang | `c_clamp_i32` | 4199120 | 4816 | 13 |

The GCC symbol is table27 row128, name offset1958, section14. Clang is table26
row105, name offset1725, section13. Both have global FUNC identity, ordinary
visibility and exact whole declared extents. The checker reads the entire file
and metadata, validates the unique requested name, and binds the selected bytes
to executable mapped addresses. Copying a correct body into a different file or
at another location does not produce this certificate.

Data checking alone supplies no functional or OS guarantee.
`Corpus.V1.Clamps.certificate compiler` additionally composes the fixed signed
low32 specification, production generated-WP semantics and shared scalar
constructor. It reuses the existing caller, fresh-file facts and separation
proofs to construct a useful current call at each selected address. It declares
a new modeled ownership world and does not authenticate native authority.
The universal claim admits equal endpoints and arbitrary upper argument halves;
the chosen interior witness narrows no other admitted call.

`tests/CorpusClamp32.lean` applies actual decoded execution in these installed
ELF mappings to independently supplied signed-boundary and equal-endpoint
results, retaining the full mathematical/ABI/RAM contract. The maintained gate
requires the complete typed instances and both complete files before emitting
its report. Both clamp-byte mutations reject, and opaque header/.comment
mutations preserve every certified GCC body while still rejecting whole-file
identity. Proof failure, timeout and unsupported code establish no defect.

The target remains the documented sequential, stable-RAM, CET-disabled profile.
No source/IR preservation, native Linux startup, physical hardware refinement,
concurrent contract, cost minimum or timing guarantee follows from this slice.
