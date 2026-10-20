# Signed clamp extension of corpus v1

This measurement extends the historical scalar-addition checkpoint from
3/40 functions and 6/80 compiler artifacts to **4/40 functions and 8/80 artifacts**
under the recorded model assumptions. Both default compiler outputs must pass
for a function to count. The accepted symbols are `c_min_u64`, `c_max_u64`,
`c_add_mod64` and `c_clamp_i32`; zero frozen concurrent entries are certified.
The immutable initial, comparison and addition measurements remain historical.

The [shared scalar constructor](../../../docs/corpus-scalar-certificates.md)
composes the registered independent mathematical task, production VCG semantics,
complete literal ELF/name checks and useful current resources at each actual
selected address. Clamp observes signed low32 RDI/RSI/RDX, admits exactly ordered
endpoints including equality, and leaves input register upper halves arbitrary.
Its result lies in the interval and equals the input or nearest endpoint.
Separate machine observations prove zero upper RAX and the complete callable
ABI/RAM contract; the independent interval relation does not mention the ISA.

| Compiler | Symbol | Address | Offset | Extent |
| --- | --- | ---: | ---: | ---: |
| GCC | `c_min_u64` | 4205904 | 11600 | 15 |
| GCC | `c_max_u64` | 4205920 | 11616 | 15 |
| GCC | `c_add_mod64` | 4205984 | 11680 | 9 |
| GCC | `c_clamp_i32` | 4205872 | 11568 | 17 |
| Clang | `c_min_u64` | 4199136 | 4832 | 11 |
| Clang | `c_max_u64` | 4199152 | 4848 | 11 |
| Clang | `c_add_mod64` | 4199200 | 4896 | 5 |
| Clang | `c_clamp_i32` | 4199120 | 4816 | 13 |

Complete file identities remain GCC41016 bytes
`3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3` and
Clang44240 bytes
`d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.
No frozen file, manifest, source, compiler option or seal was changed. GCC's
original ENDBR64 remains in its selected functions.

The target requires sequential long mode, disabled CET/IBT and shadow stacks,
supported modeled NOPs, stable modeled RAM, retained executable text and the
registered current caller/resource assumptions. Useful domains declare new
modeled ownership rather than authenticating native authority. No source/IR,
native Linux startup, physical CPU, asynchronous interference or concurrent
history refinement is established. Exact model retired counts are min/max
GCC5/Clang4, addition GCC3/Clang2 and clamp GCC7/Clang6; these counts do not prove
global minimum operations, physical micro-operations or timing.

Reproduce the certificate/report gate with
`bash scripts/verify-corpus-certificates.sh`. Both complete files must match
before any JSON is emitted. The gate builds and audits all eight typed
instances, actually fresh-replays `corpus.Certify`, checks deterministic reports,
24 rejection controls, and source/module stability. Controls include changed
clamp bytes in each compiler file and header/.comment mutations that preserve
all certified GCC bodies while still rejecting whole-file identity.

`bash scripts/verify-corpus-certificates.sh --full-project` additionally builds
`EDSL` and fresh-replays a stored aggregate importing both `EDSL` and
`corpus.Certify`. This checks both closures in one fresh kernel environment;
receipts record the actual target and scope. The global audit and deliberate
untrusted-axiom probe (`scripts/check-audit.sh`) and exact-commit CI remain
separate checks. Native CMOV32 observations do not replace kernel proof replay.
Reports concern the file bytes observed during that read.

`proof-sources.sha256` records all production Lean sources and the maintained
reporting, gate and relevant test inputs observed for this measurement. It is
diagnostic provenance, not proof of hardware correspondence or native authority.
The source parent is `543117bd844df1d2c2b7756ed167e7ce0594b013` plus the changes
in this measurement's published commit.
