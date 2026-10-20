# Byte-equality certificates v1

Validated conditional coverage is **16/40 functions and 32/80 compiler
artifacts**, including **one distinct concurrent function** under the existing
managed model; **24 functions / 48 artifacts** remain. This measurement adds
both unchanged row-20 `c_bytes_equal` outputs. The preceding
[parity and rotation measurement](../parity-rotation-v1/) retains its historical
15/40-function, 30/80-artifact result. Frozen source, compiler options,
specifications, manifests and final ELF contents are unchanged.

| Compiler | File offset | Virtual address (decimal) | Bytes | Byte cap | CFG node cap |
| --- | ---: | ---: | ---: | ---: | ---: |
| GCC | 12240 | 4206544 | 46 | 64 | 32 |
| Clang | 5376 | 4199680 | 68 | 128 | 32 |

The independent [byte-equality contract](../../../docs/byte-equality.md) compares
the complete mathematical input lists. Low8 RAX is exactly one for equal lists
and zero otherwise; the upper 56 bits are unconstrained. Other nonzero low-byte
results are rejected. Equal-length snapshots have `n < 2^64`; full64 RDI/RSI/RDX
bind the two pointers and count. Empty inputs need no DATA loan, allocation or
canonical data pointer and perform no DATA read. Compatible overlapping,
identical, unaligned, code and caller aliases require matching actual bytes
and current authority.

The body proofs reuse the production decoder, executor, sparse cutpoint VCG
and paired-buffer rules. Every modeled undefined-flag choice stream terminates.
`10 * (n + 2)` is an upper bound on retired model instructions; it establishes
neither minimum cost nor physical timing. Complete memory and permission maps,
the original caller resources and current code/input read authority survive
every actual continuing prefix and return. Return address, RSP, SysV callee-saved
registers, nonarithmetic flags and the result satisfy the ABI/postcondition at
return.

The loaded call reuses initialized paired overlapping resources through
[`ReadOnlyCallTransport`](../../../docs/read-only-call-transport.md). Attaching
the new code retains the original caller slot, worker, paired snapshots and
exact input-loan identifiers, without resetting RAM, inputs or permissions.
Both complete-file certificates apply to these overlapping mismatching inputs
for every choice stream, with the original memory and authority retained.

Clang requires the explicit 128-byte profile; the default 64-byte path rejects
the entire 68-byte function. The checked window includes its final RET at
offset 67 and the exact NOP15 encoding
`66 66 66 66 66 66 2e 0f 1f 84 00 00 00 00 00`.
Support for that exact encoding is an explicit target assumption. Decoder
admission alone establishes no equality result.

## Validation scope

The accepted certificate-gate source is
`383d1f1ef928f551b89a8424ae46c8bb019ce2e2`. On **2026-10-20**,
[Frozen corpus workflow 39454868896](https://github.com/Irvinwop/eDieSeL/actions/runs/39454868896)
completed successfully. Its downloaded artifact's entire receipt manifest was
independently checked after path rebasing, and all source/frozen hashes were
checked against an exact detached snapshot of that commit.

[report.json](report.json) records the actual accepted complete-file score.
[proof-sources.sha256](proof-sources.sha256) and
[frozen-files.sha256](frozen-files.sha256) identify the gate's proof/tooling
inputs and frozen files. These manifests identify the exact validated snapshot;
later documentation edits do not extend its proof scope.

| Certificate-gate evidence | Recorded result |
| --- | --- |
| Completion | `READY`, exit 0, `full-project-and-corpus-cli` |
| Toolchain | Lean 4.35.0, warnings as errors |
| Full-project build | 1,093 jobs passed |
| Transitive axiom audit | 30,581 declarations; only `propext`, `Quot.sound`, `Classical.choice` permitted |
| Actual external fresh kernel replay | `CorpusFullReplay`, exit 0; 16:31:52–16:39:40 UTC |
| Command expectations | 2,601 passed, including intended negative exits |
| Closing checks | All source/frozen/module/tool/binary/receipt checks passed |
| Accepted conditional score | 16/40 functions, 32/80 artifacts, one concurrent function |

The gate includes deterministic complete-file reports, exact symbol/extent
checks, useful loaded resources and equality mutation rejections. It does not
execute the input ELFs. The separate frozen/native corpus gate passed all
**80 windows**, the project-owned independent native harnesses and rejection
controls. Its actual default **64-byte/32-node** CFG diagnostics admitted
**17/40 GCC** and **15/40 Clang** windows. Diagnostic admission and finite native
conformance do not increase the certificate score or strengthen the model.

The original named-import gate also passed on this exact source. Its actual
external fresh `Joined` replay ran from **16:33:57.117766652 to
16:36:50.815863216 UTC**, its audit checked **7,682 declarations**, and all
closing pins passed. Its full downloaded receipt manifest was independently
checked. This is a separate validation scope; its counts are not added to the
certificate-gate statistics.

The installed `edsl-grade` packet interface remains scalar-only. Existing scalar
body/reference packets passed under unchanged **300,000-step / depth-128**
limits. There is no equality buffer packet API or equality packet result;
`.equalBytes` is registered through the typed buffer-certificate API. The Clang
code-size profile does not change packet limits.

[publication-sources.sha256](publication-sources.sha256) identifies only the
corrected existing one-byte RET transport regression in
[`tests/SequentialISA.lean`](../../../tests/SequentialISA.lean), checked
separately from the source-383 certificate gate. Its statement, API, no-padding
condition and 15-byte requirement are unchanged. Scoped compilation, an
allowed-only axiom audit of **2,113 declarations**, and actual external fresh
replay of `tests.SequentialISA` passed with closing source/object checks.
Production semantics and certificates are unchanged.

See [commit-specific CI results in GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions).

Reproduction commands for the separate validation scopes:

```sh
bash scripts/verify-corpus-certificates.sh --full-project
bash scripts/verify-corpus-v1.sh --frozen
```

## Reusable APIs

- [`EDSL/Grading/ByteEquality.lean`](../../../EDSL/Grading/ByteEquality.lean):
  `returnValue`, `Result`, `spec`, `resourceContract_iff`.
- [`EDSL/Grading/BufferTask.lean`](../../../EDSL/Grading/BufferTask.lean):
  `.equalBytes` and its registered independent specification.
- [`EDSL/X86/VCGen/ByteEquality.lean`](../../../EDSL/X86/VCGen/ByteEquality.lean):
  equality-specific invariants using shared paired-buffer proof rules.
- [`EDSL/Corpus/ReadOnlyCallTransport.lean`](../../../EDSL/Corpus/ReadOnlyCallTransport.lean):
  `retarget`, `retarget_contract`, `retarget_pre`, `retarget_space`,
  `resultView`, `resultView_contract_iff`, `resultView_pre_iff`.
- [`EDSL/Corpus/BufferCertificate.lean`](../../../EDSL/Corpus/BufferCertificate.lean):
  typed `Buffer.LoadedCall` and `Buffer.Certificate.ofLoadedCallWith`.
- [`EDSL/Corpus/V1/ByteEqualityWindows.lean`](../../../EDSL/Corpus/V1/ByteEqualityWindows.lean):
  complete-file/name/extent checks and explicit byte caps.
- [`EDSL/Corpus/V1/ByteEqualityBodies.lean`](../../../EDSL/Corpus/V1/ByteEqualityBodies.lean):
  `semantics` and `dynamic_bound`.
- [`EDSL/Corpus/V1/ByteEqualityResources.lean`](../../../EDSL/Corpus/V1/ByteEqualityResources.lean)
  and [`ByteEqualityCertificates.lean`](../../../EDSL/Corpus/V1/ByteEqualityCertificates.lean):
  transported loaded resources and `certificate`.

## Target assumptions

The sequential callable profile assumes stable ordinary modeled RAM, canonical
admitted addresses, supplied logical ownership and loans, x86-64 long mode,
multi-byte NOP support including the exact NOP15 above, disabled CET/IBT/shadow
stacks, and absent asynchronous interference. Native resource authority and
physical memory protections are not established by allocating a modeled world.
Source/IR/compiler preservation, physical CPU and Linux/kernel/whole-OS
refinement, and concurrent buffer execution remain open. Source load/store and
acquire/release correspondence are not proved; further atomic load/store and
OS/concurrency work is planned. Metadata and finite native tests add no modeled
guarantees. Unsupported code, proof failure and timeout establish no defect.
