# Bounded byte-scan certificates v1

Conditional coverage is **6/40 functions and 12/80 compiler artifacts**, including
one distinct concurrent function. Both unchanged frozen `c_strnlen_bytes`
functions now have the fixed `firstBoundedNulLength` task, universal generated
loop proofs and useful loaded-resource witnesses. The sequential buffer model
is `sequential-read-only-x86-buffer-callable-v1`; the concurrent row retains its
separate `managed-tso64-closed-batch-v1` model.

[report.json](report.json) is the actual deterministic complete-file CLI result.
[proof-sources.sha256](proof-sources.sha256) binds the milestone's proof, test,
validator and CI sources. The frozen corpus, source/options and earlier
measurements remain unchanged. See [the contract and limits](../../../docs/bounded-byte-scans.md).

Local validation on home-pc, 2026-10-18:

- Pinned Lean 4.35.0, warnings as errors and one Lean thread.
- Combined certificate and new regression build: 151 targets, exit 0.
- Full-project/corpus certificate gate: **463 command expectations passed**,
  including fixed-type file/task anchors, deterministic reports and rejection
  of altered code, metadata, extents, model tags, proof references and CLI inputs.
- Actual `leanchecker --fresh CorpusFullReplay`, importing both `EDSL` and
  `corpus.Certify`: exit 0. The combined audit covered **26,246 declarations**,
  permitting only `propext`, `Classical.choice` and `Quot.sound`.
- Ten existing decoder, CFG and VCG regressions: all actual source runs exit 0.
- Native Linux x86-64 probe: all **65,536** memory/immediate CMP8 pairs matched
  the public model's flags and DATA1 footprints. Read-only guard-boundary and
  NOP9 observations passed. This is finite conformance, not hardware refinement.

The full gate ran from 18:39:09 through 18:50 UTC; private command receipts and
source/object stability evidence remain in the local corpus-certificate run.
No native corpus ELF was executed by that gate. CI repeats the maintained
validation from the repository; this record makes no claim about a CI run.

The theorem covers arbitrary admitted byte snapshots with `n < 2^64`, every AF
stream, exact return behavior and complete RAM/ABI/current-resource frames.
Empty inputs require no data loan or pointer validity. Conservative model
instruction bounds are upper bounds, not minimum operations or CPU timing.
Stable ordinary RAM, modeled authority, long mode and disabled CET remain
assumptions. Source preservation, native loader/CPU/Linux refinement and
synchronization for these scan functions remain separate work.
