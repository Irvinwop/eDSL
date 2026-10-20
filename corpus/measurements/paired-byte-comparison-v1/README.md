# Paired byte-comparison certificates v1

Conditional coverage is **9/40 functions and 18/80 compiler artifacts**, with
one distinct concurrent function. Both unchanged frozen `c_memcmp_bytes`
windows now satisfy the fixed independent unsigned lexicographic sign contract,
observing signed low32 RAX. Shared paired-buffer VCG proofs and useful current
full-image resource witnesses compose through the existing certificate API.

[report.json](report.json) is the actual deterministic complete-file CLI output.
[proof-sources.sha256](proof-sources.sha256) binds this validated source snapshot,
regressions, native validator and CI wiring. Frozen compiler inputs and earlier
measurements remain unchanged. See [contracts and limits](../../../docs/paired-byte-comparison.md).

Local validation on home-pc, 2026-10-18:

- Lean 4.35.0, warnings as errors and one Lean thread.
- Combined certificate and test-library build: **166 targets**, exit 0, with
  stable sources. Both exact fixed-task/file/name certificate inhabitants were
  constructed and audited; 10,021 declarations had only the allowed axioms.
- Existing search regressions: **161 targets**, exit 0. Full production build:
  **630 targets**, exit 0; full-gate production build: **638 targets**, exit 0.
- Full-project/corpus gate: **1,032 command expectations passed**, including
  complete real-file equality, deterministic reports and synthetic rejection
  of changed code, metadata, extents, proof/task/compiler references, scope,
  registrations, counts and CLI inputs.
- Actual fresh kernel replay of `CorpusFullReplay`, importing both `EDSL` and
  `corpus.Certify`: exit 0. Combined audit: **27,363 declarations**, allowing
  only `propext`, `Classical.choice` and `Quot.sound`.
- The independent native wrapper passed **15,648 CPU observations**: 15,456
  supported MOVZX/CMP8/SUB32 observations and 192 native high-byte observations
  explicitly rejected by the modeled subset. Exact flags/GPR/RIP, DATA1/no-read
  footprints, three actual guard/read-only fault controls, 28 malformed-capture
  controls, eight corrupted observations and 20 encoding exclusions passed.
  This is finite conformance evidence, not physical hardware refinement.

Fresh replay ran from **22:28:55 through 22:39:30 UTC**. Closed local command,
source, frozen-file, compiled-module and gate-input stability receipts retain
the full run. No frozen corpus ELF was executed. This record makes no claim
about remote CI or publication.

Universal correctness covers arbitrary admitted equal finite snapshots with
`n < 2^64`, full64 pointers/count, all AF streams and complete RAM/ABI/current
resource frames. Compatible overlapping and unaligned inputs remain admitted;
empty calls use neither data pointer nor input-loan selector. The conservative
`9*(n+2)` model-instruction bound is an output upper bound. Stable ordinary RAM,
modeled current authority, the sequential callable target and disabled CET
remain assumptions. Source/LLVM preservation, physical CPU/native Linux
refinement, concurrent buffers and minimum hardware cost remain separate work.
