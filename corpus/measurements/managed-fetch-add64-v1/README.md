# Managed concurrent fetch-add extension of corpus v1

This measurement adds both unchanged `c_atomic_fetch_add64` symbols to the
preceding scalar-clamp checkpoint: **5/40 functions, 10/80 compiler artifacts
and one distinct concurrent function**, under the recorded model assumptions.
Historical scalar and initial reports remain unchanged. Both compiler artifacts
must be certified for a function to count; two artifacts do not count as two
concurrent functions.

The independent contract is `Grading.ConcurrentTask.FetchAdd64.Claim`, model
`managed-tso64-closed-batch-v1`. A static whole-window instruction-family check
composes generic admission, history, frame and progress proofs. It covers
arbitrary full64 inputs and initial words, all admitted context populations,
and every successful finite completed schedule. Exact chronological RMW/call
coverage and independent legal modular-counter histories are conclusions.
Current entry resources, prefix safety, enabled issues, global completion,
a positive own-issue bound and represented return/ABI/resource/byte frames are
required. The fixed contract assumes no desired future success or history gate.

The actual loaded witness retains the complete checked ELF installation and
uses checked allocation/store/protection/borrow/handle/attachment operations.
Two nonzero calls share one counter with pairwise private original callers;
the same successful completed schedule has `RMW0 < RMW1 < RET0` on that cell.
This finite witness supplies useful admission, separately from universal
behavior. See [the contract and proof path](../../../docs/concurrent-fetch-add-certificates.md).

| Compiler | Symbol | Address | Offset | Extent |
| --- | --- | ---: | ---: | ---: |
| GCC | `c_atomic_fetch_add64` | 4207232 | 12928 | 13 |
| Clang | `c_atomic_fetch_add64` | 4201136 | 6832 | 9 |

Complete file identities remain GCC41016 bytes
`3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3` and
Clang44240 bytes
`d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.
No frozen file, manifest, source, option or seal changed. GCC's ENDBR64 remains
under the explicit CET/IBT-off, shadow-stack-off long-mode profile.

The concurrent result assumes scalar coherent WB RAM, suitable physical
backing/aliases, stable translation and permissions, managed access and a
closed cohort without asynchronous external mutations. Modeled actors do not
authenticate native authority. Published/physical x86-TSO, Linux/GNU atomic
orders, thread lifecycle, arbitrary pending stores, scheduler fairness and
hardware operation minima remain separate obligations. The other four scalar
functions retain their independent scalar assumptions.

Reproduce with `bash scripts/verify-corpus-certificates.sh --full-project`.
The maintained gate independently requires both typed concurrent inhabitants
and the eight scalar instances; builds and audits production; freshly replays
an aggregate importing both EDSL and corpus.Certify; checks deterministic
real-file reports and rejects altered reports/files. Full-file equality is
required before JSON emission. Native execution is not proof evidence. CI's
build/test caches accelerate elaboration; fresh replay remains separate.

`report.json` records the modeled certificate report. `proof-sources.sha256`
binds the public Lean and relevant gate/test inputs for this measurement;
it is diagnostic provenance, not physical or native-OS evidence. Source parent:
`a6c6eb81773a5e6aed131f4fba395aca213d554b`, plus this measurement's published changes.

Recorded local full-project gate: all 357 command expectations passed, including
actual fresh `CorpusFullReplay` kernel replay and the combined 25,595-declaration
allowed-axiom audit. The separate project/managed-test build passed (615 Lake
jobs), and the global audit rejected its deliberate untrusted dependency probe.
Exact-commit remote CI is a separate publication check.
