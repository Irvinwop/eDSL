# Unsigned full64 average certificates v1

Conditional coverage is **13/40 functions and 26/80 compiler artifacts**,
including one concurrent function under the existing managed model. Both unchanged
row-08 `c_average_u64` windows are added: GCC offset 11712 / VA 4206016 / 20
bytes; Clang offset 4928 / VA 4199232 / 16 bytes. The
[12/40 popcount measurement](../popcount-v1/) and every previous measurement
remain historical; frozen compiler files, source and options are unchanged.

The independent `average64` task binds full64 RDI/RSI and admits every pair.
The result is the floor of the **unbounded natural sum** divided by two,
including sums that overflow a word. Distinct overflowing operands
`(0xffffffffffffffff, 0xfffffffffffffffd)` establish useful current admission
separately. Width-parametric mathematics, shared logical SHR by one, the scalar
VCG, generic candidate admission, neutral stack resources and the existing
complete named-file constructor compose the [certificates](../../../docs/unsigned-average.md).
The exact modeled retired counts, including RET and GCC ENDBR64, are 7/6;
they are execution conclusions, not algorithmic or physical minimum costs.

[report.json](report.json) is the actual complete-file CLI output from the
accepted local gate. [proof-sources.sha256](proof-sources.sha256) records that
historical gate's exact inputs. After it passed, two test-wiring changes added
the independently checked `tests.WordMathAverage` module to `AverageTests` and
the full aggregate replay imports. No ISA, contract, body, resource, registry,
report or proof-packet limit changed. The arithmetic tests also passed separate
source compilation and actual `leanchecker --fresh` replay.
Clean-checkout CI then exposed an unregistered shared native test helper:
`tests.native.RegisterCapture` is now an explicit `UnaryTests` root. With its
previous local object removed, Lake rebuilt that helper and successfully built
`UnaryTests AverageTests` (340 jobs). This additional test-registration change
does not alter the historical local gate or any production proof.
[publication-sources.sha256](publication-sources.sha256) records the final source
snapshot including that wiring. Current exact-commit CI must validate the expanded
aggregate; the earlier local receipt is not relabeled as that later snapshot.

Local validation on home-pc, 2026-10-20, with Lean 4.35.0, warnings as errors,
`LEAN_NUM_THREADS=1`, direct Lean `-j1` and unchanged packet limits:

- Full-project build: **1,013 jobs**. Aggregate axiom audit: **29,081 EDSL
  declarations**, allowing only `propext`, `Quot.sound`, `Classical.choice`.
- Actual fresh kernel replay of `CorpusFullReplay`, containing `EDSL.All`, the
  corpus CLI and reusable verification regressions: exit 0,
  **07:44:13–07:55:44 UTC**.
- **1,687 recorded command expectations passed**, including deterministic
  complete-file reports, row identity/extents, current resources, eight scalar
  body packets, source/module/frozen/tool/binary stability and synthetic
  rejection controls. All closing pins and the receipt manifest passed.
- Both installed average body packets passed unchanged defaults: **77,638 GCC**
  and **72,214 Clang** decoder steps, below 300,000 steps and depth 128.
  Wrong-addition-task and changed-final-RET controls rejected with status 5 and
  the required kernel `declTypeMismatch` diagnostic.
- The previously completed installed body/reference packet check passed all
  four combinations: GCC **77,638 / 78,265**, Clang **72,214 / 72,713** steps;
  eight intended rejection controls passed. The later neutral caller-helper
  change was covered by the final aggregate replay above.
- Historical owned SHR finite evidence contains **10,240 observations**, **320
  kernel modules** and a **33,213-declaration audit**. It predates a PATH-only
  public-runner portability repair; actual default-HOME and custom-ELAN_HOME
  setup checks passed afterward. Full current clean-checkout native CI remains
  a separate requirement. Finite conformance proves no physical refinement.

Exact local receipts remain in ignored storage at
`artifacts/corpus-certificates/runs/run.20261020T073118Z.frBVz3pg` and
`.cache/shift-average/root/{resume-aggregate-acceptance,wordmath-regressions-01,packets-02}`.
The pre-pause interrupted gate remains separate and was not accepted. HDD
archives are indexed at `/mnt/d/Codex/cold/edsl/INDEX.md`. Seals establish
identity/stability; kernel checks and audits establish the stated proof scope.
This record makes no remote-CI or main-publication claim.

The target retains stable ordinary modeled RAM, the recorded canonical-address
profile, CET/IBT/shadow stacks off, supplied logical ownership/caller loans and
no asynchronous interference. Native Linux loading/authority, physical CPU/OS
refinement, source/IR/compiler preservation, concurrency outside the managed
profile and minimum physical cost remain outside these conditional certificates.
Parity and rotation still need their own exact body/task/resource acceptance;
mathematical helpers and CFG admission alone earn no certification credit.
