# Full64 popcount certificates v1

Conditional coverage is **12/40 functions and 24/80 compiler artifacts**,
including one distinct concurrent function under the existing managed model.
Both unchanged row-11 `c_popcount_loop` windows are added: GCC offset 11776 /
VA 4206080 / 31 bytes; Clang offset 4976 / VA 4199280 / 28 bytes. The
[11/40 unary milestone](../unary-registers-v1/) and every preceding measurement
remain historical records; frozen inputs and options are unchanged.

The registered `populationCount64` task admits every Word64 input in RDI,
including zero, the high bit and all ones. It requires unsigned low32 set-bit
cardinality and leaves upper RAX unconstrained. `0x81` is a useful current-call
witness only. Independent mathematics, sparse loop invariants/ranks, shared
counter/address rules, complete-file/name/extent checking and current
caller/code resources compose the [conditional certificates](../../../docs/popcount.md).
Per-artifact semantic evidence keeps unrelated compiler annotations out of a
packet while retaining every required dependency and kernel check. There is
no per-program interpreter or executable.

[report.json](report.json) is the actual deterministic complete-file CLI output.
[proof-sources.sha256](proof-sources.sha256) records the source snapshot checked
by the accepted corpus gate, before four later proof-only legacy fixture
repairs, a native-runner clean-checkout repair and a reporting-text correction.
It is a historical gate-input manifest. Compatibility and native replay evidence
for those repairs is tracked separately.
[publication-sources.sha256](publication-sources.sha256) records the final code
snapshot including those repairs. The final report was regenerated through the
actual CLI after narrowing all-prefix RAM/resource wording to distinguish the
ABI result established at return. The current gate accepts it and rejects the
old overclaim; every other JSON field is unchanged. That scoped check is recorded
in `.cache/popcount/root/report-wording/attempt-02`. Frozen compiler inputs and
all preceding measurements are unchanged.

Local validation on home-pc, 2026-10-19, with Lean 4.35.0, warnings as errors,
`LEAN_NUM_THREADS=1`, direct Lean `-j1`, and unchanged proof-packet limits:

- The full-project/corpus gate built **993 jobs**. Its aggregate audit covered
  **28,799 declarations**, allowing only `propext`, `Quot.sound` and
  `Classical.choice`.
- Actual fresh replay of `CorpusFullReplay`, importing `EDSL.All`, the corpus
  CLI and verification regressions: exit 0, **10:48:57–11:04:24 UTC**.
- **1,451 recorded command expectations passed**, covering deterministic
  reports, complete file/name/extent/resource checks, source/module/frozen-input
  stability, actual CLI-binary pins and synthetic rejection controls. The
  source-frozen corpus gate closed at **11:15:51 UTC**, exit 0.
- The corpus gate accepted six scalar body packets at default limits, including
  both popcount artifacts. Popcount decoder steps were **210,427 GCC** and
  **183,173 Clang**, below the unchanged 300,000-step limit and depth 128.
- A separate installed export-and-grade run passed both body and reference
  modes: GCC **210,427 / 211,406** steps and Clang **183,173 / 183,952**.
  Eight wrong-task or changed-final-RET controls rejected with status 5 and the
  required kernel `declTypeMismatch` diagnostic.
- The combined named-ELF integration gate passed parser regressions, generated
  bindings, the functional contract, stale-proof controls, actual fresh replay
  of the joined closure and closing pins; it closed at **11:12:37 UTC**, exit 0.
- Independently sealed owned native evidence comprises **3,456 observations**,
  **216 finite kernel proof modules**, both AF choices and a
  **12,737-declaration audit**. This is finite conformance evidence.

The accepted commands were `bash scripts/verify-corpus-certificates.sh --full-project` and
`bash scripts/check-named-elf-import.sh` with the recorded environment and
per-call shared Lean lock. Exact arguments, environments, stdout, stderr,
statuses, timestamps and verified receipt manifests remain in local ignored
evidence: `artifacts/corpus-certificates/runs/run.20261019T104747Z.MmKhKtlB`,
`.cache/popcount/root/named-final-01/evidence/run.dmKctvUq`, and
`.cache/popcount/root/selection-01`. Seals establish evidence identity and
stability; theorem checking, fresh replay and audits provide validation.
The [validation guide](../../../docs/validation.md) describes the scoped suites.
This record makes no remote CI or publication claim.

The target retains stable ordinary RAM, four-level canonical addresses,
CET/IBT/shadow stacks disabled, supplied current logical ownership/loans and
absent asynchronous interference. Source/IR/compiler preservation, physical CPU
and native Linux/OS refinement, interference and minimum physical cost remain
outside these conditional certificates. Average → parity → rotation still
require shared shifts/bit mathematics and exact binary/task/resource proofs;
mathematical helpers alone earn no certification credit.
