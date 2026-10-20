# Absolute-value and byte-reversal certificates v1

Conditional coverage is **11/40 functions and 22/80 compiler artifacts**, with
one distinct concurrent function. Both unchanged frozen `c_abs_i32` and
`c_byteswap64` outputs now satisfy independent mathematical contracts through
the shared sequential VCG, scalar-call and complete-file resource adapters.
See [contracts and limits](../../../docs/unary-functions.md).

[report.json](report.json) is the actual deterministic complete-file CLI output.
[proof-sources.sha256](proof-sources.sha256) binds the validated public source
snapshot. Frozen compiler inputs and all preceding measurements are unchanged.

Local validation on home-pc, 2026-10-19, with Lean 4.35.0, warnings as errors,
one Lean thread and unchanged proof-packet resource limits:

- Full catalogue, all 22 executables and regression libraries: **1,355 build
  jobs**, exit 0. Global audit: **27,816 declarations**, allowed axioms only;
  an injected untrusted transitive axiom was rejected for the required reason.
- Full-project/corpus gate: **1,317 command expectations passed**, including
  typed named-ELF, current-resource and independently literal retired-count
  anchors, deterministic reports and synthetic input rejection controls.
  Its aggregate audit covered **28,124 declarations**, allowing only
  `propext`, `Quot.sound` and `Classical.choice`.
- Actual fresh replay of `CorpusFullReplay`, importing `EDSL.All`, the corpus
  CLI and reusable/unary regressions: exit 0, **07:00:05–07:12:12 UTC**.
- The gate exported all four raw body claims and accepted their installed-CLI
  grades at default limits. Eight wrong-task or changed-final-RET controls
  rejected with the required kernel declaration-type-mismatch diagnostic.
  Full named-ELF identity is a separate typed certificate obligation.
- Existing grading compatibility suite: **21 accepted grades, 18 expected
  rejections**, owned native contracts and old/new DAG-depth regression passed.
  Sources, compiled objects and actual exporter/grader binaries stayed stable.
- Finite native accepted-plus-fresh replay: **2,816 observations**, **176 kernel
  modules**, both AF choices and a **10,494-declaration audit**. This is owned
  fixture conformance evidence, not physical CPU/OS refinement.

The complete gate closed at **07:15:00 UTC** with source, frozen-file,
compiled-module, gate-input and actual CLI-binary stability checks passing.
Closed command streams, exits, timestamps and SHA256 receipts remain in local
ignored evidence. No frozen corpus ELF was executed by this certificate gate.
This record makes no claim about remote CI or publication.

Absolute value binds low32 RDI with arbitrary upper bits and excludes signed
`INT32_MIN`; its result is nonnegative with the same mathematical square.
Byte reversal admits every full64 input and specifies all eight reversed
base-256 digits. Universal theorems retain actual RET, ABI frames, full RAM
and permissions, original caller authority and every AF stream. Exact retired
model counts are GCC/Clang 5/4 for absolute value and 4/3 for reversal.
Stable ordinary RAM, no asynchronous interference, current logical authority
and CET/IBT/shadow stacks disabled remain assumptions. Source/IR preservation,
physical CPU/native Linux refinement, whole-OS safety and minimum hardware
cost remain separate work.
