# First-match search certificates v1

Conditional coverage is **8/40 functions and 16/80 compiler artifacts**, with
one distinct concurrent function. Both unchanged frozen c_memchr_index and
c_linear_search_u32 functions now have fixed independent earliest-match or
full64 SIZE_MAX contracts. One width-parametric VCG proof per compiler layout
covers both widths; current full-image resources compose through the existing
buffer certificate API.

[report.json](report.json) is the actual deterministic complete-file CLI output.
[proof-sources.sha256](proof-sources.sha256) binds the milestone sources,
regressions, native validator and CI wiring. Frozen definitions, compiler
options, final ELFs and historical measurements remain unchanged. See
[contracts and limits](../../../docs/first-match-searches.md).

Local validation on home-pc, 2026-10-18:

- Lean 4.35.0, warnings as errors and one Lean thread.
- Combined certificate build: 151 targets, exit 0. Four explicit fixed-task,
  file and symbol certificate inhabitants also checked, exit 0.
- Input-traced search test library: 159 targets, exit 0.
- Full project and previous bounded-scan regressions: 634 targets, exit 0.
- Full-project/corpus gate: **758 command expectations passed**, including
  deterministic real-file reports and rejection of altered code, metadata,
  extents, task/model/proof references, registrations and CLI inputs.
- Actual fresh kernel replay of CorpusFullReplay, importing both EDSL and
  corpus.Certify: exit 0. Combined audit: **26,892 declarations**, with only
  propext, Classical.choice and Quot.sound.
- Native wrapper: **132,152 CPU observations** matched the public machine:
  131,072 CMP8 pairs across the two encodings, 1,024 CMP32 corner cases and
  56 sign-extended register-immediate cases. Flags, GPR/RIP frames, precise
  DATA1/DATA4 footprints, guard boundaries and schema rejection controls passed.
  This is finite conformance, not a physical hardware refinement theorem.

The full gate ran from 20:20:08 through 20:37:04 UTC. Fresh replay itself ran
from 20:24:54 through 20:35:18 UTC. Closed command receipts and source, frozen
file, compiled-module and gate-input stability evidence remain in the private
local gate run. No frozen corpus ELF was executed by the gate. CI repeats the
maintained validation; this record makes no claim about a remote CI run.

Universal correctness covers arbitrary admitted finite snapshots with
n < 2^64, all AF streams, low8/low32 keys with arbitrary upper bits, exact
return behavior and complete RAM/ABI/current-resource frames. Empty inputs
need no DATA loan or valid data pointer. Compatible read-only aliases and
unaligned u32 inputs are admitted; positive reads require the entire exact
snapshot. Conservative model-instruction bounds are upper bounds, not minimum
operations or CPU timing. Stable ordinary RAM, modeled authority, long mode,
four-level canonical addressing and disabled CET remain assumptions. Source
preservation, physical CPU/native Linux refinement and synchronization for
these searches remain separate work.
