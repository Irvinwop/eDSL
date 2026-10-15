# Contributing

Read the [architecture proposal](docs/architecture.md),
[OS contracts](docs/os-semantics.md), and [roadmap](docs/roadmap.md) before
introducing an API. APIs are exploratory at this stage.

Use C, C++, and assembly for implementation. Keep OS effects explicit across
the language domains. A new operation needs a semantic contract, a target
mapping, and a clear account of unsupported capabilities and failure paths.

Build the initial compiler checks using the commands in [README.md](README.md).
CI uses Clang 18 on Linux. These checks establish GNU language-mode acceptance
and atomic/GNU syntax availability; they are not runtime or eDSL tests. The
`edsl::gnu23` and `edsl::gnucxx26` CMake interface targets carry the exact flags
for future implementation targets. Do not silently fall back to older modes.

Add tests when they establish independently defined behavior and can detect a
plausible defect. Choose unit, integration, or end-to-end coverage according to
the behavior being checked. Do not mock away native synchronization, memory,
or I/O behavior when that behavior is the subject of the test.

Do not add tests that only repeat implementation logic, assert an assigned
fixture value, or compare generated text with a copy of the generator's own
rules. Prefer executable behavior, invalid-input diagnostics, ABI checks,
compiler/IR verification, and independently defined concurrency outcomes.
Skip new tests when they add no meaningful evidence.
