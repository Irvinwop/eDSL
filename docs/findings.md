# Handling analysis results

Verification distinguishes a proved contract from an unsupported operation,
invalid certificate, timeout, or counterexample. Failed proof search alone is
not evidence of a program defect. Neither is a particular implementation
language or an `unsafe` construct.

## Review a property violation

Before attributing a result to the analyzed program, establish:

1. The independent property and why it is required.
2. The exact source revision, executable, build configuration, and initial state.
3. A checked execution or witness within the supported semantics.
4. The environmental assumptions and whether they hold for the target.
5. Whether the discrepancy belongs to the program, specification, model,
   compiler, or checker.

A security claim additionally needs a relevant trust boundary, attacker
capabilities, affected configurations, and demonstrated impact. A model-level
counterexample is useful evidence, but does not by itself establish a
vulnerability in a deployed program or kernel.

## Store and disclose evidence

The optional [record format](../findings/index.example.json) supports local
analysis. Live records and reproducers use ignored `findings/index.json`,
`findings/records/`, or `findings/private/` paths with suitable access controls.
These paths are excluded from Git; that exclusion is not encryption.

Do not publish third-party findings, metadata, traces, or reproducers in this
repository, CI logs, or artifacts. Follow the affected project's disclosure
policy. Preparing evidence and sending it are separate actions; no automated
reporting service is implemented.

For vulnerabilities in eDieSeL itself, use the private route in the
[security policy](../SECURITY.md). Public regression tests should use owned
synthetic fixtures that reproduce the relevant verifier behavior without
exposing a third-party finding.
