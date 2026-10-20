# Security policy

## Report a vulnerability in eDieSeL

Use **Report a vulnerability** in the repository's
[Security tab](https://github.com/Irvinwop/eDieSeL/security) to contact the
maintainer privately. Private vulnerability reporting is enabled. Do not post
sensitive reproducers or exploit details in public issues.

Relevant reports include proof-checking bypasses, incorrect machine or resource
semantics that invalidate advertised results, and unsafe handling of untrusted
proof or executable input. Include the affected revision, the expected property,
the observed behavior, and a minimal reproducer when available. Ordinary bugs,
unsupported features, and documentation issues can use public issues.

## Programs analyzed with eDieSeL

A proof establishes a specified property under its stated model and assumptions.
A failed proof, timeout, or unsupported instruction does not establish a
vulnerability. Model-level counterexamples need review against the specification,
model, and target environment before making a real-world security claim.

Keep findings about third-party software, including identifying metadata,
traces, and reproducers, out of this public repository and its CI artifacts.
Follow the affected project's private disclosure process. The project includes
only owned synthetic security and rejection fixtures in public tests.

See the [trust model](docs/trust.md) for verification boundaries and
[handling analysis results](docs/findings.md) for evidence guidance.
