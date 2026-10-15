# Private findings and reporting

Status: record format and planned workflow. The tracked
[example format](../findings/index.example.json) is empty. Live records are
ignored local files; never commit real findings or their metadata. No external
reporting service is implemented, and no real defects are claimed.

## Evidence before a verdict

Analysis may return proved, checked counterexample, unsupported, timeout,
invalid certificate or a model inconsistency. Unsupported analysis and failed
proof search are not violations of a program's contract. An `unsafe` construct
or particular source language is not itself a defect.

Record a candidate with its exact source revision/build/image, component,
independent violated property, initial state and environment assumptions,
witness/trace, checker/model versions and evidence location. Check that the
property is required, the state is feasible, the execution follows supported
semantics and the observation really violates it. Review whether the problem
is in the target, compiler, model, specification or checker.

For a security classification, establish the relevant trust boundary, attacker
capabilities, affected configurations and demonstrated impact. A model-level
violation is useful research evidence; it is not automatically a reproduced
security vulnerability in a deployed kernel.

## Queue states

| State | Meaning |
| --- | --- |
| suspected | Candidate evidence needs checking/model review |
| confirmed | Justified property violation with checked evidence and feasible conditions |
| report-ready | Affected revision/configuration, independent reproduction, concise impact and review are complete |
| reported | Submission to a configured recipient is recorded with a receipt/reference |
| resolved | Resolution/fix is recorded and checked against the original evidence |
| dismissed | Invalid model/specification, unreachable conditions, duplicate or disproved candidate; retain the reason |

Each future ledger entry needs an ID, state, target/build identity, property,
evidence kind and scope, reproduction status, classification, review record,
private artifact references and disclosure state. Keep raw artifacts under
access control; `findings/index.json`, `findings/records/`, `findings/private/`
and `artifacts/` are excluded from Git. Real findings must also be excluded
from CI artifacts and logs. CI uses only owned synthetic fixtures.

## Reporting boundary

Preparing a report and transmitting it are separate operations. The current
workflow only queues findings. Automated sending requires a configured recipient
and explicit authorization for that reporting route; it must record what was
sent and the response. No report is sent merely because a solver returned a
candidate or timed out.

Recheck the affected project's current disclosure procedure before submission.
For Linux, use the official [security-bug reporting guide](https://docs.kernel.org/process/security-bugs.html),
including its AI-assistance guidance and threat-model review. Prepare concise
plain-text evidence with an exact affected revision, triggering conditions,
reproduction information and demonstrated impact; follow its directions for
handling the reproducer and proposed fixes. A model-only counterexample stays
labeled as such until the required real-world evidence exists.

Normal correctness defects and security vulnerabilities may use different
routes. Public release of a finding is an explicit disclosure decision, separate
from this public code repository. Do not move local records into tracked paths.
