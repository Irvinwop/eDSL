# Callable atomic union proof grading

`EDSL.Grading.AtomicLogical64` fixes an independent discarded full64 union
contract over the strict locked-OR/RET abstract machine. A submission supplies
literal code and serialized Lean proof data. It cannot choose the input domain,
postcondition, resource policy, ISA, imports or checking limits.

The ISA currently recognizes only `LOCK OR qword [RDI], RSI` and `RET`.
Admission does not recognize a solution shape or require future success.
The domain constructs present resources for every nonempty window of at most
4096 bytes and arbitrary symbolic old64/mask64, including undecodable bytes and
RET-only code. Separate useful witnesses request a bit absent from actual RAM.
Unsupported decoding, proof rejection and resource exhaustion establish no defect.

## Fixed contract

Initial admission is the unchanged `AtomicLogical64.Pre`: current well-formed
OS resources, stored typed actor/handle authority, actual coupled RAM, complete
code and caller-slot loans, actual code bytes and caller return, and the stated
canonical/nonwrapping ABI conditions. No old target value, decoding outcome,
future mutation, successful run, instruction count or event count is assumed.

`Frame` freezes the original code extent, caller slot, target and typed cell.
`Current` rechecks authority and the original loans against the current shared
world after every step. A proof-only `Step` pairs an actual CPU step with its
actual checked OS `logicalDiscard`; RET retains the same current world and
reads the original caller slot. `CoveredExecution` covers each complete decoded
instruction inside the selected extent and retains every actual event, access,
AF choice and retired instruction. It has no administrative history-hop rule.

For every admitted input and every AF stream, `SemanticClaim` requires an
actual returning covered execution with:

- Actual initial/final target reads satisfying independent natural-number
  bit membership: a final bit occurs exactly when it occurs in the initial
  word or the original RSI mask.
- Actual caller return and original RSP+8, SysV callee-saved registers,
  nonarithmetic flags, and outside-target byte/permission frames.
- The same trace's current OS endpoint, exact surviving registries/frontiers,
  original named loans, and their actual byte/permission cells.

`Claim` also requires a useful current admission witness. Its run and actual-result
theorems derive fuel from execution, bind resources to every successful actual
result, and exclude actual non-fuel faults. The task is an uninterrupted callable
contract. It does not assert that a whole multi-instruction call is one RMW.

## Different implementations and separate costs

`Clients.claim5` proves the five-byte OR/RET implementation. `Clients.claim9`
proves two ORs followed by RET. Both solve the same count-free task for all
old words, masks and AF streams. The second consumes the first operation's
actual current world and retains both events, including unchanged-value events.
Independent bit membership proves final union idempotence; neither event is erased.
Owned GNU23 fixtures produce these distinct windows with GCC13 and Clang18.

`Returned.useful_lower_bound` in the accounting module derives at least two retired instructions
on every useful input: some requested absent bit must change, requiring an actual
RMW and RET. The first solution attains two; the second retires three and remains
admissible. This is an optimum only within the strict OR/RET instruction model
on useful inputs. It gives no global x86, micro-op, physical latency or source-level
optimum, and adds no cost requirement to admission or the task's postcondition.

## Data-only CLI and artifact scope

```sh
lake build edsl-grade-atomic-logical64 edsl-proof-export
lake env .lake/build/bin/edsl-grade-atomic-logical64 function.bin proof.json
lake env .lake/build/bin/edsl-grade-atomic-logical64 --elf 9 function.elf proof.json
```

Raw input is the complete nonempty byte window, bounded at 4096 bytes. ELF input
is bounded at 65536 bytes; the explicit span selects a file-backed executable
window beginning at ELF entry. Every executed instruction must remain completely
inside that window. Other executable regions are not claimed to execute.

The final kernel-checked wrapper binds each whole literal file, successful
selection and the fixed claim for its selected bytes. Symbols/sections do not
choose code. Unexecuted metadata can differ while the same code proof remains
applicable: each distinct file receives its own checked wrapper. Dynamic/runtime
relocations and process startup remain outside the restricted loader.

This differs from the separate [five-byte convenience certifier](atomic-logical64.md),
which requires one complete five-byte executable segment. Neither API silently
changes the other's scope.

The installed grader imports generic contracts/domains and excludes `Clients` and
submission modules. Candidate declarations and expressions are data checked with
the kernel declaration API and recursive dependency audit. Exporting local source
is a separate client operation, and does not establish successful grading.
The new CLI retains the existing packet limits and uses kernel depth512
for both packet and artifact checks. It raises no proof/checking budgets.

Exit statuses are 2 for usage, 3 for artifact admission, 4 for malformed proof
protocol data, 5 for proof/audit rejection, 6 for resource limits, and 1 for
internal/IO failure. Only `ACCEPTED` reports successful grading. The CLI and
immutable trusted installation are IO trust boundaries, not proved service
isolation, allocation or wall-clock guarantees.

## Verification and remaining work

`scripts/verify-atomic-logical64-grading.sh` compiles both owned GNU23 solutions
with GCC13/Clang18, exports reference/body packets through fresh auxiliary proofs,
and grades raw/full ELF inputs after hiding the auxiliary client's source/olean.
It checks wrong-code/proof/span bindings, malformed/bounded input and permitted
metadata changes, then audits and freshly replays the production/client proofs.
Source snapshots, commands, statuses and manifests remain on incomplete runs;
the cached workflow uploads hidden snapshot files as well.

The tests check useful unsupported and RET-only admissions, actual fault/value
refutations, current authority and lifecycle gates, literal high-bit/zero-mask
results, and truncated instruction coverage while adjacent RAM remains executable.
Compiler artifact checks in this grader job execute no native fixture. The separate
five-byte profile retains its finite native observations.

The separate [atomic set proof grader](atomic-set64-grading.md) adds AND/XOR
tasks and mixed instruction implementations under an uninterrupted contract.
The original OR-only engine and its claims remain available.

Wider ISA, mixed widths, store buffers, source memory orders,
concurrent linearizability and native pthread/kernel refinement remain future work.
The locked profile's coherent WB memory, translations/aliases/layout, controls/CET,
private context and native atomic-object lifetime interpretation assumptions remain
external. No complete OS or physical CPU refinement is established.
