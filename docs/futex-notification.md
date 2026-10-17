# Private-word notification across client traces

The notification layer connects the existing private WAIT and
payload-STORE/XCHG/WAKE1 publisher to an independent queue-safety contract.
After the publisher's actual XCHG and its associated WAKE1 service, the designated
WAIT worker has no queued invocation. Every later admitted mixed execution
preserves this fact while the published word remains different from the WAIT
expected value. The publisher's payload and current resource admission are
retained as well.

This is a theorem about the existing model and exact supported client bytes.
It supplies neither an unconditional scheduling guarantee nor Linux-kernel,
hardware or whole-distribution refinement.

## Contract and ordering

`EDSL.OS.Futex.Clients.Notification.Policy cohort worker expected` requires an
actual WAIT member, makes it the sole WAIT client in the immutable cohort, and
requires `expected != 1`. Other publisher and payload-peer clients remain
permitted under the existing resource and finite-control contracts.

The policy contains no queue conclusion, future execution or successful-service
premise. Current service records and their expected values are derived from
actual pending invocations and their captured request families. Registration,
mutable-word pins, protected code/return loans, physical/resource RAM equality
and FIFO grants remain current through `Admitted`.

| Comparison order | Required service behavior |
| --- | --- |
| Compare before publication | A queued waiter is removed and readied by the associated WAKE1. |
| Compare between publication and wake | Current W=1 mismatches; comparison readies EAGAIN without queueing. |
| Compare after publication and wake | The same persistent mismatch prevents queueing. |

Retries compare current RAM again. Spurious readiness remains allowed. An empty
wake supplies no credit for a later matching comparison. More than one WAIT
client needs a stronger wake policy; WAKE1 may choose the other eligible waiter.
A WAIT expected value of one would match the published word and is outside this
notification policy. Zero from WAIT establishes neither predicate truth nor
lock acquisition.

## Checked layers

`EDSL.OS.Futex.Notification` defines current-state `NoQueuedWait`, `ExpectedFor`,
`OnlyWaiter` and `CurrentWord` predicates. Its service effect theorems derive
queue changes from the actual comparison and wake code. Well-formed invocation
uniqueness and the structural one-worker policy derive the sole eligible queue;
no exact queue shape is assumed in admission. Current pins positively enable
mismatch comparison and a valid wake choice.

`EDSL.OS.Futex.Clients.Notification` composes actual issue, drain and service
steps. `exchange_wake_trace` binds XCHG and the associated WAKE1 to the same
publisher and its actual saved syscall request. Arbitrary mixed prefixes and
suffixes cover all comparison orders, retries, spurious readiness, private
resumption clobbers and drains from returned peers. `machineTrace_lift` derives
managed replay from physical issue/drain prefixes. `infinite_preserves` proves
safety at every index of any accepted infinite execution, without fairness.

`pending_worker_finishes` derives the invocation and phase from a currently
pending WAIT and constructs at most three actual runtime transitions: an
optional current-RAM comparison, resumption, and decoded RET. Its existing
`FinishesWithin` contract retains full raw RAX, original return target/RSP,
arbitrary full flags/RCX/R11, all RAM and every peer. Runtime transitions include
service actions; these bounds are not hardware instruction or cycle counts.
Existence of an enabled finite suffix does not force a scheduler to select it.

`worker_completes` also covers a waiter which has not entered its syscall, has
already resumed, or has already returned. Current decoded instructions and
protected return-stack bytes construct a suffix of at most six runtime
transitions from every supported stage. The independent `CompletesWithin`
contract retains typed full raw RAX, the original target/RSP, RAM, peers and
admission. Already resumed or returned workers retain their actual historical
flags/RCX/R11; they are not assigned new clobbers. `trace_completes` makes this
continuation available after every admitted mixed prefix following notification.

`EDSL.FutexNotificationCertificate.Specification` adds the independent waiter
policy to the existing publisher certificate. `sound` retains exact raw bytes
and current code membership; `loaded_sound` retains the literal ELF parse/load
and entry binding. `Specification.notification` transports that certificate and
published payload across the actual notification trace.
`Specification.complete` retains the same certificate through the all-stage
continuation; `complete_pending` retains caller-chosen full private clobbers for
the stronger pending-only contract.
The older certificate, CLI and service semantics retain their meanings. Loader
freshness, present resources and the existing environmental assumptions remain
caller obligations; ELF loading does not establish process startup safety.

## Evidence and boundaries

The symbolic service and client trace proofs are the primary evidence.
Project-owned schedules exercise actual transitions and independently specified
queue, result, memory and peer behavior. Certificate tests compose actual
notification with continuations from unentered, pending, resumed and returned
stages. Dependency auditing admits only
`propext`, `Classical.choice` and `Quot.sound`; fresh kernel replay checks stored
proofs under pinned Lean 4.35.0 with warnings as errors.

Native Linux/x86-64 checks remain in the existing exact final-byte publisher
harness. A watchdog or bounded race observation cannot establish eventual
scheduler progress. Portable Lean builds on other architectures establish model
proofs and do not replace those Linux observations.

The profile still uses one registered private word, stable managed lifetime
and mappings, and the existing finite client controls. General futex operations,
signals, timeouts, cancellation, process sharing, a predicate-rechecking binary
loop and blocking-mutex acquisition remain further work. Source/LLVM proofs
are optional and do not discharge native CPU or kernel correspondence.
