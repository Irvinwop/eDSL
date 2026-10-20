# Managed-word TSO trace refinement

`OS.TSO64.WordProjection` connects successful executions of the checked
scheduler to an independent memory-transition model. Clients reuse this
connection for admitted programs rather than proving buffer behavior again
for each instruction sequence. Import `EDSL.OS.TSO64.WordProjection`.

This is a finite trace refinement for registered 64-bit cells. It preserves
managed loads, buffered writes, FIFO publication and locked fetch-add effects.
It does not certify additional frozen corpus functions.

## Reference semantics

[`Concurrency.TSOWord`](../EDSL/Concurrency/TSOWord.lean) adapts the memory
fragment of Owens, Sarkar and Sewell's [x86-TSO abstract machine, §3.1,
Figure 2](https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf).
It imports only the underlying word type and machine-state definitions, with
no dependency on the scheduler, resource admission or its implementation.

Reference buffers are newest first. A write prepends; publication removes the
oldest entry. A read forwards the newest own matching entry or reads published
memory when there is no matching entry. The global lock restricts reads and
publication; acquiring and releasing it require an empty own buffer. Enqueue
is allowed even while a peer holds the reference lock.

The paper's presentation uses 32-bit values. This model uses uniform 64-bit
words and symbolic persistent cell identities. Registers, instruction cores,
fences and mixed-size overlapping locations are outside this fragment. It is
an adaptation with a Lean proof about its stated rules, not a mechanized
correspondence proof to the complete HOL4 model.

## Projection of actual execution

The projection reads each currently registered cell from published machine
memory. Distinct live cell identities have distinct physical qword starts,
derived from the resource model's allocation separation. Managed entries in
the actual oldest-first mixed FIFO are reversed for the reference buffer.
Ordinary stores are erased only with a frame for every registered cell.
Their erasure does not imply that ordinary memory is private to a thread.

| Actual effect | Reference labels |
| --- | --- |
| Managed qword load | Read with the selected cell and actual loaded value |
| Managed store issue | Write with the admitted cell and actual stored value |
| Managed FIFO head publication | One internal publication step |
| Successful locked fetch-add | Lock, read old word, write new word, publication, unlock |
| Ordinary disjoint effect, register/control step or blocked lock attempt | Empty trace, with the corresponding classification premises |

Managed load classification uses the decoded MOV, current authority selector
and successful local machine read. Equality of projected endpoint states alone
cannot justify erasing a managed read. Locked expansion uses the actual checked
RMW event, including unchanged-value writes; it retains every peer buffer and
restores the free reference lock.

`step_trace` supplies both the classified trace and a reference path.
`schedule_trace` composes those paths and retains one classification per
actual scheduler action. These are annotations of the existing executor:
there is no replacement scheduler or desired-result check in admission.

`scheduleLabels` computes annotations by traversing the existing checked
`step` function and propagates its failures. `schedule_labels_sound` takes
resource validity, an actual successful `schedule`, and the computed labels,
and supplies their exact classification and reference path. Clients can evaluate
these two accessors and apply the theorem, as the executable regressions do,
without constructing an instruction-specific reference proof.

## Boundaries and validation

The existing fixed-world resource and machine assumptions remain premises:
current grants, complete registered qwords, aligned non-crossing RAM accesses,
stable mappings, code and caller resources, and the stated CET/translation/WB
profile. The current resource model requires read/write authority even for
managed loads and reserves an allocation for each registered cell.

Initial queues and initial RAM are explicit boundaries, without authenticated
prehistory. RET neither publishes pending stores nor establishes quiescence.
Finite paths prove safety within the fragment; they supply no fairness,
eventual publication or the paper's infinite-path progress condition.

[`tests.TSOWordProjection`](../tests/TSOWordProjection.lean) executes actual
checked two-actor MOV programs. Store buffering permits both actors to read zero
before publication; a second case checks newest-own forwarding while RAM
remains unchanged. The store-buffering and locked-fetch-add cases also
return computed labels carrying the general classification and path proof;
the tests check both zero reads and the full five-label locked expansion.
These observations distinguish FIFO buffering from immediate
publication and catch reversed forwarding order.

Physical CPU correspondence, native Linux enforcement and source-language
memory-order preservation remain separate obligations. In particular, a
reads-from edge alone does not establish acquire/release synchronization.
The frozen acquire/release and relaxed-load corpus contracts retain their
existing requirements and receive no new coverage credit from this fragment.
