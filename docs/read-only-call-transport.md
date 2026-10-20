# Reusing read-only buffer call resources

Import and open `EDSL.Corpus.ReadOnlyCallTransport`. It transports an existing
`BufferCall.Resources spec` after another code extent is attached to the same
managed world. The complete address space, including every permission, remains
equal to the original space; live allocations and loans survive the checked
attachment.

Supply these independently established facts:

- A current `BufferCall.ResourceContract old old.shared`.
- `before : BufferResources.Managed` with `same : before.shared = old.shared`.
- A `ReadOnlyCalls.Attached before old.call.worker
  ⟨entry, newBytes.length⟩ []`, obtained through checked code attachment.
- `CodeAt (AddressSpace.toMemory old.shared.resources.space) entry newBytes`.

Construct `retarget old newBytes attached`. It changes the shared state and
the call's code address, bytes and code-loan identifier. It retains the worker,
original caller slot, return address, input value and entire `inputLoan`
function. `retarget_contract attached same originalContract currentCode` proves
the resulting current resource contract.

With an original `ResourcePre`, use
`retarget_pre attached same originalPre currentCode`. Its initial machine is
`{ initial with rip := entry }`: the argument registers, flags and complete
memory are retained. `retarget_space old newBytes attached same` supports whole
memory framing proofs. The attachment's `loans`, `allocations`, `history`,
`original_loan` and `authorize` theorems retain their existing meanings.

For a specification differing only in its return relation, use
`resultView old newResult : Resources { spec with result := newResult }`.
`resultView_contract_iff` and `resultView_pre_iff` equate the two admissions.
For example, `ByteEquality.spec` is the result-only update of
`ByteComparison.spec`, so paired comparison resources can be viewed through
`ByteEquality.Result` before or after retargeting. A body proof for the new
result relation remains a separate obligation.

Empty buffers retain arbitrary unused pointers and loan identifiers.
Compatible overlapping nonempty buffers retain their exact original loans.
Snapshots establish bytes; live manager loans establish authority. Checked
attachment can fail during adoption or borrowing, and transport requires its
successful result plus actual executable bytes in the original full memory.

The target assumptions are those of `BufferCall` and `CallResources`: modeled
ordinary RAM and ownership, stable sequential memory, ordinary RET without
CET, and absent asynchronous interference. This API adds no execution-success
admission premise, decoder profile, code-size cap or corpus registration.

`tests/ReadOnlyCallTransport.lean` uses synthetic memory with distinct old and
new code, overlapping input/code spans and arbitrary empty inputs. It checks
actual RET and borrowing operations, caller write denial, unrelated RAM
access restrictions, stale code-loan rejection and exact input-loan revocation.
