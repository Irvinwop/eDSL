# Reusable managed load/store methods

`EDSL.X86.VCGen.PlainMethods` uses one proof family for checked padding followed
by a qword load into RAX or a qword store, then RET. New byte windows supply an
operation descriptor, padding and current OS resources. The shared proofs handle
instruction execution, interference, queue draining, return frames and the own
instruction count; clients do not repeat an induction for each compiler output.

This is a machine-body interface. Complete call-history matching, universal C23
ordering and final-ELF certificates remain separate obligations.

## Describe and check the code

`Operation.load address` reads into RAX. `Operation.store address source` captures
the source register before execution. Both use the existing address semantics,
including supported base/index/displacement forms and register aliases. RSP may
be a store source; a load that overwrites RSP is available through the lower-level
primitive rule, with no total-return guarantee from this family.

The checker uses the production decoder at every padding, access and RET node.
It checks the exact final extent and retains the existing 64-byte window limit.
It rejects a matching prefix with extra suffix bytes, incorrect operands or width,
missing RET and undeclared padding. Larger or richer functions need their own
supported block/CFG interface.

```lean
import EDSL.X86.VCGen.PlainMethods
open EDSL X86 VCGen.PlainMethods

def loadBytes : List Byte :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x07, 0xc3]

example : Shape loadBytes (.load (.base .rdi)) 0 [.endbr64] :=
  (check_sound (by decide +kernel :
    check loadBytes (.load (.base .rdi)) [.endbr64] = true)).2
```

This establishes code shape. Functional results additionally require the current
machine/resource admission below. ENDBR64 retains the explicit CET-off target
assumption; recognizing its bytes does not establish the physical control state.

## Supply current resources

`Method` records the operation, exact bytes and code base, original registers and
flags, resources, complete managed reference, original queue/counter boundary
and canonical caller return. Its effective address uses the original registers;
it is not reevaluated after a load overwrites RAX. The source request fixes an
acquire load or release store independently of observed memory. MOV bytes alone
do not establish source-language intent.

`Current` requires current well-formed resources under `sharedCell`, current
published code within the original code loan, the original protected caller read,
and the exact current atomic-handle selection. It stores no invocation-memory
snapshot, desired result, successful future execution or graph-legality premise.
`At` supplies the checked entry/cutpoint, full register/flag/resource assertions
and a queue frame. Initial queues may contain any currently valid mixed entries.

`ManagedAccess.issue_loadMem64` and `issue_storeMem64` derive real enabled
primitive steps from these current conditions. A load obtains its value from the
actual own overlay or current published RAM. A store appends the complete
selected reference, original source value and actual counter to the existing
FIFO, then increments the counter once. It leaves the published world unchanged.
Ordinary-grant exclusion at a managed cell follows from current reservation and
allocation separation; the proof does not silently override lookup priority.

`ManagedReturn.step_ret` derives RET under either authority profile with valid
nonempty queues. It uses the current original caller slot and canonical target,
preserving the world, authority, FIFO and counter. Its response is the saved
full-width RAX. A logical store reply is unit, separately from that machine value.

## Reuse the body proofs

`advance` derives the next actual own issue at each unfinished cutpoint.
`schedule_preserves` covers every successful finite interleaving of the admitted
scheduler, including peer issues and own/peer drains. `complete` constructs a
completion from any current cutpoint using exactly its remaining own issues,
with the exact caller-supplied AF sequence. Its conclusion identifies the action
list as `List.range remaining` mapped to those issues. It requires no preparatory
drain or empty FIFO.

`all_completed` gives a full register/flag/caller/resource result for an actual
completed run, exactly `padding.length + 2` own instructions, and `OneAccess`.
That access witness retains its original action position, same-run prefix,
actual decoded instruction/effect, and the load's actual local read/source or the
store's original value/reference/occurrence. Coverage excludes an unrecorded
second own access; equal observed values cannot replace the supplied execution.
The load reply is retained through RET and subsequent interference.

The queue frame permits head drains between stages and after return. The store
may therefore have returned with its entry pending or with it already published.
Neither case is treated as publication inside the call interval. Arbitrary
initial entries retain an explicit provenance boundary: validity alone supplies
no earlier issue history or globally unique occurrence tags.

The completion theorem constructs one schedule. It implies no scheduler fairness
or eventual completion of every schedule. Own instructions, drain actions and
physical elapsed time are different costs; this count is no unrestricted
minimum-instruction or CPU-timing theorem.

## Scope and validation

The [regressions](../tests/PlainMethods.lean) use the four frozen GCC/Clang windows
and synthetic real executions with nonempty queues. They distinguish saved load
responses from later RAM, full64 stores from truncation, FIFO order and counters
from queue length, and pre-RET RSP capture from the popped stack pointer.

The [admission examples](../tests/PlainMethodAdmission.lean) construct current
resources through checked allocation, initialization, protection, borrowing and
worker attachment. Both MOV directions use `enabled`, exact-AF `complete` and
`all_completed` from that entry, without assuming a future successful run or
returned cutpoint. These examples start with empty FIFOs and no peer; the
separate execution regressions exercise mixed queues and interference.

The shared rules inherit the existing long-mode, CET-off, supported-padding,
aligned normal-RAM, translation/alias and managed-resource assumptions. They do
not establish physical x86/Linux correspondence, dynamic resource lifecycle,
source/compiler preservation, universal C23 legality or a full OS/kernel result.
This family adds no frozen corpus credit until the fixed independent call/order
contracts and exact final-file gates are proved. See [atomic call contracts](atomic-call-contracts.md)
and [checked finite atomic traces](checked-atomic-traces.md) for the adjacent layers.
