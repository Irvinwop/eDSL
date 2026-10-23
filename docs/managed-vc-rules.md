# Instruction and return rules for managed executions

Import `EDSL.X86.VCGen.ManagedRules` to prove ordinary instruction steps of the
resource-checked TSO64 scheduler. The rules reuse the existing instruction
decoder, execution semantics, operand checks and queue admission. They support
both authority profiles and valid nonempty mixed store queues.

`step_ordinary` derives a successful scheduler issue from:

- A checked instruction node, current code bytes, its code-loan bounds and PC.
- A live running worker in a well-formed current state.
- Supported-instruction, operand-read and queue-admission obligations.
- The existing sequential computation and a matching next/return finish effect.

The supported ordinary profile includes existing Bool-choice scalar arithmetic
and branches. Current read widths and authority remain separate gates; legacy
DWORD atomics, syscalls and vector-only flag effects remain excluded. A branch
does not enlarge the original code loan.

No successful scheduler step or desired future history is an input premise.
These are proof rules; there is no second executor. The existing node transport
retains its 64-byte checked-window limit and represented scalar/CET-off target
assumptions. Larger functions require the existing block/CFG interfaces and
their own supported-resource bridge.

`local_code` proves that a valid pending queue cannot shadow the protected code
loan. This lets a later instruction decode the current code while earlier stores
remain buffered. `queue_checked` connects the independent queue-effect contract
back to actual admission, retaining ordinary-grant priority and the selected
managed identity. A managed store appends to the queue; it does not publish RAM.

For generated multi-instruction proofs, the [effect/scheduler bridge](effect-scheduler-bridge.md#generated-blocks-and-cutpoints)
provides current-state bounded block obligations and a sparse-cutpoint adapter.
Its passive-origin closure regenerates instruction evidence after interference;
client invariants replace a separate ghost phase for every instruction. Return
postconditions remain tied to their actual response position.

## Reusing a return response

`EDSL.OS.TSO64.Return` exposes a common RET origin and response projection for
both scheduler profiles. `returnValue` reads RAX from the actual successor worker
named by a returned observation. Its soundness theorem retains the real RET,
current original caller slot, authority, local machine computation and exact
installed context. The frame preserves the world, resources, pending entries and
store counter, even when RET leaves stores unpublished.

```lean
import EDSL.OS.TSO64.Return
open EDSL OS.TSO64

example {before : State} {action : Action} {result : State × Observation}
    {tid : Nat} {value : X86.Word} {profile : Profile}
    (valid : WellFormed before profile)
    (executed : step before action profile = .ok result)
    (response : Return.returnValue result = some (tid, value)) :
    result.1.world = before.world :=
  (Return.returnValue_sound valid executed response).frame.1
```

The fetch-add call adapter uses this common theorem through its existing public
contract. New load/store call adapters can reuse the same response and caller
facts instead of proving RET dispatch again.
The [managed load/store family](managed-plain-methods.md) composes constructive
primitive access and RET rules for checked padding/MOV64/RET bodies, with valid
nonempty FIFOs and actual access origins. Full call/order contracts remain separate.

The [regressions](../tests/ManagedRules.lean) execute a managed load, buffered
store and RET, then publish afterward. They distinguish a saved high-bit return
value from current/pending RAM, check the retained queue/counter/caller slot,
and distinguish responses from two threads whose loads straddle a publication.
Existing fetch-add call regressions and the complete-batch proof are imported
alongside these checks.

These rules do not establish a whole-function ABI frame, source memory orders,
universal C23 preservation, physical CPU/Linux correspondence or liveness.
Those remain separate proof obligations. In particular, RET and completed
publication are separate events. This API adds no compiler-corpus function credit.
