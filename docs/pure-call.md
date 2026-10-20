# Generic scalar read-only calls

`EDSL.PureCall.Contract` describes a scalar function through a mathematical
`Spec`: mathematical inputs, argument bindings, input domain, result relation
and useful-input predicate. The six argument slots are RDI, RSI, RDX, RCX, R8
and R9. `word64` fixes the complete register; `low32` leaves its upper half
arbitrary. Unbound slots are unconstrained.

Each concrete specification needs independent review. Registered grading selects
its fixed specification through the trusted registry.
The generic type cannot prevent circular predicates or inputs containing an
assumed result or execution. Submissions must never select a weaker grading
contract. No concrete task or registry case is added by these modules.

`Pre` contains present mathematical-domain, argument, executable-code and
original caller-slot facts. It requires the existing canonical continuation,
nonwrapping stack extent and canonical post-return stack pointer. Admission
contains no decoder, graph, fuel, desired output or future-success callback.
`Post` requires the mathematical RAX result, complete unchanged RAM and
permissions, actual return address, RSP+8, all six SysV callee-saved GPRs and
unchanged nonarithmetic flags.

`EDSL.PureCall.Resources` binds that admission to the existing
`OS.CallResources.Current`. `ResourcePre.machine` derives raw admission, and
`semantics_of_raw` transports the original world, allocation owners/epochs,
code and caller loans through every actual prefix and return. Only the original
eight-byte STACK operand is permitted. Changing RSP or finding readable equal
bytes elsewhere creates no authority. Stores, DATA operands, atomics and
syscalls need other contracts. Useful present resource evidence establishes
both nonvacuity domains with `nonvacuous_of_resource`; it does not assume that
the code has any successful execution. The existing `CallResources.Domain`
can construct a new modeled initial registry from supplied mapping facts;
it does not authenticate existing or native ownership.

`EDSL.PureCall.Candidate.nonvacuous` packages that construction for a supplied
independent `Spec`, admitted useful input and any nonempty byte list of at most
4096 bytes. It realizes all six argument slots and retains the original caller
and code loans without a decoder, registry task or future-result premise.
Unsupported bytes can therefore have an inhabited domain while failing the
separate semantic proof. [Unsigned average](unsigned-average.md) uses this helper
instead of rebuilding its candidate resource world.

`EDSL.X86.VCGen.pureCall_semantics_of_generated` consumes a checked
complete CFG, an entry at offset zero and a universally proved production WP.
It uses the existing `VCGen.Core.sound` and `VCGen.Policy` proof infrastructure
to establish total decoded execution for all AF streams and the current-resource
policy. `Evidence` may additionally describe counts, reads or flags; its required
projection to `Post` stays separate from specification and admission. The
adapter adds no interpreter or unchecked solver interface. Optional shared
kernel-checked proof-script automation is provided separately by
`EDSL.X86.VCGen.Tactics`; see [the worked function guide](verify-a-function.md).
This module adds no minimum-cost or grading-score claim.

For sparse scalar loops, the same
[VCG adapter](../EDSL/X86/VCGen/PureCall.lean) exposes
`pureCall_raw_of_cutpoints` and `pureCall_semantics_of_cutpoints`. Clients prove
annotation existence and the entry invariant for every admitted initial state.
The [shared cutpoint policy](../EDSL/X86/VCGen/CutpointPolicy.lean) supplies
termination for every AF stream, complete memory preservation and every-prefix
original return-slot authority. Invariants and ranks are proof evidence;
admission still contains only present input, code and caller facts.

[`PureCall.ScratchFrame`](../EDSL/PureCall/Frame.lean) records permitted scratch
registers, unchanged RAM/permissions and nonarithmetic flags. Its `refl`,
`calleeSaved` and `post_return` helpers share loop and terminal frames.
`post_return` still requires the independent result, actual return target and
RSP adjustment; it supplies no execution or successful stack read. The
[popcount guide](popcount.md) shows both compiler artifacts using these shared
interfaces and separate semantic evidence with the existing ELF constructors.

The profile remains sequential stable ordinary RAM in long mode, with alignment
checking disabled, four-level canonical addresses, CET/IBT and shadow stacks
disabled, supported modeled instruction features and no asynchronous signals,
MMIO or concurrent interference. Full native SysV stack alignment and CPU/OS
feature state are not encoded by this admission. Logical worker identities
and loans do not authenticate native threads. Native loading, physical CPU
refinement and source/IR preservation remain separate obligations. Unsupported
instructions, failed proofs and timeouts establish no certificate or defect.

`tests/PureCall.lean` proves one synthetic complete LEA/RET window against
natural addition modulo 2^64. It exercises actual fetched execution, caller
return, complete ABI/RAM/flags and original-resource survival for arbitrary
caller state and every AF stream. Independent numeric instances include wrap,
high-bit addition, carry beyond low32, zero and a noncanonical integer result.
Useful nonvacuity comes from present mapping/loan facts at a supplied nondefault
entry. These are model proofs, not native conformance or ELF/corpus certificates.

For a standalone final executable, [spec-indexed ELF certificates](elf-certificates.md)
reuse this semantic claim, complete named-file checking and present caller
resources. Existing registered scalar certificates use the same construction
and retain the required proof of equality to the fixed grading contract.
