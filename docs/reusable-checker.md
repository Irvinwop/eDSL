# Reusable machine-code verification

`EDSL.X86.VCGen` generates bounded verification conditions for the production
x86 sequential semantics. A new function supplies exact bytes, a checked CFG,
an independent contract and a proof of the generated formula. It does not
supply a new per-instruction `localVC` proof or a routine-specific evaluator.

The checker reduces `Sequential.execute`, the same instruction semantics used
by `Sequential.step`. The generic `VCGen.sound` theorem connects that reduction
to actual decoding in current executable RAM through `CFG.Valid` and `CodeAt`.
An instruction claimed by an annotation cannot override the fetched bytes.
CFG discovery remains untrusted; the finite `CFG.check` result is proved in the
kernel. The entire selected window, including any suffix after an early RET,
must be accounted for by the existing CFG checker.

## Independent inputs

`VCGen.wp graph base AllowedRead fuel node initial Post` generates a proposition.

- `Post : Sequential.Result → Prop` describes the mathematical result, final
  memory and registers, ABI preservation, exact or bounded retired-instruction
  count, and ordered operand reads. The client defines this independently.
- `AllowedRead : State → Read → Prop` describes permitted accesses in the actual
  pre-instruction state. It can capture the caller's owned stack or data regions
  and resource/lifetime assumptions. It is separate from successful hardware
  access checks; accessible memory alone does not imply permission.
- `fuel` bounds the entire actual execution, including RET. It is an obligation
  parameter, not an assumption that an evaluator happened to return.
- `CodeAt initial.memory base bytes` binds every selected byte to accessible
  executable RAM, and the entry-PC premise identifies the checked instruction.

At every instruction the generator demands both undefined-AF choices, reduces
the actual instruction executor, checks every operand-read permission, and
composes the continuation formula at the actual successor RIP. Returned states
must satisfy `Post`. Errors, exhausted fuel, missing successors, atomic events
and syscall boundaries generate `False`.

Symbolic contracts can be proved by Lean simplification and arithmetic proof
terms. For decidable access and result predicates, `VCGen.decidableWP`
constructs the finite executable decision procedure. `VCGen.check` reflects its
result, and `VCGen.checked_sound` gives the same production-execution theorem.
`VCGen.certify` combines that reflection with `CFG.check`, an executable check
of the exact bytes in current RAM, and the current entry RIP. Its
`certify_sound` theorem needs only the successful combined result to produce
the actual decoded execution in the modeled initial state. The lower-level
`check` alone does not validate the graph or current code binding.
The starting node is explicit; a whole-function certificate uses the checked
entry node at offset zero, while an interior-node certificate starts there.
Neither route trusts external solvers or native evaluation. A rejection or a
timeout means no certificate was produced; neither establishes a defect.

## Independent undefined flags

The Bool interface above covers instructions with at most one independently
undefined status bit. For multi-bit families, import
`EDSL.X86.VCGen.Choices` and use `wpWith`, `soundWith`, `run_soundWith`
and `CheckedTraceWith`. These use the production `Sequential.executeWith`
and quantify over complete flag-choice vectors. Finite checking enumerates
only the active bits after proving that the other choices cannot affect the
complete execution observation. Uniform Bool vectors alone are insufficient.

Register-local vector families share `RegisterChoiceEffect`: the production
registration provides the state transformer, active-bit agreement, empty
operand-read trace and complete memory frame. Generic read provenance and
`CFG.executeWith_memory` carry those laws into the resource policy. Adding a
family therefore does not require instruction-specific cases in each policy
or weakest-precondition soundness proof. Full64 IMUL and
[low32 right shifts](shift-right32.md) use this interface.

`vcgen_runWith` reduces vector obligations using the same checked successor
and continuation helpers. The client still supplies its independent mathematical
contract and code/caller-resource premises; choosing the vector interface does
not discharge those obligations.

## The reusable conclusions

`VCGen.sound` yields a real `Sequential.Executes`, the independent contract,
an instruction bound, and a `CheckedTrace`. `VCGen.run_sound` also yields an
equation for the production evaluator at the supplied fuel. `all_executions`
quantifies over every complete AF sequence; `safe` and `no_divergence` derive
the existing machine's safety and termination predicates.

`CheckedTrace.read_origin` connects each reported operand read to an actual
decoded step in an actual execution prefix. It proves both the client's
permission at that step and `OperandReadSucceeds` in the current RAM. Instruction
fetches are bound separately by `CodeAt`; they are not included in operand reads.

The checked read-only profile also provides a shared whole-memory frame theorem.
`execution_memory`, `run_sound_frame` and `certify_sound_frame` derive complete
memory and permission-map preservation for actual executions. Executable clients
can keep their value/count/read predicates decidable without trying to decide
extensional equality of arbitrary memory functions at every possible result.

`lower_bound_exhausted` supports independent minimum-instruction contracts for
the particular binary and admitted input. If `Post` proves at least `n` retired
instructions, every evaluation with less than `n` fuel exhausts. This does not
claim an optimal algorithm, a minimum across equivalent binaries, a cycle count,
or a bound on speculation, cache activity or physical micro-operations.

## Sparse cutpoints for loops

`VCGen.Cutpoints.wp` generates a nonempty block's conditions up to RET or the
first successor marked as a cutpoint. It composes interior instructions using
the production executor. At a cutpoint arrival it requires the supplied
invariant and a strictly smaller dynamic rank. The client supplies only sparse
cutpoint invariants, ranks and proofs of the generated whole-block formulas.

`Cutpoints.Annotations.machineAnnotations` constructs the existing CFG proof
interface automatically: residual generated formulas become interior assertions,
and the single generic soundness proof supplies all local instruction
obligations. The resulting certificate reuses the established cutpoint
termination, prefix safety, all-choice execution and read-origin theorems.
Successful checking of a cyclic CFG alone still proves no termination; an
unconditional self-loop cannot satisfy the required dynamic rank decrease.

The shared [cutpoint policy](../EDSL/X86/VCGen/CutpointPolicy.lean) derives
whole-memory preservation and every-prefix read authority from the same
production execution. The [scalar bridge](pure-call.md) lifts those sparse
proofs to current caller/code resources through
`pureCall_semantics_of_cutpoints`. The [full64 popcount client](popcount.md)
uses independent cardinality for its invariant and rank, shared scalar frames,
ADD32 imm8/INC32 and signed disp8 LEA rules.

This layer's independent postcondition has type `State → Prop`. Its instruction
bound is the existing conservative cutpoint/depth bound. Exact dynamic cost and
ordered footprint contracts are currently directly expressible by the bounded
`Result → Prop` API; the loop layer does not infer exact accounting automatically.

## Proof-script reuse

`EDSL.X86.VCGen.Tactics` shares production-WP reduction and checked successor
search across clients. `vcgen_run` handles bounded WPs; `vcgen_block` handles
cutpoint blocks; `vcgen_next` proposes only indices within the existing
32-node profile and must prove the index bound and successor RIP. These
macros generate ordinary Lean proof terms. `vcgen_graph` proposes normalized
finite CFG data; its validity requires separate kernel evidence. Mathematical contracts, current
permission facts, invariants and ranks remain client obligations.

[The new-function guide](verify-a-function.md) and its small modular-doubling
example show how to reuse the scalar-call bridge without adding a decoder,
evaluator, resource manager, registry task or executable driver.

The [unsigned-average client](unsigned-average.md) shows reuse on two distinct
unchanged compiler outputs: one width-parametric arithmetic identity discharges
both generated formulas, while shared scalar frames, generic useful candidate
admission and final-file constructors handle the common obligations. Select a
compiler's semantic theorem before packet export so unrelated annotation
proofs do not enlarge its packet. Required proof dependencies stay checked.

## Current demonstrations

One shared example interface covers identity, modular addition, bitwise XOR,
unsigned minimum/maximum, an ordinary stable-memory load, and unsigned clamp.
The generated formulas prove independent mathematics together with memory/ABI
preservation, the actual return target and stack adjustment, exact retired
counts and ordered operand reads for every admitted input and AF sequence.

Default Clang output supplies the seven public examples and supported corpus
candidates. Frozen default GCC artifacts retain ENDBR64; the sequential
decoder now admits its exact encoding under the explicit CET/IBT-disabled
target. The shared `CompilerComparisons` family and
[named certificates](corpus-certificates.md) compose unsigned min/max for both
exact compiler files with actual-address OS caller resources. The later
[scalar constructor](corpus-scalar-certificates.md) reuses the same files and
caller environment for both modular-addition outputs, with a registry-owned
natural-number contract and the generic PureCall resource/WP adapters. Remaining
candidate contracts retain their independent obligations.
The [signed clamp client](compiler-clamp32.md) similarly reduces both exact
frozen bodies through the production WP and generic PureCall adapter. Its
three low32 bindings leave upper halves arbitrary; the relational interval
specification admits equal endpoints. Register CMOV32 and its resource rules
are shared ISA foundations, including false-condition upper32 clearing.
The frozen corpus is never stripped or recompiled with weaker feature options
to increase its coverage count. A CPU theorem conditional on `CodeAt` still
needs accepted final-artifact and environmental composition before increasing
the end-to-end corpus count.

The synthetic loop demonstration checks generated blocks with a sparse
invariant and a decreasing rank over the full positive 64-bit counter range.
It is a checker/invariant demonstration and is not an optimized corpus entry.
Its result and conservative bound have the loop layer's limited contract
described above.

## Scope and failure boundaries

This first generator inherits the checked CFG profile: at most 64 selected
bytes and 32 instructions; supported register operations, conditional moves,
branches and ordinary RAM loads; read-only code and data; a checked runtime
return-stack read. Straight-line and finite bounded control flow use the same
generator. The bound can unroll a loop only when the full admitted iteration
count fits; it is not an invariant-based unbounded-loop proof by itself.

Stores, locked instructions, syscalls and unsupported encodings are rejected by
the current CFG profile. They are not silently weakened to register operations
or ordinary reads. CET-enabled execution, stack-changing CALL/PUSH/POP and many
compiler instruction families remain outside this profile even where another repository
module supports a different execution profile. Frozen compiler output retains
its real bytes and default optimization features, so these gaps remain visible
in corpus measurements.

The sequential machine assumes ordinary stable RAM, four-level canonical
addresses, alignment checking and CET disabled, and no asynchronous changes to
control state or memory. OS allocation, ownership, permissions, lifetime and
caller-stack admission remain explicit environmental obligations. A completed
sequential proof establishes no x86-TSO refinement, concurrent linearizability,
source-language preservation, native-kernel conformance or whole-OS safety.

The corpus counts a function only when independent universal behavior, exact
final artifact binding, environmental obligations and audited kernel evidence
are all present. Decoding, compiling, native regression tests and a conditional
checker API do not themselves increase certification coverage.
