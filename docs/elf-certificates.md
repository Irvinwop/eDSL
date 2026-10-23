# Generic final-ELF certificates

Import `EDSL.PureCall.ELFCertificate` to combine an independently chosen
`PureCall.Spec` with the exact bytes of a named function in a complete ELF file.
Use the [named-function importer](named-elf-import.md) to generate the metadata
witness and exact-file acceptance proof through the existing `edsl-cfg-import`
command. Functional correctness still comes from the independent client proof.
`PureCall.ELFCertificate spec file name` keeps the specification, complete file
and exact byte name as external indices. Its `ELF.FunctionInput` carries the
table, symbol metadata, function window and selected bytes checked by the
existing production `ELF.FunctionSymbol` checker. The same `input.bytes`
indexes the semantic claim and every admitted call.

The module provides a thin composition of existing proofs. It imports the
neutral `ELF.CallerResources` and `PureCall.Domain` providers, with no corpus,
concrete client or task-registry dependency. It introduces no interpreter,
checker or registration. An arbitrary specification still needs independent
mathematical review: the type cannot prevent a vacuous or circular specification.
Existing registered grading requires its original trusted task and registration
equality; this API grants no authority to substitute another contract.

A certificate contains successful complete-file/name checking, a
`Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) input.bytes`, and a
useful present call at the selected address. `ELFLoadedCall` records admission
of that same input into a prior address space, current resources and ABI
arguments, the initial PC equal to the selected window base, and
`FunctionWindow.TextUnchanged` between the installation and current memory.
That last condition covers both readable byte observations and execute
permissions. Equal bytes elsewhere cannot replace the selected-address witness.
Admission contains no predicted result or successful future execution premise.

`ELFCertificate.ofCaller spec input checked semantics caller fresh callerFacts
separate value domain useful` builds a certificate from these independently
supplied facts. The caller provides present mappings, a readable complete return
slot, canonical return and post-return stack addresses, fresh rounded LOAD pages,
and code/stack interval separation. The neutral providers install the checked
image and construct arguments and current resources at its selected address.
They declare a new modeled ownership/loan world; they do not transport or
authenticate pre-existing native ownership.

`ELF.CallerResources.Stack` supplies a reusable eight-byte return-slot mapping
for arbitrary valid stack and return words. `Stack.facts` proves the slot/return
conditions from explicit bounds and canonical-address premises;
`Stack.check_sound` proves rounded-page freshness from a sufficient interval
check. The separate code/stack separation premise is still required. See the
[generated named-ELF proof](../tests/templates/NamedELFFunctional.lean) for the
complete composition with a newly imported compiler output.

| API | Proved conclusion |
| --- | --- |
| `ELFLoadedCall.code` | Executable `CodeAt` in current memory at the call's actual selected PC for the same input bytes. |
| `ELFCertificate.binding` | Checked metadata, exact symbol-name/extent contract, complete layout and selected file/address/byte correspondence. |
| `ELFCertificate.resource call` | Total correctness for every AF stream and the read-only resource policy for any admitted current call. |
| `ELFCertificate.nonvacuous` | Useful raw and current-resource domains, derived from the same selected-address witness. |
| `ELFCertificate.useful_execution` | A single admitted useful call with current executable code, total correctness and the full resource policy together. |

The `resource` theorem accepts **any** `ELFLoadedCall` for the certificate's
input, including calls with other domain values, caller resources, registers
and flags whenever their stated preconditions hold. Usefulness restricts only
the existential witness. The convenience constructor's chosen argument value,
zeroed unbound registers and initial flags do not restrict the universal
semantic claim.

`AllExecutions` supplies a finite returning execution for every AF choice
stream. `PureCall.Post` proves the specified mathematical RAX result, complete
memory/permission equality, the caller's return PC, RSP advanced by eight,
preservation of SysV callee-saved GPRs and all nonarithmetic flags. The resource
conclusion retains the original `CallResources.Current` in the same modeled
world at return. `Grading.ReadOnlyPolicy` retains it at every actual continuing
prefix, requires an actual read-only decode and successful step for either AF
choice, and authorizes each successful explicit operand read through the
original caller-slot loan. It preserves complete memory at every step and
excludes stores, atomics and syscalls. AF streams describe the executor's
arithmetic-flag nondeterminism; they do not model arbitrary hardware scheduling.
Exact instruction counts, read order and arithmetic flag values require
separate claims.

The accepted ELF subset, size limits and rejection behavior are those of
[the exact symbol checker](elf-function-symbol.md) and
[the function-window admission](elf-function-window.md): ELF64 little-endian
x86-64 ET_EXEC, with a unique exact global function symbol and a checked
positive file-backed executable extent of at most 64 bytes. The selected
function need not be the ELF entry. Invalid or unsupported metadata, incorrect
name/bytes/extent and mapping collisions fail the existing checker or admission;
this wrapper adds no fallback or weaker acceptance route. Failed proof search,
timeout or unsupported input establishes no defect.

The execution contract assumes the production sequential callable x86 target:
stable ordinary RAM, four-level canonical addresses, alignment checking
disabled, CET indirect-branch tracking and shadow stacks disabled, and no
asynchronous interference, signals, MMIO or concurrent agents between steps.
Code bytes and execute permissions must still hold at the current call after
any relocation, patching or protection change. The model does not perform
relocations or dynamic linking. Native calling-convention entry conditions,
including stack alignment and feature/control state, need separate justification.

OS allocations, owner/epoch metadata, live loans and logical worker principals
are explicit modeled facts. They do not authenticate a native thread, establish
physical allocation ownership or prove Linux page-table/loader behavior.
Physical page backing, aliases, revocation/interference control and CPU/memory
refinement remain environmental obligations. Native loading, runtime/CRT
dependency closure, startup/auxv/TLS, privileged transitions, exception handling
and whole-process or whole-OS execution are outside this theorem. Source/IR
preservation is a separate optional guarantee; a final-byte proof does not
require a source-language frontend.

## Independent flag choices

For an instruction with several independently undefined flags, import
`EDSL.PureCall.ELFCertificateFor` and select `ExecutionModel.flags`.
`ELFCertificateFor model spec file name` uses the same `ELFLoadedCall`,
complete-file/name checker, original caller loans and independently useful
selected-address witness as the Bool certificate. Its `resource` theorem
quantifies over all streams of the selected model, including each independent
undefined flag. Usefulness restricts only the existential witness; an admitted
zero input is covered by universal correctness even when it is not useful.

The shared route is:

1. Prove a vector `wpWith` for a graph authenticated by `CFG.Valid` against the
   exact executable bytes. The postcondition comes from an independent spec.
2. Apply `VCGen.pureCall_semantics_of_generatedWith` to obtain universal raw
   and current-resource semantics, with the original return-slot read policy.
3. Apply `ELFCertificateFor.ofCaller` using the existing complete named-ELF
   check, caller facts, fresh mappings and code/stack separation.

`ELFCertificateFor.ofBool` and `.toBool` preserve the complete original Bool
certificate. There is no conversion that treats IMUL as a Bool instruction.
A neutral certificate does not select a grading task or establish corpus
coverage; the grader must bind a trusted execution model and independent task.

`Corpus.CertificateFor id file name` adds trusted registration to this shared
composition. `Grading.registry id` fixes the execution model and whole task;
`CertificateFor.ofReadOnly` requires equality with that complete binding. Its
universal loaded-call resource theorem has no usefulness premise. Existing
certificates convert through `.ofLegacy` and `.toLegacy` with their original
Bool semantics, policies, admission and selected-address useful witness.
