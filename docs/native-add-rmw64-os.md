# Arithmetic RMW and current OS authority

`EDSL.OS.AddRMWMachine64` couples the
[qword XADD/ADD/INC CPU family](native-add-rmw64-isa.md) to the existing checked
`EDSL.OS.Atomics64.fetchAdd`. Its theorems quantify over arbitrary states,
instructions, actors and handles under their stated current-state premises.
They add no alternative OS operation or instruction interpreter.

## Coupling API

The declarations live in `EDSL.OS.Atomics64`:

| Entry point | Required evidence and result |
| --- | --- |
| `addRmw_step` | A successful checked OS call, present authorization, whole initial RAM projection, base/cell address binding and actual current decode imply the corresponding CPU step. |
| `addRmw_step_enabled` | Present `WellFormed`, authorization, RAM projection, operand binding and decode derive successful OS and CPU steps. No desired old value, successor or future successful call is a premise. |
| `addRmw_step_enabled_of_code` | Current `CodeAt` replaces the decode premise. It requires exactly the selected instruction's four or five bytes; INC needs no fifth executable byte. |
| `addRmw_step_effect` | Packages the checked call and CPU step into `AddRMWMachineEffect`. |
| `step_addRmw` | An actual successful CPU step, together with present well-formedness and authority, derives a matching checked OS call and joint effect. Operand binding applies to the instruction actually decoded. |

The delta is `instruction.delta initial`: the prestate source register for
XADD, the sign-extended imm8 for ADD, or one for INC. Base/source aliases and
source RSP retain their XADD semantics. ADD and INC preserve every GPR and have
no old-value destination; their response still records the complete
old/delta/new arithmetic event. INC preserves incoming CF.

`AddRMWMachineEffect` ties the actual checked call, current code/decode and CPU
step to the same event, the entire initial/final RAM projections and exactly
one `rmw8` access. Its `os` and `cpu` fields retain the underlying effects.
Actor, handle and cell labels remain OS identities; an actor is a modeled
principal, with no identification as a scheduler thread or native authentication.

## Retained authority and frames

Authorization rechecks the live handle and cell, actor, current allocation
owner and epoch, whole-qword containment, address profile and all eight operand
bytes' permissions, including when the modular result is unchanged.

The effect methods expose:

- `wellFormed`, `current`, `context`, `actor_handle`, `reserved`,
  `blocks_mutation` and `authority_retained`: retained allocation identities,
  reservations, registries and authority for linked handles. `os` also retains
  allocation/loan frontiers and loan records.
- `delta`, `rip`, `flags`, `nonarithmetic_flags`, `register_frame`,
  `all_registers`, `addImm8_registers`, `inc_registers` and `inc_carry`:
  the family-specific context laws.
- `full_permissions`, `permissions`, `frame` and `preserves_all_code`:
  readable/writable/nonexecutable operand bytes, unchanged executable/writable maps,
  the byte frame outside the qword and retained executable code.
- `loan_contents`, `loan_read` and `original_caller_loan`: preservation of
  existing loan contents and checked reads at their original addresses.
  `outside_original_loan` retains rejection outside the original loan bounds.

XADD source RSP may change RSP. Preservation of the original caller loan does
not grant authority for a replacement slot or prove RET enabledness. Arbitrary
XADD sources also retain their existing callee-save/ABI limits.

`AddRMWMachineEffect.xadd_iff` recovers the complete legacy
`FetchAddMachineEffect` under the XADD tag; `xadd` and `source_old` expose that
compatibility directly. It preserves successful tagged decoding, without a
claim that the widened decoder equals the legacy decoder globally.

## Scope and validation

This is one abstract coherent-WB-RAM transition under the existing long-mode,
CET-disabled, stable translation/permissions, injective physical backing,
no hidden alias and protected-resource assumptions. Unmanaged mixed-width,
MMIO, DMA and non-temporal interference remain excluded. The virtual checks
do not establish physical LOCK refinement.

The [arithmetic scheduler family](arithmetic-rmw-scheduler.md) uses this coupling
for actual XADD/ADD/INC issues; the default family retains XADD-only dispatch.
The existing Resumable effect adapter remains
ordinary-only; these theorems do not admit atomic heads there or supply a native
RMW boundary, whole-loop event-count proof, counter certificate or releasing
join. They add no frozen-corpus coverage. Whole-OS correctness, source/compiler
preservation, physical CPU/Linux correspondence, fairness and termination
require separate contracts and proofs.

Run `lake build AddRMW64Tests` for the CPU regressions and this production
coupling module under warnings as errors, `autoImplicit=false`, 300000 heartbeats
and recursion depth 128. `EDSL.All` and the existing full-project certificate
gate's fresh aggregate both import the module for dependency audit and fresh
kernel replay. See [validation](validation.md) for the full gate command.
