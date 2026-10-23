/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Proof-only access to the first checked production step of an existing effect
trace. The instruction and complete observation are indices of `Head`, so its
proof fields do not provide computational projections of instruction data.

This sequential evidence is used by the ordinary TSO64 adapter. It supplies
no OS admission, world transition, scheduler execution, or corpus claim.
-/

namespace EDSL.X86.VCGen.Effects
open Sequential

/-- Evidence about one actual vector-executor step at the given prestate.
The complete observation retains its result and ordered reads, including any
atomic payload. Read and effect permissions use the original policy and prestate.
A returned result additionally retains the trace's final current-state fact. -/
structure Head (bytes : List Byte) (base : Word) (policy : Policy)
    (choice : FlagChoices) (before : X86.State)
    (instruction : Sequential.Instruction)
    (observation : Sequential.Observation) : Prop where
  code : CodeAt before.memory base bytes
  current : policy.Current before
  decoded : Sequential.decodeAt before = .ok instruction
  actual : Sequential.stepWith choice before = .ok observation
  reads : ∀ read ∈ observation.reads, policy.AllowedRead before read
  effect : policy.AllowedEffect before instruction observation
  returnedCurrent : ∀ final, observation.result = .returned final →
    policy.Current final

/-- Eliminate only the existing trace's first constructor. This retains its
actual decoded instruction, entire observation and first full flag valuation;
no executor, WP recursion or instruction cases are introduced. Atomic heads
remain sequential atomic observations, without a scheduler interpretation. -/
theorem Trace.head {bytes : List Byte} {base : Word} {policy : Policy}
    {choices : ChoiceStream FlagChoices} {initial : X86.State}
    {result : Sequential.Result} {events : List AtomicEvent}
    (trace : Trace bytes base policy choices initial result events) :
    ∃ instruction observation,
      Head bytes base policy (choices 0) initial instruction observation := by
  cases trace with
  | @ret _ _ final reads instruction code current decoded actual allowedRead allowedEffect
      finalCurrent =>
    refine ⟨instruction, ⟨.returned final, reads⟩,
      code, current, decoded, actual, allowedRead, allowedEffect, ?_⟩
    intro output returned
    cases returned
    exact finalCurrent
  | @next _ _ middle reads instruction _ _ code current decoded actual allowedRead allowedEffect
      _ =>
    refine ⟨instruction, ⟨.next middle, reads⟩,
      code, current, decoded, actual, allowedRead, allowedEffect, ?_⟩
    intro output returned
    cases returned
  | @atomic _ _ middle reads instruction _ _ event code current decoded actual allowedRead
      allowedEffect _ =>
    refine ⟨instruction, ⟨.atomic event middle, reads⟩,
      code, current, decoded, actual, allowedRead, allowedEffect, ?_⟩
    intro output returned
    cases returned

#print axioms Head
#print axioms Trace.head

end EDSL.X86.VCGen.Effects

#audit_edsl
