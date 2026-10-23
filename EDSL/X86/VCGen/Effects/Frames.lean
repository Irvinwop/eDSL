/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects
import EDSL.X86.Sequential.CFGChoices
import EDSL.X86.Memory64

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
A reusable separation policy for selected executable bytes. Authorization uses
the actual instruction and its prestate write footprint, even for same-value
writes. Successful production execution supplies the actual permission checks
and successor memory; code binding is a separate initial premise.

This adapter protects only the selected executable bytes. It supplies no OS
current authority, ownership epochs, protected caller slot, memory safety,
concurrency, TSO, linearizability, physical refinement or corpus credit. A future
OS adapter must prove current world/epochs and scheduler simulation separately.
-/

namespace EDSL.X86.VCGen.Effects
open Sequential

/-- Readonly instructions or supported writes whose actual prestate footprints
avoid the selected code. These constructors also serve as authorization rules;
none inspects an observation, final-memory equality or future code binding. -/
inductive CodeSeparated (bytes : List Byte) (base : Word) (before : State) :
    Sequential.Instruction → Prop where
  | readOnly {instruction : Sequential.Instruction} (allowed : CFG.readOnly instruction = true) :
      CodeSeparated bytes base before instruction
  | store32 {instruction : Sequential.Instruction} {address : Word} {value : BitVec 32}
      (intent : instruction.storeIntent before = some (address, value))
      (disjoint : DWordDisjoint address base bytes.length) :
      CodeSeparated bytes base before instruction
  | store64 {instruction : Sequential.Instruction} {address value : Word}
      (intent : instruction.storeIntent64 before = some (address, value))
      (disjoint : QWordDisjoint address base bytes.length) :
      CodeSeparated bytes base before instruction
  | exchange (disjoint : DWordDisjoint (before.registers .rdi) base bytes.length) :
      CodeSeparated bytes base before (.legacy .exchangeEaxRdi)
  | fetchAdd (disjoint : DWordDisjoint (before.registers .rdi) base bytes.length) :
      CodeSeparated bytes base before (.legacy .fetchAddEaxRdi)

/-- Keep the client's current-state and read predicates. Effect authorization
depends only on the actual instruction and its prestate footprint. Disjointness
does not imply writability or any other executor success obligation. -/
def codeSeparatedPolicy (bytes : List Byte) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop) : Policy where
  Current := Current
  AllowedRead := AllowedRead
  AllowedEffect := fun before instruction _ => CodeSeparated bytes base before instruction

private theorem next_continuation_state {state after : State} {reads : List Read}
    (continued : CFG.Structural.Continues ⟨.next state, reads⟩ after) : after = state := by
  rcases continued with next | ⟨_, atomic⟩
  · exact (StepResult.next.inj next).symm
  · cases atomic

private theorem atomic_continuation_state {state after : State} {event : AtomicEvent}
    {reads : List Read}
    (continued : CFG.Structural.Continues ⟨.atomic event state, reads⟩ after) :
    after = state := by
  rcases continued with next | ⟨_, atomic⟩
  · cases next
  · exact (StepResult.atomic.inj atomic).2.symm

/-- An authorized actual continuation preserves the initially bound executable
bytes while allowing data writes. The exact observation and its continuing state
remain bound to `executeWith`, including the actual legacy atomic event. -/
theorem CodeSeparated.executeWith_code {bytes : List Byte} {base : Word}
    {before after : State} {instruction : Sequential.Instruction} {choices : FlagChoices}
    {observation : Observation}
    (separated : CodeSeparated bytes base before instruction)
    (actual : executeWith before instruction choices = .ok observation)
    (continued : CFG.Structural.Continues observation after)
    (code : CodeAt before.memory base bytes) : CodeAt after.memory base bytes := by
  rcases executeWith_effect before instruction choices with single | ⟨middle, executed, _, memory⟩
  · have executed := actual
    rw [executeWith_eq_execute before instruction choices single] at executed
    cases separated with
    | readOnly allowed =>
      have framed := CFG.executeWith_memory allowed actual
      rcases continued with next | ⟨_, atomic⟩
      · rw [next] at framed
        rw [framed]
        exact code
      · rw [atomic] at framed
        exact False.elim framed
    | @store32 instruction address value intent disjoint =>
      rw [execute_storeIntent_checked _ intent] at executed
      cases allowed : canStoreDWord before.memory address with
      | false => simp [allowed] at executed
      | true =>
        simp only [allowed, ↓reduceIte, Except.ok.injEq] at executed
        cases executed
        rw [next_continuation_state continued]
        exact writeDWord_preserves_code before.memory address base value bytes code disjoint
    | @store64 instruction address value intent disjoint =>
      rw [execute_storeIntent64_checked _ intent] at executed
      cases allowed : canStoreQWord before.memory address with
      | false => simp [allowed] at executed
      | true =>
        simp only [allowed, ↓reduceIte, Except.ok.injEq] at executed
        cases executed
        rw [next_continuation_state continued]
        exact writeQWord_preserves_code before.memory address base value bytes code disjoint
    | exchange disjoint =>
      cases exchanged : executeExchange before with
      | error fault => simp [execute, X86.executeInstruction, exchanged] at executed
      | ok output =>
        simp [execute, X86.executeInstruction, exchanged] at executed
        cases executed
        rw [atomic_continuation_state continued]
        have sound := executeExchange_sound exchanged
        rw [sound.1.2.2.2]
        apply writeDWord_preserves_code _ _ _ _ _ code
        rw [sound.2.1]
        exact disjoint
    | fetchAdd disjoint =>
      cases added : executeFetchAdd before with
      | error fault => simp [execute, X86.executeInstruction, added] at executed
      | ok output =>
        simp [execute, X86.executeInstruction, added] at executed
        cases executed
        rw [atomic_continuation_state continued]
        have sound := executeFetchAdd_sound added
        rw [sound.1.2.2.2]
        apply writeDWord_preserves_code _ _ _ _ _ code
        rw [sound.2.1]
        exact disjoint
  · rw [executed] at actual
    cases actual
    rw [next_continuation_state continued, memory]
    exact code

/-- This separation policy discharges the mandatory effect-aware code frame
uniformly for any current-state and read predicates. It does not prove either
predicate, executor success, or preservation of any other memory region. -/
theorem codeSeparatedPolicy_codeFrame (bytes : List Byte) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop) :
    CodeFrame (codeSeparatedPolicy bytes base Current AllowedRead) bytes base := by
  intro before instruction choices observation after _ code actual allowed continued
  exact CodeSeparated.executeWith_code allowed actual continued code

#print axioms CodeSeparated
#print axioms codeSeparatedPolicy
#print axioms CodeSeparated.executeWith_code
#print axioms codeSeparatedPolicy_codeFrame

end EDSL.X86.VCGen.Effects

#audit_edsl
