/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Clients
import EDSL.Audit

namespace EDSL.Tests.AtomicLogical64Grading
open X86 OS.AddressSpace
open EDSL.Grading.AtomicLogical64
open EDSL.Grading.AtomicLogical64.Clients

/-- Unsupported bytes are usefully admitted. Actual decoding faults, so the
fixed union Claim cannot certify them by filtering admission or vacuity. -/
theorem unsupported_rejected : Nonvacuous [0xff] ∧ ¬Claim [0xff] := by
  refine ⟨nonvacuous (by decide) (by decide), ?_⟩
  intro claim
  obtain ⟨_, _, shared, initial, pre, _, _, _⟩ := Domain.useful_current [0xff] (by decide) (by decide)
  have opcode := pre.code.2 0 0xff (by rfl)
  simp only [BitVec.add_zero] at opcode
  have failed : LockedLogical64.step false initial = .error .unsupportedEncoding := by
    simp [LockedLogical64.step, LockedLogical64.decodeAt, opcode]
  obtain ⟨_, _, covered, _⟩ := claim.1 Domain.input shared initial pre (fun _ => false)
  have fault := covered.machine.no_fault_prefix
    (LockedLogical64.run_fault (fuel := 0) (choices := fun _ => false) failed)
  cases fault

/-- RET alone really returns from the current caller slot. Its unchanged RAM
contradicts a missing requested bit on an inhabited, useful admitted input. -/
theorem ret_only_rejected : Nonvacuous [0xc3] ∧ ¬Claim [0xc3] := by
  refine ⟨nonvacuous (by decide) (by decide), ?_⟩
  intro claim
  obtain ⟨old, mask, shared, initial, pre, oldRead, source, index, missing, requested⟩ :=
    Domain.useful_current [0xc3] (by decide) (by decide)
  have decoded := LockedLogical64.decodeAt_of_code .ret pre.code
  have actual : LockedLogical64.step false initial = .ok
      ⟨.returned (OS.Atomics64.Routine.returned initial Domain.input.returnAddress),
        [.stack8 (initial.registers .rsp)]⟩ := by
    rw [LockedLogical64.step_eq_execute false decoded]
    exact LockedLogical64.execute_ret_context initial Domain.input.returnAddress false
      pre.stack pre.returnCanonical
  obtain ⟨_, returned⟩ := claim.all_results pre (LockedLogical64.Executes.ret
    (choices := fun _ => false) actual)
  obtain ⟨old', final, before, after, mathematical⟩ := returned.post.value
  have beforeEq : old' = old := Except.ok.inj (before.symm.trans oldRead)
  have afterEq : final = old := Except.ok.inj (after.symm.trans oldRead)
  subst old'
  subst final
  exact missing ((mathematical index).mpr (Or.inr (by rwa [source])))

/-- All words and all AF streams exercise the actual runner. Two current OS
operations, ordered labels, three retired instructions and current-before
chaining distinguish this implementation from the one-RMW implementation. -/
theorem double_run (old mask : Word) (choices : Choices) :
    ∃ middle evolved result first second,
      LockedLogical64.run choices 3 (Domain.initial bytes9 old mask) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes9 old) 11 ⟨0⟩ mask = .ok (middle, first) ∧
      OS.Atomics64.logicalDiscard middle 11 ⟨0⟩ mask = .ok (evolved, second) ∧
      result.instructions = 3 ∧ result.events = [first.logical, second.logical] ∧
      result.accesses = [.rmw8 65536, .rmw8 65536, .stack8 32768] ∧
      first.logical.event.before = old ∧ second.logical.event.before = first.logical.event.after ∧
      loadQWord result.state.memory 65536 = .ok second.logical.event.after ∧
      result.state.memory = toMemory evolved.legacy.shared.resources.space ∧
      Logical64.MathematicalResult .union old mask second.logical.event.after := by
  have pre := Domain.resource_pre bytes9 (by decide) (by decide) old mask
  obtain ⟨middle, evolved, result, first, second, covered, post, operation1, operation2,
    retired, events, accesses, before, chain, after, mathematical⟩ := witness9 pre choices
  have oldRead := Domain.old_read bytes9 (by decide) old mask
  have beforeEq : first.logical.event.before = old := Except.ok.inj (before.symm.trans oldRead)
  exact ⟨middle, evolved, result, first, second,
    LockedLogical64.run_complete covered.machine (by rw [retired]; exact Nat.le_refl _), operation1, operation2,
    retired, events, accesses, beforeEq, chain, after, post.current.coupled,
    by rw [beforeEq] at mathematical; exact mathematical⟩

/-- The second retained event reads the RAM of its own actual CPU/OS prefix.
This excludes an entry-memory snapshot even when repeated union is idempotent. -/
theorem second_event_current_memory (old mask : Word) (choices : Choices) :
    ∃ (evolved : Shared) (result : Result) (first second : Event)
      (currentShared : Shared) (before after : X86.State) (accesses : List LockedLogical64.Access),
      LockedLogical64.run choices 3 (Domain.initial bytes9 old mask) = .ok result ∧
      result.events = [first.logical, second.logical] ∧
      Current (frame bytes9 Domain.input (Domain.shared bytes9 old) (Domain.initial bytes9 old mask))
        currentShared before ∧
      FetchWithin (frame bytes9 Domain.input (Domain.shared bytes9 old) (Domain.initial bytes9 old mask)) before ∧
      LockedLogical64.step (choices 1) before = .ok ⟨.atomic64 second.logical after, accesses⟩ ∧
      loadQWord before.memory second.logical.event.address = .ok first.logical.event.after ∧
      loadQWord (toMemory currentShared.legacy.shared.resources.space) second.logical.event.address =
        .ok second.logical.event.before ∧
      result.state.memory = toMemory evolved.legacy.shared.resources.space := by
  have pre := Domain.resource_pre bytes9 (by decide) (by decide) old mask
  obtain ⟨_, evolved, result, first, second, covered, post, _, _, retired, events, _, _, chain, _⟩ :=
    witness9 pre choices
  have selected : result.events[1]? = some second.logical := by rw [events]; rfl
  obtain ⟨before, after, _, _, accesses, path, actual, _, effect⟩ := covered.machine.event_origin selected
  obtain ⟨currentShared, current, fetch⟩ := covered.prefix (Current.of_pre pre) path
    (by rw [retired]; decide)
  refine ⟨evolved, result, first, second, currentShared, before, after, accesses,
    LockedLogical64.run_complete covered.machine (by rw [retired]; exact Nat.le_refl _),
    events, current, fetch, actual, ?_, ?_, post.current.coupled⟩
  · simpa only [chain] using effect.transition.2.2.1
  · rw [←current.coupled]
    exact effect.transition.2.2.1

/-- The same independent literal oracle also checks the single-OR runner and
its one actual event; both implementations solve the same count-free task. -/
theorem literal_single (old mask expected : Word)
    (oracle : Logical64.MathematicalResult .union old mask expected) (choices : Choices) :
    ∃ evolved result event,
      LockedLogical64.run choices 2 (Domain.initial bytes5 old mask) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes5 old) 11 ⟨0⟩ mask = .ok (evolved, event) ∧
      result.events = [event.logical] ∧ result.instructions = 2 ∧
      event.logical.event.before = old ∧ loadQWord result.state.memory 65536 = .ok expected := by
  have pre := Domain.resource_pre bytes5 (by decide) (by decide) old mask
  obtain ⟨evolved, result, event, covered, _, operation, retired, events, _, before, after, mathematical⟩ :=
    witness5 pre choices
  have oldRead := Domain.old_read bytes5 (by decide) old mask
  have beforeEq : event.logical.event.before = old := Except.ok.inj (before.symm.trans oldRead)
  rw [beforeEq] at mathematical
  have value : event.logical.event.after = expected := Logical64.MathematicalResult.unique mathematical oracle
  exact ⟨evolved, result, event,
    LockedLogical64.run_complete covered.machine (by rw [retired]; exact Nat.le_refl _),
    operation, events, retired, beforeEq, by rwa [value] at after⟩

/-- Literal expectations use natural-bit membership, independently of the
executor's OR expression and its byte update helper. -/
theorem literal_double (old mask expected : Word)
    (oracle : Logical64.MathematicalResult .union old mask expected) (choices : Choices) :
    ∃ middle evolved result first second,
      LockedLogical64.run choices 3 (Domain.initial bytes9 old mask) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes9 old) 11 ⟨0⟩ mask = .ok (middle, first) ∧
      OS.Atomics64.logicalDiscard middle 11 ⟨0⟩ mask = .ok (evolved, second) ∧
      result.events = [first.logical, second.logical] ∧ result.instructions = 3 ∧
      first.logical.event.before = old ∧ second.logical.event.before = expected ∧
      second.logical.event.after = expected ∧ loadQWord result.state.memory 65536 = .ok expected := by
  obtain ⟨middle, evolved, result, first, second, ran, operation1, operation2,
    retired, events, _, before, chain, after, _, mathematical⟩ := double_run old mask choices
  have firstMath := OS.Atomics64.Routine.mathematical _ _ _ _ _ operation1
  have firstValue : first.logical.event.after = expected :=
    Logical64.MathematicalResult.unique (by simpa only [before] using firstMath) oracle
  have finalValue : second.logical.event.after = expected :=
    Logical64.MathematicalResult.unique mathematical oracle
  exact ⟨middle, evolved, result, first, second, ran, operation1, operation2,
    events, retired, before, chain.trans firstValue, finalValue, by rwa [finalValue] at after⟩

-- Bit63 is requested while an existing bit32 and bit0 must survive. This
-- catches dword truncation, sign extension and wrong operand selection.
example (choices : Choices) :
    ∃ middle evolved result first second,
      LockedLogical64.run choices 3
        (Domain.initial bytes9 0x0000000100000001 0x8000000000000000) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes9 0x0000000100000001) 11 ⟨0⟩
        0x8000000000000000 = .ok (middle, first) ∧
      OS.Atomics64.logicalDiscard middle 11 ⟨0⟩ 0x8000000000000000 = .ok (evolved, second) ∧
      result.events = [first.logical, second.logical] ∧ result.instructions = 3 ∧
      first.logical.event.before = 0x0000000100000001 ∧
      second.logical.event.before = 0x8000000100000001 ∧
      second.logical.event.after = 0x8000000100000001 ∧
      loadQWord result.state.memory 65536 = .ok 0x8000000100000001 :=
  literal_double _ _ _ (by
    unfold Logical64.MathematicalResult Logical64.HasBit
    decide +kernel) choices

example (choices : Choices) :
    ∃ evolved result event,
      LockedLogical64.run choices 2
        (Domain.initial bytes5 0x0123456789abcdef 0x8040201008040201) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes5 0x0123456789abcdef) 11 ⟨0⟩
        0x8040201008040201 = .ok (evolved, event) ∧
      result.events = [event.logical] ∧ result.instructions = 2 ∧
      event.logical.event.before = 0x0123456789abcdef ∧
      loadQWord result.state.memory 65536 = .ok 0x8163657789afcfef :=
  literal_single _ _ _ (by
    unfold Logical64.MathematicalResult Logical64.HasBit
    decide +kernel) choices

example (choices : Choices) :
    ∃ evolved result event,
      LockedLogical64.run choices 2 (Domain.initial bytes5 0xfedcba9876543210 0) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes5 0xfedcba9876543210) 11 ⟨0⟩ 0 = .ok (evolved, event) ∧
      result.events = [event.logical] ∧ result.instructions = 2 ∧
      event.logical.event.before = 0xfedcba9876543210 ∧
      loadQWord result.state.memory 65536 = .ok 0xfedcba9876543210 :=
  literal_single _ _ _ (by
    unfold Logical64.MathematicalResult Logical64.HasBit
    decide +kernel) choices

-- Zero is still two actual write-authorized RMWs, including both unchanged
-- current-before values and an unchanged full64 high-bit word.
example (choices : Choices) :
    ∃ middle evolved result first second,
      LockedLogical64.run choices 3 (Domain.initial bytes9 0xfedcba9876543210 0) = .ok result ∧
      OS.Atomics64.logicalDiscard (Domain.shared bytes9 0xfedcba9876543210) 11 ⟨0⟩ 0 = .ok (middle, first) ∧
      OS.Atomics64.logicalDiscard middle 11 ⟨0⟩ 0 = .ok (evolved, second) ∧
      result.events = [first.logical, second.logical] ∧ result.instructions = 3 ∧
      first.logical.event.before = 0xfedcba9876543210 ∧
      second.logical.event.before = 0xfedcba9876543210 ∧
      second.logical.event.after = 0xfedcba9876543210 ∧
      loadQWord result.state.memory 65536 = .ok 0xfedcba9876543210 :=
  literal_double _ _ _ (by
    unfold Logical64.MathematicalResult Logical64.HasBit
    decide +kernel) choices

/-- Adjacent RAM really contains the rest of the instruction and RET, and the
machine really returns. A three-byte selected window still cannot cover the
four-byte OR. This tests coverage separately from fetch/decode failure. -/
theorem truncated_extent (choices : Choices) :
    ∃ shared initial evolved result,
      EDSL.AtomicLogical64.Pre bytes5 Domain.input shared initial ∧ Useful initial ∧
      LockedLogical64.run choices 2 initial = .ok result ∧
      fetchByte initial.memory (initial.rip + 3) = .ok 0x37 ∧
      ¬FetchWithin (frame [0xf0, 0x48, 0x09] Domain.input shared initial) initial ∧
      ¬CoveredExecution (frame [0xf0, 0x48, 0x09] Domain.input shared initial)
        choices shared initial evolved result := by
  let shared := Domain.shared bytes5 0
  let initial := Domain.initial bytes5 0 0x8000000000000000
  have pre := Domain.resource_pre bytes5 (by decide) (by decide) 0 0x8000000000000000
  have useful : Useful initial :=
    ⟨0, Domain.old_read bytes5 (by decide) _ _, ⟨63, by decide⟩,
      by unfold Logical64.HasBit; decide, by unfold Logical64.HasBit; decide⟩
  obtain ⟨evolved, result, _, covered, _, _, retired, _⟩ := witness5 pre choices
  have decoded := LockedLogical64.decodeAt_of_code .orRdiRsi (OS.Atomics64.Routine.first_code pre.code)
  have noFetch : ¬FetchWithin (frame [0xf0, 0x48, 0x09] Domain.input shared initial) initial := by
    intro fetch
    obtain ⟨offset, _, bound⟩ := fetch.decoded decoded
    change offset + 4 ≤ 3 at bound
    omega
  exact ⟨shared, initial, evolved, result, pre, useful,
    LockedLogical64.run_complete covered.machine (by rw [retired]; exact Nat.le_refl _),
    pre.code.2 3 0x37 (by rfl), noFetch, fun impossible => noFetch impossible.fetchWithin⟩

/-- Coverage is checked again at a later instruction. The first OR fits, and
the machine executes the second OR using adjacent executable bytes, but the
seven-byte extent cuts that second instruction short. -/
theorem truncated_second_instruction (choices : Choices) :
    ∃ shared initial evolved result before after label accesses,
      EDSL.AtomicLogical64.Pre bytes9 Domain.input shared initial ∧
      LockedLogical64.run choices 3 initial = .ok result ∧
      Current (frame bytes9 Domain.input shared initial) evolved result.state ∧
      LockedLogical64.step (choices 1) before = .ok ⟨.atomic64 label after, accesses⟩ ∧
      before.rip = initial.rip + 4 ∧
      ¬FetchWithin (frame [0xf0, 0x48, 0x09, 0x37, 0xf0, 0x48, 0x09]
        Domain.input shared initial) before := by
  let shared := Domain.shared bytes9 0
  let initial := Domain.initial bytes9 0 0x8000000000000000
  have pre := Domain.resource_pre bytes9 (by decide) (by decide) 0 0x8000000000000000
  obtain ⟨_, evolved, result, _, second, covered, post, _, _, retired, events, _⟩ := witness9 pre choices
  have selected : result.events[1]? = some second.logical := by rw [events]; rfl
  obtain ⟨before, after, _, _, accesses, path, actual, _, _⟩ := covered.machine.event_origin selected
  have pc : before.rip = initial.rip + 4 := by
    cases path with
    | atomic64 first tail =>
      cases tail
      exact (LockedLogical64.step_atomic64_sound first).2.1.rip
  refine ⟨shared, initial, evolved, result, before, after, second.logical, accesses, pre,
    LockedLogical64.run_complete covered.machine (by rw [retired]; exact Nat.le_refl _),
    post.current, actual, pc, ?_⟩
  intro fetch
  obtain ⟨offset, atOffset, bound⟩ := fetch.decoded (LockedLogical64.step_atomic64_sound actual).1
  change offset + 4 ≤ 7 at bound
  have small : offset < 2^64 := by omega
  have total : 4096 + offset < 2^64 := by omega
  have natural := congrArg BitVec.toNat atOffset
  rw [pc] at natural
  change 4100 = (4096 + offset % 2^64) % 2^64 at natural
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total] at natural
  omega

end EDSL.Tests.AtomicLogical64Grading

#audit_edsl
