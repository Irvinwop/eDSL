/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.StoreReturnValue64.Resources

set_option warningAsError true

namespace EDSL.Grading.StoreReturnValue64
open EDSL X86 X86.Sequential OS Grading.Trace OS.WordResources64

/-- A stronger local policy for implementations whose operand reads use only
the original complete caller slot. Fetches and ordinary writes keep the same
byte spans and actual widths as the registered task. -/
def stackRules (bytes : List Byte) (input : Input) (initial : State) : Rules Unit where
  Current _ _ := True
  ReadAllowed _ _ read :=
    read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8
  Effect _ before instruction _ _ :=
    FetchAllowed initial.rip bytes.length before instruction ∧ RawEffect input.address before instruction

def StackPolicy (bytes : List Byte) (input : Input) (initial : State) : Prop :=
  Policy (stackRules bytes input initial) () initial

theorem StackPolicy.raw {bytes input initial} (policy : StackPolicy bytes input initial) :
    RawPolicy bytes input initial :=
  Policy.mono policy (fun _ _ present => present)
    (fun _ _ read allowed => by
      change read.kind = .stack ∧ _ ∧ _ at allowed
      change RawReadAllowed initial read
      rw [RawReadAllowed, allowed.1]
      exact allowed.2)
    (fun _ _ _ _ _ effect => effect)

/-- Present owner authority derives each checked store and its actual machine
successor. A readonly instruction retains the same current world, including
when it changes RSP. There is no premise asserting a future OS mutation. -/
theorem RawEffect.resource_step {call : Call} {shared : Borrowing.State} {before : State}
    {instruction : Sequential.Instruction} {observation : Observation} {af : Bool}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (actual : step af before = .ok observation)
    (effect : RawEffect call.targetPointer before instruction) :
    ∃ evolved,
      SpanEffect (Threads.principal call.worker) call.ticket call.targetPointer
        shared before instruction observation evolved ∧
      match observation.result with
      | .next after | .returned after => Current call evolved after
      | .atomic _ _ | .syscall _ => False := by
  cases effect with
  | readOnly allowed =>
    obtain ⟨after, outcome, present⟩ := current_readOnly_step current decoded allowed actual
    refine ⟨shared, .readOnly allowed, ?_⟩
    rcases outcome with next | returned
    · rw [next]; exact present
    · rw [returned]; exact present
  | store32 intent span =>
    obtain ⟨evolved, checked, chosen, present, _⟩ :=
      current_store32_step current decoded intent span af
    have same := Except.ok.inj (actual.symm.trans chosen)
    cases same
    exact ⟨evolved, .store32 intent span checked, present⟩
  | store64 intent =>
    obtain ⟨evolved, checked, chosen, present, _⟩ :=
      current_store64_step current decoded intent af
    have same := Except.ok.inj (actual.symm.trans chosen)
    cases same
    exact ⟨evolved, .store64 intent checked, present⟩

private theorem stackRead_allowed {call : Call} {shared : Borrowing.State}
    {initial before : State} {read : Read}
    (current : Current call shared before) (stack : initial.registers .rsp = call.stack)
    (allowed : read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8) :
    ReadAllowed call shared before read := by
  rcases read with ⟨kind,address,width⟩
  rcases allowed with ⟨rfl,rfl,rfl⟩
  exact ⟨stack,rfl,by rw [stack]; exact stackRead_permission current.contract⟩

/-- A proved stack-only local policy lifts to the registered resource policy
from present admission facts. The invariant carries the actual evolved world
at every prefix; original loans and usable owner authority survive all writes.
This does not turn arbitrary raw data reads into ownership or loan authority. -/
theorem StackPolicy.resources {bytes resource initial}
    (pre : ResourcePre bytes resource initial)
    (policy : StackPolicy bytes (resourceInput resource) initial) :
    ResourcePolicy resource initial := by
  obtain ⟨Inv, start, advance⟩ := policy
  refine ⟨fun shared before => Inv () before ∧ Current resource.call shared before,
    ⟨start, pre.current⟩, ?_⟩
  intro shared before valid
  obtain ⟨_, instruction, decoded, enabled⟩ := advance () before valid.1
  refine ⟨valid.2, instruction, decoded, ?_⟩
  intro af
  obtain ⟨observation, rawGhost, actual, reads, effect, progress⟩ := enabled af
  cases rawGhost
  have rawEffect : RawEffect resource.call.targetPointer before instruction := effect.2
  obtain ⟨evolved, checked, present⟩ := rawEffect.resource_step valid.2 decoded actual
  refine ⟨observation, evolved, actual, ?_, ?_, ?_⟩
  · intro read member
    obtain ⟨allowed, succeeds⟩ := reads read member
    exact ⟨stackRead_allowed valid.2 pre.stack allowed,succeeds⟩
  · refine ⟨?_, checked⟩
    change FetchAllowed resource.call.code resource.call.bytes.length before instruction
    rw [pre.code]
    simpa only [pre.entry] using effect.1
  · cases outcome : observation.result with
    | next after =>
      simp only [outcome] at present progress ⊢
      exact ⟨progress, present⟩
    | returned after =>
      simp only [outcome] at present
      change Current resource.call evolved after
      exact present
    | atomic _ _ | syscall _ => simp only [outcome] at present

end EDSL.Grading.StoreReturnValue64
