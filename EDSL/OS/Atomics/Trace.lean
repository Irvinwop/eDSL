/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Machine

namespace EDSL.OS.Atomics
open X86 AddressSpace

structure Event where
  actor : Nat
  identifier : Nat
  handle : Handle
  before : BitVec 32
  after : BitVec 32
  deriving DecidableEq, Repr

def Event.os (event : Event) : AtomicExchange.Event :=
  ⟨event.handle.owner, event.handle.ticket, ⟨event.handle.address, event.before, event.after⟩⟩

/-- Arbitrary finite exchange-only schedules at one cell. Each actor supplies
its own stored handle, and each step reads the current shared memory.
Administrative steps and zero-handle gaps are not silently treated as exchanges. -/
inductive ExchangeTrace (address : Word) : State → State → List Event → Prop where
  | refl {state} : ExchangeTrace address state state []
  | next {before middle after actor identifier value old handle events}
      (authorized : authorize before actor identifier = .ok handle)
      (atCell : handle.address = address)
      (success : exchange before actor identifier value = .ok (middle, old))
      (tail : ExchangeTrace address middle after events) :
      ExchangeTrace address before after (⟨actor, identifier, handle, old, value⟩ :: events)

theorem ExchangeTrace.history {address : Word} {before after : State} {events : List Event}
    (trace : ExchangeTrace address before after events) : History before after := by
  induction trace with
  | refl => exact .refl
  | next _ _ success _ induction => exact .next (.exchange success) induction

theorem ExchangeTrace.os {address : Word} {before after : State} {events : List Event}
    (trace : ExchangeTrace address before after events) :
    AtomicExchange.History address before.shared after.shared (events.map Event.os) := by
  induction trace with
  | refl => exact .refl
  | @next before middle after actor identifier value old handle events authorized atCell success _ induction =>
    obtain ⟨selected, shared, observed, exchanged, same⟩ := exchange_ok _ _ _ _ _ success
    have equal := Except.ok.inj (authorized.symm.trans observed)
    subst selected
    have sharedEq := congrArg (fun pair : State × BitVec 32 => (pair.1.shared, pair.2)) same
    dsimp only at sharedEq
    have actual : AtomicExchange.exchangeWord before.shared handle.owner handle.ticket handle.address value =
        .ok (middle.shared, old) := exchanged.trans (congrArg Except.ok sharedEq.symm)
    exact .next atCell (.exchange actual) induction

theorem ExchangeTrace.chain {address : Word} {before after : State} {events : List Event}
    (trace : ExchangeTrace address before after events) (old : BitVec 32)
    (observed : loadDWord (toMemory before.shared.resources.space) address = .ok old) :
    ∃ final, loadDWord (toMemory after.shared.resources.space) address = .ok final ∧
      AtomicExchange.Chain old (events.map Event.os) final := trace.os.chain old observed

/-- An independent multiset contract: initial cell plus inserted words equals
final cell plus returned old words, counting duplicates. This does not assume
any relation between actors' later replacement arguments and their old returns. -/
theorem chain_conservation {old final : BitVec 32} {events : List AtomicExchange.Event}
    (chain : AtomicExchange.Chain old events final) :
    List.Perm (old :: events.map (fun event => event.exchange.after))
      (final :: events.map (fun event => event.exchange.before)) := by
  induction chain with
  | nil => exact .refl _
  | @cons old event events final observed _ induction =>
    simp only [List.map_cons]
    rw [observed]
    exact (List.Perm.cons old induction).trans (.swap _ _ _)

theorem ExchangeTrace.conservation {address : Word} {before after : State} {events : List Event}
    (trace : ExchangeTrace address before after events) (old : BitVec 32)
    (observed : loadDWord (toMemory before.shared.resources.space) address = .ok old) :
    ∃ final, loadDWord (toMemory after.shared.resources.space) address = .ok final ∧
      List.Perm (old :: events.map (·.after)) (final :: events.map (·.before)) := by
  obtain ⟨final, read, chain⟩ := trace.chain old observed
  refine ⟨final, read, ?_⟩
  simpa only [List.map_map, Function.comp_def, Event.os] using chain_conservation chain

end EDSL.OS.Atomics
