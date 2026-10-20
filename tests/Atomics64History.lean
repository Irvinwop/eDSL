/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Trace
import EDSL.Audit

namespace EDSL.Tests.Atomics64History
open X86 (Word Error loadQWord)
open OS.AddressSpace (toMemory readWrite)
open OS.Atomics64

-- An event inserted into a history cannot relabel checked OR as XOR. This
-- guards the proof boundary, independently of any concrete memory fixture.
example {before after : State} {event : Event}
    (step : Step before (some event) after) (xor : event.logical.op = .bxor) : False := by
  obtain ⟨_, _, _, _, _, actual, _⟩ := step.event_sound
  rw [xor] at actual
  cases actual

-- Closing once permanently removes authority even if later histories contain
-- fresh registrations/handles. Endpoint cell liveness is not assumed.
example {before middle after : State} {labels : List (Option Event)}
    (actor : Nat) (handle : HandleId64) (mask : Word) (valid : WellFormed before)
    (closed : close before actor handle = .ok middle) (history : History middle labels after) :
    logicalDiscard after actor handle mask = .error .missingHandle := by
  exact congrFun (closed_for_history actor handle valid closed history) mask

-- Re-enrollment at an address cannot make the retired typed identity usable.
example {before middle after : State} {labels : List (Option Event)}
    (owner actor : Nat) (identifier : CellId64) (valid : WellFormed before)
    (retired : retire before owner identifier = .ok middle) (history : History middle labels after) :
    issue after owner identifier actor = .error .missingCell := by
  exact (retired_for_history owner identifier valid retired history).issue_denied owner actor

-- The projection includes actual loan termination, not merely memory writes.
-- A completed ordinary reader never regains its old ID during a rich history.
example {before middle after : State} {labels : List (Option Event)}
    (borrower loan : Nat) (valid : WellFormed before)
    (finished : finishLoan before borrower loan = .ok middle) (history : History middle labels after) :
    OS.Borrowing.authorize after.legacy.shared borrower loan = .error .missingLoan := by
  exact (finished_for_history borrower loan valid finished history).unauthorized borrower

-- Any finite alternating schedule of currently authorized actors exists, with
-- exactly those masks/events; there is no hypothetical-success premise.
example (state : State) (identifier : CellId64) (cell : Cell) (valid : WellFormed state)
    (live : state.cells identifier = some cell) (a b : Request)
    (aCurrent : a.Authorized state identifier) (bCurrent : b.Authorized state identifier) :
    ∃ after events, OrTrace identifier cell state events after ∧ events.map Event.request = [a, b, a] := by
  apply OrTrace.enabled state identifier cell [a, b, a] valid live
  intro request member
  rcases List.mem_cons.mp member with same | member
  · subst request; exact aCurrent
  rcases List.mem_cons.mp member with same | member
  · subst request; exact bCurrent
  rcases List.mem_cons.mp member with same | member
  · subst request; exact aCurrent
  · cases member

-- For symbolic full64 initial RAM, every second actor sees its peer's actual
-- update. This catches a spawn/issue-time snapshot masquerading as a chain.
example {identifier : CellId64} {cell : Cell} {before after : State} {first second : Event}
    (trace : OrTrace identifier cell before [first, second] after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    second.logical.event.before = initial ||| first.logical.mask := by
  obtain ⟨_, _, chain⟩ := trace.chain initial read
  cases chain with
  | cons _ _ firstWrite tail =>
    cases tail with
    | cons _ secondRead _ _ => exact secondRead.trans firstWrite

-- The final contract is natural-number bit membership, not a duplicated
-- expression for the implementation's byte writes or OR loop.
example {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial)
    (index : Fin 64) (missing : ¬ Logical64.HasBit initial index)
    (absent : ∀ event ∈ events, ¬ Logical64.HasBit event.logical.mask index) :
    ∃ final, loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final ∧
      ¬ Logical64.HasBit final index := by
  obtain ⟨final, finalRead, contract⟩ := trace.membership initial read
  refine ⟨final, finalRead, ?_⟩
  intro finalBit
  rcases (contract index).mp finalBit with original | ⟨event, member, bit⟩
  · exact missing original
  · exact absent event member bit

def initialState : State :=
  empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty)))

def allocated : Except Fault (State × OS.Ownership.Ticket) := do
  let (state, ticket) ← mutate initialState (.allocate 7 ⟨65536, 8⟩ readWrite)
  match ticket with
  | none => throw .missingCell
  | some ticket => return (state, ticket)

/-- Owned synthetic test: two actors contribute different halves, then actor
one repeats its mask. All three events must survive, including the no-change
RMW, and each event must read the preceding full64 result. -/
def interleaved : Except Fault (List Word × List Word × Except Error Word) := do
  let (state, ticket) ← allocated
  let (state, _) ← mutate state (.store64 7 ticket 65536 0x0000000100000000)
  let (state, cell) ← enroll state 7 ticket 65536
  let (state, a) ← issue state 7 cell 11
  let (state, b) ← issue state 7 cell 12
  let (state, first) ← logicalDiscard state 11 a 0x8000000000000000
  let (state, second) ← logicalDiscard state 12 b 0x0000000000000080
  let (state, third) ← logicalDiscard state 11 a 0x8000000000000000
  return ([first.logical.event.before, second.logical.event.before, third.logical.event.before],
    [first.logical.event.after, second.logical.event.after, third.logical.event.after],
    loadQWord (toMemory state.legacy.shared.resources.space) 65536)

example : interleaved = .ok
    ([0x0000000100000000, 0x8000000100000000, 0x8000000100000080],
     [0x8000000100000000, 0x8000000100000080, 0x8000000100000080], .ok 0x8000000100000080) := by rfl

#audit_edsl
#print axioms OrTrace.chain
#print axioms OrTrace.membership
#print axioms OrTrace.enabled
#print axioms History.borrowing

end EDSL.Tests.Atomics64History
