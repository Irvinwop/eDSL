/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalRoutine
import EDSL.OS.Atomics64.LogicalTrace
import EDSL.AtomicSet64Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicSet64
open X86 OS.AddressSpace OS.Atomics64

/-- RX code and a caller slot are disjoint from the live atomic allocation.
Data bytes are explicit little-endian literals, not backend store helpers. -/
def space (opcode : Byte) : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xf0, readExecute⟩
    | 4097 => some ⟨0x48, readExecute⟩
    | 4098 => some ⟨opcode, readExecute⟩
    | 4099 => some ⟨0x37, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readOnly⟩
    | 65536 => some ⟨0x10, readWrite⟩
    | 65537 => some ⟨0x32, readWrite⟩
    | 65538 => some ⟨0x54, readWrite⟩
    | 65539 => some ⟨0x76, readWrite⟩
    | 65540 => some ⟨0x98, readWrite⟩
    | 65541 => some ⟨0xba, readWrite⟩
    | 65542 => some ⟨0xdc, readWrite⟩
    | 65543 => some ⟨0xfe, readWrite⟩
    | _ => none

def setup (opcode : Byte) : Except OS.Atomics64.Fault (OS.Atomics64.State × HandleId64) := do
  let initial := empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty (space opcode))))
  let (owned, ticket) ← mutate initial (.adopt 7 ⟨65536, 8⟩)
  let ticket ← match ticket with
    | some ticket => pure ticket
    | none => throw .missingCell
  let (registered, cell) ← enroll owned 7 ticket 65536
  issue registered 7 cell 11

def entry (shared : OS.Atomics64.State) : X86.State where
  registers register := match register with
    | .rdi => 65536 | .rsi => 0x80000000ffffffff | .rsp => 32768
    | _ => 0xdeadbeef76543210
  rip := 4096
  flags := 0xed7
  memory := toMemory shared.legacy.shared.resources.space

structure View where
  op : Sequential.LogicalOp
  old : Word
  word : Except Error Word
  instructions : Nat
  eventCount : Nat
  accesses : List LockedSet64.Access
  rax : Word
  rsp : Word
  rip : Word
  definedFlags : Word
  af : Bool
  deriving Repr

def observe (opcode : Byte) (af retAF : Bool) : Except OS.Atomics64.Fault View := do
  let (shared, _) ← setup opcode
  let output ← (LockedSet64.run (fun index => if index = 0 then af else retAF) 2 (entry shared)).mapError
    OS.Atomics64.Fault.machine
  match output.events with
  | [event] => return ⟨event.op, event.event.before, loadQWord output.state.memory 65536,
      output.instructions, output.events.length, output.accesses, output.state.registers .rax,
      output.state.registers .rsp, output.state.rip, output.state.flags &&& ~~~(0x10 : Word),
      output.state.flags.getLsbD 4⟩
  | _ => throw .missingCell

-- Independent literal whole-word oracles catch opcode confusion, truncated
-- high halves, a missing RET, lost labels, favorable AF and a changed RAX.
example (af retAF : Bool) : observe 0x21 af retAF = .ok
    ⟨.band, 0xfedcba9876543210, .ok 0x8000000076543210, 2, 1,
      [.rmw8 65536, .stack8 32768], 0xdeadbeef76543210, 32776, 8192, 0x682, af⟩ := by
  cases af <;> cases retAF <;> rfl

example (af retAF : Bool) : observe 0x09 af retAF = .ok
    ⟨.bor, 0xfedcba9876543210, .ok 0xfedcba98ffffffff, 2, 1,
      [.rmw8 65536, .stack8 32768], 0xdeadbeef76543210, 32776, 8192, 0x686, af⟩ := by
  cases af <;> cases retAF <;> rfl

example (af retAF : Bool) : observe 0x31 af retAF = .ok
    ⟨.bxor, 0xfedcba9876543210, .ok 0x7edcba9889abcdef, 2, 1,
      [.rmw8 65536, .stack8 32768], 0xdeadbeef76543210, 32776, 8192, 0x602, af⟩ := by
  cases af <;> cases retAF <;> rfl

-- Two equal XOR requests must restore every initial bit; merely remembering
-- which masks occurred (as for union) loses multiplicity and fails this test.
theorem xor_pair_restores {initial final : Word} {first second : Event}
    (chain : LogicalChain initial [first, second] final)
    (firstOp : first.logical.op = .bxor) (secondOp : second.logical.op = .bxor)
    (sameMask : second.logical.mask = first.logical.mask) : final = initial := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index inside
  let bit : Fin 64 := ⟨index, inside⟩
  have uniform : ∀ event ∈ [first, second], event.logical.op = .bxor := by
    intro event member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> assumption
  have parity := chain.symmetricDifference uniform bit
  have equivalent : Logical64.HasBit final bit ↔ Logical64.HasBit initial bit := by
    cases original : initial.toNat.testBit bit <;>
      cases maskBit : first.logical.mask.toNat.testBit bit <;>
      simpa [Logical64.bitOccurrences, List.countP_cons, sameMask,
        Logical64.HasBit, original, maskBit] using parity
  exact Bool.coe_iff_coe.mp (by simpa only [Logical64.HasBit, BitVec.testBit_toNat] using equivalent)

-- A second event in a mixed trace reads the first event's current result.
example {identifier : CellId64} {cell : OS.Atomics64.Cell} {before after : OS.Atomics64.State}
    {first second : Event} (trace : LogicalTrace identifier cell before [first, second] after)
    (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    second.logical.event.before = first.logical.event.after := by
  obtain ⟨_, _, chain⟩ := trace.chain initial read
  cases chain with
  | cons _ _ tail =>
    cases tail with
    | cons current _ _ => exact current

end EDSL.Tests.AtomicSet64

#audit_edsl
#print axioms EDSL.OS.Atomics64.LogicalRoutine.correct
#print axioms EDSL.OS.Atomics64.LogicalTrace.chain
#print axioms EDSL.Logical64.xorMasks_membership
#print axioms EDSL.AtomicSet64.Domain.realized
