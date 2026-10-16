/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory
import EDSL.X86.Sequential.Model
import EDSL.OS.Threads.Framing
import EDSL.OS.Atomics.History

namespace EDSL.OS.ArrayResources
open X86 AddressSpace

/-- Exact byte span, including the empty span which needs no allocation. -/
def arrayRegion (base : Word) (values : List (BitVec 32)) : Region :=
  ⟨base, 4 * values.length⟩

/-- Values in current mapped RAM, rather than an allocation-time snapshot. -/
def currentArrayAt (shared : Borrowing.State) (base : Word)
    (values : List (BitVec 32)) : Prop :=
  ArrayAt (toMemory shared.resources.space) base values

structure LoanIds where
  code : Nat
  stack : Nat
  input : Nat
  deriving DecidableEq, Repr

/-- Resource addresses are independent of a compiler's register allocation. -/
structure Call where
  worker : Nat
  loans : LoanIds
  code : Word
  bytes : List Byte
  stack : Word
  base : Word
  values : List (BitVec 32)
  target : Word

def Call.codeRegion (call : Call) : Region := ⟨call.code, call.bytes.length⟩
def Call.stackRegion (call : Call) : Region := ⟨call.stack, 8⟩
def Call.inputRegion (call : Call) : Region := arrayRegion call.base call.values

/-- Empty input does not require a live input loan, allocation, readable byte,
alignment, or canonical base. Code and the complete return slot remain held. -/
structure Protected (shared : Borrowing.State) (call : Call) : Prop where
  code : Threads.HasLoan shared call.worker call.loans.code call.codeRegion
  stack : Threads.HasLoan shared call.worker call.loans.stack call.stackRegion
  input : call.values ≠ [] →
    Threads.HasLoan shared call.worker call.loans.input call.inputRegion
  code_stack : Ownership.Disjoint call.codeRegion call.stackRegion
  input_code : call.values ≠ [] → Ownership.Disjoint call.inputRegion call.codeRegion
  input_stack : call.values ≠ [] → Ownership.Disjoint call.inputRegion call.stackRegion

/-- Admission contains current authority and current observations only. It
contains no callback assuming a future execution, checker result, or replay.
Managed histories below are resource frames, not a concurrent ISA extension. -/
structure Contract (shared : Borrowing.State) (call : Call) : Prop where
  wellFormed : Borrowing.WellFormed shared
  held : Protected shared call
  code : CodeAt (toMemory shared.resources.space) call.code call.bytes
  stack : readWord (toMemory shared.resources.space) call.stack = .ok call.target
  array : currentArrayAt shared call.base call.values
  bound : ArrayBound call.base call.values
  returnCanonical : canonical call.target = true
  stackBound : call.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (call.stack + 8) = true

/-- Complete current read/write/execute RAM coupling, not equality restricted
to selected successful reads or a stored initial memory. -/
def Coupled (shared : Borrowing.State) (machine : X86.State) : Prop :=
  machine.memory = toMemory shared.resources.space

structure Admission (shared : Borrowing.State) (call : Call) (machine : X86.State) : Prop where
  resources : Contract shared call
  coupled : Coupled shared machine

/-- Endpoint liveness suffices because admitted histories never reuse loan IDs.
The unused input ID has no condition for an empty array. -/
structure Retained (after : Borrowing.State) (call : Call) : Prop where
  code : (after.loans call.loans.code).isSome = true
  stack : (after.loans call.loans.stack).isSome = true
  input : call.values ≠ [] → (after.loans call.loans.input).isSome = true

/-- A structural operand footprint, separate from decoder/evaluator evidence. -/
def ArrayRead (call : Call) (read : Sequential.Read) : Prop :=
  read.kind = .data ∧ read.bytes = 4 ∧
    ∃ index, index < call.values.length ∧
      read.address = call.base + BitVec.ofNat 64 (4 * index)

/-- All bytes of the operand lie within an actually authorized current loan. -/
def ReadPermission (shared : Borrowing.State) (worker : Nat) (read : Sequential.Read) : Prop :=
  ∃ identifier loan, Borrowing.authorize shared (Threads.principal worker) identifier = .ok loan ∧
    Borrowing.Subregion ⟨read.address, read.bytes⟩ loan.region

theorem Admission.current {shared : Borrowing.State} {call : Call} {machine : X86.State}
    (admitted : Admission shared call machine) :
    CodeAt machine.memory call.code call.bytes ∧
      readWord machine.memory call.stack = .ok call.target ∧
      ArrayAt machine.memory call.base call.values := by
  rw [admitted.coupled]
  exact ⟨admitted.resources.code, admitted.resources.stack, admitted.resources.array⟩

theorem Admission.unchangedMemory {shared : Borrowing.State} {call : Call}
    {before after : X86.State} (admitted : Admission shared call before)
    (unchanged : after.memory = before.memory) : Admission shared call after :=
  ⟨admitted.resources, unchanged.trans admitted.coupled⟩

theorem currentArrayAt_nil (shared : Borrowing.State) (base : Word) :
    currentArrayAt shared base [] := by
  intro index value present
  simp at present

theorem arrayBound_nil (base : Word) : ArrayBound base [] := by
  have := base.isLt
  simp only [ArrayBound, List.length_nil, Nat.mul_zero, Nat.add_zero]
  omega

end EDSL.OS.ArrayResources
