/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Contract
import EDSL.OS.ArrayResources

namespace EDSL.Pair32
open X86

/-- Both calls describe one worker executing the same code with one return
slot. Input bases, contents, and loan IDs remain independent; readonly inputs
may overlap whenever their current array contracts agree. -/
structure CallCompatibility (callA callB : OS.ArrayResources.Call) : Prop where
  worker : callB.worker = callA.worker
  code : callB.code = callA.code
  bytes : callB.bytes = callA.bytes
  stack : callB.stack = callA.stack
  target : callB.target = callA.target

theorem CallCompatibility.refl (call : OS.ArrayResources.Call) :
    CallCompatibility call call := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Two current admissions share the complete mapped RAM and the executing
worker. Each input retains its own current loan and its own code/stack
separation requirements. Empty inputs do not consult their input loan IDs. -/
structure PairAdmission (shared : OS.Borrowing.State) (callA callB : OS.ArrayResources.Call)
    (machine : State) : Prop where
  admittedA : OS.ArrayResources.Admission shared callA machine
  admittedB : OS.ArrayResources.Admission shared callB machine
  compatible : CallCompatibility callA callB

/-- Full memory preservation retains both current admissions, including the
current contents of both arrays and the complete RAM coupling. -/
theorem PairAdmission.unchangedMemory {shared : OS.Borrowing.State}
    {callA callB : OS.ArrayResources.Call} {before after : State}
    (admitted : PairAdmission shared callA callB before)
    (unchanged : after.memory = before.memory) : PairAdmission shared callA callB after :=
  ⟨admitted.admittedA.unchangedMemory unchanged,
    admitted.admittedB.unchangedMemory unchanged, admitted.compatible⟩

theorem inputReads_member {base : Word} {count : Nat} {read : Sequential.Read}
    (member : read ∈ inputReads base count) :
    read.kind = .data ∧ read.bytes = 4 ∧
      ∃ index, index < count ∧ read.address = base + BitVec.ofNat 64 (4 * index) := by
  obtain ⟨index, inside, same⟩ := List.mem_map.mp member
  subst read
  exact ⟨rfl, rfl, index, List.mem_range.mp inside, rfl⟩

theorem data_read_memberA {initial : State} {valuesA valuesB : List (BitVec 32)}
    {index : Nat} (inside : index < valuesA.length) :
    (⟨.data, initial.registers .rdi + BitVec.ofNat 64 (4 * index), 4⟩ : Sequential.Read) ∈
      operandReads initial valuesA valuesB := by
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨index, List.mem_range.mpr inside, rfl⟩

theorem data_read_memberB {initial : State} {valuesA valuesB : List (BitVec 32)}
    {index : Nat} (inside : index < valuesB.length) :
    (⟨.data, initial.registers .rdx + BitVec.ofNat 64 (4 * index), 4⟩ : Sequential.Read) ∈
      operandReads initial valuesA valuesB := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨index, List.mem_range.mpr inside, rfl⟩

theorem stack_read_member (initial : State) (valuesA valuesB : List (BitVec 32)) :
    (⟨.stack, initial.registers .rsp, 8⟩ : Sequential.Read) ∈
      operandReads initial valuesA valuesB := by
  exact List.mem_append_right _ (by simp)

/-- Current authority and full RAM coupling supply the two-array machine
precondition, using explicit full-width argument and entry bindings. -/
theorem pre_of_admission {shared : OS.Borrowing.State}
    {callA callB : OS.ArrayResources.Call} {initial : State}
    (admitted : PairAdmission shared callA callB initial)
    (entry : initial.rip = callA.code) (stack : initial.registers .rsp = callA.stack)
    (baseA : initial.registers .rdi = callA.base)
    (counterA : initial.registers .rsi = BitVec.ofNat 64 callA.values.length)
    (baseB : initial.registers .rdx = callB.base)
    (counterB : initial.registers .rcx = BitVec.ofNat 64 callB.values.length) :
    Pre callA.bytes initial callA.values callB.values callA.target := by
  obtain ⟨code, returned, arrayA⟩ := admitted.admittedA.current
  have arrayB := admitted.admittedB.current.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, counterA, counterB, ?_,
    admitted.admittedA.resources.returnCanonical, ?_⟩
  · simpa only [entry] using code
  · simpa only [baseA] using arrayA
  · simpa only [baseB] using arrayB
  · simpa only [baseA] using admitted.admittedA.resources.bound
  · simpa only [baseB] using admitted.admittedB.resources.bound
  · simpa only [stack] using returned
  · simpa only [stack] using admitted.admittedA.resources.postStackCanonical

/-- Each element read uses the complete four-byte subregion of this call's
current input loan. There are no such reads, or input-loan requests, for an
empty array. -/
theorem inputReads_permission {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    (resources : OS.ArrayResources.Contract shared call) {read : Sequential.Read}
    (member : read ∈ inputReads call.base call.values.length) :
    OS.ArrayResources.ReadPermission shared call.worker read :=
  OS.ArrayResources.arrayRead_permission resources (inputReads_member member)

/-- All independently enumerated operands have current authority. B operands
use B's own admission; compatibility identifies only the worker. The return
slot uses the complete eight-byte stack loan. -/
theorem operandReads_permission {shared : OS.Borrowing.State}
    {callA callB : OS.ArrayResources.Call} {initial : State}
    (admitted : PairAdmission shared callA callB initial)
    (baseA : initial.registers .rdi = callA.base)
    (baseB : initial.registers .rdx = callB.base)
    (stack : initial.registers .rsp = callA.stack)
    {read : Sequential.Read} (member : read ∈ operandReads initial callA.values callB.values) :
    OS.ArrayResources.ReadPermission shared callA.worker read := by
  rcases List.mem_append.mp member with inputs | returned
  · rcases List.mem_append.mp inputs with dataA | dataB
    · exact inputReads_permission admitted.admittedA.resources (by simpa only [baseA] using dataA)
    · rw [← admitted.compatible.worker]
      exact inputReads_permission admitted.admittedB.resources (by simpa only [baseB] using dataB)
  · have same : read = ⟨.stack, callA.stack, 8⟩ := by
      simpa only [List.mem_singleton, stack] using returned
    subst read
    exact OS.ArrayResources.stackRead_permission admitted.admittedA.resources

end EDSL.Pair32
